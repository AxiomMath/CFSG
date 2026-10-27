module

public import CFSG.RankThree.PartOne.TCP.AlStruct
public import CFSG.RankThree.PartOne.TCP.AlCyclic
public import CFSG.RankThree.PartOne.TCP.AlModel
public import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartOne.TCP.AlSL2
public import CFSG.RankThree.PartOne.TCP.ThreeComp

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.PartOne.KCSpComm
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom subfieldSpHom_injective
  exists_subfieldSpHom_eq fieldSp_subfieldSpHom)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement MatrixGroups

theorem false_of_commutative {G : Type*} [Group G] {C D : Subgroup G} (hDC : D ≤ C)
    (hq : CFSG.IsQuasisimple ↥D) (hc : ∀ g ∈ C, ∀ h ∈ C, g * h = h * g) : False := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hc _ (hDC a.2) _ (hDC b.2))

section Component

variable {K : Type} [Field K] [Finite K] {f p : ℕ}

theorem component_eq_spPull {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    (b : SpBlockIdx x) {D : Subgroup (StatedSp 2 K)}
    (hDc : IsComponentOf (Subgroup.centralizer ({x} : Set (StatedSp 2 K))) D) :
    D = spPull x (b.1 : K[X]) := by
  classical
  have : Finite (StatedSp 2 K) := inferInstance
  obtain ⟨hqb, hbC, -, hcomm, -⟩ := sp4_component_of_idx hD hord blocks b
  obtain ⟨hDC, hDq, hDsn⟩ := hDc
  have hDperf : ⁅D, D⁆ = D := KCUnitary.commutator_eq_of_isPerfect hDq.1
  have hCC : ⁅Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      Subgroup.centralizer ({x} : Set (StatedSp 2 K))⁆ ≤ spPull x (b.1 : K[X]) :=
    Subgroup.commutator_le.mpr fun g hg h hh => hcomm g hg h hh
  have hDb : D ≤ spPull x (b.1 : K[X]) := by
    rw [← hDperf]
    exact (Subgroup.commutator_mono hDC hDC).trans hCC
  have hsn : (D.subgroupOf (spPull x (b.1 : K[X]))).IsSubnormal := by
    have h1 := hDsn.comap (Subgroup.inclusion hbC)
    convert h1 using 1
    ext g
    simp [Subgroup.mem_subgroupOf]
  have hD1 : D ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, a, b, hab⟩ := hDq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall D).mp hbot a.1 a.2)
    apply hab
    rw [ha]
    simp
  exact eq_of_isSubnormal_of_isPerfect_of_isQuasisimple hqb hDb hDq.1 hD1 hsn

end Component

section Core

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem spEnd_mul' {r : ℕ} (a b : StatedSp r K) : spEnd (a * b) = spEnd a * spEnd b := by
  change ((spLin r K (a * b) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_mul, Units.val_mul]

omit [Finite K] in
theorem mul_comm_of_spEnd {r : ℕ} {a b : StatedSp r K} (h : spEnd a * spEnd b = spEnd b * spEnd a) :
    a * b = b * a :=
  spLin_injective (Units.ext (by rw [map_mul, map_mul, Units.val_mul, Units.val_mul]; exact h))

omit [Finite K] in
theorem spEnd_comm_of_mem_centralizer {r : ℕ} {x g : StatedSp r K}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (StatedSp r K))) :
    spEnd g * spEnd x = spEnd x * spEnd g := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [← spEnd_mul', ← spEnd_mul', h]

theorem psp_clauseA_core {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ (p * f₀)) (hord : orderOf (Nat.card K : ZMod p) = 2)
    {σ : K ≃+* K} (hkcard : Nat.card (descentField σ) = 2 ^ f₀) {x : StatedSp 2 K}
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hσx : fieldSp 2 K σ x = x) {D : Subgroup (StatedSp 2 K)}
    (hD : IsComponentOf (Subgroup.centralizer ({x} : Set (StatedSp 2 K))) D) :
    (∀ E ∈ D, ¬ ∀ g ∈ D, fieldSp 2 K σ g = E * g * E⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
    ∃ t₁ ∈ D, fieldSp 2 K σ t₁ = t₁ ∧ ∃ t₂ ∈ D, fieldSp 2 K σ t₂ = t₂ ∧
      (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcharK : CharP K 2 := charP_two_of_natCard_eq hK
  have hp2 : p ≠ 2 := by omega
  have hf1 : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hq4 : 3 < 2 ^ (p * f₀) := by
    calc 3 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hSD : SpData 2 (p * f₀) 2 p K x :=
    ⟨Nat.prime_two, hf1, hK, hq4, le_rfl, hp, by omega, by omega, hxo⟩
  have hker := TCX.ker_proj_two_eq_bot (K := K) (hK ▸ dvd_pow_self 2 (by omega)) (r := 2)
    (by norm_num)
  have hinj : Function.Injective (proj 2 K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hxop : orderOf (proj 2 K x) = p := by rw [orderOf_injective _ hinj x, hxo]
  have blocks := ((symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hK hp hp2
    hp2 (by norm_num) _ hxop).2) x rfl hxo
  have hnc : ¬ ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), g * h = h * g :=
    fun hc => false_of_commutative hD.1 hD.2.1 hc
  obtain ⟨b⟩ : Nonempty (SpBlockIdx x) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hnc (sp4_idx_empty_commute hSD blocks hne)
  have hDeq := component_eq_spPull hSD hord blocks b hD
  obtain ⟨F, _, _, _, hFcard, ⟨eK⟩⟩ := sp4_block_equiv hSD hord blocks b
  obtain ⟨hqD, hDC, hDn, hDcomm, hD2⟩ := sp4_component_of_idx hSD hord blocks b
  obtain ⟨x₀, hx₀⟩ := exists_subfieldSpHom_eq hσx
  have hfink : Finite (descentField σ) :=
    Nat.finite_of_card_ne_zero (by rw [hkcard]; positivity)
  have hchark : CharP (descentField σ) 2 := charP_two_of_natCard_eq hkcard
  have hQk : Nat.card K = Nat.card (descentField σ) ^ p := by
    rw [hK, hkcard, ← pow_mul, mul_comm]
  have hordk : orderOf (Nat.card (descentField σ) : ZMod p) = 2 :=
    (orderOf_natCast_pow_prime hp hQk).symm.trans hord
  have hpk : p ∣ Nat.card (descentField σ) + 1 := prime_dvd_card_add_one hp hordk
  have hq4k : 3 < 2 ^ f₀ := by
    rw [← hkcard]
    have := Nat.le_of_dvd (by omega) hpk
    omega
  have hx₀o : orderOf x₀ = p := by
    rw [← orderOf_injective (subfieldSpHom 2 (descentField σ))
      (subfieldSpHom_injective (descentField σ)) x₀, hx₀, hxo]
  have hSD₀ : SpData 2 f₀ 2 p (descentField σ) x₀ :=
    ⟨Nat.prime_two, hf₀, hkcard, hq4k, le_rfl, hp, by omega, by omega, hx₀o⟩
  have hker₀ := TCX.ker_proj_two_eq_bot (K := descentField σ)
    (hkcard ▸ dvd_pow_self 2 (by omega)) (r := 2) (by norm_num)
  have hinj₀ : Function.Injective (proj 2 (descentField σ)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker₀
  have hxop₀ : orderOf (proj 2 (descentField σ) x₀) = p := by
    rw [orderOf_injective _ hinj₀ x₀, hx₀o]
  have blocks₀ := ((symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf₀ hkcard hp
    hp2 hp2 (by norm_num) _ hxop₀).2) x₀ rfl hx₀o
  obtain ⟨b₀⟩ : Nonempty (SpBlockIdx x₀) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have hm1 : ∀ a : primaryFactors (spEnd x₀),
        primaryMultiplicity (spEnd x₀) (a : (descentField σ)[X]) ≤ 1 := fun a => by
      by_contra h
      exact hne.false ⟨a, by omega⟩
    obtain ⟨v₀, hv₀⟩ := exists_cyclic_of_multiplicity_le_one hSD₀.squarefree hm1
    obtain ⟨v, hv⟩ := cyclic_map_subfield (descentField σ) x₀ hv₀
    refine hnc fun g hg h hh => ?_
    rw [← hx₀] at hg hh
    exact mul_comm_of_spEnd (commute_of_cyclic hv (spEnd_comm_of_mem_centralizer hg)
      (spEnd_comm_of_mem_centralizer hh))
  obtain ⟨F₀, _, _, _, hF₀card, ⟨e₀⟩⟩ := sp4_block_equiv hSD₀ hordk blocks₀ b₀
  obtain ⟨-, hD₀C, -, hD₀comm, -⟩ := sp4_component_of_idx hSD₀ hordk blocks₀ b₀
  set D₀ := spPull x₀ (b₀.1 : (descentField σ)[X]) with hD₀def
  let τ₁ : ↥D₀ := e₀.symm sl2Upper
  let τ₂ : ↥D₀ := e₀.symm sl2Lower
  have hτ₁ : τ₁ * τ₁ = 1 := by
    show e₀.symm sl2Upper * e₀.symm sl2Upper = 1
    rw [← map_mul, sl2Upper_sq, map_one]
  have hτ₂ : τ₂ * τ₂ = 1 := by
    show e₀.symm sl2Lower * e₀.symm sl2Lower = 1
    rw [← map_mul, sl2Lower_sq, map_one]
  have hτ₁₂ : τ₁ * τ₂ ≠ τ₂ * τ₁ := fun h =>
    sl2_noncomm (e₀.symm.injective (by rw [map_mul, map_mul]; exact h))
  have hτ₁1 : τ₁ ≠ 1 := fun h => hτ₁₂ (by rw [h, one_mul, mul_one])
  have hτ₂1 : τ₂ ≠ 1 := fun h => hτ₁₂ (by rw [h, one_mul, mul_one])
  let j := subfieldSpHom 2 (descentField σ)
  have hjinj : Function.Injective j := subfieldSpHom_injective (descentField σ)
  have htC : ∀ τ : ↥D₀, j (τ : StatedSp 2 (descentField σ)) ∈
      Subgroup.centralizer ({x} : Set (StatedSp 2 K)) := by
    intro τ
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hD₀C τ.2)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hx₀, ← map_mul, ← map_mul, h1]
  have hord2 : ∀ τ : ↥D₀, τ * τ = 1 → τ ≠ 1 →
      orderOf (j (τ : StatedSp 2 (descentField σ))) = 2 := by
    intro τ h1 h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (τ : StatedSp 2 (descentField σ)) * τ = 1 := congrArg Subtype.val h1
      rw [this, map_one]
    · intro h
      apply h2
      exact Subtype.ext (hjinj (by rw [h]; exact (map_one j).symm))
  have ht₁2 : orderOf (j (τ₁ : StatedSp 2 (descentField σ))) = 2 := hord2 τ₁ hτ₁ hτ₁1
  have ht₂2 : orderOf (j (τ₂ : StatedSp 2 (descentField σ))) = 2 := hord2 τ₂ hτ₂ hτ₂1
  have ht₁D : j (τ₁ : StatedSp 2 (descentField σ)) ∈ spPull x (b.1 : K[X]) :=
    hD2 _ (htC τ₁) ⟨1, by rw [ht₁2, pow_one]⟩
  have ht₂D : j (τ₂ : StatedSp 2 (descentField σ)) ∈ spPull x (b.1 : K[X]) :=
    hD2 _ (htC τ₂) ⟨1, by rw [ht₂2, pow_one]⟩
  have hσt : ∀ τ : ↥D₀, fieldSp 2 K σ (j (τ : StatedSp 2 (descentField σ))) =
      j (τ : StatedSp 2 (descentField σ)) := fun τ => fieldSp_subfieldSpHom _
  have hnc12 : j (τ₁ : StatedSp 2 (descentField σ)) * j (τ₂ : StatedSp 2 (descentField σ)) ≠
      j (τ₂ : StatedSp 2 (descentField σ)) * j (τ₁ : StatedSp 2 (descentField σ)) := by
    intro h
    apply hτ₁₂
    apply Subtype.ext
    apply hjinj
    show j ((τ₁ : StatedSp 2 (descentField σ)) * τ₂) = j ((τ₂ : StatedSp 2 (descentField σ)) * τ₁)
    rw [map_mul, map_mul]
    exact h
  have hsq : ∀ τ : ↥D₀, τ * τ = 1 → j (τ : StatedSp 2 (descentField σ)) *
      j (τ : StatedSp 2 (descentField σ)) = 1 := fun τ h => by
    rw [← map_mul]
    have : (τ : StatedSp 2 (descentField σ)) * τ = 1 := congrArg Subtype.val h
    rw [this, map_one]
  subst hDeq
  refine ⟨?_, ?_, ?_⟩
  ·
    intro E hE hall
    have hcomm : ∀ τ : ↥D₀, j (τ : StatedSp 2 (descentField σ)) ∈ spPull x (b.1 : K[X]) →
        E * j (τ : StatedSp 2 (descentField σ)) = j (τ : StatedSp 2 (descentField σ)) * E := by
      intro τ hτ
      have h1 := hall _ hτ
      rw [hσt τ] at h1
      calc E * j (τ : StatedSp 2 (descentField σ))
          = (E * j (τ : StatedSp 2 (descentField σ)) * E⁻¹) * E := by group
        _ = j (τ : StatedSp 2 (descentField σ)) * E := by rw [← h1]
    let a₁ : ↥(spPull x (b.1 : K[X])) := ⟨j (τ₁ : StatedSp 2 (descentField σ)), ht₁D⟩
    let a₂ : ↥(spPull x (b.1 : K[X])) := ⟨j (τ₂ : StatedSp 2 (descentField σ)), ht₂D⟩
    let aE : ↥(spPull x (b.1 : K[X])) := ⟨E, hE⟩
    have ha₁ : a₁ * a₁ = 1 := Subtype.ext (hsq τ₁ hτ₁)
    have ha₂ : a₂ * a₂ = 1 := Subtype.ext (hsq τ₂ hτ₂)
    have h1 : eK aE = 1 := by
      refine eq_one_of_commute_noncomm (u := eK a₁) (v := eK a₂) ?_ ?_ ?_ ?_ ?_
      · rw [← map_mul, ha₁, map_one]
      · rw [← map_mul, ha₂, map_one]
      · intro h
        apply hnc12
        have h' : a₁ * a₂ = a₂ * a₁ := eK.injective (by rw [map_mul, map_mul]; exact h)
        exact congrArg Subtype.val h'
      · rw [← map_mul, ← map_mul]
        exact congrArg eK (Subtype.ext (hcomm τ₁ ht₁D))
      · rw [← map_mul, ← map_mul]
        exact congrArg eK (Subtype.ext (hcomm τ₂ ht₂D))
    have hE1 : E = 1 := congrArg Subtype.val (eK.injective (h1.trans (map_one eK).symm))
    have hfix : ∀ g ∈ spPull x (b.1 : K[X]), fieldSp 2 K σ g = g := by
      intro g hg
      rw [hall g hg, hE1]
      group
    have hperf : ⁅spPull x (b.1 : K[X]), spPull x (b.1 : K[X])⁆ = spPull x (b.1 : K[X]) :=
      KCUnitary.commutator_eq_of_isPerfect hqD.1
    have hle1 : spPull x (b.1 : K[X]) ≤
        (Subgroup.centralizer ({x₀} : Set (StatedSp 2 (descentField σ)))).map j := by
      intro g hg
      obtain ⟨g₀, rfl⟩ := exists_subfieldSpHom_eq (hfix g hg)
      refine ⟨g₀, ?_, rfl⟩
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hDC hg)
      rw [← hx₀, ← map_mul, ← map_mul] at h2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hjinj h2)
    have hDle : spPull x (b.1 : K[X]) ≤ D₀.map j := by
      rw [← hperf]
      calc ⁅spPull x (b.1 : K[X]), spPull x (b.1 : K[X])⁆
          ≤ ⁅(Subgroup.centralizer ({x₀} : Set (StatedSp 2 (descentField σ)))).map j,
              (Subgroup.centralizer ({x₀} : Set (StatedSp 2 (descentField σ)))).map j⁆ :=
            Subgroup.commutator_mono hle1 hle1
        _ = ⁅Subgroup.centralizer ({x₀} : Set (StatedSp 2 (descentField σ))),
              Subgroup.centralizer ({x₀} : Set (StatedSp 2 (descentField σ)))⁆.map j :=
            (Subgroup.map_commutator _ _ _).symm
        _ ≤ D₀.map j := Subgroup.map_mono
            (Subgroup.commutator_le.mpr fun g hg h hh => hD₀comm g hg h hh)
    have hcard1 : Nat.card ↥(spPull x (b.1 : K[X])) ≤ Nat.card ↥D₀ := by
      have h3 := Subgroup.card_le_of_le hDle
      have h4 : Nat.card ↥(D₀.map j) = Nat.card ↥D₀ :=
        (Nat.card_congr (D₀.equivMapOfInjective j hjinj).toEquiv).symm
      rwa [h4] at h3
    have hcD : Nat.card ↥(spPull x (b.1 : K[X])) = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr eK.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
    have hcD₀ : Nat.card ↥D₀ = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
      rw [Nat.card_congr e₀.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₀]
    rw [hcD, hcD₀] at hcard1
    have hAB : 2 ^ f₀ < 2 ^ (p * f₀) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    have hFa : Nat.card F₀ < Nat.card F := by rw [hF₀card, hkcard, hFcard, hK]; exact hAB
    have hb4 : 4 ≤ Nat.card F₀ := by rw [hF₀card, hkcard]; omega
    have hsq2 : Nat.card F₀ ^ 2 < Nat.card F ^ 2 := Nat.pow_lt_pow_left hFa (by norm_num)
    have h5 : Nat.card F₀ ^ 2 - 1 < Nat.card F ^ 2 - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) hsq2
    have h6 : Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) < Nat.card F * (Nat.card F ^ 2 - 1) :=
      Nat.mul_lt_mul'' hFa h5
    omega
  ·
    have hF2 : Nat.card F = 2 ^ (p * f₀) := hFcard.trans hK
    have hq4' : 4 ≤ 2 ^ (p * f₀) := by omega
    exact ⟨.PSL, 2, f₀, hf₀, lieModel_of_equiv_SL2 hq4' hF2 eK⟩
  · exact ⟨_, ht₁D, hσt τ₁, _, ht₂D, hσt τ₂, ⟨1, by rw [ht₁2, pow_one]⟩,
      ⟨1, by rw [ht₂2, pow_one]⟩, hnc12⟩

end Core

end CFSG.RankThree.PartOne.TCP
