module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement Pointwise

namespace OrdPInnerExc

section Model

variable {L C G : Type*} [Group L] [Group C] [Group G] {π : L →* C} {ψ : L →* G}

theorem innerAut_normal : (MulAut.conj : C →* MulAut C).range.Normal := by
  refine ⟨fun _ ⟨x, hx⟩ φ => ⟨φ x, ?_⟩⟩
  rw [← hx]
  refine MulEquiv.ext fun g => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_centralizer_of_induces_one (hkc : π.ker ≤ Subgroup.center L)
    (hperf : commutator ↥ψ.range = ⊤) {d : G} (hdN : d ∈ Subgroup.normalizer (ψ.range : Set G))
    (hd : LayerSixE.GGInduces π ψ d 1) : d ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hmove : ∀ y : L, ∃ z ∈ Subgroup.center L, d * ψ y * d⁻¹ = ψ (y * z) := by
    intro y
    obtain ⟨y', hy'⟩ := LayerSixE.exists_conj_eq hdN y
    have h1 := hd y y' hy'
    rw [MulAut.one_apply] at h1
    refine ⟨y⁻¹ * y', hkc ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    · rw [← hy', mul_inv_cancel_left]
  let H : Subgroup ↥ψ.range :=
    { carrier := {x | d * (x : G) * d⁻¹ = x}
      one_mem' := by
        change d * (1 : G) * d⁻¹ = 1
        group
      mul_mem' := fun {a b} ha hb => by
        change d * ((a : G) * b) * d⁻¹ = a * b
        calc d * ((a : G) * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
          _ = a * b := by rw [ha, hb]
      inv_mem' := fun {a} ha => by
        change d * ((a : G))⁻¹ * d⁻¹ = (a : G)⁻¹
        calc d * ((a : G))⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
          _ = (a : G)⁻¹ := by rw [ha] }
  have hle : commutator ↥ψ.range ≤ H := by
    rw [commutator, Subgroup.commutator_le]
    rintro ⟨_, y₁, rfl⟩ - ⟨_, y₂, rfl⟩ -
    obtain ⟨z₁, hz₁, e₁⟩ := hmove y₁
    obtain ⟨z₂, hz₂, e₂⟩ := hmove y₂
    change d * ((⁅ψ y₁, ψ y₂⁆ : G)) * d⁻¹ = ⁅ψ y₁, ψ y₂⁆
    have hconj : d * ⁅ψ y₁, ψ y₂⁆ * d⁻¹ = ⁅d * ψ y₁ * d⁻¹, d * ψ y₂ * d⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hconj, e₁, e₂, ← map_commutatorElement, ← map_commutatorElement,
      LayerSixE.commutatorElement_mul_central_left hz₁,
      LayerSixE.commutatorElement_mul_central_right hz₂]
  rw [hperf, top_le_iff] at hle
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hgH : (⟨g, hg⟩ : ↥ψ.range) ∈ H := by rw [hle]; exact Subgroup.mem_top _
  have e : d * g * d⁻¹ = g := hgH
  calc g * d = d * g * d⁻¹ * d := by rw [e]
    _ = d * g := by group

theorem mem_range_of_induces_inner (hπ : Function.Surjective π)
    (hkc : π.ker ≤ Subgroup.center L) (hkπ : ψ.ker ≤ π.ker) (hperf : commutator ↥ψ.range = ⊤)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut C}
    (hα : α ∈ (MulAut.conj : C →* MulAut C).range) (hc : LayerSixE.GGInduces π ψ c α) :
    c ∈ ψ.range := by
  obtain ⟨x, rfl⟩ := hα
  obtain ⟨w, rfl⟩ := hπ x
  have hwN : ψ w⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.le_normalizer ⟨w⁻¹, rfl⟩
  have hd := hc.mul hwN (LayerSixE.GGInduces.psi hkπ w⁻¹)
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one] at hd
  have hcd := mem_centralizer_of_induces_one hkc hperf (mul_mem hcN hwN) hd
  rw [hC, Subgroup.mem_bot, mul_eq_one_iff_eq_inv, map_inv, inv_inv] at hcd
  rw [hcd]
  exact ⟨w, rfl⟩

theorem ne_three_or_of_not_outdiag_E6 {p n f : ℕ} (h : ¬ GGOutdiagPrimeConfig p .E6 n f) :
    p ≠ 3 ∨ ¬ 3 ∣ 2 ^ f - 1 := by
  by_cases hp : p = 3
  · exact Or.inr fun h3 => h (Or.inr (Or.inr (Or.inl ⟨rfl, hp, h3⟩)))
  · exact Or.inl hp

end Model

section Cubes

variable {K : Type} [Field K]

theorem rootDiagAutHom_pow_three_mem_E6 (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a ^ 3 ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  rw [← map_pow]
  have hdet : Tag.E6.cartan.transpose.det = 3 := by rw [Matrix.det_transpose, det_cartan_E6]
  have hmem : rootDiagUnit .E6 (a ^ 3) ∈ torusGroup .E6 K := by
    rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (a := a ^ 3) (u := a) fun i => by
      rw [hdet, Pi.pow_apply]
      exact zpow_ofNat (a i) 3]
    exact list_prod_torusElt_mem_torusGroup _
  refine ⟨⟨rootDiagUnit .E6 (a ^ 3),
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hmem⟩, ?_⟩
  exact MulEquiv.ext fun g => Subtype.ext rfl

theorem rootDiagAutHom_mem_E6_of_not_dvd [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1)
    (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  choose b hb using fun i => OrdPNS.exists_pow_eq Nat.prime_three h3 (a i)
  have hab : a = b ^ 3 := funext fun i => (hb i).symm
  rw [hab, map_pow]
  exact rootDiagAutHom_pow_three_mem_E6 b

theorem mem_inn_of_inndiag_E6 [Finite K] {p : ℕ} (hp : p.Prime)
    (h : p ≠ 3 ∨ ¬ 3 ∣ Nat.card K - 1) {α : MulAut (adjointGroup .E6 K)}
    (hα : α ∈ LayerSixE.inndiagAut .E6 K) (hαp : α ^ p = 1) :
    α ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have := innerAut_normal (C := adjointGroup .E6 K)
  set N := (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range with hN
  have hmem : α ∈ ((N : Set (MulAut (adjointGroup .E6 K))) *
      ((rootDiagAutHom .E6 K).range : Set (MulAut (adjointGroup .E6 K)))) := by
    rw [← Subgroup.normal_mul]
    exact hα
  obtain ⟨ι, hι, δ, ⟨a, rfl⟩, rfl⟩ := Set.mem_mul.mp hmem
  rw [← QuotientGroup.eq_one_iff (N := N)]
  have h1 : ((ι * rootDiagAutHom .E6 K a : MulAut (adjointGroup .E6 K)) :
      MulAut (adjointGroup .E6 K) ⧸ N) = (rootDiagAutHom .E6 K a : MulAut _ ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ι).mpr hι, one_mul]
  rw [h1]
  rcases h with hp3 | h3
  · have hcube : (rootDiagAutHom .E6 K a : MulAut (adjointGroup .E6 K) ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact rootDiagAutHom_pow_three_mem_E6 a
    have hpow : (rootDiagAutHom .E6 K a : MulAut (adjointGroup .E6 K) ⧸ N) ^ p = 1 := by
      rw [← h1, ← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
    have hcop : Nat.gcd 3 p = 1 :=
      (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
    have h2 := pow_gcd_eq_one.mpr ⟨hcube, hpow⟩
    rwa [hcop, pow_one] at h2
  · rw [QuotientGroup.eq_one_iff]
    exact rootDiagAutHom_mem_E6_of_not_dvd h3 a

end Cubes

section E6


theorem coprime_card_center_E6 {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (h : p ≠ 3 ∨ ¬ 3 ∣ Nat.card k - 1) :
    Nat.Coprime (Nat.card (Subgroup.center ↥(e6Data_valid.minGroup k))) p := by
  rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 k).1]
  rcases h with hp3 | h3
  · exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 3 _)
      ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  · rw [(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3]
    exact Nat.coprime_one_left p

theorem inner_E6 (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .E6 n f).K →* G) (hS : GGSixFusionSetting p Bs G₀ (ggU .E6 n f).D .E6 n f ψ)
    (hout : ¬ GGOutdiagPrimeConfig p .E6 n f) (c : G)
    (hcN : c ∈ Subgroup.normalizer (G₀ : Set G)) (hcp : c ^ p = 1)
    (hci : GGPsiInnerDiag (ggU .E6 n f).D ψ c) : c ∈ G₀ := by
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hS.presents
  have hC := hS.centralizer_eq_bot
  subst hrange
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hcN hci
  have hπ := e6Isogeny_surjective (GaloisField 2 f)
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  have hcase : p ≠ 3 ∨ ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hK]
    exact ne_three_or_of_not_outdiag_E6 hout
  exact mem_range_of_induces_inner hπ
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)) hkπ
    hperf hC hcN (mem_inn_of_inndiag_E6 hS.prime hcase hαD hαp) hα

theorem ggOrdPToralMax_E6_split {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) :
    GGOrdPToralMax (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f) p := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hC := ggOrdPToralMax_adj (τ := .E6) (K := GaloisField 2 f) hp
    (TableBExc.not_dvd_index_torusGroup_E6 hp hp7 (hK ▸ hpq))
  have : Finite (adjointGroup .E6 (GaloisField 2 f)) := generated_group_finite _ _
  refine ggOrdPToralMax_of_surjective hp (e6Isogeny_surjective (GaloisField 2 f))
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)) ?_ hC
  exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)))
    (coprime_card_center_E6 hp (Or.inl (by omega)))

end E6

end OrdPInnerExc

section Tag


@[expose] def GGOrdPToralE6Rest : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (p = 3 ∧ 3 ∣ 2 ^ f - 1) → ¬ (7 ≤ p ∧ p ∣ 2 ^ f - 1) →
    (∃ A : Subgroup (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f),
      IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f) p

theorem ggOrdPToralUnivAt_E6_of_rest (h : GGOrdPToralE6Rest) : GGOrdPToralUnivAt .E6 := by
  intro n f p hadm hp hp2 hout hA
  change ∃ A : Subgroup (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f),
    IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A at hA
  change GGOrdPToralMax (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f) p
  have hf : 1 ≤ f := hadm.2.1
  by_cases hs : 7 ≤ p ∧ p ∣ 2 ^ f - 1
  · exact OrdPInnerExc.ggOrdPToralMax_E6_split hf hp hs.1 hs.2
  · refine h f p hf hp hp2 ?_ hs hA
    rintro ⟨rfl, h3⟩
    exact hout (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h3⟩)))

theorem ggOrdPInnerConjAt_E6_of_toral (hT : GGOrdPToralUnivAt .E6) : GGOrdPInnerConjAt .E6 := by
  refine OrdPInnerExc.ggOrdPInnerConjAt_of_parts OrdPInnerExc.inner_E6
    (fun n f p hadm hp hout => ?_) hT
  change Nat.Coprime (Nat.card (Subgroup.center
    (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f))) p
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by
    have := hadm.2.1
    omega)
  refine OrdPInnerExc.coprime_card_center_E6 hp ?_
  rw [hK]
  exact OrdPInnerExc.ne_three_or_of_not_outdiag_E6 hout

end Tag

end CFSG.StandardType
