module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.RigidOuter
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.CoverCentAltSix
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofEight
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Outer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem alphaNine_of_inputs {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ σ : MulAut X, ∃ k : ℕ, σ ^ (2 ^ k) ∈ (MulAut.conj : X →* MulAut X).range)
    (hchar : ∀ b : X, orderOf b = 3 →
      IsCharacteristicP 3 ↥(Subgroup.centralizer ({b} : Set X)))
    (h81 : ∀ b : X, orderOf b = 3 → 81 ∣ Nat.card ↥(Subgroup.centralizer ({b} : Set X)))
    (hfix : ∀ τ : MulAut X, τ ^ 2 = 1 → τ ∉ (MulAut.conj : X →* MulAut X).range →
      ∀ H : Subgroup X, (∀ c ∈ H, τ c = c) → ¬ 81 ∣ Nat.card H) :
    Coordinator.Cover423.AlphaNine X := by
  intro D hD hD9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD9
    omega
  have hord : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (hD.2 b hb) hb1
  refine Res423Three.alphaVanishes_of_rigid hZ hD1
    (fun b hb hb1 =>
      Res423Three.core_eq_bot_of_isCharacteristicP (hchar b (hord b hb hb1)))
    (fun b hb hb1 σ hσ hfixσ => ?_)
  have hb3 := hord b hb hb1
  have hbC : b ∈ Subgroup.centralizer ({b} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine Proving.eq_one_of_fix_of_outer hZ hOut (Subgroup.centralizer ({b} : Set X)) ?_ ?_ σ hσ
    hfixσ
  · intro g hg
    have hgC : g ∈ Subgroup.centralizer ({b} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hg b hbC)
    have hcen : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({b} : Set X))) ∈
        Subgroup.center ↥(Subgroup.centralizer ({b} : Set X)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hg h h.2).symm
    obtain ⟨k, hk⟩ := Res423Three.exists_pow_eq_one_of_mem_center (hchar b hb3) hcen
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro τ hτ2 hτo hall
    exact hfix τ hτ2 hτo (Subgroup.centralizer ({b} : Set X)) hall (h81 b hb3)

theorem sq_mem_range_conj_of_card_outer {X : Type} [Group X]
    (h : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 2)
    (σ : MulAut X) : σ ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
  have h1 := pow_card_eq_one' (G := CFSG.ComponentClassification.OuterAutomorphisms.Outer X)
    (x := (QuotientGroup.mk σ : CFSG.ComponentClassification.OuterAutomorphisms.Outer X))
  rw [h, ← QuotientGroup.mk_pow] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem isCharacteristicP_centralizer_g2_three
    {K : Type} [Field K] [Finite K] [CharP K 3] {z : adjointGroup .G2 K} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) :
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hQp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, pow_one])
  have hQ : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    apply hz1
    have h1 : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨hchar, -⟩ :=
    (RootWeightDatum.ordinary (K := K) .G2).defining_characteristic_root_local_groups_component_free
      3 (Subgroup.zpowers z) hQp hQ _ (Or.inr rfl)
  have hchar' : IsCharacteristicP 3 ↥(Subgroup.centralizer
      ((Subgroup.zpowers z : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K))) := hchar
  have hEq : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K)) = Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h y (Subgroup.mem_zpowers y)
    · intro h y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (h z rfl).symm.symm n).eq)
  rw [hEq] at hchar'
  exact hchar'

section R3

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U Item434RemG23


theorem eighty_one_dvd_card_centralizer_R3 (b : R3) (hb : orderOf b = 3) :
    81 ∣ Nat.card ↥(Subgroup.centralizer ({b} : Set R3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSR := sylow_le_R3 sylWord_lt
  have hcardS : Nat.card (sylow.subgroupOf R3) = 3 ^ (Nat.card R3).factorization 3 := by
    rw [Item434SporE81.card_subgroupOf_of_le hSR]
    exact card_sylow_eq
  have hp : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hcardS hp
  have hg' := Item434AltPerm.map_conj_inv_le hg
  set b₀ : R3 := g⁻¹ * b * g with hb₀
  have hb₀S : b₀ ∈ sylow.subgroupOf R3 :=
    hg' ⟨b, Subgroup.mem_zpowers b, by simp [hb₀]⟩
  have hb₀3 : b₀ ^ 3 = 1 := by
    have h3 : b ^ 3 = 1 := by
      have := pow_orderOf_eq_one b
      rwa [hb] at this
    have h4 : b₀ = g⁻¹ * b * g⁻¹⁻¹ := by simp only [hb₀, inv_inv]
    calc b₀ ^ 3 = g⁻¹ * b ^ 3 * g⁻¹⁻¹ := by rw [h4, conj_pow]
      _ = 1 := by rw [h3]; group
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    have : b = 1 := by
      have h2 : b = g * b₀ * g⁻¹ := by simp only [hb₀]; group
      rw [h2, h]; group
    rw [this, orderOf_one] at hb
    omega
  have hcard : Nat.card ↥(Subgroup.centralizer ({b} : Set R3)) =
      Nat.card ↥(Subgroup.centralizer ({b₀} : Set R3)) :=
    Nat.card_congr (centralizerSingletonEquivOfConj g (by simp only [hb₀]; group)).toEquiv
  rw [hcard]
  obtain ⟨z, hzS, hz3, hz1, hzc, hgood⟩ := exists_hgood sylCheck_true k2Check_true sylWord_lt
  obtain ⟨z', hz'⟩ : ∃ z' : R3, (z' : GL (Fin 14) (ZMod 3)) = z := ⟨⟨z, hSR hzS⟩, rfl⟩
  subst hz'
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz3)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  by_cases hmem : b₀ ∈ Subgroup.zpowers z'
  ·
    have hmemGL : (b₀ : GL (Fin 14) (ZMod 3)) ∈ Subgroup.zpowers (z' : GL (Fin 14) (ZMod 3)) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
    have hle : sylow.subgroupOf R3 ≤ Subgroup.centralizer ({b₀} : Set R3) := by
      intro q hq
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemGL
      have hqz : (q : GL (Fin 14) (ZMod 3)) * (z' : GL (Fin 14) (ZMod 3)) =
          (z' : GL (Fin 14) (ZMod 3)) * (q : GL (Fin 14) (ZMod 3)) :=
        hzc _ (Subgroup.mem_subgroupOf.mp hq)
      have hc : (q : GL (Fin 14) (ZMod 3)) * (b₀ : GL (Fin 14) (ZMod 3)) =
          (b₀ : GL (Fin 14) (ZMod 3)) * (q : GL (Fin 14) (ZMod 3)) := by
        rw [← hk]
        exact (Commute.zpow_right (show Commute (q : GL (Fin 14) (ZMod 3))
          (z' : GL (Fin 14) (ZMod 3)) from hqz) k).eq
      have hc' : q * b₀ = b₀ * q := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc'
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardS, card_R3, factorization_three_card] at hdvd
    exact (show 81 ∣ 3 ^ 6 by norm_num).trans hdvd
  · have hb₀S' : (b₀ : GL (Fin 14) (ZMod 3)) ∈ sylow := Subgroup.mem_subgroupOf.mp hb₀S
    have hb₀3' : (b₀ : GL (Fin 14) (ZMod 3)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hb₀3, Subgroup.coe_one]
    have hnz : (b₀ : GL (Fin 14) (ZMod 3)) ∉ Subgroup.zpowers (z' : GL (Fin 14) (ZMod 3)) := by
      intro h
      apply hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    obtain ⟨E, hER, hE, hE81, hbE, -⟩ := hgood _ hb₀S' hb₀3' hnz
    have hE' : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf R3) :=
      Res423Three.isElemAbelian_subgroupOf hE
    have hcE : Nat.card (E.subgroupOf R3) = Nat.card E :=
      Item434SporE81.card_subgroupOf_of_le hER
    have hle : E.subgroupOf R3 ≤ Subgroup.centralizer ({b₀} : Set R3) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Res423Two.comm_of_isElemAbelian hE' b₀ (Subgroup.mem_subgroupOf.mpr hbE) e he).symm
    have hdvd := Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hE').exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hk] at hdvd
    exact (pow_dvd_pow_of_dvd (show (3 : ℕ) ∣ 3 from dvd_rfl) 4 |>.trans
      (pow_dvd_pow 3 hk4)).trans hdvd |> fun h => by simpa using h

theorem not_dvd_card_of_fix_outer {X : Type} [Group X]
    (e : X ≃* CFSG.CGT.PushingUpLit.CGT6.EmbG23.G23) :
    ∀ τ : MulAut X, τ ^ 2 = 1 → τ ∉ (MulAut.conj : X →* MulAut X).range →
      ∀ H : Subgroup X, (∀ c ∈ H, τ c = c) → ¬ 81 ∣ Nat.card H := by
  intro τ hτ2 hτo H hH h81
  set α : MulAut CFSG.CGT.PushingUpLit.CGT6.EmbG23.G23 := MulAut.congr e τ with hα
  have hα2 : α * α = 1 := by
    rw [← sq, hα, ← map_pow, hτ2, map_one]
  have hout : α ∉ (MulAut.conj : CFSG.CGT.PushingUpLit.CGT6.EmbG23.G23 →*
      MulAut CFSG.CGT.PushingUpLit.CGT6.EmbG23.G23).range := by
    rintro ⟨g, hg⟩
    apply hτo
    refine ⟨e.symm g, ?_⟩
    have h1 : MulAut.congr e.symm α = τ := by
      rw [hα]
      ext x
      simp [MulAut.congr_apply]
    rw [← h1, ← hg]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e.symm g).symm
  obtain ⟨-, hcard⟩ := CFSG.CGT.PushingUpLit.CGT6.EmbG23.exists_conj_phi α hα2 hout
  have hle : H.map e.toMonoidHom ≤ CFSG.CGT.PushingUpLit.CGT6.EmbG23.fixedGroup α := by
    rintro _ ⟨h, hh, rfl⟩
    show α (e h) = e h
    simp [hα, MulAut.congr_apply, hH h hh]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective e.injective, hcard] at hdvd
  exact absurd (h81.trans hdvd) (by norm_num)

theorem alphaNine_G2 {S : Type} [Group S]
    (hS : Blueprint.ChevalleyExceptionalModel S .G2 3 1) :
    Coordinator.Cover423.AlphaNine S := by
  have hOutS := KFacts.OutFixCentralThree.card_outer_G2_three S hS
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 hS
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Fintype.card K = 3 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime hK3
  have : Finite S := Finite.of_equiv _ E.symm.toEquiv
  have hc : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 : E x ∈ Subgroup.center (adjointGroup .G2 K) := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv E]
      exact ⟨x, hx, rfl⟩
    rw [hc, Subgroup.mem_bot] at h1
    exact E.injective (h1.trans (map_one E).symm)
  let f : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hK3).symm
  obtain ⟨θ, θ', -⟩ : ∃ (θ : S ≃* R3) (θ' : S ≃* CFSG.CGT.PushingUpLit.CGT6.EmbG23.G23), True :=
    ⟨E.trans ((CFSG.TauCetiBridge.adjointGroupCongr (τ := .G2) f).trans adjointEquivR3),
      E.trans (CFSG.TauCetiBridge.adjointGroupCongr (τ := .G2) f), trivial⟩
  refine alphaNine_of_inputs hZ (fun σ => ⟨1, ?_⟩) ?_ ?_ (not_dvd_card_of_fix_outer θ')
  · simpa using sq_mem_range_conj_of_card_outer hOutS σ
  · intro b hb
    have hEb : orderOf (E b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
    have hz1 : E b ≠ 1 := fun h => by rw [h, orderOf_one] at hEb; omega
    have hz3 : (E b) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (E b)
      rwa [hEb] at this
    exact RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
      (CFSG.AGLEmbeddingD2.Wilson.Census424Rest.centralizerEquivOfMulEquiv E b).symm
      (isCharacteristicP_centralizer_g2_three hz1 hz3)
  · intro b hb
    have hθb : orderOf (θ b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
    have h := eighty_one_dvd_card_centralizer_R3 (θ b) hθb
    have hcard : Nat.card ↥(Subgroup.centralizer ({b} : Set S)) =
        Nat.card ↥(Subgroup.centralizer ({θ b} : Set R3)) :=
      Nat.card_congr (@CFSG.AGLEmbeddingD2.Wilson.Census424Rest.centralizerEquivOfMulEquiv
        S R3 _ R3.toGroup θ b).toEquiv
    rw [hcard]
    exact h

end R3

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
