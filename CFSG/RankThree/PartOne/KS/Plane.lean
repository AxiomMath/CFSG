module

public import CFSG.RankThree.PartOne.KS.Lines

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open scoped Pointwise commutatorElement

theorem commutator_eq_bot_of_card_le_two {G : Type*} [Group G] [Finite G] {U E : Subgroup G}
    (hU : Nat.card U ≤ 2) (hEU : E ≤ normalizer (U : Set G)) : ⁅U, E⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu e he
  show e * u = u * e
  by_cases hu1 : u = 1
  · rw [hu1]; simp
  have hw : e * u * e⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hEU he) u).mp hu
  by_contra hne
  have hwu : e * u * e⁻¹ ≠ u := fun h => hne (by
    calc e * u = (e * u * e⁻¹) * e := by group
      _ = u * e := by rw [h])
  have hw1 : e * u * e⁻¹ ≠ 1 := fun h => hu1 (by
    have := congrArg (fun z => e⁻¹ * z * e) h
    simpa [mul_assoc] using this)
  have h3 : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨1, ⟨u, hu⟩, ⟨e * u * e⁻¹, hw⟩, fun h => hu1 (congrArg Subtype.val h).symm,
      fun h => hw1 (congrArg Subtype.val h).symm, fun h => hwu (congrArg Subtype.val h).symm⟩
  have : 2 < Nat.card U := by
    have := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.mpr h3
  omega

theorem localCoreProduct_eq_bot_of_model_good_bound {M : Type*} [Group M] [Finite M]
    {P R Q : Subgroup M} (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hQP : Q ≤ P) (hQcard : Nat.card Q = p ^ 2) {x0 : M} (hx0Q : x0 ∈ Q) (hx0 : x0 ≠ 1)
    (hgood : ∀ B : Subgroup M, P ≤ B → B ≤ R →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x0} : Set M)) = ⊥)
    (hbound : ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M))) ≤ 2)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (θ : S ≃* P)
    (hC : centralizer (S : Set X) = ⊥) {E : Subgroup X} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : X} (htE : t ∈ E) (ht1 : t ≠ 1) :
    localCoreProduct p E t = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hinj := h.embed_injective S θ hC
  set ι := h.embed S θ with hι
  have hordE : ∀ e ∈ E, e ≠ 1 → orderOf e = p := fun e he he1 =>
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1
  have hιP : ∀ e ∈ E, ι e ∈ P := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1, map_one]; exact P.one_mem
    · exact (card_core_centralizer_eq_of_model h hidx hp hp2 S θ hC e (hordE e he he1)).1
  obtain ⟨S₀, hS₀⟩ := hSyl
  let E'' : Subgroup P := (E.map ι).subgroupOf P
  have hEmapP : E.map ι ≤ P := by
    rintro _ ⟨e, he, rfl⟩
    exact hιP e he
  have hE''card : Nat.card E'' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEmapP).toEquiv,
      Subgroup.card_map_of_injective hinj, hEcard]
  have hE''p : IsPGroup p E'' := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨e, he, hge⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp g.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, ← hge, ← map_pow]
    have : e ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian e he
    rw [this, map_one]
    rfl
  obtain ⟨S', hS'⟩ := hE''p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S'
  have hS'card : Nat.card (S' : Subgroup P) = p ^ 2 := by
    have h1 := Sylow.card_eq_multiplicity S'
    have h0 := Sylow.card_eq_multiplicity S₀
    have hS₀card : Nat.card (S₀ : Subgroup P) = p ^ 2 := by
      rw [hS₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]
    rw [h0] at hS₀card
    rw [h1, hS₀card]
  have hE''eq : E'' = (S' : Subgroup P) :=
    Subgroup.eq_of_le_of_card_ge hS' (by rw [hE''card, hS'card])
  have hx0P : x0 ∈ P := hQP hx0Q
  have hmemS₀ : (⟨x0, hx0P⟩ : P) ∈ (S₀ : Subgroup P) := by
    rw [hS₀]
    exact Subgroup.mem_subgroupOf.mpr hx0Q
  have hmemS' : (MulAut.conj g • (⟨x0, hx0P⟩ : P) : P) ∈ (S' : Subgroup P) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmemS₀
  rw [← hE''eq] at hmemS'
  obtain ⟨e0, he0E, he0⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hmemS')
  have he0' : ι e0 = (g : M) * x0 * (g : M)⁻¹ := by
    rw [he0]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have he01 : e0 ≠ 1 := by
    intro h1
    rw [h1, map_one] at he0'
    apply hx0
    have := congrArg (fun z => (g : M)⁻¹ * z * (g : M)) he0'
    simpa [mul_assoc] using this.symm
  obtain ⟨-, B, hPB, hBR, hcard⟩ :=
    card_core_centralizer_eq_of_model h hidx hp hp2 S θ hC e0 (hordE e0 he0E he01)
  rw [← hι, he0', card_core_conj hp B (hPB g.2) x0, hgood B hPB hBR, Subgroup.card_bot] at hcard
  have hbot0 : inSubgroup (aschbacherSolvableCore p) (centralizer ({e0} : Set X)) = ⊥ :=
    Subgroup.card_eq_one.mp hcard
  have hI : thetaT p E = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hbot0]
    exact iInf_le_of_le e0 (iInf_le_of_le he0E (iInf_le_of_le he01 le_rfl))
  obtain ⟨hιtP, Bt, hPBt, hBtR, hcardt⟩ :=
    card_core_centralizer_eq_of_model h hidx hp hp2 S θ hC t (hordE t htE ht1)
  have hUcard : Nat.card (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({t} : Set X))) ≤ 2 := by
    rw [hcardt]
    exact hbound Bt hPBt hBtR _ hιtP (by rw [← hι, orderOf_injective _ hinj, hordE t htE ht1])
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hEC : E ≤ centralizer ({t} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hEcomm x hx t htE)
  have hEU : E ≤ normalizer (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({t} : Set X)) : Set X) :=
    hEC.trans (le_normalizer.trans
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _))
  rw [localCoreProduct, hI, commutator_eq_bot_of_card_le_two hUcard hEU]
  simp

end CFSG.RankThree.PartOne
