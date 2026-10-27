module

public import CFSG.Quasithin.H13.NQCatG24Split
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus

public section

namespace CFSG.Quasithin.H13.NQCat.G24X3

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.LieType.BorelTits CFSG.LieType.Chevalley.ExceptionalCover

section Abstract

variable {G G' : Type*} [Group G] [Group G']

def X3 (M : Subgroup G) : Prop :=
  ∃ x ∈ M, orderOf x = 3 ∧ ∀ k ∈ perfectCore M, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)

theorem pCoreOf_map_of_inj (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem X3.map [Finite G] [Finite G'] {M : Subgroup G} (h : X3 M) (f : G →* G')
    (hf : Function.Injective f) : X3 (M.map f) := by
  obtain ⟨x, hxM, hx3, hx⟩ := h
  refine ⟨f x, Subgroup.mem_map_of_mem f hxM, (orderOf_injective f hf x).trans hx3, ?_⟩
  rw [← map_perfectCore, pCoreOf_map_of_inj f hf]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨_, hx k hk, by simp only [map_mul, map_inv]⟩

theorem X3.of_map [Finite G] [Finite G'] {M : Subgroup G} (f : G →* G')
    (hf : Function.Injective f) (h : X3 (M.map f)) : X3 M := by
  obtain ⟨_, ⟨x, hxM, rfl⟩, hx3, hx⟩ := h
  refine ⟨x, hxM, (orderOf_injective f hf x).symm.trans hx3, fun k hk => ?_⟩
  have h1 := hx (f k) (by rw [← map_perfectCore]; exact Subgroup.mem_map_of_mem f hk)
  rw [← map_perfectCore, pCoreOf_map_of_inj f hf] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x * k * x⁻¹ * k⁻¹ := hf (by rw [hyx]; simp only [map_mul, map_inv])
  rwa [this] at hy

theorem mem_pCoreOf_of_parabolicFacts [Finite G] {P Q : Subgroup G} (hF : ParabolicFacts P Q)
    {x : G} (hxP : x ∈ P) (hx : ∀ k ∈ P, x * k * x⁻¹ * k⁻¹ ∈ Q) :
    ∀ k ∈ perfectCore P, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore P) := by
  intro k hk
  have hPN : P ≤ Subgroup.normalizer (perfectCore P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hconj : ∀ g ∈ P, ∀ k ∈ perfectCore P, g * k * g⁻¹ * k⁻¹ ∈ perfectCore P :=
    fun g hg k hk => (perfectCore P).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hPN hg) k).mp hk) ((perfectCore P).inv_mem hk)
  rcases hF.levi with h | ⟨h, -⟩
  ·
    exact le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (hF.pGroup.to_le h)
      (hconj x hxP k hk)
  ·
    have hQ : Q ≤ perfectCore P := by
      refine h.trans ((Subgroup.commutator_le).2 fun q hq p hp => ?_)
      rw [commutatorElement_def]
      exact hconj q (hF.le hq) p hp
    exact le_pCoreOf_of_le_normalizer 2 hQ ((perfectCore_le P).trans hF.normalizes) hF.pGroup
      (hx k (perfectCore_le P hk))

end Abstract

section Model

variable {K : Type} [Field K]

theorem units_pow_three (hK : Nat.card K = 4) (t : Kˣ) : t ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h]
  exact pow_card_eq_one'

theorem rootChar_neg_eq_inv {τ : Tag} (α : Fin τ.rank → ℤ) (s : Fin τ.rank → Kˣ) :
    rootChar K (-α) s = (rootChar K α s)⁻¹ := by
  simp only [rootChar_apply, cartanCoord, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    zpow_neg, Finset.prod_inv_distrib]

theorem torusVec_mem_torusGroup
    {τ : Tag} (t : Fin τ.rank → Kˣ) : torusVec τ K t ∈ torusGroup τ K := by
  induction t using torusVec_induction with
  | h1 => rw [map_one]; exact one_mem _
  | hmul t t' ht ht' => rw [map_mul]; exact mul_mem ht ht'
  | hsingle k s => rw [torusVec_mulSingle]; exact torusElt_mem_torusGroup k s

theorem exists_comm_mem_parabolicRadical
    [Finite K] (hK : Nat.card K = 4) (i : Fin Tag.G2.rank) :
    ∃ x ∈ parabolicSubgroup Tag.G2 K {i}, orderOf x = 3 ∧
      ∀ k ∈ parabolicSubgroup Tag.G2 K {i},
        x * k * x⁻¹ * k⁻¹ ∈ parabolicRadical Tag.G2 K {i} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := G2.exists_units_ne_one hK.ge
  have h3 := units_pow_three hK
  obtain ⟨s, β, hβ, hs, hsβ⟩ : ∃ (s : Fin Tag.G2.rank → Kˣ) (β : Fin Tag.G2.rank → ℤ),
      IsRoot Tag.G2 β ∧ rootChar K (Pi.single i 1) s = 1 ∧ rootChar K β s = ω := by
    rcases G2.fin_two_cases i with rfl | rfl
    · refine ⟨Pi.mulSingle G2.i1 ω, -Pi.single G2.i1 1, isRoot_neg_single _ _, ?_, ?_⟩
      · rw [rootChar_mulSingle,
          show cartanCoord (Pi.single G2.i0 (1 : ℤ)) G2.i1 = -3 by decide,
          show ω ^ (-3 : ℤ) = (ω ^ 3)⁻¹ by group, h3, inv_one]
      · rw [rootChar_mulSingle,
          show cartanCoord (-Pi.single G2.i1 (1 : ℤ)) G2.i1 = -2 by decide,
          show ω ^ (-2 : ℤ) = ω * (ω ^ 3)⁻¹ by group, h3, inv_one, mul_one]
    · refine ⟨Pi.mulSingle G2.i0 ω⁻¹ * Pi.mulSingle G2.i1 ω, Pi.single G2.i0 1,
        isRoot_single _ _, ?_, ?_⟩
      · rw [map_mul, rootChar_mulSingle, rootChar_mulSingle,
          show cartanCoord (Pi.single G2.i1 (1 : ℤ)) G2.i0 = -1 by decide,
          show cartanCoord (Pi.single G2.i1 (1 : ℤ)) G2.i1 = 2 by decide,
          show ω⁻¹ ^ (-1 : ℤ) * ω ^ (2 : ℤ) = ω ^ 3 by group, h3]
      · rw [map_mul, rootChar_mulSingle, rootChar_mulSingle,
          show cartanCoord (Pi.single G2.i0 (1 : ℤ)) G2.i0 = 2 by decide,
          show cartanCoord (Pi.single G2.i0 (1 : ℤ)) G2.i1 = -3 by decide,
          show ω⁻¹ ^ (2 : ℤ) * ω ^ (-3 : ℤ) = ω * ((ω ^ 3)⁻¹) ^ 2 by group, h3, inv_one,
          one_pow, mul_one]
  set x := torusVec Tag.G2 K s with hxdef
  have hxH : x ∈ torusGroup Tag.G2 K := torusVec_mem_torusGroup s
  have hxP : x ∈ parabolicSubgroup Tag.G2 K {i} :=
    parabolicLevi_le_parabolicSubgroup {i} (torusGroup_le_parabolicLevi {i} hxH)
  have hx3 : x ^ 3 = 1 := by
    have hs3 : s ^ 3 = 1 := funext fun k => by rw [Pi.pow_apply, h3, Pi.one_apply]
    rw [hxdef, ← map_pow, hs3, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have h := torusVec_conj_pinnedX (K := K) hβ s 1
    rw [← hxdef, h1, one_mul, inv_one, mul_one, mul_one, hsβ] at h
    exact hω (Units.ext (pinnedX_injective Tag.G2 K β h).symm)
  have hroot : ∀ α : Fin Tag.G2.rank → ℤ, IsRoot Tag.G2 α → rootChar K α s = 1 →
      ∀ c : K, pinnedX Tag.G2 K α c ∈ Subgroup.centralizer ({x} : Set (ModGL Tag.G2 K)) := by
    intro α hα hαs c
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := torusVec_conj_pinnedX (K := K) hα s c
    rw [← hxdef, hαs, Units.val_one, one_mul] at h
    calc pinnedX Tag.G2 K α c * x = x * pinnedX Tag.G2 K α c * x⁻¹ * x := by rw [h]
      _ = x * pinnedX Tag.G2 K α c := by group
  have hM : parabolicLevi Tag.G2 K {i} ≤ Subgroup.centralizer ({x} : Set (ModGL Tag.G2 K)) := by
    refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup hxH)
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        rw [SetLike.mem_coe, ← pinnedX_single]
        exact hroot _ (isRoot_single _ _) hs c
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        rw [SetLike.mem_coe, ← pinnedX_neg_single]
        exact hroot _ (isRoot_neg_single _ _) (by rw [rootChar_neg_eq_inv, hs, inv_one]) c
  refine ⟨x, hxP, orderOf_eq_prime hx3 hx1, fun k hk => ?_⟩
  have hN := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.G2) (K := K) {i}
  have hMP := parabolicLevi_le_parabolicSubgroup (τ := Tag.G2) (K := K) {i}
  rw [← parabolicRadical_sup_parabolicLevi, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hMP.trans hN)] at hk
  obtain ⟨m, hm, q, hq, rfl⟩ := hk
  have hxm : x * m = m * x := (Subgroup.mem_centralizer_singleton_iff.mp (hM hm)).symm
  have e : x * (m * q) * x⁻¹ * (m * q)⁻¹ = m * (x * q * x⁻¹ * q⁻¹) * m⁻¹ := by
    calc x * (m * q) * x⁻¹ * (m * q)⁻¹ = x * m * q * x⁻¹ * q⁻¹ * m⁻¹ := by group
      _ = m * x * q * x⁻¹ * q⁻¹ * m⁻¹ := by rw [hxm]
      _ = m * (x * q * x⁻¹ * q⁻¹) * m⁻¹ := by group
  rw [e]
  have hxq : x * q * x⁻¹ * q⁻¹ ∈ parabolicRadical Tag.G2 K {i} :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hxP) q).mp hq) (inv_mem hq)
  exact (Subgroup.mem_normalizer_iff.mp (hN (hMP hm)) _).mp hxq

theorem x3_parabolicSubgroup
    [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (i : Fin Tag.G2.rank) : X3 (parabolicSubgroup Tag.G2 K {i}) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨x, hxP, hx3, hx⟩ := exists_comm_mem_parabolicRadical hK i
  have hK' : Nat.card K = 2 ^ 2 := hK
  have hF : ParabolicFacts (parabolicSubgroup Tag.G2 K {i}) (parabolicRadical Tag.G2 K {i}) := by
    rcases G2.fin_two_cases i with rfl | rfl
    · exact G2.parabolicFacts_zero hK' le_rfl
    · exact G2.parabolicFacts_one hK' le_rfl
  exact ⟨x, hxP, hx3, mem_pCoreOf_of_parabolicFacts hF hxP hx⟩

end Model

section Amalgam

theorem exists_eq_parabolic_g2
    {Y : Type} [Group Y] {f : ℕ}
    (hYm : ChevalleyExceptionalModel Y .G2 2 f) {T M₁ M : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ (θ : ↥(adjointGroup Tag.G2 K) ≃* Y) (i : Fin Tag.G2.rank),
        M = ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map
          θ.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : Holds Y 2 := holds_of_chevalleyExceptionalModel_untwisted hYm (by decide) (by decide)
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hYm
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  set C := adjointGroup Tag.G2 K with hC
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf C) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  have hRS : ∀ j : Fin 2, G24Split.RootSplit
      (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf C).map e.symm.toMonoidHom)
      (((parabolicRadical Tag.G2 K {g2Index j}).subgroupOf C).map e.symm.toMonoidHom)
      (((CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (Pi.single (g2Index j) 1)).subgroupOf
        C).map e.symm.toMonoidHom) (2 ^ f) := fun j =>
    ((G24Split.rootSplit_g2 hK hf (g2Index j)).subgroupOf
      (parabolicSubgroup_le_adjointGroup _ _ _)).map _ e.symm.injective
  obtain ⟨hM, hTM⟩ := (hpair.2.2 M).2 (Or.inr rfl)
  obtain ⟨j, g, rfl⟩ := G24Split.exists_eq_map_conj_of_isMaximalTwoLocal
    (G24Split.isSylowTwoOf_top_map hU₀ e.symm) (G2_residualOvergroupsAt.map e.symm) hBT
    (Q := fun j => ((parabolicRadical Tag.G2 K {g2Index j}).subgroupOf C).map
      e.symm.toMonoidHom)
    (fun j => ⟨fun h0 => by
        obtain ⟨x, hx, y, -, hxy⟩ := (hRS j).facts.nonabelian
        rw [h0, Subgroup.mem_bot] at hx
        exact hxy (by rw [hx, one_mul, mul_one]),
      (hRS j).facts.pGroup, (hRS j).facts.normalizes⟩) hpair.1 hM hTM
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, e.symm.trans (MulAut.conj g),
    g2Index j, ?_⟩
  rw [Subgroup.map_map]
  rfl

theorem x3_of_isYAmalgamPair
    {Y : Type} [Group Y] (hY : IsLieOverTwo .G2 0 2 Y)
    {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M) :
    ∃ x ∈ M, orderOf x = 3 ∧
      ∀ k ∈ perfectCore M, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M) := by
  have hYm : ChevalleyExceptionalModel Y .G2 2 2 := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  obtain ⟨K, _, _, _, hK, θ, i, rfl⟩ := exists_eq_parabolic_g2 hYm hpair
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite Y := Finite.of_equiv _ θ.toEquiv
  have h1 : X3 ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)) := by
    refine X3.of_map (adjointGroup Tag.G2 K).subtype (adjointGroup Tag.G2 K).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup _ _ _)]
    exact x3_parabolicSubgroup hK i
  exact h1.map θ.toMonoidHom θ.injective

theorem factX3ParabolicG2_holds :
    FactX3ParabolicG2 :=
  fun _ _ _ _ _ hY hpair _ => x3_of_isYAmalgamPair hY hpair

end Amalgam

end CFSG.Quasithin.H13.NQCat.G24X3
