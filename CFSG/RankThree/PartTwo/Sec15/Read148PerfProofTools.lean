module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.Read148Perf

open scoped commutatorElement

@[expose] def CubeComm (T : Type*) [Group T] : Prop :=
  ∀ t : T, t ^ 3 ∈ commutator T

section Basic

variable {T T' : Type*} [Group T] [Group T']

theorem commutator_le_self (X : Subgroup T) : ⁅X, X⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem map_subtype_commutator (X : Subgroup T) : (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commute_of_commutator_eq_bot {U V : Subgroup T} (hcomm : ⁅U, V⁆ = ⊥) {u v : T}
    (hu : u ∈ U) (hv : v ∈ V) : Commute u v :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu) v hv).symm

theorem exists_mul_of_mem_sup {U V : Subgroup T} (hcomm : ⁅U, V⁆ = ⊥) {t : T}
    (ht : t ∈ U ⊔ V) : ∃ u ∈ U, ∃ v ∈ V, u * v = t := by
  have hUV : U ≤ Subgroup.centralizer (V : Set T) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have ht' : t ∈ ((U ⊔ V : Subgroup T) : Set T) := ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U V
    (hUV.trans (Subgroup.centralizer_le_normalizer _))] at ht'
  exact Set.mem_mul.mp ht'

theorem le_normalizer_of_conj {B H : Subgroup T} (h : ∀ b ∈ B, ∀ x ∈ H, b * x * b⁻¹ ∈ H) :
    B ≤ Subgroup.normalizer (H : Set T) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h b hb x, fun hx => ?_⟩
  have h1 := h b⁻¹ (inv_mem hb) _ hx
  rwa [inv_inv, show b⁻¹ * (b * x * b⁻¹) * b = x by group] at h1

theorem CubeComm.of_surjective (h : CubeComm T) {f : T →* T'} (hf : Function.Surjective f) :
    CubeComm T' := by
  intro t'
  obtain ⟨t, rfl⟩ := hf t'
  have hmap : (commutator T).map f = commutator T' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  rw [← map_pow, ← hmap]
  exact Subgroup.mem_map_of_mem f (h t)

theorem CubeComm.of_mulEquiv (h : CubeComm T') (e : T ≃* T') : CubeComm T :=
  h.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem CubeComm.of_isPerfect (h : Group.IsPerfect T) : CubeComm T := fun t => by
  rw [h.commutator_eq_top]
  exact Subgroup.mem_top _

theorem CubeComm.of_isSimpleGroup [IsSimpleGroup T] (h3 : 3 ∣ Nat.card T) : CubeComm T := by
  intro t
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T) with h | h
  · have hc : IsMulCommutative T := by
      refine ⟨⟨fun a b => ?_⟩⟩
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a (Subgroup.mem_top a)
    have hp : (Nat.card T).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    have h3' : 3 = Nat.card T := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    rw [h3', pow_card_eq_one']
    exact one_mem _
  · rw [h]
    exact Subgroup.mem_top _

theorem CubeComm.of_isTripleCover {S : Type*} [Group S] (h : Sec4.IsTripleCover T S)
    (hS : Group.IsPerfect S) : CubeComm T := by
  obtain ⟨hZ, ⟨φ⟩⟩ := h
  have hQ : Group.IsPerfect (T ⧸ Subgroup.center T) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hmap : (commutator T).map (QuotientGroup.mk' (Subgroup.center T)) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def]
    exact hQ.commutator_eq_top
  intro t
  have ht : QuotientGroup.mk' (Subgroup.center T) t ∈
      (commutator T).map (QuotientGroup.mk' (Subgroup.center T)) :=
    hmap ▸ Subgroup.mem_top _
  obtain ⟨c, hc, hct⟩ := ht
  have hz : c⁻¹ * t ∈ Subgroup.center T := QuotientGroup.eq.mp hct
  have hz3 : (c⁻¹ * t) ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := (⟨c⁻¹ * t, hz⟩ : Subgroup.center T))
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hcz : Commute c (c⁻¹ * t) := Subgroup.mem_center_iff.mp hz c
  have htz : t = c * (c⁻¹ * t) := by rw [mul_inv_cancel_left]
  rw [htz, hcz.mul_pow, hz3, mul_one]
  exact pow_mem hc 3

theorem CubeComm.prod (hT : CubeComm T) (hT' : CubeComm T') : CubeComm (T × T') := by
  rintro ⟨t, t'⟩
  have hc : commutator (T × T') = (commutator T).prod (commutator T') := by
    rw [commutator_def, show (⊤ : Subgroup (T × T')) = (⊤ : Subgroup T).prod (⊤ : Subgroup T') from
      Subgroup.top_prod_top.symm, Subgroup.commutator_prod_prod, ← commutator_def,
      ← commutator_def]
  rw [hc, Prod.pow_mk]
  exact Subgroup.mem_prod.mpr ⟨hT t, hT' t'⟩

theorem cubeComm_subgroup_iff {X : Subgroup T} : CubeComm ↥X ↔ ∀ x ∈ X, x ^ 3 ∈ ⁅X, X⁆ := by
  constructor
  · intro h x hx
    rw [← map_subtype_commutator]
    exact ⟨_, h ⟨x, hx⟩, rfl⟩
  · intro h x
    have hx := h x x.2
    rw [← map_subtype_commutator] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x ^ 3 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyx)
    exact this ▸ hy

theorem pow_three_mem_commutator {U : Subgroup T} (hU : CubeComm ↥U) {u : T} (hu : u ∈ U) :
    u ^ 3 ∈ commutator T := by
  have h := cubeComm_subgroup_iff.mp hU u hu
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_top h

theorem CubeComm.of_sup {U V : Subgroup T} (hsup : U ⊔ V = ⊤) (hcomm : ⁅U, V⁆ = ⊥)
    (hU : CubeComm ↥U) (hV : CubeComm ↥V) : CubeComm T := by
  intro t
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup ▸ Subgroup.mem_top t)
  rw [(commute_of_commutator_eq_bot hcomm hu hv).mul_pow]
  exact mul_mem (pow_three_mem_commutator hU hu) (pow_three_mem_commutator hV hv)

end Basic

theorem commutator_eq_self_of_cube {Γ : Type*} [Group Γ] {X : Subgroup Γ}
    {S : Set (Subgroup Γ)} (hXS : X ≤ sSup S) (hSX : ∀ Q ∈ S, Q ≤ X)
    (hS3 : ∀ Q ∈ S, Nat.Coprime (Nat.card Q) 3) (hcube : ∀ x ∈ X, x ^ 3 ∈ ⁅X, X⁆) :
    ⁅X, X⁆ = X := by
  refine le_antisymm (commutator_le_self X) (hXS.trans (sSup_le fun Q hQ y hy => ?_))
  have hco : Nat.Coprime 3 (orderOf y) :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard Q hy) (hS3 Q hQ)).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
  rw [← hm]
  exact pow_mem (hcube y (hSX Q hQ hy)) m

end CFSG.RankThree.PartTwo.Sec15.Read148Perf
