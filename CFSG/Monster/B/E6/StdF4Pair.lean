module

public import CFSG.Monster.B.E6.StdF4PairCount
public import CFSG.Monster.B.E6.StdF4PairPlanes
public import CFSG.Monster.B.E6.StdF4PairRoot

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft thetaFirst)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical Module
open CFSG.Monster.B.E6.FixedE6 (V fixedL formL)
open CFSG.Monster.B.E6.FixedE6Root (rootVecOf a0 a0L)

theorem parLeft_one :
    parLeft (1 : parStar firstJ) = 1 := Subtype.ext rfl

theorem fibSub_conj_of_eq
    {d : Fin 5} (hd : IsMid d) {k : Fin 3} (hk : fibKd d = k)
    (γ : parStar firstJ) :
    fibSub d ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) =
      flagSub k (parLeft γ) := by
  rw [← hk]
  exact fibSub_conj hd γ

theorem fibSub_conj_conj_of_eq
    {d : Fin 5} (hd : IsMid d) {k : Fin 3} (hk : fibKd d = k)
    (γ γ' : parStar firstJ) :
    fibSub d ((γ' : GStar) * ((γ : GStar) * SemidirectProduct.inl (fibT d) *
      (γ : GStar)⁻¹) * (γ' : GStar)⁻¹) =
      (thetaFirst γ' • residueFlag (QuotientGroup.mk (parLeft γ))).sub k := by
  rw [← hk]
  exact fibSub_conj_conj hd γ γ'

theorem fibSub_conj_one
    (γ : parStar firstJ) :
    fibSub 1 ((γ : GStar) * SemidirectProduct.inl (fibT 1) * (γ : GStar)⁻¹) =
      flagSub 2 (parLeft γ) :=
  fibSub_conj_of_eq (d := 1) (k := 2) (Or.inl rfl) rfl γ

theorem fibSub_conj_two
    (γ : parStar firstJ) :
    fibSub 2 ((γ : GStar) * SemidirectProduct.inl (fibT 2) * (γ : GStar)⁻¹) =
      flagSub 0 (parLeft γ) :=
  fibSub_conj_of_eq (d := 2) (k := 0) (Or.inr (Or.inl rfl)) rfl γ

theorem fibSub_conj_conj_one
    (γ γ' : parStar firstJ) :
    fibSub 1 ((γ' : GStar) * ((γ : GStar) * SemidirectProduct.inl (fibT 1) *
      (γ : GStar)⁻¹) * (γ' : GStar)⁻¹) =
      (thetaFirst γ' • residueFlag (QuotientGroup.mk (parLeft γ))).sub 2 :=
  fibSub_conj_conj_of_eq (d := 1) (k := 2) (Or.inl rfl) rfl γ γ'

theorem fibSub_two_fibT :
    fibSub 2 (SemidirectProduct.inl (fibT 2)) = basePoint := by
  have h := fibSub_conj_two 1
  rw [OneMemClass.coe_one, one_mul, inv_one, mul_one, parLeft_one] at h
  rw [h]
  exact flagSub_one 0

theorem fibSub_mem_isoSubs_two
    {p : GStar} (hp : p ∈ fibOrbit 1) : fibSub 1 p ∈ isoSubs 2 := by
  have h := Set.mem_image_of_mem (fibSub 1) hp
  rwa [image_fibSub (Or.inl rfl)] at h

theorem commute_of_basePoint_le
    {p : GStar} (hp : p ∈ fibOrbit 1) (h : basePoint ≤ fibSub 1 p) :
    Commute p (SemidirectProduct.inl (fibT 2)) := by
  have hmid1 : IsMid 1 := Or.inl rfl
  obtain ⟨l, hl, hlT⟩ := exists_fibLevi_flagSub (fibSub_mem_isoSubs_two hp) h
  have hlG : (l : ModGL Tag.E6 K) ∈ stdGroup := nativeParabolic_le_stdGroup firstJ l.2
  set c : GStar := SemidirectProduct.inl (⟨l, hlG⟩ : stdGroup)
  have hcP : c ∈ parStar firstJ := l.2
  have hcC : c ∈ fibCent 2 := fibLStar_le 2 (show c ∈ fibLStar 2 from hl)
  have hc : c * SemidirectProduct.inl (fibT 2) * c⁻¹ = SemidirectProduct.inl (fibT 2) := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcC).2,
      mul_inv_cancel_right]
  have hx : c * SemidirectProduct.inl (fibT 1) * c⁻¹ ∈ fibOrbit 1 := ⟨c, hcP, rfl⟩
  have hsub : fibSub 1 (c * SemidirectProduct.inl (fibT 1) * c⁻¹) = fibSub 1 p := by
    rw [fibSub_conj_one ⟨c, hcP⟩, ← hlT]
    rfl
  obtain ⟨u, hu, rfl⟩ := (fibSub_eq_iff hmid1 hx hp).1 hsub
  have hu' : c⁻¹ * u * c ∈ radStar := by
    have := conj_mem_radStar (inv_mem hcP) hu
    rwa [inv_inv] at this
  have hy : (c⁻¹ * u * c) * SemidirectProduct.inl (fibT 1) * (c⁻¹ * u * c)⁻¹ ∈
      conjOrbit radStar (SemidirectProduct.inl (fibT 1)) := ⟨_, hu', rfl⟩
  have hcomm := commute_of_mem_conjOrbit_fibT_one hy
  have e : u * (c * SemidirectProduct.inl (fibT 1) * c⁻¹) * u⁻¹ =
      c * ((c⁻¹ * u * c) * SemidirectProduct.inl (fibT 1) * (c⁻¹ * u * c)⁻¹) * c⁻¹ := by
    group
  rw [e, ← hc]
  exact (Commute.conj_iff c).2 hcomm

theorem commute_fibT_two_iff
    {p : GStar} (hp : p ∈ fibOrbit 1) :
    Commute p (SemidirectProduct.inl (fibT 2)) ↔ basePoint ≤ fibSub 1 p := by
  have hsub : {p | p ∈ fibOrbit 1 ∧ basePoint ≤ fibSub 1 p} ⊆
      {p | p ∈ fibOrbit 1 ∧ Commute p (SemidirectProduct.inl (fibT 2))} :=
    fun p hp => ⟨hp.1, commute_of_basePoint_le hp.1 hp.2⟩
  have hset : {p | p ∈ fibOrbit 1 ∧ basePoint ≤ fibSub 1 p} =
      {p | p ∈ fibOrbit 1 ∧ fibSub 1 p ∈ {T | T ∈ isoSubs 2 ∧ basePoint ≤ T}} := by
    ext p
    exact ⟨fun h => ⟨h.1, fibSub_mem_isoSubs_two h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hcard : {p | p ∈ fibOrbit 1 ∧ Commute p (SemidirectProduct.inl (fibT 2))}.ncard ≤
      {p | p ∈ fibOrbit 1 ∧ basePoint ≤ fibSub 1 p}.ncard := by
    have h1 := ncard_commute_fibOrbit_one (q := SemidirectProduct.inl (fibT 2))
      (mem_conjOrbit_self _ _)
    have h2 : {p | p ∈ fibOrbit 1 ∧ basePoint ≤ fibSub 1 p}.ncard = 2 * 27 := by
      rw [hset, ncard_fibSub_preimage fun _ hT => hT.1, ncard_planes_basePoint]
    rw [h1, h2]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  refine ⟨fun hc => ?_, commute_of_basePoint_le hp⟩
  have hmem : p ∈ {p | p ∈ fibOrbit 1 ∧ Commute p (SemidirectProduct.inl (fibT 2))} := ⟨hp, hc⟩
  rw [← heq] at hmem
  exact hmem.2

theorem commute_iff_fibSub_le
    {p q : GStar} (hp : p ∈ fibOrbit 1) (hq : q ∈ fibOrbit 2) :
    Commute p q ↔ fibSub 2 q ≤ fibSub 1 p := by
  obtain ⟨γ, hγ, rfl⟩ := hq
  obtain ⟨δ, hδ, rfl⟩ := hp
  have hε : γ⁻¹ * δ ∈ parStar firstJ := mul_mem (inv_mem hγ) hδ
  have hp' : (γ⁻¹ * δ) * SemidirectProduct.inl (fibT 1) * (γ⁻¹ * δ)⁻¹ ∈ fibOrbit 1 :=
    ⟨_, hε, rfl⟩
  have e1 : δ * SemidirectProduct.inl (fibT 1) * δ⁻¹ =
      γ * ((γ⁻¹ * δ) * SemidirectProduct.inl (fibT 1) * (γ⁻¹ * δ)⁻¹) * γ⁻¹ := by group
  rw [e1, Commute.conj_iff, commute_fibT_two_iff hp', fibSub_conj_one ⟨_, hε⟩,
    fibSub_conj_conj_one ⟨_, hε⟩ ⟨γ, hγ⟩, fibSub_conj_two ⟨γ, hγ⟩, flagSub, flagSub,
    residueFlag_parLeft ⟨γ, hγ⟩]
  exact (SUFrob_smul_sub_le_iff (thetaFirst ⟨γ, hγ⟩) baseFlag _ 0 2).symm

theorem setOf_commute_eq
    {q : GStar} (hq : q ∈ fibOrbit 2) :
    {p | p ∈ fibOrbit 1 ∧ Commute p q} =
      {p | p ∈ fibOrbit 1 ∧ fibSub 1 p ∈ {T | T ∈ isoSubs 2 ∧ fibSub 2 q ≤ T}} := by
  ext p
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, fibSub_mem_isoSubs_two hp, (commute_iff_fibSub_le hp hq).1 hc⟩
  · rintro ⟨hp, -, h⟩
    exact ⟨hp, (commute_iff_fibSub_le hp hq).2 h⟩

theorem ncard_planes_fibSub
    {q : GStar} (hq : q ∈ fibOrbit 2) :
    {T | T ∈ isoSubs 2 ∧ fibSub 2 q ≤ T}.ncard = 27 := by
  have h := ncard_commute_fibOrbit_one hq
  rw [setOf_commute_eq hq, ncard_fibSub_preimage fun _ hT => hT.1] at h
  omega

theorem standard_parabolic_point_plane_commutation_and_root_pairs :
    (∀ p q : stdGroup, p ∈ rootClass → q ∈ rootClass →
      (formL (rootVecOf p) (rootVecOf q) = 1 ↔ orderOf (p * q) = 3)) ∧
    (∀ x ∈ fibOrbit 1, (conjOrbit radStar x).ncard = 2 ∧
      (fun y : GStar => rootVecOf y.left) '' conjOrbit radStar x =
        {rootVecOf x.left, rootVecOf x.left + a0L}) ∧
    (a0L : V) = a0 ∧ a0 = rootVec Tag.E6 K theta ∧
    (∀ p ∈ fibOrbit 1, ∀ q ∈ fibOrbit 2, Commute p q ↔ fibSub 2 q ≤ fibSub 1 p) ∧
    (∀ q ∈ fibOrbit 2, fibSub 2 q ∈ isoSubs 0) ∧ (∀ p ∈ fibOrbit 1, fibSub 1 p ∈ isoSubs 2) ∧
    ∀ q ∈ fibOrbit 2,
      {p | p ∈ fibOrbit 1 ∧ Commute p q}.ncard = 54 ∧
      {T | T ∈ isoSubs 2 ∧ fibSub 2 q ≤ T}.ncard = 27 ∧
      ∀ T ∈ isoSubs 2, fibSub 2 q ≤ T →
        {p | p ∈ fibOrbit 1 ∧ fibSub 1 p = T}.ncard = 2 ∧
        ∀ p ∈ fibOrbit 1, fibSub 1 p = T → Commute p q := by
  refine ⟨fun p q hp hq => formL_rootVecOf_eq_one_iff hp hq, fun x hx =>
    ⟨ncard_conjOrbit_radStar hx, image_rootVec_conjOrbit hx⟩, rfl, rfl,
    fun p hp q hq => commute_iff_fibSub_le hp hq, fun q hq => ?_,
    fun p hp => fibSub_mem_isoSubs_two hp, fun q hq =>
      ⟨ncard_commute_fibOrbit_one hq, ncard_planes_fibSub hq, fun T hT hqT =>
        ⟨ncard_fibSub_eq hT, fun p hp hpT => (commute_iff_fibSub_le hp hq).2 (hpT ▸ hqT)⟩⟩⟩
  have h := Set.mem_image_of_mem (fibSub 2) hq
  rwa [image_fibSub (Or.inr (Or.inl rfl))] at h

end CFSG.Monster.B.E6.StdF4
