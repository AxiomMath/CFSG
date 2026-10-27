module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Ex2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

theorem card_nonsingular (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    Nat.card ↥(Nonsingular P) = 6 := by
  have hr := h.rk_commV_plane hp
  have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hp.2.2.2.2.2.1
  have e : Nonsingular P = ((commV P₁ : Set V) ∪ (commV P₂ : Set V)) \ {1} := by
    rw [h.nonsingular_eq hp]
    ext v
    constructor
    · rintro ⟨hv1, hv⟩
      exact ⟨hv, hv1⟩
    · rintro ⟨hv, hv1⟩
      exact ⟨hv1, hv⟩
  have hinter : (commV P₁ : Set V) ∩ (commV P₂ : Set V) = {1} := by
    ext v
    constructor
    · intro hv
      have : v ∈ commV P₁ ⊓ commV P₂ := hv
      rw [hinf, Subgroup.mem_bot] at this
      exact this
    · rintro rfl
      exact ⟨(commV P₁).one_mem, (commV P₂).one_mem⟩
  have hc₁ : (commV P₁ : Set V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_eq_two_pow h.sq (commV P₁)).trans (by rw [hr.1]; norm_num)
  have hc₂ : (commV P₂ : Set V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_eq_two_pow h.sq (commV P₂)).trans (by rw [hr.2]; norm_num)
  have hu := Set.ncard_union_add_ncard_inter (commV P₁ : Set V) (commV P₂ : Set V)
    (Set.toFinite _) (Set.toFinite _)
  rw [hinter, Set.ncard_singleton, hc₁, hc₂] at hu
  have h1 : (1 : V) ∈ (commV P₁ : Set V) ∪ (commV P₂ : Set V) := Or.inl (commV P₁).one_mem
  rw [Nat.card_coe_set_eq, e, Set.ncard_sdiff_singleton_of_mem h1]
  omega

theorem card_stabilizer_nonsingular (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) {k : V}
    (hk : k ∈ Nonsingular P) : Nat.card ↥(MulAction.stabilizer ↥X k) = 6 := by
  have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥X k)
  rw [Nat.card_prod, h.card_X] at h1
  have horb : Nat.card ↥(MulAction.orbit ↥X k) = 6 := by
    have e : (MulAction.orbit ↥X k : Set V) = Nonsingular P := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact h.nonsingular_stable x.2 hk
      · intro hv
        obtain ⟨x, hx, hxv⟩ := h.nonsingular_transitive hk hv
        exact ⟨⟨x, hx⟩, hxv⟩
    rw [e]
    exact h.card_nonsingular hp
  rw [horb] at h1
  omega

end E9Z4Str

section Group

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem relIndex_pCoreOf_HLb
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {L : Subgroup (MulAut ↥(kOf (rhoH h)))} (hL : L ≤ (resBeta (rhoH h)).range) :
    (pCoreOf 2 H).relIndex (HLb (resBeta (rhoH h)) L) = Nat.card L := by
  have hQeq : ((HLb (resBeta (rhoH h)) L).subgroupOf H).map (resBeta (rhoH h)) = L := by
    rw [subgroupOf_HLb, Subgroup.map_comap_eq, inf_eq_right.mpr hL]
  have h1 := (Subgroup.relIndex_ker ((HLb (resBeta (rhoH h)) L).subgroupOf H)
    (resBeta (rhoH h))).symm
  rw [hQeq, ker_resBeta_eq h hsplit, Subgroup.relIndex_subgroupOf (HLb_le L)] at h1
  exact h1.symm

theorem tZero_eq_of_plane
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h)))
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb)
    (hidx : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex T = 2)
    {u : G} (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Qa)) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) ≤ tZero T u) :
    tZero T u = T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G) := by
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  have hnot : ¬ T ≤ tZero T u := by
    intro hT
    obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr hUu hu
    have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h hUu).mp (by rw [← hkc, e]; rfl))
    have hfix : ∀ y ∈ Tb, y k = k := by
      intro y hy
      obtain ⟨x, hxT', rfl⟩ := Subgroup.mem_map.mp (hTb ▸ hy)
      have hc := (hT (Subgroup.mem_subgroupOf.mp hxT')).2.2 u (Subgroup.mem_zpowers u)
      have hρ := (rhoH_clsU_eq_iff h x hUu).mpr hc
      refine Subtype.ext ((resBeta_apply _ _ _).trans ?_)
      rw [hkc]
      exact hρ
    exact ((hstr.fixV_Tb hp).2 k hfix hk1).1 hk
  have hA : tZero T u ≤ T := centralizerMod_le_left _ _ _
  have hdvd : (tZero T u).relIndex T ∣
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex T :=
    Subgroup.relIndex_dvd_of_le_left T huT
  rw [hidx] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.mp h1) hnot
  · have hmul := Subgroup.relIndex_mul_relIndex _ _ _ huT hA
    rw [h2, hidx] at hmul
    have h1 : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h)) Qa : Set G)).relIndex
        (tZero T u) = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) huT

end Group

end CFSG.Quasithin
