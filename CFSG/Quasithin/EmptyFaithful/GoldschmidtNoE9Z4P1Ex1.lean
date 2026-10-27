module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

theorem relIndex_normalizer_Tb (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    (Subgroup.normalizer (P₁ : Set (MulAut V))).relIndex Tb = 2 := by
  have hp' := hp
  obtain ⟨t, htT, ht2, -⟩ := h.inv
  obtain ⟨hP₁, hP₂, hc₁, hc₂, hsup, hdisj, hcsup, hf₁, hf₂, σ, hσ, hσP⟩ := hp
  have htn : t ∈ Subgroup.normalizer (P₁ : Set (MulAut V)) :=
    h.zpowers_le_normalizer_of_le (h.Tb_le_X htT) ht2 hP₁ (Subgroup.mem_zpowers t)
  have hσn : σ ∉ Subgroup.normalizer (P₁ : Set (MulAut V)) := by
    intro hn
    have hconj : conjBy σ P₁ = P₁ := by
      ext x
      rw [mem_conjBy_iff]
      have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x
      simpa using this.symm
    rw [hσP] at hconj
    have hinf := h.plane_inf_eq_bot hp'
    rw [hconj, inf_idem] at hinf
    have : Nat.card P₁ = 1 := by rw [hinf, Subgroup.card_bot]
    omega
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup (MulAut V),
      N₀ = Tb ⊓ Subgroup.normalizer (P₁ : Set (MulAut V)) := ⟨_, rfl⟩
  have hN₀le : N₀ ≤ Tb := hN₀ ▸ inf_le_left
  have hdvd : Nat.card N₀ ∣ 4 := h.card_Tb ▸ Subgroup.card_dvd_of_le hN₀le
  have hzt : Subgroup.zpowers t ≤ N₀ :=
    Subgroup.zpowers_le.mpr (hN₀ ▸ ⟨htT, htn⟩)
  have h2 : 2 ∣ Nat.card N₀ := by
    have := Subgroup.card_dvd_of_le hzt
    rwa [Nat.card_zpowers, ht2] at this
  have h4 : Nat.card N₀ ≠ 4 := by
    intro h4
    have hNT : N₀ = Tb := Subgroup.eq_of_le_of_card_ge hN₀le (by rw [h4, h.card_Tb])
    have hσN : σ ∈ N₀ := by rw [hNT]; exact hσ
    rw [hN₀] at hσN
    exact hσn hσN.2
  have hle : Nat.card N₀ ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card N₀ := Nat.card_pos
  have hN2 : Nat.card N₀ = 2 := by
    obtain ⟨m, hm⟩ := h2
    omega
  have hmul := Subgroup.relIndex_mul_card N₀ Tb
  rw [inf_eq_left.mpr hN₀le, hN2, h.card_Tb] at hmul
  have hrel : N₀.relIndex Tb = 2 := by omega
  rwa [hN₀, Subgroup.inf_relIndex_left] at hrel

omit [Finite V] in
theorem mem_normalizer_iff_conjBy {g : MulAut V} {Q : Subgroup (MulAut V)} :
    g ∈ Subgroup.normalizer (Q : Set (MulAut V)) ↔ conjBy g Q = Q := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hn
    ext x
    rw [mem_conjBy_iff]
    have := hn (g⁻¹ * x * g)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact this
  · intro h q
    constructor
    · intro hq
      have := mem_conjBy_of_mem (g := g) hq
      rwa [h] at this
    · intro hq
      have : g * q * g⁻¹ ∈ conjBy g Q := by rwa [h]
      rw [mem_conjBy_iff] at this
      have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rwa [e] at this

end E9Z4Str

section Ex

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem subgroupOf_HLb {V' : Type*} [Group V'] (β : ↥H →* MulAut V')
    (Q : Subgroup (MulAut V')) : (HLb β Q).subgroupOf H = Q.comap β := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  exact mem_HLb_iff x.2

theorem HLb_map_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {A : Subgroup G} (hQA : pCoreOf 2 H ≤ A) (hAH : A ≤ H) :
    HLb (resBeta (rhoH h)) ((A.subgroupOf H).map (resBeta (rhoH h))) = A := by
  have hker := ker_resBeta_eq h hsplit
  ext x
  constructor
  · intro hx
    have hxH : x ∈ H := HLb_le _ hx
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp ((mem_HLb_iff hxH).mp hx)
    have hmem : r⁻¹ * ⟨x, hxH⟩ ∈ (resBeta (rhoH h)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have h1 : (r : G)⁻¹ * x ∈ A := hQA hmem
    have e : x = (r : G) * ((r : G)⁻¹ * x) := by group
    rw [e]
    exact A.mul_mem (Subgroup.mem_subgroupOf.mp hr) h1
  · intro hx
    exact (mem_HLb_iff (hAH hx)).mpr ⟨⟨x, hAH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem isPlaneSub_HLb (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h98.toHypF91, ∃ a ∈ kOf (rhoH h98.toHypF91),
      ∃ c ∈ fixV (rhoH h98.toHypF91).range, w = a * c)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91)))}
    (hQP : Q ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) (hQ3 : Nat.card Q = 3)
    (hrk : rk (commV Q) = 2) :
    IsPlaneSub T M H PQ (HLb (resBeta (rhoH h98.toHypF91)) Q) := by
  have hH : IsHTM T M H := hred.isHTM
  have hQrange : Q ≤ (resBeta (rhoH h98.toHypF91)).range := hQP.trans (Subgroup.map_le_range _ _)
  have hRH : HLb (resBeta (rhoH h98.toHypF91)) Q ≤ H := HLb_le Q
  refine ⟨pCoreOf_le_HLb h98.toHypF91 hsplit Q, ?_, ?_, ?_⟩
  · calc HLb (resBeta (rhoH h98.toHypF91)) Q ≤
        HLb (resBeta (rhoH h98.toHypF91)) ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) :=
          HLb_mono hQP
      _ = PQ := HLb_map_eq h98.toHypF91 hsplit hred.lt.le hred.le
  · have hQeq : ((HLb (resBeta (rhoH h98.toHypF91)) Q).subgroupOf H).map
        (resBeta (rhoH h98.toHypF91)) = Q := by
      rw [subgroupOf_HLb, Subgroup.map_comap_eq, inf_eq_right.mpr hQrange]
    have h1 : Nat.card ((((HLb (resBeta (rhoH h98.toHypF91)) Q).subgroupOf H).map
        (resBeta (rhoH h98.toHypF91)) : Subgroup _)) =
        (resBeta (rhoH h98.toHypF91)).ker.relIndex
          ((HLb (resBeta (rhoH h98.toHypF91)) Q).subgroupOf H) :=
      (Subgroup.relIndex_ker _ _).symm
    rw [hQeq, hQ3, ker_resBeta_eq h98.toHypF91 hsplit, Subgroup.relIndex_subgroupOf hRH] at h1
    exact h1.symm
  · have hW := Wsub_uHi_HLb h98.toHypF91 hsplit hQrange
    have hc4 := card_Wsub_uHi S hH h98.toHypF91 hRH
    rw [hW, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hc4
    have hsq : ∀ v : ↥(kOf (rhoH h98.toHypF91)), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using IntMod.sq_eq_one (v : UMod h98.toHypF91))
    rw [card_eq_two_pow hsq (commV Q), hrk] at hc4
    exact (Nat.pow_right_injective (le_refl 2) hc4).symm

theorem mem_normalizer_HLb_iff
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range) {x : ↥H} :
    (x : G) ∈ Subgroup.normalizer (HLb (resBeta (rhoH h)) Q : Set G) ↔
      resBeta (rhoH h) x ∈ Subgroup.normalizer (Q : Set (MulAut ↥(kOf (rhoH h)))) := by
  rw [E9Z4Str.mem_normalizer_iff_conjBy]
  constructor
  · intro hn
    have h1 : conjSub (x : G) (HLb (resBeta (rhoH h)) Q) =
        HLb (resBeta (rhoH h)) (conjBy (resBeta (rhoH h) x) Q) :=
      conjSub_HLb x.2 (fun y => by rw [← mem_conjBy_iff])
    rw [conjSub_eq_of_mem_normalizer hn] at h1
    have hcq : conjBy (resBeta (rhoH h) x) Q ≤ (resBeta (rhoH h)).range := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨b, rfl⟩ := hQ hq
      exact ⟨x * b * x⁻¹, by simp [MulAut.conj_apply]⟩
    exact (HLb_injective hQ hcq h1).symm
  · intro hc
    exact mem_normalizer_of_conjSub_eq' (conjSub_HLb_of_conjBy h hc)

theorem indexT_HLb (hred : IsRedCE T M H PQ p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Tb P P₁ P₂ : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91)))}
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
    (hp : PlanePair Tb P P₁ P₂) (hP₁ : P₁ ≤ (resBeta (rhoH h98.toHypF91)).range)
    (hstr : E9Z4Str (resBeta (rhoH h98.toHypF91)).range Tb P) :
    (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) P₁ : Set G)).relIndex T = 2 := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have h1 := (Subgroup.relIndex_subgroupOf (H := T ⊓ Subgroup.normalizer
    (HLb (resBeta (rhoH h98.toHypF91)) P₁ : Set G)) hTH).symm
  rw [h1]
  have h2 : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) P₁ : Set G)).subgroupOf H =
      (Subgroup.normalizer (P₁ : Set _)).comap (resBeta (rhoH h98.toHypF91)) ⊓
        T.subgroupOf H := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.mem_subgroupOf, mem_normalizer_HLb_iff h98.toHypF91 hP₁]
    exact and_comm
  rw [h2, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap, ← hTb]
  exact hstr.relIndex_normalizer_Tb hp

end Ex

end CFSG.Quasithin
