module

public import CFSG.Quasithin.EmptyFaithful.S143VO4
public import CFSG.Quasithin.EmptyFaithful.S143EA
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.EmptyFaithful.S143VNo
public import CFSG.Quasithin.EmptyFaithful.S143VSq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
  CFSG.Quasithin.G11.P4InspOrth

namespace S143V

section Generic

theorem card_le_two_of_le_zpowers {R : Type*} [Group R] [Finite R] {y : R} (hy : orderOf y = 4)
    {X : Subgroup R} (hXy : X ≤ Subgroup.zpowers y) (hX : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 2 := by
  have hsub : X ≤ Subgroup.zpowers (y ^ 2) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hXy hx)
    have h1 : y ^ (k + k) = 1 := by
      have := hX x hx
      rw [← hk, ← zpow_add] at this
      exact this
    have h2 : (orderOf y : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hy] at h2
    obtain ⟨m, hm⟩ := h2
    have hk2 : k = 2 * m := by omega
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [← hk, hk2, zpow_mul]
    norm_cast
  have h4 : Nat.card (Subgroup.zpowers (y ^ 2)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hy]; norm_num), hy]
  rw [← h4]
  exact Subgroup.card_le_of_le hsub

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}
variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g) (D : HatModel T M)

include h hU hg in
theorem hatE_invariant : ∀ s ∈ D.img T,
    ∀ p ∈ D.hat (Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g),
      s p ∈ D.hat (Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g) := by
  intro s hs p hp
  obtain ⟨t, htT, htN, rfl⟩ := HatModel.mem_img.mp hs
  obtain ⟨e, heE, heU, rfl⟩ := D.mem_hat.mp hp
  rw [D.rho_π ⟨t, htN⟩ heU]
  refine D.mem_hat.mpr ⟨t * e * t⁻¹, ?_, HatModel.conj_mem_uOfL22 htN heU, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (S143.T_le_normalizer_E h hU hg htT) e).mp heE

open scoped Classical in
include h hU hg in
theorem qhat_hatE (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) :
    ∀ v ∈ D.hat (Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g), qhat D v = 0 := by
  intro v hv
  obtain ⟨e, heE, heU, rfl⟩ := D.mem_hat.mp hv
  rw [qhat_π h hZU D heU]
  rw [h.wOfU_inf_rconj_eq hU hg] at heE
  have he2 : e ^ 2 = 1 := (h.isElemAbelian_inf_rconj hU hg).2 e heE
  simp [he2]

section Plus

variable (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) {a : G} (haV : a ∈ VZ T M)
  (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU hg hZU haV haZ in
theorem plus_and_card_of_zu
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hker : Hyp1281Two.centralizerHat T M ≤ T)
    (hd : Module.finrank (ZMod 2) D.V = 4) (h18 : 18 ∣ Nat.card (D.img (mcOf T))) :
    CFSG.GroupTheory.WeirSylow.IsPlusType
      (p4insporth_quad (f := D.B) (q := qhat D) (fun x y => qhat_add h hZU D x y)) ∧
    Nat.card (D.img (mcOf T)) = 72 := by
  classical
  have hsymp : IsSymplectic D.B := ⟨D.B_isAlt, D.B_nondegenerate⟩
  have hq : ∀ x y, qhat D (x + y) = qhat D x + qhat D y + D.B x y :=
    fun x y => qhat_add h hZU D x y
  have hΓ := img_le_orthSub h hZU D
  have h9 : 9 ∣ Nat.card (D.img (mcOf T)) := Nat.dvd_trans (by norm_num) h18
  have hplus := isPlusType_of_nine_dvd hsymp hq hd hΓ h9
  refine ⟨hplus, ?_⟩
  have hS := isSylowTwoOf_img_T h D
  have hnoN : ∀ N : Subgroup (GLV D.V), N ≤ D.img (mcOf T) →
      (∀ γ ∈ D.img (mcOf T), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 3 :=
    fun N hNΓ hNn h3 => no_normal_three_five h hU hg D haV haZ h35 hker hNΓ hNn (Or.inl h3)
  rcases o4plus_overgroup hsymp hq hd hplus hΓ hS h9 hnoN with heq | ⟨⟨y, hSy, hy4⟩, hnoplane⟩
  · rw [heq]
    exact p4insporth_card_plus_four hsymp hq hd hplus
  · exfalso
    have hyp := h.lemma_12_8_12_one hU hg D haV haZ
    have hrank := hyp.rank
    rw [hd] at hrank
    have hiso := hyp.finrank_isotropic_le
    rw [hd] at hiso
    have hsing := qhat_hatE h hU hg D hZU
    have hinv := hatE_invariant h hU hg D
    by_cases h2 : Module.finrank (ZMod 2)
        (D.hat (Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g)) = 2
    · obtain ⟨s, hs, p, hp, hnot⟩ := hnoplane _ h2 hsing
      exact hnot (hinv s hs p hp)
    · have hlog : 2 ≤ Nat.log 2 ((D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex
          (D.img (rconj (Hyp1281Two.wOfU T M) g))) := by omega
      have hr0 : (D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex
          (D.img (rconj (Hyp1281Two.wOfU T M) g)) ≠ 0 := by
        intro h0
        rw [h0] at hlog
        simp at hlog
      have h4 : 4 ≤ (D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex
          (D.img (rconj (Hyp1281Two.wOfU T M) g)) := by
        have := Nat.pow_le_of_le_log hr0 hlog
        simpa using this
      have hXT : D.img (rconj (Hyp1281Two.wOfU T M) g) ≤ D.img T :=
        HatModel.img_mono (h.rconj_wOfU_le_T hU hg)
      have hX2 : Nat.card (D.img (rconj (Hyp1281Two.wOfU T M) g)) ≤ 2 :=
        card_le_two_of_le_zpowers hy4 (by rw [← hSy]; exact hXT) hyp.X_sq
      have hdvd := Subgroup.relIndex_dvd_card (D.img (rconj (centerOf (uOfL22 T M)) g))
        (D.img (rconj (Hyp1281Two.wOfU T M) g))
      have := Nat.le_of_dvd Nat.card_pos hdvd
      omega

end Plus

end Main

end S143V

end CFSG.Quasithin
