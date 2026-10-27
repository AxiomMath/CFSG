module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Lie
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Norm
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Open
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

local instance a2NeZeroRankMain : NeZero Tag.F4.rank := ⟨by decide⟩

local notation "𝔽₂" => GaloisField 2 1

section Main


theorem aP_mem_Lv : ((aP : ↥(B3Levi 𝔽₂)) : ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {2} := by
  rw [coe_aP]
  exact pinnedX_single_mem_Lv 2 1

theorem aM_mem_Lv : ((aM : ↥(B3Levi 𝔽₂)) : ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {2} := by
  rw [coe_aM]
  exact pinnedX_neg_single_mem_Lv 2 1

theorem bP_mem_Lv : ((bP : ↥(B3Levi 𝔽₂)) : ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {0, 1} := by
  rw [coe_bP]
  exact Lv_one_le_zero_one (pinnedX_single_mem_Lv 1 1)

theorem bM_mem_Lv : ((bM : ↥(B3Levi 𝔽₂)) : ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {0, 1} := by
  rw [coe_bM]
  exact Lv_one_le_zero_one (pinnedX_neg_single_mem_Lv 1 1)

theorem θP_aP_mem {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) :
    θP aP ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}) :=
  (mem_pimg_iff θP _).2 ⟨(aP : ↥(adjointGroup .F4 𝔽₂)), aP.2, aP_mem_Lv, rfl⟩

theorem θP_aM_mem {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) :
    θP aM ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {2}) :=
  (mem_pimg_iff θP _).2 ⟨(aM : ↥(adjointGroup .F4 𝔽₂)), aM.2, aM_mem_Lv, rfl⟩

theorem θP_bP_mem {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) :
    θP bP ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) :=
  (mem_pimg_iff θP _).2 ⟨(bP : ↥(adjointGroup .F4 𝔽₂)), bP.2, bP_mem_Lv, rfl⟩

theorem θP_bM_mem {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) :
    θP bM ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) :=
  (mem_pimg_iff θP _).2 ⟨(bM : ↥(adjointGroup .F4 𝔽₂)), bM.2, bM_mem_Lv, rfl⟩

theorem commute_words {G : Type} [Group G] {w r e m : G} (hr : w * r = r * w)
    (he : w * e = e * w) (hm : w * m = m * w) :
    w * ((r * e * r) * m * (r * e * r) * m) = ((r * e * r) * m * (r * e * r) * m) * w ∧
      w * (e * (r * m * r) * e * (r * m * r)) = (e * (r * m * r) * e * (r * m * r)) * w := by
  have hr' : Commute w r := hr
  have he' : Commute w e := he
  have hm' : Commute w m := hm
  have h1 : Commute w (r * e * r) := (hr'.mul_right he').mul_right hr'
  have h2 : Commute w (r * m * r) := (hr'.mul_right hm').mul_right hr'
  exact ⟨(((h1.mul_right hm').mul_right h1).mul_right hm'),
    (((he'.mul_right h2).mul_right he').mul_right h2)⟩

theorem marking {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) (hθ : Function.Injective θP)
    (F : H6 →* G) (X : Subgroup G)
    (hXcomm : ∀ w ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}), ∀ x ∈ X, w * x = x * w)
    (hFX : ∀ e ∈ Xstar, F e ∈ X) {u₁ u₂ : H6} (hρ₁ : F u₁ = θP aP) (hρ₂ : F u₂ = θP aM)
    (hu₁ : u₁ = pH ∨ u₁ = qH ∨ u₁ = rH) (hu₂ : u₂ = pH ∨ u₂ = qH ∨ u₂ = rH) (hne : u₁ ≠ u₂) :
    (u₁ = pH ∧ u₂ = qH) ∨ (u₁ = qH ∧ u₂ = pH) := by
  have hFp : F pH = (F rH * F ePH * F rH) * F eMH * (F rH * F ePH * F rH) * F eMH := by
    conv_lhs => rw [pH_word]
    simp only [map_mul]
  have hFq : F qH = F ePH * (F rH * F eMH * F rH) * F ePH * (F rH * F eMH * F rH) := by
    conv_lhs => rw [qH_word]
    simp only [map_mul]
  have key : ∀ w ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}), w * F rH = F rH * w →
      w * F pH = F pH * w ∧ w * F qH = F qH * w := by
    intro w hw hr
    have h := commute_words hr (hXcomm w hw _ (hFX _ ePH_mem_Xstar))
      (hXcomm w hw _ (hFX _ eMH_mem_Xstar))
    rw [hFp, hFq]
    exact h
  have hn1 : u₁ ≠ rH := by
    intro h
    have hr : θP bM * F rH = F rH * θP bM := by
      have := congrArg θP rel_ap_bm.symm
      simp only [map_mul] at this
      rw [← h, hρ₁]
      exact this
    obtain ⟨hp, hq⟩ := key _ (θP_bM_mem θP) hr
    have hcomm : θP bM * θP aM = θP aM * θP bM := by
      rcases hu₂ with h2 | h2 | h2
      · rw [h2] at hρ₂
        rw [← hρ₂]
        exact hp
      · rw [h2] at hρ₂
        rw [← hρ₂]
        exact hq
      · exact absurd (h.trans h2.symm) hne
    apply ne_am_bm
    apply hθ
    simp only [map_mul]
    exact hcomm.symm
  have hn2 : u₂ ≠ rH := by
    intro h
    have hr : θP bP * F rH = F rH * θP bP := by
      have := congrArg θP rel_am_bp.symm
      simp only [map_mul] at this
      rw [← h, hρ₂]
      exact this
    obtain ⟨hp, hq⟩ := key _ (θP_bP_mem θP) hr
    have hcomm : θP bP * θP aP = θP aP * θP bP := by
      rcases hu₁ with h1 | h1 | h1
      · rw [h1] at hρ₁
        rw [← hρ₁]
        exact hp
      · rw [h1] at hρ₁
        rw [← hρ₁]
        exact hq
      · exact absurd (h1.trans h.symm) hne
    apply ne_ap_bp
    apply hθ
    simp only [map_mul]
    exact hcomm.symm
  rcases hu₁ with h1 | h1 | h1 <;> rcases hu₂ with h2 | h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd h2 hn2
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne
  · exact absurd h2 hn2
  · exact absurd h1 hn1
  · exact absurd h1 hn1
  · exact absurd h1 hn1

theorem exists_transport {G : Type} [Group G] {M : Subgroup G} (ψ : ↥M ≃* H6) :
    ∃ f : H6 →* G, Function.Injective f ∧ f.range = M ∧
      ∀ (ρ : G) (h : ρ ∈ M), f (ψ ⟨ρ, h⟩) = ρ := by
  refine ⟨M.subtype.comp ψ.symm.toMonoidHom, Subtype.val_injective.comp ψ.symm.injective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ.symm x).2
    · intro hy
      exact ⟨ψ ⟨y, hy⟩, by simp⟩
  · intro ρ h
    simp

theorem map_comap_of_le {G : Type} [Group G] {M A : Subgroup G} (f : H6 →* G)
    (hfr : f.range = M) (hA : A ≤ M) : (A.comap f).map f = A := by
  rw [Subgroup.map_comap_eq, hfr]
  exact inf_eq_right.2 hA

theorem a2_core {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) (hθ : Function.Injective θP)
    (M X : Subgroup G) (F : H6 →* G) (hFM : F.range ≤ M) (hFX : ∀ e ∈ Xstar, F e ∈ X)
    (hXcomm : ∀ w ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}), ∀ x ∈ X, w * x = x * w) {u₁ u₂ : H6}
    (hρ₁ : F u₁ = θP aP) (hρ₂ : F u₂ = θP aM)
    (hu₁ : u₁ = pH ∨ u₁ = qH ∨ u₁ = rH) (hu₂ : u₂ = pH ∨ u₂ = qH ∨ u₂ = rH) (hne : u₁ ≠ u₂) :
    ∃ θA : ↥(Lv 𝔽₂ {2, 3}) →* G,
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {2}),
        θA ⟨x, Lv_two_le_A hx⟩ = θP ⟨x, Lv_two_le_P hx⟩) ∧
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {3}), θA ⟨x, Lv_three_le_A hx⟩ ∈ X) ∧
      θA.range ≤ M := by
  rcases marking θP hθ F X hXcomm hFX hρ₁ hρ₂ hu₁ hu₂ hne with ⟨hpl, hmi⟩ | ⟨hpl, hmi⟩
  · refine conclusion_of_values θP M X F gYH hFM ?_ ?_ ?_ ?_
    · rw [PhiHom_gY.1, ← hpl, hρ₁]
    · rw [PhiHom_gY.2.1, ← hmi, hρ₂]
    · rw [PhiHom_gY.2.2.1]
      exact hFX _ ePH_mem_Xstar
    · rw [PhiHom_gY.2.2.2]
      exact hFX _ eMH_mem_Xstar
  · refine conclusion_of_values θP M X F (gYH * jH) hFM ?_ ?_ ?_ ?_
    · rw [PhiHom_gYJ.1, ← hpl, hρ₁]
    · rw [PhiHom_gYJ.2.1, ← hmi, hρ₂]
    · rw [PhiHom_gYJ.2.2.1]
      exact hFX _ eMH_mem_Xstar
    · rw [PhiHom_gYJ.2.2.2]
      exact hFX _ ePH_mem_Xstar

theorem a2_stage2 {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) (hθ : Function.Injective θP)
    (M X : Subgroup G) (f : H6 →* G) (hfr : f.range = M)
    (hXcomm : ∀ w ∈ pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}), ∀ x ∈ X, w * x = x * w) {v₁ v₂ : H6}
    (hv₁ : f v₁ = θP aP) (hv₂ : f v₂ = θP aM) (hne : v₁ ≠ v₂) {g₁ : H6}
    (hY : (X.comap f).map (MulAut.conj g₁).toMonoidHom = Xstar)
    (hu₁ : g₁ * v₁ * g₁⁻¹ = pH ∨ g₁ * v₁ * g₁⁻¹ = qH ∨ g₁ * v₁ * g₁⁻¹ = rH)
    (hu₂ : g₁ * v₂ * g₁⁻¹ = pH ∨ g₁ * v₂ * g₁⁻¹ = qH ∨ g₁ * v₂ * g₁⁻¹ = rH) :
    ∃ θA : ↥(Lv 𝔽₂ {2, 3}) →* G,
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {2}),
        θA ⟨x, Lv_two_le_A hx⟩ = θP ⟨x, Lv_two_le_P hx⟩) ∧
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {3}), θA ⟨x, Lv_three_le_A hx⟩ ∈ X) ∧
      θA.range ≤ M := by
  obtain ⟨F, hFdef⟩ : ∃ F : H6 →* G, ∀ y, F y = f (g₁⁻¹ * y * g₁) :=
    ⟨f.comp (MulAut.conj g₁⁻¹).toMonoidHom, fun y => by simp [MulAut.conj_apply]⟩
  have hFconj : ∀ y, F (g₁ * y * g₁⁻¹) = f y := fun y => by
    rw [hFdef]
    congr 1
    group
  have hFM : F.range ≤ M := by
    rintro _ ⟨y, rfl⟩
    rw [hFdef, ← hfr]
    exact ⟨_, rfl⟩
  have hFX : ∀ e ∈ Xstar, F e ∈ X := by
    intro e he
    rw [← hY] at he
    obtain ⟨y, hy, rfl⟩ := he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hFconj]
    exact hy
  have hρ₁ : F (g₁ * v₁ * g₁⁻¹) = θP aP := by rw [hFconj, hv₁]
  have hρ₂ : F (g₁ * v₂ * g₁⁻¹) = θP aM := by rw [hFconj, hv₂]
  have hne' : g₁ * v₁ * g₁⁻¹ ≠ g₁ * v₂ * g₁⁻¹ := fun h =>
    hne (mul_left_cancel (mul_right_cancel h))
  exact a2_core θP hθ M X F hFM hFX hXcomm hρ₁ hρ₂ hu₁ hu₂ hne'

theorem a2Piece_holds : A2Piece (GaloisField 2 1) := by
  intro G _ _ θP hθ M K₀ hM hMC hK2M hX hXM hK₀X hK₀cong hK₀K2 h36₀ h36₂
  obtain ⟨ψ⟩ := nonempty_mulEquiv_H6_of_stated hM
  obtain ⟨f, hf, hfr, hfψ⟩ := exists_transport ψ
  obtain ⟨K2, hK2⟩ : ∃ K2 : Subgroup G, K2 = pimg 𝔽₂ θP (Lv 𝔽₂ {2}) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Subgroup G, R = pimg 𝔽₂ θP (Lv 𝔽₂ {0, 1}) := ⟨_, rfl⟩
  rw [← hK2] at hK2M hK₀K2 h36₂
  rw [← hR] at hX hXM hK₀X ⊢
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G, X = CenS R := ⟨_, rfl⟩
  rw [← hXdef] at hX hXM hK₀X ⊢
  obtain ⟨eX⟩ := nonempty_equiv_G3_of_isLnq hX
  have hXmap : (X.comap f).map f = X := map_comap_of_le f hfr hXM
  have hSmap : (K₀.comap f).map f = K₀ := map_comap_of_le f hfr (hK₀X.trans hXM)
  have eX' : Nonempty (↥(X.comap f) ≃* G3) :=
    ⟨((Subgroup.equivMapOfInjective (X.comap f) f hf).trans
      (MulEquiv.subgroupCongr hXmap)).trans eX⟩
  have hK₀card : Nat.card K₀ = 6 := by
    obtain ⟨e⟩ := hK₀cong
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hS6 : Nat.card (K₀.comap f) = 6 := by
    rw [← Subgroup.card_map_of_injective hf, hSmap, hK₀card]
  have hC : Nat.card ↥(Subgroup.centralizer ((K₀.comap f : Subgroup H6) : Set H6)) = 36 := by
    have h := card_inf_cen_map f hf (K₀.comap f)
    rw [hfr, hSmap] at h
    rw [← h]
    exact h36₀
  have hρP2 : θP aP ∈ K2 := by
    rw [hK2]
    exact θP_aP_mem θP
  have hρM2 : θP aM ∈ K2 := by
    rw [hK2]
    exact θP_aM_mem θP
  obtain ⟨v₁, hv₁⟩ : ∃ v : H6, f v = θP aP := ⟨ψ ⟨θP aP, hK2M hρP2⟩, hfψ _ _⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : H6, f v = θP aM := ⟨ψ ⟨θP aM, hK2M hρM2⟩, hfψ _ _⟩
  have h1 : v₁ * v₁ = 1 := hf (by rw [map_mul, hv₁, map_one, ← map_mul, aP_sq, map_one])
  have h2 : v₂ * v₂ = 1 := hf (by rw [map_mul, hv₂, map_one, ← map_mul, aM_sq, map_one])
  have hne1 : v₁ ≠ 1 := fun h => aP_ne_one (hθ (by rw [← hv₁, h, map_one, map_one]))
  have hne2 : v₂ ≠ 1 := fun h => aM_ne_one (hθ (by rw [← hv₂, h, map_one, map_one]))
  have hne : v₁ ≠ v₂ := fun h => aP_ne_aM (hθ (by rw [← hv₁, ← hv₂, h]))
  have hord : (aP * aM) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (aP * aM)
    rwa [orderOf_aP_mul_aM] at this
  have h3 : (v₁ * v₂) ^ 3 = 1 := hf (by
    rw [map_pow, map_mul, hv₁, hv₂, ← map_mul, ← map_pow, hord, map_one, map_one])
  have hcomm : ∀ s ∈ K₀.comap f, s * v₁ = v₁ * s ∧ s * v₂ = v₂ * s := fun s hs =>
    ⟨hf (by rw [map_mul, map_mul, hv₁]; exact hK₀K2 (f s) hs _ hρP2),
     hf (by rw [map_mul, map_mul, hv₂]; exact hK₀K2 (f s) hs _ hρM2)⟩
  have hK2card : Nat.card K2 = 6 := by
    rw [hK2, card_pimg θP hθ Lv_two_le_P, card_Lv_single]
  have hne12 : v₁ * v₂ ≠ 1 := by
    intro h
    apply hne
    have h' := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right h1] at h'
    exact h'.symm
  have hC2 : Nat.card ↥(Subgroup.centralizer
      ((Subgroup.closure ({v₁, v₂} : Set H6) : Subgroup H6) : Set H6)) = 36 := by
    have hTmap : (Subgroup.closure ({v₁, v₂} : Set H6)).map f = K2 := by
      have hle : (Subgroup.closure ({v₁, v₂} : Set H6)).map f ≤ K2 := by
        rw [MonoidHom.map_closure, Set.image_pair, hv₁, hv₂, Subgroup.closure_le]
        rintro x (rfl | hx)
        · exact hρP2
        · rw [Set.mem_singleton_iff.1 hx]
          exact hρM2
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective hf, hK2card]
      exact six_le_card (a := v₁) (b := v₁ * v₂) (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
        (orderOf_eq_prime (by rw [pow_two]; exact h1) hne1) (orderOf_eq_prime h3 hne12)
    have h := card_inf_cen_map f hf (Subgroup.closure ({v₁, v₂} : Set H6))
    rw [hfr, hTmap] at h
    rw [← h]
    exact h36₂
  obtain ⟨g₁, hY, hSK, hu₁, hu₂⟩ := exists_normalization eX' (Subgroup.comap_mono hK₀X) hS6 hC h1
    h2 hne1 hne2 hne h3 hcomm hC2
  refine a2_stage2 θP hθ M X f hfr ?_ hv₁ hv₂ hne hY hu₁ hu₂
  intro w hw x hx
  rw [hXdef] at hx
  rw [← hR] at hw
  exact Subgroup.mem_centralizer_iff.1 hx w hw

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
