module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.StandardType.RCKK1IIp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1

private theorem rckIIpIso_map_isElemAbelian {G X : Type*} [Group G] [Group X] {p : ℕ}
    (H : Subgroup G) (f : G →* X) (hH : IsElemAbelian p H) :
    IsElemAbelian p (H.map f) := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨ha, hha, hae⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨hb, hhb, hbe⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : X) * b = (b : X) * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val
      (hH.1.is_comm.comm (⟨ha, hha⟩ : ↥H) (⟨hb, hhb⟩ : ↥H)))
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hH.2 g hg, map_one]

private theorem rckIIpIso_K1b_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {rb : G} {Vb : Subgroup G} (h : K1Lift.K1b rb Vb) :
    K1Lift.K1b (e rb) (Vb.map e.toMonoidHom) := by
  intro Y' hY'pg hfix' hnorm' v hv φ hφ
  let Φ : MulAut G ≃* MulAut H := MulAut.congr e
  let Y : Subgroup (MulAut G) := Y'.comap Φ.toMonoidHom
  have hYpg : IsPGroup 2 Y := IsPGroup.comap_of_injective hY'pg Φ.toMonoidHom Φ.injective
  have hfix : ∀ ψ ∈ Y, ψ rb = rb := by
    intro ψ hψ
    have hψ' : Φ ψ ∈ Y' := hψ
    have hΦψ : Φ ψ (e rb) = e (ψ rb) := by
      show (MulAut.congr e ψ) (e rb) = e (ψ rb)
      simp [MulAut.congr_apply]
    have h1 : Φ ψ (e rb) = e rb := hfix' (Φ ψ) hψ'
    rw [hΦψ] at h1
    exact e.injective h1
  have hnorm : ∀ c : G, c * rb = rb * c →
      MulAut.conj c ∈ Subgroup.normalizer (Y : Set (MulAut G)) := by
    intro c hc
    have hc' : e c * e rb = e rb * e c := by rw [← map_mul, ← map_mul, hc]
    have hmem' : MulAut.conj (e c) ∈ Subgroup.normalizer (Y' : Set (MulAut H)) :=
      hnorm' (e c) hc'
    have hconj : Φ (MulAut.conj c) = MulAut.conj (e c) := by
      ext z
      show (MulAut.congr e (MulAut.conj c)) z = e c * z * (e c)⁻¹
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [Subgroup.mem_normalizer_iff] at hmem' ⊢
    intro y
    change Φ y ∈ Y' ↔ Φ (MulAut.conj c * y * (MulAut.conj c)⁻¹) ∈ Y'
    rw [map_mul, map_mul, map_inv, hconj]
    exact hmem' (Φ y)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  let ψ : MulAut G := Φ.symm φ
  have hψ : ψ ∈ Y := by
    change Φ ψ ∈ Y'
    rw [show Φ ψ = φ from MulEquiv.apply_symm_apply Φ φ]
    exact hφ
  have hmem : ψ u * u⁻¹ ∈ Subgroup.zpowers rb := h Y hYpg hfix hnorm u hu ψ hψ
  have hkey : φ (e u) = e (ψ u) := by
    have hΦψ : Φ ψ = φ := MulEquiv.apply_symm_apply Φ φ
    calc φ (e u) = Φ ψ (e u) := by rw [hΦψ]
      _ = e (ψ u) := by
        show (MulAut.congr e ψ) (e u) = e (ψ u)
        simp [MulAut.congr_apply]
  change φ (e u) * (e u)⁻¹ ∈ Subgroup.zpowers (e rb)
  rw [hkey]
  have hmem' : e (ψ u * u⁻¹) ∈ Subgroup.zpowers (e rb) := by
    change e (ψ u * u⁻¹) ∈ Subgroup.zpowers (e.toMonoidHom rb)
    rw [← MonoidHom.map_zpowers e.toMonoidHom rb]
    exact Subgroup.mem_map.mpr ⟨ψ u * u⁻¹, hmem, rfl⟩
  rwa [map_mul, map_inv] at hmem'

theorem rckK1Data_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {rb : G} {Vb : Subgroup G}
    (h : RCKK1Data rb Vb) : RCKK1Data (e rb) (Vb.map e.toMonoidHom) := by
  obtain ⟨hrb, hrb1, hab, hcard, hconj, hK1b⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨rb, hrb, rfl⟩
  · intro h1
    exact hrb1 (e.injective (by simpa using h1))
  · exact rckIIpIso_map_isElemAbelian Vb e.toMonoidHom hab
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · intro v hv hv1
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    have hu1 : u ≠ 1 := by intro h; exact hv1 (by rw [h, map_one])
    obtain ⟨j, hj⟩ := hconj u hu hu1
    refine ⟨e j, ?_⟩
    change e u = e j * e rb * (e j)⁻¹
    rw [hj, map_mul, map_mul, map_inv]
  · exact rckIIpIso_K1b_map e hK1b

theorem rckIIp_card_centralizer_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (rb : G) :
    Nat.card (Subgroup.centralizer ({e rb} : Set H)) =
      Nat.card (Subgroup.centralizer ({rb} : Set G)) := by
  have hmap : (Subgroup.centralizer ({rb} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e rb} : Set H) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      change e y * e rb = e rb * e y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

private theorem rckIIpIso_raw_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenRawDatum] at h
  case A => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twA => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case B => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case C => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case D =>
    split_ifs at h
    · obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
    · obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twD =>
    split_ifs at h
    · obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
    · obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
    · obtain ⟨K, _, _, _, b, c, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case E6 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case E7 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case E8 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case F4 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twE6 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case triD4 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case G2 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twB2 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twF4 => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case B2der => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case G2der => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩
  case twF4der => obtain ⟨K, _, _, _, hQ⟩ := h; exact ⟨_, inferInstance, _, _, hQ⟩

private theorem rckIIpIso_recipeLinear {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .IIp) {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) : LargeEvenRecipeLinear 4 2 Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggSixRCKLabelRow] at hrow
  case A =>
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn1, _, _⟩ := hlab
    have hn : n = 1 := by
      by_contra hne
      have h2 : 2 ≤ n := by omega
      rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    subst hn
    have hl : l = 3 := by
      rw [if_neg (by omega : ¬ 2 ≤ 1)] at hrow
      by_contra hne
      rw [if_neg hne] at hrow
      by_cases h4 : 4 ≤ l
      · rw [if_pos h4] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h4] at hrow; exact absurd hrow (by decide)
    subst hl
    change LargeEvenRecipeLinear 4 2 Q at h
    exact h
  case D =>
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn1, _⟩ := hlab
    have hn : n = 1 := by
      by_contra hne
      have h2 : 2 ≤ n := by omega
      rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    subst hn
    have hl : l = 3 := by
      rw [if_neg (by omega : ¬ 2 ≤ 1)] at hrow
      by_contra hne
      rw [if_neg hne] at hrow
      exact absurd hrow (by decide)
    subst hl
    change LargeEvenRecipeLinear 4 2 Q at h
    exact h
  all_goals
    exfalso
    first
      | (split_ifs at hrow <;> exact absurd hrow (by decide))
      | exact absurd hrow (by decide)

private theorem rckIIpIso_proj_congr {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {H H' : Subgroup (GL ι K)} (h : H = H') :
    Nonempty (LargeEvenProj H ≃* CFSG.Open.StatedProj H') := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem rckIIp_iso {Jb : Type} [Group Jb]
    (h : LargeEvenMarking Jb (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = .IIp)) :
    Nonempty ((Jb ⧸ Subgroup.center Jb) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := rckIIpIso_raw_exists hraw
  obtain ⟨_, _, _, hrow⟩ := hQ₀
  have hRecipe : LargeEvenRecipeLinear 4 2 _ := rckIIpIso_recipeLinear hlab hrow hraw
  unfold LargeEvenRecipeLinear at hRecipe
  obtain ⟨K, hField, hFinite, hK, hQK⟩ := hRecipe
  letI : Field K := hField
  letI : Finite K := hFinite
  obtain ⟨_, _, θ, _⟩ := hQK
  obtain ⟨eSL⟩ := rckIIpIso_proj_congr
    (show LargeEvenSLGroup (Fin 4) K = CFSG.Open.StatedSL 4 K from
      (CFSG.Open.StatedAPI.statedSL_eq_ker_det 4 K).symm)
  exact ⟨θ.trans (eSL.trans
    ((CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK 4).trans
      ((CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK 4).trans
        CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm)))⟩

end CFSG.StandardType.RCKK1IIp
