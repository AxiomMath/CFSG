module

public import CFSG.Quasithin.Background.D2Tools
public import CFSG.Quasithin.Background.B1Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem s16h_coprime_commSub_inf_fixV_eq
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {g : MulAut W}
    (hg : Odd (orderOf g)) (hgY : ∀ y ∈ Y, g * y = y * g)
    {V : Subgroup W} (hVY : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V)
    (hVg : ∀ v ∈ V, g v ∈ V) (hgen : commSub V Y = V) :
    V ⊓ fixV (Subgroup.zpowers g) = commSub (V ⊓ fixV (Subgroup.zpowers g)) Y := by
  classical
  have hgV : ∀ v ∈ V, g⁻¹ v ∈ V := by
    have hsub : g '' (V : Set W) ⊆ (V : Set W) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hVg v hv
    have heq : g '' (V : Set W) = (V : Set W) := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      rw [Set.ncard_image_of_injective _ g.injective]
    intro v hv
    have hv' : v ∈ g '' (V : Set W) := by rw [heq]; exact hv
    obtain ⟨w, hw, hwv⟩ := hv'
    rw [← hwv, MulAut.inv_apply_self]
    exact hw
  have hstab : g ∈ stabSub V := by
    intro u
    constructor
    · intro hgu
      have h := hgV (g u) hgu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact hVg u hu
  have hVg' : ∀ y ∈ Subgroup.zpowers g, ∀ m ∈ V, y m ∈ V := by
    intro y hy m hm
    exact (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hstab) hy) m).2 hm
  have hCY : ∀ y ∈ Y, ∀ c ∈ fixV (Subgroup.zpowers g), y c ∈ fixV (Subgroup.zpowers g) := by
    intro y hy c hc
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply] at hc ⊢
    calc g (y c) = (g * y) c := rfl
      _ = (y * g) c := by rw [hgY y hy]
      _ = y (g c) := rfl
      _ = y c := by rw [hc]
  have hVCY : ∀ y ∈ Y, ∀ v ∈ V ⊓ fixV (Subgroup.zpowers g),
      y v ∈ V ⊓ fixV (Subgroup.zpowers g) :=
    fun y hy v hv => ⟨hVY y hy v hv.1, hCY y hy v hv.2⟩
  have hDinv : ∀ y ∈ Y, ∀ d ∈ commSub V (Subgroup.zpowers g),
      y d ∈ commSub V (Subgroup.zpowers g) := by
    intro y hy d hd
    refine Subgroup.closure_induction (p := fun d _ =>
      y d ∈ commSub V (Subgroup.zpowers g)) ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨x, hx, u, hu, rfl⟩
      have hgcen : g ∈ Subgroup.centralizer ({y} : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (hgY y hy).symm
      have hyx : y * x = x * y :=
        Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hgcen) hx) y
          (Set.mem_singleton y)
      have hmap : y (x u * u⁻¹) = x (y u) * (y u)⁻¹ := by
        rw [map_mul, map_inv]
        congr 1
        calc y (x u) = (y * x) u := rfl
          _ = (x * y) u := by rw [hyx]
          _ = x (y u) := rfl
      rw [hmap]
      exact Subgroup.subset_closure ⟨x, hx, y u, hVY y hy u hu, rfl⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv]; exact Subgroup.inv_mem _ ha
  have hYodd : Odd (Nat.card (Subgroup.zpowers g)) := by rwa [Nat.card_zpowers]
  obtain ⟨hsplit, hdisj⟩ := CFSG.Quasithin.B1.coprime_decomp hW hYodd hVg'
  have hmain : V = commSub (V ⊓ fixV (Subgroup.zpowers g)) Y ⊔
      commSub (commSub V (Subgroup.zpowers g)) Y := by
    calc V = commSub V Y := hgen.symm
      _ = commSub ((V ⊓ fixV (Subgroup.zpowers g)) ⊔ commSub V (Subgroup.zpowers g)) Y := by
            rw [hsplit]
      _ = commSub (V ⊓ fixV (Subgroup.zpowers g)) Y ⊔
            commSub (commSub V (Subgroup.zpowers g)) Y := commSub_sup_left _ _ _
  have hle1 : commSub (V ⊓ fixV (Subgroup.zpowers g)) Y ≤ V ⊓ fixV (Subgroup.zpowers g) :=
    commSub_le_of_invariant hVCY
  have hle2 : commSub (commSub V (Subgroup.zpowers g)) Y ≤ commSub V (Subgroup.zpowers g) :=
    commSub_le_of_invariant hDinv
  refine le_antisymm ?_ hle1
  rintro v ⟨hvV, hvC⟩
  have hv : v ∈ commSub (V ⊓ fixV (Subgroup.zpowers g)) Y ⊔
      commSub (commSub V (Subgroup.zpowers g)) Y := by rw [← hmain]; exact hvV
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hv
  have hbC : b ∈ V ⊓ fixV (Subgroup.zpowers g) := by
    have hb' : b = a⁻¹ * v := by rw [← hab]; group
    rw [hb']
    exact (V ⊓ fixV (Subgroup.zpowers g)).mul_mem
      ((V ⊓ fixV (Subgroup.zpowers g)).inv_mem (hle1 ha)) ⟨hvV, hvC⟩
  have hbD : b ∈ commSub V (Subgroup.zpowers g) := hle2 hb
  have hb1 : b = 1 := by
    have hmem : b ∈ (V ⊓ fixV (Subgroup.zpowers g)) ⊓ commSub V (Subgroup.zpowers g) :=
      ⟨hbC, hbD⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [← hab, hb1, mul_one]
  exact ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
