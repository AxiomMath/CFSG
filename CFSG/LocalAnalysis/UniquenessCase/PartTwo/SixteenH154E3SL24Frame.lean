module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ConjRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_map_commSub_le {L : Subgroup (MulAut W)} (σ : MulAut W) :
    (commSub ⊤ L).map σ.toMonoidHom ≤ commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom) := by
  rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨c, ⟨x, hx, w, -, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨(MulAut.conj σ) x, ⟨x, hx, rfl⟩, σ w, Subgroup.mem_top _, ?_⟩
  simp [MulAut.conj_apply]

private theorem s16h_sl24_map_conj_mul (X : Subgroup (MulAut W)) (x y : MulAut W) :
    (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      X.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s16h_sl24_map_conj_one (X : Subgroup (MulAut W)) :
    X.map (MulAut.conj (1 : MulAut W)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

private theorem s16h_sl24_map_conj_inv (X : Subgroup (MulAut W)) (x : MulAut W) :
    (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = X := by
  rw [s16h_sl24_map_conj_mul, inv_mul_cancel, s16h_sl24_map_conj_one]

theorem s16h_sl4_conc_cent {A : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (hW : Conc4_136W A t L) {g : MulAut W} (hg : g ∈ A)
    (hgn : g ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    L.map (MulAut.conj g).toMonoidHom ≤ centSub (commSub ⊤ L) ∧
      L ≤ centSub (commSub ⊤ (L.map (MulAut.conj g).toMonoidHom)) := by
  have h2 := hW.2.1
  refine ⟨fun x hx u hu => (commSub_eq_bot_iff.1 (h2 g hg hgn).2) hu x hx, ?_⟩
  have hgi : g⁻¹ ∈ A := A.inv_mem hg
  have hgin : g⁻¹ ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h =>
    hgn (by simpa using (Subgroup.normalizer (L : Set (MulAut W))).inv_mem h)
  have h3 := commSub_eq_bot_iff.1 (h2 g⁻¹ hgi hgin).2
  intro a ha u hu
  have h4 := s16h_sl24_map_commSub_le (L := L.map (MulAut.conj g).toMonoidHom) g⁻¹
  rw [s16h_sl24_map_conj_inv] at h4
  have hu0 : g⁻¹ u ∈ commSub ⊤ L := h4 ⟨u, hu, rfl⟩
  have hya : (MulAut.conj g⁻¹) a ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := ⟨a, ha, rfl⟩
  have h5 := h3 hu0 _ hya
  have h6 : (g⁻¹ * a * g⁻¹⁻¹) (g⁻¹ u) = g⁻¹ u := by
    simpa [MulAut.conj_apply] using h5
  have h7 : a u = u := by
    have := congrArg g h6
    simpa [MulAut.mul_apply] using this
  exact h7

private theorem s16h_sl24_normalizes_other {X L L' T : Subgroup (MulAut W)}
    (F : s16h_SL4TwoFrame X L L' T) (hne : L ≠ L') {x : MulAut W} (hx : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    L'.map (MulAut.conj x).toMonoidHom = L' := by
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 hxN
  rcases F.perm x hx with ⟨-, h2⟩ | ⟨h2, -⟩
  · exact h2
  · exact absurd (h1.symm.trans h2) hne

theorem s16h_sl4_frame_fixed_outside_Z (hW : ∀ w : W, w ^ 2 = 1)
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T) (hne : L ≠ L')
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hWW : commSub ⊤ L ⊓ commSub ⊤ L' = commSub ⊤ L ⊓ fixV L) :
    ∃ w : W, w ∈ fixV T ∧ w ∉ commSub ⊤ L ⊓ fixV L := by
  classical
  obtain ⟨s, hsT, hsL⟩ := F.swap
  have hsX : s ∈ X := F.t_le hsT
  have hsL' : L'.map (MulAut.conj s).toMonoidHom = L := by
    rcases F.perm s hsX with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans hsL) hne
    · exact h2
  have hsLi : L'.map (MulAut.conj s⁻¹).toMonoidHom = L := by
    rw [← hsL, s16h_sl24_map_conj_inv]
  set T0 : Subgroup (MulAut W) := T ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hT0
  have hT02 : IsPGroup 2 ↥T0 := F.t_two.to_inf_left
  obtain ⟨w, hwU, hwZ, hwT0⟩ :=
    s16h_sl24_cover_sylow_fixed hW hrow hZ4 (inf_le_right : T0 ≤ _) hT02
  have hconj : ∀ t ∈ T0, s⁻¹ * t * s ∈ T0 := by
    intro t ht
    obtain ⟨htT, htN⟩ := Subgroup.mem_inf.1 ht
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (T.inv_mem hsT) htT) hsT, ?_⟩
    have hLt' := s16h_sl24_normalizes_other F hne (F.t_le htT) htN
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    calc L.map (MulAut.conj (s⁻¹ * t * s)).toMonoidHom
        = L.map (MulAut.conj (s⁻¹ * (t * s))).toMonoidHom := by rw [mul_assoc]
      _ = (L.map (MulAut.conj (t * s)).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
          (s16h_sl24_map_conj_mul L (t * s) s⁻¹).symm
      _ = ((L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj s⁻¹).toMonoidHom := by rw [s16h_sl24_map_conj_mul L s t]
      _ = L := by rw [hsL, hLt', hsLi]
  have hss : s * s ∈ T0 := by
    refine Subgroup.mem_inf.2 ⟨T.mul_mem hsT hsT, Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_⟩
    change L.map (MulAut.conj (s * s)).toMonoidHom = L
    rw [← s16h_sl24_map_conj_mul L s s, hsL, hsL']
  have hcos : ∀ t ∈ T, t ∉ T0 → s⁻¹ * t ∈ T0 := by
    intro t htT htn
    have htN : t ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h =>
      htn (Subgroup.mem_inf.2 ⟨htT, h⟩)
    have hLt : L.map (MulAut.conj t).toMonoidHom = L' := by
      rcases F.perm t (F.t_le htT) with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.2 h1) htN
      · exact h2
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.inv_mem hsT) htT,
      Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_⟩
    change L.map (MulAut.conj (s⁻¹ * t)).toMonoidHom = L
    rw [← s16h_sl24_map_conj_mul L t s⁻¹, hLt, hsLi]
  have hsw' : ∀ t ∈ T0, t (s w) = s w := by
    intro t ht
    have h1 : (s * (s⁻¹ * t * s)) w = t (s w) := by
      have : s * (s⁻¹ * t * s) = t * s := by group
      rw [this]; rfl
    have h2 : (s⁻¹ * t * s) w = w := hwT0 _ (hconj t ht)
    rw [← h1, MulAut.mul_apply, h2]
  have hfix : ∀ t ∈ T, t (w * s w) = w * s w := by
    intro t htT
    by_cases ht0 : t ∈ T0
    · rw [map_mul, hwT0 t ht0, hsw' t ht0]
    · have ht' := hcos t htT ht0
      have htt : t = s * (s⁻¹ * t) := by group
      rw [htt, MulAut.mul_apply, map_mul, hwT0 _ ht', hsw' _ ht', map_mul,
        ← MulAut.mul_apply, hwT0 _ hss, mul_comm]
  refine ⟨w * s w, fun t ht => hfix t ht, fun hw1 => hwZ ?_⟩
  have hsw : s w ∈ commSub ⊤ L' := by
    have := s16h_sl24_map_commSub_le (L := L) s
    rw [hsL] at this
    exact this ⟨w, hwU, rfl⟩
  have hsw_W : s w ∈ commSub ⊤ L := by
    have := (commSub ⊤ L).mul_mem ((commSub ⊤ L).inv_mem hwU) hw1.1
    simpa using this
  have hsw_Z : s w ∈ commSub ⊤ L ⊓ fixV L := by
    rw [← hWW]
    exact ⟨hsw_W, hsw⟩
  have := (commSub ⊤ L ⊓ fixV L).mul_mem hw1 ((commSub ⊤ L ⊓ fixV L).inv_mem hsw_Z)
  simpa using this

theorem s16h_sl4_frame_involution_rank (hW : ∀ w : W, w ^ 2 = 1)
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T) (hne : L ≠ L')
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hJoin : commSub ⊤ L ⊔ commSub ⊤ L' = ⊤)
    {s : MulAut W} (hs : s ∈ X) (hsq : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  by_cases h1 : ∃ u ∈ commSub ⊤ L, s u ≠ u
  · exact s16h_sl24_cover_involution_rank hW hrow hZ4 hsN hsq h1
  by_cases h2 : ∃ u ∈ commSub ⊤ L', s u ≠ u
  · obtain ⟨t, -, htL⟩ := F.swap
    obtain ⟨hrow', hZ4'⟩ := s16h_sl24_conj_row t hrow hZ4
    rw [htL] at hrow' hZ4'
    have hsN' : s ∈ Subgroup.normalizer (L' : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (s16h_sl24_normalizes_other F hne hs hsN)
    exact s16h_sl24_cover_involution_rank hW hrow' hZ4' hsN' hsq h2
  · exfalso
    apply hs1
    have h1' : ∀ u ∈ commSub ⊤ L, s u = u := fun u hu => by_contra fun h => h1 ⟨u, hu, h⟩
    have h2' : ∀ u ∈ commSub ⊤ L', s u = u := fun u hu => by_contra fun h => h2 ⟨u, hu, h⟩
    have hle : (⊤ : Subgroup W) ≤ MonoidHom.eqLocus s.toMonoidHom (MonoidHom.id W) := by
      rw [← hJoin]
      exact sup_le (fun u hu => h1' u hu) (fun u hu => h2' u hu)
    ext v
    exact hle (Subgroup.mem_top v)

theorem s16h_sl4_frame_normalizer_cent_Z (hW : ∀ w : W, w ^ 2 = 1)
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T) (hne : L ≠ L')
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hJoin : commSub ⊤ L ⊔ commSub ⊤ L' = ⊤)
    (hLc : L ≤ centSub (commSub ⊤ L')) (hL'c : L' ≤ centSub (commSub ⊤ L))
    {τ : MulAut W} (hτ : τ ∈ X) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτZ : ∀ z ∈ (commSub ⊤ L ⊓ fixV L) ⊔ (commSub ⊤ L' ⊓ fixV L'), τ z = z) :
    τ ∈ L ⊔ L' := by
  obtain ⟨t, -, htL⟩ := F.swap
  obtain ⟨hrow', hZ4'⟩ := s16h_sl24_conj_row t hrow hZ4
  rw [htL] at hrow' hZ4'
  have hτN' : τ ∈ Subgroup.normalizer (L' : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (s16h_sl24_normalizes_other F hne hτ hτN)
  obtain ⟨l, hl, hlτ⟩ := s16h_sl24_cover_normalizer_cent_Z hW hrow hZ4 hτN
    (fun z hz => hτZ z (Subgroup.mem_sup_left hz))
  obtain ⟨l', hl', hl'τ⟩ := s16h_sl24_cover_normalizer_cent_Z hW hrow' hZ4' hτN'
    (fun z hz => hτZ z (Subgroup.mem_sup_right hz))
  have hcomm : l * l' = l' * l := F.comm l hl l' hl'
  have hEq : τ = l * l' := by
    have hle : (⊤ : Subgroup W) ≤ MonoidHom.eqLocus τ.toMonoidHom (l * l').toMonoidHom := by
      rw [← hJoin]
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · show τ u = (l * l') u
        rw [hlτ u hu, MulAut.mul_apply, hL'c hl' u hu]
      · show τ u = (l * l') u
        rw [hl'τ u hu, MulAut.mul_apply]
        have hlu : l u = u := hLc hl u hu
        calc l' u = l' (l u) := by rw [hlu]
          _ = (l' * l) u := rfl
          _ = (l * l') u := by rw [hcomm]
    ext v
    exact hle (Subgroup.mem_top v)
  rw [hEq]
  exact Subgroup.mul_mem_sup hl hl'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
