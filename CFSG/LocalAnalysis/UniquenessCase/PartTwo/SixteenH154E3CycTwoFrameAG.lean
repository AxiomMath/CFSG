module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrameG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

private theorem s16h_e3_CycTwoG_map_conj_one {T : Type*} [Group T] (X : Subgroup T) :
    X.map (MulAut.conj (1 : T)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

private theorem s16h_e3_CycTwoG_map_conj_map_conj {T : Type*} [Group T] (X : Subgroup T)
    (x y : T) :
    (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      X.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext t
  simp [MulAut.conj_apply, mul_assoc]

private theorem s16h_e3_CycTwoG_relIndex_stabilizer_eq_two {T : Type*} [Group T]
    {X K : Subgroup (MulAut T)} {x₁ : MulAut T} (hx₁ : x₁ ∈ X)
    (hx₁K : K.map (MulAut.conj x₁).toMonoidHom ≠ K)
    (huniq : ∀ a ∈ X, ∀ b ∈ X, K.map (MulAut.conj a).toMonoidHom ≠ K →
      K.map (MulAut.conj b).toMonoidHom ≠ K →
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    ((X ⊓ Subgroup.normalizer (K : Set (MulAut T))).subgroupOf X).index = 2 := by
  set K' := K.map (MulAut.conj x₁).toMonoidHom with hK'
  have hmemA : ∀ b : X, b ∈ (X ⊓ Subgroup.normalizer (K : Set (MulAut T))).subgroupOf X ↔
      K.map (MulAut.conj (b : MulAut T)).toMonoidHom = K := fun b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => (Subgroup.mem_normalizer_iff_map_conj_eq).1 h.2,
      fun h => ⟨b.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 h⟩⟩
  have hinj : ∀ (b : MulAut T) (A₁ A₂ : Subgroup (MulAut T)),
      A₁.map (MulAut.conj b).toMonoidHom = A₂.map (MulAut.conj b).toMonoidHom → A₁ = A₂ :=
    fun b _ _ h => Subgroup.map_injective (MulAut.conj b).injective h
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x₁, hx₁⟩, fun b => xor_iff_iff_not.mpr ⟨fun hbg hb => ?_, fun hb => ?_⟩⟩
  · rw [hmemA, Subgroup.coe_mul, ← s16h_e3_CycTwoG_map_conj_map_conj] at hbg
    rw [hmemA] at hb
    exact hx₁K (hinj b K' K (hbg.trans hb.symm))
  · rw [hmemA] at hb
    rw [hmemA, Subgroup.coe_mul, ← s16h_e3_CycTwoG_map_conj_map_conj]
    by_contra hne
    have h1 := huniq _ (X.mul_mem b.2 hx₁) _ b.2
      (by rw [← s16h_e3_CycTwoG_map_conj_map_conj]; exact hne) hb
    rw [← s16h_e3_CycTwoG_map_conj_map_conj] at h1
    exact hx₁K (hinj b K' K h1)

theorem s16h_e3_CycTwoFrameAG_frame
    {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ 2 = 1) {A Lb : Subgroup (MulAut W)} {z t : MulAut W}
    {q n : ℕ} (hq : 1 < q)
    (hzA : z ∈ A) (hzord : orderOf z = q) (hLb : Lb = Subgroup.zpowers z)
    (hconc : Conc4_136W A t Lb)
    (hs2 : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ A, Y = Lb.map (MulAut.conj φ).toMonoidHom} = 2)
    (hZ : commSub (⊤ : Subgroup W) Lb ⊓ fixV Lb = ⊥)
    (hcard : Nat.card ↥(commSub (⊤ : Subgroup W) Lb) = 2 ^ n) :
    ∃ ψ : MulAut W, s16h_CycFrameG q n A ψ z (commSub (⊤ : Subgroup W) Lb) := by
  have hzLb : z ∈ Lb := by rw [hLb]; exact Subgroup.mem_zpowers z
  let S : Set (Subgroup (MulAut W)) :=
    {Y | ∃ φ ∈ A, Y = Lb.map (MulAut.conj φ).toMonoidHom}
  have hs2S : S.ncard = 2 := hs2
  have hmemS : Lb ∈ S := by
    refine ⟨1, A.one_mem, ?_⟩
    exact (s16h_e3_CycTwoG_map_conj_one Lb).symm
  obtain ⟨x, y, hxy, hSxy⟩ := Set.ncard_eq_two.1 hs2S
  rw [hSxy] at hmemS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemS
  obtain ⟨B, hBA, hSAB⟩ : ∃ B : Subgroup (MulAut W), B ≠ Lb ∧ S = {Lb, B} := by
    rcases hmemS with h1 | h1
    · exact ⟨y, fun hy => hxy (h1.symm.trans hy.symm), by rw [hSxy, h1]⟩
    · exact ⟨x, fun hx => hxy (hx.trans h1), by rw [hSxy, h1, Set.pair_comm]⟩
  have hBS : B ∈ S := by
    rw [hSAB]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨ψ, hψA, hBψ⟩ := hBS
  have hAB : Lb.map (MulAut.conj ψ).toMonoidHom = B := hBψ.symm
  have hpairH : ∀ φ ∈ A, Lb.map (MulAut.conj φ).toMonoidHom = Lb ∨
      Lb.map (MulAut.conj φ).toMonoidHom = B := by
    intro φ hφ
    have hmem : Lb.map (MulAut.conj φ).toMonoidHom ∈ S := ⟨φ, hφ, rfl⟩
    rw [hSAB] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hψ_notmemN : ψ ∉ Subgroup.normalizer (Lb : Set (MulAut W)) := by
    intro h
    have hmap : Lb.map (MulAut.conj ψ).toMonoidHom = Lb :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := Lb)).1 h
    exact hBA (hAB.symm.trans hmap)
  have hψinv_notmemN : ψ⁻¹ ∉ Subgroup.normalizer (Lb : Set (MulAut W)) :=
    fun h => hψ_notmemN (by
      simpa using (Subgroup.normalizer (Lb : Set (MulAut W))).inv_mem h)
  have hsup : commSub (⊤ : Subgroup W) Lb ⊔
      (commSub (⊤ : Subgroup W) Lb).map ψ.toMonoidHom = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup W) = ⨆ X ∈ conjSubs A (commSub (⊤ : Subgroup W) Lb), X :=
          hconc.1.symm
      _ ≤ commSub (⊤ : Subgroup W) Lb ⊔ (commSub (⊤ : Subgroup W) Lb).map ψ.toMonoidHom := by
          refine iSup_le fun X => iSup_le fun hX => ?_
          rcases hX with ⟨g, hgA, rfl⟩
          rw [← Asc81c.commSub_map_conj Lb g]
          rcases hpairH g hgA with h | h
          · rw [h]; exact le_sup_left
          · rw [h, ← hAB, Asc81c.commSub_map_conj Lb ψ]; exact le_sup_right
  have hfixU : commSub (⊤ : Subgroup W) Lb ≤
      fixV (Lb.map (MulAut.conj ψ⁻¹).toMonoidHom) :=
    commSub_eq_bot_iff.1 (hconc.2.1 ψ⁻¹ (A.inv_mem hψA) hψinv_notmemN).2
  have ztriv : ∀ u ∈ (commSub (⊤ : Subgroup W) Lb).map ψ.toMonoidHom, z u = u := by
    intro u hu
    obtain ⟨u₁, hu₁, rfl⟩ := Subgroup.mem_map.1 hu
    have hmem : (MulAut.conj ψ⁻¹) z ∈ Lb.map (MulAut.conj ψ⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzLb
    have h1 : ((MulAut.conj ψ⁻¹) z) u₁ = u₁ := mem_fixV.1 (hfixU hu₁) _ hmem
    have h1' : (ψ⁻¹ * z * ψ) u₁ = u₁ := by simpa [MulAut.conj_apply] using h1
    have h2 : (z * ψ) u₁ = ψ u₁ := by
      have h3 : ψ * (ψ⁻¹ * z * ψ) = z * ψ := by group
      calc (z * ψ) u₁ = (ψ * (ψ⁻¹ * z * ψ)) u₁ := by rw [h3]
        _ = ψ ((ψ⁻¹ * z * ψ) u₁) := by rw [MulAut.mul_apply]
        _ = ψ u₁ := by rw [h1']
    simpa [MulAut.mul_apply] using h2
  have zfpf : ∀ u ∈ commSub (⊤ : Subgroup W) Lb, z u = u → u = 1 := by
    intro u hu hzu
    have hfixmem : u ∈ fixV Lb := by
      rw [hLb]
      exact mem_fixV_zpowers_iff.2 hzu
    have hmem : u ∈ commSub (⊤ : Subgroup W) Lb ⊓ fixV Lb := ⟨hu, hfixmem⟩
    rw [hZ] at hmem
    simpa using hmem
  have hstab : s16h_CycN A z ≤ stabSub (commSub (⊤ : Subgroup W) Lb) := by
    intro g hg
    have hginv : g⁻¹ ∈ s16h_CycN A z := (s16h_CycN A z).inv_mem hg
    have hgN : g ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := by rw [hLb]; exact hg.2
    have hnorm : ∀ x ∈ Lb, g * x * g⁻¹ ∈ Lb := fun x hx =>
      ((Subgroup.mem_normalizer_iff (H := Lb)).1 hgN x).1 hx
    have hgNinv : g⁻¹ ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := by
      rw [hLb]; exact hginv.2
    have hnorm' : ∀ x ∈ Lb, g⁻¹ * x * (g⁻¹)⁻¹ ∈ Lb := fun x hx =>
      ((Subgroup.mem_normalizer_iff (H := Lb)).1 hgNinv x).1 hx
    refine mem_stabSub.2 fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · have hthis := commSub_top_stable151b (X := Lb) (g := g⁻¹) hnorm' (g u) hu
      rwa [MulAut.inv_apply_self] at hthis
    · exact commSub_top_stable151b (X := Lb) (g := g) hnorm u hu
  have huniq : ∀ a ∈ A, ∀ b ∈ A, Lb.map (MulAut.conj a).toMonoidHom ≠ Lb →
      Lb.map (MulAut.conj b).toMonoidHom ≠ Lb →
      Lb.map (MulAut.conj a).toMonoidHom = Lb.map (MulAut.conj b).toMonoidHom := by
    intro a ha b hb ha' hb'
    rcases hpairH a ha with h | h
    · exact absurd h ha'
    · rcases hpairH b hb with h2 | h2
      · exact absurd h2 hb'
      · rw [h, h2]
  have hψN : Lb.map (MulAut.conj ψ).toMonoidHom ≠ Lb := by rw [hAB]; exact hBA
  have hidx : (s16h_CycN A z).relIndex A = 2 := by
    show ((A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W))).subgroupOf A).index
      = 2
    rw [← hLb]
    exact s16h_e3_CycTwoG_relIndex_stabilizer_eq_two (X := A) (K := Lb) (x₁ := ψ)
      hψA hψN huniq
  exact
    ⟨ψ,
      { exp2 := hexp
        card_u := hcard
        sup_top := hsup
        psi_mem := hψA
        z_mem := hzA
        one_lt := hq
        z_ord := hzord
        z_fpf := zfpf
        z_triv := ztriv
        stab := hstab
        idx := hidx }⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
