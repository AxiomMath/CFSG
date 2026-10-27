module

public import CFSG.Quasithin.Background.HPair
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Cent
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Matrix
open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private noncomputable def s16h_e3_l3P_matAct {m : ℕ} (δ : GL (Fin m) (ZMod 2))
    (w : Multiplicative (Fin m → ZMod 2)) : Multiplicative (Fin m → ZMod 2) :=
  Multiplicative.ofAdd ((δ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd w)

private theorem s16h_e3_l3P_matAct_mul {m : ℕ} (A B : GL (Fin m) (ZMod 2))
    (w : Multiplicative (Fin m → ZMod 2)) :
    s16h_e3_l3P_matAct A (s16h_e3_l3P_matAct B w) = s16h_e3_l3P_matAct (A * B) w := by
  rw [s16h_e3_l3P_matAct, s16h_e3_l3P_matAct, s16h_e3_l3P_matAct, toAdd_ofAdd,
    Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]

private noncomputable def s16h_e3_l3P_matMulEquiv {m : ℕ} (A : GL (Fin m) (ZMod 2)) :
    Multiplicative (Fin m → ZMod 2) ≃* Multiplicative (Fin m → ZMod 2) where
  toFun := s16h_e3_l3P_matAct A
  invFun := s16h_e3_l3P_matAct A⁻¹
  left_inv w := by
    change s16h_e3_l3P_matAct A⁻¹ (s16h_e3_l3P_matAct A w) = w
    rw [s16h_e3_l3P_matAct_mul, inv_mul_cancel, s16h_e3_l3P_matAct,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv w := by
    change s16h_e3_l3P_matAct A (s16h_e3_l3P_matAct A⁻¹ w) = w
    rw [s16h_e3_l3P_matAct_mul, mul_inv_cancel, s16h_e3_l3P_matAct,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    simp only [s16h_e3_l3P_matAct, toAdd_ofAdd, toAdd_mul, Matrix.mulVec_add]

private theorem s16h_e3_l3_coordP_data {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsL3 ↥L 1) {I : Subgroup W}
    (hI : BinaryNaturalSL L I ⊥ 3 1) :
    ∃ (ρ : ↥L ≃* GL (Fin 3) (ZMod 2))
      (f : ↥I ≃* Multiplicative (Fin 3 → ZMod 2)),
      ∀ (l : ↥L) (u : W) (hu : u ∈ I) (hlu : (l : MulAut W) u ∈ I),
        f ⟨(l : MulAut W) u, hlu⟩ = s16h_e3_l3P_matAct (ρ l) (f ⟨u, hu⟩) := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hI
  obtain ⟨f₀, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  have hcardDom : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
    CFSG.Open.StatedAPI.card_statedSL_three_zmod_two
  have hcardCod : Nat.card ↥L = 168 := card_eq_of_isL3 hL
  have hbij : Function.Bijective π :=
    (Nat.bijective_iff_surjective_and_card π).mpr ⟨hπ.1, by rw [hcardDom, hcardCod]⟩
  let eπ : ↥(StatedSL 3 (ZMod 2)) ≃* ↥L := MulEquiv.ofBijective π hbij
  have hfinj : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  have hfbij : Function.Bijective f₀ := ⟨hfinj, hfs⟩
  let f : ↥I ≃* Multiplicative (Fin 3 → ZMod 2) := MulEquiv.ofBijective f₀ hfbij
  have hTop : StatedSL 3 (ZMod 2) = ⊤ :=
    le_antisymm le_top (fun x _ => FFC.mem_statedSL_zmod x)
  let ι : GL (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop).symm
  have hι : ∀ δ : GL (Fin 3) (ZMod 2),
      ((ι δ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) = δ := fun _ => rfl
  let ρ : ↥L ≃* GL (Fin 3) (ZMod 2) := eπ.symm.trans ι.symm
  refine ⟨ρ, f, ?_⟩
  intro l u hu hlu
  let γ : ↥(StatedSL 3 (ZMod 2)) := eπ.symm l
  have hπγ : π γ = l := by
    change eπ (eπ.symm l) = l
    rw [MulEquiv.apply_symm_apply]
  have hγcoe : (γ : GL (Fin 3) (ZMod 2)) = (ρ l : GL (Fin 3) (ZMod 2)) := by
    have hρl : (ρ l : GL (Fin 3) (ZMod 2)) = ι.symm γ := rfl
    rw [hρl]
    exact (hι (ι.symm γ)).symm
  have h1 : f₀ ⟨(l : MulAut W) u, hlu⟩ =
      CFSG.Quasithin.natAct (StatedSL 3 (ZMod 2)) γ (f₀ ⟨u, hu⟩) := by
    have hu' : ((π γ : ↥L) : MulAut W) u ∈ I := by rw [hπγ]; exact hlu
    have hfe' := hfe γ ⟨u, hu⟩ hu'
    have hcoe : ((π γ : ↥L) : MulAut W) u = (l : MulAut W) u :=
      congrArg (fun x : ↥L => ((x : MulAut W) u)) hπγ
    have hsub : (⟨((π γ : ↥L) : MulAut W) u, hu'⟩ : ↥I) = ⟨(l : MulAut W) u, hlu⟩ :=
      Subtype.ext hcoe
    rwa [hsub] at hfe'
  have h2 : f ⟨(l : MulAut W) u, hlu⟩ =
      CFSG.Quasithin.natAct (StatedSL 3 (ZMod 2)) γ (f ⟨u, hu⟩) := h1
  rw [h2]
  simp only [CFSG.Quasithin.natAct, s16h_e3_l3P_matAct, hγcoe]

private theorem s16h_e3_l3_coordP_inv {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hI : BinaryNaturalSL L I ⊥ 3 1) :
    ∀ l ∈ L, ∀ u ∈ I, l u ∈ I := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hI
  intro l hl u hu
  exact hπ.2.2.2.1 ⟨l, hl⟩ u hu

theorem s16h_e3_l3_two_iso {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hL : IsL3 ↥L 1) {I : Fin 3 → Subgroup W}
    (hI : ∀ i, BinaryNaturalSL L (I i) ⊥ 3 1) :
    ∃ i j : Fin 3, i ≠ j ∧ H.Pair.IsoMod L (I i) (I j) := by
  choose ρ f hf using fun i => s16h_e3_l3_coordP_data hL (hI i)
  let δ : Fin 3 → MulAut ↥L := fun i => (ρ i).trans (ρ 0).symm
  let Inn : Subgroup (MulAut ↥L) := (MulAut.conj : ↥L →* MulAut ↥L).range
  have hinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply s16h_isL3_centreless hL a
    intro b
    have h := congrArg (fun φ : MulAut ↥L => φ b) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h]
  have hInncard : Nat.card Inn = Nat.card ↥L := by
    have h : Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range = Nat.card ↥L :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    simpa [Inn] using h
  have h168 : Nat.card ↥L = 168 := card_eq_of_isL3 hL
  have hAutdvd : Nat.card (MulAut ↥L) ∣ 336 := card_mulAut_dvd_of_isL3 hL
  have hInnindex : Inn.index ≤ 2 := by
    have h := Subgroup.index_mul_card Inn
    rw [hInncard, h168] at h
    have hAutle : Nat.card (MulAut ↥L) ≤ 336 := Nat.le_of_dvd (by norm_num) hAutdvd
    have hle : Inn.index * 168 ≤ 2 * 168 := by
      rw [h]
      rwa [show (336 : ℕ) = 2 * 168 by norm_num] at hAutle
    exact Nat.le_of_mul_le_mul_right hle (by norm_num)
  have hquotcard : Nat.card (MulAut ↥L ⧸ Inn) ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hInnindex
  let g : Fin 3 → MulAut ↥L ⧸ Inn := fun i => QuotientGroup.mk (δ i)
  have hlt : Nat.card (MulAut ↥L ⧸ Inn) < Nat.card (Fin 3) := by
    rw [Nat.card_fin]
    exact lt_of_le_of_lt hquotcard (by norm_num)
  have hpin : ∃ i j : Fin 3, i ≠ j ∧ g i = g j := by
    by_contra hcon
    have hg : Function.Injective g := by
      intro i j hij
      by_contra hne
      exact hcon ⟨i, j, hne, hij⟩
    have hcard := Nat.card_le_card_of_injective g hg
    exact absurd hcard (not_le.mpr hlt)
  obtain ⟨i, j, hij, heq⟩ := hpin
  have hmem : (δ i)⁻¹ * δ j ∈ Inn := by
    change QuotientGroup.mk (δ i) = QuotientGroup.mk (δ j) at heq
    exact QuotientGroup.eq.mp heq
  obtain ⟨l₀, hl₀⟩ := hmem
  have hδ : δ j = δ i * MulAut.conj l₀ := by
    have h1 : δ i * ((δ i)⁻¹ * δ j) = δ j := by group
    rw [← hl₀] at h1
    exact h1.symm
  set A : GL (Fin 3) (ZMod 2) := ρ i l₀ with hA
  have hρ : ∀ x : ↥L, ρ j x = A * ρ i x * A⁻¹ := by
    intro x
    have h := congrArg (fun φ : MulAut ↥L => φ x) hδ
    simp only [δ, MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply] at h
    have h2 : ρ j x = ρ i (l₀ * x * l₀⁻¹) := (ρ 0).symm.injective h
    rw [h2, hA]
    simp only [map_mul, map_inv]
  refine ⟨i, j, hij, ?_⟩
  let Ae : Multiplicative (Fin 3 → ZMod 2) ≃* Multiplicative (Fin 3 → ZMod 2) :=
    s16h_e3_l3P_matMulEquiv A
  have hAe : ∀ v, Ae v = s16h_e3_l3P_matAct A v := fun v => rfl
  let e : ↥(I i) ≃* ↥(I j) := (f i).trans (Ae.trans (f j).symm)
  have he : ∀ u : ↥(I i), f j (e u) = s16h_e3_l3P_matAct A (f i u) := by
    intro u
    change f j ((f j).symm (Ae (f i u))) = s16h_e3_l3P_matAct A (f i u)
    rw [MulEquiv.apply_symm_apply, hAe]
  refine ⟨e, ?_⟩
  intro l hl w h
  let l' : ↥L := ⟨l, hl⟩
  have hinvj : (l : MulAut W) (e w : W) ∈ I j :=
    s16h_e3_l3_coordP_inv (hI j) l hl (e w : W) (e w).2
  have hfi := hf i l' w w.2 h
  have hfj := hf j l' (e w : W) (e w).2 hinvj
  have hAρ : A * ρ i l' = ρ j l' * A := by
    rw [hρ l']
    group
  have hL : f j (e ⟨l w, h⟩) = s16h_e3_l3P_matAct (ρ j l') (f j (e w)) := by
    calc f j (e ⟨l w, h⟩)
        = s16h_e3_l3P_matAct A (f i ⟨l w, h⟩) := he ⟨l w, h⟩
      _ = s16h_e3_l3P_matAct A (s16h_e3_l3P_matAct (ρ i l') (f i w)) := by rw [hfi]
      _ = s16h_e3_l3P_matAct (A * ρ i l') (f i w) := s16h_e3_l3P_matAct_mul _ _ _
      _ = s16h_e3_l3P_matAct (ρ j l' * A) (f i w) := by rw [hAρ]
      _ = s16h_e3_l3P_matAct (ρ j l') (s16h_e3_l3P_matAct A (f i w)) :=
            (s16h_e3_l3P_matAct_mul _ _ _).symm
      _ = s16h_e3_l3P_matAct (ρ j l') (f j (e w)) := by rw [he w]
  have heeq : e ⟨l w, h⟩ = ⟨(l : MulAut W) (e w : W), hinvj⟩ := by
    apply (f j).injective
    rw [hL, hfj]
  exact congrArg Subtype.val heeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
