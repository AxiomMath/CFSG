module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Free
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Local

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem conjSet_eq_of_mem {L X Y : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) :
    conjSet X Y = conjSet L Y := by
  obtain ⟨n, hn, rfl⟩ := hX
  ext Z
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * n, Y.mul_mem hm hn, CFSG.Quasithin.B19.map_conj_map_conj L m n⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m * n⁻¹, Y.mul_mem hm (Y.inv_mem hn), ?_⟩
    rw [CFSG.Quasithin.B19.map_conj_map_conj, inv_mul_cancel_right]

omit [Finite W] in
theorem eq_of_sup_fixV_eq {H : Subgroup (MulAut W)} {I U : Subgroup W} (hI : I ∈ irrSet H)
    (hU : U ∈ irrSet H) (h : I ⊔ fixV H = U ⊔ fixV H) : I = U :=
  calc I = commSub I H := hI.1.symm
    _ = commSub (I ⊔ fixV H) H := (CFSG.Quasithin.commSub_sup_fixV le_rfl).symm
    _ = commSub (U ⊔ fixV H) H := by rw [h]
    _ = commSub U H := CFSG.Quasithin.commSub_sup_fixV le_rfl
    _ = U := hU.1

omit [Finite W] in
theorem not_commSub_le_map_conj {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {g : MulAut W} (hg : g ∈ Y) {I : Subgroup W}
    {X : Subgroup (MulAut W)} (hXI : ¬ commSub I X ≤ fixV H) :
    ¬ commSub (I.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) ≤ fixV H := by
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  have hgH' : ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
    intro x hx
    simpa using hn g⁻¹ (Y.inv_mem hg) x hx
  intro h
  apply hXI
  rw [commSub_map_conj, ← map_fixV_of_normalizes (hn g hg) hgH'] at h
  exact (Subgroup.map_le_map_iff_of_injective g.injective).mp h

section Moves

variable (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
  (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (ht : t ∈ Y)
  (ht2 : orderOf t = 2) (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
  (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
  (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) {U : Subgroup W} (hU : U ∈ irrSet H)
  (hLU : ¬ commSub U L ≤ fixV H)
include hD hW hL hH ht ht2 hfix hm hmove hU hLU

theorem eq_of_not_commSub_le {I : Subgroup W} (hI : I ∈ irrSet H)
    (hLI : ¬ commSub I L ≤ fixV H) : I = U :=
  eq_of_sup_fixV_eq hI hU
    (sup_fixV_eq_of_not_commSub_le hD hW hL hH ht ht2 hfix hm hmove hU hLU hI hLI)

omit hD hW ht2 hm hmove [Finite W] in
theorem not_commSub_map_conj_le : ¬ commSub U (L.map (MulAut.conj t).toMonoidHom) ≤ fixV H := by
  have h := not_commSub_le_map_conj hL hH ht hLU
  rwa [hfix U hU] at h

omit hD in
theorem inf_fixV_eq_bot_of_moves : U ⊓ fixV H = ⊥ := by
  have hUt := hfix U hU
  have htU := not_commSub_zpowers_le_of_map_ne hL hH ht hmove hU hUt hLU
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  refine inf_fixV_eq_bot_of_pair hW hL hH hU (self_mem_conjSet L Y) hLt (Ne.symm hmove) hLU
    (not_commSub_map_conj_le hL hH ht hfix hU hLU) ?_
  intro K hK hKL hKLt
  exact commSub_le_of_ne_of_ne hW hL hH ht ht2 hm hU hUt hLU htU hK hKL hKLt

theorem exists_eq_map_of_moves {I : Subgroup W} (hI : I ∈ irrSet H) :
    ∃ g ∈ Y, I = U.map g.toMonoidHom := by
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  obtain ⟨X, ⟨h, hh, rfl⟩, hXI⟩ := exists_conj_not_le hL hH hI
  have hJ : I.map h⁻¹.toMonoidHom ∈ irrSet H :=
    map_mem_irrSet (hn h⁻¹ (Y.inv_mem hh)) (by simpa using hn h hh) hI
  have hLJ : ¬ commSub (I.map h⁻¹.toMonoidHom) L ≤ fixV H := by
    have h1 := not_commSub_le_map_conj hL hH (Y.inv_mem hh) hXI
    rwa [CFSG.Quasithin.B19.map_conj_map_conj, inv_mul_cancel,
      CFSG.Quasithin.Asc81c.Pf.map_conj_one] at h1
  have hJU := eq_of_not_commSub_le hD hW hL hH ht ht2 hfix hm hmove hU hLU hJ hLJ
  refine ⟨h, hh, ?_⟩
  rw [← hJU, Subgroup.map_map]
  ext x
  simp

theorem fixV_eq_bot_of_moves
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) : fixV H = ⊥ := by
  obtain ⟨h1, -, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.1
  have hU0 := inf_fixV_eq_bot_of_moves hW hL hH ht ht2 hfix hm hmove hU hLU
  have h0 := iSup_inf_fixV_eq_bot hW H (irrSet H) fun I hI => by
    obtain ⟨g, hg, rfl⟩ := exists_eq_map_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hI
    have hgH' : ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
      intro x hx
      simpa using hn g⁻¹ (Y.inv_mem hg) x hx
    have hI0 : U.map g.toMonoidHom ⊓ fixV H = ⊥ := by
      rw [← map_fixV_of_normalizes (hn g hg) hgH', ← Subgroup.map_inf_eq _ _ _ g.injective, hU0,
        Subgroup.map_bot]
    refine ⟨hI.2.2.1, fun J hJs hJI => ?_, hI0⟩
    have h2 := hI.2.2.2.2 J hJs (by rw [hI0]; exact bot_le) hJI
    rwa [hI0] at h2
  rwa [htop, top_inf_eq] at h0

theorem commSub_zpowers_le_of_ne {I : Subgroup W} (hI : I ∈ irrSet H) (hIU : I ≠ U) :
    commSub I (Subgroup.zpowers t) ≤ fixV H := by
  by_contra htI
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  have htC : t ∈ stabSub (fixV H) := le_stabSub_fixV hn ht
  have hIt := hfix I hI
  obtain ⟨h, hh, rfl⟩ := exists_eq_map_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hI
  set X := L.map (MulAut.conj h).toMonoidHom with hX
  set X' := (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj h).toMonoidHom with hX'
  have hXc : X ∈ conjSet L Y := ⟨h, hh, rfl⟩
  have hX'c : X' ∈ conjSet L Y :=
    ⟨h * t, Y.mul_mem hh ht, CFSG.Quasithin.B19.map_conj_map_conj L h t⟩
  have hXcomp : IsComponentOf X Y := isComponentOf_map_conj_of_mem hL hh
  have hHX : H = ⨆ Z ∈ conjSet X Y, Z := by rw [conjSet_eq_of_mem hXc]; exact hH
  have hdX : dMinDeg ↥X = dMinDeg ↥L :=
    (dMinDeg_congr (L.equivMapOfInjective _ (MulAut.conj h).injective)).symm
  have hmX : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥X := by rw [hdX]; exact hm
  have hXI : ¬ commSub (U.map h.toMonoidHom) X ≤ fixV H := not_commSub_le_map_conj hL hH hh hLU
  have hX'I : ¬ commSub (U.map h.toMonoidHom) X' ≤ fixV H :=
    not_commSub_le_map_conj hL hH hh (not_commSub_map_conj_le hL hH ht hfix hU hLU)
  have hXX' : X' ≠ X := by
    intro h'
    have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
    exact hmove (Subgroup.map_injective hinj h')
  by_cases hXt : X.map (MulAut.conj t).toMonoidHom = X
  · apply hX'I
    have hX'c' : X' ∈ conjSet X Y := by rw [conjSet_eq_of_mem hXc]; exact hX'c
    exact commSub_le_of_ne_of_ne hW hXcomp hHX ht ht2 hmX hI hIt hXI htI hX'c' hXX'
      (by rw [hXt]; exact hXX')
  · obtain ⟨eU, hdU, hrkU⟩ :=
      exists_rk_commSub_eq hD hW hL hH ht ht2 hm hmove htC hU (hfix U hU) hLU
    obtain ⟨eI, hdI, hrkI⟩ := exists_rk_commSub_eq hD hW hXcomp hHX ht ht2 hmX hXt htC hI hIt hXI
    have hne : U.map h.toMonoidHom ⊔ fixV H ≠ U ⊔ fixV H := fun h' =>
      hIU (eq_of_sup_fixV_eq hI hU h')
    have hsum := rk_commSub_add_le_rkIdx hL hH htC hU (hfix U hU) hI hIt hne
    omega

theorem commSub_le_of_ne {I : Subgroup W} (hI : I ∈ irrSet H) (hIU : I ≠ U) :
    commSub I L ≤ fixV H ∧ commSub I (L.map (MulAut.conj t).toMonoidHom) ≤ fixV H := by
  have hL' : commSub I L ≤ fixV H := by
    by_contra h
    exact hIU (eq_of_not_commSub_le hD hW hL hH ht ht2 hfix hm hmove hU hLU hI h)
  refine ⟨hL', ?_⟩
  by_contra h
  have h2 := not_commSub_le_map_conj hL hH ht h
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  rw [hfix I hI, map_conj_map_conj_of_mul_eq_one L ht2'] at h2
  exact h2 hL'

end Moves

end CFSG.LocalAnalysis.WeakClosure81
