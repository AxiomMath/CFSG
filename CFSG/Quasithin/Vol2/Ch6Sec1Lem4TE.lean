module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TW
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Background.C58Transport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.H13.Tits614

section Transport

variable {Y Z : Type} [Group Y] [Group Z]

theorem mem_center_map_subtype614 {S : Subgroup Y} {g : Y} :
    g ∈ (Subgroup.center S).map S.subtype ↔ g ∈ S ∧ ∀ s ∈ S, s * g = g * s := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun s hs => congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨s, hs⟩)⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext (h s s.2), rfl⟩

theorem map_titsH614 (e : Y ≃* Z) (S : Subgroup Y) :
    (titsH614 S).map e.toMonoidHom = titsH614 (S.map e.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, titsH614, titsH614, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [SetLike.mem_coe, mem_center_map_subtype614] at hg
    have hg' : e.symm g ∈ (Subgroup.center S).map S.subtype := by
      rw [mem_center_map_subtype614]
      refine ⟨?_, fun s hs => ?_⟩
      · obtain ⟨y, hy, hyg⟩ := hg.1
        rw [← hyg]
        simpa using hy
      · have := hg.2 (e s) ⟨s, hs, rfl⟩
        apply e.injective
        simpa using this
    have := h _ hg'
    apply e.symm.injective
    simpa using this
  · intro h g hg
    rw [SetLike.mem_coe, mem_center_map_subtype614] at hg
    have hg' : e g ∈ (Subgroup.center (S.map e.toMonoidHom)).map (S.map e.toMonoidHom).subtype := by
      rw [mem_center_map_subtype614]
      refine ⟨⟨g, hg.1, rfl⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have := hg.2 s hs
      simpa using congrArg e this
    have := h _ hg'
    apply e.injective
    simpa using this

theorem mulAut_congr_conj_tits614 (e : Y ≃* Z) (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

end Transport

theorem isSylowTwoOf_titsS614 :
    IsSylowTwoOf (titsS.subgroupOf titsD) ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 11) (by
    rw [card_subgroupOf_eq titsS_le_titsD, titsQS_facts.2.2.2]; norm_num), ?_⟩
  have h : ((titsS.subgroupOf titsD).subgroupOf ⊤).index = (titsS.subgroupOf titsD).index :=
    Subgroup.relIndex_top_right _
  have h2 := (titsS.subgroupOf titsD).card_mul_index
  rw [card_subgroupOf_eq titsS_le_titsD, titsQS_facts.2.2.2, card_titsD] at h2
  rw [h]
  have : (titsS.subgroupOf titsD).index = 8775 := by omega
  rw [this]
  decide

theorem exists_mulEquiv_titsS614
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* titsD) {S₀ : Subgroup Y}
    (hS₀ : IsSylowTwoOf S₀ ⊤) :
    ∃ e' : Y ≃* titsD, S₀.map e'.toMonoidHom = titsS.subgroupOf titsD := by
  have : Finite titsD := Finite.of_equiv Y e.toEquiv
  have hS₁ : IsSylowTwoOf (S₀.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS₀.2.1.map _, ?_⟩
    have h1 : ((S₀.map e.toMonoidHom).subgroupOf ⊤).index = (S₀.map e.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have h2 : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right _
    have h3 : (S₀.map e.toMonoidHom).index = S₀.index := by
      simp
    rw [h1, h3, ← h2]
    exact hS₀.2.2
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_titsS614 hS₁
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_⟩
  have e1 : S₀.map (e.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (S₀.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [e1, hg]
  show B6.conjSub g⁻¹ (B6.conjSub g (titsS.subgroupOf titsD)) = _
  rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]

theorem titsH614_titsS :
    titsH614 (titsS.subgroupOf titsD) = titsH.subgroupOf titsD := by
  obtain ⟨-, hH, -⟩ := AT_Tits_intrinsic_local_pair
  ext x
  rw [titsH614, Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, hH, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, fun g hg => ?_⟩
    rw [SetLike.mem_coe, mem_center_map_subtype614] at hg
    have hgD : g ∈ titsD := titsS_le_titsD hg.1
    have := h ⟨g, hgD⟩ (by
      rw [SetLike.mem_coe, mem_center_map_subtype614]
      exact ⟨hg.1, fun s hs => Subtype.ext (hg.2 s hs)⟩)
    exact congrArg Subtype.val this
  · rintro ⟨-, h⟩ g hg
    rw [SetLike.mem_coe, mem_center_map_subtype614] at hg
    apply Subtype.ext
    apply h
    rw [SetLike.mem_coe, mem_center_map_subtype614]
    exact ⟨hg.1, fun s hs => by
      have := hg.2 ⟨s, titsS_le_titsD hs⟩ hs
      exact congrArg Subtype.val this⟩

theorem titsBasicFact_holds :
    TitsBasicFact := by
  intro Y _ h
  obtain ⟨e⟩ := titsModelEquiv Y 2 1 h
  have : IsSimpleGroup titsD := titsD_simple
  have : Nontrivial titsD := titsD_nontrivial
  have hnc : ∃ a b : titsD, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.center titsD = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hc y x
    rw [titsD_center] at htop
    exact bot_ne_top htop
  have : Nontrivial Y := e.toEquiv.nontrivial
  have : IsSimpleGroup Y :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hncY : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h' => hab (by simpa using congrArg e h')⟩
  obtain ⟨hq, hz⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncY
  exact ⟨Finite.of_equiv titsD e.symm.toEquiv, hq, hz⟩

theorem titsOver5Fact_holds :
    TitsOver5Fact := by
  intro Y _ _ h S₀ P hS₀ hSP h5
  obtain ⟨e⟩ := titsModelEquiv Y 2 1 h
  obtain ⟨e', he'⟩ := exists_mulEquiv_titsS614 e hS₀
  set f : Y →* Equiv.Perm (Fin 1755) := titsD.subtype.comp e'.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp e'.injective
  have hS : S₀.map f = titsS := by
    rw [hf, ← Subgroup.map_map, he', Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr titsS_le_titsD]
  have hPD : P.map f ≤ titsD := by
    rintro _ ⟨y, -, rfl⟩
    exact (e' y).2
  have hSP' : titsS ≤ P.map f := hS ▸ Subgroup.map_mono hSP
  have h5' : titsS.relIndex (P.map f) = 5 := by
    rw [← hS, Subgroup.relIndex_map_map_of_injective _ _ hfinj, h5]
  have hP := eq_titsH_of_relIndex_five614 hPD hSP' h5'
  have hH : (titsH614 S₀).map f = titsH := by
    rw [hf, ← Subgroup.map_map, map_titsH614, he', titsH614_titsS,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr titsH_le_titsD]
  exact Subgroup.map_injective hfinj (hP.trans hH.symm)

theorem titsWCFact_holds :
    TitsWCFact := by
  intro Y _ _ h S₀ hS₀ Tst U hT2 hST hUT hU1 hHU _ hwc
  obtain ⟨e⟩ := titsModelEquiv Y 2 1 h
  obtain ⟨e', he'⟩ := exists_mulEquiv_titsS614 e hS₀
  set Ψ : MulAut Y ≃* titsA := (MulAut.congr e').trans titsConjEquiv.symm with hΨ
  set F : MulAut Y →* Equiv.Perm (Fin 1755) := titsA.subtype.comp Ψ.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp Ψ.injective
  have hFconj : ∀ y : Y, F (MulAut.conj y) = (e' y : Equiv.Perm (Fin 1755)) := by
    intro y
    have h1 : titsConjEquiv ⟨(e' y : Equiv.Perm (Fin 1755)), titsD_le_titsA (e' y).2⟩ =
        MulAut.congr e' (MulAut.conj y) := by
      rw [mulAut_congr_conj_tits614]
      refine MulEquiv.ext fun d => Subtype.ext ?_
      show ((titsConj ⟨_, titsD_le_titsA (e' y).2⟩ d : titsD) : Equiv.Perm (Fin 1755)) = _
      rw [coe_titsConj_apply, MulAut.conj_apply]
      rfl
    have h2 : Ψ (MulAut.conj y) = ⟨(e' y : Equiv.Perm (Fin 1755)), titsD_le_titsA (e' y).2⟩ := by
      rw [hΨ, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
    show ((Ψ (MulAut.conj y) : titsA) : Equiv.Perm (Fin 1755)) = _
    rw [h2]
  have hcomp : F.comp (MulAut.conj : Y →* MulAut Y) = titsD.subtype.comp e'.toMonoidHom :=
    MonoidHom.ext hFconj
  have hmapc : ∀ W : Subgroup Y,
      (W.map (MulAut.conj : Y →* MulAut Y)).map F = (W.map e'.toMonoidHom).map titsD.subtype := by
    intro W
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have hS : (S₀.map (MulAut.conj : Y →* MulAut Y)).map F = titsS := by
    rw [hmapc, he', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr titsS_le_titsD]
  have hH : ((titsH614 S₀).map (MulAut.conj : Y →* MulAut Y)).map F = titsH := by
    rw [hmapc, map_titsH614, he', titsH614_titsS, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr titsH_le_titsD]
  have hTA : Tst.map F ≤ titsA := by
    rintro _ ⟨σ, -, rfl⟩
    exact (Ψ σ).2
  have hST' : titsS ≤ Tst.map F := hS ▸ Subgroup.map_mono hST
  have hU1' : U.map F ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective U hFinj]
  have hHU' : titsH ≤ Subgroup.normalizer ((U.map F : Subgroup _) : Set (Equiv.Perm (Fin 1755))) :=
    hH ▸ ((Subgroup.map_mono hHU).trans (Subgroup.le_normalizer_map F))
  have hwc' : ∀ d ∈ titsD, (U.map F).map (MulAut.conj d).toMonoidHom ≤ Tst.map F →
      (U.map F).map (MulAut.conj d).toMonoidHom = U.map F := by
    intro d hd hle
    set y := e'.symm ⟨d, hd⟩ with hydef
    have hy : F (MulAut.conj y) = d := by rw [hFconj, hydef, MulEquiv.apply_symm_apply]
    have hcomm : (U.map (MulAut.conj (MulAut.conj y)).toMonoidHom).map F =
        (U.map F).map (MulAut.conj d).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext σ : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv, hy]
    rw [← hcomm] at hle ⊢
    rw [hwc y ((Subgroup.map_le_map_iff_of_injective hFinj).mp hle)]
  have hJ := titsJ_le_of_wc614 hTA (hT2.map F) hST' (Subgroup.map_mono hUT) hU1' hHU' hwc'
  rw [← Subgroup.map_le_map_iff_of_injective hFinj]
  have hfinj : Function.Injective (titsD.subtype.comp e'.toMonoidHom) :=
    Subtype.val_injective.comp e'.injective
  have hcore : ((pCoreOf 2 (titsH614 S₀)).map (MulAut.conj : Y →* MulAut Y)).map F =
      pCoreOf 2 titsH := by
    rw [hmapc, Subgroup.map_map, ← C58.pCoreOf_map_of_injective hfinj, ← Subgroup.map_map,
      map_titsH614, he', titsH614_titsS, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr titsH_le_titsD]
  rw [hcore]
  exact pCoreOf_titsH_le614.trans hJ

theorem res614Tits_of_core
    (h331 : Stmt3_3_1) (h512 : Stmt5_1_2) (h513 : Stmt5_1_3) (h37 : A37ForSQTK)
    (hcore : Res614TitsCore) : Res614Tits :=
  res614Tits_of h331 h512 h513 h37 titsBasicFact_holds titsOver5Fact_holds titsWCFact_holds hcore

end CFSG.Quasithin.H13
