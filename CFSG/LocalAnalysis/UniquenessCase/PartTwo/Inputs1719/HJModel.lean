module

public import CFSG.RankThree.PartTwo.J2Residue.C4725Module
public import CFSG.Quasithin.Background.RonanH143Vocab
public import CFSG.Quasithin.Background.SmithB45J2Holds
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 CFSG.Certificates

abbrev W12 : Type := Multiplicative (Fin 12 → ZMod 2)

noncomputable abbrev hjAct : GL (Fin 12) (ZMod 2) →* MulAut W12 :=
  CFSG.Quasithin.RonanH143.natHom 12 (ZMod 2)

noncomputable def hjL0 : Subgroup (MulAut W12) :=
  Subgroup.closure {hjAct A12, hjAct B12}

noncomputable def hjWord (w : List ℕ) : MulAut W12 :=
  (w.map fun l => if l = 0 then hjAct A12 else hjAct B12).prod

theorem hjAct_apply (g : GL (Fin 12) (ZMod 2)) (v : Fin 12 → ZMod 2) :
    hjAct g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v) := rfl

theorem hjAct_injective : Function.Injective hjAct := by
  intro g h hgh
  apply Units.ext
  ext i j
  have := congrArg (fun φ : MulAut W12 =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))) i) hgh
  simpa [hjAct_apply, Matrix.mulVec_single_one] using this

theorem signedProd_wordA : signedProd gen12 CFSG.Timmesfeld.Moufang.J2.wordA = A12 := by
  decide +kernel

theorem signedProd_wordB : signedProd gen12 CFSG.Timmesfeld.Moufang.J2.wordB = B12 := by
  decide +kernel

theorem A12_mem_closure : A12 ∈ Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem B12_mem_closure : B12 ∈ Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem d12_mem_closure : d12 ∈ Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) := by
  unfold d12
  refine CFSG.Sporadic.Bridge.wordProd_mem (fun k => ?_) _
  show (if k = 0 then A12 else B12) ∈ _
  split_ifs
  · exact A12_mem_closure
  · exact B12_mem_closure

theorem uABD12_mem (i : ℕ) :
    uABD12 i ∈ Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) := by
  match i with
  | 0 => exact A12_mem_closure
  | 1 => exact B12_mem_closure
  | _ + 2 => exact d12_mem_closure

theorem gen12_mem (j : Fin 7) :
    gen12 j ∈ Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) := by
  match j with
  | ⟨0, _⟩ => exact uABD12_mem 2
  | ⟨_ + 1, _⟩ => exact CFSG.Sporadic.Bridge.wordProd_mem uABD12_mem _

theorem range_repPres :
    repPres.range = Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) := by
  apply le_antisymm
  · rw [repPres, range_wordsHom, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact gen12_mem j
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨signedProd PresentedGroup.of CFSG.Timmesfeld.Moufang.J2.wordA, by
        rw [repPres, wordsHom_signedProd, signedProd_wordA]⟩
    · exact ⟨signedProd PresentedGroup.of CFSG.Timmesfeld.Moufang.J2.wordB, by
        rw [repPres, wordsHom_signedProd, signedProd_wordB]⟩

theorem hjL0_eq_map :
    hjL0 = (Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2)))).map hjAct := by
  rw [hjL0, MonoidHom.map_closure, Set.image_pair]

theorem range_rep12 :
    rep12.range = Subgroup.closure ({A12, B12} : Set (GL (Fin 12) (ZMod 2))) := by
  rw [rep12, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_repPres]

theorem hjL0_eq_range : hjL0 = (hjAct.comp rep12).range := by
  rw [hjL0_eq_map, MonoidHom.range_comp, range_rep12]

theorem hjL0_isSpor : IsSpor ↥hjL0 .J2 := by
  have hinj : Function.Injective (hjAct.comp rep12) := hjAct_injective.comp rep12_injective
  rw [hjL0_eq_range]
  exact ⟨(MonoidHom.ofInjective hinj).symm⟩

theorem hjAct_A12_mem : hjAct A12 ∈ hjL0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem hjAct_B12_mem : hjAct B12 ∈ hjL0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem hjWord_mem (w : List ℕ) : hjWord w ∈ hjL0 := by
  unfold hjWord
  refine Subgroup.list_prod_mem (K := hjL0) (fun x hx => ?_)
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact hjAct_A12_mem
  · exact hjAct_B12_mem

theorem hjL0_isIrrOn : IsIrrOn hjL0 ⊤ ⊥ := by
  refine ⟨bot_lt_top, fun _ _ _ _ => Subgroup.mem_top _, fun x _ u hu => ?_, fun J hJ _ _ => ?_⟩
  · rw [Subgroup.mem_bot] at hu ⊢
    rw [hu]
    exact x.map_one
  · let U : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
      { carrier := {v | Multiplicative.ofAdd v ∈ J}
        add_mem' := fun {a b} ha hb => J.mul_mem ha hb
        zero_mem' := J.one_mem
        smul_mem' := fun c v hv => by
          rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
          · rw [zero_smul]
            exact J.one_mem
          · rw [one_smul]
            exact hv }
    have hA : ∀ v ∈ U, Amat.mulVec v ∈ U := fun v hv => by
      have h : Multiplicative.ofAdd ((A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v) ∈ J :=
        hJ (hjAct A12) hjAct_A12_mem (Multiplicative.ofAdd v) hv
      rw [← Amat_eq] at h
      exact h
    have hB : ∀ v ∈ U, Bmat.mulVec v ∈ U := fun v hv => by
      have h : Multiplicative.ofAdd ((B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v) ∈ J :=
        hJ (hjAct B12) hjAct_B12_mem (Multiplicative.ofAdd v) hv
      rw [← Bmat_eq] at h
      exact h
    rcases CFSG.RankThree.PartTwo.J2Residue.C4725.eq_bot_or_eq_top_of_mulVec_mem U hA hB with
      h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have hw' : Multiplicative.toAdd w ∈ U := hw
      rw [h, Submodule.mem_bot] at hw'
      rw [Subgroup.mem_bot]
      exact Multiplicative.toAdd.injective hw'
    · right
      rw [eq_top_iff]
      intro w _
      have hw' : Multiplicative.toAdd w ∈ U := by rw [h]; exact Submodule.mem_top
      exact hw'

theorem W12_sq (w : W12) : w ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd w i + Multiplicative.toAdd w i = 0
  generalize Multiplicative.toAdd w i = x
  fin_cases x <;> rfl

theorem rk_W12 : rk W12 = 12 := by
  rw [rk, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  exact padicValNat.prime_pow 12

theorem isIrrSec_of_isIrrOn_top {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : IsIrrOn L ⊤ ⊥) : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ :=
  ⟨h.1, fun J hJ _ _ => h.2.2.2 J (fun x hx u hu => hJ ⟨x, hx⟩ u hu) bot_le le_top⟩

theorem card_lt_of_rk_eq_twelve {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hr : rk V = 12) : Nat.card V < 2 ^ 24 := by
  rw [card_eq_two_pow_rk hV, hr]
  norm_num

theorem exists_map_eq_of_realizes {W W' : Type} [CommGroup W] [CommGroup W'] {D : FFModel}
    {L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')}
    (h : D.Realizes L ⊤ ⊥) (h' : D.Realizes L' ⊤ ⊥) :
    ∃ ψ : W ≃* W', L.map (MulAut.congr ψ).toMonoidHom = L' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨π', hπ'⟩ := h'
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv hπ
  obtain ⟨e', he'⟩ := G64.RealizesVia.exists_modEquiv hπ'
  let ψ : W ≃* W' := e.trans e'.symm
  have hint : ∀ (γ : D.Gam) (v : W),
      ψ (((π γ : ↥L) : MulAut W) v) = ((π' γ : ↥L') : MulAut W') (ψ v) := by
    intro γ v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e v)
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hπ.2.2.2.2.2.1 γ m m.2
    have h1 := he γ v m hact hm.symm
    have h2 := he' γ (ψ v) m hact (by
      show e' (e'.symm (e v)) = _
      rw [MulEquiv.apply_symm_apply]
      exact hm.symm)
    show e'.symm (e (((π γ : ↥L) : MulAut W) v)) = _
    rw [h1, ← h2, MulEquiv.symm_apply_apply]
  refine ⟨ψ, le_antisymm ?_ ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨l, hl⟩
    have hconj : (MulAut.congr ψ).toMonoidHom l = ((π' γ : ↥L') : MulAut W') := by
      ext w'
      show ψ (l (ψ.symm w')) = _
      have := hint γ (ψ.symm w')
      rw [hγ, MulEquiv.apply_symm_apply] at this
      exact this
    rw [hconj]
    exact (π' γ).2
  · intro l' hl'
    obtain ⟨γ, hγ⟩ := hπ'.1 ⟨l', hl'⟩
    refine ⟨((π γ : ↥L) : MulAut W), (π γ).2, ?_⟩
    ext w'
    show ψ ((π γ : MulAut W) (ψ.symm w')) = l' w'
    rw [hint, MulEquiv.apply_symm_apply, hγ]

theorem w4Lem11_8Unique_holds :
    ∀ (W W' : Type) [CommGroup W] [Finite W] [CommGroup W'] [Finite W'],
      (∀ w : W, w ^ 2 = 1) → (∀ w : W', w ^ 2 = 1) → rk W = 12 → rk W' = 12 →
      ∀ (L : Subgroup (MulAut W)) (L' : Subgroup (MulAut W')),
        IsSpor ↥L .J2 → IsSpor ↥L' .J2 → IsIrrOn L ⊤ ⊥ → IsIrrOn L' ⊤ ⊥ →
          ∃ ψ : W ≃* W', L.map (MulAut.congr ψ).toMonoidHom = L' := by
  intro W W' _ _ _ _ hW hW' hrk hrk' L L' hL hL' hirr hirr'
  exact exists_map_eq_of_realizes
    (J2Mod.j2SmallModules_holds W hW L hL (isIrrSec_of_isIrrOn_top hirr)
      (card_lt_of_rk_eq_twelve hW hrk))
    (J2Mod.j2SmallModules_holds W' hW' L' hL' (isIrrSec_of_isIrrOn_top hirr')
      (card_lt_of_rk_eq_twelve hW' hrk'))

theorem exists_mulEquiv_map_eq_hjL0 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W = 12) {L : Subgroup (MulAut W)}
    (hL : IsSpor ↥L .J2) (hirr : IsIrrOn L ⊤ ⊥) :
    ∃ ψ : W ≃* W12, L.map (MulAut.congr ψ).toMonoidHom = hjL0 :=
  w4Lem11_8Unique_holds W W12 hW W12_sq hrk rk_W12 L hjL0 hL hjL0_isSpor hirr hjL0_isIrrOn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
