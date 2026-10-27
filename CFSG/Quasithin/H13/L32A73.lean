module

public import CFSG.Quasithin.H13.L32ASetting
public import CFSG.Quasithin.H13.L32ARuTwo
public import CFSG.Quasithin.Background.F9Fourteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace L32A

variable {G : Type} [Group G] [Finite G]

theorem exists_sl3_mulVec_eq : ∀ x y : Fin 3 → ZMod 2, x ≠ 0 → y ≠ 0 →
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x = y := by
  decide +kernel

theorem exists_conj_eq_of_mem {T L V : Subgroup G} (h : Hyp1281One G T L V 3) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨hcard, hsq, hcomm⟩ := h.card_sq
  have hA : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One h
  have : IsMulCommutative ↥V :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hx : Multiplicative.toAdd (e ⟨v, hv⟩) ≠ 0 := by
    intro h0
    apply hv1
    have : e ⟨v, hv⟩ = 1 := by rw [← ofAdd_toAdd (e ⟨v, hv⟩), h0]; rfl
    have := congrArg Subtype.val (e.injective (this.trans (map_one e).symm))
    simpa using this
  have hy : Multiplicative.toAdd (e ⟨w, hw⟩) ≠ 0 := by
    intro h0
    apply hw1
    have : e ⟨w, hw⟩ = 1 := by rw [← ofAdd_toAdd (e ⟨w, hw⟩), h0]; rfl
    have := congrArg Subtype.val (e.injective (this.trans (map_one e).symm))
    simpa using this
  obtain ⟨A, hAxy⟩ := exists_sl3_mulVec_eq _ _ hx hy
  set φ : MulAut ↥V := ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL 3)).symm
    (Matrix.SpecialLinearGroup.toGL A) with hφ
  have hφv : φ ⟨v, hv⟩ = ⟨w, hw⟩ := by
    have h1 : ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL 3)) φ =
        Matrix.SpecialLinearGroup.toGL A := MulEquiv.apply_symm_apply _ _
    have h2 := mulAutPiEquivGL_mulVec 3 (MulAut.congr e φ)
      (Multiplicative.toAdd (e ⟨v, hv⟩))
    rw [show Vol2.Ch10.SecA.mulAutPiEquivGL 3 (MulAut.congr e φ) =
      Matrix.SpecialLinearGroup.toGL A from h1, MulAut.congr_apply] at h2
    simp only [ofAdd_toAdd, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    apply e.injective
    rw [← ofAdd_toAdd (e (φ ⟨v, hv⟩)), ← h2]
    show Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (Multiplicative.toAdd (e ⟨v, hv⟩))) = e ⟨w, hw⟩
    rw [hAxy, ofAdd_toAdd]
  have hφA : φ ∈ autOn L V := by rw [hA]; exact Subgroup.mem_top _
  obtain ⟨x, hxL, hxφ⟩ := hφA
  refine ⟨(x : G), hxL, ?_⟩
  have := congrArg (fun ψ : MulAut ↥V => ((ψ ⟨v, hv⟩ : ↥V) : G)) hxφ
  simp only [hφv] at this
  rw [← this]
  rfl

variable {T L V H : Subgroup G}

theorem lemma14_7_3_one (hF : HypF98 T V L (fsuV1 T V) V H) :
    3 ≤ F8.b T V L H ∧ Odd (F8.b T V L H) :=
  hF.three_le_b_and_odd

theorem lemma14_7_3_two (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H) :
    conjClosure (conjClosure V H) L ≤ pCoreOf 2 (L ⊔ T) := by
  have hT := S.hyp.fsu.sylow
  have hTH : T ≤ H := le_sup_right.trans hF.L₁T_le_H
  have hidx : ¬ 2 ∣ (T.subgroupOf H).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow hT.1 hTH hidx
  have hUO : conjClosure V H ≤ pCoreOf 2 H :=
    conjClosure_le fun k hk v hv =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hk) v).mp (hF.V_le_pCoreOf hv)
  have hUQ : conjClosure V H ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← hF.cT]
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨hOT (hUO hu), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact F7.isElemAbelian_comm hF.F911_2 (le_conjClosure V H hv) hu
  exact conjClosure_le fun l hl u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left hl)) u).mp (hUQ hu)

theorem lemma14_7_3_three (hF : HypF98 T V L (fsuV1 T V) V H) :
    (∀ x ∈ conjClosure (conjClosure V H) L, ∀ y ∈ conjClosure (conjClosure V H) L,
      x * y = y * x) ↔ 3 < F8.b T V L H :=
  hF.F914_1 (le_conjClosure V H)

theorem lemma14_7_3_four (S : Setting147 G T L V H) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) (hF : HypF98 T V L (fsuV1 T V) V H) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hH : H = Subgroup.centralizer (fsuV1 T V : Set G)) {k : G} (hk : k ∈ H)
    (hA : conjSub k⁻¹ (F8.A₁ (fsuV1 T V) (g : G)) ≤ V) :
    F8.b T V L H = 3 ∧
      ∃ l ∈ L, conjSub k⁻¹ (F8.Uγ V H (g : G)) = conjSub l (conjClosure V H) :=
  hF.F914_3 s (fun _ hv _ hw hv1 hw1 =>
    exists_conj_eq_of_mem (S.hyp.hyp1281One h13322 hMod) hv hw hv1 hw1) hH hk hA

end L32A

end CFSG.Quasithin.H13
