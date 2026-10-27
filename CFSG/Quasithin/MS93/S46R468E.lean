module

public import CFSG.Quasithin.MS93.S46R468B

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem le_normalizer_ptSub {x : Vtx X} {P K : Subgroup X.Universal} (hK : K ≤ stab X x)
    (hKP : K ≤ Subgroup.normalizer (P : Set X.Universal)) :
    K ≤ Subgroup.normalizer (ptSub X x P : Set X.Universal) :=
  le_normalizer_of_map_conj_le fun k hk => by
    rw [← ptSub_smul, MulAction.mem_stabilizer_iff.mp (hK hk),
      map_conj_eq_of_mem_normalizer (hKP hk)]

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem relIndex_ne_zero_of_le_stab (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {K : Subgroup (puAmalgam c.pu.le).Universal}
    (hK : K ≤ stab (puAmalgam c.pu.le) x) (H : Subgroup (puAmalgam c.pu.le).Universal) :
    H.relIndex K ≠ 0 := by
  have := I466b.finite_of_le_stab c.pu hx hK
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem pencil_le_vv (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (P : Subgroup (puAmalgam c.pu.le).Universal) :
    pencil (puAmalgam c.pu.le) x P ≤ Vv _ x :=
  pencil_le fun _ hxβ' _ => I466b.vv_le_vv_of_adj c.pu hx hxβ'

theorem pencil_le_qv (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    (P : Subgroup (puAmalgam c.pu.le).Universal) :
    pencil (puAmalgam c.pu.le) x P ≤ Qv _ β :=
  pencil_le fun β' hxβ' _ => by
    have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hxβ').mp hx
    refine vv_le_qv_of_dist_le_two c.b4 hβ' ?_
    by_cases he : β' = β
    · rw [he, SimpleGraph.dist_self]; omega
    · exact (dist_eq_two_of_adj_adj _ hxβ'.symm hxβ he).le

theorem relIndex_commutator_pencil_ptSub_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {δ p P R : Subgroup (puAmalgam c.pu.le).Universal}
    (hδ : IsPtOn (puAmalgam c.pu.le) α β δ) (hp : IsPtOn (puAmalgam c.pu.le) α β p)
    (hP : IsPtOn (puAmalgam c.pu.le) γ β P) (hR : IsPtOn (puAmalgam c.pu.le) γ β R) (hPR : P ≠ R)
    (hY : pencil (puAmalgam c.pu.le) γ P ≤ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ α p)
    (hU : Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ R ≤ ptSub (puAmalgam c.pu.le) α δ ⊔ Qv _ γ) :
    (ptSub (puAmalgam c.pu.le) γ P).relIndex
      (⁅pencil (puAmalgam c.pu.le) γ P, ptSub _ α δ⁆ ⊔ ptSub _ γ P) ≤ Fintype.card F := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  have h464' := h464 G M T L F φ c
  set Y := pencil (puAmalgam c.pu.le) γ P with hYdef
  set U := ptSub (puAmalgam c.pu.le) α δ with hUdef
  set N := ptSub (puAmalgam c.pu.le) γ P with hNdef
  set C := ⁅Y, U⁆ with hCdef
  set Zα := ZM (puAmalgam c.pu.le) α with hZαdef
  set Zβ := ZH (puAmalgam c.pu.le) β with hZβdef
  set Zγ := ZM (puAmalgam c.pu.le) γ with hZγdef
  have hUVα : U ≤ Vv _ α := ptSub_le_vv c hα δ
  have hUT : U ≤ Qv _ β := (ptSub_le_pencil α δ).trans (pencil_le_qv c hα hαβ δ)
  have hYVγ : Y ≤ Vv _ γ := pencil_le_vv c hγ P
  have hYT : Y ≤ Qv _ β := hY.trans inf_le_left
  have hNY : N ≤ Y := ptSub_le_pencil γ P
  have hNVγ : N ≤ Vv _ γ := ptSub_le_vv c hγ P
  have hZγN : Zγ ≤ N := zm_le_ptSub c hγ hP
  have hTγ : Qv (puAmalgam c.pu.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hγβ.symm
  have hTα : Qv (puAmalgam c.pu.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hVγs : Vv (puAmalgam c.pu.le) γ ≤ stab _ γ := vv_le_stab_self c γ
  have hVαs : Vv (puAmalgam c.pu.le) α ≤ stab _ α := vv_le_stab_self c α
  have hZαs : Zα ≤ stab _ α := (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)
  have hZγs : Zγ ≤ stab _ γ := (zm_le_qv_self _ hγ hb0).trans (qv_le_stab _ γ)
  have hZγV : Zγ ≤ Vv _ γ := zm_le_vv c.pu hγ
  have hCVγ : C ≤ Vv _ γ :=
    (Subgroup.commutator_mono hYVγ le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hUT.trans hTγ).trans (stab_le_normalizer_vv c.pu γ)))
  have hCVα : C ≤ Vv _ α := by
    rw [hCdef, Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hUVα le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hYT.trans hTα).trans (stab_le_normalizer_vv c.pu α)))
  have hPU : P ≤ Usup (puAmalgam c.pu.le) γ β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  have hQγN : Qv (puAmalgam c.pu.le) γ ≤ Subgroup.normalizer (N : Set _) :=
    le_normalizer_ptSub (qv_le_stab _ γ) fun q hq =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hγ
          (I464.usup_le_zm c.pu hγ hγβ (hPU ha))) q hq).symm)
  have hVγN : Vv (puAmalgam c.pu.le) γ ≤ Subgroup.normalizer (N : Set _) :=
    (vv_le_qv c.pu hb hγ).trans hQγN
  have hUN : U ≤ Subgroup.normalizer (N : Set _) :=
    le_normalizer_ptSub (hUT.trans hTγ) fun u hu =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' γ β hγ hγβ (hPU ha)))
          u (hUT hu)).symm)
  have hNUN : ⁅N, U⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp hUN
  have hNUC : ⁅N, U⁆ ≤ C := Subgroup.commutator_mono hNY le_rfl
  set cc := ptConst (puAmalgam c.pu.le) γ (Qv _ β) P R with hccdef
  have hXs : ⁅N, Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ R⁆ ⊔ Zγ ≤ stab _ γ :=
    sup_le ((Subgroup.commutator_mono (hNVγ.trans hVγs) (inf_le_left.trans hTγ)).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer)) hZγs
  have hcc0 : 0 < cc := Nat.pos_of_ne_zero (relIndex_ne_zero_of_le_stab c hγ hXs _)
  have hCZα : Zα.relIndex C ≤ cc := by
    have h1 : Zα.relIndex (C ⊔ Zα) = Zα.relIndex C :=
      S46.relIndex_sup_of_le_normalizer (hCVα.trans (hVαs.trans (stab_le_normalizer_zm _ α)))
    have h2 : Zα.relIndex (C ⊔ Zα) ≤ ptConst (puAmalgam c.pu.le) α (Qv _ β) δ p := by
      rw [ptConst]
      refine Subgroup.relIndex_le_of_le_right (sup_le_sup_right ?_ _)
        (relIndex_ne_zero_of_le_stab c hα (sup_le ((Subgroup.commutator_mono (hUVα.trans hVαs)
          (inf_le_left.trans hTα)).trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
            Subgroup.le_normalizer)) hZαs) _)
      rw [hCdef, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl hY
    have h3 : ptConst (puAmalgam c.pu.le) α (Qv _ β) δ p ≤ cc := by
      by_cases hδp : δ = p
      · rw [hδp, ptConst_self c hα]
        exact hcc0
      · exact (ptConst_eq h464 h465 h466a c hα hαβ hγ hγβ hδ hp hδp hP hR hPR).le
    rw [← h1]
    exact h2.trans h3
  have hZβZα : Zβ ≤ Zα := zh_le_zm _ hαβ
  have hZβZγ : Zβ ≤ Zγ := zh_le_zm _ hγβ
  have hq : Zβ.relIndex Zα = Fintype.card F := (h465 G M T L F φ c α β hα hαβ).2.1
  have hCZβ : Zβ.relIndex C ≤ Fintype.card F * cc := by
    have e := Subgroup.relIndex_inf_mul_relIndex Zβ Zα C
    rw [inf_of_le_left hZβZα] at e
    rw [← e]
    refine Nat.mul_le_mul ?_ hCZα
    rw [← hq]
    exact Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_le_stab c hα hZαs _)
  have hCZγ : Zγ.relIndex C ≤ Fintype.card F * cc :=
    (Subgroup.relIndex_le_of_le_left hZβZγ
      (relIndex_ne_zero_of_le_stab c hγ (hCVγ.trans hVγs) _)).trans hCZβ
  set D := ⁅N, U⁆ ⊔ Zγ with hDdef
  have hDV : D ≤ Vv _ γ := sup_le (hNUC.trans hCVγ) hZγV
  have hVQ : ⁅Vv (puAmalgam c.pu.le) γ, Qv _ γ⁆ ≤ Zγ := (h465 G M T L F φ c γ β hγ hγβ).2.2
  have hDnU : U ≤ Subgroup.normalizer (D : Set _) :=
    le_normalizer_sup (le_normalizer_commutator hUN Subgroup.le_normalizer)
      ((hUT.trans hTγ).trans (stab_le_normalizer_zm _ γ))
  have hDnQ : Qv (puAmalgam c.pu.le) γ ≤ Subgroup.normalizer (D : Set _) :=
    le_normalizer_of_map_conj_le fun q hq => by
      rintro _ ⟨w, hw, rfl⟩
      have e : (MulAut.conj q).toMonoidHom w = w * ⁅w⁻¹, q⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hw (Subgroup.mem_sup_right
        (hVQ (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hDV hw)) hq)))
  have hDn : U ⊔ Qv (puAmalgam c.pu.le) γ ≤ Subgroup.normalizer (D : Set _) := sup_le hDnU hDnQ
  let K : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ U ⊔ Qv (puAmalgam c.pu.le) γ ∧ ∀ n ∈ N, ⁅n, k⁆ ∈ D}
      one_mem' := ⟨Subgroup.one_mem _, fun n _ => by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', fun n hn => ?_⟩
        have e : ⁅n, a * b⁆ = ⁅n, a⁆ * (a * ⁅n, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (ha' n hn) ((Subgroup.mem_normalizer_iff.mp (hDn ha) _).mp
          (hb'' n hn))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun n hn => ?_⟩
        have e : ⁅n, a⁻¹⁆ = a⁻¹ * ⁅n, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hDn (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ (ha' n hn)) }
  have hUK : U ⊔ Qv (puAmalgam c.pu.le) γ ≤ K :=
    sup_le (fun u hu => ⟨Subgroup.mem_sup_left hu, fun n hn =>
        Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hn hu)⟩)
      (fun q hq => ⟨Subgroup.mem_sup_right hq, fun n hn =>
        Subgroup.mem_sup_right (hVQ (Subgroup.commutator_mem_commutator (hNVγ hn) hq))⟩)
  have hc_le : cc ≤ Zγ.relIndex D := by
    rw [hccdef, ptConst]
    refine Subgroup.relIndex_le_of_le_right ?_
      (relIndex_ne_zero_of_le_stab c hγ (hDV.trans hVγs) _)
    refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    exact fun n hn x hx => (hUK (hU hx)).2 n hn
  set C₁ := C ⊔ Zγ with hC₁def
  have hC₁s : C₁ ≤ stab _ γ := sup_le (hCVγ.trans hVγs) hZγs
  have hDC₁ : D ≤ C₁ := sup_le (hNUC.trans le_sup_left) le_sup_right
  have hstep1 : N.relIndex (C ⊔ N) ≤ D.relIndex C₁ := by
    have e : C ⊔ N = C₁ ⊔ N := by rw [hC₁def, sup_assoc, sup_eq_right.mpr hZγN]
    rw [e, S46.relIndex_sup_of_le_normalizer (sup_le (hCVγ.trans hVγN) (hZγV.trans hVγN)),
      ← Subgroup.inf_relIndex_right N C₁]
    exact Subgroup.relIndex_le_of_le_left (le_inf (sup_le hNUN hZγN) hDC₁)
      (relIndex_ne_zero_of_le_stab c hγ hC₁s _)
  have hstep2 : Zγ.relIndex D * D.relIndex C₁ = Zγ.relIndex C₁ :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hDC₁
  have hstep3 : Zγ.relIndex C₁ = Zγ.relIndex C :=
    S46.relIndex_sup_of_le_normalizer (hCVγ.trans (hVγs.trans (stab_le_normalizer_zm _ γ)))
  have hfinal : N.relIndex (C ⊔ N) * cc ≤ Fintype.card F * cc :=
    calc N.relIndex (C ⊔ N) * cc ≤ D.relIndex C₁ * Zγ.relIndex D := Nat.mul_le_mul hstep1 hc_le
      _ = Zγ.relIndex C₁ := by rw [mul_comm, hstep2]
      _ = Zγ.relIndex C := hstep3
      _ ≤ Fintype.card F * cc := hCZγ
  exact Nat.le_of_mul_le_mul_right hfinal hcc0

end CFSG.Quasithin.MS93.S46R
