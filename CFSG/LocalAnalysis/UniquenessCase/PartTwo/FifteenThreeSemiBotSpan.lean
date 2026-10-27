module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Commutator

theorem s15_semiBot_commSub_iSup_left {W : Type*} [CommGroup W] {ι : Sort*}
    (U : ι → Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (⨆ i, U i) X = ⨆ i, commSub (U i) X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    refine Subgroup.iSup_induction U
      (C := fun w => x w * w⁻¹ ∈ ⨆ i, commSub (U i) X) hw ?_ ?_ ?_
    · intro i u hu
      exact Subgroup.mem_iSup_of_mem i (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
    · simp
    · intro a b ha hb
      have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h1]
      exact mul_mem ha hb
  · exact iSup_le fun i => commSub_mono (le_iSup U i) le_rfl

theorem s15_semiBot_iSup_map_conj_normal {A : Type*} [Group A] {K B : Subgroup A}
    (hKB : K ≤ B) :
    ((⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom).subgroupOf B).Normal := by
  classical
  set X : Subgroup A := ⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom with hX
  have hXB : X ≤ B := by
    refine iSup_le fun φ => ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact B.mul_mem (B.mul_mem φ.2 (hKB hc)) (B.inv_mem φ.2)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXB]
  have hfwd : ∀ b ∈ B, ∀ x ∈ X, MulAut.conj b x ∈ X := by
    intro b hb x hx
    have hx' : x ∈ ⨆ φ : B, K.map (MulAut.conj (φ : A)).toMonoidHom := by
      rw [hX] at hx; exact hx
    refine Subgroup.iSup_induction (fun φ : B => K.map (MulAut.conj (φ : A)).toMonoidHom)
      (C := fun z => MulAut.conj b z ∈ X) hx' ?_ ?_ ?_
    · intro φ c hc
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hc
      have h1 : MulAut.conj b ((MulEquiv.toMonoidHom (MulAut.conj (φ : A))) d) =
          (MulEquiv.toMonoidHom (MulAut.conj (((⟨b * φ, B.mul_mem hb φ.2⟩ : B)) : A))) d := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h1]
      exact Subgroup.mem_iSup_of_mem ⟨b * φ, B.mul_mem hb φ.2⟩
        (Subgroup.mem_map_of_mem _ hd)
    · simp
    · intro x y hx hy
      rw [map_mul]
      exact X.mul_mem hx hy
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hfwd b hb x hx
  · intro hx
    have hb' : b⁻¹ ∈ B := B.inv_mem hb
    have h1 := hfwd b⁻¹ hb' (b * x * b⁻¹) hx
    rwa [show MulAut.conj b⁻¹ (b * x * b⁻¹) = x by
      simp only [MulAut.conj_apply]; group] at h1

end Commutator

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_mem_compBar_of_isComponentOf (h : Hyp151 D V₀ V L)
    {K : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hK : IsComponentOf K (barSub V₀ V h.isElemAbelian L)) :
    K ∈ compBar D.M V₀ V h.isElemAbelian := by
  have hV := h.isElemAbelian
  have hLM : barSub V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.le
  exact ⟨hK.1.trans hLM, IsSubnormal.trans hK.2.1 (s15_Kbar_isSubnormal_barSub h), hK.2.2⟩

theorem s15_semiBot_wTil_eq_iSup_of_span (h : Hyp151 D V₀ V L)
    {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hY : Y ≤ barSub V₀ V h.isElemAbelian L)
    (hspan : commSub ⊤ (⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      Y.map (MulAut.conj φ).toMonoidHom) = ⊤) :
    wTil V₀ V h.isElemAbelian L =
      ⨆ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
          normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
        commSub ⊤ (Y.map (MulAut.conj n).toMonoidHom) := by
  have hV := h.isElemAbelian
  let Vt := Vtil V₀ V hV
  let Lb : Subgroup (MulAut Vt) := barSub V₀ V hV L
  let Mb : Subgroup (MulAut Vt) := Mbar D.M V₀ V hV
  let N : Subgroup (MulAut Vt) := Mb ⊓ normalizer (Lb : Set (MulAut Vt))
  let U : MulAut Vt → Subgroup Vt :=
    fun φ => commSub ⊤ (Y.map (MulAut.conj φ).toMonoidHom)
  let Uall : Subgroup Vt := ⨆ n ∈ N, U n
  have hUall_eq : Uall = ⨆ n : N, U (n : MulAut Vt) := by
    change (⨆ n ∈ N, U n) = ⨆ n : N, U (n : MulAut Vt)
    exact (iSup_subtype'' (N : Set (MulAut Vt)) U).symm
  have hLbN : Lb ≤ N := by
    intro x hx
    exact Subgroup.mem_inf.2
      ⟨barSub_mono V₀ V hV h.le hx, Subgroup.le_normalizer hx⟩
  have hmapUn : ∀ (n : MulAut Vt), n ∈ N → ∀ x : MulAut Vt, x ∈ Lb →
      (U n).map x.toMonoidHom = U (x * n) := by
    intro n hn x hx
    have hh := s15_Kbar_commSub_map_conj (⊤ : Subgroup Vt)
      (Y.map (MulAut.conj n).toMonoidHom) x
    rw [Subgroup.map_top_of_surjective x.toMonoidHom x.surjective] at hh
    have hfh : (MulAut.conj x).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (x * n)).toMonoidHom := by
      ext y
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    have hcomp : (Y.map (MulAut.conj n).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = Y.map (MulAut.conj (x * n)).toMonoidHom := by
      rw [Subgroup.map_map, hfh]
    rw [hcomp] at hh
    exact hh.symm
  have hUall_inv : ∀ x ∈ Lb, ∀ w ∈ (⨆ n : N, U (n : MulAut Vt)),
      x w ∈ ⨆ n : N, U (n : MulAut Vt) := by
    intro x hxLb w hw
    have hxN : x ∈ N := hLbN hxLb
    refine Subgroup.iSup_induction (S := fun n : N => U (n : MulAut Vt))
      (C := fun z => x z ∈ ⨆ n : N, U (n : MulAut Vt)) hw ?_ ?_ ?_
    · intro n a ha
      have hxn : x * (n : MulAut Vt) ∈ N := N.mul_mem hxN n.2
      have ha' : x a ∈ U (x * (n : MulAut Vt)) := by
        rw [← hmapUn (n : MulAut Vt) n.2 x hxLb]
        exact Subgroup.mem_map_of_mem x.toMonoidHom ha
      exact le_iSup (fun m : N => U (m : MulAut Vt))
        ⟨x * (n : MulAut Vt), hxn⟩ ha'
    · simpa using Subgroup.one_mem (⨆ n : N, U (n : MulAut Vt))
    · intro a b ha hb
      rw [map_mul]
      exact (⨆ n : N, U (n : MulAut Vt)).mul_mem ha hb
  have hspan_sub : commSub ⊤ (⨆ φ : Mb,
      Y.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom) = ⊤ := by
    rw [← hspan]
    congr 1
    exact (iSup_subtype'' (Mb : Set (MulAut Vt))
      (fun φ => Y.map (MulAut.conj φ).toMonoidHom))
  have hLin := s15_Lin_commSub_top_iSup (W := Vt) (ι := Mb)
    (fun φ : Mb => Y.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom)
  have hstep1 : (⨆ φ : Mb, U (φ : MulAut Vt)) = ⊤ := by
    change (⨆ φ : Mb,
      commSub ⊤ (Y.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom)) = ⊤
    exact hLin.symm.trans hspan_sub
  change wTil V₀ V hV L = Uall
  rw [hUall_eq]
  apply le_antisymm
  · change commSub ⊤ Lb ≤ ⨆ n : N, U (n : MulAut Vt)
    rw [← hstep1]
    rw [s15_semiBot_commSub_iSup_left (fun φ : Mb => U (φ : MulAut Vt)) Lb]
    refine iSup_le fun φ => ?_
    by_cases hφN : (φ : MulAut Vt) ∈ N
    · have hle1 : commSub (U (φ : MulAut Vt)) Lb ≤
          commSub (⨆ n : N, U (n : MulAut Vt)) Lb :=
        commSub_mono (le_iSup (fun n : N => U (n : MulAut Vt))
          ⟨(φ : MulAut Vt), hφN⟩) le_rfl
      exact hle1.trans (commSub_le_of_invariant hUall_inv)
    · have hφnorm : (φ : MulAut Vt) ∉ normalizer (Lb : Set (MulAut Vt)) := by
        intro hh
        exact hφN (Subgroup.mem_inf.2 ⟨φ.2, hh⟩)
      obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M (φ : MulAut Vt)).1 φ.2
      let m : G := (g : G)⁻¹
      have hmM : m ∈ D.M := by simpa only [m] using D.M.inv_mem hgM
      have hstm : m ∈ stabTil V₀ V := by
        simpa only [m] using (stabTil V₀ V).inv_mem g.2
      have hg_not : (g : G) ∉ nBar D.M V₀ V hV L := by
        rw [s15_Infra_mem_nBar_iff h.hyp125 hV hgM]
        intro hconj
        rw [s15_Infra_barSub_conjSubgroup V₀ V hV g.2 L, hgφ] at hconj
        have hmem : (φ : MulAut Vt)⁻¹ ∈ normalizer (Lb : Set (MulAut Vt)) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          exact hconj
        exact hφnorm (by simpa using (normalizer (Lb : Set (MulAut Vt))).inv_mem hmem)
      have hne : 1 * m⁻¹ ∉ nBar D.M V₀ V hV L := by
        simpa [m] using hg_not
      obtain ⟨-, hcomm2⟩ := s15_Kbar_commute_conj h hmM D.M.one_mem hne
      have hact : actTil V₀ V hV ⟨m, hstm⟩ = (φ : MulAut Vt)⁻¹ := by
        show actTil V₀ V hV ⟨(g : G)⁻¹, hstm⟩ = (φ : MulAut Vt)⁻¹
        rw [show (⟨(g : G)⁻¹, hstm⟩ : stabTil V₀ V) =
            (⟨g, g.2⟩ : stabTil V₀ V)⁻¹ from rfl, map_inv, hgφ]
      have hKm : barSub V₀ V hV (conjSubgroup L m) =
          Lb.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom := by
        rw [s15_Infra_barSub_conjSubgroup V₀ V hV hstm L, hact,
          inv_inv (φ : MulAut Vt)]
      have hcomm2' : commSub (commSub ⊤
          (Lb.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom)) Lb = ⊥ := by
        rw [← hKm]
        simpa only [conjSubgroup_one] using hcomm2
      have hUle : U (φ : MulAut Vt) ≤
          commSub ⊤ (Lb.map (MulAut.conj (φ : MulAut Vt)).toMonoidHom) :=
        commSub_mono le_rfl (Subgroup.map_mono hY)
      exact ((commSub_mono hUle le_rfl).trans (le_of_eq hcomm2')).trans bot_le
  · refine iSup_le fun n => ?_
    have hnnorm : (n : MulAut Vt) ∈ normalizer (Lb : Set (MulAut Vt)) := (Subgroup.mem_inf.1 n.2).2
    have hmapn : Lb.map (MulAut.conj (n : MulAut Vt)).toMonoidHom = Lb :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := Lb) (g := (n : MulAut Vt))).1 hnnorm
    calc U (n : MulAut Vt)
        = commSub ⊤ (Y.map (MulAut.conj (n : MulAut Vt)).toMonoidHom) := rfl
      _ ≤ commSub ⊤ (Lb.map (MulAut.conj (n : MulAut Vt)).toMonoidHom) :=
          commSub_mono le_rfl (Subgroup.map_mono hY)
      _ = commSub ⊤ Lb := by rw [hmapn]
      _ = wTil V₀ V hV L := rfl

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
