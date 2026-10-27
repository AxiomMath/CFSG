module

public import CFSG.Quasithin.Vol2.KGFactC31M24Grp
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 Matrix _root_.Certificates

@[expose] def genOf (ws : List (List ℤ)) : Subgroup G₀ :=
  Subgroup.closure {x | ∃ w ∈ ws, elt w = x}

theorem map_genOf (ws : List (List ℤ)) :
    (genOf ws).map NativeSporadic.M24.subtype =
      Subgroup.closure {g | g ∈ ws.map fun w => tab (wordG gensG w)} := by
  rw [genOf, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map, tab_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem card_genOf {ws : List (List ℤ)} {Q : RawSchreierDatum 24}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ ws.map fun w => tab (wordG gensG w)})
    (hv : ValidSchreier Q) : Nat.card (genOf ws) = Q.orderCertificate := by
  rw [Q.orderCertificate_eq_card hv, hQ, ← map_genOf,
    Subgroup.card_map_of_injective Subtype.val_injective]

theorem genOf_le {ws : List (List ℤ)} {K : Subgroup G₀} (h : ∀ w ∈ ws, elt w ∈ K) :
    genOf ws ≤ K := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

theorem elt_mem_genOf {ws : List (List ℤ)} {w : List ℤ} (hw : w ∈ ws) : elt w ∈ genOf ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

@[expose] def conjGenOf (ws : List (List ℤ)) (y : List ℤ) : Subgroup G₀ :=
  Subgroup.closure {x | ∃ w ∈ ws, elt w * elt y * (elt w)⁻¹ = x}

theorem map_conjGenOf (ws : List (List ℤ)) (y : List ℤ) :
    (conjGenOf ws y).map NativeSporadic.M24.subtype =
      Subgroup.closure {g | g ∈ ws.map fun w =>
        tab (wordG gensG w * wordG gensG y * (wordG gensG w)⁻¹)} := by
  rw [conjGenOf, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map, tab_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem card_conjGenOf {ws : List (List ℤ)} {y : List ℤ} {Q : RawSchreierDatum 24}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ ws.map fun w =>
      tab (wordG gensG w * wordG gensG y * (wordG gensG w)⁻¹)})
    (hv : ValidSchreier Q) : Nat.card (conjGenOf ws y) = Q.orderCertificate := by
  rw [Q.orderCertificate_eq_card hv, hQ, ← map_conjGenOf,
    Subgroup.card_map_of_injective Subtype.val_injective]

theorem conjGenOf_le {ws : List (List ℤ)} {y : List ℤ} {K : Subgroup G₀}
    (h : ∀ w ∈ ws, elt w * elt y * (elt w)⁻¹ ∈ K) : conjGenOf ws y ≤ K := by
  rw [conjGenOf, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

theorem mem_conjGenOf_of_sift {ws : List (List ℤ)} {y : List ℤ} {Q : RawSchreierDatum 24}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ ws.map fun w =>
      tab (wordG gensG w * wordG gensG y * (wordG gensG w)⁻¹)})
    (hv : ValidSchreier Q) {x : G₀} (h : Q.sift (tab (x : Equiv.Perm (Fin 24))) 0 = true) :
    x ∈ conjGenOf ws y := by
  rw [Q.sift_eq_true_iff_mem_original hv, tab_eq, hQ, ← map_conjGenOf] at h
  obtain ⟨z, hz, hxz⟩ := h
  rw [← Subtype.val_injective hxz]
  exact hz

theorem mem_eNorm_of_masksOK {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    {T : Table} {g : G₀} (hT : Rep 24 T (g : Equiv.Perm (Fin 24))) {masks : List ℕ}
    (h : masksOK 24 bs T masks = true) : g ∈ eNorm hv := by
  rw [mem_eNorm_iff hv]
  intro i
  refine ⟨maskVec k (masks.getD i 0), Subtype.ext ?_⟩
  have h1 := conj_of_masksOK hn24 hbs hT h i
  rw [show ((eElt v (maskVec k (masks.getD i 0)) : G₀) : Equiv.Perm (Fin 24)) =
    eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 24))) (maskVec k (masks.getD i 0)) from
      map_eElt NativeSporadic.M24.subtype _]
  exact h1

theorem mem_zip_of_mem {α β : Type*} {l : List α} {m : List β} (hl : l.length = m.length)
    {a : α} (ha : a ∈ l) : ∃ b, (a, b) ∈ l.zip m := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  refine ⟨m[j]'(hl ▸ hj), ?_⟩
  rw [List.mem_iff_getElem]
  exact ⟨j, by rw [List.length_zip]; omega, by simp⟩

theorem genOf_le_eNorm {ws : List (List ℤ)} {masks : List (List ℕ)}
    (hl : ws.length = masks.length) {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (h : ((ws.map fun w => tab (wordG gensG w)).zip masks).all
      (fun p => masksOK 24 bs (toTable p.1) p.2) = true) : genOf ws ≤ eNorm hv := by
  refine genOf_le fun w hw => ?_
  obtain ⟨b, hb⟩ := mem_zip_of_mem (l := ws.map fun w => tab (wordG gensG w)) (m := masks)
    (by rw [List.length_map]; exact hl) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have h1 := List.all_eq_true.mp h _ hb
  have hT : Rep 24 (toTable (tab (wordG gensG w))) ((elt w : G₀) : Equiv.Perm (Fin 24)) := by
    rw [tab_eq]
    exact rep_toTable hn24 _
  exact mem_eNorm_of_masksOK hv hbs hT h1

theorem words_mem_eNorm {ws : List (List ℤ)} {masks : List (List ℕ)}
    (hl : ws.length = masks.length) {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (h : ((ws.map (wordT 24 gensT)).zip masks).all (fun p => masksOK 24 bs p.1 p.2) = true) :
    ∀ w ∈ ws, elt w ∈ eNorm hv := by
  intro w hw
  obtain ⟨b, hb⟩ := mem_zip_of_mem (l := ws.map (wordT 24 gensT)) (m := masks)
    (by rw [List.length_map]; exact hl) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have h1 : masksOK 24 bs (wordT 24 gensT w) b = true := List.all_eq_true.mp h _ hb
  exact mem_eNorm_of_masksOK hv hbs (rep_elt w) h1

theorem orderOf_elt {w : List ℤ} {q : ℕ} (hq : 0 < q)
    (h : ordTest 24 q (wordT 24 gensT w) = true) : orderOf (elt w) = q := by
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful (rep_elt w) hq).1 h

@[expose] def Mo : Subgroup G₀ := genOf moGenW

theorem card_Mo : Nat.card Mo = 322560 := by
  rw [Mo, card_genOf (Q := moChain) (certificate_originalSubgroup _ _ _ _ _) c_mo_check,
    c_mo_order]

theorem Mo_le : Mo ≤ eNorm basis_o :=
  genOf_le_eNorm rfl basis_o forall₂_o c_masks_mo

@[expose] def Ns : Subgroup G₀ := genOf nsGenW

theorem card_Ns : Nat.card Ns = 138240 := by
  rw [Ns, card_genOf (Q := nsChain) (certificate_originalSubgroup _ _ _ _ _) c_ns_check,
    c_ns_order]

theorem Ns_le : Ns ≤ eNorm basis_s :=
  genOf_le_eNorm rfl basis_s forall₂_s c_masks_ns

@[expose] def y5 : G₀ := elt y5W

theorem orderOf_y5 : orderOf y5 = 5 := orderOf_elt (by norm_num) c_ord_y5

theorem y5_mem : y5 ∈ eNorm basis_s :=
  mem_eNorm_of_masksOK basis_s forall₂_s (rep_elt _) c_masks_y5

theorem nj_mem : ∀ w ∈ njW, elt w ∈ eNorm basis_s :=
  words_mem_eNorm rfl basis_s forall₂_s c_masks_nj

@[expose] def Ls : Subgroup G₀ := conjGenOf njW y5W

theorem card_Ls : Nat.card Ls = 69120 := by
  rw [Ls, card_conjGenOf (Q := lsChain) (certificate_originalSubgroup _ _ _ _ _) c_ls_check,
    c_ls_order]

theorem Ls_le : Ls ≤ eNorm basis_s :=
  conjGenOf_le fun w hw => (eNorm basis_s).mul_mem
    ((eNorm basis_s).mul_mem (nj_mem w hw) y5_mem) ((eNorm basis_s).inv_mem (nj_mem w hw))

theorem s_le_Ls : eSub basis_s ≤ Ls := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have h := List.all_eq_true.mp c_sift_s (sW.get i) (List.get_mem _ _)
  exact mem_conjGenOf_of_sift (certificate_originalSubgroup _ _ _ _ _) c_ls_check
    (x := vS i) h

@[expose] def Qg : Subgroup G₀ := genOf qGenW

theorem card_Qg : Nat.card Qg = 128 := by
  rw [Qg, card_genOf (Q := qChain) (certificate_originalSubgroup _ _ _ _ _) c_q_check,
    c_q_order]

theorem Qg_le : Qg ≤ Subgroup.centralizer (eSub basis_u5 : Set G₀) := by
  refine genOf_le fun w hw => ?_
  have h1 := List.all_eq_true.mp c_q_comm (tab (wordG gensG w)) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hT : Rep 24 (toTable (tab (wordG gensG w))) ((elt w : G₀) : Equiv.Perm (Fin 24)) := by
    rw [tab_eq]
    exact rep_toTable hn24 _
  have h2 := (commAll_iff forall₂_u5 _ _ hT).mp h1
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (mem_eSub_iff basis_u5 y).mp hy
  have : Commute (elt w) (eElt vU5 c) := commute_eElt (fun i => Subtype.ext (h2 i)) c
  exact this.eq.symm

theorem cent_u5 :
    Subgroup.centralizer (eSub basis_u5 : Set G₀) = Qg :=
  (Subgroup.eq_of_le_of_card_ge Qg_le (by
    rw [card_centralizer_eq_cb0 basis_u5 forall₂_u5 0 vU5_zero c_cent_u5, card_Qg])).symm

@[expose] def Nq : Subgroup G₀ := genOf nqGenW

theorem card_Nq : Nat.card Nq = 21504 := by
  rw [Nq, card_genOf (Q := nqChain) (certificate_originalSubgroup _ _ _ _ _) c_nq_check,
    c_nq_order]

theorem Nq_le : Nq ≤ eNorm basis_u5 :=
  genOf_le_eNorm rfl basis_u5 forall₂_u5 c_masks_nq

@[expose] def y7 : G₀ := elt y7W

theorem orderOf_y7 : orderOf y7 = 7 := orderOf_elt (by norm_num) c_ord_y7

theorem y7_mem : y7 ∈ eNorm basis_u5 :=
  mem_eNorm_of_masksOK basis_u5 forall₂_u5 (rep_elt _) c_masks_y7

theorem mj_mem : ∀ w ∈ mjW, elt w ∈ eNorm basis_u5 :=
  words_mem_eNorm rfl basis_u5 forall₂_u5 c_masks_mj

@[expose] def Lq : Subgroup G₀ := conjGenOf mjW y7W

theorem card_Lq : Nat.card Lq = 10752 := by
  rw [Lq, card_conjGenOf (Q := lqChain) (certificate_originalSubgroup _ _ _ _ _) c_lq_check,
    c_lq_order]

theorem Lq_le : Lq ≤ eNorm basis_u5 :=
  conjGenOf_le fun w hw => (eNorm basis_u5).mul_mem
    ((eNorm basis_u5).mul_mem (mj_mem w hw) y7_mem) ((eNorm basis_u5).inv_mem (mj_mem w hw))

theorem et_le_Lq : eSub basis_et ≤ Lq := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have h := List.all_eq_true.mp c_sift_et (etW.get i) (List.get_mem _ _)
  exact mem_conjGenOf_of_sift (certificate_originalSubgroup _ _ _ _ _) c_lq_check
    (x := vEt i) h

theorem et_le_cent :
    eSub basis_et ≤ Subgroup.centralizer (eSub basis_u5 : Set G₀) := by
  rw [eSub_eq_closure basis_u5]
  refine le_centralizer_of_comm basis_et fun i x hx => ?_
  obtain ⟨j, rfl⟩ := hx
  exact comm_of_all forall₂_et forall₂_u5 c_et_comm i j

theorem mem_centralizer_eSub_iff {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (x : G₀) :
    x ∈ Subgroup.centralizer (eSub hv : Set G₀) ↔ ∀ i, (x : Equiv.Perm (Fin 24)) *
      ((v i : G₀) : Equiv.Perm (Fin 24)) = ((v i : G₀) : Equiv.Perm (Fin 24)) * x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx i
    have := hx _ (mem_eSub hv i)
    exact (congrArg Subtype.val this).symm
  · intro hx y hy
    obtain ⟨c, rfl⟩ := (mem_eSub_iff hv y).mp hy
    have : Commute x (eElt v c) := commute_eElt (fun i => Subtype.ext (hx i)) c
    exact this.eq.symm

theorem Lq_inf_cent :
    Lq ⊓ Subgroup.centralizer (eSub basis_u5 : Set G₀) = eSub basis_et := by
  classical
  have hle : eSub basis_et ≤ Lq ⊓ Subgroup.centralizer (eSub basis_u5 : Set G₀) :=
    le_inf et_le_Lq et_le_cent
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h := card_subtype_eq_countProducts hn24 lqChain c_lq_check
    (P := fun g => ∀ i, g * ((vU5 i : G₀) : Equiv.Perm (Fin 24)) =
      ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * g) (commAll_iff forall₂_u5)
  rw [c_lq_cent] at h
  have hQ : lqChain.originalSubgroup = Lq.map NativeSporadic.M24.subtype := by
    rw [lqChain, certificate_originalSubgroup, Lq, map_conjGenOf]
    rfl
  rw [hQ] at h
  have h2 : Nat.card ↥(Lq ⊓ Subgroup.centralizer (eSub basis_u5 : Set G₀)) =
      Nat.card {x : ↥(Lq.map NativeSporadic.M24.subtype) // ∀ i, (x : Equiv.Perm (Fin 24)) *
        ((vU5 i : G₀) : Equiv.Perm (Fin 24)) = ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * x} := by
    refine (Nat.card_congr ?_).trans (Nat.card_congr (Equiv.subtypeEquiv
      (Lq.equivMapOfInjective _ Subtype.val_injective).toEquiv fun x => Iff.rfl))
    exact
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, (mem_centralizer_eSub_iff basis_u5 _).mp x.2.2⟩
        invFun := fun x => ⟨x.1.1, x.1.2, (mem_centralizer_eSub_iff basis_u5 _).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h2, h, card_eSub]
  norm_num

@[expose] def Nt : Subgroup G₀ := genOf ntGenW

theorem card_Nt : Nat.card Nt = 64512 := by
  rw [Nt, card_genOf (Q := ntChain) (certificate_originalSubgroup _ _ _ _ _) c_nt_check,
    c_nt_order]

theorem Nt_le : Nt ≤ eNorm basis_t :=
  genOf_le_eNorm rfl basis_t forall₂_t c_masks_nt

@[expose] def qt : G₀ := elt qtW

theorem qt_mem : qt ∈ eNorm basis_t :=
  mem_eNorm_of_masksOK basis_t forall₂_t (rep_elt _) c_masks_qt

theorem mem_eSub_iff_inSpan {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    {T : Table} {x : G₀} (hT : Rep 24 T (x : Equiv.Perm (Fin 24))) :
    x ∈ eSub hv ↔ inSpan 24 bs T = true := by
  have h := mem_spanTabs_iff hn24 hbs (f := tblEq 24 T)
    (P := fun u => (x : Equiv.Perm (Fin 24)) = u) fun U u hU => tblEq_iff_eq hT hU
  rw [inSpan, h, mem_eSub_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, map_eElt NativeSporadic.M24.subtype c⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext (by rw [hc]; exact map_eElt NativeSporadic.M24.subtype c)⟩

theorem rep_qt : Rep 24 qtT ((qt : G₀) : Equiv.Perm (Fin 24)) := rep_elt qtW

theorem qt_not_mem : qt ∉ eSub basis_t := by
  rw [mem_eSub_iff_inSpan basis_t forall₂_t rep_qt, c_qt_notin]
  exact Bool.false_ne_true

theorem qt_sq_mem : qt * qt ∈ eSub basis_t :=
  (mem_eSub_iff_inSpan (x := qt * qt) basis_t forall₂_t (Rep.compT rep_qt rep_qt)).mpr c_qt_sq

@[expose] def Kq : Subgroup G₀ := genOf kqGenW

theorem card_Kq : Nat.card Kq = 21504 := by
  rw [Kq, card_genOf (Q := kqChain) (certificate_originalSubgroup _ _ _ _ _) c_kq_check,
    c_kq_order]

theorem kq_mem : ∀ w ∈ kqGenW, elt w ∈ eNorm basis_t :=
  words_mem_eNorm rfl basis_t forall₂_t c_masks_kq

theorem Kq_le : Kq ≤ sectionCent (eSub basis_t) qt_mem := by
  refine genOf_le fun w hw => ⟨kq_mem w hw, ?_⟩
  have h1 := List.all_eq_true.mp c_kq_comm (wordT 24 gensT w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  rw [Bool.and_eq_true] at h1
  have hk := rep_elt w
  have hki := Rep.inv_of_invOK hk h1.1
  have hqi := Rep.inv_of_invOK rep_qt c_qt_inv
  have hrep : Rep 24 (compT 24 (conjTab 24 (wordT 24 gensT w) (invT 24 (wordT 24 gensT w)) qtT)
      (invT 24 qtT)) ((elt w * qt * (elt w)⁻¹ * qt⁻¹ : G₀) : Equiv.Perm (Fin 24)) :=
    Rep.compT (Rep.compT (Rep.compT hk rep_qt) hki) hqi
  exact (mem_eSub_iff_inSpan (x := elt w * qt * (elt w)⁻¹ * qt⁻¹) basis_t forall₂_t hrep).mpr
    h1.2

theorem mem_eNorm_of_coe {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {g : G₀}
    (h : (g : Equiv.Perm (Fin 24)) ∈
      eNorm (hv.map (f := NativeSporadic.M24.subtype) Subtype.val_injective)) :
    g ∈ eNorm hv := by
  rw [mem_eNorm_iff hv]
  intro i
  obtain ⟨c, hc⟩ := (mem_eNorm_iff _ _).mp h i
  refine ⟨c, Subtype.ext ?_⟩
  rw [show ((eElt v c : G₀) : Equiv.Perm (Fin 24)) =
    eElt (fun i => NativeSporadic.M24.subtype (v i)) c from map_eElt NativeSporadic.M24.subtype c]
  exact hc

theorem coe_mem_eNorm {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {g : G₀} (hg : g ∈ eNorm hv) :
    (g : Equiv.Perm (Fin 24)) ∈
      eNorm (hv.map (f := NativeSporadic.M24.subtype) Subtype.val_injective) := by
  rw [mem_eNorm_iff]
  intro i
  obtain ⟨c, hc⟩ := (mem_eNorm_iff hv g).mp hg i
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  rw [show eElt (fun i => NativeSporadic.M24.subtype (v i)) c =
    ((eElt v c : G₀) : Equiv.Perm (Fin 24)) from (map_eElt NativeSporadic.M24.subtype c).symm]
  simpa using this

@[expose] def CB0 : Subgroup G₀ := m24CentQ2.originalSubgroup.comap NativeSporadic.M24.subtype

theorem map_CB0 :
    CB0.map NativeSporadic.M24.subtype = m24CentQ2.originalSubgroup := by
  rw [CB0, Subgroup.map_comap_eq, Subgroup.range_subtype]
  refine inf_eq_right.mpr ?_
  obtain ⟨-, -, hK, -, -⟩ := m24_rep_data2
  rw [← m24Certificate_originalSubgroup]
  exact hK.trans inf_le_left

theorem card_CB0 : Nat.card CB0 = 21504 := by
  obtain ⟨-, -, -, hKc, -⟩ := m24_rep_data2
  rw [← hKc, ← map_CB0, Subgroup.card_map_of_injective Subtype.val_injective]

theorem CB0_le : CB0 ≤ eNorm basis_r2 := by
  intro x hx
  apply mem_eNorm_of_coe
  have hx' : (x : Equiv.Perm (Fin 24)) ∈ m24CentQ2.originalSubgroup := hx
  rw [m24CentQ2, certificate_originalSubgroup] at hx'
  refine (Subgroup.closure_le _).mpr ?_ hx'
  intro g hg
  have hg' : g ∈ cb0Gen := hg
  obtain ⟨b, hb⟩ := mem_zip_of_mem (l := cb0Gen) (m := cb0Masks) rfl hg'
  have h1 := List.all_eq_true.mp c_masks_cb0 _ hb
  beta_reduce at h1
  rw [SetLike.mem_coe, mem_eNorm_iff]
  intro i
  exact ⟨_, conj_of_masksOK hn24 forall₂_r2 (rep_toTable hn24 g) h1 i⟩

theorem card_le_of_cosetOK
    {k : ℕ}
    {v : Fin k → Equiv.Perm (Fin 24)} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn v)) (i₀ : Fin k) (hi₀ : v i₀ = b0)
    {ws : List (List ℤ)} (hok : cosetOK 24 b0T bs (ws.map (wordT 24 gensT)) = true)
    {f : Table → Bool} {P : Equiv.Perm (Fin 24) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 24 T g → (f T = true ↔ P g)) (hPN : ∀ g, P g → g ∈ eNorm hv) :
    Nat.card {g : NativeSporadic.M24 // P g} ≤
      cosetCount 24 cb0T (ws.map (wordT 24 gensT)) f := by
  refine card_le_cosetCount hfP (forall₂_words ws) (fun r hr => ?_) fun g _ hgP => ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact (elt w).2
  · have hb0 : b0 ∈ eSub hv := hi₀ ▸ mem_eSub hv i₀
    have hx : g * b0 * g⁻¹ ∈ eSub hv := (Subgroup.mem_normalizer_iff.mp (hPN g hgP) b0).mp hb0
    have hb1 : b0 ≠ 1 := by
      intro h
      have h1 := hv.ne_one (Pi.single i₀ 1) (by rw [eElt_single, hi₀, h])
      have := congrFun h1 i₀
      simp at this
    have hx1 : g * b0 * g⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc b0 = g⁻¹ * (g * b0 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact exists_conj_of_cosetOK hn24 hv hbs rep_b0 (forall₂_words ws) hok hx hx1

theorem card_eNorm_r2_le :
    Nat.card (eNorm basis_r2) ≤ 21504 := by
  classical
  have hvP := basis_r2.map (f := NativeSporadic.M24.subtype) Subtype.val_injective
  have h : Nat.card (eNorm basis_r2) = Nat.card {g : NativeSporadic.M24 //
      (g : Equiv.Perm (Fin 24)) ∈ eNorm hvP} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx => coe_mem_eNorm basis_r2 hx, fun hx => mem_eNorm_of_coe basis_r2 hx⟩)
  rw [h, ← c_ccount_r2]
  exact card_le_of_cosetOK hvP forall₂_r2 0 vR2_zero c_coset_r2 (P := fun g => g ∈ eNorm hvP)
    (fun T g hT => normAll_iff hn24 hvP forall₂_r2 hT) fun _ h => h

end CFSG.Quasithin.KGC31.M24

end
