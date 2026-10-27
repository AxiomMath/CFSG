module

public import Certificates.Kernel.AE6Twin.Checks
public import CFSG.Certificates.Kernel.AE6TwinKSound
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cSym
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cTransport

public section

namespace CFSG.KD.AE6Twin

open CFSG.KC.WrTwin CFSG.KC.AE6TwinK CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

theorem card_α₀ : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := rfl

theorem mem_P720 (σ : Equiv.Perm (Fin 6)) : lvl σ ∈ P720 :=
  mem_prods_of_chainOK rfl ae6t_chain ae6t_chain_len σ

theorem eqPi_iff_mkQ {x y : Wr 6} : eqPi x y = true ↔ mkQ 6 x = mkQ 6 y :=
  TL4.Mdl117.eqPi_iff x y

theorem eqPi_false {x y : Wr 6} (h : mkQ 6 x ≠ mkQ 6 y) : eqPi x y = false :=
  Bool.eq_false_iff.2 fun h' => h (eqPi_iff_mkQ.1 h')

theorem zBar_α₀ : zBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ = mkQ 6 z0 :=
  zBar_eq _ card_α₀

theorem mem_memBar₀ {b : Bool} {m : Wr 6} (hm : m ∈ mem0 b) :
    mkQ 6 m ∈ memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ b := by
  refine (TL4.Mdl117.mem_memBar_iff _ card_α₀ b _).2 ⟨m, ?_, rfl⟩
  rw [memAtL_α₀]
  exact hm

theorem mem0_length (b : Bool) : (mem0 b).length = 8 := by
  cases b <;> rfl

theorem getD_mem' {l : List (Wr 6)} {i : Nat} (hi : i < l.length) : l.getD i 1 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem gens0_mem : ∀ s ∈ gens0, s ∈ mem0 true ∨ s ∈ mem0 false := by
  intro s hs
  simp only [gens0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl (getD_mem' (by rw [mem0_length]; omega))
  · exact Or.inl (getD_mem' (by rw [mem0_length]; omega))
  · exact Or.inr (getD_mem' (by rw [mem0_length]; omega))
  · exact Or.inr (getD_mem' (by rw [mem0_length]; omega))

theorem comm_gens0 {a : Wr 6}
    (h1 : ∀ k ∈ memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true, k * mkQ 6 a = mkQ 6 a * k)
    (h2 : ∀ k ∈ memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false, k * mkQ 6 a = mkQ 6 a * k) :
    ∀ s ∈ gens0, eqPi (s * a) (a * s) = true := by
  intro s hs
  rw [eqPi_iff_mkQ]
  simp only [map_mul]
  rcases gens0_mem s hs with h | h
  · exact h1 _ (mem_memBar₀ h)
  · exact h2 _ (mem_memBar₀ h)

theorem cent_rec {a : Wr 6}
    (h1 : ∀ k ∈ memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true, k * mkQ 6 a = mkQ 6 a * k)
    (h2 : ∀ k ∈ memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false, k * mkQ 6 a = mkQ 6 a * k) :
    ∃ c ∈ Crec, mkQ 6 a = mkQ 6 c := by
  obtain ⟨c, hc, h⟩ := centOK_sound rfl ae6t_cent a (mem_P720 _) (mem_V64 _) (comm_gens0 h1 h2)
  exact ⟨c, hc, eqPi_iff_mkQ.1 h⟩

theorem perm_of_mkQ {a c : Wr 6} (h : mkQ 6 a = mkQ 6 c) : a.perm = c.perm :=
  eqPi_perm' (eqPi_iff_mkQ.2 h)

theorem sum_of_mkQ {a c : Wr 6} (h : mkQ 6 a = mkQ 6 c) (ha : ∑ i, a.vec i = 0) :
    ∑ i, c.vec i = 0 := by
  rcases eqPi_iff'.1 (eqPi_iff_mkQ.2 h) with rfl | rfl
  · exact ha
  · have hv : ∀ i, (a * allOnes 6).vec i = a.vec i + 1 := fun i => rfl
    simp only [hv, Finset.sum_add_distrib, ha, zero_add]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide

theorem small :
    centUOK z0 Crec = true ∧ dlOK z0 Crec Dl = true ∧ twin3OK z0 Crec = true ∧
      twin2OK (mem0 true) (mem0 false) = true := by
  have h := ae6t_small
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem centU₀ : CentUAt (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true)
    (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false) (zBar _ card_α₀) := by
  intro x hx h1 h2
  obtain ⟨v, hv, rfl⟩ := inU_iff.mp hx
  obtain ⟨c, hc, hvc⟩ := cent_rec h1 h2
  have hp : c.perm = 1 := (perm_of_mkQ hvc).symm
  have hs : ∑ i, c.vec i = 0 := sum_of_mkQ hvc hv
  rw [zBar_α₀, hvc]
  rcases centUOK_sound small.1 c hc hp hs with h | h
  · left
    rw [eqPi_iff_mkQ.1 h, map_one]
  · exact Or.inr (eqPi_iff_mkQ.1 h)

theorem twin2₀ : Twin2At (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true)
    (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false) := by
  obtain ⟨hl1, hl2, h5⟩ := twin2OK_sound small.2.2.2
  refine ⟨fun i => mkQ 6 ((mem0 true).getD (2 * (i.1 / 2)) 1 * (mem0 false).getD i.1 1), ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hne' : i.1 ≠ j.1 := fun e => hne (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
    · have := (h5 j.1 j.2).2 i.1 hlt
      have h6 := eqPi_iff_mkQ.2 hij.symm
      rw [h6] at this
      exact Bool.noConfusion this
    · have := (h5 i.1 i.2).2 j.1 hgt
      have h6 := eqPi_iff_mkQ.2 hij
      rw [h6] at this
      exact Bool.noConfusion this
  · intro i
    refine ⟨(h5 i.1 i.2).1, mkQ 6 ((mem0 true).getD (2 * (i.1 / 2)) 1), mem_memBar₀ ?_,
      mkQ 6 ((mem0 false).getD i.1 1), mem_memBar₀ ?_, map_mul _ _ _⟩
    · exact getD_mem' (by rw [hl1]; omega)
    · exact getD_mem' (by rw [hl2]; exact i.2)

theorem twin3₀ : Twin3At (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true)
    (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false) (zBar _ card_α₀) := by
  intro x y hx1 hx2 hy1 hy2 hxx hyy hyx
  obtain ⟨a, rfl⟩ : ∃ a : Wr 6, mkQ 6 a = x := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ : ∃ b : Wr 6, mkQ 6 b = y := QuotientGroup.mk_surjective y
  obtain ⟨ca, hca, ha⟩ := cent_rec hx1 hx2
  obtain ⟨cb, hcb, hb⟩ := cent_rec hy1 hy2
  rw [ha, zBar_α₀] at hxx
  rw [hb] at hyy
  rw [ha, hb, zBar_α₀] at hyx
  have h1 : eqPi (ca * ca) z0 = true := by
    rw [eqPi_iff_mkQ, map_mul]
    exact hxx
  have h2 : eqPi (cb * cb) 1 = true := by
    rw [eqPi_iff_mkQ, map_mul, map_one]
    exact hyy
  have h3 : eqPi (cb * ca * cb⁻¹) (ca * z0) = true := by
    rw [eqPi_iff_mkQ]
    simp only [map_mul, map_inv]
    exact hyx
  rw [ha, hb, ← map_mul]
  exact twin3OK_sound small.2.2.1 ca hca cb hcb h1 h2 h3

theorem vec_comm (u w : Fin 6 → ZMod 2) : ofVec u * ofVec w = ofVec w * ofVec u :=
  Wr.ext (funext fun i => add_comm (u i) (w i)) rfl

theorem ofVec_mul_self (w : Fin 6 → ZMod 2) : ofVec w * ofVec w = 1 :=
  Wr.ext (funext fun i => zmod_two_add_self (w i)) rfl

theorem ofVec_inv (w : Fin 6 → ZMod 2) : (ofVec w)⁻¹ = ofVec w :=
  inv_eq_of_mul_eq_one_right (ofVec_mul_self w)

theorem eq_ofVec {x : Wr 6} (h : x.perm = 1) : x = ofVec x.vec := by
  conv_lhs => rw [← AE.ofVec_mul_ofPerm x]
  rw [h, ofPerm_one, mul_one]

theorem vec_conj_vec (u : Fin 6 → ZMod 2) {x : Wr 6} (h : x.perm = 1) : ofVec u * x * ofVec u = x := by
  rw [eq_ofVec h, mul_assoc, vec_comm, ← mul_assoc, ofVec_mul_self, one_mul]

theorem mem_E32W {w : Wr 6} (hw : w ∈ E32W) : ∃ v : Fin 6 → ZMod 2, ∑ i, v i = 0 ∧ w = ofVec v := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hw
  exact ⟨vecL l, of_decide_eq_true (List.mem_filter.1 hl).2, rfl⟩

theorem comW_indep (w v : Fin 6 → ZMod 2) (τ : Equiv.Perm (Fin 6)) :
    ofVec w * (⟨v, τ⟩ : Wr 6) * (ofVec w)⁻¹ * (⟨v, τ⟩ : Wr 6)⁻¹ =
      ofVec w * ofPerm τ * (ofVec w)⁻¹ * (ofPerm τ)⁻¹ := by
  have hg : (⟨v, τ⟩ : Wr 6) = ofVec v * ofPerm τ := (AE.ofVec_mul_ofPerm _).symm
  have hp : (ofVec w * ofPerm τ * ofVec w * (ofPerm τ)⁻¹).perm = 1 := by
    change 1 * τ * 1 * τ⁻¹ = 1
    group
  rw [hg, mul_inv_rev, ofVec_inv, ofVec_inv]
  calc ofVec w * (ofVec v * ofPerm τ) * ofVec w * ((ofPerm τ)⁻¹ * ofVec v)
      = ofVec v * (ofVec w * ofPerm τ * ofVec w * (ofPerm τ)⁻¹) * ofVec v := by
        rw [← mul_assoc (ofVec w) (ofVec v), vec_comm w v]
        group
    _ = ofVec w * ofPerm τ * ofVec w * (ofPerm τ)⁻¹ := vec_conj_vec v hp

theorem conj_vec (v d : Fin 6 → ZMod 2) (τ : Equiv.Perm (Fin 6)) :
    (⟨v, τ⟩ : Wr 6) * ofVec d * (⟨v, τ⟩ : Wr 6)⁻¹ = ofPerm τ * ofVec d * (ofPerm τ)⁻¹ := by
  have hg : (⟨v, τ⟩ : Wr 6) = ofVec v * ofPerm τ := (AE.ofVec_mul_ofPerm _).symm
  have hp : (ofPerm τ * ofVec d * (ofPerm τ)⁻¹).perm = 1 := by
    change τ * 1 * τ⁻¹ = 1
    group
  rw [hg, mul_inv_rev, ofVec_inv]
  calc ofVec v * ofPerm τ * ofVec d * ((ofPerm τ)⁻¹ * ofVec v)
      = ofVec v * (ofPerm τ * ofVec d * (ofPerm τ)⁻¹) * ofVec v := by group
    _ = ofPerm τ * ofVec d * (ofPerm τ)⁻¹ := vec_conj_vec v hp

theorem twin4₀ : Twin4At (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ true)
    (memBar ({0, 1, 2, 3} : Finset (Fin 6)) card_α₀ false) (zBar _ card_α₀) := by
  intro g H1 H2 δ hδ hd1 hd2 hδ1 hδz
  obtain ⟨⟨gv, gp⟩, rfl⟩ : ∃ gw : Wr 6, mkQ 6 gw = g := QuotientGroup.mk_surjective g
  obtain ⟨dv, rfl⟩ := exists_vec_of_perm_one hδ
  rw [zBar_α₀] at H1 H2 hδz
  have hcomm : ∀ w : Fin 6 → ZMod 2, mkQ 6 (ofVec w) * mkQ 6 (⟨gv, gp⟩ : Wr 6) *
      (mkQ 6 (ofVec w))⁻¹ * (mkQ 6 (⟨gv, gp⟩ : Wr 6))⁻¹ =
        mkQ 6 (ofVec w * ofPerm gp * (ofVec w)⁻¹ * (ofPerm gp)⁻¹) := by
    intro w
    rw [← comW_indep w gv gp]
    simp only [map_mul, map_inv]
  have hE : ∀ w ∈ E32W, w * w = 1 := by
    intro w hw
    obtain ⟨v, -, rfl⟩ := mem_E32W hw
    exact ofVec_mul_self v
  have h1 : ∀ w ∈ E32W, eqPi (w * ofPerm gp * w⁻¹ * (ofPerm gp)⁻¹) 1 = true ∨
      eqPi (w * ofPerm gp * w⁻¹ * (ofPerm gp)⁻¹) z0 = true := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_E32W hw
    rw [eqPi_iff_mkQ, eqPi_iff_mkQ, ← hcomm, map_one]
    exact H1 _ (inU_iff.mpr ⟨v, hv, rfl⟩)
  have h2 : ∃ w ∈ E32W, eqPi (w * ofPerm gp * w⁻¹ * (ofPerm gp)⁻¹) z0 = true := by
    obtain ⟨x, hx, h8⟩ := H2
    obtain ⟨w, hw, rfl⟩ := inU_iff.mp hx
    refine ⟨ofVec w, mem_E32 hw, ?_⟩
    rw [eqPi_iff_mkQ, ← hcomm]
    exact h8
  have htv := tvOK_sound rfl rfl ae6t_tv hE gp (mem_P720 gp) h1 h2
  obtain ⟨c, hc, hdc⟩ := cent_rec hd1 hd2
  have hp : c.perm = 1 := (perm_of_mkQ hdc).symm
  have hc1 : eqPi c 1 = false := eqPi_false (by rw [← hdc, map_one]; exact hδ1)
  have hcz : eqPi c z0 = false := eqPi_false (by rw [← hdc]; exact hδz)
  obtain ⟨d, hd, hcd⟩ := dlOK_sound small.2.1 c hc hp hc1 hcz
  have hdd : mkQ 6 (ofVec dv) = mkQ 6 d := hdc.trans (eqPi_iff_mkQ.1 hcd)
  have hdv : ∃ u, d = ofVec u := by
    simp only [Dl, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨u, rfl⟩ := hdv
  intro hge
  have h4 : mkQ 6 (ofPerm gp * ofVec u * (ofPerm gp)⁻¹) = mkQ 6 (ofVec u) := by
    rw [← conj_vec gv u gp]
    simp only [map_mul, map_inv]
    rw [← hdd]
    exact hge
  have h3 := htv _ hd
  rw [eqPi_iff_mkQ.2 h4] at h3
  exact Bool.noConfusion h3

theorem transW_even : ∀ σ ∈ transW, σ ∈ alternatingGroup (Fin 6) := by
  intro σ hσ
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
  have hd : transD.all (fun q => !decide (q.1 = q.2.1) && !decide (q.2.2.1 = q.2.2.2)) = true := by
    decide +kernel
  have key := List.all_eq_true.1 hd q hq
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at key
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap key.1,
    Equiv.Perm.sign_swap key.2]
  decide

theorem exists_zip {α β : Type*} : ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
    ∀ y ∈ l1, ∃ σ, (y, σ) ∈ l1.zip l2
  | [], _, _, y, hy => absurd hy List.not_mem_nil
  | _ :: _, [], h, _, _ => absurd h (by simp)
  | a :: l1, b :: l2, h, y, hy => by
    rw [List.zip_cons_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨b, List.mem_cons_self⟩
    · obtain ⟨σ, hσ⟩ := exists_zip l1 l2 (by simpa using h) y hy
      exact ⟨σ, List.mem_cons_of_mem _ hσ⟩

theorem conj_rep {x : AEQ 6} (hx : InU x) (h1 : x ≠ 1) :
    ∃ s ∈ TL4.aeModel 6, x = s * mkQ 6 (ofVec (indL [(0 : Fin 6), 1])) * s⁻¹ := by
  obtain ⟨v, hv, rfl⟩ := inU_iff.mp hx
  have hm : enc (ofVec v) ∈ E32 := by
    rw [E32_eq]
    exact List.mem_map_of_mem (mem_E32 hv)
  have hu := List.all_eq_true.1 ae6t_ucover _ hm
  obtain ⟨y, hy, hvy⟩ := (inModPi_iff (pp := pi12) rfl _ _).1 hu
  rcases List.mem_cons.1 hy with rfl | hy
  · exact absurd ((eqPi_iff_mkQ.1 hvy).trans (map_one _)) h1
  · obtain ⟨σ, hσ⟩ := exists_zip U15 transW rfl y hy
    have ht := transOK_sound (b := ofVec (indL [(0 : Fin 6), 1])) rfl ae6t_trans (y, σ) hσ
    refine ⟨mkQ 6 (ofPerm σ), TC.Thin.mem_aeModel_ofPerm (transW_even σ (List.of_mem_zip hσ).2), ?_⟩
    rw [eqPi_iff_mkQ.1 hvy, ← eqPi_iff_mkQ.1 ht]
    simp only [map_mul, map_inv]

theorem trans_k :
    ∀ x y : AEQ 6, InU x → InU y → x ≠ 1 → y ≠ 1 → ∃ g ∈ TL4.aeModel 6, g * x * g⁻¹ = y := by
  intro x y hx hy hx1 hy1
  obtain ⟨s, hs, rfl⟩ := conj_rep hx hx1
  obtain ⟨t, ht, rfl⟩ := conj_rep hy hy1
  exact ⟨t * s⁻¹, mul_mem ht (inv_mem hs), by group⟩

theorem ae6Fin_k : AE6Fin := ae6Fin_of_base card_α₀ trans_k centU₀ twin2₀ twin3₀ twin4₀

end CFSG.KD.AE6Twin

end
