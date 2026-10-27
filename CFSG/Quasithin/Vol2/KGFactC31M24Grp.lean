module

public import CFSG.Quasithin.Vol2.KGFactC31M24Base
public import CFSG.Quasithin.Vol2.KGFactC31Gen

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 Matrix _root_.Certificates

@[expose] def basisOf (ws : List (List ℤ)) : Fin ws.length → G₀ := fun i => elt (ws.get i)

theorem forall₂_basisOf (ws : List (List ℤ)) :
    List.Forall₂ (Rep 24) (ws.map (wordT 24 gensT))
      (List.ofFn fun i => ((basisOf ws i : G₀) : Equiv.Perm (Fin 24))) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, basisOf]
  exact rep_elt _

@[expose] def vO : Fin 4 → G₀ := basisOf oW
@[expose] def vS : Fin 6 → G₀ := basisOf sW
@[expose] def vS16 : Fin 4 → G₀ := basisOf s16W
@[expose] def vS32 : Fin 5 → G₀ := basisOf s32W
@[expose] def vR2 : Fin 4 → G₀ := basisOf r2W
@[expose] def vU4 : Fin 3 → G₀ := basisOf u4W
@[expose] def vU5 : Fin 3 → G₀ := basisOf u5W
@[expose] def vU6 : Fin 3 → G₀ := basisOf u6W
@[expose] def vT : Fin 6 → G₀ := basisOf tW
@[expose] def vEt : Fin 6 → G₀ := basisOf etW

theorem forall₂_o : List.Forall₂ (Rep 24) oT
    (List.ofFn fun i => ((vO i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf oW
theorem forall₂_s : List.Forall₂ (Rep 24) sT
    (List.ofFn fun i => ((vS i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf sW
theorem forall₂_s16 : List.Forall₂ (Rep 24) s16T
    (List.ofFn fun i => ((vS16 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf s16W
theorem forall₂_s32 : List.Forall₂ (Rep 24) s32T
    (List.ofFn fun i => ((vS32 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf s32W
theorem forall₂_r2 : List.Forall₂ (Rep 24) r2T
    (List.ofFn fun i => ((vR2 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf r2W
theorem forall₂_u4 : List.Forall₂ (Rep 24) u4T
    (List.ofFn fun i => ((vU4 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf u4W
theorem forall₂_u5 : List.Forall₂ (Rep 24) u5T
    (List.ofFn fun i => ((vU5 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf u5W
theorem forall₂_u6 : List.Forall₂ (Rep 24) u6T
    (List.ofFn fun i => ((vU6 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf u6W
theorem forall₂_t : List.Forall₂ (Rep 24) tT
    (List.ofFn fun i => ((vT i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf tW
theorem forall₂_et : List.Forall₂ (Rep 24) etT
    (List.ofFn fun i => ((vEt i : G₀) : Equiv.Perm (Fin 24))) := forall₂_basisOf etW

theorem basis_of_ok {k : ℕ} {v : Fin k → G₀} {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (h : ebasisOK 24 bs = true) : EBasis v :=
  EBasis.of_map (f := NativeSporadic.M24.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn24 hbs h)

theorem basis_o : EBasis vO := basis_of_ok forall₂_o c_eb_o
theorem basis_s : EBasis vS := basis_of_ok forall₂_s c_eb_s
theorem basis_s16 : EBasis vS16 := basis_of_ok forall₂_s16 c_eb_s16
theorem basis_s32 : EBasis vS32 := basis_of_ok forall₂_s32 c_eb_s32
theorem basis_r2 : EBasis vR2 := basis_of_ok forall₂_r2 c_eb_r2
theorem basis_u4 : EBasis vU4 := basis_of_ok forall₂_u4 c_eb_u4
theorem basis_u5 : EBasis vU5 := basis_of_ok forall₂_u5 c_eb_u5
theorem basis_u6 : EBasis vU6 := basis_of_ok forall₂_u6 c_eb_u6
theorem basis_t : EBasis vT := basis_of_ok forall₂_t c_eb_t
theorem basis_et : EBasis vEt := basis_of_ok forall₂_et c_eb_et

theorem vO_zero : ((vO 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vS_zero : ((vS 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vS16_zero : ((vS16 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vS32_zero : ((vS32 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vR2_zero : ((vR2 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vU4_zero : ((vU4 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vU5_zero : ((vU5 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl
theorem vU6_zero : ((vU6 0 : G₀) : Equiv.Perm (Fin 24)) = b1 := rfl
theorem vT_zero : ((vT 0 : G₀) : Equiv.Perm (Fin 24)) = b0 := rfl

theorem card_centralizer_eq_subtype {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) =
      Nat.card {g : NativeSporadic.M24 // ∀ i, g * ((v i : G₀) : Equiv.Perm (Fin 24)) =
        ((v i : G₀) : Equiv.Perm (Fin 24)) * g} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx i
    have := hx _ (mem_eSub hv i)
    exact (congrArg Subtype.val this).symm
  · intro hx y hy
    obtain ⟨c, rfl⟩ := (mem_eSub_iff hv y).mp hy
    have : Commute x (eElt v c) := commute_eElt (fun i => Subtype.ext (hx i)) c
    exact this.eq.symm

theorem commAll_iff {k : ℕ} {v : Fin k → G₀} {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (T : Table) (g : Equiv.Perm (Fin 24)) (hT : Rep 24 T g) :
    commAll 24 bs T = true ↔ ∀ i, g * ((v i : G₀) : Equiv.Perm (Fin 24)) =
      ((v i : G₀) : Equiv.Perm (Fin 24)) * g := by
  unfold commAll
  exact all_iff_of_forall₂ hbs fun b x hb => (tblEq_iff_eq (Rep.compT hT hb) (Rep.compT hb hT))

theorem card_centralizer_eq_cb0
    {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (i₀ : Fin k) (hi₀ : ((v i₀ : G₀) : Equiv.Perm (Fin 24)) = b0) {N : ℕ}
    (h : cb0T.countP (commAll 24 bs) = N) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = N := by
  classical
  rw [card_centralizer_eq_subtype, ← h]
  exact card_eq_countP_cb0 (commAll_iff hbs) fun g hg => by rw [← hi₀]; exact hg i₀

theorem card_centralizer_eq_cb1
    {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (i₀ : Fin k) (hi₀ : ((v i₀ : G₀) : Equiv.Perm (Fin 24)) = b1) {N : ℕ}
    (h : cb1T.countP (commAll 24 bs) = N) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = N := by
  classical
  rw [card_centralizer_eq_subtype, ← h]
  exact card_eq_countP_cb1 (commAll_iff hbs) fun g hg => by rw [← hi₀]; exact hg i₀

theorem eSub_le_centralizer {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    eSub hv ≤ Subgroup.centralizer (eSub hv : Set G₀) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv y x hy hx

theorem centralizer_eq_of_card {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    (h : Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = 2 ^ k) :
    Subgroup.centralizer (eSub hv : Set G₀) = eSub hv :=
  le_antisymm (centralizer_le_of_card hv h) (eSub_le_centralizer hv)

theorem le_centralizer_of_comm {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {s : Set G₀}
    (h : ∀ i, ∀ x ∈ s, v i * x = x * v i) :
    eSub hv ≤ Subgroup.centralizer (Subgroup.closure s : Set G₀) := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  refine Subgroup.closure_induction (p := fun y _ => y * v i = v i * y)
    (fun x hx => (h i x hx).symm) (by simp) (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) hy
  · rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  · calc a⁻¹ * v i = a⁻¹ * (v i * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * v i) * a⁻¹ := by rw [ha]
      _ = v i * a⁻¹ := by group

theorem comm_of_all {k l : ℕ} {v : Fin k → G₀} {w : Fin l → G₀} {bs cs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (hcs : List.Forall₂ (Rep 24) cs (List.ofFn fun i => ((w i : G₀) : Equiv.Perm (Fin 24))))
    (h : bs.all (commAll 24 cs) = true) : ∀ i j, v i * w j = w j * v i := by
  intro i j
  obtain ⟨b, hb, hbi⟩ : ∃ b ∈ bs, Rep 24 b ((v i : G₀) : Equiv.Perm (Fin 24)) :=
    exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have h1 := (commAll_iff hcs b _ hbi).mp (List.all_eq_true.mp h b hb) j
  exact Subtype.ext h1

theorem cent_o :
    Subgroup.centralizer (eSub basis_o : Set G₀) = eSub basis_o :=
  centralizer_eq_of_card basis_o (by
    rw [card_centralizer_eq_cb0 basis_o forall₂_o 0 vO_zero c_cent_o]; norm_num)

theorem cent_s :
    Subgroup.centralizer (eSub basis_s : Set G₀) = eSub basis_s :=
  centralizer_eq_of_card basis_s (by
    rw [card_centralizer_eq_cb0 basis_s forall₂_s 0 vS_zero c_cent_s]; norm_num)

theorem cent_r2 :
    Subgroup.centralizer (eSub basis_r2 : Set G₀) = eSub basis_r2 :=
  centralizer_eq_of_card basis_r2 (by
    rw [card_centralizer_eq_cb0 basis_r2 forall₂_r2 0 vR2_zero c_cent_r2]; norm_num)

theorem cent_t :
    Subgroup.centralizer (eSub basis_t : Set G₀) = eSub basis_t :=
  centralizer_eq_of_card basis_t (by
    rw [card_centralizer_eq_cb0 basis_t forall₂_t 0 vT_zero c_cent_t]; norm_num)

theorem cent_s16 :
    Subgroup.centralizer (eSub basis_s16 : Set G₀) = eSub basis_s := by
  have hle : eSub basis_s ≤ Subgroup.centralizer (eSub basis_s16 : Set G₀) := by
    rw [eSub_eq_closure basis_s16]
    refine le_centralizer_of_comm basis_s fun i x hx => ?_
    obtain ⟨j, rfl⟩ := hx
    exact comm_of_all forall₂_s forall₂_s16 c_comm_s16 i j
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_eq_cb0 basis_s16 forall₂_s16 0 vS16_zero c_cent_s16, card_eSub]
  norm_num

theorem cent_s32 :
    Subgroup.centralizer (eSub basis_s32 : Set G₀) = eSub basis_s := by
  have hle : eSub basis_s ≤ Subgroup.centralizer (eSub basis_s32 : Set G₀) := by
    rw [eSub_eq_closure basis_s32]
    refine le_centralizer_of_comm basis_s fun i x hx => ?_
    obtain ⟨j, rfl⟩ := hx
    exact comm_of_all forall₂_s forall₂_s32 c_comm_s32 i j
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_eq_cb0 basis_s32 forall₂_s32 0 vS32_zero c_cent_s32, card_eSub]
  norm_num

@[expose] def d4 : G₀ := elt d4W

@[expose] def d6 : G₀ := elt d6W

theorem forall₂_conjAll {w : List ℤ} (hinv : invOK 24 (wordT 24 gensT w)
    (invT 24 (wordT 24 gensT w)) = true) {l : ℕ} {v : Fin l → G₀} {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24)))) :
    List.Forall₂ (Rep 24) (conjAll (wordT 24 gensT w) bs) (List.ofFn fun i =>
      (((elt w * v i * (elt w)⁻¹ : G₀)) : Equiv.Perm (Fin 24))) := by
  have hc : Rep 24 (wordT 24 gensT w) ((elt w : G₀) : Equiv.Perm (Fin 24)) := rep_elt _
  have hci := Rep.inv_of_invOK hc hinv
  have h := forall₂_conjTab hbs hc hci
  have e : (List.ofFn fun i => (((elt w * v i * (elt w)⁻¹ : G₀)) : Equiv.Perm (Fin 24))) =
      List.ofFn fun i => ((elt w : G₀) : Equiv.Perm (Fin 24)) * ((v i : G₀) : Equiv.Perm (Fin 24)) *
        ((elt w : G₀) : Equiv.Perm (Fin 24))⁻¹ := rfl
  rw [e]
  exact h

theorem basis_conj {l : ℕ} {v : Fin l → G₀} (hv : EBasis v) (c : G₀) :
    EBasis fun i => c * v i * c⁻¹ :=
  hv.map (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective

theorem eSub_conj {l : ℕ} {v : Fin l → G₀} (hv : EBasis v) (c : G₀) :
    eSub (basis_conj hv c) = (eSub hv).map (MulAut.conj c).toMonoidHom :=
  (eSub_map hv (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).symm

theorem cent_u4 :
    Subgroup.centralizer (eSub basis_u4 : Set G₀) =
      (eSub basis_r2).map (MulAut.conj d4).toMonoidHom := by
  have hcs := forall₂_conjAll c_d4_inv forall₂_r2
  have hle : eSub (basis_conj basis_r2 d4) ≤ Subgroup.centralizer (eSub basis_u4 : Set G₀) := by
    rw [eSub_eq_closure basis_u4]
    refine le_centralizer_of_comm (basis_conj basis_r2 d4) fun i x hx => ?_
    obtain ⟨j, rfl⟩ := hx
    exact comm_of_all hcs forall₂_u4 c_d4_comm i j
  rw [← eSub_conj]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_eq_cb0 basis_u4 forall₂_u4 0 vU4_zero c_cent_u4, card_eSub]
  norm_num

theorem cent_u6 :
    Subgroup.centralizer (eSub basis_u6 : Set G₀) =
      (eSub basis_t).map (MulAut.conj d6).toMonoidHom := by
  have hcs := forall₂_conjAll c_d6_inv forall₂_t
  have hle : eSub (basis_conj basis_t d6) ≤ Subgroup.centralizer (eSub basis_u6 : Set G₀) := by
    rw [eSub_eq_closure basis_u6]
    refine le_centralizer_of_comm (basis_conj basis_t d6) fun i x hx => ?_
    obtain ⟨j, rfl⟩ := hx
    exact comm_of_all hcs forall₂_u6 c_d6_comm i j
  rw [← eSub_conj]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_eq_cb1 basis_u6 forall₂_u6 0 vU6_zero c_cent_u6, card_eSub]
  norm_num

end CFSG.Quasithin.KGC31.M24

end
