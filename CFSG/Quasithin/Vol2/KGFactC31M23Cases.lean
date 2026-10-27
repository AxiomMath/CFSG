module

public import CFSG.Quasithin.Vol2.KGFactC31M23Base
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Duad
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Vol2.KGFactC31M23Ref
public import CFSG.Quasithin.Vol2.KGFactC31A7

public section

namespace CFSG.Quasithin.KGC31.M23

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 Matrix _root_.Certificates

@[expose] def basisOf (ws : List (List ℤ)) : Fin ws.length → G₀ := fun i => elt (ws.get i)

theorem forall₂_basisOf (ws : List (List ℤ)) :
    List.Forall₂ (Rep 23) (ws.map (wordT 23 gensT))
      (List.ofFn fun i => ((basisOf ws i : G₀) : Equiv.Perm (Fin 23))) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, basisOf]
  exact rep_elt _

theorem forall₂_words (ws : List (List ℤ)) :
    List.Forall₂ (Rep 23) (ws.map (wordT 23 gensT))
      (ws.map fun w => ((elt w : G₀) : Equiv.Perm (Fin 23))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (rep_elt w) ih

@[expose] def vW : Fin 4 → G₀ := basisOf wW
@[expose] def vDuad : Fin 4 → G₀ := basisOf tW
@[expose] def vE8 : Fin 3 → G₀ := basisOf eW
@[expose] def vS : Fin 3 → G₀ := basisOf sW

theorem forall₂_w : List.Forall₂ (Rep 23) wT
    (List.ofFn fun i => ((vW i : G₀) : Equiv.Perm (Fin 23))) := forall₂_basisOf wW
theorem forall₂_duad : List.Forall₂ (Rep 23) tT
    (List.ofFn fun i => ((vDuad i : G₀) : Equiv.Perm (Fin 23))) := forall₂_basisOf tW
theorem forall₂_e8 : List.Forall₂ (Rep 23) eT
    (List.ofFn fun i => ((vE8 i : G₀) : Equiv.Perm (Fin 23))) := forall₂_basisOf eW
theorem forall₂_s : List.Forall₂ (Rep 23) sT
    (List.ofFn fun i => ((vS i : G₀) : Equiv.Perm (Fin 23))) := forall₂_basisOf sW

theorem basis_w : EBasis vW :=
  EBasis.of_map (f := NativeSporadic.M23.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn23 forall₂_w c_eb_w)
theorem basis_duad : EBasis vDuad :=
  EBasis.of_map (f := NativeSporadic.M23.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn23 forall₂_duad c_eb_duad)
theorem basis_e8 : EBasis vE8 :=
  EBasis.of_map (f := NativeSporadic.M23.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn23 forall₂_e8 c_eb_e8)
theorem basis_s : EBasis vS :=
  EBasis.of_map (f := NativeSporadic.M23.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn23 forall₂_s c_eb_s)

theorem vW_zero : ((vW 0 : G₀) : Equiv.Perm (Fin 23)) = b0 := rfl
theorem vDuad_zero : ((vDuad 0 : G₀) : Equiv.Perm (Fin 23)) = b0 := rfl
theorem vE8_zero : ((vE8 0 : G₀) : Equiv.Perm (Fin 23)) = b0 := rfl
theorem vS_zero : ((vS 0 : G₀) : Equiv.Perm (Fin 23)) = b0 := rfl

theorem card_centralizer_eq_cb {k : ℕ} {v : Fin k → G₀}
    (hv : EBasis v) {bs : List Table} (hbs : List.Forall₂ (Rep 23) bs (List.ofFn fun i =>
      ((v i : G₀) : Equiv.Perm (Fin 23)))) (i₀ : Fin k) (hi₀ : ((v i₀ : G₀) :
        Equiv.Perm (Fin 23)) = b0) {N : ℕ} (h : cbT.countP (commAll 23 bs) = N) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = N := by
  classical
  rw [← h, ← card_eq_countP_cbT (P := fun g => ∀ i, g * ((v i : G₀) : Equiv.Perm (Fin 23)) =
    ((v i : G₀) : Equiv.Perm (Fin 23)) * g)]
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx i
      have := hx _ (mem_eSub hv i)
      exact (congrArg Subtype.val this).symm
    · intro hx y hy
      obtain ⟨c, rfl⟩ := (mem_eSub_iff hv y).mp hy
      have : Commute x (eElt v c) := commute_eElt (fun i => Subtype.ext (hx i)) c
      exact this.eq.symm
  · intro T g hT
    unfold commAll
    exact all_iff_of_forall₂ hbs fun b x hb => (tblEq_iff_eq (Rep.compT hT hb) (Rep.compT hb hT))
  · intro g hg
    rw [← hi₀]
    exact hg i₀

theorem cent_w :
    Subgroup.centralizer (eSub basis_w : Set G₀) ≤ eSub basis_w :=
  centralizer_le_of_card basis_w (card_centralizer_eq_cb basis_w forall₂_w 0 vW_zero
    c_cent_w_count)

theorem cent_duad :
    Subgroup.centralizer (eSub basis_duad : Set G₀) ≤ eSub basis_duad :=
  centralizer_le_of_card basis_duad (card_centralizer_eq_cb basis_duad forall₂_duad 0
    vDuad_zero c_cent_duad_count)

theorem cent_e8 :
    Subgroup.centralizer (eSub basis_e8 : Set G₀) ≤ eSub basis_e8 :=
  centralizer_le_of_card basis_e8 (card_centralizer_eq_cb basis_e8 forall₂_e8 0 vE8_zero
    c_cent_e8_count)

theorem card_cent_s :
    Nat.card (Subgroup.centralizer (eSub basis_s : Set G₀)) = 16 :=
  card_centralizer_eq_cb basis_s forall₂_s 0 vS_zero c_cent_s_count

theorem card_le_of_cosetOK {k : ℕ}
    {v : Fin k → Equiv.Perm (Fin 23)} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 23) bs (List.ofFn v)) (i₀ : Fin k) (hi₀ : v i₀ = b0)
    {ws : List (List ℤ)} (hok : cosetOK 23 b0T bs (ws.map (wordT 23 gensT)) = true)
    {f : Table → Bool} {P : Equiv.Perm (Fin 23) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 23 T g → (f T = true ↔ P g)) (hPN : ∀ g, P g → g ∈ eNorm hv) :
    Nat.card {g : NativeSporadic.M23 // P g} ≤
      cosetCount 23 cbT (ws.map (wordT 23 gensT)) f := by
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
    exact exists_conj_of_cosetOK hn23 hv hbs rep_b0 (forall₂_words ws) hok hx hx1

theorem card_eNorm_eq {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    Nat.card (eNorm hv) = Nat.card {g : NativeSporadic.M23 // (g : Equiv.Perm (Fin 23)) ∈
      eNorm (hv.map (f := NativeSporadic.M23.subtype) Subtype.val_injective)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [mem_eNorm_iff hv, mem_eNorm_iff]
  refine forall_congr' fun i => exists_congr fun c => ?_
  have hE : eElt (fun i => NativeSporadic.M23.subtype (v i)) c =
      ((eElt v c : G₀) : Equiv.Perm (Fin 23)) := (map_eElt NativeSporadic.M23.subtype c).symm
  rw [hE]
  constructor
  · intro h1; rw [← h1]; rfl
  · intro h1; exact Subtype.ext h1

theorem coe_mem_eNorm {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {g : G₀} (hg : g ∈ eNorm hv) :
    (g : Equiv.Perm (Fin 23)) ∈
      eNorm (hv.map (f := NativeSporadic.M23.subtype) Subtype.val_injective) := by
  rw [mem_eNorm_iff]
  intro i
  obtain ⟨c, hc⟩ := (mem_eNorm_iff hv g).mp hg i
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  rw [show eElt (fun i => NativeSporadic.M23.subtype (v i)) c =
    ((eElt v c : G₀) : Equiv.Perm (Fin 23)) from (map_eElt NativeSporadic.M23.subtype c).symm]
  simpa using this

theorem card_eNorm_w_le :
    Nat.card (eNorm basis_w) ≤ 40320 := by
  classical
  have hvP := basis_w.map (f := NativeSporadic.M23.subtype) Subtype.val_injective
  rw [card_eNorm_eq, ← c_ccount_w]
  exact card_le_of_cosetOK hvP forall₂_w 0 vW_zero c_coset_w (P := fun g => g ∈ eNorm hvP)
    (fun T g hT => normAll_iff hn23 hvP forall₂_w hT) fun _ h => h

theorem card_eNorm_e8_le :
    Nat.card (eNorm basis_e8) ≤ 1344 := by
  classical
  have hvP := basis_e8.map (f := NativeSporadic.M23.subtype) Subtype.val_injective
  rw [card_eNorm_eq, ← c_ccount_e8]
  exact card_le_of_cosetOK hvP forall₂_e8 0 vE8_zero c_coset_e8 (P := fun g => g ∈ eNorm hvP)
    (fun T g hT => normAll_iff hn23 hvP forall₂_e8 hT) fun _ h => h

theorem triT_lt : ∀ i ∈ triT, i < 23 := by decide

theorem hexH_lt : ∀ i ∈ hexH, i < 23 := by decide

@[expose] def nTri : Subgroup G₀ :=
  eNorm basis_duad ⊓ (ptStab 23 triT).comap NativeSporadic.M23.subtype

theorem mem_nTri {x : G₀} :
    x ∈ nTri ↔ x ∈ eNorm basis_duad ∧
      ∀ i : Fin 23, i.val ∈ triT → (x : Equiv.Perm (Fin 23)) i = i :=
  Iff.rfl

theorem card_nTri_le :
    Nat.card nTri ≤ 960 := by
  classical
  have hvP := basis_duad.map (f := NativeSporadic.M23.subtype) Subtype.val_injective
  have h : Nat.card nTri = Nat.card {g : NativeSporadic.M23 // (g : Equiv.Perm (Fin 23)) ∈
      eNorm hvP ∧ (g : Equiv.Perm (Fin 23)) ∈ ptStab 23 triT} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [mem_nTri, mem_ptStab]
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨coe_mem_eNorm basis_duad hx, hp⟩
    · rintro ⟨hx, hp⟩
      refine ⟨?_, hp⟩
      rw [mem_eNorm_iff basis_duad]
      intro i
      obtain ⟨c, hc⟩ := (mem_eNorm_iff hvP _).mp hx i
      refine ⟨c, Subtype.ext ?_⟩
      rw [show ((eElt vDuad c : G₀) : Equiv.Perm (Fin 23)) =
        eElt (fun i => NativeSporadic.M23.subtype (vDuad i)) c from
          map_eElt NativeSporadic.M23.subtype c]
      exact hc
  rw [h, ← c_ccount_duad]
  exact card_le_of_cosetOK hvP forall₂_duad 0 vDuad_zero c_coset_duad
    (P := fun g => g ∈ eNorm hvP ∧ g ∈ ptStab 23 triT)
    (fun T g hT => by
      rw [Bool.and_eq_true, normAll_iff hn23 hvP forall₂_duad hT, fixesAll_iff triT_lt hT]
      rfl)
    fun _ h => h.1

@[expose] def genOf (ws : List (List ℤ)) : Subgroup G₀ := Subgroup.closure {x | ∃ w ∈ ws, elt w = x}

theorem map_genOf (ws : List (List ℤ)) :
    (genOf ws).map NativeSporadic.M23.subtype =
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

theorem card_genOf {ws : List (List ℤ)} {Q : RawSchreierDatum 23}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ ws.map fun w => tab (wordG gensG w)})
    (hv : ValidSchreier Q) : Nat.card (genOf ws) = Q.orderCertificate := by
  rw [Q.orderCertificate_eq_card hv, hQ, ← map_genOf,
    Subgroup.card_map_of_injective Subtype.val_injective]

theorem exists_index_of_mem {ws : List (List ℤ)} (hl : ws.length = 2) {w : List ℤ}
    (hw : w ∈ ws) : ∃ j < 2, ws.getD j [] = w := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
  exact ⟨j, hl ▸ hj, List.getD_eq_getElem _ _ hj⟩

theorem genOf_le {ws : List (List ℤ)} (hl : ws.length = 2) {K : Subgroup G₀}
    (h : ∀ j < 2, elt (ws.getD j []) ∈ K) : genOf ws ≤ K := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hl hw
  exact h j hj

@[expose] def matOf (k : ℕ) (masks : List (List ℕ)) (j : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun r i => maskVec k ((masks.getD j []).getD i 0) r

theorem conj_gen {k : ℕ} {ws : List (List ℤ)} {masks : List (List ℕ)} {v : Fin k → G₀}
    {bs : List Table} (hbs : List.Forall₂ (Rep 23) bs (List.ofFn fun i => ((v i : G₀) :
      Equiv.Perm (Fin 23))))
    (h : ((ws.map fun w => tab (wordG gensG w)).zip masks).all
      (fun p => masksOK 23 bs (toTable p.1) p.2) = true) {j : ℕ} (hj : j < ws.length)
    (hjm : j < masks.length) (i : Fin k) :
    elt (ws.getD j []) * v i * (elt (ws.getD j []))⁻¹ = eElt v fun r => matOf k masks j r i := by
  have hmem : ((ws.map fun w => tab (wordG gensG w))[j]'(by simpa using hj), masks[j]) ∈
      (ws.map fun w => tab (wordG gensG w)).zip masks := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by rw [List.length_zip, List.length_map]; omega, by simp⟩
  have h1 := List.all_eq_true.mp h _ hmem
  simp only [List.getElem_map, tab_eq] at h1
  have hT : Rep 23 (toTable (wordG gensG ws[j])) (wordG gensG ws[j]) := rep_toTable hn23 _
  have h2 := conj_of_masksOK hn23 hbs hT h1 i
  apply Subtype.ext
  rw [List.getD_eq_getElem _ _ hj]
  show wordG gensG ws[j] * ((v i : G₀) : Equiv.Perm (Fin 23)) * (wordG gensG ws[j])⁻¹ = _
  rw [h2]
  have hE : eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 23))) (fun r => matOf k masks j r i) =
      ((eElt v fun r => matOf k masks j r i : G₀) : Equiv.Perm (Fin 23)) :=
    (map_eElt NativeSporadic.M23.subtype _).symm
  rw [← hE]
  congr 1
  funext r
  simp [matOf, List.getElem?_eq_getElem hjm]

@[expose] def Mw : Subgroup G₀ := genOf wGenW
@[expose] def Mduad : Subgroup G₀ := genOf tGenW
@[expose] def Me : Subgroup G₀ := genOf eGenW

theorem card_Mw : Nat.card Mw = 40320 := by
  rw [Mw, card_genOf (Q := wChain) (certificate_originalSubgroup _ _ _ _ _) c_wChain_check,
    c_wChain_order]

theorem card_Mduad : Nat.card Mduad = 960 := by
  rw [Mduad, card_genOf (Q := tChain) (certificate_originalSubgroup _ _ _ _ _) c_tChain_check,
    c_tChain_order]

theorem card_Me : Nat.card Me = 1344 := by
  rw [Me, card_genOf (Q := eChain) (certificate_originalSubgroup _ _ _ _ _) c_eChain_check,
    c_eChain_order]

theorem wGenW_length : wGenW.length = 2 := rfl
theorem wMasks_length : wMasks.length = 2 := rfl
theorem tGenW_length : tGenW.length = 2 := rfl
theorem tMasks_length : tMasks.length = 2 := rfl
theorem eGenW_length : eGenW.length = 2 := rfl
theorem eMasks_length : eMasks.length = 2 := rfl

theorem conj_w {j : ℕ} (hj : j < 2) (i : Fin 4) :
    elt (wGenW.getD j []) * vW i * (elt (wGenW.getD j []))⁻¹ =
      eElt vW fun r => matOf 4 wMasks j r i :=
  conj_gen forall₂_w c_masks_w (by rw [wGenW_length]; exact hj)
    (by rw [wMasks_length]; exact hj) i

theorem Mw_le_eNorm : Mw ≤ eNorm basis_w :=
  genOf_le wGenW_length fun j hj => mem_eNorm basis_w (matOf 4 wMasks j) fun i => conj_w hj i

theorem Mw_eq : Mw = eNorm basis_w :=
  Subgroup.eq_of_le_of_card_ge Mw_le_eNorm (by rw [card_Mw]; exact card_eNorm_w_le)

theorem trans_w : ∀ c : Fin 4 → ZMod 2, c ≠ 0 →
    (matStep (matOf 4 wMasks 0) (matOf 4 wMasks 1))^[7] {c} = Finset.univ.erase 0 := by
  decide +kernel

theorem irr_of_gens {Γ : Type*} [Group Γ] {v : Fin 4 → Γ} (hv : EBasis v) {g₁ g₂ : Γ}
    (hg₁ : ∀ i, g₁ * v i * g₁⁻¹ = eElt v fun r => matOf 4 wMasks 0 r i)
    (hg₂ : ∀ i, g₂ * v i * g₂⁻¹ = eElt v fun r => matOf 4 wMasks 1 r i) {W : Subgroup Γ}
    (hW : W ≤ eSub hv) (hn₁ : g₁ ∈ Subgroup.normalizer (W : Set Γ))
    (hn₂ : g₂ ∈ Subgroup.normalizer (W : Set Γ)) : W = ⊥ ∨ W = eSub hv :=
  eq_bot_or_eq_of_trans hv trans_w hg₁ hg₂ hW hn₁ hn₂

@[expose] def hexSet : Finset (Fin 23) := Finset.univ.filter fun i => i.val ∈ hexH

theorem card_hexSet : hexSet.card = 7 := by decide

theorem mem_hexSet (i : Fin 23) : i ∈ hexSet ↔ i.val ∈ hexH := by
  simp [hexSet]

theorem fix_w_iff (i : Fin 23) :
    (∀ u ∈ eSub (basis_w.map (f := NativeSporadic.M23.subtype) Subtype.val_injective),
      u i = i) ↔ i ∈ hexSet := by
  rw [fix_eSub_iff, mem_hexSet]
  exact fixSetIs_iff forall₂_w c_fix_w i

theorem Mw_le_setStab (x : ↥Mw) :
    NativeSporadic.M23.subtype (Mw.subtype x) ∈ setStab hexSet :=
  mem_setStab_of_normalizer _ fix_w_iff (coe_mem_eNorm basis_w (Mw_le_eNorm x.2))

@[expose] noncomputable def wAct :
    ↥Mw →* Equiv.Perm (Fin 7) :=
  (setAct hexSet card_hexSet).comp
    ((NativeSporadic.M23.subtype.comp Mw.subtype).codRestrict _ Mw_le_setStab)

theorem wAct_eq_one_iff (x : ↥Mw) :
    wAct x = 1 ↔ ∀ i : Fin 23, i.val ∈ hexH → ((x : G₀) : Equiv.Perm (Fin 23)) i = i := by
  rw [wAct, MonoidHom.comp_apply, setAct_eq_one_iff]
  simp only [mem_hexSet]
  rfl

theorem vW_le_Mw : eSub basis_w ≤ Mw :=
  Mw_eq ▸ Subgroup.le_normalizer

theorem card_fix_hexH :
    Nat.card {x : ↥Mw // ∀ i : Fin 23, i.val ∈ hexH →
      ((x : G₀) : Equiv.Perm (Fin 23)) i = i} = 16 := by
  classical
  have h := card_subtype_eq_countProducts hn23 wChain c_wChain_check
    (P := fun g => ∀ i : Fin 23, i.val ∈ hexH → g i = i) fun T g hT => fixesAll_iff hexH_lt hT
  rw [c_kerH] at h
  have hQ : wChain.originalSubgroup = Mw.map NativeSporadic.M23.subtype := by
    rw [wChain, certificate_originalSubgroup, Mw, map_genOf]
    rfl
  rw [hQ] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv
    (Mw.equivMapOfInjective _ Subtype.val_injective).toEquiv fun x => Iff.rfl)

theorem ker_wAct :
    wAct.ker = (eSub basis_w).subgroupOf Mw := by
  classical
  have hle : (eSub basis_w).subgroupOf Mw ≤ wAct.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, wAct_eq_one_iff]
    intro i hi
    have hxP : ((x : G₀) : Equiv.Perm (Fin 23)) ∈
        eSub (basis_w.map (f := NativeSporadic.M23.subtype) Subtype.val_injective) := by
      rw [← eSub_map basis_w (f := NativeSporadic.M23.subtype) Subtype.val_injective]
      exact ⟨x, hx, rfl⟩
    exact (fix_w_iff i).mpr ((mem_hexSet i).mpr hi) _ hxP
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 : Nat.card wAct.ker = 16 := by
    rw [← card_fix_hexH]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [MonoidHom.mem_ker, wAct_eq_one_iff])
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe vW_le_Mw).toEquiv, card_eSub]
  norm_num

theorem range_wAct :
    wAct.range = alternatingGroup (Fin 7) := by
  apply A7.eq_alt7_of_card
  have h := card_range_eq vW_le_Mw wAct ker_wAct
  rw [card_eSub, card_Mw] at h
  omega

@[expose] noncomputable def wAlt :
    ↥Mw →* ↥(alternatingGroup (Fin 7)) :=
  wAct.codRestrict _ fun x => by rw [← range_wAct]; exact ⟨x, rfl⟩

theorem wAlt_surjective :
    Function.Surjective wAlt := by
  intro σ
  have hσ : (σ : Equiv.Perm (Fin 7)) ∈ wAct.range := by rw [range_wAct]; exact σ.2
  obtain ⟨x, hx⟩ := hσ
  exact ⟨x, Subtype.ext hx⟩

theorem ker_wAlt :
    wAlt.ker = (eSub basis_w).subgroupOf Mw := by
  rw [wAlt, MonoidHom.ker_codRestrict, ker_wAct]

theorem refData_w :
    RefData (eSub basis_w) Mw where
  cent := cent_w
  comm := fun a ha b hb => eSub_comm basis_w a b ha hb
  le := vW_le_Mw
  norm := Mw_le_eNorm
  perf := fun _ hK _ => Mw_eq ▸ hK
  simple := by
    have := A7.alt7_simple
    exact simple_of_surj wAlt wAlt_surjective ker_wAlt

theorem conj_duad {j : ℕ} (hj : j < 2) (i : Fin 4) :
    elt (tGenW.getD j []) * vDuad i * (elt (tGenW.getD j []))⁻¹ =
      eElt vDuad fun r => matOf 4 tMasks j r i :=
  conj_gen forall₂_duad c_masks_duad (by rw [tGenW_length]; exact hj)
    (by rw [tMasks_length]; exact hj) i

theorem duadMat_comm : ∀ j < 2, matOf 4 tMasks j * Duad.Om = Duad.Om * matOf 4 tMasks j := by
  decide

theorem duadMat_det : ∀ j < 2, (Duad.f4Mat (matOf 4 tMasks j)).det = 1 := by decide

theorem duadGen_norm {j : ℕ} (hj : j < 2) :
    elt (tGenW.getD j []) ∈ eNorm basis_duad :=
  mem_eNorm basis_duad (matOf 4 tMasks j) fun i => conj_duad hj i

theorem duadGen_eMat {j : ℕ} (hj : j < 2) :
    eMat basis_duad ⟨elt (tGenW.getD j []), duadGen_norm hj⟩ = matOf 4 tMasks j :=
  eMat_eq basis_duad _ _ fun i => conj_duad hj i

theorem duadGen_f4 {j : ℕ} (hj : j < 2) :
    elt (tGenW.getD j []) ∈ Duad.f4Stab basis_duad :=
  ⟨duadGen_norm hj, by rw [duadGen_eMat hj]; exact duadMat_comm j hj⟩

theorem Mduad_le_f4Stab : Mduad ≤ Duad.f4Stab basis_duad :=
  genOf_le tGenW_length fun _ hj => duadGen_f4 hj

theorem Mduad_le_eNorm : Mduad ≤ eNorm basis_duad :=
  fun _ hx => (Mduad_le_f4Stab hx).1

theorem Mduad_det (x : ↥Mduad) :
    (Duad.f4Mat (eMat basis_duad ⟨x, (Mduad_le_f4Stab x.2).1⟩)).det = 1 := by
  let D : ↥(Duad.f4Stab basis_duad) →* (Duad.F4)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (Duad.f4Rep basis_duad)
  let K : Subgroup G₀ := D.ker.map (Duad.f4Stab basis_duad).subtype
  have hmemK : ∀ (y : G₀) (hy : y ∈ Duad.f4Stab basis_duad),
      (Duad.f4Mat (eMat basis_duad ⟨y, hy.1⟩)).det = 1 → y ∈ K := by
    intro y hy hd
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show D ⟨y, hy⟩ = 1
    apply Units.ext
    simpa [D, Duad.f4Rep_coe] using hd
  have hle : Mduad ≤ K := genOf_le tGenW_length fun j hj =>
    hmemK _ (duadGen_f4 hj) (by rw [duadGen_eMat hj]; exact duadMat_det j hj)
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have h2 : (Duad.f4Mat (eMat basis_duad ⟨y, y.2.1⟩)).det = 1 := by
    have h3 := congrArg Units.val (show D y = 1 from hy)
    simpa [D, Duad.f4Rep_coe] using h3
  have hyx' : (⟨(y : G₀), y.2.1⟩ : ↥(eNorm basis_duad)) = ⟨x, (Mduad_le_f4Stab x.2).1⟩ :=
    Subtype.ext hyx
  rwa [hyx'] at h2

theorem fix_duad_iff (i : Fin 23) :
    (∀ u ∈ eSub (basis_duad.map (f := NativeSporadic.M23.subtype) Subtype.val_injective),
      u i = i) ↔ i.val ∈ triT := by
  rw [fix_eSub_iff]
  exact fixSetIs_iff forall₂_duad c_fix_duad i

theorem Mduad_le_nTri : Mduad ≤ nTri :=
  genOf_le tGenW_length fun j hj => mem_nTri.mpr ⟨duadGen_norm hj, by
    have h := c_tGen_fix
    rw [List.all_eq_true] at h
    have hmem : tab (wordG gensG (tGenW.getD j [])) ∈ tGen := by
      rw [List.getD_eq_getElem _ _ (by rw [tGenW_length]; exact hj)]
      exact List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩
    have h1 := h _ hmem
    rw [fixesAll_iff triT_lt (rep_toTable hn23 _), tab_eq] at h1
    exact h1⟩

theorem Mduad_eq : Mduad = nTri :=
  Subgroup.eq_of_le_of_card_ge Mduad_le_nTri (by rw [card_Mduad]; exact card_nTri_le)

theorem vDuad_le_Mduad :
    eSub basis_duad ≤ Mduad := by
  rw [Mduad_eq]
  refine fun x hx => mem_nTri.mpr ⟨Subgroup.le_normalizer hx, fun i hi => ?_⟩
  have hxP : ((x : G₀) : Equiv.Perm (Fin 23)) ∈
      eSub (basis_duad.map (f := NativeSporadic.M23.subtype) Subtype.val_injective) := by
    rw [← eSub_map basis_duad (f := NativeSporadic.M23.subtype) Subtype.val_injective]
    exact ⟨x, hx, rfl⟩
  exact (fix_duad_iff i).mpr hi _ hxP

@[expose] def triSet : Finset (Fin 23) := Finset.univ.filter fun i => i.val ∈ triT

theorem card_triSet : triSet.card = 3 := by decide

theorem perf_duad (K : Subgroup G₀)
    (hK : K ≤ eNorm basis_duad) (hperf : ⁅K, K⁆ = K) : K ≤ Mduad := by
  set KP := K.map NativeSporadic.M23.subtype with hKP
  have hKN : KP ≤ Subgroup.normalizer ((eSub (basis_duad.map
      (f := NativeSporadic.M23.subtype) Subtype.val_injective) : Subgroup _) :
        Set (Equiv.Perm (Fin 23))) := by
    rintro _ ⟨k, hk, rfl⟩
    exact coe_mem_eNorm basis_duad (hK hk)
  have hKperf : ⁅KP, KP⁆ = KP := by rw [hKP, ← Subgroup.map_commutator, hperf]
  have hfix := fixes_of_perfect hKN hKperf triSet card_triSet fun i => by
    rw [fix_duad_iff]
    simp [triSet]
  intro k hk
  rw [Mduad_eq]
  refine mem_nTri.mpr ⟨hK hk, fun i hi => hfix _ ⟨k, hk, rfl⟩ i ?_⟩
  simpa [triSet] using hi

theorem refData_duad :
    RefData (eSub basis_duad) Mduad where
  cent := cent_duad
  comm := fun a ha b hb => eSub_comm basis_duad a b ha hb
  le := vDuad_le_Mduad
  norm := Mduad_le_eNorm
  perf := perf_duad
  simple := by
    let φ := Duad.f4Hom basis_duad Mduad_le_f4Stab Mduad_det
    have hker : φ.ker = (eSub basis_duad).subgroupOf Mduad := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 : Duad.f4Rep basis_duad (Subgroup.inclusion Mduad_le_f4Stab x) = 1 :=
          congrArg Subtype.val h1
        exact cent_duad ((Duad.f4Rep_eq_one_iff basis_duad _).mp h2)
      · intro hx
        apply Subtype.ext
        refine (Duad.f4Rep_eq_one_iff basis_duad (Subgroup.inclusion Mduad_le_f4Stab x)).mpr ?_
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_duad _ _ hy hx
    have hsurj : Function.Surjective φ := by
      have h1 := card_range_eq vDuad_le_Mduad φ hker
      rw [card_eSub, card_Mduad] at h1
      have h2 : Nat.card φ.range = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 Duad.F4) := by
        rw [Duad.card_statedSL]; omega
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ h2
    have := Duad.isSimpleGroup_statedSL
    exact simple_of_surj φ hsurj hker

theorem conj_e8 {j : ℕ} (hj : j < 2) (i : Fin 3) :
    elt (eGenW.getD j []) * vE8 i * (elt (eGenW.getD j []))⁻¹ =
      eElt vE8 fun r => matOf 3 eMasks j r i :=
  conj_gen forall₂_e8 c_masks_e8 (by rw [eGenW_length]; exact hj)
    (by rw [eMasks_length]; exact hj) i

theorem Me_le_eNorm : Me ≤ eNorm basis_e8 :=
  genOf_le eGenW_length fun j hj => mem_eNorm basis_e8 (matOf 3 eMasks j) fun i => conj_e8 hj i

theorem card_eNorm_e8 :
    Nat.card (eNorm basis_e8) = 1344 := by
  have h := Subgroup.card_le_of_le Me_le_eNorm
  rw [card_Me] at h
  exact le_antisymm card_eNorm_e8_le h

theorem refData_e8 :
    RefData (eSub basis_e8) (eNorm basis_e8) where
  cent := cent_e8
  comm := fun a ha b hb => eSub_comm basis_e8 a b ha hb
  le := Subgroup.le_normalizer
  norm := le_rfl
  perf := fun _ hK _ => hK
  simple := by
    let φ := E8.e3Hom basis_e8 (X := eNorm basis_e8) le_rfl
    have hker : φ.ker = (eSub basis_e8).subgroupOf (eNorm basis_e8) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
      constructor
      · intro h; exact cent_e8 h
      · intro hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_e8 _ _ hy hx
    have hsurj : Function.Surjective φ := by
      have h1 := card_range_eq Subgroup.le_normalizer φ hker
      rw [card_eSub, card_eNorm_e8] at h1
      have h2 : Nat.card φ.range =
          Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
        rw [E8.card_statedSL3]; omega
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ h2
    have := E8.isSimpleGroup_statedSL3
    exact simple_of_surj φ hsurj hker

theorem s_le_w : eSub basis_s ≤ eSub basis_w := by
  rw [eSub_eq_closure basis_s, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := eq_eElt_of_coords hn23 forall₂_w forall₂_s c_s_in_w i
  have h3 : vS i = eElt vW c := by
    apply Subtype.ext
    rw [hc]
    exact (map_eElt (v := vW) NativeSporadic.M23.subtype c).symm
  rw [SetLike.mem_coe, h3]
  exact eElt_mem basis_w _

theorem centralizer_s_eq :
    Subgroup.centralizer (eSub basis_s : Set G₀) = eSub basis_w := by
  have hle : eSub basis_w ≤ Subgroup.centralizer (eSub basis_s : Set G₀) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_w _ _ (s_le_w hy) hx
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_cent_s, card_eSub]; norm_num)).symm

@[expose] def x5 : G₀ := elt w5
@[expose] def x7 : G₀ := elt w7
@[expose] def x11 : G₀ := elt w11
@[expose] def x23 : G₀ := elt w23

theorem orderOf_elt {w : List ℤ} {q : ℕ} (hq : 0 < q) (h : ordTest 23 q (wordT 23 gensT w) = true) :
    orderOf (elt w) = q := by
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful (rep_elt w) hq).1 h

theorem orderOf_x5 : orderOf x5 = 5 := orderOf_elt (by norm_num) c_ord5
theorem orderOf_x7 : orderOf x7 = 7 := orderOf_elt (by norm_num) c_ord7
theorem orderOf_x11 : orderOf x11 = 11 := orderOf_elt (by norm_num) c_ord11
theorem orderOf_x23 : orderOf x23 = 23 := orderOf_elt (by norm_num) c_ord23

theorem exists_powTab {x : G₀} {w : List ℤ} (hx : x = elt w) {q : ℕ} (hq : orderOf x = q)
    {y : G₀} (hy : y ∈ Subgroup.zpowers x) :
    ∃ e ∈ powTabs 23 (wordT 23 gensT w) q, Rep 23 e (y : Equiv.Perm (Fin 23)) := by
  subst hx
  have := exists_powTabs hn23 (H := NativeSporadic.M23) (rep_elt w) hy
  rwa [hq] at this

theorem exists_invTab {t : G₀} (ht : orderOf t = 2) :
    ∃ T ∈ invs, Rep 23 T (t : Equiv.Perm (Fin 23)) :=
  exists_orderTables hn23 m23Certificate validM23
    (by rw [m23Certificate_originalSubgroup]; exact t.2) (by rw [Subgroup.orderOf_coe]; exact ht)

theorem closure_ofFn_conj {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (c : G₀) :
    Subgroup.closure {x | x ∈ List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 23)) *
      ((v i : G₀) : Equiv.Perm (Fin 23)) * ((c : G₀) : Equiv.Perm (Fin 23))⁻¹} =
      ((eSub hv).map (MulAut.conj c).toMonoidHom).map NativeSporadic.M23.subtype := by
  rw [eSub_eq_closure, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_ofFn, MulAut.conj_apply]

theorem perm_facts {y t : G₀} {m : ℕ} (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < m, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (y : Equiv.Perm (Fin 23)) * t * (y : Equiv.Perm (Fin 23))⁻¹ ≠ t ∧
      ∀ j < m, (t : Equiv.Perm (Fin 23)) * ((y : Equiv.Perm (Fin 23)) ^ j * t *
        (y : Equiv.Perm (Fin 23))⁻¹ ^ j) =
        (y : Equiv.Perm (Fin 23)) ^ j * t * (y : Equiv.Perm (Fin 23))⁻¹ ^ j * t := by
  refine ⟨fun h => hmove (Subtype.ext (by simpa using h)), fun j hj => ?_⟩
  have := congrArg Subtype.val (hcomm j hj)
  simpa using this

@[expose] def cand (k : ℕ) : G₀ := elt (candW.getD k [])

theorem forall₂_cand {k : ℕ} (hk : k < 8) {l : ℕ} {v : Fin l → G₀}
    {bs : List Table} (hbs : List.Forall₂ (Rep 23) bs (List.ofFn fun i => ((v i : G₀) :
      Equiv.Perm (Fin 23)))) :
    List.Forall₂ (Rep 23) (conjAll (candT k) bs) (List.ofFn fun i =>
      ((cand k : G₀) : Equiv.Perm (Fin 23)) * ((v i : G₀) : Equiv.Perm (Fin 23)) *
        ((cand k : G₀) : Equiv.Perm (Fin 23))⁻¹) := by
  have hc : Rep 23 (candT k) ((cand k : G₀) : Equiv.Perm (Fin 23)) := rep_elt _
  have h := c_candInv
  rw [List.all_eq_true] at h
  have hci := Rep.inv_of_invOK hc (h k (List.mem_range.mpr hk))
  exact forall₂_conjTab hbs hc hci

theorem pow_eq_one_of_mem {x y : G₀} {q : ℕ} (hx : orderOf x = q) (hy : y ∈ Subgroup.zpowers x) :
    (y : Equiv.Perm (Fin 23)) ^ q = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← Subgroup.coe_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    zpow_natCast, ← hx, pow_orderOf_eq_one, _root_.one_zpow, Subgroup.coe_one]

theorem orbSub_cases5 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x5) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 5, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (∃ c : G₀, orbSub y t = (eSub basis_duad).map (MulAut.conj c).toMonoidHom) ∨
      ∃ c : G₀, orbSub y t = (eSub basis_w).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x5 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hcands : List.Forall₂ (List.Forall₂ (Rep 23)) cands5
      [List.ofFn fun i => ((cand 0 : G₀) : Equiv.Perm (Fin 23)) *
          ((vDuad i : G₀) : Equiv.Perm (Fin 23)) * ((cand 0 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 1 : G₀) : Equiv.Perm (Fin 23)) *
          ((vW i : G₀) : Equiv.Perm (Fin 23)) * ((cand 1 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 2 : G₀) : Equiv.Perm (Fin 23)) *
          ((vW i : G₀) : Equiv.Perm (Fin 23)) * ((cand 2 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 3 : G₀) : Equiv.Perm (Fin 23)) *
          ((vW i : G₀) : Equiv.Perm (Fin 23)) * ((cand 3 : G₀) : Equiv.Perm (Fin 23))⁻¹] :=
    .cons (forall₂_cand (by norm_num) forall₂_duad) (.cons (forall₂_cand (by norm_num) forall₂_w)
      (.cons (forall₂_cand (by norm_num) forall₂_w)
        (.cons (forall₂_cand (by norm_num) forall₂_w) .nil)))
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn23 c_orb5 hcands he hT hey hTt (by norm_num)
    (pow_eq_one_of_mem orderOf_x5 hy) hmove' hcomm'
  have hmap : (orbSub y t).map NativeSporadic.M23.subtype =
      orbSub (y : Equiv.Perm (Fin 23)) (t : Equiv.Perm (Fin 23)) := orbSub_map _ y t
  have hinj := Subgroup.map_injective (f := NativeSporadic.M23.subtype) Subtype.val_injective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  rcases hcg with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨cand 0, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_duad])⟩
  · exact Or.inr ⟨cand 1, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_w])⟩
  · exact Or.inr ⟨cand 2, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_w])⟩
  · exact Or.inr ⟨cand 3, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_w])⟩

theorem orbSub_cases7 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x7) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 7, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (∃ c : G₀, orbSub y t = (eSub basis_e8).map (MulAut.conj c).toMonoidHom) ∨
      (∃ c : G₀, orbSub y t = (eSub basis_w).map (MulAut.conj c).toMonoidHom) ∨
      ∃ c : G₀, orbSub y t = (eSub basis_s).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x7 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hcands : List.Forall₂ (List.Forall₂ (Rep 23)) cands7
      [List.ofFn fun i => ((cand 4 : G₀) : Equiv.Perm (Fin 23)) *
          ((vE8 i : G₀) : Equiv.Perm (Fin 23)) * ((cand 4 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 5 : G₀) : Equiv.Perm (Fin 23)) *
          ((vW i : G₀) : Equiv.Perm (Fin 23)) * ((cand 5 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 6 : G₀) : Equiv.Perm (Fin 23)) *
          ((vE8 i : G₀) : Equiv.Perm (Fin 23)) * ((cand 6 : G₀) : Equiv.Perm (Fin 23))⁻¹,
        List.ofFn fun i => ((cand 7 : G₀) : Equiv.Perm (Fin 23)) *
          ((vS i : G₀) : Equiv.Perm (Fin 23)) * ((cand 7 : G₀) : Equiv.Perm (Fin 23))⁻¹] :=
    .cons (forall₂_cand (by norm_num) forall₂_e8) (.cons (forall₂_cand (by norm_num) forall₂_w)
      (.cons (forall₂_cand (by norm_num) forall₂_e8)
        (.cons (forall₂_cand (by norm_num) forall₂_s) .nil)))
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn23 c_orb7 hcands he hT hey hTt (by norm_num)
    (pow_eq_one_of_mem orderOf_x7 hy) hmove' hcomm'
  have hmap : (orbSub y t).map NativeSporadic.M23.subtype =
      orbSub (y : Equiv.Perm (Fin 23)) (t : Equiv.Perm (Fin 23)) := orbSub_map _ y t
  have hinj := Subgroup.map_injective (f := NativeSporadic.M23.subtype) Subtype.val_injective
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  rcases hcg with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨cand 4, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_e8])⟩
  · exact Or.inr (Or.inl ⟨cand 5, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_w])⟩)
  · exact Or.inl ⟨cand 6, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_e8])⟩
  · exact Or.inr (Or.inr ⟨cand 7, hinj (by rw [hmap, hcl, closure_ofFn_conj basis_s])⟩)

theorem not_bad11 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x11) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 11, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) : False := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x11 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  exact false_of_actCheck hn23 c_act11 hT he hey hTt hmove' hcomm'

theorem not_bad23 {y t : G₀}
    (hy : y ∈ Subgroup.zpowers x23) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < 23, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) : False := by
  obtain ⟨e, he, hey⟩ := exists_powTab rfl orderOf_x23 hy
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  exact false_of_actCheck hn23 c_act23 hT he hey hTt hmove' hcomm'

end CFSG.Quasithin.KGC31.M23

end
