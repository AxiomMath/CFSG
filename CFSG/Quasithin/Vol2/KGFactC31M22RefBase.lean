
module

public import CFSG.Quasithin.Vol2.KGFactC31M22Data
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31Duad
public import CFSG.Sporadic.Schreier.M22Check

@[expose] public section

namespace CFSG.Quasithin.KGC31.M22

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31 Matrix _root_.Certificates

abbrev G₀ : Type := ↥NativeSporadic.M22

theorem hn22 : (22 : ℕ) < 2 ^ 32 := by norm_num

theorem hgens : ∀ l, gensG l ∈ NativeSporadic.M22 := fun l => by
  unfold gensG
  split_ifs
  · exact m22a.2
  · exact m22b.2

theorem hrep : ∀ l, Rep 22 (gensT l) (gensG l) := fun l => by
  unfold gensT gensG
  split_ifs
  · exact rep_toTable hn22 _
  · exact rep_toTable hn22 _

@[expose] def elt (w : List ℤ) : G₀ := ⟨wordG gensG w, wordG_mem_of _ hgens w⟩

theorem rep_elt (w : List ℤ) : Rep 22 (wordT 22 gensT w) ((elt w : G₀) : Equiv.Perm (Fin 22)) :=
  Rep.wordT hn22 w fun l _ => hrep l

theorem m22Certificate_original : m22Certificate.originalSubgroup = NativeSporadic.M22 := by
  rw [m22Certificate, certificate_originalSubgroup, m22_eq]
  congr 1
  ext g
  simp

@[expose] def basisOf (ws : List (List ℤ)) : Fin ws.length → G₀ := fun i => elt (ws.get i)

theorem forall₂_basisOf (ws : List (List ℤ)) :
    List.Forall₂ (Rep 22) (ws.map (wordT 22 gensT))
      (List.ofFn fun i => ((basisOf ws i : G₀) : Equiv.Perm (Fin 22))) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, basisOf]
  exact rep_elt _

theorem EBasis.of_map {Γ B : Type*} [Group Γ] [Group B] {n : ℕ} {v : Fin n → Γ} {f : Γ →* B}
    (hf : Function.Injective f) (h : EBasis fun i => f (v i)) : EBasis v where
  sq i := hf (by rw [map_mul, h.sq i, map_one])
  comm i j := hf (by rw [map_mul, map_mul]; exact (h.comm i j).eq)
  ne_one c hc := h.ne_one c (by rw [← map_eElt, hc, map_one])

@[expose] def vHex : Fin 4 → G₀ := basisOf hexW
@[expose] def vDuad : Fin 4 → G₀ := basisOf duadW
@[expose] def vE8 : Fin 3 → G₀ := basisOf e8W

theorem forall₂_hex : List.Forall₂ (Rep 22) hexT
    (List.ofFn fun i => ((vHex i : G₀) : Equiv.Perm (Fin 22))) := forall₂_basisOf hexW
theorem forall₂_duad : List.Forall₂ (Rep 22) duadT
    (List.ofFn fun i => ((vDuad i : G₀) : Equiv.Perm (Fin 22))) := forall₂_basisOf duadW
theorem forall₂_e8 : List.Forall₂ (Rep 22) e8T
    (List.ofFn fun i => ((vE8 i : G₀) : Equiv.Perm (Fin 22))) := forall₂_basisOf e8W

theorem all_iff_of_forall₂ {k : ℕ} {v : Fin k → Equiv.Perm (Fin 22)} {bs : List Table}
    (h : List.Forall₂ (Rep 22) bs (List.ofFn v)) {f : Table → Bool}
    {Q : Equiv.Perm (Fin 22) → Prop} (hfQ : ∀ b g, Rep 22 b g → (f b = true ↔ Q g)) :
    bs.all f = true ↔ ∀ i, Q (v i) := by
  rw [List.all_eq_true]
  constructor
  · intro hall i
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem h (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (hfQ b _ hbi).mp (hall b hb)
  · intro hall b hb
    obtain ⟨g, hg, hbg⟩ := exists_rep_of_mem h hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact (hfQ b _ hbg).mpr (hall i)

theorem mem_eNorm_iff {Γ : Type*} [Group Γ] [Finite Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (x : Γ) : x ∈ eNorm hv ↔ ∀ i, ∃ c, x * v i * x⁻¹ = eElt v c := by
  constructor
  · intro hx i
    obtain ⟨c, hc⟩ := (mem_eSub_iff hv _).mp
      ((Subgroup.mem_normalizer_iff.mp hx _).mp (mem_eSub hv i))
    exact ⟨c, hc.symm⟩
  · intro h
    choose cs hcs using h
    exact mem_eNorm hv (Matrix.of fun r i => cs i r) fun i => by rw [hcs i]; rfl

theorem validM22 : ValidSchreier m22Certificate := m22Certificate_check

theorem card_m22_eq {f : Table → Bool} {P : Equiv.Perm (Fin 22) → Prop}
    [DecidablePred P] (hfP : ∀ T g, Rep 22 T g → (f T = true ↔ P g)) :
    Nat.card {x : G₀ // P x} = countProducts 22 f (levelTables m22Certificate) (idT 22) := by
  have h := card_subtype_eq_countProducts hn22 m22Certificate validM22 hfP
  rw [m22Certificate_original] at h
  exact h

theorem card_centralizer_eq {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    {bs : List Table} (hbs : List.Forall₂ (Rep 22) bs (List.ofFn fun i => ((v i : G₀) :
      Equiv.Perm (Fin 22)))) {N : ℕ}
    (h : countProducts 22 (commAll 22 bs) (levelTables m22Certificate) (idT 22) = N) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = N := by
  classical
  rw [← h, ← card_m22_eq (P := fun g => ∀ i, g * ((v i : G₀) : Equiv.Perm (Fin 22)) =
    ((v i : G₀) : Equiv.Perm (Fin 22)) * g)]
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

theorem card_normalizer_eq {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    {bs : List Table} (hbs : List.Forall₂ (Rep 22) bs (List.ofFn fun i => ((v i : G₀) :
      Equiv.Perm (Fin 22)))) {N : ℕ}
    (h : countProducts 22 (normAll 22 bs) (levelTables m22Certificate) (idT 22) = N) :
    Nat.card (eNorm hv) = N := by
  classical
  have hvP : EBasis fun i => ((v i : G₀) : Equiv.Perm (Fin 22)) :=
    hv.map (f := NativeSporadic.M22.subtype) Subtype.val_injective
  rw [← h, ← card_m22_eq (P := fun g => g ∈ eNorm hvP)]
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [mem_eNorm_iff hv, mem_eNorm_iff hvP]
    refine forall_congr' fun i => exists_congr fun c => ?_
    have hE : eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 22))) c =
        ((eElt v c : G₀) : Equiv.Perm (Fin 22)) := (map_eElt NativeSporadic.M22.subtype c).symm
    rw [hE]
    constructor
    · intro h1; rw [← h1]; rfl
    · intro h1; exact Subtype.ext h1
  · intro T g hT
    exact normAll_iff hn22 hvP hbs hT

@[expose] def genOf (ws : List (List ℤ)) : Subgroup G₀ := Subgroup.closure {x | ∃ w ∈ ws, elt w = x}

theorem map_genOf (ws : List (List ℤ)) :
    (genOf ws).map NativeSporadic.M22.subtype =
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

theorem card_genOf {ws : List (List ℤ)} {Q : RawSchreierDatum 22}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ ws.map fun w => tab (wordG gensG w)})
    (hv : ValidSchreier Q) : Nat.card (genOf ws) = Q.orderCertificate := by
  rw [Q.orderCertificate_eq_card hv, hQ, ← map_genOf,
    Subgroup.card_map_of_injective Subtype.val_injective]

@[expose] def Mhex : Subgroup G₀ := genOf hexGenW
@[expose] def Mduad : Subgroup G₀ := genOf duadGenW

@[expose] def matOf (masks : List (List ℕ)) (j : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun r i => maskVec 4 ((masks.getD j []).getD i 0) r

theorem conj_gen {ws : List (List ℤ)} {masks : List (List ℕ)} {v : Fin 4 → G₀}
    {bs : List Table} (hbs : List.Forall₂ (Rep 22) bs (List.ofFn fun i => ((v i : G₀) :
      Equiv.Perm (Fin 22))))
    (h : ((ws.map fun w => tab (wordG gensG w)).zip masks).all
      (fun p => masksOK 22 bs (toTable p.1) p.2) = true) {j : ℕ} (hj : j < ws.length)
    (hjm : j < masks.length) (i : Fin 4) :
    elt (ws.getD j []) * v i * (elt (ws.getD j []))⁻¹ = eElt v fun r => matOf masks j r i := by
  have hmem : ((ws.map fun w => tab (wordG gensG w))[j]'(by simpa using hj), masks[j]) ∈
      (ws.map fun w => tab (wordG gensG w)).zip masks := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by rw [List.length_zip, List.length_map]; omega, by simp⟩
  have h1 := List.all_eq_true.mp h _ hmem
  simp only [List.getElem_map, tab_eq] at h1
  have hT : Rep 22 (toTable (wordG gensG ws[j])) (wordG gensG ws[j]) := rep_toTable hn22 _
  have h2 := conj_of_masksOK hn22 hbs hT h1 i
  apply Subtype.ext
  rw [List.getD_eq_getElem _ _ hj]
  show wordG gensG ws[j] * ((v i : G₀) : Equiv.Perm (Fin 22)) * (wordG gensG ws[j])⁻¹ = _
  rw [h2]
  have hE : eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 22))) (fun r => matOf masks j r i) =
      ((eElt v fun r => matOf masks j r i : G₀) : Equiv.Perm (Fin 22)) :=
    (map_eElt NativeSporadic.M22.subtype _).symm
  rw [← hE]
  congr 1
  funext r
  simp [matOf, List.getElem?_eq_getElem hjm]

theorem centralizer_le_of_card {Γ : Type*} [Group Γ] [Finite Γ] {n : ℕ} {v : Fin n → Γ}
    (hv : EBasis v) (h : Nat.card (Subgroup.centralizer (eSub hv : Set Γ)) = 2 ^ n) :
    Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv := by
  have hle : eSub hv ≤ Subgroup.centralizer (eSub hv : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv _ _ hy hx
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, card_eSub])).symm.le

theorem simple_of_surj {Γ : Type} [Group Γ] {U L : Subgroup Γ} {H : Type*} [Group H]
    [IsSimpleGroup H] (φ : ↥L →* H) (hφ : Function.Surjective φ) (hker : φ.ker = U.subgroupOf L) :
    ∀ K : Subgroup Γ, U ≤ K → K ≤ L → L ≤ Subgroup.normalizer (K : Set Γ) → K = U ∨ K = L := by
  have hn : (U.subgroupOf L).Normal := hker ▸ φ.normal_ker
  have hs : IsSimpleGroup (↥L ⧸ U.subgroupOf L) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).isSimpleGroup
  exact forall_eq_of_simple hs

theorem card_range_eq {Γ : Type*} [Group Γ] {U L : Subgroup Γ} (hUL : U ≤ L) {H : Type*} [Group H]
    (φ : ↥L →* H) (hker : φ.ker = U.subgroupOf L) :
    Nat.card φ.range * Nat.card U = Nat.card L := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv] at h1
  exact h1.symm

theorem hexGenW_length : hexGenW.length = 2 := rfl
theorem hexMasks_length : hexMasks.length = 2 := rfl
theorem duadGenW_length : duadGenW.length = 2 := rfl
theorem duadMasks_length : duadMasks.length = 2 := rfl

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

theorem hexMat_perm : ∀ j < 2, ∀ i : Fin 6, ∃ k : Fin 6,
    (Hex.ovoid i).image (matOf hexMasks j *ᵥ ·) = Hex.ovoid k := by decide

theorem duadMat_comm : ∀ j < 2, matOf duadMasks j * Duad.Om = Duad.Om * matOf duadMasks j := by
  decide

theorem duadMat_det : ∀ j < 2, (Duad.f4Mat (matOf duadMasks j)).det = 1 := by decide

@[expose] def x5 : G₀ := elt w5
@[expose] def x7 : G₀ := elt w7
@[expose] def x11 : G₀ := elt w11
@[expose] def cHex : G₀ := elt hexConjW

theorem orderOf_elt {w : List ℤ} {q : ℕ} (hq : 0 < q) (h : ordTest 22 q (wordT 22 gensT w) = true) :
    orderOf (elt w) = q := by
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful (rep_elt w) hq).1 h

theorem exists_powTab {x : G₀} {w : List ℤ} (hx : x = elt w) {q : ℕ} (hq : orderOf x = q)
    {y : G₀} (hy : y ∈ Subgroup.zpowers x) :
    ∃ e ∈ powTabs 22 (wordT 22 gensT w) q, Rep 22 e (y : Equiv.Perm (Fin 22)) := by
  subst hx
  have := exists_powTabs hn22 (H := NativeSporadic.M22) (rep_elt w) hy
  rwa [hq] at this

theorem exists_invTab {t : G₀} (ht : orderOf t = 2) :
    ∃ T ∈ orderTables m22Certificate 2, Rep 22 T (t : Equiv.Perm (Fin 22)) :=
  exists_orderTables hn22 m22Certificate validM22 (by rw [m22Certificate_original]; exact t.2)
    (by rw [Subgroup.orderOf_coe]; exact ht)

theorem closure_ofFn {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    Subgroup.closure {x | x ∈ List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 22))} =
      (eSub hv).map NativeSporadic.M22.subtype := by
  rw [eSub_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_ofFn]

theorem closure_ofFn_conj {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (c : G₀) :
    Subgroup.closure {x | x ∈ List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 22)) *
      ((v i : G₀) : Equiv.Perm (Fin 22)) * ((c : G₀) : Equiv.Perm (Fin 22))⁻¹} =
      ((eSub hv).map (MulAut.conj c).toMonoidHom).map NativeSporadic.M22.subtype := by
  rw [eSub_eq_closure, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_ofFn, MulAut.conj_apply]

theorem perm_facts {y t : G₀} {m : ℕ} (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < m, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (y : Equiv.Perm (Fin 22)) * t * (y : Equiv.Perm (Fin 22))⁻¹ ≠ t ∧
      ∀ j < m, (t : Equiv.Perm (Fin 22)) * ((y : Equiv.Perm (Fin 22)) ^ j * t *
        (y : Equiv.Perm (Fin 22))⁻¹ ^ j) =
        (y : Equiv.Perm (Fin 22)) ^ j * t * (y : Equiv.Perm (Fin 22))⁻¹ ^ j * t := by
  refine ⟨fun h => hmove (Subtype.ext (by simpa using h)), fun j hj => ?_⟩
  have := congrArg Subtype.val (hcomm j hj)
  simpa using this

end CFSG.Quasithin.KGC31.M22

end
