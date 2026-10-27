module

public import CFSG.Quasithin.Vol2.KGFactC31HSCount
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.RankThree.Native Matrix

@[expose] noncomputable def basisOf (ws : List (List ℤ)) :
    Fin ws.length → G₀ := fun i => elt (ws.get i)

theorem forall₂_basisOf (ws : List (List ℤ)) :
    List.Forall₂ (Rep 100) (tabsOf ws)
      (List.ofFn fun i => ((basisOf ws i : G₀) : Equiv.Perm (Fin 100))) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [tabsOf], fun i h₁ h₂ => ?_⟩
  simp only [tabsOf, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, basisOf]
  exact rep_elt _

theorem getD_tabsOf (ws : List (List ℤ)) (i : ℕ) :
    (tabsOf ws).getD i (idT 100) = wordT 100 gensT (ws.getD i []) := by
  unfold tabsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases ws[i]? <;> rfl

theorem rep_getD_tabsOf (ws : List (List ℤ)) (i : ℕ) :
    Rep 100 ((tabsOf ws).getD i (idT 100)) ((elt (ws.getD i []) : G₀) : Equiv.Perm (Fin 100)) := by
  rw [getD_tabsOf]
  exact rep_elt _

theorem basisOf_eq (ws : List (List ℤ)) (i : Fin ws.length) :
    basisOf ws i = elt (ws.getD i []) := by
  rw [basisOf, List.getD_eq_getElem _ _ i.2, List.get_eq_getElem]

@[expose] noncomputable def vU16 : Fin 4 → G₀ := basisOf u16W

@[expose] noncomputable def vU8 : Fin 3 → G₀ := basisOf u8W

theorem forall₂_u16 :
    List.Forall₂ (Rep 100) u16T (List.ofFn fun i => ((vU16 i : G₀) : Equiv.Perm (Fin 100))) :=
  forall₂_basisOf u16W

theorem forall₂_u8 :
    List.Forall₂ (Rep 100) u8T (List.ofFn fun i => ((vU8 i : G₀) : Equiv.Perm (Fin 100))) :=
  forall₂_basisOf u8W

theorem basis_u16 : EBasis vU16 :=
  EBasis.of_map (f := hs100P.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn100 forall₂_u16 c_eb16)

theorem basis_u8 : EBasis vU8 :=
  EBasis.of_map (f := hs100P.subtype) Subtype.val_injective
    (ebasis_of_ebasisOK hn100 forall₂_u8 c_eb8)

theorem vU16_zero :
    ((vU16 0 : G₀) : Equiv.Perm (Fin 100)) = permA := b0_eq

theorem vU8_zero :
    ((vU8 0 : G₀) : Equiv.Perm (Fin 100)) = permA := b0_eq

theorem card_centralizer_eq_cb
    {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 100) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 100))))
    (i₀ : Fin k) (hi₀ : ((v i₀ : G₀) : Equiv.Perm (Fin 100)) = permA) {N : ℕ}
    (h : cbT.countP (commAll 100 bs) = N) :
    Nat.card (Subgroup.centralizer (eSub hv : Set G₀)) = N := by
  classical
  rw [← h, ← card_eq_countP_cbT (P := fun g => ∀ i, g * ((v i : G₀) : Equiv.Perm (Fin 100)) =
    ((v i : G₀) : Equiv.Perm (Fin 100)) * g)]
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

theorem cent_u16 :
    Subgroup.centralizer (eSub basis_u16 : Set G₀) ≤ eSub basis_u16 :=
  centralizer_le_of_card basis_u16 (card_centralizer_eq_cb basis_u16 forall₂_u16 0 vU16_zero
    c_cent16)

theorem card_cent_u8 :
    Nat.card (Subgroup.centralizer (eSub basis_u8 : Set G₀)) = 64 :=
  card_centralizer_eq_cb basis_u8 forall₂_u8 0 vU8_zero c_cent8

theorem forall₂_tabsOf (ws : List (List ℤ)) :
    List.Forall₂ (Rep 100) (tabsOf ws) (ws.map fun w => ((elt w : G₀) : Equiv.Perm (Fin 100))) := by
  unfold tabsOf
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (rep_elt w) ih

theorem card_le_of_cosetOK {k : ℕ}
    {v : Fin k → Equiv.Perm (Fin 100)} (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep 100) bs (List.ofFn v)) (i₀ : Fin k) (hi₀ : v i₀ = permA)
    {ws : List (List ℤ)} (hok : cosetOK 100 b0T bs (tabsOf ws) = true)
    {f : Table → Bool} {P : Equiv.Perm (Fin 100) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 100 T g → (f T = true ↔ P g)) (hPN : ∀ g, P g → g ∈ eNorm hv) :
    Nat.card {g : hs100P // P g} ≤ cosetCount 100 cbT (tabsOf ws) f := by
  have hws := forall₂_tabsOf ws
  refine card_le_cosetCount hfP hws (fun r hr => ?_) fun g _ hgP => ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact (elt w).2
  · have hb0 : permA ∈ eSub hv := hi₀ ▸ mem_eSub hv i₀
    have hx : g * permA * g⁻¹ ∈ eSub hv :=
      (Subgroup.mem_normalizer_iff.mp (hPN g hgP) permA).mp hb0
    have hb1 : permA ≠ 1 := by
      intro h
      have h1 := hv.ne_one (Pi.single i₀ 1) (by rw [eElt_single, hi₀, h])
      have := congrFun h1 i₀
      simp at this
    have hx1 : g * permA * g⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc permA = g⁻¹ * (g * permA * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact exists_conj_of_cosetOK hn100 hv hbs rep_b0' hws hok hx hx1

theorem card_eNorm_eq {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    Nat.card (eNorm hv) = Nat.card {g : hs100P // (g : Equiv.Perm (Fin 100)) ∈
      eNorm (hv.map (f := hs100P.subtype) Subtype.val_injective)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [mem_eNorm_iff hv, mem_eNorm_iff]
  refine forall_congr' fun i => exists_congr fun c => ?_
  have hE : eElt (fun i => hs100P.subtype (v i)) c =
      ((eElt v c : G₀) : Equiv.Perm (Fin 100)) := (map_eElt hs100P.subtype c).symm
  rw [hE]
  constructor
  · intro h1; rw [← h1]; rfl
  · intro h1; exact Subtype.ext h1

theorem card_eNorm_u16_le :
    Nat.card (eNorm basis_u16) ≤ 11520 := by
  classical
  have hvP := basis_u16.map (f := hs100P.subtype) Subtype.val_injective
  rw [card_eNorm_eq, ← c_ccount16]
  exact card_le_of_cosetOK hvP forall₂_u16 0 vU16_zero c_coset16 (P := fun g => g ∈ eNorm hvP)
    (fun T g hT => normAll_iff hn100 hvP forall₂_u16 hT) fun _ h => h

theorem card_eNorm_u8_le :
    Nat.card (eNorm basis_u8) ≤ 10752 := by
  classical
  have hvP := basis_u8.map (f := hs100P.subtype) Subtype.val_injective
  rw [card_eNorm_eq, ← c_ccount8]
  exact card_le_of_cosetOK hvP forall₂_u8 0 vU8_zero c_coset8 (P := fun g => g ∈ eNorm hvP)
    (fun T g hT => normAll_iff hn100 hvP forall₂_u8 hT) fun _ h => h

theorem genOf_le {ws : List (List ℤ)} {K : Subgroup G₀}
    (h : ∀ j < ws.length, elt (ws.getD j []) ∈ K) : genOf ws ≤ K := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
  have := h j hj
  rwa [List.getD_eq_getElem _ _ hj] at this

@[expose] def matOf (k : ℕ) (masks : List (List ℕ)) (j : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun r i => maskVec k ((masks.getD j []).getD i 0) r

theorem conj_gen {k : ℕ} {ws : List (List ℤ)}
    {masks : List (List ℕ)} {v : Fin k → G₀} {bs : List Table}
    (hbs : List.Forall₂ (Rep 100) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 100))))
    (h : ((permsOf ws).zip masks).all (fun p => masksOK 100 bs (toTable p.1) p.2) = true)
    {j : ℕ} (hj : j < ws.length) (hjm : j < masks.length) (i : Fin k) :
    elt (ws.getD j []) * v i * (elt (ws.getD j []))⁻¹ = eElt v fun r => matOf k masks j r i := by
  have hmem : ((permsOf ws)[j]'(by simpa [permsOf] using hj), masks[j]) ∈
      (permsOf ws).zip masks := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by rw [List.length_zip, permsOf, List.length_map]; omega, by simp⟩
  have h1 := List.all_eq_true.mp h _ hmem
  simp only [permsOf, List.getElem_map, tab_eq] at h1
  have hT : Rep 100 (toTable (wordG gensG ws[j])) (wordG gensG ws[j]) := rep_toTable hn100 _
  have h2 := conj_of_masksOK hn100 hbs hT h1 i
  apply Subtype.ext
  rw [List.getD_eq_getElem _ _ hj]
  show wordG gensG ws[j] * ((v i : G₀) : Equiv.Perm (Fin 100)) * (wordG gensG ws[j])⁻¹ = _
  rw [h2]
  have hE : eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 100))) (fun r => matOf k masks j r i) =
      ((eElt v fun r => matOf k masks j r i : G₀) : Equiv.Perm (Fin 100)) :=
    (map_eElt hs100P.subtype _).symm
  rw [← hE]
  congr 1
  funext r
  simp [matOf, List.getElem?_eq_getElem hjm]

@[expose] noncomputable def M16 : Subgroup G₀ := genOf m16GenW

theorem m16GenW_length : m16GenW.length = 2 := rfl
theorem m16Masks_length : m16Masks.length = 2 := rfl

theorem card_M16 :
    Nat.card M16 = 5760 := by
  rw [M16, card_genOf (Q := m16Chain) (certificate_originalSubgroup _ _ _ _ _) c_m16Check,
    c_m16Order]

theorem conj_m16 {j : ℕ}
    (hj : j < 2) (i : Fin 4) :
    elt (m16GenW.getD j []) * vU16 i * (elt (m16GenW.getD j []))⁻¹ =
      eElt vU16 fun r => matOf 4 m16Masks j r i :=
  conj_gen forall₂_u16 c_masks16 (by rw [m16GenW_length]; exact hj)
    (by rw [m16Masks_length]; exact hj) i

theorem m16Mat_perm : ∀ j < 2, ∀ i : Fin 6, ∃ k : Fin 6,
    (Hex.ovoid i).image (matOf 4 m16Masks j *ᵥ ·) = Hex.ovoid k := by decide

theorem m16Gen_norm {j : ℕ}
    (hj : j < 2) : elt (m16GenW.getD j []) ∈ eNorm basis_u16 :=
  mem_eNorm basis_u16 (matOf 4 m16Masks j) fun i => conj_m16 hj i

theorem m16Gen_eMat {j : ℕ}
    (hj : j < 2) :
    eMat basis_u16 ⟨elt (m16GenW.getD j []), m16Gen_norm hj⟩ = matOf 4 m16Masks j :=
  eMat_eq basis_u16 _ _ fun i => conj_m16 hj i

theorem M16_le_ovStab :
    M16 ≤ Hex.ovStab basis_u16 :=
  genOf_le fun j hj => by
    have hj2 : j < 2 := by rw [m16GenW_length] at hj; exact hj
    exact ⟨m16Gen_norm hj2, fun i => by
      rw [Hex.ovImg, m16Gen_eMat hj2]
      exact m16Mat_perm j hj2 i⟩

theorem M16_le_eNorm :
    M16 ≤ eNorm basis_u16 :=
  fun _ hx => (M16_le_ovStab hx).1

theorem evalCodes_mem (ws : List (List ℤ)) :
    ∀ w : List ℤ, ∃ x ∈ genOf ws, (x : Equiv.Perm (Fin 100)) = evalCodes (permsOf ws) w := by
  intro w
  induction w with
  | nil => exact ⟨1, (genOf ws).one_mem, rfl⟩
  | cons z w ih =>
    obtain ⟨x, hx, hxe⟩ := ih
    have hgen : ∀ m : ℕ, ∃ y ∈ genOf ws,
        (y : Equiv.Perm (Fin 100)) = (permsOf ws).getD m 1 := by
      intro m
      by_cases hm : m < ws.length
      · refine ⟨elt (ws.get ⟨m, hm⟩), elt_mem_genOf (List.get_mem _ _), ?_⟩
        rw [List.getD_eq_getElem _ _ (by simpa [permsOf] using hm)]
        simp [permsOf, coe_elt, tab_eq]
      · refine ⟨1, (genOf ws).one_mem, ?_⟩
        rw [List.getD_eq_default _ _ (by simp [permsOf]; omega)]
        rfl
    by_cases hz : 0 < z
    · obtain ⟨y, hy, hye⟩ := hgen (z.toNat - 1)
      refine ⟨y * x, (genOf ws).mul_mem hy hx, ?_⟩
      rw [evalCodes, ite_eq_left hz, Subgroup.coe_mul, hye, hxe]
    · obtain ⟨y, hy, hye⟩ := hgen ((-z).toNat - 1)
      refine ⟨y⁻¹ * x, (genOf ws).mul_mem ((genOf ws).inv_mem hy) hx, ?_⟩
      rw [evalCodes, ite_eq_right hz, Subgroup.coe_mul, Subgroup.coe_inv, hye, hxe]

theorem u16_le_M16 :
    eSub basis_u16 ≤ M16 := by
  rw [eSub_eq_closure basis_u16, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have h1 := List.all_eq_true.mp c_u16InM16 i (List.mem_range.mpr i.2)
  obtain ⟨x, hx, hxe⟩ := evalCodes_mem m16GenW (u16InM16.getD i [])
  have hrep : Rep 100 (u16T.getD i (idT 100)) ((vU16 i : G₀) : Equiv.Perm (Fin 100)) := by
    have := rep_getD_tabsOf u16W i
    rwa [← basisOf_eq u16W i] at this
  have heq := (tblEq_iff_eq hrep (rep_toTable hn100 _)).mp h1
  have hxv : x = vU16 i := Subtype.ext (hxe.trans heq.symm)
  rw [SetLike.mem_coe, ← hxv]
  exact hx

theorem refData_u16 :
    RefData (eSub basis_u16) M16 where
  cent := cent_u16
  comm := fun a ha b hb => eSub_comm basis_u16 a b ha hb
  le := u16_le_M16
  norm := M16_le_eNorm
  perf := perf_of_card M16_le_eNorm (by
    have := card_eNorm_u16_le
    rw [card_M16]
    omega)
  simple := by
    obtain ⟨α, hα, hker, -⟩ := Hex.exists_ovAlt basis_u16 M16_le_ovStab u16_le_M16
      (inf_le_right.trans cent_u16) (by rw [card_M16])
    have := Hex.alt6_simple
    exact simple_of_surj α hα hker

end CFSG.Quasithin.KGC31.HS

end
