module

public import CFSG.Sporadic.Schreier.LySevenProof
public import CFSG.RankThree.PartOne.KS.LyFiveGeneric
public import Certificates.Data.CFSGNative.LyFive.Conj

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
  CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

theorem conjTree_parts' {root : Array ℕ} {gens : Array (Array ℕ × Array ℕ)}
    {T : Array (Array ℕ) × Array ℕ × Array ℕ} (h : conjTreeOK root gens T = true) :
    T.1[0]! = root ∧ (∀ X ∈ T.1, X.size = 49 ∧ ∀ x ∈ X, x < 5) ∧
    (∀ k, 1 ≤ k → k < T.1.size → T.2.1[k]! < k ∧ T.2.2[k]! < gens.size ∧
      mul7 (mul7 gens[T.2.2[k]!]!.1 T.1[T.2.1[k]!]!) gens[T.2.2[k]!]!.2 = T.1[k]!) ∧
    (∀ k < T.1.size, ∀ k' < T.1.size, T.1[k]! = T.1[k']! → k = k') := by
  unfold conjTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h0⟩, hred⟩, htree⟩, hidx⟩ := h
  refine ⟨h0, fun v hv => ?_, fun k hk1 hk2 => ?_, fun k hk k' hk' he => ?_⟩
  · rw [Array.all_eq_true'] at hred
    have := hred v hv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · have := (allIn_eq_true.1 htree) k hk1 hk2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have e1 := (allIn_eq_true.1 hidx) k (Nat.zero_le _) hk
    have e2 := (allIn_eq_true.1 hidx) k' (Nat.zero_le _) hk'
    simp only [beq_iff_eq] at e1 e2
    rw [← e1, ← e2, he]

theorem conj_witness'
    {t : J} (ht : t ∈ stabU) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) :
    ∀ k < T.1.size, ∃ h ∈ lyH, mat7 (T.1[k]!) = restr7 (h * t * h⁻¹) := by
  obtain ⟨h0, -, hstep, -⟩ := conjTree_parts' hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨1, lyH.one_mem, ?_⟩
      rw [h0, hroot]
      simp
    · obtain ⟨hp, hl, he⟩ := hstep k hpos hk
      rw [hGenPairs_size] at hl
      obtain ⟨h, hH, hhm⟩ := ih _ hp (by omega)
      obtain ⟨m1, m2⟩ := mat7_hGenPair hl
      refine ⟨aStar (T.2.2[k]! + 2) * h, lyH.mul_mem (aStar_mem_lyH (by omega)) hH, ?_⟩
      rw [← he, mat7_mul7, mat7_mul7, m1, m2, hhm]
      have hS1 := aStar_mem_stabU (j := T.2.2[k]! + 2) (by omega) (by omega)
      have hS2 : h * t * h⁻¹ ∈ stabU :=
        stabU.mul_mem (stabU.mul_mem (lyH_le_stabU hH) ht) (stabU.inv_mem (lyH_le_stabU hH))
      have e1 := rho7.map_mul ⟨_, hS1⟩ ⟨_, hS2⟩
      have e2 := rho7.map_mul (⟨_, hS1⟩ * ⟨_, hS2⟩) ⟨_, stabU.inv_mem hS1⟩
      simp only [rho7_apply] at e1 e2
      rw [← e1, ← e2]
      refine congrArg restr7 ?_
      simp only [Subgroup.coe_mul]
      group

theorem card_conj_class_ge'
    {t : J} (ht : t ∈ lyH) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) :
    T.1.size ≤ Nat.card (MulAction.orbit (ConjAct lyH) (⟨t, ht⟩ : lyH)) := by
  obtain ⟨-, hred, -, hidx⟩ := conjTree_parts' hT
  have hw := conj_witness' (lyH_le_stabU ht) hroot hT
  choose! hk hkH hkm using hw
  let φ : Fin T.1.size → MulAction.orbit (ConjAct lyH) (⟨t, ht⟩ : lyH) := fun k =>
    ⟨⟨hk k * t * (hk k)⁻¹, lyH.mul_mem (lyH.mul_mem (hkH k k.2) ht) (lyH.inv_mem (hkH k k.2))⟩,
      ⟨ConjAct.toConjAct ⟨hk k, hkH k k.2⟩, by
        apply Subtype.ext
        simp [ConjAct.smul_def]⟩⟩
  have hφ : Function.Injective φ := by
    intro k k' h
    have e := congrArg (fun x => restr7 ((x : lyH) : J)) (congrArg Subtype.val h)
    simp only [φ] at e
    rw [← hkm k k.2, ← hkm k' k'.2] at e
    apply Fin.ext
    apply hidx k k.2 k' k'.2
    apply mat7_inj _ _ e
    · rw [getElem!_pos T.1 k.val k.2]; exact hred _ (Array.getElem_mem k.2)
    · rw [getElem!_pos T.1 k'.val k'.2]; exact hred _ (Array.getElem_mem k'.2)
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this

theorem card_centralizer_lyH_le
    {t : J} (ht : t ∈ lyH) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) {N : ℕ} (hN : N ≤ T.1.size) :
    Nat.card (Subgroup.centralizer ({t} : Set J) ⊓ lyH : Subgroup J) * N ≤ 5859000000 := by
  have hc := card_conj_class_ge' ht hroot hT
  have h1 := card_centralizer_mul_le (⟨t, ht⟩ : lyH) (hN.trans hc)
  rw [← card_centralizer_inf_eq lyH t ht] at h1
  have hcard : Nat.card lyH = 5859000000 := seven_space_centralizer_bound.2.1
  rwa [hcard] at h1

theorem foldl_insert_contains (pts : Array (Array ℕ)) (n : ℕ) (y : Array ℕ) :
    ((List.range n).foldl (fun m k => m.insert pts[k]! k)
      (∅ : Std.HashMap (Array ℕ) ℕ)).contains y = true → ∃ k < n, pts[k]! = y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Std.HashMap.contains_insert, Bool.or_eq_true,
      beq_iff_eq]
    rintro (h | h)
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨k, hk, hy⟩ := ih h
      exact ⟨k, Nat.lt_succ_of_lt hk, hy⟩

theorem conjClosedOK_spec {gens : Array (Array ℕ × Array ℕ)}
    {T : Array (Array ℕ) × Array ℕ × Array ℕ} (h : conjClosedOK gens T = true) :
    ∀ k < T.1.size, ∀ j < gens.size, ∃ k' < T.1.size,
      T.1[k']! = mul7 (mul7 gens[j]!.1 T.1[k]!) gens[j]!.2 := by
  intro k hk j hj
  unfold conjClosedOK at h
  have h1 := (allIn_eq_true.1 h) k (Nat.zero_le _) hk
  rw [Array.all_eq_true'] at h1
  have h2 := h1 gens[j]! (by rw [getElem!_pos gens j hj]; exact Array.getElem_mem hj)
  exact foldl_insert_contains T.1 T.1.size _ h2

theorem restr7_mul {a b : J}
    (ha : a ∈ stabU) (hb : b ∈ stabU) : restr7 (a * b) = restr7 a * restr7 b :=
  rho7.map_mul ⟨a, ha⟩ ⟨b, hb⟩

theorem restr7_eq_one_imp
    {g : J} (hg : g ∈ lyH) (h1 : restr7 g = 1) : g = 1 := by
  obtain ⟨-, -, -, hinj, -⟩ := (seven_space_centralizer_bound : _)
  apply hinj g hg
  intro v hv
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mem_stabU.1 (lyH_le_stabU hg),
    ← Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem restr7_inj_lyH
    {u u' : J} (hu : u ∈ lyH) (hu' : u' ∈ lyH)
    (h : restr7 u = restr7 u') : u = u' := by
  have hS := lyH_le_stabU hu
  have hS' := lyH_le_stabU hu'
  have hinv : u'⁻¹ ∈ lyH := lyH.inv_mem hu'
  have hm : u'⁻¹ * u ∈ lyH := lyH.mul_mem hinv hu
  have hr : restr7 (u'⁻¹ * u) = 1 := by
    have e1 : restr7 (u'⁻¹ * u) = restr7 u'⁻¹ * restr7 u := restr7_mul (lyH_le_stabU hinv) hS
    have e2 : restr7 (u'⁻¹ * u') = restr7 u'⁻¹ * restr7 u' := restr7_mul (lyH_le_stabU hinv) hS'
    rw [e1, h, ← e2, inv_mul_cancel, restr7_one]
  have := restr7_eq_one_imp hm hr
  exact (inv_mul_eq_one.mp this).symm

theorem mem_tree_conj
    {t : J} (ht : t ∈ lyH) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) (hpos : 0 < T.1.size)
    (hcl : conjClosedOK (hGenPairs asArr) T = true) :
    ∀ h ∈ lyH, ∃ k < T.1.size, mat7 (T.1[k]!) = restr7 (h * t * h⁻¹) := by
  obtain ⟨h0, -, -, -⟩ := conjTree_parts' hT
  have hspec := conjClosedOK_spec hcl
  have key : ∀ h ∈ lyH, ∀ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
      (∃ k < T.1.size, mat7 (T.1[k]!) = M) →
        ∃ k < T.1.size, mat7 (T.1[k]!) = restr7 h * M * restr7 h⁻¹ := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨j, ⟨hj2, hj6⟩, rfl⟩ := hg
      rintro M ⟨k, hk, rfl⟩
      have hj' : j - 2 < 5 := by omega
      obtain ⟨k', hk', hk'e⟩ := hspec k hk (j - 2) (by rw [hGenPairs_size]; exact hj')
      refine ⟨k', hk', ?_⟩
      obtain ⟨m1, m2⟩ := mat7_hGenPair hj'
      rw [hk'e, mat7_mul7, mat7_mul7, m1, m2, show j - 2 + 2 = j by omega]
    | one =>
      intro M hM
      rw [restr7_one, inv_one, restr7_one, Matrix.one_mul, Matrix.mul_one]
      exact hM
    | mul g1 g2 hg1 hg2 ih1 ih2 =>
      rintro M hM
      obtain ⟨k, hk, hke⟩ := ih2 M hM
      obtain ⟨k', hk', hk'e⟩ := ih1 _ ⟨k, hk, hke⟩
      refine ⟨k', hk', ?_⟩
      have hg1' : g1 ∈ lyH := hg1
      have hg2' : g2 ∈ lyH := hg2
      rw [hk'e, _root_.mul_inv_rev, restr7_mul (lyH_le_stabU hg1') (lyH_le_stabU hg2'),
        restr7_mul (lyH_le_stabU (lyH.inv_mem hg2')) (lyH_le_stabU (lyH.inv_mem hg1'))]
      simp only [Matrix.mul_assoc]
    | inv g hg ih =>
      have hg' : g ∈ lyH := hg
      have hpow : ∀ n : ℕ, ∀ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          (∃ k < T.1.size, mat7 (T.1[k]!) = M) →
            ∃ k < T.1.size, mat7 (T.1[k]!) = restr7 (g ^ n) * M * restr7 (g ^ n)⁻¹ := by
        intro n
        induction n with
        | zero =>
          intro M hM
          rw [pow_zero, restr7_one, inv_one, restr7_one, Matrix.one_mul, Matrix.mul_one]
          exact hM
        | succ n ihn =>
          intro M hM
          obtain ⟨k, hk, hke⟩ := ihn M hM
          obtain ⟨k', hk', hk'e⟩ := ih _ ⟨k, hk, hke⟩
          refine ⟨k', hk', ?_⟩
          rw [hk'e, pow_succ', _root_.mul_inv_rev,
            restr7_mul (lyH_le_stabU hg') (lyH_le_stabU (lyH.pow_mem hg' n)),
            restr7_mul (lyH_le_stabU (lyH.inv_mem (lyH.pow_mem hg' n))) (lyH_le_stabU (lyH.inv_mem hg'))]
          simp only [Matrix.mul_assoc]
      have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos g),
          pow_orderOf_eq_one]
      intro M hM
      have := hpow (orderOf g - 1) M hM
      rwa [← hinv, inv_inv] at this
  intro h hh
  obtain ⟨k, hk, hke⟩ := key h hh (mat7 root) ⟨0, hpos, by rw [h0]⟩
  refine ⟨k, hk, ?_⟩
  rw [hke, hroot, restr7_mul (lyH_le_stabU (lyH.mul_mem hh ht)) (lyH_le_stabU (lyH.inv_mem hh)),
    restr7_mul (lyH_le_stabU hh) (lyH_le_stabU ht)]

theorem orbit_card_le_of_closed
    {t : J} (ht : t ∈ lyH) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) (hpos : 0 < T.1.size)
    (hcl : conjClosedOK (hGenPairs asArr) T = true) :
    Nat.card (MulAction.orbit (ConjAct lyH) (⟨t, ht⟩ : lyH)) ≤ T.1.size := by
  have hmem := mem_tree_conj ht hroot hT hpos hcl
  have hex : ∀ y : MulAction.orbit (ConjAct lyH) (⟨t, ht⟩ : lyH),
      ∃ k : Fin T.1.size, mat7 (T.1[k.val]!) = restr7 (((y : lyH) : lyH) : J) := by
    intro y
    obtain ⟨c, hc⟩ := y.2
    have hy : ((y : lyH) : J) = (ConjAct.ofConjAct c : lyH) * t * ((ConjAct.ofConjAct c : lyH) : J)⁻¹ := by
      rw [← hc]
      simp [ConjAct.smul_def]
    obtain ⟨k, hk, hke⟩ := hmem (ConjAct.ofConjAct c : lyH) (ConjAct.ofConjAct c).2
    exact ⟨⟨k, hk⟩, by rw [hy]; exact hke⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := by
    intro y y' h
    apply Subtype.ext
    apply Subtype.ext
    apply restr7_inj_lyH (y : lyH).2 (y' : lyH).2
    rw [← hφ y, ← hφ y', h]
  have := Nat.card_le_card_of_injective φ hinj
  simpa using this

theorem card_centralizer_lyH_ge
    {t : J} (ht : t ∈ lyH) {root : Array ℕ}
    (hroot : mat7 root = restr7 t) {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) (hpos : 0 < T.1.size)
    (hcl : conjClosedOK (hGenPairs asArr) T = true) :
    5859000000 ≤ Nat.card (Subgroup.centralizer ({t} : Set J) ⊓ lyH : Subgroup J) * T.1.size := by
  have hc := orbit_card_le_of_closed ht hroot hT hpos hcl
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct lyH)
    (⟨t, ht⟩ : lyH))
  rw [Nat.card_prod, Nat.card_congr ConjAct.toConjAct.symm.toEquiv, card_stabilizer_conjAct'] at h
  rw [← card_centralizer_inf_eq lyH t ht] at h
  have hcard : Nat.card lyH = 5859000000 := seven_space_centralizer_bound.2.1
  rw [hcard] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_left _ hc


section Point

attribute [local instance] lyXAction

theorem stab_zero_eq :
    MulAction.stabilizer J (0 : Fin 8835156) = lyH := by
  rw [(seven_space_centralizer_bound).1]
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

theorem conj_mem_lyH
    (w τ : J) (d : Fin 8835156) (hτ : lyAct τ 0 = d)
    (hw : lyAct w d = d) : τ⁻¹ * w * τ ∈ lyH := by
  rw [(seven_space_centralizer_bound).1, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  show lyAct (τ⁻¹ * w * τ) 0 = 0
  have hinv : lyAct τ⁻¹ d = 0 := by
    rw [← hτ, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ, hw, hinv]

theorem card_centralizer_stab_mul_le
    (w τ : J) (d : Fin 8835156) (hτ : lyAct τ 0 = d)
    (hw : lyAct w d = d) {root : Array ℕ} (hroot : mat7 root = restr7 (τ⁻¹ * w * τ))
    {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) {N : ℕ} (hN : N ≤ T.1.size) :
    Nat.card (Subgroup.centralizer ({w} : Set J) ⊓ MulAction.stabilizer J d : Subgroup J) * N ≤
      5859000000 := by
  have hτ' : τ • (0 : Fin 8835156) = d := hτ
  have hle := card_inf_stabilizer_le_of_conj w τ d 0 hτ'
  rw [stab_zero_eq] at hle
  have h2 := card_centralizer_lyH_le (conj_mem_lyH w τ d hτ hw) hroot hT hN
  exact (Nat.mul_le_mul_right N hle).trans h2

theorem card_centralizer_stab_eq
    (w τ : J) (d : Fin 8835156) (hτ : lyAct τ 0 = d)
    (hw : lyAct w d = d) {root : Array ℕ} (hroot : mat7 root = restr7 (τ⁻¹ * w * τ))
    {T : Array (Array ℕ) × Array ℕ × Array ℕ}
    (hT : conjTreeOK root (hGenPairs asArr) T = true) (hpos : 0 < T.1.size)
    (hcl : conjClosedOK (hGenPairs asArr) T = true) :
    Nat.card (Subgroup.centralizer ({w} : Set J) ⊓ MulAction.stabilizer J d : Subgroup J) *
      T.1.size = 5859000000 := by
  have hτ' : τ • (0 : Fin 8835156) = d := hτ
  have heq := card_inf_stabilizer_eq_of_conj w τ d 0 hτ'
  rw [stab_zero_eq] at heq
  have hmem := conj_mem_lyH w τ d hτ hw
  have hge := card_centralizer_lyH_ge hmem hroot hT hpos hcl
  have hle := card_centralizer_lyH_le hmem hroot hT (le_refl _)
  rw [heq]
  exact le_antisymm hle hge

end Point

end CFSG.RankThree.PartOne.LyFive
