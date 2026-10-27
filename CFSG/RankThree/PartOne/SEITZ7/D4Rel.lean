module

public import CFSG.RankThree.PartOne.SEITZ7.D4Ord
public import CFSG.RankThree.PartOne.SEITZ3.LongRoot

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

theorem proj_dict : proj (d4Root 2) = rt 0 ∧ proj (d4Root 0) = rt 1 ∧ proj (d4Root 5) = rt 4 ∧
    proj (d4Root 12) = rt 8 ∧ proj (d4Root 19) = rt 3 ∧ proj (d4Root 22) = rt 7 := by
  decide +kernel

theorem rho_dict : rho (d4Root 2) = d4Root 2 ∧ rho (d4Root 19) = d4Root 19 ∧
    rho (d4Root 22) = d4Root 22 ∧ rho (d4Root 0) = d4Root 1 ∧ rho (d4Root 1) = d4Root 3 ∧
    rho (d4Root 5) = d4Root 7 ∧ rho (d4Root 7) = d4Root 9 ∧ rho (d4Root 12) = d4Root 15 ∧
    rho (d4Root 15) = d4Root 13 := by
  decide +kernel

theorem rho_ne_dict : rho (d4Root 0) ≠ d4Root 0 ∧ rho (d4Root 5) ≠ d4Root 5 ∧
    rho (d4Root 12) ≠ d4Root 12 := by
  decide +kernel

@[expose] def posT : List ℕ := [0, 1, 4, 8, 3, 7]

@[expose] def hT : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 4 => 2
  | 8 => 3
  | 3 => 4
  | 7 => 5
  | _ => 0

theorem mem_posT {p : ℕ} (hp : p ∈ posT) : p = 0 ∨ p = 1 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [posT] using hp

theorem posT_nodup : posT.Nodup := by decide

theorem posT_sorted : posT.Pairwise fun a b => hT a ≤ hT b := by decide

theorem lt_twelve_of_mem_posT {p : ℕ} (hp : p ∈ posT) : p < 12 := by
  rcases mem_posT hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem det_check : ∀ a ∈ posT, ∀ b ∈ posT, a ≠ b → rt a 0 * rt b 1 - rt a 1 * rt b 0 ≠ 0 := by
  decide +kernel

theorem linIndep_of_det {α β : Fin 2 → ℤ} (hdet : α 0 * β 1 - α 1 * β 0 ≠ 0) :
    LinIndepPair α β := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  constructor
  · have : a * (α 0 * β 1 - α 1 * β 0) = 0 := by linear_combination β 1 * h0 - β 0 * h1
    exact (mul_eq_zero.1 this).resolve_right hdet
  · have : b * (α 0 * β 1 - α 1 * β 0) = 0 := by linear_combination α 0 * h1 - α 1 * h0
    exact (mul_eq_zero.1 this).resolve_right hdet

theorem ht_check : (∀ k < 12, rt k 0 + rt k 1 ≤ 5) ∧ ∀ a ∈ posT, 1 ≤ rt a 0 + rt a 1 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cone_check : ∀ a ∈ posT, ∀ b ∈ posT, ∀ k < 12, ∀ i : ℕ, i < 6 → ∀ j : ℕ, j < 6 →
    0 < i → 0 < j → rt k 0 = (i : ℤ) * rt a 0 + (j : ℤ) * rt b 0 →
    rt k 1 = (i : ℤ) * rt a 1 + (j : ℤ) * rt b 1 →
    k ∈ posT ∧ min (hT a) (hT b) < hT k := by
  decide +kernel

theorem cone_pos {a b k : ℕ} (ha : a ∈ posT) (hb : b ∈ posT) (hk : k < 12) {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (h : rt k = i • rt a + j • rt b) :
    k ∈ posT ∧ min (hT a) (hT b) < hT k := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply] at h0 h1
  simp only [nsmul_eq_mul] at h0 h1
  have hs : rt k 0 + rt k 1 = i * (rt a 0 + rt a 1) + j * (rt b 0 + rt b 1) := by
    linear_combination h0 + h1
  obtain ⟨hle, hge⟩ := ht_check
  have h5 := hle k hk
  have ha1 := hge a ha
  have hb1 := hge b hb
  have hia := mul_le_mul_of_nonneg_left ha1 (Int.natCast_nonneg i)
  have hjb := mul_le_mul_of_nonneg_left hb1 (Int.natCast_nonneg j)
  have hi' : (0 : ℤ) < i := by exact_mod_cast hi
  have hj' : (0 : ℤ) < j := by exact_mod_cast hj
  have hi6 : i < 6 := by
    have : (i : ℤ) < 6 := by linarith
    exact_mod_cast this
  have hj6 : j < 6 := by
    have : (j : ℤ) < 6 := by linarith
    exact_mod_cast this
  exact cone_check a ha b hb k hk i hi6 j hj6 hi hj h0 h1

variable {K : Type} [Field K] (σ : K →+* K)

theorem isRoot_d4 {k : ℕ} (hk : k < 24) : IsRoot d4 (d4Root k) :=
  isRoot_d4Root (by rw [d4_roots_length]; exact hk)

theorem twistSign_char2 [CharP K 2] (γ : Fin d4.rank → ℤ) : twistSign σ γ = 1 := by
  rcases twistSign_eq_one_or σ γ with h | h
  · exact h
  · rw [h]
    exact CharTwo.neg_eq _

theorem xOrbit_eq [CharP K 2] {p q r : ℕ} (h1 : rho (d4Root p) = d4Root q)
    (h2 : rho (d4Root q) = d4Root r) (c : K) :
    xOrbit σ (d4Root p) c = xd p c * xd q (σ c) * xd r (σ (σ c)) := by
  simp only [xOrbit, h1, h2, twistSign_char2, one_mul]

variable {σ}

theorem mem_XB (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 0) ↔ ∃ c, σ c = c ∧ g = xB c :=
  mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 (by norm_num)) proj_dict.1 rho_dict.1 g

theorem mem_XN (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 3) ↔ ∃ c, σ c = c ∧ g = xN c :=
  mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 (by norm_num)) proj_dict.2.2.2.2.1
    rho_dict.2.1 g

theorem mem_XH (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 7) ↔ ∃ c, σ c = c ∧ g = xH c :=
  mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 (by norm_num)) proj_dict.2.2.2.2.2
    rho_dict.2.2.1 g

theorem mem_XA [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 1) ↔ ∃ a, g = xA σ a := by
  rw [mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_d4 (by norm_num)) proj_dict.2.1
    rho_ne_dict.1 g]
  simp only [xOrbit_eq σ rho_dict.2.2.2.1 rho_dict.2.2.2.2.1]
  rfl

theorem mem_XAB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 4) ↔ ∃ c, g = xAB σ c := by
  rw [mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_d4 (by norm_num)) proj_dict.2.2.1
    rho_ne_dict.2.1 g]
  simp only [xOrbit_eq σ rho_dict.2.2.2.2.2.1 rho_dict.2.2.2.2.2.2.1]
  rfl

theorem mem_XAAB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 8) ↔ ∃ c, g = xAAB σ c := by
  rw [mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_d4 (by norm_num)) proj_dict.2.2.2.1
    rho_ne_dict.2.2 g]
  simp only [xOrbit_eq σ rho_dict.2.2.2.2.2.2.2.1 rho_dict.2.2.2.2.2.2.2.2]
  rfl

theorem comm_condT :
    ∀ a ∈ posT, ∀ b ∈ posT, a ≠ b → ∀ x ∈ twistedRootSubgroupD4 σ (rt a),
      ∀ y ∈ twistedRootSubgroupD4 σ (rt b),
      ⁅x, y⁆ ∈ ⨆ c ∈ posT, ⨆ (_ : min (hT a) (hT b) < hT c), twistedRootSubgroupD4 σ (rt c) := by
  intro a ha b hb hab x hx y hy
  have hra : IsRoot .G2 (rt a) := isRoot_rt (lt_twelve_of_mem_posT ha)
  have hrb : IsRoot .G2 (rt b) := isRoot_rt (lt_twelve_of_mem_posT hb)
  have hlin : LinIndepPair (rt a) (rt b) := linIndep_of_det (det_check a ha b hb hab)
  have hx' : (⟨x, twistedRootSubgroupD4_le_twistedGroup σ hra hx⟩ : twistedGroup σ) ∈
      twistedRootGroup σ (rt a) := Subgroup.mem_subgroupOf.2 hx
  have hy' : (⟨y, twistedRootSubgroupD4_le_twistedGroup σ hrb hy⟩ : twistedGroup σ) ∈
      twistedRootGroup σ (rt b) := Subgroup.mem_subgroupOf.2 hy
  have h := commutator_mem_iSup_twistedRootGroup (σ := σ) hlin hx' hy'
  rw [iSup_twistedRootGroup_eq_subgroupOf σ fun β hβ => hβ.1, Subgroup.mem_subgroupOf] at h
  refine (iSup₂_le fun ε hε => ?_ :
    (⨆ ε ∈ openCone {β | IsRoot .G2 β} (rt a) (rt b), twistedRootSubgroupD4 σ ε) ≤ _) h
  obtain ⟨hεR, i, j, hi, hj, hεij⟩ := hε
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hεR
  have hk12 : k < 12 := by simpa [len_roots] using hk
  obtain ⟨hkp, hkh⟩ := cone_pos ha hb hk12 hi hj hεij
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ posT) =>
    ⨆ (_ : min (hT a) (hT b) < hT c), twistedRootSubgroupD4 σ (rt c)) k hkp
    (le_iSup (fun _ : min (hT a) (hT b) < hT k => twistedRootSubgroupD4 σ (rt k)) hkh)

@[expose] noncomputable def Uhat (σ : K →+* K) : Subgroup (adjointGroup d4 K) :=
  ⨆ p ∈ posT, twistedRootSubgroupD4 σ (rt p)

theorem exists_ordT [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K}
    (hu : u ∈ Uhat σ) :
    ∃ c : ℕ → K, σ (c 0) = c 0 ∧ σ (c 3) = c 3 ∧ σ (c 7) = c 7 ∧ u = ordT σ c := by
  classical
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem
    (fun p => twistedRootSubgroupD4 σ (rt p)) hT posT_nodup posT_sorted comm_condT u hu
  obtain ⟨c0, hc0, e0⟩ := (mem_XB hσ _).1 (hf 0 (by simp [posT]))
  obtain ⟨c1, e1⟩ := (mem_XA hσ _).1 (hf 1 (by simp [posT]))
  obtain ⟨c4, e4⟩ := (mem_XAB hσ _).1 (hf 4 (by simp [posT]))
  obtain ⟨c8, e8⟩ := (mem_XAAB hσ _).1 (hf 8 (by simp [posT]))
  obtain ⟨c3, hc3, e3⟩ := (mem_XN hσ _).1 (hf 3 (by simp [posT]))
  obtain ⟨c7, hc7, e7⟩ := (mem_XH hσ _).1 (hf 7 (by simp [posT]))
  refine ⟨fun p => if p = 0 then c0 else if p = 1 then c1 else if p = 4 then c4 else
    if p = 8 then c8 else if p = 3 then c3 else c7, by simpa using hc0, by simpa using hc3,
    by simpa using hc7, ?_⟩
  simp only [posT, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e0, e1,
    e4, e8, e3, e7, ordT]
  simp [mul_assoc]

end CFSG.RankThree.PartOne.SEITZ7
