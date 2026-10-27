module

public import Certificates.Kernel.D4.FieldChecks
public import Certificates.Kernel.D4.PhiFacts
public import CFSG.Certificates.Kernel.D4FieldSound
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Model
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Lines
public import CFSG.Mathlib.GroupTheory.SylowConj
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4Field CFSG.Monster.B.Co2 CFSG.StandardType.TriD4TwoRow
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Open Subgroup

section Group

variable {G : Type*} [Group G]

theorem three_mul_le_card_of_lt {H K : Subgroup G} [Finite K] (hHK : H ≤ K) (hne : ¬ K ≤ H)
    (hK : Nat.card K ∣ 27) : 3 * Nat.card H ≤ Nat.card K := by
  have h := H.relIndex_mul_card K
  rw [inf_of_le_left hHK] at h
  have hd : H.relIndex K ∣ 3 ^ 3 := (H.relIndex_dvd_card K).trans hK
  have h1 : H.relIndex K ≠ 1 := fun h1 => hne (Subgroup.relIndex_eq_one.mp h1)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have h3 : 3 ≤ H.relIndex K := by
    rw [hk']
    interval_cases k <;> simp_all
  rw [← h]
  exact Nat.mul_le_mul_right _ h3

theorem eq_one_or_of_mem_zpowers [Finite G] {u x : G} (hu : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u ∨ x = u * u := by
  classical
  have ho : orderOf u = 3 := orderOf_eq_prime hu hu1
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k
  · exact Or.inl (pow_zero u)
  · exact Or.inr (Or.inl (pow_one u))
  · exact Or.inr (Or.inr (pow_two u))

theorem mem_normalizer_of_conj_mem_closure [Finite G] {S : Set G} {n : G}
    (h : ∀ g ∈ S, n * g * n⁻¹ ∈ closure S) : n ∈ normalizer (closure S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (closure S).map (MulAut.conj n).toMonoidHom ≤ closure S := by
    rw [Subgroup.map_le_iff_le_comap, closure_le]
    intro g hg
    exact h g hg
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])

end Group

theorem getD_eq_get {α : Type*} {l : List α} {d : α} {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

noncomputable def pk (X : ℕ) : Equiv.Perm (Fin 2457) := permOfArr 2457 (unpack 2457 12 X)

theorem rep_pk {X : ℕ} (h : permB 2457 12 X = true) : Rep 2457 (unpack 2457 12 X) (pk X) :=
  rep_of_validA (validA_of h)

theorem ap_eq {X : ℕ} (h : permB 2457 12 X = true) (y : Fin 2457) : ap X y = (pk X y : ℕ) :=
  (Orb.unpack_get y.2).symm.trans (rep_pk h y)

theorem perm_eq {a b : Equiv.Perm (Fin 2457)} {f g : ℕ → ℕ} (hf : ∀ y : Fin 2457, f y = a y)
    (hg : ∀ y : Fin 2457, g y = b y) (h : ∀ x < 2457, f x = g x) : a = b :=
  Equiv.ext fun y => Fin.ext ((hf y).symm.trans ((h y y.2).trans (hg y)))

theorem perm_ne {a b : Equiv.Perm (Fin 2457)} {f g : ℕ → ℕ} (hf : ∀ y : Fin 2457, f y = a y)
    (hg : ∀ y : Fin 2457, g y = b y) (h : ∃ x < 2457, f x ≠ g x) : a ≠ b := by
  rintro rfl
  obtain ⟨x, hx, hne⟩ := h
  exact hne ((hf ⟨x, hx⟩).trans (hg ⟨x, hx⟩).symm)

theorem mul_ap (a b : Equiv.Perm (Fin 2457)) (y : Fin 2457) : (a * b) y = a (b y) := by
  rw [Equiv.Perm.mul_apply]

theorem pow1_ap (a : Equiv.Perm (Fin 2457)) (y : Fin 2457) : (a ^ 1) y = a y := by
  rw [pow_one]

theorem pow2_ap (a : Equiv.Perm (Fin 2457)) (y : Fin 2457) : (a ^ 2) y = a (a y) := by
  rw [pow_two, mul_ap]

theorem pow3_ap (a : Equiv.Perm (Fin 2457)) (y : Fin 2457) : (a ^ 3) y = a (a (a y)) := by
  rw [pow_three, Equiv.Perm.mul_apply, mul_ap]

theorem hN81 : EQ.N = 81 := Nat.eq_of_beq_eq_true bQ.2.2

theorem hng4 : EQ.ng = 4 := Nat.eq_of_beq_eq_true bQ.2.1

theorem pT {i : ℕ} (hi : i < 81) : permB 2457 12 (EQ.T i) = true :=
  CFSG.KC.D4K.permB_pts okQ pQG i (by rw [hN81]; exact hi)

theorem pF : permB 2457 12 (FX 0) = true := (fOK_sound (fieldK_parts fieldOK).1).1

theorem pG0 : permB 2457 12 (FX 1) = true := (fOK_sound (fieldK_parts fieldOK).1).2.2.1

theorem pW {k : ℕ} (hk : k < 4) : permB 2457 12 (FX (2 + k)) = true :=
  ((fieldK_parts fieldOK).2.1 k hk).1

theorem class_lt : ∀ m < 10, (∀ d ∈ CFSG.KD.D4F.CD.getD m [], d < 81) ∧
    (CFSG.KD.D4F.CR.getD m (0, 0)).1 < 81 ∧ (CFSG.KD.D4F.CR.getD m (0, 0)).2 < 81 := by
  decide +kernel

theorem phi_pk : pk (PH 0) = d4Phi := (rep_pk phiFacts.1).unique rep_phi

set_option maxRecDepth 400000 in
theorem zAt_eq {i c : ℕ} (hi : i < 81) (hc : c = 1 ∨ c = 2) (y : Fin 2457) :
    zAt EQ.T (FX 0) i c y = ((pk (EQ.T i) * pk (FX 0) ^ c) y : ℕ) := by
  rcases hc with rfl | rfl
  · have e : zAt EQ.T (FX 0) i 1 y = ap (EQ.T i) (ap (FX 0) y) := rfl
    rw [e, ap_eq pF, ap_eq (pT hi), mul_ap, pow1_ap]
  · have e : zAt EQ.T (FX 0) i 2 y = ap (EQ.T i) (ap (FX 0) (ap (FX 0) y)) := rfl
    rw [e, ap_eq pF, ap_eq pF, ap_eq (pT hi), mul_ap, pow2_ap]

theorem T_mem {i : ℕ} (hi : i < 81) : pk (EQ.T i) ∈ d4Q := by
  have hi' : i < EQ.N := by rw [hN81]; exact hi
  have hr : Rep 2457 d4QCert.pts[i]! (pk (EQ.T i)) := by
    rw [enumQ.2.2 i hi']
    exact rep_pk (pT hi)
  exact enumOK_mem d4Keys_lt enumQ.1 (by rw [enumQ.2.1]; exact hi') hr

theorem exists_T {x : Equiv.Perm (Fin 2457)} (hx : x ∈ d4Q) : ∃ i < 81, x = pk (EQ.T i) := by
  obtain ⟨i, hi, he⟩ := ((enumOK_spec d4Keys_lt enumQ.1).1 x).1 hx
  rw [enumQ.2.1] at hi
  rw [enumQ.2.2 i hi] at he
  exact ⟨i, hN81 ▸ hi, he.symm⟩

theorem T_zero : pk (EQ.T 0) = 1 :=
  perm_eq (f := ap (EQ.T 0)) (g := fun x => x) (ap_eq (pT (by norm_num))) (fun _ => rfl)
    (fOK_sound (fieldK_parts fieldOK).1).2.2.2.2.2.1

theorem F_cube : pk (FX 0) ^ 3 = 1 := by
  refine perm_eq (f := fun x => ap (FX 0) (ap (FX 0) (ap (FX 0) x))) (g := fun x => x)
    (fun y => ?_) (fun _ => rfl) (fOK_sound (fieldK_parts fieldOK).1).2.1
  simp only [ap_eq pF, pow3_ap, mul_ap]

theorem G0_eq : pk (FX 1) = pk (FX 0) * d4Phi * d4Phi := by
  rw [← phi_pk]
  refine perm_eq (f := ap (FX 1)) (g := fun x => ap (FX 0) (ap (PH 0) (ap (PH 0) x)))
    (ap_eq pG0) (fun y => ?_) (fOK_sound (fieldK_parts fieldOK).1).2.2.2.1
  simp only [ap_eq pF, ap_eq phiFacts.1, mul_ap]

theorem G0_mem : pk (FX 1) ∈ d4P :=
  mem_d4P_of_sift (rep_pk pG0) (siftA_ofOK (fOK_sound (fieldK_parts fieldOK).1).2.2.2.2.1)

theorem W_mem {k : ℕ} (hk : k < 4) : pk (FX (2 + k)) ∈ d4P :=
  mem_d4P_of_sift (rep_pk (pW hk)) (siftA_ofOK ((fieldK_parts fieldOK).2.1 k hk).2)

theorem F_mem_G : pk (FX 0) ∈ d4G := by
  have e : pk (FX 0) = pk (FX 1) * (d4Phi * d4Phi)⁻¹ := by
    rw [G0_eq]
    group
  rw [e]
  exact d4G.mul_mem (d4P_le_d4G G0_mem) (d4G.inv_mem (d4G.mul_mem d4Phi_mem_d4G d4Phi_mem_d4G))

theorem F_not_mem :
    pk (FX 0) ∉ d4P := by
  intro h
  apply d4Phi_not_mem
  have h2 : d4Phi * d4Phi ∈ d4P := by
    have := d4P.mul_mem (d4P.inv_mem h) G0_mem
    rwa [G0_eq, mul_assoc, inv_mul_cancel_left] at this
  have e : d4Phi = (d4Phi * d4Phi) * (d4Phi * d4Phi) := by
    have h3 : d4Phi * d4Phi * d4Phi = 1 := by rw [← pow_three', d4Phi_pow_three]
    calc d4Phi = (d4Phi * d4Phi * d4Phi) * d4Phi := by rw [h3, one_mul]
      _ = (d4Phi * d4Phi) * (d4Phi * d4Phi) := by group
  rw [e]
  exact d4P.mul_mem h2 h2

theorem F_ne_one :
    pk (FX 0) ≠ 1 :=
  fun h => F_not_mem (h ▸ d4P.one_mem)

theorem F_sq_not_mem :
    pk (FX 0) ^ 2 ∉ d4P := by
  intro h
  apply F_not_mem
  have e : pk (FX 0) = pk (FX 0) ^ 2 * pk (FX 0) ^ 2 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, F_cube, one_mul]
  rw [e]
  exact d4P.mul_mem h h

theorem d4QGens_size_eq : d4QGens.size = 4 := bindQ.1.trans hng4

theorem F_norm : pk (FX 0) ∈ normalizer (d4Q : Set (Equiv.Perm (Fin 2457))) := by
  unfold d4Q
  refine mem_normalizer_of_conj_mem_closure ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk4 : k < 4 := by
    rw [Set.mem_setOf_eq, d4QGens_size_eq] at hk
    exact hk
  obtain ⟨hNJ, hpt⟩ := (fOK_sound (fieldK_parts fieldOK).1).2.2.2.2.2.2 k hk4
  have hg : permOfArr 2457 d4QGens[k]! = pk (EQ.G k) := by
    rw [bindQ.2 k (by rw [hng4]; exact hk4)]
    rfl
  have hpG := pQG k (by rw [hng4]; exact hk4)
  have e : pk (FX 0) * pk (EQ.G k) = pk (EQ.T (CFSG.KD.D4F.NJ.getD k 0)) * pk (FX 0) := by
    refine perm_eq (f := fun x => ap (FX 0) (ap (EQ.G k) x))
      (g := fun x => ap (EQ.T (CFSG.KD.D4F.NJ.getD k 0)) (ap (FX 0) x)) (fun y => ?_)
      (fun y => ?_) hpt
    · simp only [ap_eq pF, ap_eq hpG, mul_ap]
    · simp only [ap_eq pF, ap_eq (pT hNJ), mul_ap]
  dsimp only
  rw [hg, e, mul_inv_cancel_right]
  exact T_mem hNJ

noncomputable def sS : Subgroup (Equiv.Perm (Fin 2457)) := d4Q ⊔ zpowers (pk (FX 0))

theorem F_mem_sS : pk (FX 0) ∈ sS := mem_sup_right (mem_zpowers _)

theorem exists_sS
    {x : Equiv.Perm (Fin 2457)}
    (hx : x ∈ sS) : ∃ i < 81, ∃ c < 3, x = pk (EQ.T i) * pk (FX 0) ^ c := by
  classical
  rw [sS, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left d4Q _ (zpowers_le.2 F_norm), Set.mem_mul] at hx
  obtain ⟨q, hq, y, hy, rfl⟩ := hx
  obtain ⟨i, hi, rfl⟩ := exists_T hq
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime F_cube F_ne_one] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  exact ⟨i, hi, c, hc, rfl⟩

theorem sS_le_G : sS ≤ d4G :=
  sup_le (d4Q_le.trans d4P_le_d4G) (zpowers_le.2 F_mem_G)

theorem mem_d4Q_of_sS
    {x : Equiv.Perm (Fin 2457)}
    (hxS : x ∈ sS) (hxP : x ∈ d4P) : x ∈ d4Q := by
  obtain ⟨i, hi, c, hc, rfl⟩ := exists_sS hxS
  have hF : pk (FX 0) ^ c ∈ d4P := by
    have := d4P.mul_mem (d4P.inv_mem (d4Q_le (T_mem hi))) hxP
    rwa [inv_mul_cancel_left] at this
  interval_cases c
  · rw [pow_zero, mul_one]
    exact T_mem hi
  · rw [pow_one] at hF
    exact absurd hF F_not_mem
  · exact absurd hF F_sq_not_mem

theorem card_eq_three_mul
    {B : Subgroup (Equiv.Perm (Fin 2457))} (hBG : B ≤ d4G) (hBP : ¬ B ≤ d4P) :
    Nat.card B = 3 * Nat.card ↥(B ⊓ d4P) := by
  have := d4P_normal_d4G
  have h := (d4P.subgroupOf d4G).relIndex_mul_card (B.subgroupOf d4G)
  have hd : (d4P.subgroupOf d4G).relIndex (B.subgroupOf d4G) ∣ 3 :=
    index_d4P_d4G ▸ Subgroup.relIndex_dvd_index_of_normal _ _
  have h1 : (d4P.subgroupOf d4G).relIndex (B.subgroupOf d4G) ≠ 1 := by
    intro h1
    apply hBP
    intro x hx
    have hx' : (⟨x, hBG hx⟩ : d4G) ∈ B.subgroupOf d4G := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (Subgroup.relIndex_eq_one.mp h1 hx')
  have h3 : (d4P.subgroupOf d4G).relIndex (B.subgroupOf d4G) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h' | h'
    · exact absurd h' h1
    · exact h'
  have hB : Nat.card ↥(B.subgroupOf d4G) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv
  have hI : Nat.card ↥(d4P.subgroupOf d4G ⊓ B.subgroupOf d4G) = Nat.card ↥(B ⊓ d4P) := by
    have hI' : d4P.subgroupOf d4G ⊓ B.subgroupOf d4G = (B ⊓ d4P).subgroupOf d4G := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [hI']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hBG)).toEquiv
  rw [hB, hI, h3] at h
  exact h.symm

theorem card_sS :
    Nat.card sS = 243 := by
  have hinf : sS ⊓ d4P = d4Q :=
    le_antisymm (fun x hx => mem_d4Q_of_sS hx.1 hx.2) (le_inf le_sup_left d4Q_le)
  have hQ : Nat.card d4Q = 81 := by rw [card_d4Q, factorization_card_d4P_three]; norm_num
  rw [card_eq_three_mul sS_le_G fun h => F_not_mem (h F_mem_sS), hinf, hQ]

theorem exists_conj_le_sS
    {B : Subgroup (Equiv.Perm (Fin 2457))} (hBG : B ≤ d4G) (hB : IsPGroup 3 B) :
    ∃ g ∈ d4G, ∀ b ∈ B, g⁻¹ * b * g ∈ sS := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hB.exists_mem_conj_mem_of_card_eq sS_le_G ?_ hBG
  rw [card_sS, card_d4G, show (634023936 : ℕ) = 3 ^ 5 * 2609152 by norm_num,
    factorization_pow_mulG Nat.prime_three (by norm_num)]
  norm_num

theorem d4X_zero_fix :
    ∃ p : Fin 2457, permOfArr 2457 d4Lines[0]! p = p := by
  have hR := rep_of_validA (d4Lines_valid (by norm_num : 0 < 31))
  have h11 : 11 < 2457 := by norm_num
  have h : (d4Lines[0]!)[11]! = 11 := by
    rw [lineX0, Orb.unpack_get h11]
    decide +kernel
  exact ⟨⟨11, h11⟩, Fin.ext ((hR ⟨11, h11⟩).symm.trans h)⟩

theorem isSolvable_centralizer_of_noFix
    {u : Equiv.Perm (Fin 2457)}
    (hu : u ∈ d4P) (huo : orderOf u = 3) (hfix : ∀ x, u x ≠ x) :
    IsSolvable ↥(centralizer {u} ⊓ d4P) := by
  obtain ⟨k, hk, j, hj, e, he, hvk⟩ := exists_conj_rep d4Q_le card_d4Q
    (fun j => permOfArr 2457 d4Lines[j]!) (fun c => permOfArr 2457 d4Lines[c]!)
    (fun j => permOfArr 2457 d4Trans[j]!) (fun j => d4Rec.getD j 0) (r := 31)
    (fun g hg hg3 => d4_lines hg hg3) (fun j hj => d4_trans hj) hu huo
  have hrec : d4Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec d4_lines_check.2.2.2 hj)
  rcases (by omega : d4Rec.getD j 0 = 0 ∨ d4Rec.getD j 0 = 1) with h | h
  · exfalso
    rw [h] at hvk
    obtain ⟨p, hp⟩ := d4X_zero_fix
    apply hfix (k p)
    have hx : (permOfArr 2457 d4Lines[0]! ^ e) p = p :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hp e
    have hkk : k⁻¹ (k p) = p := Equiv.Perm.inv_eq_iff_eq.mpr rfl
    rw [hvk, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hkk, hx]
  · rw [h] at hvk
    rw [hvk]
    apply isSolvable_centralizer_conj fun x hx => d4P.mul_mem (d4P.mul_mem (d4P.inv_mem hk) hx) hk
    have hx1 : (centralizer {d4X 1 ^ e} : Subgroup (Equiv.Perm (Fin 2457))) =
        centralizer {d4X 1} := by
      rcases he with rfl | rfl
      · rw [pow_one]
      · refine le_antisymm (centralizer_pow_two_le (d4X_cube (by norm_num))) ?_
        intro z hz
        rw [mem_centralizer_singleton_iff] at hz ⊢
        exact (Commute.pow_right hz 2)
    have hX : d4X 1 = permOfArr 2457 d4Lines[1]! := rfl
    rw [← hX, hx1]
    exact isSolvable_centralizer_d4X_one

set_option maxRecDepth 400000 in
theorem field_in_sS
    {B : Subgroup (Equiv.Perm (Fin 2457))} (hBS : B ≤ sS) (hB : IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) (hBP : ¬ B ≤ d4P) {u : Equiv.Perm (Fin 2457)} (huB : u ∈ B)
    (huP : u ∈ d4P) (hu1 : u ≠ 1) :
    IsSolvable ↥(centralizer {u} ⊓ d4P) ∨
      ∃ n ∈ d4P, n ∈ normalizer (B : Set (Equiv.Perm (Fin 2457))) ∧ n * u * n⁻¹ ∉ zpowers u := by
  classical
  have hBG : B ≤ d4G := hBS.trans sS_le_G
  have hBP9 : Nat.card ↥(B ⊓ d4P) = 9 := by
    have := card_eq_three_mul hBG hBP
    omega
  have hBQ : ∀ {x}, x ∈ B → x ∈ d4P → ∃ j < 81, x = pk (EQ.T j) := fun hx hxP =>
    exists_T (mem_d4Q_of_sS (hBS hx) hxP)
  obtain ⟨z, hzB, hzP⟩ : ∃ z ∈ B, z ∉ d4P := by
    by_contra hc
    push Not at hc
    exact hBP fun x hx => hc x hx
  obtain ⟨i, hi, c, hc3, hzeq⟩ := exists_sS (hBS hzB)
  have hc : c = 1 ∨ c = 2 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with h | h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hzeq
      exact hzP (hzeq ▸ d4Q_le (T_mem hi))
    · exact Or.inl h
    · exact Or.inr h
  have hzf : ∀ y : Fin 2457, zAt EQ.T (FX 0) i c y = (z y : ℕ) := fun y => by
    rw [hzeq]
    exact zAt_eq hi hc y
  have hz3 : z ^ 3 = 1 := hB.2 z hzB
  have hp162 : 2 * i + (c - 1) < 162 := by omega
  have hpi : (2 * i + (c - 1)) / 2 = i := by omega
  have hpc : (2 * i + (c - 1)) % 2 + 1 = c := by omega
  have hzOK := (fieldK_parts fieldOK).2.2.1 _ hp162
  rw [hpi, hpc] at hzOK
  have ho : CFSG.KD.D4F.ZO.getD (2 * i + (c - 1)) 0 ≠ 0 := by
    intro h0
    rw [h0] at hzOK
    refine perm_ne (a := z ^ 3) (b := 1)
      (f := fun x => zAt EQ.T (FX 0) i c (zAt EQ.T (FX 0) i c (zAt EQ.T (FX 0) i c x)))
      (g := fun x => x) (fun y => ?_) (fun _ => rfl) (zOK_zero hzOK) hz3
    simp only [hzf, pow3_ap, mul_ap]
  obtain ⟨hA, hlen, hW, hM⟩ := zOK_sound ho hzOK
  have comm_ne : ∀ {j}, j < 81 → (∃ x < 2457, ap (EQ.T j) (zAt EQ.T (FX 0) i c x) ≠
      zAt EQ.T (FX 0) i c (ap (EQ.T j) x)) → pk (EQ.T j) * z ≠ z * pk (EQ.T j) :=
    fun hj h => perm_ne (fun y => by simp only [hzf, ap_eq (pT hj), mul_ap])
      (fun y => by simp only [hzf, ap_eq (pT hj), mul_ap]) h
  have cube_ne : ∀ {j}, j < 81 →
      (∃ x < 2457, ap (EQ.T j) (ap (EQ.T j) (ap (EQ.T j) x)) ≠ x) → pk (EQ.T j) ^ 3 ≠ 1 :=
    fun hj h => perm_ne (g := fun x => x)
      (fun y => by simp only [ap_eq (pT hj), pow3_ap, mul_ap]) (fun _ => rfl) h
  have tcomm_ne : ∀ {j w}, j < 81 → w < 81 →
      (∃ y < 2457, ap (EQ.T j) (ap (EQ.T w) y) ≠ ap (EQ.T w) (ap (EQ.T j) y)) →
      pk (EQ.T j) * pk (EQ.T w) ≠ pk (EQ.T w) * pk (EQ.T j) :=
    fun hj hw h => perm_ne
      (fun y => by simp only [ap_eq (pT hj), ap_eq (pT hw), mul_ap])
      (fun y => by simp only [ap_eq (pT hj), ap_eq (pT hw), mul_ap]) h
  have noFix : ∀ {j}, j < 81 → (∀ x < 2457, ap (EQ.T j) x ≠ x) → ∀ x, pk (EQ.T j) x ≠ x :=
    fun hj h x hx => h x x.2 (by rw [ap_eq (pT hj), hx])
  have hinL : ∀ {j}, j < 81 → j ≠ 0 → pk (EQ.T j) ∈ B →
      j ∈ CFSG.KD.D4F.ZL.getD (2 * i + (c - 1)) [] := by
    intro j hj hj0 hjB
    by_contra hjL
    rcases hA j hj hj0 hjL with h | h
    · exact comm_ne hj h (hB.comm hjB hzB)
    · exact cube_ne hj h (hB.2 _ hjB)
  obtain ⟨w, hw, rfl⟩ := hBQ huB huP
  have hu3 : pk (EQ.T w) ^ 3 = 1 := hB.2 _ huB
  have huo : orderOf (pk (EQ.T w)) = 3 := orderOf_eq_prime hu3 hu1
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu1 T_zero
  obtain ⟨jj, hjj, hLj⟩ := List.getElem_of_mem (hinL hw hw0 huB)
  have hjjC : jj < (CFSG.KD.D4F.ZC.getD (2 * i + (c - 1)) []).length := hlen ▸ hjj
  have hmem : (w, (CFSG.KD.D4F.ZC.getD (2 * i + (c - 1)) [])[jj]) ∈
      (CFSG.KD.D4F.ZL.getD (2 * i + (c - 1)) []).zip
        (CFSG.KD.D4F.ZC.getD (2 * i + (c - 1)) []) := by
    have hz : jj < ((CFSG.KD.D4F.ZL.getD (2 * i + (c - 1)) []).zip
        (CFSG.KD.D4F.ZC.getD (2 * i + (c - 1)) [])).length := by
      rw [List.length_zip]
      exact Nat.lt_min.2 ⟨hjj, hjjC⟩
    have := List.getElem_mem hz
    rwa [List.getElem_zip, hLj] at this
  rcases hW _ hmem with ⟨-, hnf⟩ | ⟨hlt, hcls⟩
  · exact Or.inl (isSolvable_centralizer_of_noFix huP huo (noFix hw hnf))
  set ci := (CFSG.KD.D4F.ZC.getD (2 * i + (c - 1)) [])[jj] with hci
  set ma := (CFSG.KD.D4F.ZP.getD (2 * i + (c - 1)) []).getD ci (0, 0) with hma
  have hmaP : ma ∈ CFSG.KD.D4F.ZP.getD (2 * i + (c - 1)) [] := by
    rw [hma, getD_eq_get hlt]
    exact List.getElem_mem hlt
  obtain ⟨hm10, haD, hzR⟩ := hM ma hmaP
  obtain ⟨hDlt, hr1, hr2⟩ := class_lt ma.1 hm10
  obtain ⟨hD9, hD0, -, hR21, hNq, hWL⟩ := cOK_sound ((fieldK_parts fieldOK).2.2.2 ma.1 hm10)
  set D := CFSG.KD.D4F.CD.getD ma.1 [] with hD
  set r := CFSG.KD.D4F.CR.getD ma.1 (0, 0) with hr
  have h0D : 0 ∈ D := by
    have h0 : 0 < D.length := by omega
    rw [getD_eq_get h0] at hD0
    exact hD0 ▸ List.getElem_mem h0
  have hBD : ∀ {y}, y ∈ B → y ∈ d4P → ∃ d ∈ D, y = pk (EQ.T d) := by
    intro y hyB hyP
    obtain ⟨j, hj, rfl⟩ := hBQ hyB hyP
    by_cases hj0 : j = 0
    · exact ⟨0, h0D, by rw [hj0]⟩
    rcases hcls j (hinL hj hj0 hyB) with h | h
    · exact ⟨j, h, rfl⟩
    · exact absurd (hB.comm hyB huB) (tcomm_ne hj hw h)
  set Ts : Finset (Equiv.Perm (Fin 2457)) := (D.map fun d => pk (EQ.T d)).toFinset with hTs
  have hsub : ((B ⊓ d4P : Subgroup (Equiv.Perm (Fin 2457))) : Set (Equiv.Perm (Fin 2457))) ⊆
      ↑Ts := by
    rintro y ⟨hyB, hyP⟩
    obtain ⟨d, hd, rfl⟩ := hBD hyB hyP
    simp only [hTs, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨d, hd, rfl⟩
  have hTcard : Ts.card ≤ 9 := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map]
    exact hD9.le
  have hncard : ((B ⊓ d4P : Subgroup (Equiv.Perm (Fin 2457))) :
      Set (Equiv.Perm (Fin 2457))).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hBP9
  have heqT := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_coe_finset, hncard]; exact hTcard) (Finset.finite_toSet _)
  have hDB : ∀ d ∈ D, pk (EQ.T d) ∈ B := by
    intro d hd
    have : pk (EQ.T d) ∈ (Ts : Set (Equiv.Perm (Fin 2457))) := by
      simp only [hTs, Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨d, hd, rfl⟩
    rw [← heqT] at this
    exact this.1
  have hR1def : ∀ y : Fin 2457, zAt EQ.T (FX 0) r.1 1 y =
      ((pk (EQ.T r.1) * pk (FX 0) ^ 1) y : ℕ) := zAt_eq hr1 (Or.inl rfl)
  have hR1B : pk (EQ.T r.1) * pk (FX 0) ^ 1 ∈ B := by
    have hrc : rep r c < 81 := by
      rcases hc with rfl | rfl
      · exact hr1
      · exact hr2
    have hRc : z = pk (EQ.T ma.2) * (pk (EQ.T (rep r c)) * pk (FX 0) ^ c) :=
      perm_eq (f := zAt EQ.T (FX 0) i c)
        (g := fun x => ap (EQ.T ma.2) (zAt EQ.T (FX 0) (rep r c) c x)) hzf
        (fun y => by
          simp only [zAt_eq hrc hc, ap_eq (pT (hDlt _ haD)), mul_ap]) hzR
    have hRcB : pk (EQ.T (rep r c)) * pk (FX 0) ^ c ∈ B := by
      have := B.mul_mem (B.inv_mem (hDB _ haD)) hzB
      rwa [hRc, inv_mul_cancel_left] at this
    rcases hc with rfl | rfl
    · exact hRcB
    · have e : (pk (EQ.T r.2) * pk (FX 0) ^ 2) * (pk (EQ.T r.2) * pk (FX 0) ^ 2) =
          pk (EQ.T r.1) * pk (FX 0) ^ 1 :=
        perm_eq (f := fun x => zAt EQ.T (FX 0) r.2 2 (zAt EQ.T (FX 0) r.2 2 x))
          (g := zAt EQ.T (FX 0) r.1 1)
          (fun y => by simp only [zAt_eq hr2 (Or.inr rfl), mul_ap]) hR1def hR21
      rw [← e]
      exact B.mul_mem hRcB hRcB
  have hR1P : pk (EQ.T r.1) * pk (FX 0) ^ 1 ∉ d4P := by
    intro h
    apply F_not_mem
    have := d4P.mul_mem (d4P.inv_mem (d4Q_le (T_mem hr1))) h
    rwa [inv_mul_cancel_left, pow_one] at this
  obtain ⟨d, hdD, hud⟩ := hBD huB huP
  obtain ⟨jd, hjd, hDjd⟩ := List.getElem_of_mem hdD
  have hjd0 : jd ≠ 0 := by
    rintro rfl
    have h0 : 0 < D.length := by omega
    rw [getD_eq_get h0] at hD0
    rw [← hDjd, hD0, T_zero] at hud
    exact hu1 hud
  obtain ⟨q, rfl⟩ : ∃ q, jd = q + 1 := ⟨jd - 1, by omega⟩
  have hq8 : q < 8 := by omega
  have hDq : D.getD (q + 1) 0 = d := by rw [getD_eq_get hjd, hDjd]
  rcases hNq q hq8 with ⟨-, hnf⟩ | ⟨⟨e, heWL, he1⟩, hmv1, hmv2⟩
  · left
    rw [hDq] at hnf
    rw [hud]
    rw [hud] at huP huo
    exact isSolvable_centralizer_of_noFix huP huo (noFix (hDlt d hdD) hnf)
  right
  obtain ⟨he4, -, hperm, he22, hRw⟩ := hWL e heWL
  rw [← he1, hDq] at hmv1 hmv2
  have hd81 := hDlt d hdD
  have hpn := pW he4
  have hn1 : pk (FX (2 + e.1)) * pk (EQ.T d) ≠ pk (EQ.T d) * pk (FX (2 + e.1)) :=
    perm_ne (fun y => by simp only [ap_eq hpn, ap_eq (pT hd81), mul_ap])
      (fun y => by simp only [ap_eq hpn, ap_eq (pT hd81), mul_ap]) hmv1
  have hn2 : pk (FX (2 + e.1)) * pk (EQ.T d) ≠
      pk (EQ.T d) * pk (EQ.T d) * pk (FX (2 + e.1)) :=
    perm_ne (fun y => by simp only [ap_eq hpn, ap_eq (pT hd81), mul_ap])
      (fun y => by simp only [ap_eq hpn, ap_eq (pT hd81), mul_ap]) hmv2
  set X : Set (Equiv.Perm (Fin 2457)) :=
    {y | ∃ d ∈ D, y = pk (EQ.T d)} ∪ {pk (EQ.T r.1) * pk (FX 0) ^ 1} with hX
  have hXB : closure X ≤ B := by
    rw [closure_le]
    rintro y (⟨d', hd', rfl⟩ | hy)
    · exact hDB d' hd'
    · rw [Set.mem_singleton_iff.mp hy]
      exact hR1B
  have hXeq : closure X = B := by
    refine Subgroup.eq_of_le_of_card_ge hXB ?_
    have hle : B ⊓ d4P ≤ closure X := by
      intro y hy
      obtain ⟨d', hd', rfl⟩ := hBD hy.1 hy.2
      exact subset_closure (Or.inl ⟨d', hd', rfl⟩)
    have hlt : ¬ closure X ≤ B ⊓ d4P := fun h =>
      hR1P (h (subset_closure (Or.inr rfl))).2
    have := three_mul_le_card_of_lt hle hlt (hB27 ▸ Subgroup.card_dvd_of_le hXB)
    omega
  refine ⟨pk (FX (2 + e.1)), W_mem he4, ?_, ?_⟩
  · rw [← hXeq]
    refine mem_normalizer_of_conj_mem_closure ?_
    rintro y (⟨d', hd', rfl⟩ | hy)
    · obtain ⟨jd', hjd', hDjd'⟩ := List.getElem_of_mem hd'
      have hDl : D.length = 9 := hD9
      rcases Nat.eq_zero_or_eq_succ_pred jd' with h0 | hs
      · have h0' : 0 < D.length := by omega
        have : d' = 0 := by
          rw [← hDjd']
          simp only [h0]
          rw [getD_eq_get h0'] at hD0
          exact hD0
        rw [this, T_zero, mul_one, mul_inv_cancel]
        exact (closure X).one_mem
      · have hj1 : 1 ≤ jd' := by
          rw [hs]
          exact Nat.succ_pos _
        obtain ⟨hπ, hpt⟩ := hperm (jd' - 1) (by omega)
        have hD' : D.getD (jd' - 1 + 1) 0 = d' := by
          have e1 : jd' - 1 + 1 = jd' := by omega
          rw [e1, getD_eq_get hjd', hDjd']
        rw [hD'] at hpt
        have hπ81 := hDlt _ hπ
        have hd'81 := hDlt _ hd'
        have e2 : pk (FX (2 + e.1)) * pk (EQ.T d') =
            pk (EQ.T (e.2.1.getD (jd' - 1) 0)) * pk (FX (2 + e.1)) :=
          perm_eq (fun y => by simp only [ap_eq hpn, ap_eq (pT hd'81), mul_ap])
            (fun y => by simp only [ap_eq hpn, ap_eq (pT hπ81), mul_ap]) hpt
        rw [e2, mul_inv_cancel_right]
        exact subset_closure (Or.inl ⟨_, hπ, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hy]
      have h22 := hDlt _ he22
      have e3 : pk (FX (2 + e.1)) * (pk (EQ.T r.1) * pk (FX 0) ^ 1) =
          pk (EQ.T e.2.2) * (pk (EQ.T r.1) * pk (FX 0) ^ 1) * pk (FX (2 + e.1)) :=
        perm_eq (fun y => by simp only [hR1def, ap_eq hpn, mul_ap])
          (fun y => by simp only [hR1def, ap_eq hpn, ap_eq (pT h22), mul_ap])
          hRw
      rw [e3, mul_inv_cancel_right]
      exact (closure X).mul_mem (subset_closure (Or.inl ⟨_, he22, rfl⟩))
        (subset_closure (Or.inr rfl))
  · rw [hud]
    rw [hud] at hu1 hu3
    intro hmem
    rcases eq_one_or_of_mem_zpowers hu3 hu1 hmem with h | h | h
    · apply hu1
      have e4 : pk (EQ.T d) =
          (pk (FX (2 + e.1)))⁻¹ * (pk (FX (2 + e.1)) * pk (EQ.T d) * (pk (FX (2 + e.1)))⁻¹) *
            pk (FX (2 + e.1)) := by group
      rw [e4, h]
      group
    · exact hn1 (mul_inv_eq_iff_eq_mul.mp h)
    · exact hn2 (mul_inv_eq_iff_eq_mul.mp h)

theorem field_facts :     ∀ B : Subgroup (Equiv.Perm (Fin 2457)), B ≤ zpowers d4Phi ⊔ d4P → IsElemAbelian 3 B →
      Nat.card B = 27 → ¬ B ≤ d4P → ∀ u ∈ B, u ∈ d4P → u ≠ 1 →
      IsSolvable ↥(centralizer {u} ⊓ d4P) ∨
        ∃ n ∈ d4P, n ∈ normalizer (B : Set (Equiv.Perm (Fin 2457))) ∧ n * u * n⁻¹ ∉ zpowers u := by
  intro B hBG hB hB27 hBP u huB huP hu1
  obtain ⟨g, hgG, hg⟩ := exists_conj_le_sS hBG hB.isPGroup
  have hgi : g⁻¹ ∈ d4G := d4G.inv_mem hgG
  have hcP : ∀ {x}, x ∈ d4P → g⁻¹ * x * g ∈ d4P := by
    intro x hx
    simpa using conj_mem_d4P hgi hx
  set B' : Subgroup (Equiv.Perm (Fin 2457)) := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hmemB' : ∀ {x}, x ∈ B → g⁻¹ * x * g ∈ B' := by
    intro x hx
    exact ⟨_, hx, by simp⟩
  have key : ∀ y, y ∈ B ↔ g⁻¹ * y * g ∈ B' := fun y => by
    refine ⟨hmemB', fun ⟨w, hw, he⟩ => ?_⟩
    have : w = y := by
      have he' : g⁻¹ * w * g = g⁻¹ * y * g := by simpa using he
      simpa using he'
    exact this ▸ hw
  have hB'S : B' ≤ sS := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hg x hx
  have hB'c : Nat.card B' = 27 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB27]
  have hB'P : ¬ B' ≤ d4P := by
    intro h
    apply hBP
    intro x hx
    have := conj_mem_d4P hgG (h (hmemB' hx))
    simpa [mul_assoc] using this
  have hu'1 : g⁻¹ * u * g ≠ 1 := fun h => hu1 (by
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group)
  rcases field_in_sS hB'S (hB.map _) hB'c hB'P (hmemB' huB) (hcP huP) hu'1 with
    hs | ⟨n, hnP, hnN, hnu⟩
  · left
    have hu : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [hu]
    exact isSolvable_centralizer_conj (fun x hx => by simpa using conj_mem_d4P hgi hx) hs
  · right
    refine ⟨g * n * g⁻¹, conj_mem_d4P hgG hnP, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro b
      rw [key b, key (g * n * g⁻¹ * b * (g * n * g⁻¹)⁻¹), Subgroup.mem_normalizer_iff.mp hnN]
      constructor <;> intro h <;> simpa [mul_assoc] using h
    · intro hmem
      apply hnu
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      have : (g⁻¹ * u * g) ^ k = g⁻¹ * u ^ k * g := by
        rw [show g⁻¹ * u * g = MulAut.conj g⁻¹ u by simp, ← map_zpow]
        simp
      rw [this, hk]
      group

end CertificateChecks.KernelD4

end
