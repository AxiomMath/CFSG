module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import Certificates.Certificate89090
import CFSG.RankThree.PartTwo.J2Residue.KFactsCommon
import CFSG.RankThree.PartTwo.J2Residue.KJFixCore
import CFSG.GroupTheory.SmallFixedTwoGroup.PropBTransfer
import CFSG.GroupTheory.CentralizerMapMulEquiv
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k90uo3_card_J2 :
    Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 :=
  (Nat.card_congr CFSG.ComponentClassification.J2Cover.nativeEquivP.toEquiv).trans
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.card_GJ

private theorem k90uo3_fact : (604800 : ℕ).factorization 3 = 3 :=
  CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)

private theorem k90uo3_nine_dvd
    {a : CFSG.Blueprint.NativeSporadic.J2} (ha : orderOf a = 3) :
    9 ∣ Nat.card (Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.J2)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [k90uo3_card_J2]; norm_num)
  have hzp : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hScard : Nat.card S = 27 := by
    rw [Sylow.card_eq_multiplicity S, k90uo3_card_J2, k90uo3_fact]
    norm_num
  set Z : Subgroup CFSG.Blueprint.NativeSporadic.J2 :=
    (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ⊓ Subgroup.centralizer (S : Set CFSG.Blueprint.NativeSporadic.J2) with hZdef
  set K : Subgroup CFSG.Blueprint.NativeSporadic.J2 :=
    (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ⊓ Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.J2) with hKdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef]
    exact CFSG.RankThree.PartTwo.J2Residue.card_sylow_inf_centralizer_J2 S
  have hZK : Z ≤ K := by
    intro z hz
    rw [hZdef] at hz
    rw [hKdef]
    refine ⟨hz.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 a (hS (Subgroup.mem_zpowers a))).symm
  have hZlt : Z < K := by
    refine lt_of_le_of_ne hZK ?_
    intro hZeqK
    by_cases haC : a ∈ Subgroup.centralizer (S : Set CFSG.Blueprint.NativeSporadic.J2)
    · have hSle : (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ≤
          Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.J2) := by
        intro s hs
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp haC s hs)
      have hKeq : K = (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) := by
        rw [hKdef, inf_eq_left.mpr hSle]
      have hcardK : Nat.card K = 27 := by rw [hKeq, hScard]
      have h3 : Nat.card K = 3 := by rw [← hZeqK, hZcard]
      rw [hcardK] at h3
      norm_num at h3
    · have haK : a ∈ K := by
        rw [hKdef]
        exact ⟨hS (Subgroup.mem_zpowers a), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have haZ : a ∈ Z := by rw [hZeqK]; exact haK
      rw [hZdef] at haZ
      exact haC haZ.2
  have hKp : IsPGroup 3 K := by
    rw [hKdef]
    exact S.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hKp
  have h3lt : 3 < Nat.card K := by
    rw [← hZcard]
    exact Subgroup.card_lt_of_lt hZlt
  have h3lt' : (3 : ℕ) < 3 ^ k := by simpa [hk] using h3lt
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> norm_num at h3lt'
  have h9K : 9 ∣ Nat.card K := by
    rw [hk]
    exact dvd_trans (show 9 ∣ 3 ^ 2 by norm_num) (pow_dvd_pow 3 hk2)
  exact dvd_trans h9K (Subgroup.card_dvd_of_le inf_le_right)

private theorem k90uo3_exists_sylow
    {a : CFSG.Blueprint.NativeSporadic.J2} (ha : orderOf a = 3)
    (hC : (Nat.card (Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.J2))).factorization 3 ≠ 2) :
    ∃ S : Sylow 3 CFSG.Blueprint.NativeSporadic.J2, a ∈ (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ∧
      (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ≤ Subgroup.centralizer {a} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [k90uo3_card_J2]; norm_num)
  set C : Subgroup CFSG.Blueprint.NativeSporadic.J2 :=
    Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.J2) with hCdef
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have h9 : 9 ∣ Nat.card C := by
    rw [hCdef]
    exact k90uo3_nine_dvd ha
  have h2 : 2 ≤ (Nat.card C).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hC0).mp (by simpa using h9)
  have h3 : (Nat.card C).factorization 3 ≤ 3 := by
    have hdvd : Nat.card C ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := Subgroup.card_subgroup_dvd_card C
    have h := (Nat.factorization_le_iff_dvd hC0 (Nat.card_pos.ne' :
      Nat.card CFSG.Blueprint.NativeSporadic.J2 ≠ 0)).mpr hdvd 3
    rwa [k90uo3_card_J2, k90uo3_fact] at h
  have hfac : (Nat.card C).factorization 3 = 3 := by
    have hC' : (Nat.card C).factorization 3 ≠ 2 := by rw [hCdef]; exact hC
    omega
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := C)
  set Q' : Subgroup CFSG.Blueprint.NativeSporadic.J2 := (Q : Subgroup C).map C.subtype with hQ'def
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card CFSG.Blueprint.NativeSporadic.J2).factorization 3 := by
    rw [hQ'def, Subgroup.card_subtype, Sylow.card_eq_multiplicity Q, hfac, k90uo3_card_J2,
      k90uo3_fact]
  set aC : C := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with haCdef
  have haCord : orderOf aC = 3 := by
    rw [← orderOf_coe aC]
    exact ha
  set N : Subgroup C := Subgroup.zpowers aC with hNdef
  have hcomm : ∀ g : C, Commute g aC := fun g => by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  have haCcenter : aC ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr hcomm
  have hNcenter : N ≤ Subgroup.center C := by
    rw [hNdef]
    exact Subgroup.zpowers_le.mpr haCcenter
  have : N.Normal := Subgroup.normal_of_le_center hNcenter
  have hNp : IsPGroup 3 N := by
    rw [hNdef]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, haCord, pow_one])
  have hNQ : N ≤ Q := hNp.le_sylow_of_normal Q
  refine ⟨Sylow.ofCard Q' hQ'card, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact Subgroup.mem_map_of_mem C.subtype (hNQ (Subgroup.mem_zpowers aC))
  · rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le (Q : Subgroup C)

private theorem k90uo3_exists_zpowers_of_card_three {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (hA : Nat.card A = 3) :
    ∃ a : X, a ≠ 1 ∧ A = Subgroup.zpowers a ∧ orderOf a = 3 := by
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    norm_num at hA
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have haA : (a : X) ∈ A := a.2
  have haX1 : (a : X) ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨hAz, haord⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F09.eq_zpowers_of_card_eq_three hA haA haX1
  exact ⟨(a : X), haX1, hAz, haord⟩

private theorem k90uo3_card_centralizer_eq {X : Type} [Group X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) {A : Subgroup X} {a : X}
    (hA : A = Subgroup.zpowers a) :
    Nat.card (Subgroup.centralizer (A : Set X)) =
      Nat.card (Subgroup.centralizer ({e a} : Set CFSG.Blueprint.NativeSporadic.J2)) := by
  rw [hA, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    CFSG.GroupTheory.card_centralizer_singleton_mulEquiv e a]

private theorem k90uo3_exists_conj_of_zpowers {X : Type} [Group X]
    {e : X ≃* CFSG.Blueprint.NativeSporadic.J2} {A B : Subgroup X} {a b : X}
    (hA : A = Subgroup.zpowers a) (hB : B = Subgroup.zpowers b)
    (hg : ∃ g : CFSG.Blueprint.NativeSporadic.J2,
      (Subgroup.zpowers (e a)).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (e b)) :
    ∃ x : X, B = A.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g, hg⟩ := hg
  refine ⟨e.symm g, ?_⟩
  have hconj : (MulAut.conj g).toMonoidHom (e a) = g * e a * g⁻¹ :=
    MulAut.conj_apply g (e a)
  have hg' : Subgroup.zpowers (g * e a * g⁻¹) = Subgroup.zpowers (e b) := by
    rw [← hg, MonoidHom.map_zpowers, hconj]
  have hmap : Subgroup.zpowers (e.symm g * a * (e.symm g)⁻¹) = Subgroup.zpowers b := by
    have h := congrArg (fun H : Subgroup CFSG.Blueprint.NativeSporadic.J2 =>
      H.map e.symm.toMonoidHom) hg'
    simp only [MonoidHom.map_zpowers] at h
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.symm_apply_apply] using h
  rw [hA, hB, ← hmap, MonoidHom.map_zpowers]
  have hconj' : (MulAut.conj (e.symm g)).toMonoidHom a = e.symm g * a * (e.symm g)⁻¹ :=
    MulAut.conj_apply (e.symm g) a
  rw [hconj']

theorem j2OrderThree_890_holds :
    J2OrderThree_890 := by
  intro X _ _ hX A B hA hB hCA hCB
  obtain ⟨e₀⟩ := hX
  let e : X ≃* CFSG.Blueprint.NativeSporadic.J2 := e₀
  obtain ⟨a, ha1, hAz, haord⟩ := k90uo3_exists_zpowers_of_card_three hA
  obtain ⟨b, hb1, hBz, hbord⟩ := k90uo3_exists_zpowers_of_card_three hB
  have hca : (Nat.card (Subgroup.centralizer ({e a} :
      Set CFSG.Blueprint.NativeSporadic.J2))).factorization 3 ≠ 2 := by
    rw [← k90uo3_card_centralizer_eq e hAz]
    exact hCA
  have hea1 : e a ≠ 1 := fun h => ha1 (e.injective (by rw [h, map_one]))
  have heord : orderOf (e a) = 3 := by rw [MulEquiv.orderOf_eq, haord]
  obtain ⟨SA, hSA, hSAC⟩ := k90uo3_exists_sylow heord hca
  have hcb : (Nat.card (Subgroup.centralizer ({e b} :
      Set CFSG.Blueprint.NativeSporadic.J2))).factorization 3 ≠ 2 := by
    rw [← k90uo3_card_centralizer_eq e hBz]
    exact hCB
  have heb1 : e b ≠ 1 := fun h => hb1 (e.injective (by rw [h, map_one]))
  have hebord : orderOf (e b) = 3 := by rw [MulEquiv.orderOf_eq, hbord]
  obtain ⟨SB, hSB, hSBC⟩ := k90uo3_exists_sylow hebord hcb
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.J2Residue.exists_map_conj_zpowers_eq_J2 hea1 ⟨SA, hSA, hSAC⟩ heb1
      ⟨SB, hSB, hSBC⟩
  exact k90uo3_exists_conj_of_zpowers hAz hBz ⟨g, hg⟩

private theorem k90ufp_two_nsmul {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (w : V) :
    (2 : ℕ) • w = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 w, ZMod.natCast_self 2, zero_smul]

private theorem k90ufp_nsmul_mod_two {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (n : ℕ)
    (w : V) : n • w = (n % 2) • w :=
  nsmul_eq_mod_nsmul n (k90ufp_two_nsmul w)

private def k90ufp_u {X V : Type} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : X →* (V ≃ₗ[ZMod 2] V)) (y : X) (h : X) (v₀ : V) : V :=
  ρ h v₀ + ρ y (ρ h v₀) + ρ (y ^ 2) (ρ h v₀)

private theorem k90ufp_fixed {X V : Type} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : X →* (V ≃ₗ[ZMod 2] V)) {y : X} (hy : y ^ 3 = 1) (w : V) :
    ρ y (w + ρ y w + ρ (y ^ 2) w) = w + ρ y w + ρ (y ^ 2) w := by
  have h1 : ρ y (ρ y w) = ρ (y ^ 2) w := by
    rw [← LinearEquiv.mul_apply, ← map_mul, ← pow_two]
  have h2 : ρ y (ρ (y ^ 2) w) = w := by
    rw [← LinearEquiv.mul_apply, ← map_mul, ← pow_succ' y 2]
    rw [show y ^ (2 + 1) = 1 by simpa using hy]
    simp
  rw [map_add, map_add, h1, h2]
  abel

private theorem k90ufp_sum_flatMap {X V : Type} [Group X] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : X →* (V ≃ₗ[ZMod 2] V)) (y : X) (v₀ : V) (l : List (X × X)) :
    ((l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).map
        fun g => ρ g v₀).sum
      = (l.map fun p => ρ p.1 (k90ufp_u ρ y p.2 v₀)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ih]
    rw [add_right_cancel_iff]
    simp only [k90ufp_u, map_add, map_mul, LinearEquiv.mul_apply]
    abel

private theorem k90ufp_sum_eq {X V : Type} [Group X] [DecidableEq X] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : X →* (V ≃ₗ[ZMod 2] V)) (y : X) (v₀ : V) (l : List (X × X))
    (hl : ∀ g : X,
      (l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).count g % 2 =
        if g = 1 then 1 else 0) :
    ((l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).map
        fun g => ρ g v₀).sum = v₀ := by
  rw [Finset.sum_list_map_count]
  trans ∑ m ∈ (l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).toFinset,
      (if m = 1 then ρ m v₀ else 0)
  · exact Finset.sum_congr rfl (fun m _ => by
      rw [k90ufp_nsmul_mod_two, hl m]
      by_cases h : m = 1 <;> simp [h])
  · have hmem : (1 : X) ∈
        (l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).toFinset := by
      rw [List.mem_toFinset]
      by_contra h
      have hc :
          (l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).count 1 = 0 :=
        List.count_eq_zero_of_not_mem h
      have h1 := hl 1
      rw [hc] at h1
      rw [if_pos rfl, Nat.zero_mod] at h1
      exact Nat.zero_ne_one h1
    simp [hmem]

theorem r890u_exists_fixed_of_parity {X V : Type} [Group X] [DecidableEq X] [AddCommGroup V]
    [Module (ZMod 2) V] [Nontrivial V] (ρ : X →* (V ≃ₗ[ZMod 2] V)) {y : X} (hy : y ^ 3 = 1)
    (l : List (X × X))
    (hl : ∀ g : X,
      (l.flatMap fun p => [p.1 * p.2, p.1 * y * p.2, p.1 * y ^ 2 * p.2]).count g % 2 =
        if g = 1 then 1 else 0) :
    ∃ v : V, v ≠ 0 ∧ ρ y v = v := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  by_contra hne
  have hne' : ∀ v : V, v ≠ 0 → ρ y v ≠ v := fun v hv hvfix => hne ⟨v, hv, hvfix⟩
  have hzero : ∀ p ∈ l, k90ufp_u ρ y p.2 v₀ = 0 := by
    intro p _
    by_contra h
    exact hne' (k90ufp_u ρ y p.2 v₀) h
      (by simpa only [k90ufp_u] using k90ufp_fixed ρ hy (ρ p.2 v₀))
  have hsum0 : (l.map fun p => ρ p.1 (k90ufp_u ρ y p.2 v₀)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [hzero q hq, map_zero]
  have h3 := k90ufp_sum_eq ρ y v₀ l hl
  have h2 := k90ufp_sum_flatMap ρ y v₀ l
  rw [h2, hsum0] at h3
  exact hv₀ h3.symm

open CFSG.RankThree.PartTwo.J2Residue CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private noncomputable def k90utb_y0 : GJ := C280.wordP C89090.y0W

open CFSG.RankThree.PartTwo.J2Residue CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private noncomputable def k90utb_L : List (GJ × GJ) :=
  C89090.pairW.map fun p => (C280.wordP p.1, C280.wordP p.2)

open CFSG.Monster.B.Co2 CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_rep_y0 :
    Rep 315 (C280.wordA C89090.y0W) k90utb_y0.1 :=
  C280.rep_wordA C89090.y0W

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_pow_three :
    k90utb_y0 ^ 3 = 1 := by
  have hA := Certificates.certificate89090.1
  simp only [C89090.check89090A, C89090.y0A, C89090.prods89090, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, beq_iff_eq] at hA
  obtain ⟨⟨h3, -⟩, -⟩ := hA
  have h := rep_mul (C280.rep_wordA C89090.y0W)
    (rep_mul (C280.rep_wordA C89090.y0W) (C280.rep_wordA C89090.y0W))
  have he : C280.wordP C89090.y0W * (C280.wordP C89090.y0W * C280.wordP C89090.y0W) =
      (C280.wordP C89090.y0W) ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
  rw [he] at h
  exact eq_of_rep h rep_one h3

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_specA :
    eqA 315 (compA 315 (C280.wordA C89090.y0W)
        (compA 315 (C280.wordA C89090.y0W) (C280.wordA C89090.y0W))) (idA 315) = true ∧
      (∃ t ∈ C89090.prods89090 (), eqA 315 t (idA 315) = true) ∧
      (∀ t ∈ C89090.prods89090 (),
        (C89090.prods89090 ()).countP (fun u => eqA 315 u t) % 2 =
          (if eqA 315 t (idA 315) then 1 else 0)) := by
  have hA := Certificates.certificate89090.1
  simp only [C89090.check89090A, C89090.y0A, C89090.prods89090, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, beq_iff_eq] at hA
  obtain ⟨⟨h3, hany⟩, hall⟩ := hA
  exact ⟨h3, hany, hall⟩

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_specB :
    ∀ j ∈ List.range 27,
      inZ (cP3.pts[j]!) = true ∨
        ∃ c ∈ C89090.conjW.map C280.wordA,
          eqA 315 (compA 315 c (C280.wordA C89090.y0W))
            (compA 315 cP3.pts[j]! c) = true := by
  have hB := Certificates.certificate89090.2
  simp only [C89090.check89090B, C89090.y0A, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true] at hB
  exact hB

open CFSG.RankThree.PartTwo.J2Residue CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private noncomputable def k90utb_flat : List GJ :=
  k90utb_L.flatMap fun p => [p.1 * p.2, p.1 * k90utb_y0 * p.2, p.1 * k90utb_y0 ^ 2 * p.2]

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_count {T : List (Array Nat)} {L : List GJ} {s : Array Nat} {g : GJ}
    (h : List.Forall₂ (fun t g => Rep 315 t g.1) T L) (hs : Rep 315 s g.1) :
    L.countP (fun x => decide (x = g)) = T.countP (fun t => eqA 315 t s) := by
  induction h with
  | nil => rfl
  | @cons a b as bs hhead htail ih =>
    rw [List.countP_cons, List.countP_cons, ih]
    congr 1
    have he : eqA 315 a s = decide (b = g) := by
      rw [Bool.eq_iff_iff]
      simpa using (eqA_iff hhead hs)
    rw [he]

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
private theorem k90utb_forall₂ :
    List.Forall₂ (fun t g => Rep 315 t g.1) (C89090.prods89090 ()) k90utb_flat := by
  simp only [C89090.prods89090, C89090.y0A, k90utb_flat, k90utb_L, k90utb_y0]
  set ps := C89090.pairW
  induction ps with
  | nil => exact List.Forall₂.nil
  | cons p ps ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons]
    refine List.rel_append ?_ ih
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
    · exact rep_mul (C280.rep_wordA p.1) (C280.rep_wordA p.2)
    · exact rep_mul (rep_mul (C280.rep_wordA p.1) (C280.rep_wordA C89090.y0W))
        (C280.rep_wordA p.2)
    · show Rep 315 (compA 315 (compA 315 (C280.wordA p.1)
          (compA 315 (C280.wordA C89090.y0W) (C280.wordA C89090.y0W))) (C280.wordA p.2))
        ((C280.wordP p.1 * (C280.wordP C89090.y0W) ^ 2 * C280.wordP p.2).1)
      rw [pow_two]
      exact rep_mul (rep_mul (C280.rep_wordA p.1)
        (rep_mul (C280.rep_wordA C89090.y0W) (C280.rep_wordA C89090.y0W)))
        (C280.rep_wordA p.2)

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.J2Residue
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
theorem r890u_threeB_fix_model
    {w : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ}
    (hw : w ∈ CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3)
    (hwz : w ∉ Subgroup.zpowers CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zJ)
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (ρ : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ →* (V ≃ₗ[ZMod 2] V)) :
    ∃ v : V, v ≠ 0 ∧ ρ w v = v := by
  have hy0 : k90utb_y0 ^ 3 = 1 := k90utb_pow_three
  obtain ⟨-, hAny, hAll⟩ := k90utb_specA
  have hfor := k90utb_forall₂
  have hL : ∀ g : GJ,
      k90utb_flat.countP (fun x => decide (x = g)) % 2 = if g = 1 then 1 else 0 := by
    intro g
    by_cases hg : g ∈ k90utb_flat
    · obtain ⟨⟨i, hi⟩, hn⟩ := List.get_of_mem hg
      have hnT : i < (C89090.prods89090 ()).length := by
        rw [hfor.length_eq]; exact hi
      have hrep : Rep 315 ((C89090.prods89090 ()).get ⟨i, hnT⟩) g.1 := by
        have hg' := hfor.get hnT hi
        rw [hn] at hg'
        exact hg'
      have hcnt := k90utb_count hfor hrep
      have hall := hAll ((C89090.prods89090 ()).get ⟨i, hnT⟩) (List.get_mem _ _)
      have hiff : eqA 315 ((C89090.prods89090 ()).get ⟨i, hnT⟩) (idA 315) = true ↔
          g = 1 := by
        rw [eqA_iff hrep rep_one]
        exact Subtype.ext_iff.symm
      have hif : (if eqA 315 ((C89090.prods89090 ()).get ⟨i, hnT⟩) (idA 315) then 1 else 0) =
          (if g = 1 then 1 else 0) := by
        by_cases hg1 : g = 1
        · rw [if_pos (hiff.2 hg1), if_pos hg1]
        · have hfalse : eqA 315 ((C89090.prods89090 ()).get ⟨i, hnT⟩) (idA 315) = false := by
            rw [Bool.eq_false_iff]
            intro hc
            exact hg1 (hiff.1 hc)
          rw [if_neg (Bool.eq_false_iff.1 hfalse), if_neg hg1]
      calc k90utb_flat.countP (fun x => decide (x = g)) % 2
          = (C89090.prods89090 ()).countP
              (fun t => eqA 315 t ((C89090.prods89090 ()).get ⟨i, hnT⟩)) % 2 := by rw [hcnt]
        _ = (if eqA 315 ((C89090.prods89090 ()).get ⟨i, hnT⟩) (idA 315) then 1 else 0) := hall
        _ = (if g = 1 then 1 else 0) := hif
    · have hzero : k90utb_flat.countP (fun x => decide (x = g)) = 0 := by
        apply List.countP_eq_zero.2
        intro x hx
        simp only [decide_eq_true_eq]
        exact fun hxg => hg (hxg ▸ hx)
      rw [hzero]
      have h1L : (1 : GJ) ∈ k90utb_flat := by
        obtain ⟨t, ht, ht1⟩ := hAny
        obtain ⟨⟨i, hiT⟩, htget⟩ := List.get_of_mem ht
        have hiL : i < k90utb_flat.length := by
          rw [← hfor.length_eq]; exact hiT
        have hrep := hfor.get hiT hiL
        rw [htget] at hrep
        have hL1 : k90utb_flat.get ⟨i, hiL⟩ = 1 := eq_of_rep hrep rep_one ht1
        exact hL1 ▸ List.get_mem _ _
      have hg1 : g ≠ 1 := fun h => hg (h ▸ h1L)
      rw [if_neg hg1]
  obtain ⟨v, hv0, hv⟩ := r890u_exists_fixed_of_parity ρ hy0 k90utb_L (by
    intro g
    change k90utb_flat.countP (fun x => decide (x = g)) % 2 = if g = 1 then 1 else 0
    exact hL g)
  obtain ⟨j, hj, hwj⟩ := rep_mem_P3 hw
  rcases k90utb_specB j (List.mem_range.2 hj) with hinZ | ⟨c, hc, hceq⟩
  · have hw' : w ∈ zpowers zJ := by
      simp only [inZ, Bool.or_eq_true, or_assoc] at hinZ
      rcases hinZ with h1 | h2 | h3
      · have hw1 : w = 1 := eq_of_rep hwj rep_one h1
        rw [hw1]; exact one_mem _
      · have hw2 : w = zJ := eq_of_rep hwj rep_z h2
        rw [hw2]; exact mem_zpowers _
      · have hw3 : w = zJ * zJ := eq_of_rep hwj (rep_mul rep_z rep_z) h3
        rw [hw3]; exact mul_mem (mem_zpowers _) (mem_zpowers _)
    exact absurd hw' hwz
  · obtain ⟨cw, -, rfl⟩ := List.mem_map.1 hc
    have hrepc : Rep 315 (C280.wordA cw) (C280.wordP cw).1 := C280.rep_wordA cw
    have heq : C280.wordP cw * k90utb_y0 = w * C280.wordP cw :=
      eq_of_rep (rep_mul hrepc k90utb_rep_y0) (rep_mul hwj hrepc) hceq
    refine ⟨ρ (C280.wordP cw) v, ?_, ?_⟩
    · exact (ρ (C280.wordP cw)).map_ne_zero_iff.2 hv0
    · calc ρ w (ρ (C280.wordP cw) v)
          = (ρ w * ρ (C280.wordP cw)) v := (LinearEquiv.mul_apply _ _ _).symm
        _ = ρ (w * C280.wordP cw) v := by rw [← map_mul]
        _ = ρ (C280.wordP cw * k90utb_y0) v := by rw [← heq]
        _ = (ρ (C280.wordP cw) * ρ k90utb_y0) v := by rw [map_mul]
        _ = ρ (C280.wordP cw) (ρ k90utb_y0 v) := LinearEquiv.mul_apply _ _ _
        _ = ρ (C280.wordP cw) v := by rw [hv]
open scoped Pointwise

private noncomputable def k90ufx_sylowP3 :
    Sylow 3 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sylow.ofCard CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 ?_
  rw [CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.card_P3,
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.card_GJ,
    CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
  norm_num

private theorem k90ufx_conj_into_P3
    {t : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ} (ht : orderOf t = 3) :
    ∃ c : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ,
      c * t * c⁻¹ ∈ CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num) :
    IsPGroup 3 (Subgroup.zpowers t)).exists_le_sylow
  have : Finite (Sylow 3 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) :=
    Sylow.finite_of_finiteIndex S
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq
    (CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) S k90ufx_sylowP3
  refine ⟨c, ?_⟩
  have htS : t ∈ S := hS (Subgroup.mem_zpowers t)
  have hmem : c * t * c⁻¹ ∈ (c • S : Sylow 3 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) :=
    show c * t * c⁻¹ ∈ (MulAut.conj c • (S : Subgroup
        CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) : Subgroup
        CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) from by
      simpa only [MulAut.smul_def, MulAut.conj_apply] using
        (Subgroup.smul_mem_pointwise_smul t (MulAut.conj c)
          (S : Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) htS)
  rwa [hc] at hmem

private theorem k90ufx_not_mem_zpowers
    {w : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ}
    (hC : (Nat.card (centralizer ({w} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ))).factorization
      3 = 2) :
    w ∉ Subgroup.zpowers CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zJ := by
  intro hwz
  have hz_eq : Subgroup.zpowers CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zJ =
      CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 ⊓
        centralizer (CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 : Set _) := by
    rw [CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.z_eq,
      ← CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.inf_centralizer_P3]
  have hwc : w ∈ centralizer (CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 : Set _) :=
    (hz_eq ▸ hwz).2
  have hle : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 ≤ centralizer ({w} : Set _) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hwc p hp
  have h27 : 27 ∣ Nat.card (centralizer ({w} : Set _)) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.card_P3] at h
  have hne : Nat.card (centralizer ({w} : Set _)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have h3 : 3 ≤ (Nat.card (centralizer ({w} : Set _))).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1
      (by simpa only [show (3 : ℕ) ^ 3 = 27 by norm_num] using h27)
  omega

theorem j2ThreeBFix_890_holds :
    J2ThreeBFix_890 := by
  intro X _ _ hX y hy hC V _ _ _ ρ hV _
  have : Nontrivial V := hV
  obtain ⟨e⟩ := hX
  let φ : X ≃* CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ :=
    e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have ht : orderOf (φ y) = 3 := (MulEquiv.orderOf_eq φ y).trans hy
  obtain ⟨c, hcP3⟩ := k90ufx_conj_into_P3 ht
  let w : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ := c * φ y * c⁻¹
  have hwP : w ∈ CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.P3 := hcP3
  have hcard_eq : Nat.card (centralizer ({w} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ)) =
      Nat.card (centralizer ({y} : Set X)) := by
    have h1 : Nat.card (centralizer ({w} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ)) =
        Nat.card (centralizer ({φ y} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ)) := by
      change Nat.card (centralizer ({c * φ y * c⁻¹} : Set
        CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ)) =
        Nat.card (centralizer ({φ y} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ))
      have := CFSG.GroupTheory.SmallFixedTwoGroup.card_centralizer_conj (E :=
        CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ) c⁻¹ (φ y)
      simpa only [inv_inv] using this
    have h2 : Nat.card (centralizer ({φ y} : Set CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ)) =
        Nat.card (centralizer ({y} : Set X)) :=
      (CFSG.GroupTheory.card_centralizer_singleton_mulEquiv φ y).symm
    rw [h1, h2]
  have hCw : (Nat.card (centralizer ({w} : Set
      CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ))).factorization 3 = 2 := by
    rw [hcard_eq]
    exact hC
  have hwz : w ∉ Subgroup.zpowers CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zJ :=
    k90ufx_not_mem_zpowers hCw
  obtain ⟨v, hv0, hv⟩ :=
    r890u_threeB_fix_model hwP hwz V (ρ.comp φ.symm.toMonoidHom)
  have hsymmw : φ.symm w =
      φ.symm c * y * (φ.symm c)⁻¹ := by
    change φ.symm (c * φ y * c⁻¹) = φ.symm c * y * (φ.symm c)⁻¹
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hv' : ρ (φ.symm c * y * (φ.symm c)⁻¹) v = v := by
    have hvraw : ρ (φ.symm w) v = v := by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hv
    simpa only [hsymmw] using hvraw
  refine ⟨(ρ (φ.symm c))⁻¹ v, ?_, ?_⟩
  · exact ((ρ (φ.symm c))⁻¹).map_ne_zero_iff.mpr hv0
  · have hmap : ρ (φ.symm c * y * (φ.symm c)⁻¹) =
        ρ (φ.symm c) * ρ y * (ρ (φ.symm c))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have h3 : ρ (φ.symm c) (ρ y ((ρ (φ.symm c))⁻¹ v)) = v := by
      have h := hv'
      rw [hmap, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
      exact h
    have h4 := congrArg (fun x => (ρ (φ.symm c))⁻¹ x) h3
    simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
