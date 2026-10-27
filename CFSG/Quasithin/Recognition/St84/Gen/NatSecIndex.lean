module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Recognition.St84.Gen.S1Five
import CFSG.Quasithin.Recognition.St84.Gen.S1FiveNat
import CFSG.GroupTheory.ConjQuot
import CFSG.GroupTheory.PGroup.OmegaComm
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Gen
import CFSG.Quasithin.Recognition.St84.Sec67A
import CFSG.CGT.Timmesfeld75.Lemma27

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mulAut_eq_one_of_card_two {N : Type*} [Group N] (hN : Nat.card N = 2)
    (f : MulAut N) : f = 1 := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · have hfx : f x ≠ 1 := by
      intro h
      apply hx
      exact f.injective (by rw [h, map_one])
    calc f x = y := huniq (f x) hfx
      _ = x := (huniq x hx).symm
      _ = (1 : MulAut N) x := rfl

private theorem mulAut_eq_one_of_odd_of_central_quotient {Q : Type*} [Group Q]
    {A : Subgroup Q} (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (g : MulAut Q) (hg : Odd (orderOf g))
    (hfixA : ∀ a ∈ A, g a = a) (hquot : ∀ q : Q, g q / q ∈ A) : g = 1 := by
  have hsq : g ^ 2 = 1 := by
    ext q
    set a : Q := g q / q with ha
    have haA : a ∈ A := hquot q
    have hcong : g q = a * q := by rw [ha, div_mul_cancel]
    calc (g ^ 2) q = g (g q) := by rw [pow_two, MulAut.mul_apply]
      _ = g (a * q) := by rw [hcong]
      _ = g a * g q := map_mul g _ _
      _ = a * g q := by rw [hfixA a haA]
      _ = a * (a * q) := by rw [hcong]
      _ = (a * a) * q := by group
      _ = q := by rw [← pow_two, hA2 a haA, one_mul]
  obtain ⟨k, hk⟩ := hg
  calc g = (g ^ 2) ^ k * g := by rw [hsq, one_pow, one_mul]
    _ = g ^ (2 * k) * g := by rw [pow_mul]
    _ = g ^ (2 * k + 1) := by rw [pow_succ]
    _ = 1 := by rw [← hk, pow_orderOf_eq_one]

private theorem mulAut_eq_one_of_card_le_two {Q : Type} [Group Q] [Finite Q]
    (hQ : Nat.card Q ≤ 2) (f : MulAut Q) : f = 1 := by
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hQ' : Nat.card Q = 1 ∨ Nat.card Q = 2 := by
    have := hQ
    omega
  rcases hQ' with h1 | h2
  · haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp h1).1
    ext x
    exact Subsingleton.elim _ _
  · exact mulAut_eq_one_of_card_two h2 f

private theorem eq_one_of_isL2Quot_of_group {P : Type} [Group P] [Finite P] {Q : Type}
    [Group Q] [Finite Q] {n f : ℕ} (hn : 2 ≤ n) (hfn : f < 2 * n)
    (hP : IsL2Quot n P) (ρ : P →* MulAut Q) (hQ : Nat.card Q = 2 ^ f) : ρ = 1 := by
  obtain ⟨e⟩ := hP
  let π : P →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom
  have hπinj : Function.Injective π := e.injective
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hπs : Function.Surjective π := e.surjective
  have : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with hb | ht
  · have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxm : π x ∈ ρ.ker.map π := ⟨x, hx, rfl⟩
      rw [hb] at hxm
      have hx0 : π x = 1 := Subgroup.mem_bot.mp hxm
      apply e.injective
      rw [map_one]
      simpa [π] using hx0
    by_cases hn3 : n = 3
    · subst hn3
      have := CGT.Timmesfeld75.lemma27_psl2_eight π hπs ρ hρinj hQ
      omega
    · have hcard : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card P := by
        rw [Nat.card_congr e.toEquiv, card_psl_two_gf2 n (by omega)]
        rw [show (2 ^ n) ^ 2 = 4 ^ n by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num]
      have hle := CGT.Timmesfeld75.lemma27_psl2 hn hn3 hcard ρ hρinj hQ
      have hf' : f < 2 * n := hfn
      omega
  · have hkertop : ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxm : π x ∈ ρ.ker.map π := by rw [ht]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hxm
      have hkx' : k = x := hπinj hkx
      simpa [hkx'] using hk
    refine MonoidHom.ext fun x => ?_
    have hx : ρ x = 1 := by
      have hmem : x ∈ ρ.ker := by rw [hkertop]; exact Subgroup.mem_top x
      simpa using hmem
    exact hx

private theorem action_eq_one_of_card_lt {L : Subgroup G} [Finite ↥L] {n : ℕ}
    {Q : Type} [Group Q] [Finite Q] (hn : 1 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥L)) (hQ2 : IsPGroup 2 Q)
    (ρ : ↥L →* MulAut Q) (hcard : Nat.card Q < 2 ^ (2 * n))
    (hcore : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → ρ p = 1) : ρ = 1 := by
  rcases lt_or_ge n 2 with hn1 | hn2
  · have hn' : 1 ≤ n := hn
    have hn_eq : n = 1 := by omega
    subst hn_eq
    have hcard4 : Nat.card Q < 4 := by simpa using hcard
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hklt : k < 2 := by
      rw [hk] at hcard4
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hcard4)
    have hQle : Nat.card Q ≤ 2 := by
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hk]; norm_num
      · rw [hk]; norm_num
    ext l x
    have h := congrArg (fun f : MulAut Q => f x) (mulAut_eq_one_of_card_le_two hQle (ρ l))
    simpa using h
  · let P := oTwoQuot ↥L
    let π : ↥L →* P := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    haveI : Finite P := inferInstance
    let ρP : P →* MulAut Q :=
      QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ (fun x hx => hcore x hx)
    obtain ⟨f, hf⟩ := hQ2.exists_card_eq
    have hfn : f < 2 * n := by
      rw [hf] at hcard
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcard
    have hρP : ρP = 1 := eq_one_of_isL2Quot_of_group hn2 hfn hq ρP hf
    ext l x
    have h := congrArg (fun φ : P →* MulAut Q => φ (π l)) hρP
    have hρl : ρ l = 1 := by
      have h2 : ρP (π l) = ρ l := by
        change QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ
          (fun x hx => hcore x hx) (QuotientGroup.mk l) = ρ l
        exact QuotientGroup.lift_mk' (N := CFSG.pCore 2 ↥L) (φ := ρ)
          (fun x hx => hcore x hx) l
      simpa [h2] using h
    exact congrArg (fun f : MulAut Q => f x) hρl

theorem comm_le_of_relIndex_lt_two_pow {L E N : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hNE : N ≤ E)
    (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hE : IsPGroup 2 E)
    (hcore : ⁅E, pCoreOf 2 L⁆ ≤ N) (h0 : N.relIndex E ≠ 0)
    (hlt : N.relIndex E < 2 ^ (2 * n)) :
    ⁅E, L⁆ ≤ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNnormal : (N.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hEN
  let Q := ↥E ⧸ N.subgroupOf E
  have hQ2 : IsPGroup 2 Q := hE.to_quotient (N.subgroupOf E)
  let ρ : ↥L →* MulAut Q := CFSG.GroupTheory.conjQuotHom hLE hLN
  have hQcard : Nat.card Q = N.relIndex E := rfl
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; exact h0)
  rcases lt_or_ge n 2 with hn1 | hn2
  · have hn' : 1 ≤ n := hn
    have hn_eq : n = 1 := by omega
    subst hn_eq
    have hrel : N.relIndex E = 1 ∨ N.relIndex E = 2 := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      have hklt : k < 2 := by
        have hlt' : Nat.card Q < 2 ^ (2 * 1) := by rwa [hQcard]
        rw [hk] at hlt'
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlt')
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · left; rw [← hQcard, hk]; norm_num
      · right; rw [← hQcard, hk]; norm_num
    rw [Subgroup.commutator_le]
    intro e he l hl
    have hmem := CFSG.Quasithin.S15223.commutator_mem_of_relIndex_le_two
      (N := N) (Q := E) hrel (hLN hl) (hLE hl) he
    rw [commutatorElement_def]
    have hinv : (l * e * l⁻¹ * e⁻¹)⁻¹ ∈ N := N.inv_mem hmem
    simpa [commutatorElement_def, mul_assoc] using hinv
  · have hcoreKer : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → ρ p = 1 := by
      intro p hp
      ext q
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
      have hpO : (p : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff (H := L) p).mpr hp
      have hcomm : ⁅(e : G), (p : G)⁆ ∈ N :=
        hcore (Subgroup.commutator_mem_commutator e.2 hpO)
      have hcomm' : ⁅(p : G), (e : G)⁆ ∈ N := by
        rw [← commutatorElement_inv (g₁ := (e : G)) (g₂ := (p : G))]
        exact N.inv_mem hcomm
      have hfix : ρ p (QuotientGroup.mk e) = QuotientGroup.mk e := by
        rw [show ρ p = CFSG.GroupTheory.conjQuotAut (hLE p.2) (hLN p.2) from rfl]
        rw [CFSG.GroupTheory.conjQuotAut_mk, QuotientGroup.eq_iff_div_mem]
        exact Subgroup.mem_subgroupOf.mpr (by
          simpa [div_eq_mul_inv, commutatorElement_def] using hcomm')
      simpa using hfix
    have hcard : Nat.card Q < 2 ^ (2 * n) := by
      rw [hQcard]
      exact hlt
    have hρ : ρ = 1 := action_eq_one_of_card_lt hn hq hQ2 ρ hcard hcoreKer
    rw [Subgroup.commutator_le]
    intro e he l hl
    have h1 : ρ ⟨l, hl⟩ = 1 := by rw [hρ]; rfl
    have h2 : ρ ⟨l, hl⟩ (QuotientGroup.mk ⟨e, he⟩) = QuotientGroup.mk ⟨e, he⟩ := by
      rw [h1]; rfl
    have h2' : QuotientGroup.mk' (N.subgroupOf E)
        (⟨l * e * l⁻¹, (hLE hl e).mp he⟩ : ↥E) =
        QuotientGroup.mk' (N.subgroupOf E) ⟨e, he⟩ := by
      have h3 := h2
      rw [show ρ ⟨l, hl⟩ = CFSG.GroupTheory.conjQuotAut (hLE hl) (hLN hl) from rfl,
        CFSG.GroupTheory.conjQuotAut_mk] at h3
      simpa using h3
    have hmem : ((⟨l * e * l⁻¹, (hLE hl e).mp he⟩ : ↥E) / ⟨e, he⟩) ∈ N.subgroupOf E :=
      (QuotientGroup.eq_iff_div_mem).mp h2'
    have hmemG : l * e * l⁻¹ * e⁻¹ ∈ N := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [commutatorElement_def]
    simpa [mul_assoc] using N.inv_mem hmemG

private theorem map_eq_self_of_forall_mem_of_finite {Q : Type} [Group Q] {A : Subgroup Q}
    [Finite A] (f : MulAut Q) (hf : ∀ a ∈ A, f a ∈ A) : A.map (f : Q →* Q) = A := by
  have hle : A.map (f : Q →* Q) ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact hf a ha
  have hcard : Nat.card (A.map (f : Q →* Q)) = Nat.card A :=
    Subgroup.card_map_of_injective f.injective
  refine le_antisymm hle ?_
  rw [Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])]

private noncomputable def mulAutRestrict {Q : Type} [Group Q] {A : Subgroup Q} [Finite A]
    (f : MulAut Q) (hf : ∀ a ∈ A, f a ∈ A) : MulAut A where
  toFun a := ⟨f a, hf a a.2⟩
  invFun a := ⟨f.symm a, by
    have hmap := map_eq_self_of_forall_mem_of_finite f hf
    have ha : (a : Q) ∈ A.map (f : Q →* Q) := by rw [hmap]; exact a.2
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
    rw [← hba]
    change f.symm (f b) ∈ A
    rw [f.symm_apply_apply]
    exact hb⟩
  left_inv a := Subtype.ext (f.symm_apply_apply (a : Q))
  right_inv a := Subtype.ext (f.apply_symm_apply (a : Q))
  map_mul' a b := Subtype.ext (map_mul f (a : Q) (b : Q))

private noncomputable def restrictAction {L' Q : Type} [Group L'] [Group Q]
    {A : Subgroup Q} [Finite A] (ρ : L' →* MulAut Q)
    (hA : ∀ l : L', ∀ a ∈ A, ρ l a ∈ A) : L' →* MulAut A where
  toFun l := mulAutRestrict (ρ l) (hA l)
  map_one' := by
    ext a
    change ρ 1 (a : Q) = (a : Q)
    simp
  map_mul' l m := by
    ext a
    change (ρ (l * m)) (a : Q) = (ρ l) ((ρ m) (a : Q))
    rw [map_mul, MulAut.mul_apply]

private noncomputable def quotientAction {L' Q : Type} [Group L'] [Group Q] [Finite Q]
    {A : Subgroup Q} [A.Normal] (ρ : L' →* MulAut Q)
    (hA : ∀ l : L', ∀ a ∈ A, ρ l a ∈ A) : L' →* MulAut (Q ⧸ A) where
  toFun l := QuotientGroup.congr A A (ρ l) (map_eq_self_of_forall_mem_of_finite (ρ l) (hA l))
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on
    · simp
  map_mul' l m := by
    ext q
    induction q using QuotientGroup.induction_on
    · simp [QuotientGroup.congr_mk, MulAut.mul_apply]

@[simp]
private theorem quotientAction_mk {L' Q : Type} [Group L'] [Group Q] [Finite Q]
    {A : Subgroup Q} [A.Normal] (ρ : L' →* MulAut Q)
    (hA : ∀ l : L', ∀ a ∈ A, ρ l a ∈ A) (l : L') (q : Q) :
    quotientAction ρ hA l (QuotientGroup.mk q) = QuotientGroup.mk (ρ l q) := rfl

private theorem exists_fixed_central_subgroup {Q L' : Type} [Group Q] [Group L'] [Finite Q]
    [Finite L'] (ρ : L' →* MulAut Q) (P : Subgroup L') [P.Normal]
    (hQ2 : IsPGroup 2 Q) (hP2 : IsPGroup 2 P) (hQnt : Nontrivial Q) :
    ∃ A : Subgroup Q, A ≠ ⊥ ∧ A ≤ Subgroup.center Q ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
      (∀ l : L', ∀ a ∈ A, ρ l a ∈ A) ∧ (∀ p ∈ P, ∀ a ∈ A, ρ p a = a) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := hQnt
  let Z : Subgroup Q := Subgroup.center Q
  let Ω : Subgroup ↥Z := CFSG.omega₁ ↥Z (p := 2)
  let Z0 : Subgroup Q := Ω.map Z.subtype
  have hZ0char : Z0.Characteristic := by
    dsimp only [Z0, Ω, Z]
    letI : (CFSG.omega₁ ↥(Subgroup.center Q) (p := 2)).Characteristic :=
      CFSG.omega₁_characteristic ↥(Subgroup.center Q)
    infer_instance
  have hZ0sq : ∀ z ∈ Z0, z ^ 2 = 1 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : ∀ a b : ↥Z, a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp a.2 (b : Q)).symm
    have hw2 : w ^ 2 = 1 := (CFSG.mem_omega₁_iff_of_comm hcomm).mp hw
    simpa using congrArg (fun x : ↥Z => (x : Q)) hw2
  have hZ0center : Z0 ≤ Subgroup.center Q := by
    rintro z ⟨w, hw, rfl⟩
    exact w.2
  have hZne : Z ≠ ⊥ := ne_of_gt hQ2.bot_lt_center
  have hdvdZ : 2 ∣ Nat.card ↥Z := by
    obtain ⟨k, hk⟩ := (hQ2.to_subgroup Z).exists_card_eq
    have hkpos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      exact hZne (Z.eq_bot_of_card_eq hk)
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  have hZ0ne : Z0 ≠ ⊥ := by
    have h := CFSG.omega₁_map_subtype_ne_bot (M := Z) 2 hdvdZ
    simpa [Z0, Ω] using h
  have hZ0dvd : 2 ∣ Nat.card ↥Z0 := by
    obtain ⟨k, hk⟩ := (hQ2.to_subgroup Z0).exists_card_eq
    have hkpos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      exact hZ0ne (Z0.eq_bot_of_card_eq hk)
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  let ρZ0 : L' →* MulAut Z0 := (MulAut.characteristic Z0).comp ρ
  let ρP : ↥P →* MulAut Z0 := ρZ0.comp P.subtype
  letI : MulAction ↥P Z0 := MulAction.compHom Z0 ρP
  have hfix1 : (1 : Z0) ∈ MulAction.fixedPoints ↥P Z0 := by
    intro p
    exact map_one (ρP p)
  obtain ⟨a, hafix, ha1⟩ :=
    hP2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := Z0) hZ0dvd hfix1
  have hfixA : ∀ p ∈ P, ρ p (a : Q) = (a : Q) := by
    intro p hp
    have h : ρP ⟨p, hp⟩ a = a := by
      simpa [MulAction.compHom_smul_def] using hafix ⟨p, hp⟩
    have hq : ((MulAut.characteristic Z0 (ρ p)) a : Q) = (ρ p) (a : Q) := rfl
    have h2 : (ρ p) (a : Q) = (a : Q) := by
      rw [← hq]
      exact congrArg (fun x : Z0 => (x : Q)) h
    simpa [ρP, ρZ0] using h2
  let A : Subgroup Q := Z0 ⊓ CFSG.SL2MinimalFaithful.fixedPoints ρ P
  have hAne : A ≠ ⊥ := by
    intro hbot
    have haA : (a : Q) ∈ A := by
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      intro p hp
      exact hfixA p hp
    rw [hbot] at haA
    exact ha1 (Subtype.ext (by simpa using haA)).symm
  have hAle : A ≤ Subgroup.center Q := fun x hx => hZ0center (Subgroup.mem_inf.mp hx).1
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hZ0sq a (Subgroup.mem_inf.mp ha).1
  have hAinv : ∀ l : L', ∀ a ∈ A, ρ l a ∈ A := by
    intro l a ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hz : a ∈ Z0 := (Subgroup.mem_inf.mp ha).1
      have hmap : Z0.map ((ρ l : MulAut Q) : Q →* Q) = Z0 :=
        Subgroup.characteristic_iff_map_eq.mp hZ0char (ρ l)
      exact hmap ▸ Subgroup.mem_map_of_mem (ρ l : Q →* Q) hz
    · intro p hp
      have hfixp : ∀ x ∈ P, ρ x a = a := (Subgroup.mem_inf.mp ha).2
      have hnorm : l⁻¹ * p * l ∈ P := by
        have := (inferInstance : P.Normal).conj_mem p hp l⁻¹
        simpa using this
      calc ρ p (ρ l a) = ρ (p * l) a := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (l * (l⁻¹ * p * l)) a := by
            rw [show p * l = l * (l⁻¹ * p * l) by group]
        _ = ρ l (ρ (l⁻¹ * p * l) a) := by rw [map_mul, MulAut.mul_apply]
        _ = ρ l a := by rw [hfixp _ hnorm]
  exact ⟨A, hAne, hAle, hAsq, hAinv, fun p hp a ha => (Subgroup.mem_inf.mp ha).2 p hp⟩

private theorem odd_eq_one_of_action_of_card_lt {L : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (m : ℕ) :
    ∀ {Q : Type} [Group Q] [Finite Q], Nat.card Q = m → IsPGroup 2 Q →
      m < 2 ^ (2 * n) → ∀ ρ : ↥L →* MulAut Q, ∀ y : ↥L, Odd (orderOf y) → ρ y = 1 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro Q _ _ hm hQ2 hlt ρ y hy
    by_cases hsub : Subsingleton Q
    · haveI := hsub
      ext q
      exact Subsingleton.elim _ _
    · have hQnt : Nontrivial Q := by
        by_contra h
        exact hsub (not_nontrivial_iff_subsingleton.mp h)
      haveI : Nontrivial Q := hQnt
      obtain ⟨A, hAne, hAcenter, hA2, hAinv, hAfix⟩ :=
        exists_fixed_central_subgroup (Q := Q) (L' := ↥L) ρ (CFSG.pCore 2 ↥L)
          hQ2 (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hQnt
      by_cases hAtop : A = ⊤
      · have hcoreρ : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → ρ p = 1 := by
          intro p hp
          ext q
          have hqA : q ∈ A := by rw [hAtop]; exact Subgroup.mem_top q
          exact hAfix p hp q hqA
        have hcard : Nat.card Q < 2 ^ (2 * n) := by rwa [hm]
        have hρ : ρ = 1 := action_eq_one_of_card_lt hn hq hQ2 ρ hcard hcoreρ
        rw [hρ]
        rfl
      · have hAlt : A < ⊤ := lt_of_le_of_ne le_top hAtop
        have hAcardlt : Nat.card A < m := by
          rw [← hm]
          simpa [Subgroup.card_top] using Subgroup.card_lt_of_lt hAlt
        have hQA_lt : Nat.card (Q ⧸ A) < m := by
          rw [← hm, ← Subgroup.index_eq_card, Subgroup.index_eq_card_div]
          exact Nat.div_lt_self Nat.card_pos
            ((Subgroup.one_lt_card_iff_ne_bot A).mpr hAne)
        have hltA : Nat.card A < 2 ^ (2 * n) := hAcardlt.trans_le hlt.le
        have hltQA : Nat.card (Q ⧸ A) < 2 ^ (2 * n) := hQA_lt.trans_le hlt.le
        have hAnormal : A.Normal := Subgroup.normal_of_le_center hAcenter
        letI : A.Normal := hAnormal
        have hQ2A : IsPGroup 2 A := hQ2.to_subgroup A
        have hQ2QA : IsPGroup 2 (Q ⧸ A) := hQ2.to_quotient A
        let ρA : ↥L →* MulAut A := restrictAction ρ hAinv
        let ρQA : ↥L →* MulAut (Q ⧸ A) := quotientAction ρ hAinv
        have hIA : ρA y = 1 :=
          ih (Nat.card A) hAcardlt rfl hQ2A hltA ρA y hy
        have hIQA : ρQA y = 1 :=
          ih (Nat.card (Q ⧸ A)) hQA_lt rfl hQ2QA hltQA ρQA y hy
        have hfixAy : ∀ a ∈ A, ρ y a = a := by
          intro a ha
          have h := congrArg (fun f : MulAut A => f ⟨a, ha⟩) hIA
          simpa [ρA, restrictAction, mulAutRestrict] using
            congrArg (fun x : A => (x : Q)) h
        have hquot : ∀ q : Q, ρ y q / q ∈ A := by
          intro q
          have h := congrArg (fun f : MulAut (Q ⧸ A) => f (QuotientGroup.mk q)) hIQA
          rw [show ρQA y = quotientAction ρ hAinv y from rfl,
            quotientAction_mk] at h
          exact (QuotientGroup.eq_iff_div_mem).mp h
        have hoddg : Odd (orderOf (ρ y)) := hy.of_dvd_nat (orderOf_map_dvd ρ y)
        exact mulAut_eq_one_of_odd_of_central_quotient hA2 (ρ y) hoddg hfixAy hquot

private theorem isElemSec_of_subgroupOf' {H N E : Subgroup G} (hNH : N ≤ H) (hEH : E ≤ H)
    (h : IsElemSec (N.subgroupOf H) (E.subgroupOf H)) : IsElemSec N E := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (⟨x, hNH hx⟩ : ↥H) ∈ N.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxE' : (⟨x, hNH hx⟩ : ↥H) ∈ E.subgroupOf H := h.1 hx'
    exact Subgroup.mem_subgroupOf.mp hxE'
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : (⟨x, hEH hx⟩ : ↥H) ∈ E.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hy' : (⟨y, hEH hy⟩ : ↥H) ∈ E.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    have hc := Subgroup.commutator_le.mp h.2.1
      (⟨x, hEH hx⟩ : ↥H) hx' (⟨y, hEH hy⟩ : ↥H) hy'
    have hc' : (H.subtype ⁅(⟨x, hEH hx⟩ : ↥H), (⟨y, hEH hy⟩ : ↥H)⁆ : G) ∈ N :=
      Subgroup.mem_subgroupOf.mp hc
    simpa using hc'
  · intro x hx
    have hx' : (⟨x, hEH hx⟩ : ↥H) ∈ E.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hp := h.2.2 (⟨x, hEH hx⟩ : ↥H) hx'
    have hp' : (H.subtype ((⟨x, hEH hx⟩ : ↥H) ^ 2) : G) ∈ N :=
      Subgroup.mem_subgroupOf.mp hp
    simpa using hp'

theorem isElemSec_of_relIndex_eq_two_pow {L E N : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hNE : N ≤ E)
    (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (h : N.relIndex E = 2 ^ (2 * n))
    (hnt : ∃ y ∈ L, Odd (orderOf y) ∧ ∃ e ∈ E, ⁅e, y⁆ ∉ N) : IsElemSec N E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNnormal : (N.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hEN
  let Q := ↥E ⧸ N.subgroupOf E
  have hQcard : Nat.card Q = 2 ^ (2 * n) := by
    change N.relIndex E = 2 ^ (2 * n)
    exact h
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (p := 2) (n := 2 * n) hQcard
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; positivity)
  let ρ : ↥L →* MulAut Q := CFSG.GroupTheory.conjQuotHom hLE hLN
  have hQnt : Nontrivial Q := by
    have h1 : 1 < Nat.card Q := by
      rw [hQcard]
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨A, hAne, hAcenter, hA2, hAinv, hAfix⟩ :=
    exists_fixed_central_subgroup (Q := Q) (L' := ↥L) ρ (CFSG.pCore 2 ↥L)
      hQ2 (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hQnt
  have hAnormal : A.Normal := Subgroup.normal_of_le_center hAcenter
  letI : A.Normal := hAnormal
  have hAtop : A = ⊤ := by
    by_contra hAtop
    have hAlt : A < ⊤ := lt_of_le_of_ne le_top hAtop
    have hltA : Nat.card A < 2 ^ (2 * n) := by
      have hlt' := Subgroup.card_lt_of_lt hAlt
      rw [Subgroup.card_top, hQcard] at hlt'
      exact hlt'
    have hltQA : Nat.card (Q ⧸ A) < 2 ^ (2 * n) := by
      have hlt' : Nat.card (Q ⧸ A) < Nat.card Q := by
        rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div]
        exact Nat.div_lt_self Nat.card_pos
          ((Subgroup.one_lt_card_iff_ne_bot A).mpr hAne)
      rwa [hQcard] at hlt'
    have hQ2A : IsPGroup 2 A := hQ2.to_subgroup A
    have hQ2QA : IsPGroup 2 (Q ⧸ A) := hQ2.to_quotient A
    let ρA : ↥L →* MulAut A := restrictAction ρ hAinv
    let ρQA : ↥L →* MulAut (Q ⧸ A) := quotientAction ρ hAinv
    obtain ⟨y, hyL, hyodd, e, he, hne⟩ := hnt
    let y' : ↥L := ⟨y, hyL⟩
    have hyodd' : Odd (orderOf y') := by simpa [y'] using hyodd
    have hIA : ρA y' = 1 :=
      odd_eq_one_of_action_of_card_lt (L := L) hn hq (Nat.card A) rfl hQ2A hltA ρA y' hyodd'
    have hIQA : ρQA y' = 1 :=
      odd_eq_one_of_action_of_card_lt (L := L) hn hq (Nat.card (Q ⧸ A)) rfl hQ2QA hltQA
        ρQA y' hyodd'
    have htrivA : ∀ a ∈ A, ρ y' a = a := by
      intro a ha
      have h1 := congrArg (fun f : MulAut A => f ⟨a, ha⟩) hIA
      simpa [ρA, restrictAction, mulAutRestrict] using congrArg (fun x : A => (x : Q)) h1
    have htrivQ : ∀ q : Q, ρ y' q / q ∈ A := by
      intro q
      have h1 := congrArg (fun f : MulAut (Q ⧸ A) => f (QuotientGroup.mk q)) hIQA
      rw [show ρQA y' = quotientAction ρ hAinv y' from rfl, quotientAction_mk] at h1
      exact (QuotientGroup.eq_iff_div_mem).mp h1
    have hoddg : Odd (orderOf (ρ y')) := hyodd'.of_dvd_nat (orderOf_map_dvd ρ y')
    have hρy : ρ y' = 1 :=
      mulAut_eq_one_of_odd_of_central_quotient hA2 (ρ y') hoddg htrivA htrivQ
    apply hne
    have hfix : ρ y' (QuotientGroup.mk ⟨e, he⟩) = QuotientGroup.mk ⟨e, he⟩ := by
      rw [hρy]; rfl
    have h2' : QuotientGroup.mk' (N.subgroupOf E)
        (⟨y * e * y⁻¹, (hLE hyL e).mp he⟩ : ↥E) =
        QuotientGroup.mk' (N.subgroupOf E) ⟨e, he⟩ := by
      have h3 := hfix
      rw [show ρ y' = CFSG.GroupTheory.conjQuotAut (hLE hyL) (hLN hyL) from rfl,
        CFSG.GroupTheory.conjQuotAut_mk] at h3
      simpa [y'] using h3
    have hmem : ((⟨y * e * y⁻¹, (hLE hyL e).mp he⟩ : ↥E) / ⟨e, he⟩) ∈
        N.subgroupOf E :=
      (QuotientGroup.eq_iff_div_mem).mp h2'
    have hmemG : y * e * y⁻¹ * e⁻¹ ∈ N := by
      have h1 := Subgroup.mem_subgroupOf.mp hmem
      simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using N.inv_mem hmemG
  have hQelem : ∀ q : Q, q ^ 2 = 1 ∧ ∀ q' : Q, q * q' = q' * q := by
    intro q
    have hqA : q ∈ A := by rw [hAtop]; exact Subgroup.mem_top q
    exact ⟨hA2 q hqA, fun q' => (Subgroup.mem_center_iff.mp (hAcenter hqA) q').symm⟩
  refine ⟨hNE, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro e1 he1 e2 he2
    have h1 : (QuotientGroup.mk' (N.subgroupOf E))
        ⁅(⟨e1, he1⟩ : ↥E), (⟨e2, he2⟩ : ↥E)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hQelem _).2 _
    have hmem : ⁅(⟨e1, he1⟩ : ↥E), (⟨e2, he2⟩ : ↥E)⁆ ∈ N.subgroupOf E :=
      (QuotientGroup.eq_one_iff _).mp h1
    have hmemG : ⁅e1, e2⁆ ∈ N := by
      have h2 := Subgroup.mem_subgroupOf.mp hmem
      have h3 : E.subtype ⁅(⟨e1, he1⟩ : ↥E), (⟨e2, he2⟩ : ↥E)⁆ = ⁅e1, e2⁆ := by
        rw [map_commutatorElement]
        rfl
      have h2' : E.subtype ⁅(⟨e1, he1⟩ : ↥E), (⟨e2, he2⟩ : ↥E)⁆ ∈ N := h2
      rwa [h3] at h2'
    simpa using hmemG
  · intro e he
    have h1 : (QuotientGroup.mk' (N.subgroupOf E)) ((⟨e, he⟩ : ↥E) ^ 2) = 1 := by
      rw [map_pow]
      exact (hQelem (QuotientGroup.mk ⟨e, he⟩)).1
    have hmem : ((⟨e, he⟩ : ↥E) ^ 2) ∈ N.subgroupOf E :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h2 := Subgroup.mem_subgroupOf.mp hmem
    simpa using h2

theorem isElemSec_of_natQuot_of_comm_le {L E Z N : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 2 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L))
    (hE2 : IsPGroup 2 E) (hnat : NatQuot L E Z n) (hsec : IsElemSec Z E)
    (hZN : IsElemSec N Z) (hcent : ⁅Z, L⁆ ≤ N) : IsElemSec N E := by
  have hEL : E ≤ L := hnat.E_le
  have hZL : Z ≤ L := hnat.Z_le.trans hEL
  have hNL : N ≤ L := hZN.1.trans hZL
  have hA : IsElemSec (N.subgroupOf L) (Z.subgroupOf L) :=
    isElemSec_subgroupOf (H := L) hZN
  have hQ : IsElemSec (Z.subgroupOf L) (E.subgroupOf L) :=
    isElemSec_subgroupOf (H := L) hsec
  refine isElemSec_of_subgroupOf' (H := L) hNL hEL ?_
  refine isElemSec_of_transitive (G := ↥L) (K := N.subgroupOf L) (A := Z.subgroupOf L)
    (Q := E.subgroupOf L) (L := ⊤) le_top hA hQ ?_ ?_ ?_
  · intro a ha l hl
    have haZ : (a : G) ∈ Z := Subgroup.mem_subgroupOf.mp ha
    have hlL : (l : G) ∈ L := l.2
    rw [Subgroup.mem_subgroupOf]
    exact hcent (Subgroup.commutator_mem_commutator haZ hlL)
  · rw [Subgroup.relIndex_subgroupOf (H := Z) (K := E) (L := L) hEL]
    have h := hnat.index
    have h8 : 8 ≤ 2 ^ (2 * n) := by
      have hn' : 2 ≤ n := hn
      calc 8 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 8 ≤ 2 ^ (2 * n) := h8
      _ = Z.relIndex E := h.symm
  · intro x hx hxA y hy hyA
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
    have hxZ : (x : G) ∉ Z := fun h => hxA (Subgroup.mem_subgroupOf.mpr h)
    have hyZ : (y : G) ∉ Z := fun h => hyA (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨l, hl, hmem⟩ :=
      NatQuot.exists_conj_mul_mem hnat hq hE2 hxE hxZ hyE hyZ
    refine ⟨(⟨l, hl⟩ : ↥L), Subgroup.mem_top _, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hmem

end CFSG.Quasithin.St84

end
