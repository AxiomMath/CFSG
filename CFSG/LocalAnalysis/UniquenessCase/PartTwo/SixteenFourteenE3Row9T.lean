module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9B
import CFSG.GroupTheory.SupCommute
import CFSG.Quasithin.Background.D36GluedA5Mod
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1614e3_card_dvd_of_free {P X : Type*} [Group P] [MulAction P X] [Finite P]
    [Finite X] (hfree : ∀ (g : P) (x : X), g • x = x → g = 1) : Nat.card P ∣ Nat.card X := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite X
  have hstab : ∀ x : X, MulAction.stabilizer P x = ⊥ := fun x => by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨hfree g x, fun h => by rw [h, one_smul]⟩
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer P X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [hstab]
  exact (Nat.card_congr (QuotientGroup.quotientBot (G := P)).toEquiv).symm ▸ dvd_refl _

private theorem s1614e3_closure_comm_exp' {G : Type*} [Group G] {p : ℕ} (S : Set G)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hexp : ∀ a ∈ S, a ^ p = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ p = 1 := by
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm y hb x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b rfl).symm
  have h2 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {a} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h1 y ha x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hb) a rfl)
  refine ⟨h2, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hexp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := h2 x hx y hy
    rw [hc.mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

private theorem s1614e3_zpow_eq_nat_pow {T : Type} [CommGroup T] {x : MulAut T}
    (hx : orderOf x = 7) (m : ℤ) : x ^ m = x ^ ((m % 7).toNat) := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hx]
  have h1 : m ≡ m % 7 [ZMOD (7 : ℤ)] := (Int.mod_modEq m 7).symm
  have h2 : ((m % 7).toNat : ℤ) = m % 7 :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  rw [h2]
  exact h1

private theorem s1614e3_mem_sup_zpowers_eq {T : Type} [CommGroup T]
    {ℓ z : MulAut T} (hℓ : orderOf ℓ = 7) (hz : orderOf z = 7) (hℓz : ℓ * z = z * ℓ)
    {p : MulAut T} (hp : p ∈ Subgroup.zpowers ℓ ⊔ Subgroup.zpowers z) :
    ∃ i j : ℕ, p = ℓ ^ i * z ^ j := by
  have hcomm : ∀ a ∈ Subgroup.zpowers ℓ, ∀ b ∈ Subgroup.zpowers z, Commute a b := by
    intro a ha b hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← hm, ← hn]
    exact (show Commute ℓ z from hℓz).zpow_zpow m n
  rw [CFSG.mem_sup_of_commute hcomm] at hp
  obtain ⟨u, hu, v, hv, huv⟩ := hp
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hv
  refine ⟨(m % 7).toNat, (n % 7).toNat, ?_⟩
  have h1 : u * v = ℓ ^ ((m % 7).toNat) * z ^ ((n % 7).toNat) := by
    rw [← hm, ← hn, s1614e3_zpow_eq_nat_pow hℓ m, s1614e3_zpow_eq_nat_pow hz n]
  exact huv.symm.trans h1

private theorem s1614e3_pow_apply_mem {T : Type} [CommGroup T] {S : Subgroup T}
    {φ : MulAut T} (h : ∀ s ∈ S, φ s ∈ S) (n : ℕ) : ∀ s ∈ S, (φ ^ n) s ∈ S := by
  induction n with
  | zero => intro s hs; simpa using hs
  | succ n ih =>
    intro s hs
    rw [pow_succ, MulAut.mul_apply]
    exact ih (φ s) (h s hs)

@[reducible]
private def s1614e3_smulNonzero {T : Type} [CommGroup T] {S : Subgroup T}
    (P : Subgroup (MulAut T)) (hP : ∀ p ∈ P, ∀ s ∈ S, p s ∈ S) :
    MulAction ↥P {s : T // s ∈ S ∧ s ≠ 1} where
  smul p x := ⟨(p : MulAut T) x.1, hP p p.2 x.1 x.2.1, by
    have h1 : ((p : MulAut T)⁻¹) ((p : MulAut T) x.1) = x.1 := by
      have h2 := congrArg (fun e : MulAut T => e x.1) (inv_mul_cancel (p : MulAut T))
      simpa [MulAut.mul_apply] using h2
    intro h
    rw [h] at h1
    simp only [map_one] at h1
    exact x.2.2 h1.symm⟩
  one_smul x := rfl
  mul_smul p q x := rfl

private theorem s1614e3_mul_pow_seven {T : Type} [CommGroup T] {a c : MulAut T}
    (hac : a * c = c * a) (ha : a ^ 7 = 1) (hc : c ^ 7 = 1) (i j : ℕ) :
    (a ^ i * c ^ j) ^ 7 = 1 := by
  have hcomm : Commute (a ^ i) (c ^ j) := (show Commute a c from hac).pow_pow i j
  rw [hcomm.mul_pow]
  have hai : (a ^ i) ^ 7 = 1 := by
    rw [← pow_mul, mul_comm i 7, pow_mul, ha, one_pow]
  have hcj : (c ^ j) ^ 7 = 1 := by
    rw [← pow_mul, mul_comm j 7, pow_mul, hc, one_pow]
  rw [hai, hcj, mul_one]

private theorem s1614e3_card_fixV_modEq {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ x : T, x ^ 2 = 1) {S : Subgroup T} {g : MulAut T}
    (hS : ∀ s ∈ S, g s ∈ S) (hg : g ^ 7 = 1) :
    Nat.card S ≡ 2 ^ rk ↥(S ⊓ fixV (Subgroup.zpowers g)) [MOD 7] := by
  have h := CFSG.Quasithin.A5Mod.card_fix_modEq 7 g hg S hS
  have hefix : CFSG.Quasithin.A5Mod.fixSub g = fixV (Subgroup.zpowers g) := by
    ext x
    rw [CFSG.Quasithin.A5Mod.mem_fixSub, mem_fixV_zpowers_iff_apply]
  rw [hefix] at h
  have h2 : Nat.card ↥(S ⊓ fixV (Subgroup.zpowers g)) =
      2 ^ rk ↥(S ⊓ fixV (Subgroup.zpowers g)) := card_eq_two_pow hT _
  rw [h2] at h
  exact h

theorem s1614e3_row9_fixed_rank {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    {S : Subgroup T} (hS : rk S = 9) {ℓ z : MulAut T} (hℓ : orderOf ℓ = 7) (hz : orderOf z = 7)
    (hℓz : ℓ * z = z * ℓ) (hind : ∀ i j : ℕ, ℓ ^ i = z ^ j → ℓ ^ i = 1)
    (hSℓ : ∀ s ∈ S, ℓ s ∈ S) (hSz : ∀ s ∈ S, z s ∈ S) :
    ∃ i j : ℕ, ℓ ^ i * z ^ j ≠ 1 ∧ 2 ≤ rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) := by
  classical
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  by_contra hcon
  have hcon' : ∀ i j : ℕ, ℓ ^ i * z ^ j ≠ 1 →
      rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) ≤ 1 := by
    intro i j hne
    by_contra hle
    exact hcon ⟨i, j, hne, by omega⟩
  have hℓ7 : ℓ ^ 7 = 1 := by rw [← hℓ]; exact pow_orderOf_eq_one ℓ
  have hz7 : z ^ 7 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hS512 : Nat.card S = 512 := by
    rw [card_eq_two_pow hT S, hS]; norm_num
  have hdisj : Subgroup.zpowers ℓ ⊓ Subgroup.zpowers z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx.2
    have h1 : ℓ ^ ((m % 7).toNat) = z ^ ((n % 7).toNat) := by
      rw [← s1614e3_zpow_eq_nat_pow hℓ m, ← s1614e3_zpow_eq_nat_pow hz n, hm, hn]
    have h2 := hind (m % 7).toNat (n % 7).toNat h1
    rw [← hm, s1614e3_zpow_eq_nat_pow hℓ m, h2]
  let P : Subgroup (MulAut T) := Subgroup.zpowers ℓ ⊔ Subgroup.zpowers z
  have hcardP : Nat.card ↥P = 49 := by
    have hcomm : ∀ a ∈ Subgroup.zpowers ℓ, ∀ b ∈ Subgroup.zpowers z, Commute a b := by
      intro a ha b hb
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← hm, ← hn]
      exact (show Commute ℓ z from hℓz).zpow_zpow m n
    have h := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers ℓ)
      (Subgroup.zpowers z) hcomm hdisj
    rw [Nat.card_zpowers, Nat.card_zpowers, hℓ, hz] at h
    simpa [P] using h
  have hPstab : ∀ p ∈ P, ∀ s ∈ S, p s ∈ S := by
    intro p hp s hs
    obtain ⟨i, j, rfl⟩ := s1614e3_mem_sup_zpowers_eq hℓ hz hℓz hp
    rw [MulAut.mul_apply]
    exact s1614e3_pow_apply_mem hSℓ i _ (s1614e3_pow_apply_mem hSz j s hs)
  let X : Type := {s : T // s ∈ S ∧ s ≠ 1}
  letI : MulAction ↥P X := s1614e3_smulNonzero P hPstab
  have hfree : ∀ (p : ↥P) (x : X), p • x = x → p = 1 := by
    intro p x hpx
    by_contra hpne
    obtain ⟨i, j, hpij⟩ := s1614e3_mem_sup_zpowers_eq hℓ hz hℓz p.2
    have hpne' : ℓ ^ i * z ^ j ≠ 1 := fun h =>
      hpne (Subtype.ext (by rw [hpij, h]; rfl))
    have hrk1 : rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) ≤ 1 := hcon' i j hpne'
    have hfix : (p : MulAut T) x.1 = x.1 := congrArg Subtype.val hpx
    have hmemfix : x.1 ∈ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j)) := by
      rw [mem_fixV_zpowers_iff_apply, ← hpij]
      exact hfix
    have hne_bot : S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j)) ≠ ⊥ := by
      intro hbot
      have hmem : x.1 ∈ S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j)) := ⟨x.2.1, hmemfix⟩
      rw [hbot] at hmem
      exact x.2.2 (Subgroup.mem_bot.1 hmem)
    have hrk0 : rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) ≠ 0 := by
      intro h0
      exact hne_bot ((rk_eq_zero_iff hT).1 h0)
    have hSg : ∀ s ∈ S, (ℓ ^ i * z ^ j) s ∈ S := by
      intro s hs
      rw [MulAut.mul_apply]
      exact s1614e3_pow_apply_mem hSℓ i _ (s1614e3_pow_apply_mem hSz j s hs)
    have hg7 : (ℓ ^ i * z ^ j) ^ 7 = 1 := s1614e3_mul_pow_seven hℓz hℓ7 hz7 i j
    have hmod := s1614e3_card_fixV_modEq hT hSg hg7
    have hrk_ne1 : rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) ≠ 1 := by
      intro hr1
      rw [hS512, hr1] at hmod
      norm_num [Nat.ModEq] at hmod
    have : 1 ≤ rk ↥(S ⊓ fixV (Subgroup.zpowers (ℓ ^ i * z ^ j))) :=
      Nat.pos_iff_ne_zero.2 hrk0
    omega
  have hdvd : Nat.card ↥P ∣ Nat.card X := s1614e3_card_dvd_of_free hfree
  have hX : Nat.card X = 511 := by
    let e : X ≃ {s : S // (s : T) ≠ 1} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    have h1 : Nat.card X = Nat.card {s : S // (s : T) ≠ 1} := Nat.card_congr e
    rw [h1]
    haveI : Fintype S := Fintype.ofFinite S
    haveI : Fintype {s : S // (s : T) = 1} := Fintype.ofFinite _
    haveI : Fintype {s : S // (s : T) ≠ 1} := Fintype.ofFinite _
    have hcompl := Fintype.card_subtype_compl (α := S) (p := fun s : S => (s : T) = 1)
    have hsingle : Fintype.card {s : S // (s : T) = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, by simp⟩, fun x => Subtype.ext ?_⟩
      simpa using x.2
    rw [Nat.card_eq_fintype_card, hcompl, hsingle, ← Nat.card_eq_fintype_card, hS512]
  rw [hcardP, hX] at hdvd
  exact absurd hdvd (by norm_num)

theorem s1614e3_row9_side {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    {M : Subgroup (MulAut T)} {S : Subgroup T} (hS : rk S = 9) {ℓ z c : MulAut T}
    (hℓM : ℓ ∈ M) (hzM : z ∈ M) (hcM : c ∈ M) (hℓ : orderOf ℓ = 7) (hz : orderOf z = 7)
    (hc : orderOf c = 7) (hℓz : ℓ * z = z * ℓ) (hind : ∀ i j : ℕ, ℓ ^ i = z ^ j → ℓ ^ i = 1)
    (hSℓ : ∀ s ∈ S, ℓ s ∈ S) (hSz : ∀ s ∈ S, z s ∈ S) (hcℓ : c * ℓ = ℓ * c)
    (hcz : c * z = z * c) (hcS : ∀ s ∈ S, c s = s)
    (hcn : ∀ m i j : ℕ, c ^ m = ℓ ^ i * z ^ j → c ^ m = 1) {W₀ : Subgroup T}
    (hW₀ : 8 ≤ rk ↥(W₀ ⊓ S)) :
    ∃ w ∈ W₀, w ≠ 1 ∧ ∃ B : Subgroup (MulAut T), B ≤ M ∧ IsPGroup 7 ↥B ∧ ¬ IsCyclic ↥B ∧
      w ∈ fixV B := by
  classical
  obtain ⟨i, j, ha_ne, ha_rk⟩ := s1614e3_row9_fixed_rank hT hS hℓ hz hℓz hind hSℓ hSz
  set a : MulAut T := ℓ ^ i * z ^ j with ha_def
  have ha_ne' : a ≠ 1 := by rw [ha_def]; exact ha_ne
  have ha_rk' : 2 ≤ rk ↥(S ⊓ fixV (Subgroup.zpowers a)) := by rw [ha_def]; exact ha_rk
  have hℓ7 : ℓ ^ 7 = 1 := by rw [← hℓ]; exact pow_orderOf_eq_one ℓ
  have hz7 : z ^ 7 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hc7 : c ^ 7 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have ha7 : a ^ 7 = 1 := by rw [ha_def]; exact s1614e3_mul_pow_seven hℓz hℓ7 hz7 i j
  have ha_ord : orderOf a = 7 := orderOf_eq_prime ha7 ha_ne'
  have hsup_le : rk ↥((W₀ ⊓ S) ⊔ (S ⊓ fixV (Subgroup.zpowers a))) ≤ 9 := by
    rw [← hS]
    exact rk_mono (sup_le inf_le_right inf_le_left)
  have hsum := rk_sup_add_rk_inf (W₀ ⊓ S) (S ⊓ fixV (Subgroup.zpowers a))
  have hinf_ge : 1 ≤ rk ↥((W₀ ⊓ S) ⊓ (S ⊓ fixV (Subgroup.zpowers a))) := by
    omega
  have hinf_ne : (W₀ ⊓ S) ⊓ (S ⊓ fixV (Subgroup.zpowers a)) ≠ ⊥ := by
    intro hbot
    rw [hbot, rk_bot] at hinf_ge
    omega
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinf_ne
  have hwmem := w.2
  simp only [Subgroup.mem_inf] at hwmem
  have hwW₀ : (w : T) ∈ W₀ := hwmem.1.1
  have hwS : (w : T) ∈ S := hwmem.1.2
  have hw_ne : (w : T) ≠ 1 := by
    simpa using Subtype.coe_injective.ne hw1
  have haw : a (w : T) = (w : T) := by
    have hmemfix : (w : T) ∈ fixV (Subgroup.zpowers a) := hwmem.2.2
    rwa [mem_fixV_zpowers_iff_apply] at hmemfix
  have hcw : c (w : T) = (w : T) := hcS (w : T) hwS
  have haM : a ∈ M := by
    rw [ha_def]
    exact M.mul_mem (M.pow_mem hℓM i) (M.pow_mem hzM j)
  have hℓc : Commute ℓ c := (show Commute c ℓ from hcℓ).symm
  have hzc : Commute z c := (show Commute c z from hcz).symm
  have hac : Commute a c := by
    rw [ha_def]
    exact (hℓc.pow_left i).mul_left (hzc.pow_left j)
  set B : Subgroup (MulAut T) := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hB_def
  have hdisjB : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx.2
    have hxk : a ^ ((m % 7).toNat) = c ^ ((n % 7).toNat) := by
      rw [← s1614e3_zpow_eq_nat_pow ha_ord m, ← s1614e3_zpow_eq_nat_pow hc n, hm, hn]
    have hcommij : Commute (ℓ ^ i) (z ^ j) := (show Commute ℓ z from hℓz).pow_pow i j
    have hapow : a ^ ((m % 7).toNat) =
        ℓ ^ (i * (m % 7).toNat) * z ^ (j * (m % 7).toNat) := by
      rw [ha_def, hcommij.mul_pow, ← pow_mul, ← pow_mul]
    have h1 : c ^ ((n % 7).toNat) =
        ℓ ^ (i * (m % 7).toNat) * z ^ (j * (m % 7).toNat) := by
      rw [← hxk, hapow]
    have h2 : c ^ ((n % 7).toNat) = 1 := hcn _ _ _ h1
    rw [← hn, s1614e3_zpow_eq_nat_pow hc n, h2]
  have hcardB : Nat.card ↥B = 49 := by
    have h := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers a) (Subgroup.zpowers c)
      (fun x hx y hy => by
        obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [← hp, ← hq]
        exact hac.zpow_zpow p q) hdisjB
    rw [Nat.card_zpowers, Nat.card_zpowers, ha_ord, hc] at h
    simpa [hB_def] using h
  have hclosure : Subgroup.closure ({a, c} : Set (MulAut T)) = B := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hexpB : ∀ x ∈ B, x ^ 7 = 1 := by
    have hcomm' : ∀ x ∈ ({a, c} : Set (MulAut T)), ∀ y ∈ ({a, c} : Set (MulAut T)),
        x * y = y * x := by
      intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hac
      · exact hac.symm
      · rfl
    have hexp' : ∀ x ∈ ({a, c} : Set (MulAut T)), x ^ 7 = 1 := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact ha7
      · rw [hx]; exact hc7
    intro x hx
    rw [← hclosure] at hx
    exact (s1614e3_closure_comm_exp' ({a, c} : Set (MulAut T)) hcomm' hexp').2 x hx
  have hBpg : IsPGroup 7 ↥B := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hexpB (g : MulAut T) g.2
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    haveI := hcyc
    haveI : Fintype ↥B := Fintype.ofFinite _
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥B) (n := 7) (by norm_num)
    have hcard : (Finset.univ.filter (fun x : ↥B => x ^ 7 = 1)).card = 49 := by
      have htrue : (Finset.univ.filter (fun x : ↥B => x ^ 7 = 1)) = Finset.univ :=
        Finset.filter_true_of_mem (fun x _ => by
          apply Subtype.ext
          simpa using hexpB (x : MulAut T) x.2)
      rw [htrue, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardB]
    omega
  have hBM : B ≤ M := by
    rw [hB_def]
    exact sup_le (Subgroup.zpowers_le.mpr haM) (Subgroup.zpowers_le.mpr hcM)
  have hfixB : (w : T) ∈ fixV B := by
    rw [mem_fixV]
    intro x hx
    rw [← hclosure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]; exact haw
      · rw [hy]; exact hcw
    | one => rfl
    | mul y z' hy hz' ihy ihz' => rw [MulAut.mul_apply, ihz', ihy]
    | inv y hy ihy =>
      have h := congrArg (fun v => (y : MulAut T)⁻¹ v) ihy
      rw [← MulAut.mul_apply, inv_mul_cancel] at h
      simpa using h.symm
  exact ⟨(w : T), hwW₀, hw_ne, B, hBM, hBpg, hBnc, hfixB⟩

private def s1614e3_caseCom {T : Type} [CommGroup T] (φ : MulAut T) : T →* T where
  toFun t := φ t * t⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

private theorem s1614e3_caseCom_apply {T : Type} [CommGroup T] (φ : MulAut T) (t : T) :
    s1614e3_caseCom φ t = φ t * t⁻¹ := rfl

private theorem s1614e3_rk_le_commV {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {W : Subgroup T} {φ : MulAut T}
    (hinj : ∀ w ∈ W, φ w = w → w = 1) :
    rk ↥W ≤ rk ↥(commV (Subgroup.zpowers φ)) := by
  have hmem : ∀ w : W, s1614e3_caseCom φ (w : T) ∈ commV (Subgroup.zpowers φ) := fun w =>
    Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, (w : T), rfl⟩
  let f : ↥W →* ↥(commV (Subgroup.zpowers φ)) :=
    ((s1614e3_caseCom φ).comp W.subtype).codRestrict _ hmem
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : s1614e3_caseCom φ (w : T) = 1 := congrArg Subtype.val hw
    rw [s1614e3_caseCom_apply, mul_inv_eq_one] at h1
    exact Subtype.ext (hinj w w.2 h1)
  have hcard : Nat.card ↥W ≤ Nat.card ↥(commV (Subgroup.zpowers φ)) :=
    Nat.card_le_card_of_injective f hf
  rw [card_eq_two_pow hT W, card_eq_two_pow hT] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

private theorem s1614e3_map_conj_map_conj {T : Type} [CommGroup T]
    (A : Subgroup (MulAut T)) (x y : MulAut T) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s1614e3_map_conj_one {T : Type} [CommGroup T]
    (A : Subgroup (MulAut T)) :
    A.map (MulAut.conj (1 : MulAut T)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem s1614e3_row9_split {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    {M A : Subgroup (MulAut T)} {g : MulAut T} (h : s16n9b_case9Two M A g)
    (hrank : s16n9b_case9Rank M A 3) (hW9 : rk ↥(commSub ⊤ A) = 9) {t : MulAut T} (htM : t ∈ M)
    (ht2 : orderOf t = 2) (hcomm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 4) :
    ((∀ w ∈ commSub ⊤ A, t w = w) ∧
        rk ↥((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) ≤ 6) ∨
      ((∀ w ∈ (commSub ⊤ A).map g.toMonoidHom, t w = w) ∧
        rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) ≤ 6) := by
  classical
  have ht2' : ∃ a : ℕ, orderOf t = 2 ^ a := ⟨1, by simp [ht2]⟩
  have hrk_commV : rk (commV (Subgroup.zpowers t)) ≤ 4 := by
    rw [← rkIdx_fixV_zpowers t]
    exact hcomm
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) =
      (commSub ⊤ A).map g.toMonoidHom := s15_Infra_commSub_top_map_conj A g
  have hA : A.map (MulAut.conj t).toMonoidHom = A := by
    rcases h.conj t htM with hA | hB
    · exact hA
    · exfalso
      have hWφ : (commSub ⊤ A).map t.toMonoidHom = (commSub ⊤ A).map g.toMonoidHom := by
        rw [← s15_Infra_commSub_top_map_conj A t, hB, hgB]
      have hinj : ∀ w ∈ commSub ⊤ A, t w = w → w = 1 := by
        intro w hw hfix
        have h1 : t w ∈ (commSub ⊤ A).map g.toMonoidHom := by
          rw [← hWφ]
          exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
        rw [hfix] at h1
        have h2 : w ∈ commSub ⊤ A ⊓ (commSub ⊤ A).map g.toMonoidHom := ⟨hw, h1⟩
        rw [h.inf] at h2
        exact Subgroup.mem_bot.1 h2
      have hle := s1614e3_rk_le_commV hT hinj
      omega
  have hBφ : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [s1614e3_map_conj_map_conj]
    rcases h.conj (t * g) (M.mul_mem htM h.mem) with h1 | h1
    · exfalso
      apply h.ne
      have h2 : A.map (MulAut.conj t⁻¹).toMonoidHom = A := by
        have := congrArg (fun X : Subgroup (MulAut T) =>
          X.map (MulAut.conj t⁻¹).toMonoidHom) hA
        simp only [s1614e3_map_conj_map_conj, inv_mul_cancel,
          s1614e3_map_conj_one] at this
        exact this.symm
      calc A.map (MulAut.conj g).toMonoidHom
          = (A.map (MulAut.conj (t * g)).toMonoidHom).map
              (MulAut.conj t⁻¹).toMonoidHom := by
            rw [s1614e3_map_conj_map_conj, inv_mul_cancel_left]
        _ = A.map (MulAut.conj t⁻¹).toMonoidHom := by rw [h1]
        _ = A := h2
    · exact h1
  have hWt : (commSub ⊤ A).map t.toMonoidHom = commSub ⊤ A := by
    rw [← s15_Infra_commSub_top_map_conj A t, hA]
  have hW't : ((commSub ⊤ A).map g.toMonoidHom).map t.toMonoidHom =
      (commSub ⊤ A).map g.toMonoidHom := by
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ t, hBφ]
  have hstW : t ∈ stabSub (commSub ⊤ A) := s16n9b_case9_mem_stabSub_of_map_eq hWt
  have hstW' : t ∈ stabSub ((commSub ⊤ A).map g.toMonoidHom) :=
    s16n9b_case9_mem_stabSub_of_map_eq hW't
  have hWinv : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commSub ⊤ A, x w ∈ commSub ⊤ A :=
    fun x hx w hw => (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW hx) w).2 hw
  have hW'inv : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ (commSub ⊤ A).map g.toMonoidHom,
      x w ∈ (commSub ⊤ A).map g.toMonoidHom :=
    fun x hx w hw => (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW' hx) w).2 hw
  obtain ⟨t', ht'⟩ : ∃ t' : MulAut T, t' = g⁻¹ * t * g := ⟨_, rfl⟩
  have ht'M : t' ∈ M := by
    rw [ht']
    exact M.mul_mem (M.mul_mem (M.inv_mem h.mem) htM) h.mem
  have ht'2 : ∃ a : ℕ, orderOf t' = 2 ^ a := by
    obtain ⟨a, ha⟩ := ht2'
    refine ⟨a, ?_⟩
    rw [← ha]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    rw [ht']
    simpa [MulAut.conj_apply] using this
  have hAt' : A.map (MulAut.conj t').toMonoidHom = A := by
    have e1 : A.map (MulAut.conj t').toMonoidHom =
        ((A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      rw [ht']
      simp only [mul_assoc]
      rw [← s1614e3_map_conj_map_conj A (t * g) g⁻¹,
        ← s1614e3_map_conj_map_conj A g t]
    rw [e1, hBφ, s1614e3_map_conj_map_conj, inv_mul_cancel, s1614e3_map_conj_one]
  have ht'W : ∀ w ∈ commSub ⊤ A, t ((MulEquiv.toMonoidHom g) w) =
      (MulEquiv.toMonoidHom g) (t' w) := by
    intro w _
    rw [ht']
    simp [MulAut.mul_apply]
  have hr1 := hrank t htM ht2' hA
  have hr2 := hrank t' ht'M ht'2 hAt'
  have hrelW : rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers t)) +
      rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) = 9 := by
    have := rk_commSub_add_rk_inf_fixV hWinv
    rwa [hW9] at this
  have hzp : (Subgroup.zpowers t').map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change g * t' * g⁻¹ = t
    rw [ht']
    group
  have hcommSub_eq : commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t) =
      (commSub (commSub ⊤ A) (Subgroup.zpowers t')).map g.toMonoidHom := by
    have := s15_Core_commSub_map_conj (commSub ⊤ A) (Subgroup.zpowers t') g
    rwa [hzp] at this
  have hrk_commSub : rk ↥(commSub ((commSub ⊤ A).map g.toMonoidHom)
        (Subgroup.zpowers t)) =
      rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers t')) := by
    rw [hcommSub_eq, s16n9b_rk_map]
  have hfix_eq : (commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t) =
      (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t')).map g.toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨w, hwW, rfl⟩ := Subgroup.mem_map.1 hx.1
      refine Subgroup.mem_map.2 ⟨w, ?_, rfl⟩
      rw [Subgroup.mem_inf]
      refine ⟨hwW, ?_⟩
      rw [mem_fixV_zpowers_iff_apply]
      have hxfix : t ((MulEquiv.toMonoidHom g) w) = (MulEquiv.toMonoidHom g) w := by
        rw [mem_fixV_zpowers_iff_apply] at hx
        exact hx.2
      rw [ht'W w hwW] at hxfix
      exact g.injective hxfix
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_inf] at hw
      rw [Subgroup.mem_inf]
      refine ⟨Subgroup.mem_map.2 ⟨w, hw.1, rfl⟩, ?_⟩
      rw [mem_fixV_zpowers_iff_apply, ht'W w hw.1, mem_fixV_zpowers_iff_apply.mp hw.2]
  have hrelW' : rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers t')) +
      rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t')) = 9 := by
    have hbase := rk_commSub_add_rk_inf_fixV hW'inv
    rw [s16n9b_rk_map g (commSub ⊤ A), hW9, hrk_commSub, hfix_eq,
      s16n9b_rk_map g (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t'))] at hbase
    exact hbase
  rcases hr1 with hfixW | hr1
  · rcases hr2 with hfixW' | hr2
    ·
      exfalso
      have htW' : ∀ w ∈ (commSub ⊤ A).map g.toMonoidHom, t w = w := by
        intro w' hw'
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
        rw [ht'W w hw, hfixW' w hw]
      have ht_all : ∀ x : T, t x = x := by
        intro x
        have hx : x ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
          rw [h.sup]; exact Subgroup.mem_top x
        obtain ⟨u, hu, v, hv, huv⟩ := (Subgroup.mem_sup).1 hx
        rw [← huv, map_mul, hfixW u hu, htW' v hv]
      have ht1 : t = 1 := by
        ext x
        simpa using ht_all x
      rw [ht1, orderOf_one] at ht2
      omega
    ·
      left
      refine ⟨hfixW, ?_⟩
      have hrank_eq : rk ↥((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) =
          rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t')) := by
        rw [hfix_eq, s16n9b_rk_map]
      rw [hrank_eq]
      omega
  · rcases hr2 with hfixW' | hr2
    ·
      right
      refine ⟨?_, ?_⟩
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
        rw [ht'W u hu, hfixW' u hu]
      · omega
    ·
      exfalso
      have hU1 : commSub (commSub ⊤ A) (Subgroup.zpowers t) ≤ commSub ⊤ A :=
        commSub_le_of_invariant fun x hx w hw =>
          (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW hx) w).2 hw
      have hU2 : commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t) ≤
          (commSub ⊤ A).map g.toMonoidHom :=
        commSub_le_of_invariant fun x hx w hw =>
          (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW' hx) w).2 hw
      have hbot : commSub (commSub ⊤ A) (Subgroup.zpowers t) ⊓
          commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t) = ⊥ :=
        le_bot_iff.1 ((inf_le_inf hU1 hU2).trans h.inf.le)
      have hsum := rk_sup_add_rk_inf (commSub (commSub ⊤ A) (Subgroup.zpowers t))
        (commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t))
      rw [hbot, rk_bot, add_zero] at hsum
      have hle : rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers t) ⊔
          commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t)) ≤
          rk ↥(commV (Subgroup.zpowers t)) :=
        rk_mono (by
          rw [commV_eq_commSub]
          exact sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl))
      have hsum2 : rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers t)) +
          rk ↥(commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers t)) ≤ 4 := by
        rw [← hsum]
        exact hle.trans hrk_commV
      omega

private theorem s1614e3_commute_of_commutator_eq_bot {T : Type} [CommGroup T]
    {A B : Subgroup (MulAut T)} (h : ⁅A, B⁆ = ⊥) {a b : MulAut T}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h2 : a ∈ Subgroup.centralizer (B : Set (MulAut T)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha
  exact (Subgroup.mem_centralizer_iff.mp h2 b hb).symm

private theorem s1614e3_map_conj_mem_self {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {a : MulAut T} (ha : a ∈ X) :
    X.map (MulAut.conj a).toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem ha hy) (X.inv_mem ha)
  · intro hx
    refine Subgroup.mem_map.2 ⟨a⁻¹ * x * a, X.mul_mem (X.mul_mem (X.inv_mem ha) hx) ha, ?_⟩
    change a * (a⁻¹ * x * a) * a⁻¹ = x
    group

private theorem s1614e3_map_conj_eq_of_comm {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {z : MulAut T} (h : ∀ x ∈ X, z * x = x * z) :
    X.map (MulAut.conj z).toMonoidHom = X := by
  have hconj : ∀ x ∈ X, (MulAut.conj z) x = x := by
    intro x hx
    change z * x * z⁻¹ = x
    rw [h x hx, mul_assoc, mul_inv_cancel, mul_one]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (MulAut.conj z) x ∈ X
    rw [hconj x hx]
    exact hx
  · intro hy
    refine Subgroup.mem_map.2 ⟨y, hy, ?_⟩
    change (MulAut.conj z) y = y
    exact hconj y hy

private theorem s1614e3_stab_commSub {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {a : MulAut T}
    (hmap : X.map (MulAut.conj a).toMonoidHom = X) :
    ∀ s ∈ commSub ⊤ X, a s ∈ commSub ⊤ X := by
  have hstab : (commSub ⊤ X).map a.toMonoidHom = commSub ⊤ X := by
    rw [← s15_Infra_commSub_top_map_conj X a, hmap]
  have hmem : a ∈ stabSub (commSub ⊤ X) := s16n9b_case9_mem_stabSub_of_map_eq hstab
  intro s hs
  exact (mem_stabSub.1 hmem s).2 hs

theorem s1614e3_row9_witness {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    (hrk : rk (⊤ : Subgroup T) = 18) {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : s16n9b_case9Two M A g) (hrank : s16n9b_case9Rank M A 3)
    (hW9 : rk ↥(commSub ⊤ A) = 9)
    (hcen : ∀ x ∈ A, (∀ y ∈ A, x * y = y * x) → x = 1) (hA7 : ∃ a ∈ A, orderOf a = 7)
    {Z : Subgroup (MulAut T)} (hZM : Z ≤ M) (hZcard : Nat.card ↥Z = 7)
    (hZnorm : ∀ x ∈ M, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZcomm : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hZW : ∀ z ∈ Z, ∀ w ∈ commSub ⊤ A, z w ∈ commSub ⊤ A) {t : MulAut T} (htM : t ∈ M)
    (ht2 : orderOf t = 2) {W₀ : Subgroup T} (hW₀ : W₀ ≤ fixV (Subgroup.zpowers t))
    (hW₀r : rkIdx W₀ ≤ 4) :
    ∃ w ∈ W₀, w ≠ 1 ∧ ∃ B : Subgroup (MulAut T), B ≤ M ∧ IsPGroup 7 ↥B ∧ ¬ IsCyclic ↥B ∧
      w ∈ fixV B := by
  classical
  obtain ⟨z, hzZ, hzord⟩ : ∃ z ∈ Z, orderOf z = 7 := by
    have h1 : 1 < Nat.card ↥Z := by rw [hZcard]; norm_num
    haveI : Nontrivial ↥Z := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨zz, hzz1⟩ := exists_ne (1 : ↥Z)
    have hdvd : orderOf zz ∣ Nat.card ↥Z := orderOf_dvd_natCard zz
    rw [hZcard] at hdvd
    have hne : orderOf zz ≠ 1 := fun hh => hzz1 (orderOf_eq_one_iff.mp hh)
    have h7 : orderOf zz = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with hh | hh
      · exact absurd hh hne
      · exact hh
    exact ⟨(zz : MulAut T), zz.2, by rw [Subgroup.orderOf_coe]; exact h7⟩
  obtain ⟨a₀, ha₀A, ha₀ord⟩ := hA7
  set c : MulAut T := g * a₀ * g⁻¹ with hc_def
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) =
      (commSub ⊤ A).map g.toMonoidHom := s15_Infra_commSub_top_map_conj A g
  have hcAg : c ∈ A.map (MulAut.conj g).toMonoidHom := by
    rw [hc_def]
    exact Subgroup.mem_map.2 ⟨a₀, ha₀A, rfl⟩
  have hcM : c ∈ M := by
    rw [hc_def]
    exact M.mul_mem (M.mul_mem h.mem (h.le ha₀A)) (M.inv_mem h.mem)
  have hcord : orderOf c = 7 := by
    rw [hc_def, ← ha₀ord]
    simpa [MulAut.conj_apply]
      using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₀
  have hcenAg : ∀ x ∈ A.map (MulAut.conj g).toMonoidHom,
      (∀ y ∈ A.map (MulAut.conj g).toMonoidHom, x * y = y * x) → x = 1 := by
    intro x hx hcent
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have hacent : ∀ b ∈ A, a * b = b * a := by
      intro b hb
      have hb' : (MulAut.conj g) b ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.2 ⟨b, hb, rfl⟩
      have hh := hcent ((MulAut.conj g) b) hb'
      have h3 : (MulAut.conj g) (a * b) = (MulAut.conj g) (b * a) := by
        rw [map_mul, map_mul]
        exact hh
      exact (MulAut.conj g).injective h3
    have ha1 : a = 1 := hcen a ha hacent
    rw [ha1]
    simp
  have hzg : ∀ z ∈ Z, ∀ x ∈ A.map (MulAut.conj g).toMonoidHom, z * x = x * z := by
    intro z hzZ x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have hzgZ : g⁻¹ * z * g ∈ Z := by
      have hh := hZnorm g⁻¹ (M.inv_mem h.mem)
      rw [← hh]
      exact Subgroup.mem_map.2 ⟨z, hzZ, rfl⟩
    have h1 : (g⁻¹ * z * g) * a = a * (g⁻¹ * z * g) := hZcomm _ hzgZ a ha
    have h2 := congrArg (fun y : MulAut T => g * y * g⁻¹) h1
    have hL : g * ((g⁻¹ * z * g) * a) * g⁻¹ = z * (g * a * g⁻¹) := by group
    have hR : g * (a * (g⁻¹ * z * g)) * g⁻¹ = (g * a * g⁻¹) * z := by group
    rw [hL, hR] at h2
    exact h2
  have hstabW : ∀ s ∈ commSub ⊤ A, a₀ s ∈ commSub ⊤ A :=
    s1614e3_stab_commSub (s1614e3_map_conj_mem_self ha₀A)
  have hstabW'c : ∀ s ∈ commSub ⊤ (A.map (MulAut.conj g).toMonoidHom), c s ∈
      commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) :=
    s1614e3_stab_commSub (s1614e3_map_conj_mem_self hcAg)
  have hstabW'z : ∀ s ∈ commSub ⊤ (A.map (MulAut.conj g).toMonoidHom), z s ∈
      commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) :=
    s1614e3_stab_commSub (s1614e3_map_conj_eq_of_comm (fun x hx => hzg z hzZ x hx))
  have hℓz : a₀ * z = z * a₀ := (hZcomm z hzZ a₀ ha₀A).symm
  have hcℓ : c * a₀ = a₀ * c :=
    (s1614e3_commute_of_commutator_eq_bot h.comm ha₀A hcAg).symm
  have hcz : c * z = z * c := by
    have hzgZ : g⁻¹ * z * g ∈ Z := by
      have hh := hZnorm g⁻¹ (M.inv_mem h.mem)
      rw [← hh]
      exact Subgroup.mem_map.2 ⟨z, hzZ, rfl⟩
    have h1 := hZcomm (g⁻¹ * z * g) hzgZ a₀ ha₀A
    have h2 := congrArg (fun y : MulAut T => g * y * g⁻¹) h1
    have hL : g * ((g⁻¹ * z * g) * a₀) * g⁻¹ = z * c := by rw [hc_def]; group
    have hR : g * (a₀ * (g⁻¹ * z * g)) * g⁻¹ = c * z := by rw [hc_def]; group
    rw [hL, hR] at h2
    exact h2.symm
  have hind1 : ∀ i j : ℕ, a₀ ^ i = z ^ j → a₀ ^ i = 1 := by
    intro i j hij
    refine hcen (a₀ ^ i) (A.pow_mem ha₀A i) ?_
    intro y hy
    rw [hij]
    exact hZcomm (z ^ j) (Z.pow_mem hzZ j) y hy
  have hind2 : ∀ i j : ℕ, c ^ i = z ^ j → c ^ i = 1 := by
    intro i j hij
    refine hcenAg (c ^ i) ((A.map (MulAut.conj g).toMonoidHom).pow_mem hcAg i) ?_
    intro y hy
    rw [hij]
    exact hzg (z ^ j) (Z.pow_mem hzZ j) y hy
  have hcn1 : ∀ m i j : ℕ, c ^ m = a₀ ^ i * z ^ j → c ^ m = 1 := by
    intro m i j hm
    have hcmAg : c ^ m ∈ A.map (MulAut.conj g).toMonoidHom :=
      (A.map (MulAut.conj g).toMonoidHom).pow_mem hcAg m
    have hzjZ : z ^ j ∈ Z := Z.pow_mem hzZ j
    have haicent : ∀ y ∈ A, a₀ ^ i * y = y * a₀ ^ i := by
      intro y hy
      have h1 : Commute (c ^ m) y :=
        (s1614e3_commute_of_commutator_eq_bot h.comm hy hcmAg).symm
      have h2 : Commute (z ^ j) y := hZcomm (z ^ j) hzjZ y hy
      have haeq : a₀ ^ i = c ^ m * (z ^ j)⁻¹ := by rw [hm]; group
      rw [haeq]
      exact (h1.mul_left h2.inv_left).eq
    have hai1 : a₀ ^ i = 1 := hcen (a₀ ^ i) (A.pow_mem ha₀A i) haicent
    rw [hai1, one_mul] at hm
    refine hcenAg (c ^ m) hcmAg ?_
    intro y hy
    rw [hm]
    exact hzg (z ^ j) hzjZ y hy
  have hcn2 : ∀ m i j : ℕ, a₀ ^ m = c ^ i * z ^ j → a₀ ^ m = 1 := by
    intro m i j hm
    have hamA : a₀ ^ m ∈ A := A.pow_mem ha₀A m
    have hciAg : c ^ i ∈ A.map (MulAut.conj g).toMonoidHom :=
      (A.map (MulAut.conj g).toMonoidHom).pow_mem hcAg i
    have hzjZ : z ^ j ∈ Z := Z.pow_mem hzZ j
    have hcicent : ∀ y ∈ A.map (MulAut.conj g).toMonoidHom, c ^ i * y = y * c ^ i := by
      intro y hy
      have h1 : Commute (a₀ ^ m) y :=
        s1614e3_commute_of_commutator_eq_bot h.comm hamA hy
      have h2 : Commute (z ^ j) y := hzg (z ^ j) hzjZ y hy
      have hceq : c ^ i = a₀ ^ m * (z ^ j)⁻¹ := by rw [hm]; group
      rw [hceq]
      exact (h1.mul_left h2.inv_left).eq
    have hci1 : c ^ i = 1 := hcenAg (c ^ i) hciAg hcicent
    rw [hci1, one_mul] at hm
    refine hcen (a₀ ^ m) hamA ?_
    intro y hy
    rw [hm]
    exact hZcomm (z ^ j) hzjZ y hy
  have hrkIdx : rkIdx (fixV (Subgroup.zpowers t)) ≤ 4 := (rkIdx_anti hW₀).trans hW₀r
  rcases s1614e3_row9_split hT h hrank hW9 htM ht2 hrkIdx with ⟨hfixW, h6⟩ | ⟨hfixW', h6⟩
  ·
    have hle : W₀ ≤ commSub ⊤ A ⊔
        ((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) := by
      intro x hx
      have hxsup : x ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
        rw [h.sup]; exact Subgroup.mem_top x
      obtain ⟨u, hu, v, hv, huv⟩ := (Subgroup.mem_sup).1 hxsup
      have hvfix : v ∈ (commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t) := by
        refine ⟨hv, mem_fixV_zpowers_iff_apply.2 ?_⟩
        have hxfix : t x = x := mem_fixV_zpowers_iff_apply.mp (hW₀ hx)
        rw [← huv, map_mul, hfixW u hu] at hxfix
        exact mul_left_cancel hxfix
      rw [← huv]
      exact Subgroup.mem_sup.2 ⟨u, hu, v, hvfix, rfl⟩
    have hsup_eq : rk ↥(commSub ⊤ A ⊔
        ((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t))) =
        rk ↥(commSub ⊤ A) +
          rk ↥((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) := by
      have hh := rk_sup_add_rk_inf (commSub ⊤ A)
        ((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t))
      have hbot : commSub ⊤ A ⊓
          ((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) = ⊥ := by
        apply le_bot_iff.mp
        exact (inf_le_inf le_rfl inf_le_left).trans h.inf.le
      rw [hbot, rk_bot, add_zero] at hh
      exact hh
    have hW0rk : 14 ≤ rk ↥W₀ := by
      have hh := rk_add_rkIdx W₀
      have hrkT : rk T = 18 := by rw [← rk_top]; exact hrk
      rw [hrkT] at hh
      omega
    have hsup_le : rk ↥(W₀ ⊔ commSub ⊤ A) ≤ 15 := by
      have hh := rk_mono (sup_le hle le_sup_left)
      rw [hsup_eq] at hh
      calc rk ↥(W₀ ⊔ commSub ⊤ A) ≤ rk ↥(commSub ⊤ A) +
            rk ↥((commSub ⊤ A).map g.toMonoidHom ⊓ fixV (Subgroup.zpowers t)) := hh
        _ ≤ 9 + 6 := add_le_add (le_of_eq hW9) h6
        _ = 15 := by norm_num
    have hsum := rk_sup_add_rk_inf W₀ (commSub ⊤ A)
    have h8 : 8 ≤ rk ↥(W₀ ⊓ commSub ⊤ A) := by omega
    exact s1614e3_row9_side hT hW9 (h.le ha₀A) (hZM hzZ) hcM ha₀ord hzord hcord hℓz
      hind1 hstabW (fun s hs => hZW z hzZ s hs) hcℓ hcz (fun s hs => h.fixB c hcAg s hs)
      hcn1 h8
  ·
    have hW'9 : rk ↥((commSub ⊤ A).map g.toMonoidHom) = 9 := by
      rw [s16n9b_rk_map g (commSub ⊤ A), hW9]
    have hle : W₀ ≤ (commSub ⊤ A).map g.toMonoidHom ⊔
        (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) := by
      intro x hx
      have hxsup : x ∈ (commSub ⊤ A).map g.toMonoidHom ⊔ commSub ⊤ A := by
        rw [sup_comm, h.sup]; exact Subgroup.mem_top x
      obtain ⟨u, hu, v, hv, huv⟩ := (Subgroup.mem_sup).1 hxsup
      have hvfix : v ∈ commSub ⊤ A ⊓ fixV (Subgroup.zpowers t) := by
        refine ⟨hv, mem_fixV_zpowers_iff_apply.2 ?_⟩
        have hxfix : t x = x := mem_fixV_zpowers_iff_apply.mp (hW₀ hx)
        rw [← huv, map_mul, hfixW' u hu] at hxfix
        exact mul_left_cancel hxfix
      rw [← huv]
      exact Subgroup.mem_sup.2 ⟨u, hu, v, hvfix, rfl⟩
    have hsup_eq : rk ↥((commSub ⊤ A).map g.toMonoidHom ⊔
        (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t))) =
        rk ↥((commSub ⊤ A).map g.toMonoidHom) +
          rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) := by
      have hh := rk_sup_add_rk_inf ((commSub ⊤ A).map g.toMonoidHom)
        (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t))
      have hbot : (commSub ⊤ A).map g.toMonoidHom ⊓
          (commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) = ⊥ := by
        apply le_bot_iff.mp
        refine (inf_le_inf le_rfl inf_le_left).trans ?_
        rw [inf_comm]
        exact h.inf.le
      rw [hbot, rk_bot, add_zero] at hh
      exact hh
    have hW0rk : 14 ≤ rk ↥W₀ := by
      have hh := rk_add_rkIdx W₀
      have hrkT : rk T = 18 := by rw [← rk_top]; exact hrk
      rw [hrkT] at hh
      omega
    have hsup_le : rk ↥(W₀ ⊔ (commSub ⊤ A).map g.toMonoidHom) ≤ 15 := by
      have hh := rk_mono (sup_le hle le_sup_left)
      rw [hsup_eq] at hh
      calc rk ↥(W₀ ⊔ (commSub ⊤ A).map g.toMonoidHom) ≤
            rk ↥((commSub ⊤ A).map g.toMonoidHom) +
              rk ↥(commSub ⊤ A ⊓ fixV (Subgroup.zpowers t)) := hh
        _ ≤ 9 + 6 := add_le_add (le_of_eq hW'9) h6
        _ = 15 := by norm_num
    have hsum := rk_sup_add_rk_inf W₀ ((commSub ⊤ A).map g.toMonoidHom)
    have h8 : 8 ≤ rk ↥(W₀ ⊓ (commSub ⊤ A).map g.toMonoidHom) := by omega
    have hstabW'c' : ∀ s ∈ (commSub ⊤ A).map g.toMonoidHom, c s ∈
        (commSub ⊤ A).map g.toMonoidHom := by
      rw [← hgB]; exact hstabW'c
    have hstabW'z' : ∀ s ∈ (commSub ⊤ A).map g.toMonoidHom, z s ∈
        (commSub ⊤ A).map g.toMonoidHom := by
      rw [← hgB]; exact hstabW'z
    exact s1614e3_row9_side hT hW'9 hcM (hZM hzZ) (h.le ha₀A) hcord hzord ha₀ord
      hcz hind2 hstabW'c' hstabW'z' hcℓ.symm hℓz (fun s hs => h.fixA a₀ ha₀A s hs) hcn2 h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
