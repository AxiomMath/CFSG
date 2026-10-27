module

public import CFSG.Quasithin.Background.RonanD321EndCore
public import CFSG.Quasithin.Background.SmithD321Kplus
public import CFSG.Quasithin.Background.SmithD321SzK

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.RonanD321.EndCore
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_isotypic_of_d321Three (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ (n : ℕ) (I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
      (hI : XMod.IsIrr ↥(L.subgroupOf M) I),
      IsPSL 2 2 n ↥L ∧ 2 ≤ n ∧ Nat.card ↥L = 2 ^ n * (2 ^ (2 * n) - 1) ∧
      I ≤ tilde Mp ⊤ (commV L) ∧
      IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) I 2 ∧
      Nat.card ↥I = 2 ^ (2 * n) ∧
      Nat.card (Module.End ↥(XMod.opRing ↥(L.subgroupOf M) (W ⧸ modFix Mp (⊤ : Subgroup W)))
        ↥(XMod.toSubmod hI.1)) = 2 ^ n := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨n, K, hKf, hKfin, S, σ, E, hpsl, hK, hσ, hSinv, hE, hsup, hinf⟩ :=
    exists_natCoord hB h3
  have hirr : ∀ i, XMod.IsIrr ↥(L.subgroupOf M) (S i) := fun i => (hE i).isIrr (hSinv i)
  have hiso : XMod.Iso ↥(L.subgroupOf M) (S 1) (S 0) := (hE 1).iso hσ.2 (hSinv 0) (hE 0)
  have hcard : ∀ i, Nat.card ↥(S i) = 2 ^ (2 * n) := by
    intro i
    rw [card_eq_of_coord (E i), hK, ← pow_mul, mul_comm]
  have hrk : ∀ i, rk ↥(S i) = 2 * n := by
    intro i
    have h1 := card_eq_two_pow hB.quot_sq (S i)
    rw [hcard i] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  refine ⟨n, S 0, hirr 0, hpsl, two_le_of_isPSL hpsl, ?_, hsup ▸ le_sup_left, ⟨?_, ?_, ?_⟩,
    hcard 0, ?_⟩
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB.L_le).toEquiv,
      ← Nat.card_congr (MulEquiv.ofBijective σ hσ).toEquiv, StatedAPI.card_statedSL_two, hK,
      ← pow_mul, mul_comm n 2]
  · rw [← hsup]
    exact (hSinv 0).sup (hSinv 1)
  · rw [← hsup]
    exact sup_le (le_isoComp (hirr 0) (XMod.Iso.refl _)) (le_isoComp (hirr 1) hiso)
  · rw [← hsup]
    have h := rk_sup_add_rk_inf (S 0) (S 1)
    rw [hinf, rk_bot, hrk 0, hrk 1] at h
    rw [hrk 0]
    omega
  · rw [card_end_eq (hirr 0).1, (hE 0).card_eqv hσ.2 (hSinv 0), hK]

theorem tildeU_inf_fixed_eq_bot (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) :
    letI := qAct hB.hD.hyp.Mp_normal
    tilde Mp ⊤ (commV L) ⊓ XMod.fixed ↥(L.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) = ⊥ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨n, K, hKf, hKfin, S, σ, E, -, -, -, hSinv, hE, hsup, hinf⟩ := exists_natCoord hB h3
  rw [eq_bot_iff]
  rintro q ⟨hqU, hqF⟩
  rw [← hsup] at hqU
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hqU
  have hfix : ∀ l : ↥(L.subgroupOf M), l • a = a ∧ l • b = b := by
    intro l
    have h1 : l • (a * b) = a * b := (XMod.mem_fixed.1 hqF).2 l
    rw [smul_mul'] at h1
    have e : (l • a) * a⁻¹ = b * (l • b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_right_comm, h1, mul_comm a b, mul_inv_cancel_right]
    have hx : (l • a) * a⁻¹ ∈ S 0 ⊓ S 1 :=
      ⟨(S 0).mul_mem (hSinv 0 l a ha) ((S 0).inv_mem ha),
        e ▸ (S 1).mul_mem hb ((S 1).inv_mem (hSinv 1 l b hb))⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hx
    refine ⟨hx, ?_⟩
    rw [hx] at h1
    exact mul_left_cancel h1
  have ha1 : (⟨a, ha⟩ : ↥(S 0)) = 1 := (hE 0).eq_one_of_fixed fun l => (hfix l).1
  have hb1 : (⟨b, hb⟩ : ↥(S 1)) = 1 := (hE 1).eq_one_of_fixed fun l => (hfix l).2
  rw [Subgroup.mem_bot, show a = 1 from congrArg Subtype.val ha1,
    show b = 1 from congrArg Subtype.val hb1, mul_one]

theorem smul_eq_of_pElement (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : ¬ p ∣ Nat.card ↥L) {y : MulAut W} (hyM : y ∈ M)
    (hyL : ∀ l ∈ L, y * l = l * y)
    (hyp : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) ^ p • q = q) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) • q = q := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨n, I, hI, -, -, hcardL, -, hY, -, hE⟩ := exists_isotypic_of_d321Three hB h3
  set y₀ : ↥M := ⟨y, hyM⟩
  set Y := tilde Mp ⊤ (commV L)
  have hyΛ : ∀ l ∈ L.subgroupOf M, y₀ * l = l * y₀ := fun l hl =>
    Subtype.ext (hyL _ (Subgroup.mem_subgroupOf.1 hl))
  have hyN : y ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hyL h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h1 := hyL _ hh
      have h2 : y * h * y⁻¹ * y = y * h := by group
      rw [h2] at h1
      have h3 : y * h * y⁻¹ = h := mul_left_cancel h1
      rwa [h3] at hh
  have hYy : ∀ q ∈ Y, y₀ • q ∈ Y := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, B15P4.map_commV_mem hyN u hu, rfl⟩
  set F := Y ⊓ XMod.fixed ↥(Subgroup.zpowers y₀) ⊤
  have hFinv : XMod.IsInv ↥(L.subgroupOf M) F := by
    rintro ⟨l, hl⟩ q ⟨hqY, hqF⟩
    refine ⟨hY.1 ⟨l, hl⟩ q hqY, (mem_fixed_zpowers_iff (b := y₀)).2 ?_⟩
    have h1 := (mem_fixed_zpowers_iff (b := y₀)).1 hqF
    show y₀ • (l • q) = l • q
    rw [smul_smul, hyΛ l hl, mul_smul, h1]
  obtain ⟨c', hc'⟩ := IsotypicOfLength.exists_of_le hB.quot_sq hI hY hFinv inf_le_left
  have : Fact p.Prime := ⟨hp⟩
  have hmod := card_end_pow_modEq hB.quot_sq hI hY (fun l hl => (hyΛ l hl).symm) hYy hyp hc'
  rw [hE] at hmod
  have hrkI : 0 < rk ↥I := by
    by_contra h0
    exact hI.2.1.ne' ((rk_eq_zero_iff hB.quot_sq).1 (by omega))
  have hc'2 : c' ≤ 2 := by
    have h1 := rk_mono (inf_le_left : F ≤ Y)
    rw [hc'.2.2, hY.2.2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hrkI
  have hdvd : (2 ^ n) ^ 2 - 1 ∣ Nat.card ↥L := by
    rw [hcardL, ← pow_mul, mul_comm n 2]
    exact dvd_mul_left _ _
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  interval_cases c'
  · exfalso
    apply hpL
    rw [pow_zero] at hmod
    exact (((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hpos)).1 hmod.symm)).trans hdvd
  · exfalso
    apply hpL
    rw [pow_one] at hmod
    have h1 := (Nat.modEq_iff_dvd' (Nat.le_self_pow (by norm_num) _)).1 hmod.symm
    have h2 : (2 ^ n) ^ 2 - 2 ^ n ∣ Nat.card ↥L := by
      have e1 : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
        rw [Nat.mul_sub_one, sq]
      have e2 : Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
        rw [hcardL, ← pow_mul, mul_comm n 2]
      rw [e1, e2]
      exact Nat.mul_dvd_mul_left _ (Nat.sub_one_dvd_pow_sub_one _ 2)
    exact h1.trans h2
  · have hFY : F = Y := eq_of_le_of_rk_le hB.quot_sq inf_le_left (by rw [hc'.2.2, hY.2.2])
    intro q hq
    rw [← hFY] at hq
    exact (mem_fixed_zpowers_iff (b := y₀)).1 hq.2

end CFSG.Quasithin.RonanD321
