module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.Quasithin.Vol2.Ch11SecDGroup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_orderOf_eq_of_isPGroup_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {E Y : Subgroup G}
    (hE : IsPGroup p E) (hEN : E ≤ Subgroup.normalizer (Y : Set G)) (hp : p ∣ Nat.card Y) :
    ∃ y ∈ Y, orderOf y = p ∧ ∀ e ∈ E, e * y = y * e := by
  let φ : ↥E →* MulAut ↥Y := (CFSG.Quasithin.conjAct Y).comp (Subgroup.inclusion hEN)
  let _ : MulDistribMulAction ↥E ↥Y := MulDistribMulAction.compHom ↥Y φ
  have hmod := hE.card_modEq_card_fixedPoints ↥Y
  have hdvd : p ∣ Nat.card (FixedPoints.subgroup ↥E ↥Y) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hp))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((y : ↥Y) : G), (y : ↥Y).2, ?_, fun e he => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · have hfix : (⟨e, he⟩ : ↥E) • (y : ↥Y) = y := MulAction.mem_fixedPoints.mp y.2 ⟨e, he⟩
    have h1 : e * ((y : ↥Y) : G) * e⁻¹ = ((y : ↥Y) : G) := by
      have := congrArg Subtype.val hfix
      change ((SecA.conjV Y e (hEN he) (y : ↥Y) : ↥Y) : G) = _ at this
      rwa [SecA.conjV_apply_coe] at this
    calc e * ((y : ↥Y) : G) = e * ((y : ↥Y) : G) * e⁻¹ * e := by group
      _ = ((y : ↥Y) : G) * e := by rw [h1]

theorem isElemAbelian_sup_zpowers {p : ℕ} {E : Subgroup G} {y : G} (hE : IsElemAbelian p E)
    (hy : y ^ p = 1) (hyE : ∀ e ∈ E, e * y = y * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers y) := by
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj (fun e he => ?_) (fun e he => ?_)
    · have : y * e * y⁻¹ = e := by rw [← hyE e he]; group
      rwa [this]
    · have : y⁻¹ * e * y = e := by
        rw [mul_assoc, hyE e he]
        group
      rwa [this]
  have hcomm : ∀ e ∈ E, ∀ z ∈ Subgroup.zpowers y, Commute e z := by
    intro e he z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_right (hyE e he) k
  have hEc : ∀ a ∈ E, ∀ b ∈ E, Commute a b := fun a ha b hb => by
    have := hE.1
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  have hzz : ∀ z₁ ∈ Subgroup.zpowers y, ∀ z₂ ∈ Subgroup.zpowers y, Commute z₁ z₂ := by
    intro z₁ h₁ z₂ h₂
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₁
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₂
    exact Commute.zpow_zpow_self y a b
  have hrep : ∀ x ∈ E ⊔ Subgroup.zpowers y, ∃ e ∈ E, ∃ z ∈ Subgroup.zpowers y, e * z = x := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left E _ hN] at hx
    obtain ⟨e, he, z, hz, rfl⟩ := hx
    exact ⟨e, he, z, hz, rfl⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e₁, he₁, z₁, hz₁, h₁⟩ := hrep a a.2
    obtain ⟨e₂, he₂, z₂, hz₂, h₂⟩ := hrep b b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂]
    exact ((hEc e₁ he₁ e₂ he₂).mul_right (hcomm e₁ he₁ z₂ hz₂)).mul_left
      ((hcomm e₂ he₂ z₁ hz₁).symm.mul_right (hzz z₁ hz₁ z₂ hz₂))
  · obtain ⟨e, he, z, hz, rfl⟩ := hrep x hx
    rw [(hcomm e he z hz).mul_pow, hE.2 e he, one_mul]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem card_sup_zpowers_of_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {E : Subgroup G} {y : G}
    (hyp : orderOf y = p) (hyE : ∀ e ∈ E, e * y = y * e) (hy : y ∉ E) :
    Nat.card ↥(E ⊔ Subgroup.zpowers y) = Nat.card E * p := by
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj (fun e he => ?_) (fun e he => ?_)
    · have : y * e * y⁻¹ = e := by rw [← hyE e he]; group
      rwa [this]
    · have : y⁻¹ * e * y = e := by
        rw [mul_assoc, hyE e he]
        group
      rwa [this]
  have hcy : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyp]
  have hdisj : Disjoint E (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(E ⊓ Subgroup.zpowers y) ∣ p :=
      hcy ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : E ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcy, hp'])
      exact hy ((heq ▸ inf_le_left : Subgroup.zpowers y ≤ E) (Subgroup.mem_zpowers y))
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hN hdisj, hcy]

theorem le_two_of_elemAbelian [Finite G] (hQ : CFSG.Assembly.evenRank G ≤ 2) {P F : Subgroup G}
    (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : F ≤ Subgroup.normalizer (P : Set G)) (hFab : IsElemAbelian p F)
    (hcard : Nat.card F = p ^ k) : k ≤ 2 := by
  have hbd : ∀ q : ℕ, 1 < q → ∀ H : Subgroup G, ∀ j ∈ {k | ∃ E : Subgroup G, E ≤ H ∧
      CFSG.Assembly.IsElemAbelian q E ∧ Nat.card E = q ^ k}, j ≤ Nat.card G := by
    rintro q hq H j ⟨E, -, -, hE⟩
    calc j ≤ q ^ j := (Nat.lt_pow_self hq).le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E
  have h1 : k ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (P : Set G)) :=
    le_csSup ⟨Nat.card G, hbd p hp.one_lt _⟩ ⟨F, hF, hFab, hcard⟩
  have h2 : CFSG.Assembly.pRank p (Subgroup.normalizer (P : Set G)) ≤
      CFSG.Assembly.evenRank G := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨p, _, hp, hp2, ⟨P, hP, hP2, rfl⟩, rfl⟩
    rintro j ⟨q, H, hq, -, -, rfl⟩
    exact csSup_le' (hbd q hq.one_lt H)
  omega

theorem center_SL2_eq_bot {F : Type} [Field F] (h2 : (2 : F) = 0) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  let U : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let W : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hU := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) (hz U)
  have hW := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) (hz W)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hU hW
  have hdet : (z : Matrix (Fin 2) (Fin 2) F).det = 1 := z.2
  rw [Matrix.det_fin_two] at hdet
  have e1 := congrFun (congrFun hU 0) 0
  have e2 := congrFun (congrFun hU 0) 1
  have e3 := congrFun (congrFun hW 0) 0
  simp [U, W, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hc : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e1
  have hd : (z : Matrix (Fin 2) (Fin 2) F) 1 1 = (z : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination e2
  have hb : (z : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := e3
  rw [hc, hd, hb] at hdet
  have ha : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : ((z : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) ^ 2 = 0 := by
      linear_combination hdet + ((z : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination this - h2
  rw [Subgroup.mem_bot]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem three_dvd_card_SL2 {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hneg : (-1 : F) = 1 := by linear_combination -h2
  let M : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, hneg]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM3 : M ^ 3 = 1 := by
    apply Subtype.ext
    have h11 : (1 : F) + 1 = 0 := by linear_combination h2
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h11]
  have hM1 : M ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [M] at this
  have hord : orderOf M = 3 := orderOf_eq_prime hM3 hM1
  rw [← hord]
  exact orderOf_dvd_natCard M

end CFSG.Quasithin.Vol2.Ch11.SecD
