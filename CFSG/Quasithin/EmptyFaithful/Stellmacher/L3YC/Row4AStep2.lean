module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Lemma2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Lemma2Bridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AOut
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section SL

def sl4A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

def sl4B : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide⟩

theorem sl4A_pow_three : sl4A ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem sl4B_pow_three : sl4B ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem sl4A_ne_one : sl4A ≠ 1 := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this
  decide

theorem sl4B_ne_one : sl4B ≠ 1 := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this
  decide

theorem sl4A_mul_sl4B : sl4A * sl4B = sl4B * sl4A := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  decide

theorem sl4B_ne_pow : ∀ r : ℤ, sl4A ^ r ≠ sl4B := by
  intro r hr
  have h3 : sl4A ^ r = sl4A ^ (r % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv r 3, zpow_add, zpow_mul]
    have : sl4A ^ (3 : ℤ) = 1 := by exact_mod_cast sl4A_pow_three
    rw [this, one_zpow, mul_one]
  rw [h3] at hr
  have hr' : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hr' with h | h | h <;> rw [h] at hr
  · simp only [zpow_zero] at hr
    exact sl4B_ne_one hr.symm
  · simp only [zpow_one] at hr
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) hr
    revert this
    decide
  · have hh : sl4A ^ (2 : ℤ) = sl4A ^ 2 := zpow_ofNat _ 2
    rw [hh] at hr
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) hr
    simp only [Matrix.SpecialLinearGroup.coe_pow] at this
    revert this
    decide

theorem exists_E9_sl4 :
    ∃ E : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : orderOf sl4A = 3 := orderOf_eq_prime sl4A_pow_three sl4A_ne_one
  obtain ⟨hE, hEc⟩ := isElemAbelian_zpowers_order_three hA
  have hB : orderOf sl4B = 3 := orderOf_eq_prime sl4B_pow_three sl4B_ne_one
  have hcomm : ∀ e ∈ Subgroup.zpowers sl4A, e * sl4B = sl4B * e := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((show Commute sl4A sl4B from sl4A_mul_sl4B).zpow_left k).eq
  obtain ⟨hE', hEc'⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (G := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (p := 3) (E := Subgroup.zpowers sl4A) hE (y := sl4B) hB
    (fun e he => (hcomm e he)) (fun h => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact sl4B_ne_pow k hk)
  exact ⟨_, hE', by rw [hEc', hEc]⟩

end SL

section Transfer

variable {X : Type} [Group X]

theorem nonempty_mulEquiv_sl_of_isPSL {n : ℕ} (h : IsPSL n 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two n K
    (by simpa using hK))⟩

theorem eq_one_of_central_isPSL {n : ℕ} (h : IsPSL n 2 1 X) {z : X}
    (hz : ∀ a : X, z * a = a * z) : z = 1 := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_sl_of_isPSL h
  have hc : φ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg φ (hz (φ.symm g))
    simpa using this.symm
  rw [CFSG.QuasithinUnique.Setup.Family.center_specialLinear_eq_bot_of_card_two n (ZMod 2)
    (by simp), Subgroup.mem_bot] at hc
  exact φ.injective (by rw [hc, map_one])

theorem isElemAbelian_map {Y Z : Type*} [Group Y] [Group Z] {E : Subgroup Y}
    (hE : IsElemAbelian 3 E) (f : Y →* Z) : IsElemAbelian 3 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem exists_E9_of_isPSL_four (h : IsPSL 4 2 1 X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_sl_of_isPSL h
  obtain ⟨E, hE, hEc⟩ := exists_E9_sl4
  exact ⟨E.map φ.symm.toMonoidHom, isElemAbelian_map hE _,
    by rw [Subgroup.card_map_of_injective φ.symm.injective, hEc]⟩

end Transfer

section Main

variable {G : Type} [Group G] [Finite G]

theorem row4a_three_mem {H L₁ : Subgroup G} (hN : (L₁.subgroupOf H).Normal)
    (hrk : CFSG.Open.pRank 3 H ≤ 2) (h42 : IsPSL 4 2 1 ↥(modO2Image H L₁)) :
    ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H, (∃ m : ℕ, g ^ 3 ^ m = 1) → g ∈ modO2Image H L₁ := by
  have hNn : (modO2Image H L₁).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rintro g ⟨m, hg⟩
  refine mem_of_T1_T2 (N := modO2Image H L₁) (le_nine_modO2_of_pRank_le H hrk) ?_ ?_ ?_ hg
  · obtain ⟨E, hE, hEc⟩ := exists_E9_of_isPSL_four h42
    refine ⟨E.map (modO2Image H L₁).subtype, ?_, isElemAbelian_map hE _, ?_⟩
    · rintro _ ⟨a, -, rfl⟩
      exact a.2
    · rw [Subgroup.card_map_of_injective (modO2Image H L₁).subtype_injective, hEc]
  · intro z hz hzc
    have := eq_one_of_central_isPSL h42 (z := ⟨z, hz⟩) (fun a => Subtype.ext (hzc a a.2))
    exact congrArg Subtype.val this
  · intro g hg3
    obtain ⟨m, hm⟩ := hg3
    have hτ : (MulAut.conjNormal g : MulAut ↥(modO2Image H L₁)) ^ 3 ^ m = 1 := by
      rw [← map_pow, hm, map_one]
    obtain ⟨n, hn⟩ := inner_of_three_pow_L42 h42 _ hτ
    refine ⟨n.1, n.2, fun a ha => ?_⟩
    have := congrArg (fun τ : MulAut ↥(modO2Image H L₁) => (τ ⟨a, ha⟩ : _).1) hn
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this

theorem row4a_three_mem_centralizer {c₀ : G} (hc1 : c₀ ≠ 1) (hc2 : c₀ * c₀ = 1)
    (hev : evenRank G ≤ 2) {L₁ : Subgroup G}
    (hN : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (h42 : IsPSL 4 2 1 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)) :
    ∀ g : ↥(Subgroup.centralizer ({c₀} : Set G)) ⧸
        CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)),
      (∃ m : ℕ, g ^ 3 ^ m = 1) →
        g ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁ := by
  have hloc : IsTwoLocal (Subgroup.centralizer ({c₀} : Set G)) :=
    CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one (by rw [pow_two]; exact hc2) hc1
  have hrk := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  exact row4a_three_mem hN (hrk.trans hev) h42

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
