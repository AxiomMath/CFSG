module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

section Generic

variable {G : Type*} [Group G]

theorem hind_of_pair {x y : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hy : y ∉ ({1, x, x * x} : Set G)) :
    ∀ a b : ℕ, a < 3 → b < 3 → x ^ a * y ^ b = 1 → a = 0 ∧ b = 0 := by
  intro a b ha hb h
  have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
  have hy3' : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
  have hxi : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right hx3'
  have hy4 : y * y * (y * y) = y := by rw [mul_assoc, hy3', mul_one]
  have hx4 : x * x * (x * x) = x := by rw [mul_assoc, hx3', mul_one]
  interval_cases a <;> interval_cases b <;> simp [pow_succ] at h ⊢
  ·
    exact hy (Or.inl h)
  ·
    exact hy (Or.inl (by rw [← hy3', h, mul_one]))
  ·
    exact hx1 h
  ·
    exact hy (Or.inr (Or.inr (by rw [← hxi]; exact eq_inv_of_mul_eq_one_right h)))
  ·
    have h1 : y * y = x * x := by rw [← hxi]; exact eq_inv_of_mul_eq_one_right h
    exact hy (Or.inr (Or.inl (by rw [← hy4, h1, hx4])))
  ·
    exact hx1 (by rw [← hx3', h, mul_one])
  ·
    have hxxx : x * x * x = 1 := by rw [mul_assoc]; exact hx3'
    have h1 : y = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right h
    exact hy (Or.inr (Or.inl (by rw [h1]; exact inv_eq_of_mul_eq_one_right hxxx)))
  ·
    have hxxx : x * x * x = 1 := by rw [mul_assoc]; exact hx3'
    have h1 : y * y = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : y * y = x := by rw [h1]; exact inv_eq_of_mul_eq_one_right hxxx
    exact hy (Or.inr (Or.inr (by show y = x * x; rw [← hy4, h2])))

theorem exists_gen_pair [Finite G] {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ x y : G, x ∈ E ∧ y ∈ E ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      y ∉ ({1, x, x * x} : Set G) ∧ E = Subgroup.closure {x, y} := by
  haveI := hE
  have hpow : ∀ a ∈ E, a ^ 3 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hne : E ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨⟨x, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := hpow x hxE
  have hnle : ¬ E ≤ Subgroup.zpowers x := by
    intro hle
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have h3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨y, hyE, hyx⟩ := SetLike.not_le_iff_exists.mp hnle
  have hy3 : y ^ 3 = 1 := hpow y hyE
  have hyset : y ∉ ({1, x, x * x} : Set G) := by
    intro h
    apply hyx
    rcases h with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h, ← pow_two]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
  have hxy : x * y = y * x := hcomm x hxE y hyE
  obtain ⟨-, -, hc⟩ := CFSG.AGLEmbedding.ChevOuter.closure_pair x y hx3 hy3 hxy
    (hind_of_pair hx1' hx3 hy3 hyset)
  have hle : Subgroup.closure {x, y} ≤ E := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxE
    · exact hyE
  refine ⟨x, y, hxE, hyE, hx1', hx3, hy3, hxy, hyset, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard])).symm

theorem exists_conj_le_sylow [Finite G] {S E : Subgroup G}
    (hS : Nat.card S = 3 ^ (Nat.card G).factorization 3) (hE : IsPGroup 3 E) :
    ∃ g : G, ∀ x ∈ E, g * x * g⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard S hS)
  have hPQ : S = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    have h : ((g • Q : Sylow 3 G) : Subgroup G) = S := by
      have := congrArg (fun T : Sylow 3 G => (T : Subgroup G)) hg
      simpa using this
    rw [← h, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, fun x hx => ?_⟩
  rw [hPQ]
  exact ⟨x, hQ hx, by simp [MulAut.conj_apply]⟩

theorem isElementaryAbelian_map_conj {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (g : G) :
    CFSG.IsElementaryAbelian 3 (E.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj g).toMonoidHom) = 3 ^ 2 := by
  have h1 : CFSG.Open.IsElemAbelian 3 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE
  have h2 := CFSG.Open.IsElemAbelian.map h1 (MulAut.conj g).toMonoidHom
  exact ⟨CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h2,
    by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hcard⟩

end Generic

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
