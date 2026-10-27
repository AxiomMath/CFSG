module

public import CFSG.Sporadic.Schreier.LyGLQSylow
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Pointwise

theorem exists_sylow_fixed (α : MulAut J) (hα : α ^ 2 = 1) :
    ∃ P : Sylow 2 J, ∀ x ∈ (P : Subgroup J), α x ∈ (P : Subgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers α) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hdvd : orderOf g ∣ 2 := by
      rw [← Subgroup.orderOf_coe]
      exact (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one hα)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨P, hP⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 J)
    (not_dvd_card_sylow 2 J)
  refine ⟨P, fun x hx => ?_⟩
  have hfix : (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) • P = P := hP _
  have h1 : ((⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) • x) ∈
      ((⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) • (P : Subgroup J)) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have h2 : ((⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) • x) ∈
      (((⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) • P : Sylow 2 J) : Subgroup J) := h1
  rw [hfix] at h2
  exact h2

theorem fixed_pair_J (α : MulAut J) (hα : α ^ 2 = 1) :
    ∃ u v : J, u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ α u = u ∧
      α v = v := by
  obtain ⟨P, hP⟩ := exists_sylow_fixed α hα
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J lySylow P
  have hPg : (P : Subgroup J) = MulAut.conj g • lyS := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hαα : ∀ y : J, α (α y) = y := fun y => by
    have := DFunLike.congr_fun hα y
    rwa [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
  have hmem : ∀ x ∈ lyS, g⁻¹ * α (g * x * g⁻¹) * g ∈ lyS := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ (P : Subgroup J) := by
      rw [hPg]
      exact ⟨x, hx, rfl⟩
    have h2 := hP _ h1
    rw [hPg, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
    have e : (MulAut.conj g)⁻¹ • α (g * x * g⁻¹) = g⁻¹ * α (g * x * g⁻¹) * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [e] at h2
    exact h2
  have hinv : ∀ x : J, g⁻¹ * α (g * (g⁻¹ * α (g * x * g⁻¹) * g) * g⁻¹) * g = x := by
    intro x
    rw [show g * (g⁻¹ * α (g * x * g⁻¹) * g) * g⁻¹ = α (g * x * g⁻¹) by group, hαα]
    group
  let β : MulAut lyS :=
    { toFun := fun x => ⟨g⁻¹ * α (g * x * g⁻¹) * g, hmem x x.2⟩
      invFun := fun x => ⟨g⁻¹ * α (g * x * g⁻¹) * g, hmem x x.2⟩
      left_inv := fun x => Subtype.ext (hinv x)
      right_inv := fun x => Subtype.ext (hinv x)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        rw [show g * (x * y : J) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group, map_mul]
        group) }
  have hβ : ∀ x : lyS, (β x : J) = g⁻¹ * α (g * x * g⁻¹) * g := fun _ => rfl
  have hβ2 : β ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hβ, hβ]
    exact hinv x
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne, hfa, hfb⟩ := fixed_pair β hβ2
  have hfix : ∀ x : lyS, β x = x → α (g * x * g⁻¹) = g * x * g⁻¹ := by
    intro x hx
    have h1 := congrArg Subtype.val hx
    rw [hβ] at h1
    calc α (g * x * g⁻¹) = g * (g⁻¹ * α (g * x * g⁻¹) * g) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [h1]
  refine ⟨g * a * g⁻¹, g * b * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, hfix a hfa, hfix b hfb⟩
  · have h1 : (a : J) * a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    calc g * (a : J) * g⁻¹ * (g * a * g⁻¹) = g * ((a : J) * a) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have h1 : (b : J) * b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    calc g * (b : J) * g⁻¹ * (g * b * g⁻¹) = g * ((b : J) * b) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have h1 : (a : J) * b = b * a := by
      have := congrArg Subtype.val hab
      simpa using this
    calc g * (a : J) * g⁻¹ * (g * b * g⁻¹) = g * ((a : J) * b) * g⁻¹ := by group
      _ = g * ((b : J) * a) * g⁻¹ := by rw [h1]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · intro h
    apply ha1
    apply Subtype.ext
    calc (a : J) = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hb1
    apply Subtype.ext
    calc (b : J) = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hne
    apply Subtype.ext
    calc (a : J) = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [h]
      _ = b := by group

theorem mem_fourSub {G : Type*} [Group G] {u v : G} {hu : u * u = 1} {hv : v * v = 1}
    {huv : u * v = v * u} {x : G} :
    x ∈ fourSub u v hu hv huv ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := Iff.rfl

theorem fourSub_ea {G : Type*} [Group G] {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) : CFSG.IsElementaryAbelian 2 (fourSub u v hu hv huv) := by
  have e5 : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu, hv, one_mul]
  have hcu : ∀ x ∈ fourSub u v hu hv huv, x * u = u * x := by
    rintro x (rfl | rfl | rfl | rfl)
    · rw [one_mul, mul_one]
    · rfl
    · exact huv.symm
    · rw [mul_assoc, ← huv]
  have hcv : ∀ x ∈ fourSub u v hu hv huv, x * v = v * x := by
    rintro x (rfl | rfl | rfl | rfl)
    · rw [one_mul, mul_one]
    · exact huv
    · rfl
    · calc u * v * v = v * u * v := by rw [huv]
        _ = v * (u * v) := by group
  apply mk_ea
  · intro x hx y hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hcu x hx
    · exact hcv x hx
    · calc x * (u * v) = (x * u) * v := (mul_assoc _ _ _).symm
        _ = (u * x) * v := by rw [hcu x hx]
        _ = u * (x * v) := mul_assoc _ _ _
        _ = u * (v * x) := by rw [hcv x hx]
        _ = u * v * x := (mul_assoc _ _ _).symm
  · rintro a (rfl | rfl | rfl | rfl)
    · exact one_mul 1
    · exact hu
    · exact hv
    · exact e5

theorem card_fourSub {G : Type*} [Group G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    Nat.card (fourSub u v hu hv huv) = 4 := by
  classical
  have h1 : u * v ≠ 1 := by
    intro h
    apply hne
    calc u = u * (v * v) := by rw [hv, mul_one]
      _ = (u * v) * v := by rw [mul_assoc]
      _ = v := by rw [h, one_mul]
  have h2 : u * v ≠ u := fun h => hv1 (by
    calc v = u⁻¹ * (u * v) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h3 : u * v ≠ v := fun h => hu1 (by
    calc u = (u * v) * v⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have e : (fourSub u v hu hv huv : Set G) = (({1, u, v, u * v} : Finset G) : Set G) := by
    rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_pair]
    rfl
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h3.symm]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne, h2.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu1, Ne.symm hv1, Ne.symm h1⟩

theorem two_le_pRank_of_four {H : Type*} [Group H] [Finite H] (E : Subgroup H)
    (hea : CFSG.IsElementaryAbelian 2 E) (hcard : Nat.card E = 4) : 2 ≤ CFSG.pRank 2 H := by
  apply le_csSup
  · refine ⟨Nat.card H, fun r hr => ?_⟩
    obtain ⟨A, -, hA⟩ := hr
    have h1 : 2 ^ r ≤ Nat.card H := hA ▸ Subgroup.card_le_card_group A
    exact le_trans Nat.lt_two_pow_self.le h1
  · exact ⟨E, hea, by rw [hcard]; norm_num⟩

theorem outer_involution_fixed_rank_one_exclusion {L : Type*} [Group L]
    (hL : Nonempty (L ≃* NativeSporadic.Ly)) (α : MulAut L) (hα : α ^ 2 = 1) :
    (∃ E : Subgroup L, E ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
      2 ≤ CFSG.pRank 2 (fixedSubgroup α) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hL
  have e : L ≃* J := e₀.trans lyEquivJ
  have : Finite L := Finite.of_equiv J e.symm.toEquiv
  have hαJ : (e.symm.trans (α.trans e) : MulAut J) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro y
    have := DFunLike.congr_fun hα (e.symm y)
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
    show e (α (e.symm (e (α (e.symm y))))) = y
    rw [MulEquiv.symm_apply_apply, this, MulEquiv.apply_symm_apply]
  obtain ⟨u, v, hu, hv, huv, hu1, hv1, hne, hfu, hfv⟩ := fixed_pair_J _ hαJ
  have hfix : ∀ y : J, e (α (e.symm y)) = y → α (e.symm y) = e.symm y := by
    intro y hy
    have := congrArg e.symm hy
    rwa [MulEquiv.symm_apply_apply] at this
  have hu' : e.symm u * e.symm u = 1 := by rw [← map_mul, hu, map_one]
  have hv' : e.symm v * e.symm v = 1 := by rw [← map_mul, hv, map_one]
  have huv' : e.symm u * e.symm v = e.symm v * e.symm u := by rw [← map_mul, huv, map_mul]
  have hu1' : e.symm u ≠ 1 := fun h => hu1 (by rw [← e.apply_symm_apply u, h, map_one])
  have hv1' : e.symm v ≠ 1 := fun h => hv1 (by rw [← e.apply_symm_apply v, h, map_one])
  have hne' : e.symm u ≠ e.symm v := fun h => hne (e.symm.injective h)
  have hle : fourSub (e.symm u) (e.symm v) hu' hv' huv' ≤ fixedSubgroup α := by
    intro x hx
    show α x = x
    rcases mem_fourSub.1 hx with rfl | rfl | rfl | rfl
    · exact map_one α
    · exact hfix u hfu
    · exact hfix v hfv
    · rw [map_mul, hfix u hfu, hfix v hfv]
  have hea := fourSub_ea hu' hv' huv'
  have hcard := card_fourSub hu' hv' huv' hu1' hv1' hne'
  refine ⟨⟨_, hle, hea, hcard⟩, ?_⟩
  have := hea
  exact two_le_pRank_of_four ((fourSub (e.symm u) (e.symm v) hu' hv' huv').subgroupOf
    (fixedSubgroup α)) (CFSG.IsElementaryAbelian.subgroupOf hle)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard])

end CFSG.Sporadic.LySchreier
