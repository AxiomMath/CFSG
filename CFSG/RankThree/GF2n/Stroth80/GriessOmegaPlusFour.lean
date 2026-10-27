module

public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.GroupTheory.PerfectCoverProduct
public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

section SL

variable {K : Type} [Field K] [Finite K]

theorem exceptionalOrders_psl_two_mul {f : ℕ} (hf : 2 ≤ f) :
    (exceptionalOrders .PSL 2 2 f).1 * (exceptionalOrders .PSL 2 2 f).2 =
      if f = 2 then 2 else 1 := by
  by_cases h2 : f = 2
  · subst h2
    rfl
  · rw [exceptionalOrders_psl_eq_one hf (fun h => h2 h.2) (fun h => by omega)]
    simp [h2]

theorem statedSL_two_cover_pow (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (F : Type) [Group F] [Finite F] (hF : Group.IsPerfect F)
    (q : F →* ↥(StatedSL 2 K)) (hq : Function.Surjective q)
    (hqc : q.ker ≤ Subgroup.center F) :
    ∀ y ∈ q.ker, y ^ (if f = 2 then 2 else 1) = 1 := by
  let q' : F →* GL (Fin 2) K := (StatedSL 2 K).subtype.comp q
  have hrange : q'.range = StatedSL 2 K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective q hq, Subgroup.map_top,
      Subgroup.range_subtype]
  have hker : q'.ker = q.ker := by
    ext x
    simp [q', MonoidHom.mem_ker]
  have hdvd := statedSL_ker_card_dvd hGA (m := 2) le_rfl hf hK hF q' hrange (hker ▸ hqc)
  rw [hker, exceptionalOrders_psl_two_mul hf] at hdvd
  intro y hy
  have h1 : orderOf (⟨y, hy⟩ : ↥q.ker) ∣ Nat.card q.ker := orderOf_dvd_natCard _
  have h2 : (⟨y, hy⟩ : ↥q.ker) ^ (if f = 2 then 2 else 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (h1.trans hdvd)
  exact congrArg Subtype.val h2

end SL

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Group E] [Finite E]

private theorem nonempty_mulEquiv_statedOmegaPlus_four (h4 : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card K h4
  exact ⟨e.trans (MulEquiv.prodCongr (specialLinearGroupEquivStatedSL 2 K)
    (specialLinearGroupEquivStatedSL 2 K))⟩

theorem statedOmegaPlus_four_ker_exponent (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E) (π : E →* GL (Fin 2 ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadPlus 2 K)) (hker : π.ker ≤ Subgroup.center E) :
    ∀ y ∈ π.ker, y ^ (if f = 2 then 2 else 1) = 1 := by
  have h4 : 4 ≤ Nat.card K := hK ▸ two_pow_ge_four hf
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  obtain ⟨e⟩ := nonempty_mulEquiv_statedOmegaPlus_four h4
  let π₂ : E →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) := e.toMonoidHom.comp π₁
  have hπ₂ : Function.Surjective π₂ := e.surjective.comp hπ₁
  have hk₂ : π₂.ker = π.ker := by
    rw [← hk₁]
    ext x
    simp [π₂, MonoidHom.mem_ker]
  have hperf := CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card h4
  rw [← hk₂]
  exact CFSG.GroupTheory.PerfectCover.exponent_ker_prod_cover hE hperf hperf π₂ hπ₂
    (hk₂ ▸ hker) (if f = 2 then 2 else 1)
    (fun F _ _ hF q hq hqc => statedSL_two_cover_pow hGA hf hK F hF q hq hqc)
    (fun F _ _ hF q hq hqc => statedSL_two_cover_pow hGA hf hK F hF q hq hqc)

theorem statedOmegaPlus_four_ker_eq_bot (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 3 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E) (π : E →* GL (Fin 2 ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadPlus 2 K)) (hker : π.ker ≤ Subgroup.center E) :
    π.ker = ⊥ := by
  have h := statedOmegaPlus_four_ker_exponent hGA (by omega) hK hE π hrange hker
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have := h y hy
  rwa [if_neg (by omega), pow_one] at this

end Omega

end CFSG.RankThree.GF2n.Stroth80
