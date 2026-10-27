module

public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut fieldSp coe_fieldSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat statedSp_ext)
open CFSG.RankThree.PartTwo.KFacts (ordThreeSL ordThreeMat coe_ordThreeSL)
open CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof (slPair slPair_apply slPair_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uc22s218k_exists_torus_plus (h3 : 3 ∣ Nat.card K + 1) :
    ∃ (B : SL(2, K)) (S : Subgroup SL(2, K)), orderOf B = Nat.card K + 1 ∧ ordThreeSL K ∈ S ∧
      S ≤ zpowers B ∧ IsPGroup 3 S ∧ ¬ 3 ∣ S.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B₀, hB₀⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  have hidxB : ¬ 3 ∣ (zpowers B₀).index := by
    have h1 := (zpowers B₀).card_mul_index
    rw [Nat.card_zpowers, hB₀, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
    obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by
      have := Nat.card_pos (α := K)
      omega⟩
    have e : Nat.card K * (Nat.card K ^ 2 - 1) = (Nat.card K + 1) * (Nat.card K * r) := by
      rw [hr, show (r + 1) ^ 2 - 1 = (r + 2) * r from Nat.sub_eq_of_eq_add (by ring)]
      ring
    rw [Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans e)]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h <;> omega
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 ↥(zpowers B₀)) := inferInstance
  have hS₀p : IsPGroup 3 ((P₀ : Subgroup ↥(zpowers B₀)).map (zpowers B₀).subtype) :=
    P₀.isPGroup'.map _
  have hS₀i : ¬ 3 ∣ ((P₀ : Subgroup ↥(zpowers B₀)).map (zpowers B₀).subtype).index := by
    rw [index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact P₀.not_dvd_index h
    · exact hidxB h
  have hζo : orderOf (ordThreeSL K) = 3 :=
    orderOf_eq_prime (CFSG.RankThree.PartTwo.KFacts.ordThreeSL_pow_three K)
      (CFSG.RankThree.PartTwo.KFacts.ordThreeSL_ne_one K)
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.exists_conj_map_le_sylow'
    (hS₀p.toSylow hS₀i) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hζo, pow_one]) :
      IsPGroup 3 (zpowers (ordThreeSL K)))
  rw [IsPGroup.toSylow_coe] at hc
  refine ⟨MulAut.conj c⁻¹ B₀, ((P₀ : Subgroup ↥(zpowers B₀)).map (zpowers B₀).subtype).map
    (MulAut.conj c⁻¹).toMonoidHom, by rw [MulEquiv.orderOf_eq, hB₀], ?_, ?_, hS₀p.map _, ?_⟩
  · refine ⟨_, hc (mem_map_of_mem _ (mem_zpowers _)), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (map_subtype_le _ hx)
    exact ⟨k, by simp only [MulEquiv.coe_toMonoidHom, map_zpow]⟩
  · rwa [index_map_of_bijective (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).bijective]

omit [Finite K] [CharP K 2] in
private theorem uc22s218k_fieldSp_lam (σ : K ≃+* K) (i : Fin 2) :
    fieldSp 2 K σ (lam i (ordThreeSL K)) = lam i (ordThreeSL K) := by
  apply statedSp_ext
  rw [coe_fieldSp, coe_lam, coe_ordThreeSL]
  ext x y
  simp only [Matrix.map_apply, pairMat, Matrix.of_apply, ordThreeMat]
  split_ifs <;> simp [Matrix.one_apply, apply_ite]

theorem uc22s218k_odd_model {p : ℕ} (hpK : p ∣ Nat.card K + 1) (h3 : 3 ∣ Nat.card K + 1) :
    ∃ E Q : Subgroup (StatedProj (StatedSp 2 K)), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ≤ Q ∧ IsPGroup 3 Q ∧ ¬ 3 ∣ Q.index ∧
      Q ≤ centralizer (E : Set (StatedProj (StatedSp 2 K))) ∧ (∀ x ∈ Q, x ^ 3 = 1 → x ∈ E) ∧
      (∃ z ∈ centralizer (E : Set (StatedProj (StatedSp 2 K))), orderOf z = p) ∧
      ∀ σ : K ≃+* K, ∀ x ∈ E, fieldAut 2 K σ x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, S, hB, hζS, hSB, hSp, hSi⟩ := uc22s218k_exists_torus_plus h3
  have hζo : orderOf (ordThreeSL K) = 3 :=
    orderOf_eq_prime (CFSG.RankThree.PartTwo.KFacts.ordThreeSL_pow_three K)
      (CFSG.RankThree.PartTwo.KFacts.ordThreeSL_ne_one K)
  have hζB : zpowers (ordThreeSL K) ≤ zpowers B := (zpowers_le.2 hζS).trans hSB
  let ψ : SL(2, K) × SL(2, K) →* StatedProj (StatedSp 2 K) := (proj 2 K).comp (slPair K)
  have hψ : Function.Injective ψ :=
    CFSG.RankThree.PartTwo.KFacts.proj_injective_of_charTwo.comp slPair_injective
  have hcB : ∀ a ∈ zpowers B, ∀ b ∈ zpowers B, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self B i j).eq
  have hΩ : ∀ a ∈ zpowers B, a ^ 3 = 1 → a ∈ zpowers (ordThreeSL K) := by
    intro a ha ha3
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    have h1 := (IsCyclic.subgroup_eq_iff_card_eq (H := zpowers (⟨a, ha⟩ : zpowers B))
      (K := zpowers (⟨ordThreeSL K, hζB (mem_zpowers _)⟩ : zpowers B))).2 (by
        rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hζo,
          orderOf_eq_prime ha3 ha1])
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h1 ▸ mem_zpowers _ : (⟨a, ha⟩ : zpowers B) ∈
      zpowers (⟨ordThreeSL K, hζB (mem_zpowers _)⟩ : zpowers B))
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hel : IsElemAbelian 3 ((zpowers (ordThreeSL K)).prod (zpowers (ordThreeSL K))) := by
    refine CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.2 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact Prod.ext (hcB _ (hζB ha.1) _ (hζB hb.1)) (hcB _ (hζB ha.2) _ (hζB hb.2))
    · exact Prod.ext (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers ha.1).trans
        hζo.dvd)) (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers ha.2).trans hζo.dvd))
  obtain ⟨a, ha⟩ := hSp.exists_card_eq
  refine ⟨((zpowers (ordThreeSL K)).prod (zpowers (ordThreeSL K))).map ψ, (S.prod S).map ψ,
    hel.map ψ, ?_, map_mono (prod_mono (zpowers_le.2 hζS) (zpowers_le.2 hζS)),
    (IsPGroup.of_card (n := a + a) ?_).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_map_of_injective hψ, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_zpowers, hζo, sq]
  · rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, pow_add]
  · rw [index_map_of_injective _ hψ, index_prod, MonoidHom.range_comp, index_map_of_bijective
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h <;> exact hSi h
    · exact CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.not_three_dvd_index_slPair h
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Prod.ext (hcB _ (hζB hy.1) _ (hSB hx.1)) (hcB _ (hζB hy.2) _ (hSB hx.2)))
  · rintro _ ⟨x, hx, rfl⟩ h
    rw [← map_pow, ← map_one ψ] at h
    have h1 := hψ h
    exact ⟨x, ⟨hΩ _ (hSB hx.1) (congrArg Prod.fst h1), hΩ _ (hSB hx.2) (congrArg Prod.snd h1)⟩,
      rfl⟩
  · refine ⟨ψ (B ^ (orderOf B / p), 1), ?_, ?_⟩
    · rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Prod.ext (hcB _ (hζB hy.1) _ (pow_mem (mem_zpowers B) _)) (by simp))
    · rw [orderOf_injective ψ hψ, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_right,
        orderOf_pow_orderOf_div (by rw [hB]; omega) (by rw [hB]; exact hpK)]
  · have hfix : ∀ σ : K ≃+* K, ∀ i : Fin 2, zpowers (ordThreeSL K) ≤
        ((fieldSp 2 K σ).toMonoidHom.comp (lam i)).eqLocus (lam i) := fun σ i =>
      zpowers_le.2 (uc22s218k_fieldSp_lam σ i)
    rintro σ _ ⟨⟨x₁, x₂⟩, hx, rfl⟩
    show fieldAut 2 K σ (proj 2 K (slPair K (x₁, x₂))) = proj 2 K (slPair K (x₁, x₂))
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj, slPair_apply,
      map_mul (fieldSp 2 K σ)]
    exact congrArg (proj 2 K) (congrArg₂ (· * ·) (hfix σ 0 hx.1) (hfix σ 1 hx.2))

end CFSG.LocalAnalysis.UniquenessCase.UC22
