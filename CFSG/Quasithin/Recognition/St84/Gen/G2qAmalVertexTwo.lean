module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalLevi
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoModel
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoLocal
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoCoord
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
import CFSG.LieType.Chevalley.SylowOpposition
import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.EvenBN.G2 CFSG.ComponentClassification.UnbalancedCatalog
open scoped MatrixGroups commutatorElement

section Group

variable {G : Type} [Group G]

private theorem conj_mem_centerOf_of_mem_normalizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) {z : G} (hz : z ∈ centerOf Q) :
    g * z * g⁻¹ ∈ centerOf Q := by
  have hz1 := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz1.1,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
  have h := (Subgroup.mem_centralizer_iff.mp hz1.2) _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * y := by group

private theorem mul_comm_of_mem_utri {F : Type} [Field F] {g h : SL(2, F)} (hg : g ∈ utri F)
    (hh : h ∈ utri F) : g * h = h * g := by
  obtain ⟨s, hs⟩ := mem_utri_iff_eq_unitri.mp hg
  obtain ⟨t, ht⟩ := mem_utri_iff_eq_unitri.mp hh
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs, ht]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem map_subgroupOf_eq_of_card_le {H : Type*} [Group H] {P A : Subgroup G}
    {B : Subgroup H} [Finite B] (Φ : ↥P →* H) (hΦ : Function.Injective Φ) (hAP : A ≤ P)
    (hle : ∀ x : ↥P, (x : G) ∈ A → Φ x ∈ B) (hcard : Nat.card B ≤ Nat.card A) :
    (A.subgroupOf P).map Φ = B := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hle x (Subgroup.mem_subgroupOf.mp hx)
  · rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv]
    exact hcard

private theorem mem_iff_of_map_subgroupOf_eq {H : Type*} [Group H] {P A : Subgroup G}
    {B : Subgroup H} {Φ : ↥P →* H} (hΦ : Function.Injective Φ)
    (h : (A.subgroupOf P).map Φ = B) (x : ↥P) : (x : G) ∈ A ↔ Φ x ∈ B := by
  rw [← h]
  refine ⟨fun hx => ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  rw [← hΦ hyx]
  exact Subgroup.mem_subgroupOf.mp hy

end Group

section Local

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem G2qLocalData.commutator_mem_pCoreOf_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (hf : 1 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1)) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) : ⁅a, b⁆ ∈ pCoreOf 2 L1 := by
  obtain ⟨c⟩ := hD.exists_coordLeft hH h1
  letI := c.field
  have hS1 := hD.le_left hH hf h1
  have h : c.α ⁅(⟨a, hS1 ha⟩ : ↥L1), ⟨b, hS1 hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm_of_mem_utri ((c.memS _).mp ha) ((c.memS _).mp hb)
  exact (c.ker _).mp h

private theorem G2qLocalData.commutator_commutator_mul_comm (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (hf : 1 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    {x a₁ a₂ b : G} (hx : x ∈ pCoreOf 2 L1) (ha₁ : a₁ ∈ S) (ha₂ : a₂ ∈ S) (hb : b ∈ S) :
    ⁅x, ⁅a₁, a₂⁆⁆ * b = b * ⁅x, ⁅a₁, a₂⁆⁆ := by
  have hz : ⁅x, ⁅a₁, a₂⁆⁆ ∈ centerOf L1 := by
    rw [← hD.center_left, commutatorElement_def x]
    exact commutator_mem_centerOf_of_special hD.special_left.1 hx
      (hD.commutator_mem_pCoreOf_left hH hf h1 ha₁ ha₂)
  exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) b
    (hD.le_left hH hf h1 hb)).symm

private theorem eq_one_of_centralizes_pCoreOf_right (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1)
    (hS2 : S ≤ L2) {H₀ : Subgroup G} (hH₀B : H₀ ≤ bigB L1 L2 S) (hinf : H₀ ⊓ L2 = ⊥) {n : G}
    (hn : n ∈ H₀) (hc : ∀ u ∈ pCoreOf 2 L2, n * u * n⁻¹ = u) : n = 1 := by
  have hP : L2 ⊔ S ⊔ borelOf L1 S = L2 ⊔ bigB L1 L2 S := by
    rw [sup_bigB_right_of_le hS2, sup_eq_left.mpr hS2]
  have hct : (L2 ⊔ S ⊔ borelOf L1 S) ⊓
      Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) : Set G) ≤
        pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) := hH.h2.charTwo
  rw [hP, pCoreOf_sup_bigB_right_of_le hH hS1 hS2] at hct
  have hnQ : n ∈ pCoreOf 2 L2 := hct (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_sup_right (hH₀B hn), Subgroup.mem_centralizer_iff.mpr fun u hu => by
      calc u * n = n * u * n⁻¹ * n := by rw [hc u hu]
        _ = n * u := by group⟩)
  have hmem : n ∈ H₀ ⊓ L2 := Subgroup.mem_inf.mpr
    ⟨hn, CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 L2 hnQ⟩
  rw [hinf] at hmem
  exact Subgroup.mem_bot.mp hmem

end Local

section VertexTwo


variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem G2qLocalData.exists_mulEquiv_vertexTwo (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (hIndec : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K),
        (∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
          ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) ∧
        (∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
          ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K)) := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hf2 : 2 ≤ f := by omega
  have hS1 : S ≤ L1 := hD.le_left hH hf1 h1
  have hS2 : S ≤ L2 := hD.le_right hH hf1 h2
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  letI := c.field
  letI := c.fintype
  haveI : CharP c.F 2 := charP_of_card_eq_prime_pow
    (by rw [← Nat.card_eq_fintype_card]; exact c.card : Fintype.card c.F = 2 ^ f)
  haveI : Finite (ModGL Tag.G2 c.F) := finite_modGL
  have hK8 : 8 ≤ Nat.card c.F := by
    rw [c.card]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK3 : 3 ≤ Nat.card c.F := by omega
  obtain ⟨γ, hγ, hγker, hγeq⟩ := hD.exists_radCoord_right hf2 hH h1 h2 hIndec c.card c.α
    c.surj c.ker c.memS c.nat c.center_le c.commutator_le c.natW
  obtain ⟨δ, hδeq⟩ := exists_natCoord_of_bot c.nat
  obtain ⟨H₀, hH₀B, -, hH₀card, hH₀L, hH₀inf, hH₀sup⟩ := hD.exists_torus_right hf2 hH h1 h2
  have hH₀Q : H₀ ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hH₀B.trans hH.bigB_le_normalizer_pCoreOf_right
  have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_parB_of_coords (L := L2) (Q := pCoreOf 2 L2)
    (Z := centerOf (pCoreOf 2 L2)) (N := H₀) hK8
    (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 L2) inf_le_left
    (fun z hz x hx => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm)
    (fun x hx => hD.sq_mem_centerOf_right hx)
    (fun x hx hc => Subgroup.mem_inf.mpr
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩)
    (le_normalizer_pCoreOf 2 L2)
    (fun ℓ hℓ z hz => conj_mem_centerOf_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hℓ) hz)
    c.α c.surj c.ker γ hγ hγker hγeq δ hδeq hH₀Q
    (fun n hn z hz => conj_mem_centerOf_of_mem_normalizer (hH₀Q hn) hz)
    hH₀L (by rw [hH₀card]; exact hodd) (by rw [hH₀card, c.card]) hH₀inf
    (fun n hn hc => eq_one_of_centralizes_pCoreOf_right hH hS1 hS2 hH₀B hH₀inf hn hc)
    (by
      rw [hH₀card, hD.card_right]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
  let ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB c.F) :=
    (MulEquiv.subgroupCongr hH₀sup).trans (ψ.trans G2q.parBEquiv)
  let Φ : ↥(L2 ⊔ bigB L1 L2 S) →* ModGL Tag.G2 c.F :=
    (adjointGroup Tag.G2 c.F).subtype.comp ((g2ParB c.F).subtype.comp ψ₂.toMonoidHom)
  have hΦinj : Function.Injective Φ :=
    (adjointGroup Tag.G2 c.F).subtype_injective.comp
      ((g2ParB c.F).subtype_injective.comp ψ₂.injective)
  have hΦL : ∀ (x : ↥(L2 ⊔ bigB L1 L2 S)) (hx : (x : G) ∈ L2),
      ∃ y ∈ Model.M c.F, Φ x = y * G2q.leviBHom (c.α ⟨(x : G), hx⟩, 1) := by
    intro x hx
    obtain ⟨y, hy, hyeq⟩ := hψ ⟨(x : G), hx⟩
    exact ⟨y, hy, hyeq⟩
  have hSfwd : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S → Φ x ∈ Model.S c.F := by
    intro x hx
    obtain ⟨y, hy, hyeq⟩ := hΦL x (hS2 hx)
    obtain ⟨t, ht⟩ := mem_utri_iff_eq_unitri.mp ((c.memS ⟨(x : G), hS2 hx⟩).mp hx)
    have hαt : c.α ⟨(x : G), hS2 hx⟩ = uSL t := Subtype.ext ht
    rw [hyeq, hαt, G2q.leviBHom_uSL, pinnedX_a_eq_g2N]
    exact (Model.S c.F).mul_mem (Model.M_le_S hy) (Model.mem_S.2 ⟨_, _, _, _, _, _, rfl⟩)
  have hSmap : (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map Φ = Model.S c.F :=
    map_subgroupOf_eq_of_card_le Φ hΦinj (hS2.trans le_sup_left) hSfwd
      (by rw [Model.card_S, hD.card_S, c.card, ← pow_mul, mul_comm])
  have hSiff := mem_iff_of_map_subgroupOf_eq hΦinj hSmap
  have hQfwd : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 → Φ x ∈ Model.D c.F := by
    intro x hx
    refine (G2q.mem_D_iff_forall_commutator hK3 ((hSiff x).mp (hH.pCoreOf_le_left hx))).mpr ?_
    intro y₁ hy₁ y₂ hy₂ s hs
    rw [← hSmap] at hy₁ hy₂ hs
    obtain ⟨a₁, ha₁, rfl⟩ := hy₁
    obtain ⟨a₂, ha₂, rfl⟩ := hy₂
    obtain ⟨b, hb, rfl⟩ := hs
    rw [← map_commutatorElement, ← map_commutatorElement, ← map_mul, ← map_mul]
    exact congrArg Φ (Subtype.ext (hD.commutator_commutator_mul_comm hH hf1 h1 hx
      (Subgroup.mem_subgroupOf.mp ha₁) (Subgroup.mem_subgroupOf.mp ha₂)
      (Subgroup.mem_subgroupOf.mp hb)))
  have hQmap : ((pCoreOf 2 L1).subgroupOf (L2 ⊔ bigB L1 L2 S)).map Φ = Model.D c.F :=
    map_subgroupOf_eq_of_card_le Φ hΦinj ((hH.pCoreOf_le_left.trans hS2).trans le_sup_left)
      hQfwd (by rw [Model.card_D, hD.card_left, c.card, ← pow_mul, mul_comm])
  have hQiff := mem_iff_of_map_subgroupOf_eq hΦinj hQmap
  refine ⟨c.F, c.field, inferInstance, inferInstance, c.card, ψ₂, fun x => hSiff x,
    fun x => ?_⟩
  rw [G2q.mem_pCoreOf_g2ParA_iff, ← G2q.D_eq_parabolicRadical_one]
  exact hQiff x

end VertexTwo

end CFSG.Quasithin.F112R.St84

end
