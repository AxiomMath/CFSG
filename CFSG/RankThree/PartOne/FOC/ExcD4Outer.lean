module

public import CFSG.RankThree.PartOne.FOC.OuterLayer
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub fixSubEquiv)


theorem fixSub_le_of_mem_zpowers {G : Type} [Group G] {α β : MulAut G}
    (h : α ∈ Subgroup.zpowers β) : fixSub β ≤ fixSub α := by
  intro x hx
  have hs : β ∈ MulAction.stabilizer (MulAut G) x := by
    rw [MulAction.mem_stabilizer_iff]
    exact hx
  have := Subgroup.zpowers_le.2 hs h
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

section D4


theorem outerComp_D4 {f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    OuterComp p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine outerComp_of_fixed_simple_layer ?_
  intro β hβp hβinn
  have hβ1 : β ≠ 1 := fun h => hβinn (h ▸ Subgroup.one_mem _)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  obtain ⟨hηord, hpf, ⟨h0, hh0⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨β, Subgroup.mem_top β⟩ hβinn
      (by rw [Subgroup.orderOf_mk]; exact hβord)
  obtain ⟨d, rfl⟩ := hpf
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hf
      omega
    · exact h
  have hK3 : Nat.card K = 2 ^ (3 * d * p) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (d * p) := fun c => by rw [hσ c, mul_comm p d]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hp.pos) hK3
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let φ : K →+* K := iterateFrobenius K 2 (3 * d)
  let δ : K ≃+* K := RingEquiv.ofBijective φ (Finite.injective_iff_bijective.mp φ.injective)
  have hδ : ∀ c, δ c = c ^ 2 ^ (3 * d) := fun c => iterateFrobenius_def 2 (3 * d) c
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, hδord, -⟩ := triality_canonical_field_facts Nat.prime_two hd1 (by omega : 2 ≤ p)
    hm3 hK3 hσ' hδ
  obtain ⟨-, -, -, -, -, -, himage, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hd1
      (by omega : 2 ≤ p) hm3 K hK3 σ hσ' δ hδ
  have : IsCyclic (K ≃+* K) := hcyc
  set η : K ≃+* K := Θ β with hη
  have hηp : η ^ p = 1 := hηord ▸ pow_orderOf_eq_one η
  have hδp : δ ^ p = 1 := hδord ▸ pow_orderOf_eq_one δ
  have hηδ : η ∈ Subgroup.zpowers δ := mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hδord hηp
  have hδη : δ ∈ Subgroup.zpowers η := mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hηord hδp
  have hact : ∀ {a b : K ≃+* K}, a ∈ Subgroup.zpowers b →
      fieldActor (t := TwistTag.D4) σ a ∈ Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ b) := by
    intro a b hab
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hab
    exact ⟨k, (map_zpow (fieldActorHom (t := TwistTag.D4) σ) b k).symm⟩
  have hfix : fixSub (fieldActor (t := TwistTag.D4) σ η) =
      fixSub (fieldActor (t := TwistTag.D4) σ δ) :=
    le_antisymm (fixSub_le_of_mem_zpowers (hact hδη)) (fixSub_le_of_mem_zpowers (hact hηδ))
  have hcg : MulAut.congr (MulAut.conj h0) β = fieldActor σ η := hh0
  let e1 : ↥(fixSub β) ≃* ↥(fixSub (fieldActor (t := TwistTag.D4) σ η)) :=
    (fixSubEquiv (MulAut.conj h0) β).trans (MulEquiv.subgroupCongr (by rw [hcg]))
  let e2 : ↥(fixSub (fieldActor (t := TwistTag.D4) σ η)) ≃*
      ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) :=
    MulEquiv.subgroupCongr hfix
  let e3 : ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) ≃* ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr himage)
  let ε : ↥(fixSub β) ≃* ↥(trialityFieldImage σ δ) := (e1.trans e2).trans e3
  have hsF : IsSimpleGroup ↥(fixSub β) := ε.isSimpleGroup
  have hnc' : ∃ u v : ↥(trialityFieldImage σ δ), u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    exact hnc hcon
  obtain ⟨u, v, huv⟩ := hnc'
  refine ⟨⊤, Subgroup.topEquiv.isSimpleGroup, ?_, le_top, fun y _ => Subgroup.mem_top y⟩
  refine ⟨⟨ε.symm u, Subgroup.mem_top _⟩, ⟨ε.symm v, Subgroup.mem_top _⟩, fun h => huv ?_⟩
  apply ε.symm.injective
  rw [map_mul, map_mul]
  exact congrArg Subtype.val h

end D4

end CFSG.RankThree.PartOne.FOC
