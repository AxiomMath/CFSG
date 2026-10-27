module

public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqCard
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqPar
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.F112R

open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.NFq CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open scoped Pointwise commutatorElement

section Model


private theorem d4Zz_subgroupOf_le_commutator
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    (d4Zz K σ).subgroupOf (d4Vr K σ) ≤ commutator ↥(d4Vr K σ) := by
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨f, hf⟩ := (mem_Zg_iff σ hσ).1 hz
  have hx5 : vmk σ (0, 0, 0, f) 0 ∈ d4Vr K σ := vmk_mem σ hσ _ _
  have hx2 : vmk σ ((1 : d4k K σ), 0, 0, 0) 0 ∈ d4Vr K σ := vmk_mem σ hσ _ _
  have hx2' : vmk σ ((1 : d4k K σ), 0, 0, 0) 0 = d4x₂ K (1 : K) := by
    simpa using (x2_eq_vmk σ (1 : d4k K σ)).symm
  have hzeq : (z : ModGL TwistTag.D4.tag K) =
      ⁅vmk σ (0, 0, 0, f) 0, vmk σ ((1 : d4k K σ), 0, 0, 0) 0⁆ := by
    rw [hf, ← x6_eq_vmk, ← x5_eq_vmk, hx2', comm_d4x₅_d4x₂, mul_one]
  have h1 : (z : ModGL TwistTag.D4.tag K) ∈ ⁅d4Vr K σ, d4Vr K σ⁆ := by
    rw [hzeq]
    exact Subgroup.commutator_mem_commutator hx5 hx2
  rw [← Subgroup.map_subtype_commutator] at h1
  obtain ⟨w, hw, hwz⟩ := h1
  rwa [← (d4Vr K σ).subtype_injective hwz]

theorem isSpecialPow_d4Q0 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (2 ^ f)) :
    IsSpecialPow 2 (2 ^ f) 4 ↥(Q0 σ) := by
  have hQ : Q0 σ = d4Vr K σ := radical_eq_simpleComplement σ.toRingHom fa0 supp_fa0
  rw [hQ]
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := charP_two_of_std (K := K) hf hK
  haveI hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_cube σ hK hσq
  have hcardQ : Nat.card ↥(d4Vr K σ) = (2 ^ f) ^ 9 := card_Qg σ hf hK hσq
  have hP : IsPGroup 2 ↥(d4Vr K σ) := by
    refine IsPGroup.of_card (n := 9 * f) ?_
    rw [hcardQ, ← pow_mul, mul_comm]
  have hcenter : Subgroup.center ↥(d4Vr K σ) =
      (d4Zz K σ).subgroupOf (d4Vr K σ) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    constructor
    · intro hz
      exact (Zg_iff_center σ hσ).1 ⟨z.2, fun y hy =>
        (congrArg Subtype.val (hz ⟨y, hy⟩)).symm⟩
    · intro hz y
      exact Subtype.ext (Zg_central_Qg σ hσ y.2 hz)
  have hcomm : commutator ↥(d4Vr K σ) = Subgroup.center ↥(d4Vr K σ) := by
    rw [hcenter]
    refine le_antisymm ?_ (d4Zz_subgroupOf_le_commutator σ hσ)
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅x, y⁆ : ↥(d4Vr K σ)) : ModGL TwistTag.D4.tag K) =
        ⁅(x : ModGL TwistTag.D4.tag K), (y : ModGL TwistTag.D4.tag K)⁆ :=
      map_commutatorElement (d4Vr K σ).subtype x y
    rw [hcoe]
    exact commutator_mem_Zg σ hσ x.2 y.2
  have hsq : ∀ y : ↥(d4Vr K σ), y ^ 2 ∈ Subgroup.center ↥(d4Vr K σ) := by
    intro y
    rw [hcenter, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_pow, pow_two, Subgroup.coe_mul] using sq_mem_Zg σ hσ y.2
  have hfr : frattini ↥(d4Vr K σ) = Subgroup.center ↥(d4Vr K σ) := by
    haveI : Fact (IsPGroup 2 ↥(d4Vr K σ)) := ⟨hP⟩
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥(d4Vr K σ)) (p := 2)]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · rwa [hcomm] at hx
      · exact hsq y
    · intro x hx
      exact Subgroup.subset_closure (Or.inl (by rwa [hcomm]))
  have hZpow : ∀ z ∈ Subgroup.center ↥(d4Vr K σ), z ^ 2 = 1 := by
    intro z hz
    rw [hcenter] at hz
    obtain ⟨h, hh⟩ := (mem_Zg_iff σ hσ).1 (Subgroup.mem_subgroupOf.mp hz)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_two, hh, ← x6_eq_vmk]
    exact d4x₆_mul_self K h
  refine ⟨⟨hP, Or.inr ⟨hcomm, hfr, hZpow⟩⟩, ?_, ?_⟩
  · simpa [hcardQ]
  · rw [hcenter]
    calc Nat.card ↥((d4Zz K σ).subgroupOf (d4Vr K σ))
        = Nat.card ↥(d4Zz K σ) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Zg_le_Qg σ hσ)).toEquiv
      _ = 2 ^ f := card_Zg σ hf hK hσq

theorem card_d4Q1 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card ↥(Q1 σ) = (2 ^ f) ^ 11 := by
  have hQ1 : Q1 σ = graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1 :=
    radical_eq_simpleComplement σ.toRingHom fa1 supp_fa1
  rw [hQ1]
  classical
  haveI hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUcard : Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) =
      (2 ^ f) ^ 12 := card_U σ hf hK hσq
  have hLa : Nat.card (orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 ^ f := by
    have h := card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
      (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσq c) fa1
    rwa [orbit_card_fa1, pow_one] at h
  obtain ⟨-, -, hset, -, -, huniq, -, -, -, -⟩ :=
    fixed_simple_positive_complement TwistTag.D4 K σ fa1
  let toU : ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1) ×
      orbitField TwistTag.D4 K σ.toRingHom fa1 →
      ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := fun p =>
    ⟨(p.1 : ModGL TwistTag.D4.tag K) *
        (orbitX TwistTag.D4 K σ.toRingHom fa1 p.2 : ModGL TwistTag.D4.tag K), by
      change (p.1 : ModGL TwistTag.D4.tag K) *
          (orbitX TwistTag.D4 K σ.toRingHom fa1 p.2 : ModGL TwistTag.D4.tag K) ∈
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K))
      rw [hset]
      exact Set.mul_mem_mul p.1.2 ⟨p.2, rfl⟩⟩
  have hbij : Function.Bijective toU := by
    constructor
    · rintro ⟨v, c⟩ ⟨v', c'⟩ h
      have h' : (v : ModGL TwistTag.D4.tag K) *
          (orbitX TwistTag.D4 K σ.toRingHom fa1 c : ModGL TwistTag.D4.tag K) =
          (v' : ModGL TwistTag.D4.tag K) *
            (orbitX TwistTag.D4 K σ.toRingHom fa1 c' : ModGL TwistTag.D4.tag K) :=
        congrArg Subtype.val h
      obtain ⟨hv, hc⟩ := huniq (v : ModGL TwistTag.D4.tag K) v.2
        (v' : ModGL TwistTag.D4.tag K) v'.2 c c' h'
      exact Prod.ext (Subtype.ext hv) hc
    · rintro ⟨u, hu⟩
      have hu' : (u : ModGL TwistTag.D4.tag K) ∈
          (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1 : Set
            (ModGL TwistTag.D4.tag K)) *
            Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom fa1 =>
              (orbitX TwistTag.D4 K σ.toRingHom fa1 c : ModGL TwistTag.D4.tag K)) := by
        rw [← hset]
        exact hu
      obtain ⟨v, hv, x, ⟨c, rfl⟩, hvc⟩ := hu'
      exact ⟨(⟨v, hv⟩, c), Subtype.ext hvc⟩
  have hcard := Nat.card_congr (Equiv.ofBijective toU hbij)
  rw [Nat.card_prod, hUcard, hLa] at hcard
  have hqpos : 0 < 2 ^ f := pow_pos (by norm_num) f
  refine Nat.eq_of_mul_eq_mul_right hqpos ?_
  calc Nat.card ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1) * 2 ^ f
      = (2 ^ f) ^ 12 := hcard
    _ = (2 ^ f) ^ 11 * 2 ^ f := by
        rw [show 12 = 11 + 1 by norm_num, pow_succ]

end Model

end CFSG.Quasithin.F112R
