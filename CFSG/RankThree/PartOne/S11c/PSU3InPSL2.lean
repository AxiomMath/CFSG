module

public import CFSG.RankThree.PartOne.S11c.ClassicalFiveFixed

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem commute_of_commute_nonscalar {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V = 2) {z A B : Module.End k V}
    (hz : ∀ a : k, z ≠ a • (1 : Module.End k V)) (hA : Commute A z) (hB : Commute B z) :
    Commute A B := by
  obtain ⟨v, hv⟩ : ∃ v, LinearIndependent k ![v, z v] := by
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    exact hz a ha
  have hspan : Submodule.span k (Set.range ![v, z v]) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hrange : Set.range ![v, z v] = {v, z v} := by
    simp [Matrix.range_cons]
    exact Set.pair_comm _ _
  have key : ∀ T : Module.End k V, Commute T z → ∃ α β : k, T = α • 1 + β • z := by
    intro T hT
    have hTv : T v ∈ Submodule.span k ({v, z v} : Set V) := by
      rw [← hrange, hspan]; exact Submodule.mem_top
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hTv
    refine ⟨α, β, ?_⟩
    apply LinearMap.ext_on hspan
    rintro w ⟨i, rfl⟩
    fin_cases i
    · simp [← hαβ]
    · have h1 : T (z v) = z (T v) := by
        have := congrArg (fun F : Module.End k V => F v) hT.eq
        simpa using this
      simp [h1, ← hαβ, map_add, map_smul]
  obtain ⟨α, β, rfl⟩ := key A hA
  obtain ⟨α', β', rfl⟩ := key B hB
  have hzQ : Commute z (α' • (1 : Module.End k V) + β' • z) :=
    Commute.add_right ((Commute.one_right z).smul_right α') ((Commute.refl z).smul_right β')
  exact Commute.add_left ((Commute.one_left _).smul_left α) (hzQ.smul_left β)

theorem exists_heisenberg_of_cover {B G : Type} [Group B] [Group G] [Finite G]
    (hB : StatedClassicalModel B .PSU 3 5 1) (ν : G →* B) (hν : Function.Surjective ν)
    (hcent : ν.ker ≤ Subgroup.center G) :
    ∃ x y : G, x ^ 5 = 1 ∧ ⁅y, x⁆ ^ 5 = 1 ∧ Commute ⁅y, x⁆ x ∧ Commute ⁅y, x⁆ y ∧
      ⁅y, x⁆ ≠ 1 := by
  obtain ⟨hcard, hperf, -, -⟩ := CFSG.RankThree.Classical.unitary_three_five_model B hB
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, hFperf, hFsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective ν hν hcent hperf
  have : Group.IsPerfect (commutator G) := hFperf
  let νF : commutator G →* B := ν.comp (commutator G).subtype
  have hνF : Function.Surjective νF := hFsurj
  have hcentF : νF.ker ≤ Subgroup.center (commutator G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hgE : (g : G) ∈ ν.ker := hg
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcent hgE) (g' : G))
  have hC5 := not_five_dvd_card_ker hB νF hνF hcentF
  obtain ⟨x, y, h, m, hm, hx, hy, hcx, hcy, hz5, hz1, hhz⟩ :=
    unitary_three_five_heisenberg_data hB
  obtain ⟨x', y', h', hx', hy', hh', hx5, hcx', hcy', hz5', hhz'⟩ :=
    exists_lifted_heisenberg hνF hcentF hC5 hx hy hcx hcy hhz
  have hz1' : ⁅y', x'⁆ ≠ 1 := by
    intro h1
    apply hz1
    rw [← hx', ← hy', ← map_commutatorElement, h1, map_one]
  have hcomm : ∀ a b : commutator G,
      (((⁅a, b⁆ : commutator G)) : G) = ⁅(a : G), (b : G)⁆ := fun a b => rfl
  refine ⟨(x' : G), (y' : G), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hx5]; rfl
  · rw [← hcomm, ← Subgroup.coe_pow, hz5']; rfl
  · rw [← hcomm]
    exact hcx'.map (commutator G).subtype
  · rw [← hcomm]
    exact hcy'.map (commutator G).subtype
  · rw [← hcomm]
    intro h1
    exact hz1' (Subtype.ext h1)

theorem exists_cover_of_proj_model {V : Type} [Group V] (K : Subgroup V) {k : Type} [Field k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (E : Subgroup (GL ι k)) (e : V ≃* StatedProj E) :
    ∃ (G : Type) (_ : Group G) (ρ : G →* GL ι k) (ν : G →* K), Function.Injective ρ ∧
      Function.Surjective ν ∧ ∀ g ∈ ν.ker, ρ g ∈ StatedScalars ι k := by
  let q : E →* StatedProj E := QuotientGroup.mk' _
  let P : Subgroup E := (K.map e.toMonoidHom).comap q
  have hPmem : ∀ g : E, g ∈ P ↔ ∃ x ∈ K, e x = q g := by
    intro g
    simp only [P, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  have hmemK : ∀ g : P, e.symm (q g) ∈ K := by
    intro g
    obtain ⟨x, hx, hxg⟩ := (hPmem g).1 g.2
    rw [← hxg, MulEquiv.symm_apply_apply]
    exact hx
  let ν : P →* K :=
    (e.symm.toMonoidHom.comp (q.comp P.subtype)).codRestrict K fun g => hmemK g
  refine ⟨P, inferInstance, E.subtype.comp P.subtype, ν,
    E.subtype_injective.comp P.subtype_injective, ?_, ?_⟩
  · intro x
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective (StatedScalars ι k |>.subgroupOf E)
      (e (x : V))
    have hg₀P : g₀ ∈ P := (hPmem g₀).2 ⟨x, x.2, hg₀.symm⟩
    refine ⟨⟨g₀, hg₀P⟩, Subtype.ext ?_⟩
    change e.symm (q g₀) = x
    rw [show q g₀ = e (x : V) from hg₀, MulEquiv.symm_apply_apply]
  · intro g hg
    have hg1 : e.symm (q g) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact this
    have hq1 : q g = 1 := by
      have := congrArg e hg1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have : (g : E) ∈ (StatedScalars ι k).subgroupOf E := (QuotientGroup.eq_one_iff _).1 hq1
    exact this

theorem psu3FiveNotInPSL2Char5_holds : PSU3FiveNotInPSL2Char5 := by
  intro V _ K f hK hmod
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := id hmod
  have hf : 1 ≤ f := hmod.1.2.1
  have hchar : CharP k 5 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_five hf hk
  obtain ⟨G, _, ρ, ν, hρ, hν, hker⟩ := exists_cover_of_proj_model K (StatedSL 2 k) e
  have : Finite G := Finite.of_injective ρ hρ
  have hcentG : ν.ker ≤ Subgroup.center G := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hgs : ρ g ∈ StatedScalars (Fin 2) k := hker g hg
    have hgc : ρ g ∈ Subgroup.center (GL (Fin 2) k) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hgs
    exact hρ (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp hgc (ρ g'))
  obtain ⟨x, y, hx5, hz5, hcx, hcy, hz1⟩ := exists_heisenberg_of_cover hK ν hν hcentG
  let ρ' : G →* Module.End k (Fin 2 → k) := (glToEndIdx (Fin 2) k).comp ρ
  have hρ' : Function.Injective ρ' := (glToEndIdx_injective (Fin 2) k).comp hρ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hnonscalar : ∀ a : k, ρ' ⁅y, x⁆ ≠ a • (1 : Module.End k (Fin 2 → k)) := by
    intro a ha
    have h5 : (ρ' ⁅y, x⁆) ^ 5 = 1 := by rw [← map_pow, hz5, map_one]
    rw [ha, smul_pow, one_pow] at h5
    have hw : (Pi.single (0 : Fin 2) (1 : k) : Fin 2 → k) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    have ha5 : a ^ 5 = 1 := by
      have h1 := congrArg (fun F : Module.End k (Fin 2 → k) => F (Pi.single (0 : Fin 2) (1 : k)))
        h5
      have h2 : a ^ 5 • (Pi.single (0 : Fin 2) (1 : k) : Fin 2 → k) =
          (1 : k) • (Pi.single (0 : Fin 2) (1 : k) : Fin 2 → k) := by simpa using h1
      exact smul_left_injective k hw h2
    have ha1 : a = 1 := by
      have h0 : (a - 1) ^ 5 = 0 := by rw [sub_pow_char a 1 (p := 5), ha5, one_pow, sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
    apply hz1
    apply hρ'
    rw [ha, ha1, one_smul, map_one]
  have hcomm := commute_of_commute_nonscalar (Module.finrank_fin_fun k) hnonscalar
    (hcy.symm.map ρ') (hcx.symm.map ρ')
  have hyx : y * x = x * y := hρ' (by simpa [map_mul] using hcomm.eq)
  exact hz1 (commutatorElement_eq_one_iff_mul_comm.2 hyx)

theorem fiveFixedExcludesClassical_of_sp4_even
    (hSp4 : OddSymplecticFourInnerDefiningFixedComponentFree)
    (hEven : EvenClassicalHighDimRankFour) : FiveFixedExcludesClassical :=
  fiveFixedExcludesClassical_of_inputs hSp4 psu3FiveNotInPSL2Char5_holds hEven

end CFSG.RankThree.PartOne.HNRed
