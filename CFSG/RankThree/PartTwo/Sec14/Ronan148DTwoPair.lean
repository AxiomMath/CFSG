module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_theta {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hNs : Group.IsSolvable ↥N) (hN3 : ¬ 3 ∣ Nat.card N) :
    N.subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := by
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  let ι : ↥(N.subgroupOf X) →* ↥N :=
    { toFun := fun x => ⟨((x : ↥X) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy => by
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  refine hmax _ ⟨fun n hn g => ?_⟩ ?_ ?_
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hXN g.2) n).mp hn
    simpa using this
  · haveI := hNs
    exact Group.isSolvable_of_isSolvable_injective hι
  · exact fun h3 => hN3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))

theorem isCentralProductA6Covers_sup {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ thetaComponentsAt 3 a) (hK₂ : K₂ ∈ thetaComponentsAt 3 a)
    (hne : K₁ ≠ K₂) (haK₁ : a ∈ K₁) (haK₂ : a ∈ K₂)
    (h₁ : Sec4.IsTripleCover (↥K₁ ⧸ aschbacherSolvableCore 3 ↥K₁) (alternatingGroup (Fin 6)))
    (h₂ : Sec4.IsTripleCover (↥K₂ ⧸ aschbacherSolvableCore 3 ↥K₂) (alternatingGroup (Fin 6))) :
    IsCentralProductA6Covers (↥(K₁ ⊔ K₂) ⧸ aschbacherSolvableCore 3 ↥(K₁ ⊔ K₂)) := by
  set X := K₁ ⊔ K₂ with hXdef
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  set θX := aschbacherSolvableCore 3 ↥X with hθX
  set π := QuotientGroup.mk' θX with hπ
  have hK₁C : K₁ ≤ C := le_centralizer_of_mem_thetaComponentsAt hK₁
  have hK₂C : K₂ ≤ C := le_centralizer_of_mem_thetaComponentsAt hK₂
  have hXC : X ≤ C := sup_le hK₁C hK₂C
  have hK₁X : K₁ ≤ X := le_sup_left
  have hK₂X : K₂ ≤ X := le_sup_right
  obtain ⟨hTs, hT3⟩ := Sec6.theta_solvable_and_not_dvd C
  have hTX : ∀ x : ↥X, (x : G) ∈ T → x ∈ θX := fun x hx =>
    subgroupOf_le_theta (hXC.trans (Sec6.le_normalizer_theta C)) hTs hT3
      (show x ∈ T.subgroupOf X from hx)
  obtain ⟨hθXs, hθXc, hθX3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hθXn : θX.Normal := Subgroup.normal_of_characteristic θX
  have key : ∀ {K : Subgroup G}, K ∈ thetaComponentsAt 3 a → ∀ hKX : K ≤ X,
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) →
      Sec4.IsTripleCover ↥((K.subgroupOf X).map π) (alternatingGroup (Fin 6)) := by
    intro K hK hKX htc
    set ψ : ↥K →* ↥X ⧸ θX := π.comp (Subgroup.inclusion hKX) with hψ
    have hker : ψ.ker = aschbacherSolvableCore 3 ↥K := by
      ext k
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · intro hk
        obtain ⟨-, -, -, hmaxK, -⟩ :=
          solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
        have hN : (θX.comap (Subgroup.inclusion hKX)).Normal := hθXn.comap _
        have hNs : Group.IsSolvable ↥(θX.comap (Subgroup.inclusion hKX)) := by
          haveI := hθXs
          let ι : ↥(θX.comap (Subgroup.inclusion hKX)) →* ↥θX :=
            { toFun := fun x => ⟨Subgroup.inclusion hKX x, x.2⟩
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          refine Group.isSolvable_of_isSolvable_injective (f := ι) fun x y hxy => ?_
          have h1 := congrArg (fun z => ((z : ↥X) : G)) (congrArg Subtype.val hxy)
          exact Subtype.ext (Subtype.ext h1)
        have hN3 : ¬ 3 ∣ Nat.card ↥(θX.comap (Subgroup.inclusion hKX)) := by
          let ι : ↥(θX.comap (Subgroup.inclusion hKX)) →* ↥θX :=
            { toFun := fun x => ⟨Subgroup.inclusion hKX x, x.2⟩
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          have hι : Function.Injective ι := fun x y hxy => by
            have h1 := congrArg (fun z => ((z : ↥X) : G)) (congrArg Subtype.val hxy)
            exact Subtype.ext (Subtype.ext h1)
          exact fun h3 => hθX3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
        exact hmaxK _ hN hNs hN3 hk
      · intro hk
        have hkT : (k : G) ∈ T := by
          have h1 : (k : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨k, hk, rfl⟩
          rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
          exact h1.2
        exact hTX _ hkT
    have hrange : ψ.range = (K.subgroupOf X).map π := by
      rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    have e1 : ↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* ↥((K.subgroupOf X).map π) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))
    exact KFacts.KS14.isTripleCover_congr e1 htc
  set U := (K₁.subgroupOf X).map π with hU
  set V := (K₂.subgroupOf X).map π with hV
  have hUt := key hK₁ hK₁X h₁
  have hVt := key hK₂ hK₂X h₂
  have hUV : ⁅U, V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨k₁, hk₁, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k₂, hk₂, rfl⟩
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    apply hTX
    have hc : ⁅(k₂ : G), (k₁ : G)⁆ ∈ T :=
      Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK₂ hK₁ (Ne.symm hne)
        (Subgroup.commutator_mem_commutator hk₂ hk₁)
    have e : ((k₂ * k₁ * (k₁ * k₂)⁻¹ : ↥X) : G) = ⁅(k₂ : G), (k₁ : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hc
  have hsup : U ⊔ V = ⊤ := by
    rw [hU, hV, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hK₁X hK₂X, Subgroup.subgroupOf_self,
      ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  have hUcV : U ≤ Subgroup.centralizer (V : Set (↥X ⧸ θX)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUV
  have hVcU : V ≤ Subgroup.centralizer (U : Set (↥X ⧸ θX)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hUV
  have hUn : U.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer (hVcU.trans (Subgroup.centralizer_le_normalizer _))
  have hVn : V.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (hUcV.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  set aX : ↥X := ⟨a, hK₁X haK₁⟩ with haX
  have haU : π aX ∈ U := ⟨aX, show (aX : G) ∈ K₁ from haK₁, rfl⟩
  have haV : π aX ∈ V := ⟨aX, show (aX : G) ∈ K₂ from haK₂, rfl⟩
  have haπ1 : π aX ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h1' : aX = 1 := by
      have h3 : aX ^ 3 = 1 := Subtype.ext (by simpa [haX] using ha3)
      obtain ⟨-, -, hθ3, -⟩ :=
        solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
      exact eq_one_of_mem_of_pow_three_pow hθ3 h1 (k := 1) (by rw [pow_one]; exact h3)
    exact ha1 (congrArg Subtype.val h1')
  have haπ3 : (π aX) ^ 3 = 1 := by
    rw [← map_pow]
    have : aX ^ 3 = 1 := Subtype.ext (by simpa [haX] using ha3)
    rw [this, map_one]
  have hcard : Nat.card ↥(U ⊓ V) = 3 := by
    apply le_antisymm
    ·
      let ι : ↥(U ⊓ V) → ↥(Subgroup.center ↥U) := fun x =>
        ⟨⟨x, x.2.1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext
          (Subgroup.mem_centralizer_iff.mp (hVcU x.2.2) y y.2)⟩
      have hι : Function.Injective ι := fun x y hxy => by
        have h := congrArg Subtype.val (congrArg Subtype.val hxy)
        exact Subtype.ext h
      calc Nat.card ↥(U ⊓ V) ≤ Nat.card ↥(Subgroup.center ↥U) :=
            Nat.card_le_card_of_injective ι hι
        _ = 3 := hUt.1
    · have hle : Subgroup.zpowers (π aX) ≤ U ⊓ V := Subgroup.zpowers_le.mpr ⟨haU, haV⟩
      calc 3 = Nat.card (Subgroup.zpowers (π aX)) := by
            rw [Nat.card_zpowers, orderOf_eq_prime haπ3 haπ1]
        _ ≤ Nat.card ↥(U ⊓ V) := Subgroup.card_le_of_le hle
  exact ⟨U, V, hUn, hVn, hsup, hUV, hcard, hUt, hVt⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
