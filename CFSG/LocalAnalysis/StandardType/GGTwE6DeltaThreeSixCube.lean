module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeRefl

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.TwE6DD2

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6D3

@[expose] def cartanRow (j : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  fun l => ((Tag.E6.cartan j l : ℤ) : ZMod 3)

@[expose] def succIdx (i : Fin 5) : Fin Tag.E6.rank :=
  i.succ

theorem adRefl_eq (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    adRefl Tag.E6 3 j x = x - x j • cartanRow j :=
  rfl

theorem cartanRow_self (j : Fin Tag.E6.rank) : cartanRow j j = 2 := by
  simp [cartanRow, Tag.cartan_self]

theorem adRefl_adRefl (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    adRefl Tag.E6 3 j (adRefl Tag.E6 3 j x) = x := by
  funext l
  simp only [adRefl_eq, cartanRow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Tag.cartan_self]
  push_cast
  ring

theorem adRefl_cartanRow (j : Fin Tag.E6.rank) :
    adRefl Tag.E6 3 j (cartanRow j) = -cartanRow j := by
  rw [adRefl_eq, cartanRow_self, two_smul]
  abel

theorem cartanRow_indep : ∀ a b c d e : ZMod 3, (∀ l : Fin Tag.E6.rank,
    a * cartanRow (succIdx 0) l + b * cartanRow (succIdx 1) l + c * cartanRow (succIdx 2) l +
      d * cartanRow (succIdx 3) l + e * cartanRow (succIdx 4) l = 0) →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  decide +kernel

theorem sum_cartanRow_injective :
    Function.Injective fun e : Fin 5 → ZMod 3 => ∑ i, e i • cartanRow (succIdx i) := by
  intro e e' h
  obtain ⟨h0', h1', h2', h3', h4'⟩ := cartanRow_indep (e 0 - e' 0) (e 1 - e' 1) (e 2 - e' 2)
    (e 3 - e' 3) (e 4 - e' 4) fun l => by
      have h1 := congrFun h l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_five] at h1
      linear_combination h1
  funext i
  fin_cases i
  exacts [sub_eq_zero.1 h0', sub_eq_zero.1 h1', sub_eq_zero.1 h2', sub_eq_zero.1 h3',
    sub_eq_zero.1 h4']

theorem card_closure_cartanRow :
    3 ^ 5 ≤ Nat.card (Subgroup.closure (Set.range fun i : Fin 5 =>
      Multiplicative.ofAdd (cartanRow (succIdx i)))) := by
  have hmem : ∀ e : Fin 5 → ZMod 3, Multiplicative.ofAdd (∑ i, e i • cartanRow (succIdx i)) ∈
      Subgroup.closure (Set.range fun i : Fin 5 =>
        Multiplicative.ofAdd (cartanRow (succIdx i))) := by
    intro e
    rw [ofAdd_sum]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [← ZMod.natCast_zmod_val (e i), Nat.cast_smul_eq_nsmul (ZMod 3), ofAdd_nsmul]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  calc 3 ^ 5 = Nat.card (Fin 5 → ZMod 3) := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    _ ≤ _ := Nat.card_le_card_of_injective (fun e => ⟨_, hmem e⟩)
        fun e e' h => sum_cartanRow_injective
          (Multiplicative.ofAdd.injective (congrArg Subtype.val h))

section Refl


theorem reflData_langCube {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    ReflData (langCube hn hK σ hσ Fr hFr g) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  set Φ := rgrpConjAut hn hK σ hσ Fr hFr with hΦ
  have hb : ∀ x : Fin Tag.E6.rank → ZMod 3, ∀ i, zetaVec ζ hζ x i ^ 3 = 1 := fun x i => by
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hdR : ∀ x : Fin Tag.E6.rank → ZMod 3,
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := fun x =>
    conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn ⟨_, rootDiagUnit_mem_cubeTorus (hb x), rfl⟩
  let θ : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ↥(TwistedDiag.Rgrp Ω Fr) :=
    MonoidHom.mk' (fun x => ⟨_, hdR (Multiplicative.toAdd x)⟩) fun x y => Subtype.ext (by
      change g * rootDiagUnit Tag.E6 (zetaVec ζ hζ
          (Multiplicative.toAdd x + Multiplicative.toAdd y)) * g⁻¹ =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹ *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹)
      rw [ExcFrames.zetaVec_add, rootDiagUnit_mul]
      group)
  have hθinj : Function.Injective θ := fun x y hxy =>
    Multiplicative.toAdd.injective (zetaVec_injective hζo hζ
      (rootDiagUnit_injective (τ := Tag.E6) (K := Ω)
        (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hxy)))))
  have hmemY : ∀ y ∈ langCube hn hK σ hσ Fr hFr g, ∃ x, Φ (θ (Multiplicative.ofAdd x)) = y := by
    intro y hy
    obtain ⟨b, hb3, hx, rfl⟩ := (mem_langCube hn hK σ hσ Fr hFr).1 hy
    have hb3' : b ^ 3 = 1 := by funext i; exact hb3 i
    obtain ⟨x, rfl⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3'
    exact ⟨x, rfl⟩
  have hθY : ∀ x, Φ (θ x) ∈ langCube hn hK σ hσ Fr hFr g := fun x =>
    (mem_langCube hn hK σ hσ Fr hFr).2 ⟨_, hb _, hdR _, rfl⟩
  have hlift : ∀ j : Fin Tag.E6.rank, ∃ m : ↥(TwistedDiag.Rgrp Ω Fr), ∀ x,
      m * θ (Multiplicative.ofAdd x) * m⁻¹ = θ (Multiplicative.ofAdd (adRefl Tag.E6 3 j x)) := by
    intro j
    obtain ⟨m, ⟨hmM, hmθ⟩, hmw⟩ := TwistedDiag.exists_lift Fr hFr (simple Tag.E6 j)
    refine ⟨⟨g * m * g⁻¹, (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn m).1 hmθ⟩,
      fun x => Subtype.ext ?_⟩
    change g * m * g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) * (g * m * g⁻¹)⁻¹ =
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl Tag.E6 3 j x)) * g⁻¹
    rw [← adAct_simple, ← weylTuple_zetaVec, ← monomial_conj_rootDiagUnit_weylTuple hmM hmw]
    group
  choose M hM using hlift
  have hM3 : ∀ j x, M j ^ 3 * θ (Multiplicative.ofAdd x) * (M j ^ 3)⁻¹ =
      θ (Multiplicative.ofAdd (adRefl Tag.E6 3 j x)) := by
    intro j x
    calc M j ^ 3 * θ (Multiplicative.ofAdd x) * (M j ^ 3)⁻¹
        = M j * (M j * (M j * θ (Multiplicative.ofAdd x) * (M j)⁻¹) * (M j)⁻¹) * (M j)⁻¹ := by
          simp only [pow_three, mul_inv_rev, mul_assoc]
      _ = _ := by rw [hM, hM, hM, adRefl_adRefl]
  obtain ⟨-, -, hCn, hCi, -⟩ := TwistedDiag.cgrp_facts (ℓ := 2) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have hinnR : ∀ y : ↥(TwistedDiag.Rgrp Ω Fr),
      (y : ModGL Tag.E6 Ω) ∈ TwistedDiag.Cgrp K σ.toRingHom Ω →
      Φ y ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := fun y hy =>
    rgrpConjAut_mem_range_conj hn hK σ hσ Fr hFr y.2 hy
  have hinn : ∀ j, Φ (M j ^ 3) ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
    intro j
    haveI := hCn
    have h1 := Subgroup.pow_index_mem
      ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)) (M j)
    have hidx : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
        (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCi
    rw [hidx] at h1
    exact hinnR _ (Subgroup.mem_subgroupOf.1 h1)
  refine ⟨fun i => Φ (M (succIdx i) ^ 3),
    fun i => Φ (θ (Multiplicative.ofAdd (cartanRow (succIdx i)))), fun i => hinn _,
    fun i => hθY _, fun i y hy => ?_, fun i => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hmemY y hy
    refine ⟨(-x (succIdx i)).val, ?_⟩
    have h1 : adRefl Tag.E6 3 (succIdx i) x =
        (-x (succIdx i)).val • cartanRow (succIdx i) + x := by
      rw [adRefl_eq, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
      funext l
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    dsimp only
    rw [← map_inv Φ (M (succIdx i) ^ 3), ← map_mul Φ, ← map_mul Φ, hM3, h1, ofAdd_add,
      ofAdd_nsmul, map_mul, map_pow, map_mul, map_pow]
  · dsimp only
    rw [← map_inv Φ (M (succIdx i) ^ 3), ← map_mul Φ, ← map_mul Φ, hM3, adRefl_cartanRow,
      ofAdd_neg, map_inv θ, map_inv Φ]
  · have hTinj : Function.Injective (Φ.comp θ) :=
      (rgrpConjAut_injective hn hK σ hσ Fr hFr).comp hθinj
    have hr : Set.range (fun i : Fin 5 => Φ (θ (Multiplicative.ofAdd (cartanRow (succIdx i))))) =
        (Φ.comp θ) '' Set.range fun i : Fin 5 => Multiplicative.ofAdd (cartanRow (succIdx i)) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, Subgroup.card_map_of_injective hTinj]
    exact card_closure_cartanRow

end Refl

end CFSG.StandardType.TwE6DD2
