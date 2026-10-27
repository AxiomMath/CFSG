module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeCoroot

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three

section Torus


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

theorem exists_cubeHom (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    ∃ Ψ : Multiplicative (Fin Tag.E6.rank → ZMod 3) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      Function.Injective Ψ ∧ (∀ y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g, ∃ x, Ψ x = y) ∧
      ∀ x, ∃ hx : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹ ∈
        TwistedDiag.Rgrp Ω Fr, Ψ x = rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Φ := rgrpConjAut hn hK σ hσ Fr hFr with hΦ
  have hb : ∀ x : Fin Tag.E6.rank → ZMod 3, ∀ i, zetaVec ζ hζ x i ^ 3 = 1 := fun x i => by
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hdR : ∀ x : Fin Tag.E6.rank → ZMod 3,
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := fun x =>
    TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn
      ⟨_, TwE6DD2.rootDiagUnit_mem_cubeTorus (hb x), rfl⟩
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
  refine ⟨Φ.comp θ, (rgrpConjAut_injective hn hK σ hσ Fr hFr).comp hθinj, ?_,
    fun x => ⟨hdR _, rfl⟩⟩
  intro y hy
  obtain ⟨b, hb3, hx, rfl⟩ := (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).1 hy
  have hb3' : b ^ 3 = 1 := by funext i; exact hb3 i
  obtain ⟨x, rfl⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3'
  exact ⟨Multiplicative.ofAdd x, rfl⟩

theorem exists_coroot_mem_of_le (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hS : S ≤ TwE6DD2.langCube hn hK σ hσ Fr hFr g) (h5 : 3 ^ 5 ≤ Nat.card S) :
    ∃ (γ : Fin TwistTag.E6.tag.rank → ℤ) (ζ : Ωˣ), IsRoot TwistTag.E6.tag γ ∧ ζ ^ 3 = 1 ∧
      ζ ≠ 1 ∧ ∃ hd : g * rootDiagUnit Tag.E6 (TwE6RootAs.corootTuple γ ζ) * g⁻¹ ∈
        TwistedDiag.Rgrp Ω Fr, rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  obtain ⟨Ψ, hΨinj, hΨrange, hΨ⟩ := exists_cubeHom hn hK σ hσ Fr hFr h3 hg hgn hζ hζo
  let S0 : AddSubgroup (Fin Tag.E6.rank → ZMod 3) :=
    { carrier := {x | Ψ (Multiplicative.ofAdd x) ∈ S}
      zero_mem' := by
        rw [Set.mem_setOf_eq, ofAdd_zero, map_one]
        exact one_mem S
      add_mem' := fun {x y} hx hy => by
        rw [Set.mem_setOf_eq, ofAdd_add, map_mul]
        exact mul_mem hx hy
      neg_mem' := fun {x} hx => by
        rw [Set.mem_setOf_eq, ofAdd_neg, map_inv]
        exact inv_mem hx }
  have hcard : Nat.card S0 = Nat.card S :=
    Nat.card_congr (Equiv.ofBijective (fun x : S0 => (⟨Ψ (Multiplicative.ofAdd x.1), x.2⟩ : S))
      ⟨fun x y hxy => Subtype.ext (Multiplicative.ofAdd.injective
          (hΨinj (congrArg Subtype.val hxy))),
        fun s => by
          obtain ⟨x, hx⟩ := hΨrange s.1 (hS s.2)
          exact ⟨⟨Multiplicative.toAdd x, by
            change Ψ (Multiplicative.ofAdd (Multiplicative.toAdd x)) ∈ S
            rw [ofAdd_toAdd, hx]
            exact s.2⟩, Subtype.ext (by
              change Ψ (Multiplicative.ofAdd (Multiplicative.toAdd x)) = s.1
              rw [ofAdd_toAdd, hx])⟩⟩)
  have h5' : 3 ^ 5 ≤ Nat.card (AddSubgroup.toZModSubmodule 3 S0) := by
    rw [← hcard] at h5
    exact h5
  obtain ⟨γ, hγ, hγS⟩ := exists_root_corootVec_mem (AddSubgroup.toZModSubmodule 3 S0) h5'
  refine ⟨γ, ζ, hγ, hζ, fun h => by rw [h, orderOf_one] at hζo; omega, ?_⟩
  have e : TwE6RootAs.corootTuple γ ζ = zetaVec ζ hζ (corootVec γ) :=
    corootTuple_eq_zetaVec ζ hζ γ
  obtain ⟨hx, hΨx⟩ := hΨ (Multiplicative.ofAdd (corootVec γ))
  have hd : g * rootDiagUnit Tag.E6 (TwE6RootAs.corootTuple γ ζ) * g⁻¹ ∈
      TwistedDiag.Rgrp Ω Fr := by
    rw [e]
    exact hx
  refine ⟨hd, ?_⟩
  have h1 : (⟨_, hd⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) = ⟨_, hx⟩ :=
    Subtype.ext (congrArg (fun b => g * rootDiagUnit Tag.E6 b * g⁻¹) e)
  rw [h1, ← hΨx]
  exact hγS

end Torus

end CFSG.StandardType.TwE6EndNode3

end
