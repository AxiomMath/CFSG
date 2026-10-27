module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveF2Model
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

local instance noOffE8FiveFactFiveAF : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

section AutFrame

theorem mulAut_mul_conj_mul_inv {C : Type*} [Group C] (g : MulAut C) (a₀ : C) :
    g * MulAut.conj a₀ * g⁻¹ = MulAut.conj (g a₀) := by
  ext h
  simp [MulAut.conj_apply]


theorem exists_conj_eq_on_E8_five {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    {A : Subgroup (adjointGroup Tag.E8 K)} (hA : IsElemAbelian 5 A)
    (hA4 : 5 ^ 4 ≤ Nat.card A) (g : MulAut (adjointGroup Tag.E8 K)) :
    ∃ d : adjointGroup Tag.E8 K, ∀ a ∈ A, g a = d * a * d⁻¹ := by
  classical
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ι, hιinj, hισ, -⟩ := exists_f2Model_E8 (K := K)
  have hXel : IsElemAbelian 5 ι.range := isElemAbelian_range_of_module (p := 5) ι
  have hXcard : Nat.card ι.range = 5 ^ 4 := by
    rw [← NoOffRest.card_eigE8 (p := 5) (by norm_num) NoOffRest.three_mul_three_zmod_five]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  obtain ⟨c, hc⟩ := exists_conj_map_eq_E8_five h5 hXel hA hXcard.ge hA4
  obtain ⟨⟨x, σ⟩, hx, -⟩ :=
    ((even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK Tag.E8 (Or.inr rfl)).1 g)
  have hgy : ∀ y ∈ ι.range, g y = x * y * x⁻¹ := by
    rintro _ ⟨v, rfl⟩
    apply Subtype.ext
    rw [hx, hισ σ v]
    rfl
  refine ⟨g c * x * c⁻¹, ?_⟩
  intro a ha
  rw [← hc] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  change g (c * y * c⁻¹) =
    (g c * x * c⁻¹) * (c * y * c⁻¹) * (g c * x * c⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv, hgy y hy]
  group

theorem exists_autFrame_E8 {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    {M' S : Subgroup (MulAut (adjointGroup Tag.E8 K))}
    (hSI : S ≤ (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)).range)
    (hSel : IsElemAbelian 5 S) (hS4 : 5 ^ 4 ≤ Nat.card S) :
    GGBstarModelFrame (NoOffRest.eigPerm 5 3) 5 M' S := by
  classical
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  have hZ : Subgroup.center (adjointGroup Tag.E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hγinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center (adjointGroup Tag.E8 K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 : (MulAut.conj g) h = h := by rw [hg]; rfl
      rw [MulAut.conj_apply] at h1
      calc h * g = g * h * g⁻¹ * g := by rw [h1]
        _ = g * h := by group
    rw [hZ] at hgc
    exact Subgroup.mem_bot.1 hgc
  set γ : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K) := MulAut.conj with hγ
  set A : Subgroup (adjointGroup Tag.E8 K) := S.comap γ with hA
  have hAel : IsElemAbelian 5 A := ExcFrames.isElemAbelian_comap_frame γ hγinj hSel
  have hAcard : Nat.card A = Nat.card S := ExcFrames.card_comap_of_le_range γ hγinj hSI
  have hSA : A.map γ = S := Subgroup.map_comap_eq_self hSI
  obtain ⟨ι, hιinj, -, hιaut⟩ := exists_f2Model_E8 (K := K)
  have hXel : IsElemAbelian 5 ι.range := isElemAbelian_range_of_module (p := 5) ι
  have hXcard : Nat.card ι.range = 5 ^ 4 := by
    rw [← NoOffRest.card_eigE8 (p := 5) (by norm_num) NoOffRest.three_mul_three_zmod_five]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  obtain ⟨c, hc⟩ := exists_conj_map_eq_E8_five h5 hXel hAel hXcard.ge (hAcard ▸ hS4)
  let ιS : Multiplicative (NoOffRest.eigE8 5 3) →* MulAut (adjointGroup Tag.E8 K) :=
    γ.comp ((MulAut.conj c).toMonoidHom.comp ι)
  have hιSinj : Function.Injective ιS := hγinj.comp ((MulAut.conj c).injective.comp hιinj)
  have hιSrange : ιS.range = S := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hc, hSA]
  refine ⟨ιS, hιSinj, hιSrange, ?_⟩
  intro g _ hgN _
  obtain ⟨d, hd⟩ := exists_conj_eq_on_E8_five hf hK h5 hAel (hAcard ▸ hS4) g
  have hgA : ∀ a₀ ∈ A, g a₀ ∈ A := by
    intro a₀ ha₀
    have h2 := (Subgroup.mem_normalizer_iff.mp hgN (γ a₀)).mp ha₀
    rw [mulAut_mul_conj_mul_inv] at h2
    exact h2
  set a : adjointGroup Tag.E8 K := c⁻¹ * d * c with ha
  have hcomp : ∀ y ∈ ι.range, g (c * y * c⁻¹) = c * (a * y * a⁻¹) * c⁻¹ := by
    intro y hy
    have hcy : c * y * c⁻¹ ∈ A := by
      rw [← hc]
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [hd _ hcy, ha]
    group
  have hnorm : ∀ s : NoOffRest.eigE8 5 3, ∃ t : NoOffRest.eigE8 5 3,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t) := by
    intro s
    have hyX : ι (Multiplicative.ofAdd s) ∈ ι.range := ⟨_, rfl⟩
    have hcyA : c * ι (Multiplicative.ofAdd s) * c⁻¹ ∈ A := by
      rw [← hc]
      exact ⟨_, hyX, by simp [MulAut.conj_apply]⟩
    have hgc := hgA _ hcyA
    rw [hcomp _ hyX, ← hc] at hgc
    obtain ⟨y', ⟨v, hv⟩, hy'⟩ := hgc
    refine ⟨Multiplicative.toAdd v, ?_⟩
    have hy'' : c * y' * c⁻¹ = c * (a * ι (Multiplicative.ofAdd s) * a⁻¹) * c⁻¹ := hy'
    have := mul_left_cancel (mul_right_cancel hy'')
    rw [← this, ← hv]
    rfl
  obtain ⟨u, hu⟩ := hιaut a hnorm
  refine ⟨u, fun s => ?_⟩
  have hyX : ι (Multiplicative.ofAdd s) ∈ ι.range := ⟨_, rfl⟩
  change g * γ (c * ι (Multiplicative.ofAdd s) * c⁻¹) * g⁻¹ =
    γ (c * ι (Multiplicative.ofAdd (NoOffRest.eigPerm 5 3 u s)) * c⁻¹)
  rw [hγ, mulAut_mul_conj_mul_inv, hcomp _ hyX, hu s]

end AutFrame

end NoOffE8Five

end CFSG.StandardType
