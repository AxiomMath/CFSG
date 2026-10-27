module

public import CFSG.RankThree.PartOne.KLR.Embedding
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.FrobTrick

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Basic

variable {τ : Tag} {L : Type} [Field L]

theorem rootSpan_rootCharKernel_le_centralizer (b : Fin τ.rank → Lˣ) :
    rootSpan τ L (rootCharKernel b) ≤
      Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)) := by
  refine iSup₂_le fun α hα => ?_
  show rootSubgroup τ L α ≤ _
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX b hα.1 c
  rw [hα.2, Units.val_one, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

end Basic

variable {L : Type} [Field L]

section MasterThm

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

@[expose] def StarRadFree (n : ModGL ReeTag.F4.tag L) (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) :
    Prop :=
  NoSolvableRadical (rootSpan ReeTag.F4.tag L S ⊓ twistedFixed D.F n)

theorem odd_card_of_solvable_normal_centralizer
    {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      StarRadFree D n (rootCharKernel b))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p)
    (V : Subgroup (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) [V.Normal]
    [Group.IsSolvable V] : Odd (Nat.card V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcH⟩ := hconj x hx
  let Dg : Subgroup (ReeTag.F4.reeGamma K a) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))
  let ψ : Dg →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp
      ((MulAut.conj c).toMonoidHom.comp Dg.subtype)
  have hψ : ∀ d : Dg, ψ d = g₀⁻¹ * thetaGamma L a (c * (d : ReeTag.F4.reeGamma K a) * c⁻¹) * g₀ :=
    fun d => by simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h
    rw [hψ, hψ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
    exact Subtype.ext h2
  have hψmem : ∀ d : Dg, ψ d ∈ adjointGroup ReeTag.F4.tag L := fun d => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀) (thetaGamma_mem_adjointGroup L _)) hg₀
  have hψtw : ∀ d : Dg, ψ d ∈ twistedFixed D.F n := fun d => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L _) (D.fext_theta _)
  have hxD : x ∈ Dg := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xD : Dg := ⟨x, hxD⟩ with hxDdef
  have hy : ψ xD = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := hψ xD
  have hyH : ψ xD ∈ torusGroup ReeTag.F4.tag L := by rw [hy]; exact hcH
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hordy : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [← hb, orderOf_injective ψ hψinj xD, ← Subgroup.orderOf_coe]
    exact hx
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hordy
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hordy
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hcommh : ∀ d : Dg, ψ d * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * ψ d :=
    fun d => by
      rw [← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 d.2)
  have hHQ : ∀ d : Dg, ψ d ∈ (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) *
      (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) := fun d =>
    mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn (fun _ h => h) (hψmem d) (hcommh d)
  have hL2 : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : PerfectRing L 2 := PerfectField.toPerfectRing 2
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃+* L, ∀ c, σ c = c ^ 2 :=
    ⟨frobeniusEquiv L 2, fun c => by simp [frobeniusEquiv_apply, frobenius_def]⟩
  have hinv : ∀ d : Dg, d ^ 2 = 1 →
      ψ d ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n := fun d hd => by
    refine ⟨?_, hψtw d⟩
    have h1 : ψ d * ψ d = 1 := by rw [← map_mul, ← sq, hd, map_one]
    exact mem_rootSpan_of_mul_self_eq_one σ hσ hS (hHQ d) h1
  have hPψ : rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n ≤ ψ.range := by
    rintro u ⟨huQ, huT⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀ hFg₀ huT
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    have hθc : thetaGamma L a (c * x * c⁻¹) = g₀ * ψ xD * g₀⁻¹ := by
      rw [hy]; group
    have huy : u * ψ xD = ψ xD * u := by
      rw [hb]
      exact Subgroup.mem_centralizer_singleton_iff.1
        (rootSpan_rootCharKernel_le_centralizer b huQ)
    have hcomm : γ * (c * x * c⁻¹) = (c * x * c⁻¹) * γ := by
      apply thetaGamma_injective L
      rw [map_mul (thetaGamma L a) γ (c * x * c⁻¹), map_mul (thetaGamma L a) (c * x * c⁻¹) γ, hγ,
        hθc]
      calc g₀ * u * g₀⁻¹ * (g₀ * ψ xD * g₀⁻¹) = g₀ * (u * ψ xD) * g₀⁻¹ := by group
        _ = g₀ * (ψ xD * u) * g₀⁻¹ := by rw [huy]
        _ = g₀ * ψ xD * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
    have hd : c⁻¹ * γ * c ∈ Dg := by
      show _ ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * γ * c) * x = c⁻¹ * (γ * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * γ) * c := by rw [hcomm]
        _ = x * (c⁻¹ * γ * c) := by group
    refine ⟨⟨c⁻¹ * γ * c, hd⟩, ?_⟩
    rw [hψ]
    change g₀⁻¹ * thetaGamma L a (c * (c⁻¹ * γ * c) * c⁻¹) * g₀ = u
    rw [show c * (c⁻¹ * γ * c) * c⁻¹ = γ by group, hγ]
    group
  have hrad' := hrad b hordy (by rw [← hb]; exact hψtw xD)
  exact odd_card_of_solvable_normal_of_involutions ψ hψinj _ hPψ hrad' hinv V

end MasterThm

end CFSG.RankThree.PartOne.KLR
