module

public import CFSG.RankThree.PartOne.KLR.B2Twist
public import CFSG.RankThree.PartOne.TCF.Simple

public noncomputable section

namespace CFSG.RankThree.PartOne.TCF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KLR
open Matrix

section B2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

theorem simpleOrBot_B2 [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    SimpleOrBot (B2Q L ⊓ twistedFixed D.F n') := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨ω, hω, hε1, hε2⟩ := b2_exists_eps hstab
  have hεW := wordProd_mem_parabolicWeylGroup_b2 (b2Words_letters ω hω)
  set ε := (coxeterSystem ReeTag.F4.tag).wordProd ω with hε
  set m := canonicalRep (coxeterSystem ReeTag.F4.tag) L ε with hm
  have hmQ : m ∈ B2Q L := canonicalRep_mem_subsystemGroup hεW
  have heq : ∀ g ∈ B2Q L, twistMap D.F n' g = twistMap D.F m g := fun g hg =>
    twist_eq_on_B2Q D hperm hε1 hε2 hg
  obtain ⟨S₀, hS₀, hLang⟩ := antiSp_lang_aut L a
  let mQ : B2Q L := ⟨m, hmQ⟩
  let M : antiSp L := B2eQ L mQ
  obtain ⟨h, hh⟩ := hLang M
  let Fm : B2Q L →* B2Q L := (MulAut.conj mQ).toMonoidHom.comp (B2Ftilde D)
  have hFm : ∀ x, B2eQ L (Fm x) = M * S₀ (B2eQ L x) * M⁻¹ := by
    intro x
    show B2eQ L (mQ * B2Ftilde D x * mQ⁻¹) = _
    rw [map_mul, map_mul, map_inv, B2eQ_Ftilde D hS₀]
  let P' : Subgroup (ModGL ReeTag.F4.tag L) := B2Q L ⊓ twistedFixed D.F n'
  let P'₀ : Subgroup (B2Q L) := P'.subgroupOf (B2Q L)
  have hP'₀ : ∀ x : B2Q L, x ∈ P'₀ ↔ Fm x = x := by
    intro x
    have hxad := B2Q_le_adjointGroup x.2
    show (x : ModGL ReeTag.F4.tag L) ∈ P' ↔ _
    constructor
    · rintro ⟨-, -, hfix⟩
      refine Subtype.ext ?_
      show m * Fext D.F x * m⁻¹ = x
      have : twistMap D.F n' x = x := hfix
      rw [heq x x.2] at this
      exact this
    · intro hFx
      refine ⟨x.2, hxad, ?_⟩
      have h1 : m * Fext D.F x * m⁻¹ = x := congrArg Subtype.val hFx
      show twistMap D.F n' x = x
      rw [heq x x.2]
      exact h1
  have hP'eq : P'₀.map (B2Q L).subtype = P' :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  let Y₁ : Subgroup (antiSp L) := P'₀.map (B2eQ L).toMonoidHom
  have hY₁ : ∀ A : antiSp L, A ∈ Y₁ ↔ M * S₀ A * M⁻¹ = A := by
    intro A
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hP'₀ x).1 hx
      have h2 := hFm x
      rw [h1] at h2
      exact h2.symm
    · intro hA
      refine ⟨(B2eQ L).symm A, (hP'₀ _).2 ?_, by simp⟩
      apply (B2eQ L).injective
      rw [hFm, MulEquiv.apply_symm_apply]
      exact hA
  have hY₂ : ∀ A : antiSp L, A ∈ Y₁.map (MulAut.conj h).toMonoidHom ↔ S₀ A = A := by
    intro A
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hB' := (hY₁ B).1 hB
      rw [hh] at hB'
      show S₀ (h * B * h⁻¹) = h * B * h⁻¹
      rw [map_mul, map_mul, map_inv]
      calc S₀ h * S₀ B * (S₀ h)⁻¹ = h * (h⁻¹ * S₀ h * S₀ B * (h⁻¹ * S₀ h)⁻¹) * h⁻¹ := by group
        _ = h * B * h⁻¹ := by rw [hB']
    · intro hA
      refine ⟨h⁻¹ * A * h, (hY₁ _).2 ?_, ?_⟩
      · rw [hh, map_mul, map_mul, map_inv, hA]
        group
      · show h * (h⁻¹ * A * h) * h⁻¹ = A
        group
  have hrange : Y₁.map (MulAut.conj h).toMonoidHom = (szEmbed hK (algebraMap K L)).range := by
    ext A
    rw [hY₂, fixed_S0_iff_mem_range hK hS₀]
  obtain ⟨-, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  have hns : ¬ Group.IsSolvable (suzukiGroup a K) := Group.IsPerfect.not_isSolvable _
  have h1 : SimpleOrBot (szEmbed hK (algebraMap K L)).range :=
    simpleOrBot_range hns _ (szEmbed_injective hK _)
  rw [← hrange] at h1
  have h2 : SimpleOrBot Y₁ :=
    SimpleOrBot.of_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective h1
  have h3 : SimpleOrBot P'₀ :=
    SimpleOrBot.of_map (B2eQ L).toMonoidHom (B2eQ L).injective h2
  have h4 := SimpleOrBot.map (B2Q L).subtype (B2Q L).subtype_injective h3
  rw [hP'eq] at h4
  exact h4


end B2

end CFSG.RankThree.PartOne.TCF
