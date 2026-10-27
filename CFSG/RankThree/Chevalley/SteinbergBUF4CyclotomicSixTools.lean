module

public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourSetup
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace SteinbergBN
open scoped commutatorElement Pointwise

theorem adjointGroup_inf_centralizer_rootDiagUnit_eq_parabolic {M : Type} [Field M] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {c : Fin Tag.F4.rank → Mˣ} (hcp : c ^ p = 1) (hc1 : c ≠ 1)
    {J : Set (Fin Tag.F4.rank)} (hker : rootCharKernel c = parabolicRoots .F4 J) :
    adjointGroup .F4 M ⊓ Subgroup.centralizer {rootDiagUnit .F4 c} =
      torusGroup .F4 M ⊔ subsystemGroup .F4 M J := by
  have h1 := toralCentralizer_eq_toralRootGroup_of_le
    (EvenF4QPlus.F4_rootCharStabilizer_le_kernelReflectionGroup hp hp3 hcp hc1)
  rw [toralCentralizer, toralRootGroup, hker, ← subsystemGroup_eq_rootSpan] at h1
  exact h1

theorem exists_rootDiagUnit_of_conj_parabolic {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)
    {p : ℕ} (hp : p.Prime) {x₀ : ModGL Tag.F4 L} (hx₀ : x₀ ∈ torusGroup Tag.F4 L)
    (hxp : orderOf (baseChangeGL ι x₀) = p) (u : WeylGroup Tag.F4) {J : Set (Fin Tag.F4.rank)}
    (hu : (fun α => u • α) '' {α | IsRoot Tag.F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots Tag.F4 J) :
    ∃ c : Fin Tag.F4.rank → Lˣ,
      canonicalRep (coxeterSystem Tag.F4) L u * x₀ * (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ =
        rootDiagUnit Tag.F4 c ∧ c ^ p = 1 ∧ c ≠ 1 ∧ rootCharKernel c = parabolicRoots Tag.F4 J := by
  set y₀ := canonicalRep (coxeterSystem Tag.F4) L u * x₀ *
    (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ with hy₀
  have hy₀H : y₀ ∈ torusGroup Tag.F4 L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer u) x₀).1 hx₀
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hord : orderOf y₀ = p := by
    rw [hy₀, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj _).injective x₀,
      ← orderOf_injective _ hinj x₀, hxp]
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy₀H
  have hcp : c ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hc, ← hord, pow_orderOf_eq_one, rootDiagUnit_one])
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, rootDiagUnit_one] at hc
    rw [hc, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hker₀ : {β | IsRoot Tag.F4 β ∧ torusRootChar y₀ β = 1} = parabolicRoots Tag.F4 J := by
    rw [← hu]
    have e := EvenF4QPlus.survivingRoots_canonicalRep_conj (L := L) hx₀ u
    rw [← hy₀] at e
    rw [e]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq, torusRootChar_baseChangeGL, map_eq_one_iff _ ι.injective]
  refine ⟨c, hc, hcp, hc1, ?_⟩
  rw [← hker₀]
  ext β
  constructor
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, EvenF4QPlus.torusRootChar_rootDiagUnit c hβ, h1, Units.val_one]
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, EvenF4QPlus.torusRootChar_rootDiagUnit c hβ] at h1
    exact Units.val_eq_one.1 h1

theorem smul_eq_neg_smul_of_weylAct_eq_neg {J : Set (Fin Tag.F4.rank)} {v w' : WeylGroup Tag.F4}
    (h : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots Tag.F4 J),
      weylAct Tag.F4 v z = -weylAct Tag.F4 w' z)
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ parabolicRoots Tag.F4 J) : v • α = -(w' • α) := by
  have e := h _ (Submodule.subset_span (Set.mem_image_of_mem ofLattice hα))
  rw [weylAct_ofLattice, weylAct_ofLattice, ← ofLatticeHom_apply, ← ofLatticeHom_apply,
    ← map_neg, ofLatticeHom_apply, ofLatticeHom_apply] at e
  exact ofLattice_injective e

theorem canonicalRep_conj_eq_of_smul_single {M : Type} [Field M] [CharP M 2]
    {J : Set (Fin Tag.F4.rank)} {v v' : WeylGroup Tag.F4}
    (h : ∀ k ∈ J, v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) = v' • Pi.single k 1)
    {z : ModGL Tag.F4 M} (hz : z ∈ subsystemGroup Tag.F4 M J) :
    canonicalRep (coxeterSystem Tag.F4) M v * z * (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ =
      canonicalRep (coxeterSystem Tag.F4) M v' * z *
        (canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ := by
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  have hgen : ∀ {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α), v • α = v' • α → ∀ c : M,
      pinnedX Tag.F4 M α c * ((canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ *
        canonicalRep (coxeterSystem Tag.F4) M v) =
      (canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ * canonicalRep (coxeterSystem Tag.F4) M v *
        pinnedX Tag.F4 M α c := by
    intro α hα hvα c
    have e1 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 v hα c
    have e2 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 v' hα c
    rw [hvα, ← e2] at e1
    calc pinnedX Tag.F4 M α c * ((canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ *
          canonicalRep (coxeterSystem Tag.F4) M v) =
        (canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ * (canonicalRep (coxeterSystem Tag.F4) M v' *
          pinnedX Tag.F4 M α c * (canonicalRep (coxeterSystem Tag.F4) M v')⁻¹) *
            canonicalRep (coxeterSystem Tag.F4) M v := by group
      _ = (canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ * (canonicalRep (coxeterSystem Tag.F4) M v *
          pinnedX Tag.F4 M α c * (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹) *
            canonicalRep (coxeterSystem Tag.F4) M v := by rw [e1]
      _ = _ := by group
  have hle : subsystemGroup Tag.F4 M J ≤ Subgroup.centralizer
      {(canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ * canonicalRep (coxeterSystem Tag.F4) M v} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
      exact hgen (isRoot_single _ k) (h k hk) c
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
      exact hgen (isRoot_neg_single _ k) (by rw [smul_neg, smul_neg, h k hk]) c
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
  calc canonicalRep (coxeterSystem Tag.F4) M v * z * (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ =
      canonicalRep (coxeterSystem Tag.F4) M v' *
        (z * ((canonicalRep (coxeterSystem Tag.F4) M v')⁻¹ *
          canonicalRep (coxeterSystem Tag.F4) M v)) *
        (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ := by
        rw [hc]
        group
    _ = _ := by group

theorem canonicalRep_simple_pair_zpow {M : Type} [Field M] [CharP M 2] (i j : Fin Tag.F4.rank)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    canonicalRep (coxeterSystem Tag.F4) M ((simple Tag.F4 i * simple Tag.F4 j) ^ ε) =
      (weylElt Tag.F4 M i 1 * weylElt Tag.F4 M j 1) ^ ε := by
  have h1 : canonicalRep (coxeterSystem Tag.F4) M (simple Tag.F4 i * simple Tag.F4 j) =
      weylElt Tag.F4 M i 1 * weylElt Tag.F4 M j 1 := by
    rw [EvenF4QPlus.canonicalRep_mul_of_charTwo, canonicalRep_simple, canonicalRep_simple]
  rcases hε with rfl | rfl
  · rw [zpow_one, zpow_one, h1]
  · rw [_root_.zpow_neg_one, _root_.zpow_neg_one, ← EvenF4QPlus.canonicalRep_inv_of_charTwo, h1]

@[expose] def pairCharKernelTorus (M : Type) [Field M] (i j : Fin Tag.F4.rank) :
    Subgroup (ModGL Tag.F4 M) where
  carrier := {h | h ∈ torusGroup Tag.F4 M ∧ torusRootChar h (Pi.single i 1) = 1 ∧
    torusRootChar h (Pi.single j 1) = 1}
  one_mem' := ⟨one_mem _, torusRootChar_one _, torusRootChar_one _⟩
  mul_mem' := fun {a b} ha hb => by
    have hda := torusGroup_le_diagonalGroup ha.1
    have hdb := torusGroup_le_diagonalGroup hb.1
    refine ⟨mul_mem ha.1 hb.1, ?_, ?_⟩
    · rw [torusRootChar_mul hda hdb, ha.2.1, hb.2.1, one_mul]
    · rw [torusRootChar_mul hda hdb, ha.2.2, hb.2.2, one_mul]
  inv_mem' := fun {a} ha => by
    have hda := torusGroup_le_diagonalGroup ha.1
    refine ⟨inv_mem ha.1, ?_, ?_⟩
    · rw [torusRootChar_inv hda, ha.2.1, inv_one]
    · rw [torusRootChar_inv hda, ha.2.2, inv_one]

theorem mem_pairCharKernelTorus {M : Type} [Field M] {i j : Fin Tag.F4.rank}
    (h : ModGL Tag.F4 M) :
    h ∈ pairCharKernelTorus M i j ↔ h ∈ torusGroup Tag.F4 M ∧
      torusRootChar h (Pi.single i 1) = 1 ∧ torusRootChar h (Pi.single j 1) = 1 :=
  Iff.rfl

theorem commutator_sup_le_of_abelian {G : Type*} [Group G] {H Q : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅H ⊔ Q, H ⊔ Q⁆ ≤ Q := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right H Q hN
  have hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (hN hh) q).1 hq
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have ha' : a ∈ (H : Set G) * (Q : Set G) := by rw [← hcoe]; exact ha
  have hb' : b ∈ (H : Set G) * (Q : Set G) := by rw [← hcoe]; exact hb
  obtain ⟨h₁, hh₁, q₁, hq₁, rfl⟩ := ha'
  obtain ⟨h₂, hh₂, q₂, hq₂, rfl⟩ := hb'
  have e : ⁅h₁ * q₁, h₂ * q₂⁆ = (h₁ * q₁ * h₁⁻¹) * ((h₁ * h₂) * (q₂ * q₁⁻¹) * (h₁ * h₂)⁻¹) *
      ((h₁ * h₂ * h₁⁻¹) * q₂⁻¹ * (h₁ * h₂ * h₁⁻¹)⁻¹) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) := by
    rw [commutatorElement_def]
    group
  have h4 : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = 1 := by
    rw [hH h₁ hh₁ h₂ hh₂]
    group
  rw [e, h4, mul_one]
  exact mul_mem (mul_mem (hconj _ hh₁ _ hq₁)
    (hconj _ (mul_mem hh₁ hh₂) _ (mul_mem hq₂ (inv_mem hq₁))))
    (hconj _ (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) _ (inv_mem hq₂))

theorem levi_fixed_commutator_eq {M : Type} [Field M] (J : Set (Fin Tag.F4.rank))
    (θ : ModGL Tag.F4 M →* ModGL Tag.F4 M)
    (hperf : Group.IsPerfect ↥(subsystemGroup Tag.F4 M J ⊓ θ.eqLocus (MonoidHom.id _))) :
    ⁅(torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M J) ⊓ θ.eqLocus (MonoidHom.id _),
        (torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M J) ⊓ θ.eqLocus (MonoidHom.id _)⁆ =
      subsystemGroup Tag.F4 M J ⊓ θ.eqLocus (MonoidHom.id _) := by
  have hHab := (triangular_borel_structure.{0, 0} Tag.F4 M).1
  have hnorm : torusGroup Tag.F4 M ≤
      Subgroup.normalizer (subsystemGroup Tag.F4 M J : Set (ModGL Tag.F4 M)) := by
    rw [subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hLQ := commutator_sup_le_of_abelian hHab hnorm
  apply le_antisymm
  · intro z hz
    refine Subgroup.mem_inf.2 ⟨hLQ (Subgroup.commutator_mono inf_le_left inf_le_left hz), ?_⟩
    exact (commutator_le_of_self _ hz).2
  · calc subsystemGroup Tag.F4 M J ⊓ θ.eqLocus (MonoidHom.id _) =
        ⁅subsystemGroup Tag.F4 M J ⊓ θ.eqLocus (MonoidHom.id _),
          subsystemGroup Tag.F4 M J ⊓ θ.eqLocus (MonoidHom.id _)⁆ :=
        (Subgroup.isPerfect_iff.1 hperf).symm
      _ ≤ _ := Subgroup.commutator_mono (inf_le_inf_right _ le_sup_right)
          (inf_le_inf_right _ le_sup_right)

end CFSG.RankThree.Chevalley
