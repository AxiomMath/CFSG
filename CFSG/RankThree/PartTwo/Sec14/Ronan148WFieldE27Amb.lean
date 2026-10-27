module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjField
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofAut
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Aut
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

section Inner

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def innerEquiv (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) :
    ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner (projImage (slPi π 3 (p ^ f) K))) ≃*
      projImage (slPi π 3 (p ^ f) K) :=
  (MonoidHom.ofInjective (conj_injective_projImage hK hq hq2)).symm

theorem coe_innerEquiv_symm (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (m : projImage (slPi π 3 (p ^ f) K)) :
    (((innerEquiv hK hq hq2).symm m : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projImage (slPi π 3 (p ^ f) K)))) : MulAut (projImage (slPi π 3 (p ^ f) K))) =
      MulAut.conj m :=
  rfl

theorem slAct_innerEquiv (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) :
    slAct (innerEquiv hK hq hq2) ⟨β, mem_normalizer_of_normal β⟩ = β := by
  refine MulEquiv.ext fun m => ?_
  rw [slAct_apply]
  apply (innerEquiv hK hq hq2).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [coe_normalizerMonoidHom, coe_innerEquiv_symm, coe_innerEquiv_symm, mulAut_conj_apply_eq]
  rfl

end Inner

section FieldB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem fieldB_structure_of_elemAbelian (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s)) :
    (∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)),
        ∃ y, IsPGLAtP e b y ∧ frobGL ψ y = y) ∧
      Nat.card A = Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) * 3 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hΨ3 := frobGL_three' hφ3 hψ
  have hσs : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) =
        projOf _ ⟨frobGL ψ s, frobGL_mem_slPi hK ψ hs⟩ :=
    fun s hs => Subtype.ext (by rw [hσψ, coe_projOf])
  have hinnerpgl : ∀ b ∈ L ⊔ Subgroup.centralizer (L : Set G), ∃ y, IsPGLAtP e b y := by
    intro b hb
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨_, isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu)⟩
  have hfix : ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∃ y', IsPGLAtP e a y' ∧ frobGL ψ y' = y' :=
    fun a ha y hy => exists_fixed_liftP hK hq hf hφ hφ3 hψ hσψ (hAcomm a ha σ hσA) hy
  have hpglB : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) := by
    intro a ha y hy
    obtain ⟨y', hy', hy'ψ⟩ := hfix a ha y hy
    exact ⟨ha, mem_sup_centralizer_of_fixedP hK hq hf hφ hφ3 hψ hy' hy'ψ⟩
  have hpglOf : ∀ x : G, ∀ g ∈ glPi π 3 (p ^ f) K, (∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨x, mem_normalizer_of_normal x⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * s * g⁻¹)) → IsPGLAtP e x g := by
    intro x g hg hx
    refine ⟨hg, fun m => ?_⟩
    obtain ⟨⟨s, hs⟩, rfl⟩ := projOf_surjective _ m
    rw [hx, coe_projOf, map_mul, map_mul, map_inv]
  have hgen : ∀ a ∈ A, a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers σ := by
    intro a ha
    have ha3 : slAct e ⟨a, mem_normalizer_of_normal a⟩ ^ 3 = 1 :=
      slAct_pow_three_of e (mem_normalizer_of_normal a) (hA.2 a ha)
    rcases Sec11.KS11LieProof.aut_pgl_or_field hK hq2 _ ha3 with ⟨y, hy, hys⟩ |
      ⟨f₀', hf', ψa, hψa, g, hg, hga⟩
    · exact Subgroup.mem_sup_left (hpglB a ha y ⟨hy, hys⟩)
    · have hf₀' : f₀' = f₀ := by omega
      subst hf₀'
      have hψa' : ψa = φ ∨ ψa = φ ^ 2 := eq_or_eq_sq_of_pow hφ hψa
      have hσσ : σ * σ ∈ Subgroup.zpowers σ := mul_mem (Subgroup.mem_zpowers σ)
        (Subgroup.mem_zpowers σ)
      by_cases hsame : ψa = ψ
      · have hx : IsPGLAtP e (a * σ * σ) g := by
          refine hpglOf _ g hg fun s hs => ?_
          rw [slAct_mul_applyP, slAct_mul_applyP, hσs, hσs, hga, hsame, hΨ3]
        have hxB := hpglB _ (mul_mem (mul_mem ha hσA) hσA) g hx
        have : a = a * σ * σ * (σ * σ)⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB) (Subgroup.mem_sup_right (inv_mem hσσ))
      · have hx : IsPGLAtP e (a * σ) g := by
          refine hpglOf _ g hg fun s hs => ?_
          rw [slAct_mul_applyP, hσs, hga,
            frobGL_comp_eq (ringAut_comp_of_ne hφ3 hψ hψa' hsame)]
        have hxB := hpglB _ (mul_mem ha hσA) g hx
        have : a = a * σ * σ⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB)
          (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers σ)))
  have hAeq : A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ :=
    le_antisymm (fun a ha => hgen a ha) (sup_le inf_le_left (Subgroup.zpowers_le.mpr hσA))
  have hBσ : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.zpowers σ = ⊥ :=
    inf_zpowers_eq_bot (hA.2 σ hσA) (fun h => hσB h.2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 :=
    orderOf_eq_prime (hA.2 σ hσA) (fun h => hσB (h ▸ Subgroup.one_mem _))
  have hcomm : ∀ x ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∀ y ∈ Subgroup.zpowers σ,
      x * y = y * x := fun x hx y hy =>
    hAcomm x hx.1 y ((Subgroup.zpowers_le.mpr hσA) hy)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [← hAeq, hBσ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hσo] at hcard
  refine ⟨fun b hb => ?_, hcard⟩
  obtain ⟨y, hy⟩ := hinnerpgl b hb.2
  exact hfix b hb.1 y hy

end FieldB

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
