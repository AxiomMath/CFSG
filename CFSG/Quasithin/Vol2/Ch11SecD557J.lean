module

public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11SecD557NatA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] {n : ℕ} {L K V V₁ W : Subgroup G}

noncomputable def autOnHom (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    ↥L →* ↥(autOn L W) :=
  ((conjAct W).comp (Subgroup.inclusion hLW)).codRestrict (autOn L W) fun l =>
    ⟨Subgroup.inclusion hLW l, l.2, rfl⟩

theorem autOnHom_apply (hLW : L ≤ Subgroup.normalizer (W : Set G)) (l : ↥L) (w : ↥W) :
    (((autOnHom hLW l : ↥(autOn L W)) : MulAut ↥W) w : G) = (l : G) * w * (l : G)⁻¹ :=
  conjAct_coe_apply W _ w

theorem autOnHom_surjective (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    Function.Surjective (autOnHom hLW) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem binaryNaturalSL_autOn (hn : 0 < n) (D : NatData3 n L K V V₁) [IsMulCommutative ↥W]
    (hVW : V ≤ W) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hKW : ∀ k ∈ L, k ∈ K → ∀ w ∈ W, k * w * k⁻¹ = w) :
    BinaryNaturalSL (autOn L W) (V.subgroupOf W) ⊥ 3 n := by
  set F := GaloisField 2 n
  have hker : D.θ.ker ≤ (autOnHom hLW).ker := by
    intro l hl
    have hlK : (l : G) ∈ K := by
      have h1 : l ∈ K.subgroupOf L := by rw [← D.ker_eq]; exact hl
      exact h1
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [autOnHom_apply]
    exact hKW l l.2 hlK w w.2
  let π₁ : SL(3, F) →* ↥(autOn L W) := (QuotientGroup.lift D.θ.ker (autOnHom hLW) hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective D.θ D.surj).symm.toMonoidHom
  have hπ₁ : ∀ l : ↥L, π₁ (D.θ l) = autOnHom hLW l := fun l => by
    have e : (QuotientGroup.quotientKerEquivOfSurjective D.θ D.surj).symm (D.θ l) =
        (l : ↥L ⧸ D.θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift D.θ.ker (autOnHom hLW) hker
      ((QuotientGroup.quotientKerEquivOfSurjective D.θ D.surj).symm (D.θ l)) = _
    rw [e, QuotientGroup.lift_mk]
  let π : ↥(StatedSL 3 F) →* ↥(autOn L W) := π₁.comp (statedSLEquiv' 3 F).toMonoidHom
  have hπ : ∀ γ : ↥(StatedSL 3 F), ∃ l : ↥L, D.θ l = statedSLEquiv' 3 F γ ∧
      π γ = autOnHom hLW l := fun γ => by
    obtain ⟨l, hl⟩ := D.surj (statedSLEquiv' 3 F γ)
    refine ⟨l, hl, ?_⟩
    show π₁ (statedSLEquiv' 3 F γ) = _
    rw [← hl, hπ₁]
  have hπs : Function.Surjective π := by
    intro a
    obtain ⟨l, rfl⟩ := autOnHom_surjective hLW a
    obtain ⟨γ, hγ⟩ := (statedSLEquiv' 3 F).surjective (D.θ l)
    exact ⟨γ, by show π₁ (statedSLEquiv' 3 F γ) = _; rw [hγ, hπ₁]⟩
  let f : ↥(V.subgroupOf W) →* Multiplicative (Fin 3 → F) :=
    D.ψ.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hVW).toMonoidHom
  have hf : ∀ u : ↥(V.subgroupOf W),
      f u = D.ψ ⟨((u : ↥W) : G), Subgroup.mem_subgroupOf.mp u.2⟩ := fun u => rfl
  refine ⟨F, inferInstance, inferInstance, GaloisField.card 2 n hn.ne', π,
    CFSG.Quasithin.G64.realizesVia_nat_of hπs bot_le ?_ ?_ f ?_ ?_ ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    show ((conjAct W x u : ↥W) : G) ∈ V
    rw [conjAct_coe_apply]
    exact (Subgroup.mem_normalizer_iff.mp (D.hnorm hx) u).mp hu
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨v, rfl⟩ := D.ψ.surjective y
    exact ⟨(Subgroup.subgroupOfEquivOfLe hVW).symm v, by simp [f]⟩
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : (Subgroup.subgroupOfEquivOfLe hVW) u = 1 :=
        D.ψ.injective (h1.trans (map_one _).symm)
      have h3 : u = 1 :=
        (Subgroup.subgroupOfEquivOfLe hVW).injective (h2.trans (map_one _).symm)
      rw [h3]
      rfl
    · intro h1
      have h3 : u = 1 := Subtype.ext h1
      rw [h3, map_one]
  · intro γ u hu
    obtain ⟨l, hl, hπl⟩ := hπ γ
    have hconj : (⟨((((π γ : ↥(autOn L W)) : MulAut ↥W) (u : ↥W)) : G),
        Subgroup.mem_subgroupOf.mp hu⟩ : ↥V) =
        conjAct V ⟨l, D.hnorm l.2⟩ ⟨((u : ↥W) : G), Subgroup.mem_subgroupOf.mp u.2⟩ := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      show (((π γ : ↥(autOn L W)) : MulAut ↥W) (u : ↥W) : G) = _
      rw [hπl, autOnHom_apply]
    rw [hf, hf, hconj, D.equiv l, natAct3_apply, hl]
    show _ = Multiplicative.ofAdd ((((γ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).mulVec
      (Multiplicative.toAdd (D.ψ ⟨((u : ↥W) : G), Subgroup.mem_subgroupOf.mp u.2⟩)))
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, coe_statedSLEquiv']

end CFSG.Quasithin.Vol2.Ch11.SecD
