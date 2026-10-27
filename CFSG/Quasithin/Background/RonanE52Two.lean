module

public import CFSG.Quasithin.Background.E5Two

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem dichotomy_two {S B D X : Subgroup Γ} (hE : E1.ETwo Γ S B) (hD2 : IsPGroup 2 D)
    [hXn : X.Normal] (hDX : D ≤ X)
    (hX : twoResidual X ≤ Subgroup.centralizer (CFSG.Open.pCore 2 Γ : Set Γ)) :
    twoResidual (⊤ : Subgroup Γ) ≤ Subgroup.centralizer (CFSG.Open.pCore 2 Γ : Set Γ) ∨
      D ≤ CFSG.Open.pCore 2 Γ := by
  set Q := CFSG.Open.pCore 2 Γ with hQdef
  set C := Subgroup.centralizer (Q : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  obtain ⟨h2c, h2top, hres, L, hL, hlayer, -⟩ := hE
  set R := CFSG.solvableRadical Γ with hRdef
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hrad : CFSG.solvableRadical (Γ ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot Γ
  set Xb := X.map π with hXb
  have hXbn : Xb.Normal := Subgroup.Normal.map hXn π hπs
  by_cases hX1 : Xb = ⊥
  · right
    have hXR : X ≤ R := by
      rwa [hXb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hX1
    have h1 := E3.inf_solvableRadical_eq_inf_pCore h2c hD2
    intro d hd
    have hd' : d ∈ R ⊓ D := ⟨hXR (hDX hd), hd⟩
    rw [h1] at hd'
    exact hd'.1
  · left
    obtain ⟨K, hK, hKX⟩ := E3.exists_component_le_of_normal hrad hX1
    have hKL : ∃ t ∈ (E1.tauOf ⊤ S B).map π, K = A1b.conjSub t L := by
      by_contra hno
      push Not at hno
      have hle : CFSG.layer (Γ ⧸ R) ≤ Subgroup.centralizer (K : Set (Γ ⧸ R)) := by
        rw [hlayer]
        refine iSup₂_le fun t ht => ?_
        have hcL : CFSG.IsComponent (A1b.conjSub t L) :=
          CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL
        have := (CFSG.LocalCores.distinct_components_commute hK hcL).resolve_left (hno t ht)
        rw [Subgroup.commutator_comm] at this
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
      have hKc : K ≤ Subgroup.centralizer (K : Set (Γ ⧸ R)) :=
        (CFSG.LocalCores.component_le_layer hK).trans hle
      have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.1 (hKc ha) b hb).symm
      exact E3.component_not_isSolvable hK
        (Group.isSolvable_of_comm fun a b => Subtype.ext (hab a a.2 b b.2))
    obtain ⟨t, -, hKt⟩ := hKL
    have hlay : CFSG.layer (Γ ⧸ R) ≤ Xb := by
      rw [hlayer]
      refine iSup₂_le fun t' _ => ?_
      have e : A1b.conjSub t' L = A1b.conjSub (t' * t⁻¹) K := by
        rw [hKt, ← A1b.conjSub_mul, inv_mul_cancel_right]
      rw [e]
      intro x hx
      rw [A1b.mem_conjSub_iff] at hx
      have := hXbn.conj_mem _ (hKX hx) (t' * t⁻¹)
      simpa [mul_assoc] using this
    have hlay2 : CFSG.layer (Γ ⧸ R) ≤ C.map π := by
      calc CFSG.layer (Γ ⧸ R) ≤ perfectCore Xb :=
            le_perfectCore_of_perfect hlay CFSG.LocalCores.layer_perfect
        _ ≤ twoResidual Xb := E5.perfectCore_le_twoResidual Xb
        _ = (twoResidual X).map π := (E1.map_twoResidual π X).symm
        _ ≤ C.map π := Subgroup.map_mono hX
    have hR : twoResidual (⊤ : Subgroup Γ) ≤ C ⊔ R := by
      refine (twoResidual_le_of_isTwoQuotient le_top
        (fun g _ => (Subgroup.normalizer_eq_top_iff.2 (E1.instNormalOInftyE Γ)) ▸
          Subgroup.mem_top g)
        (fun y _ => E1.exists_pow_mem_of_mem_pCore (M := oInftyE Γ)
          (fun q => by rw [h2top]; exact Subgroup.mem_top _) y)).trans ?_
      have h1 : oInftyE Γ = (CFSG.layer (Γ ⧸ R)).comap π := rfl
      rw [h1]
      calc (CFSG.layer (Γ ⧸ R)).comap π ≤ (C.map π).comap π := Subgroup.comap_mono hlay2
        _ = C ⊔ R := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
    rw [hres] at hR ⊢
    calc perfectCore (⊤ : Subgroup Γ) = perfectCore (perfectCore (⊤ : Subgroup Γ)) :=
          (perfectCore_eq_self_of_perfect (perfectCore_perfect _)).symm
      _ ≤ perfectCore (C ⊔ R) := perfectCore_mono hR
      _ ≤ C := perfectCore_le_of_sup_solvable le_sup_left
          ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
            (le_top.trans (Subgroup.normalizer_eq_top_iff.2 hCn).ge)) rfl hRs

end CFSG.Quasithin.RonanE52
