module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Core
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGTBJF4ModelAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

theorem ggTBJ_f4_stdModel
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* ↥(adjointGroup Tag.F4 K)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p 4 ↥(adjointGroup Tag.F4 K)
      (Set.range (MulAut.conj : ↥(adjointGroup Tag.F4 K) →* MulAut ↥(adjointGroup Tag.F4 K)))
      L' ψ₀ A) :
    ∃ (ζ : Kˣ) (ψ : L' →* ModGL Tag.F4 K) (σ : Multiplicative (Fin 4 → ZMod p) →* L')
      (Θ : Multiplicative (Fin 4 → ZMod p) ≃* ↥A),
      GGTBJF4Std p ζ ψ σ ∧ ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := by
  classical
  obtain ⟨hψ0, hker0, hperf0, hAe0, hAI0, hr0, h3_0, -⟩ := hA
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K)
  have hG : GGTorusWeylGenElt p 4 ↥(adjointGroup Tag.F4 K) :=
    ExcWeylGen.ggTorusWeylGenElt_adjointF4_all (K := K) hp hp2
  have hI : Set.range (MulAut.conj : ↥(adjointGroup Tag.F4 K) →*
      MulAut ↥(adjointGroup Tag.F4 K)) ⊆
      Set.range (MulAut.conj : ↥(adjointGroup Tag.F4 K) →*
      MulAut ↥(adjointGroup Tag.F4 K)) := fun _ hx => hx
  obtain ⟨k, τ, σ, s, hτinj, hψσ, hΘσ, -⟩ :=
    exists_weylGenModel hp hp2 hI hZ hG hψ0 hker0 hperf0 hAe0 hAI0 hr0 h3_0
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  set E : Subgroup ↥(adjointGroup Tag.F4 K) := τ.range with hE
  have hEab : IsElemAbelian p E := by
    rw [hE]
    exact isElemAbelian_range (fun a b => mul_comm a b)
      (fun a => pow_eq_one_of_multiplicative_fin_zmod a) τ
  have hcardE : Nat.card E = Nat.card A := by
    rw [hE]
    exact Nat.card_congr ((MonoidHom.ofInjective hτinj).toEquiv.symm.trans s.toEquiv)
  have hrE : p ^ 4 ≤ Nat.card E := by rw [hcardE]; exact hr0
  obtain ⟨g, hg⟩ := hT E hEab hrE
  have hcardp : Nat.card E = p ^ 4 := by
    have h1 : Nat.card E = Nat.card (E.map (MulAut.conj g).toMonoidHom) :=
      Nat.card_congr (E.equivMapOfInjective (MulAut.conj g).toMonoidHom
        fun _ _ h => (MulAut.conj g).injective h).toEquiv
    rw [h1, hg, TableBF4.card_torusPow hp hpq]
  have hcardA : Nat.card (Multiplicative (Fin k → ZMod p)) = p ^ 4 := by
    rw [Nat.card_congr s.toEquiv, ← hcardE, hcardp]
  have hk : k = 4 := Nat.pow_right_injective hp.two_le (by
    change p ^ k = p ^ 4
    rw [← CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod k]
    exact hcardA)
  subst hk
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  set χ : Multiplicative (Fin 4 → ZMod p) →* ↥(adjointGroup Tag.F4 K) :=
    chevTorus .F4 ζ hζ with hχdef
  have hχinj : Function.Injective χ := by
    rw [hχdef]
    exact chevTorus_injective hζo hζ hdet
  have hχr : χ.range = TableBF4.torusPow K p := by
    rw [hχdef]
    exact range_chevTorus_eq_torusPow_of_prime hp hpq hζo hζ
  set τ₀ : Multiplicative (Fin 4 → ZMod p) →* ↥(adjointGroup Tag.F4 K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp χ with hτ₀def
  have hτ₀inj : Function.Injective τ₀ := by
    rw [hτ₀def]
    exact (MulAut.conj g⁻¹).injective.comp hχinj
  have hτ₀range : τ₀.range = E := by
    rw [hτ₀def, MonoidHom.range_comp, hχr,
      show TableBF4.torusPow K p = E.map (MulAut.conj g).toMonoidHom from hg.symm,
      Subgroup.map_map]
    have h2 : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id ↥(adjointGroup Tag.F4 K) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [h2, Subgroup.map_id]
  obtain ⟨γ, hγ⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτinj hτ₀inj
    (hE.symm.trans hτ₀range.symm)
  set χ' : Multiplicative (Fin 4 → ZMod p) →* ↥(adjointGroup Tag.F4 K) :=
    ggTBJF4RootDiagModel (K := K) p ζ hζ with hχ'def
  have hχ'inj : Function.Injective χ' := by
    rw [hχ'def]
    exact ggTBJF4RootDiagModel_injective (K := K) p ζ hζ hζo
  have hχ'r : χ'.range = TableBF4.torusPow K p := by
    rw [hχ'def]
    exact ggTBJF4RootDiagModel_range (K := K) p ζ hζ hζo
  obtain ⟨ε, hε⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hχ'inj hχinj (hχ'r.trans hχr.symm)
  let ψ : L' →* ModGL Tag.F4 K :=
    (adjointGroup Tag.F4 K).subtype.comp ((MulAut.conj g).toMonoidHom.comp ψ₀)
  have hψ_apply : ∀ l : L', ψ l = (((MulAut.conj g) (ψ₀ l) : ↥(adjointGroup Tag.F4 K)) :
      ModGL Tag.F4 K) := fun l => rfl
  refine ⟨ζ, ψ, σ.comp (ε.trans γ.symm).toMonoidHom, (ε.trans γ.symm).trans s, ?_, ?_⟩
  · refine ⟨?_, ?_, hζo, ?_⟩
    ·
      intro l hl
      rw [MonoidHom.mem_ker] at hl
      apply hker0
      rw [MonoidHom.mem_ker]
      have h2 : (MulAut.conj g) (ψ₀ l) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_one]
        simpa only [hψ_apply l] using hl
      exact (MulAut.conj g).map_eq_one_iff.mp h2
    ·
      have hmapTop : (⊤ : Subgroup ↥(adjointGroup Tag.F4 K)).map
          (adjointGroup Tag.F4 K).subtype = adjointGroup Tag.F4 K := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩; exact y.2
        · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
      show (((adjointGroup Tag.F4 K).subtype.comp
        ((MulAut.conj g).toMonoidHom.comp ψ₀)).range) = adjointGroup Tag.F4 K
      rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ0,
        Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, hmapTop]
    ·
      intro f
      show ψ (σ ((ε.trans γ.symm) f)) = rootDiagUnit Tag.F4 (ggTBJa p ζ f)
      have hεf : χ (ε f) = χ' f := by
        have h := MonoidHom.ext_iff.mp hε f
        rw [MonoidHom.comp_apply] at h
        exact h
      have hτδ : τ ((ε.trans γ.symm) f) =
          g⁻¹ * χ' f * g := by
        have hδ : (ε.trans γ.symm) f = γ.symm (ε f) := rfl
        calc τ ((ε.trans γ.symm) f)
            = τ₀ (γ ((ε.trans γ.symm) f)) :=
                (MonoidHom.ext_iff.mp hγ ((ε.trans γ.symm) f)).symm
          _ = τ₀ (ε f) := by rw [hδ, MulEquiv.apply_symm_apply]
          _ = g⁻¹ * χ (ε f) * g := by
                rw [hτ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
                group
          _ = g⁻¹ * χ' f * g := by rw [hεf]
      have hconj : (MulAut.conj g) (τ ((ε.trans γ.symm) f)) = χ' f := by
        rw [hτδ, MulAut.conj_apply]
        group
      rw [hψ_apply, hψσ ((ε.trans γ.symm) f)]
      rw [congrArg Subtype.val hconj, hχ'def, ggTBJF4RootDiagModel_apply]
  ·
    intro f
    show ((s ((ε.trans γ.symm) f) : ↥A) : MulAut L') =
      MulAut.conj (σ ((ε.trans γ.symm) f))
    exact hΘσ ((ε.trans γ.symm) f)

end CFSG.StandardType

end
