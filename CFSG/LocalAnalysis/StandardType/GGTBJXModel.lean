module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylNormAdjoint
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcToralRank
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

section RootDiag

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def ggTBJXRootDiagModel (τ : Tag) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : ζ ^ p = 1)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K) :
    Multiplicative (Fin τ.rank → ZMod p) →* ↥(adjointGroup τ K) :=
  ((rootDiagUnitHom τ K).comp (chevTorusExp τ ζ hζ)).codRestrict (adjointGroup τ K) fun f =>
    torusGroup_le_adjointGroup (hfullp _ fun i => by
      change (ζ ^ (Multiplicative.toAdd f i).val) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])

theorem ggTBJXRootDiagModel_apply (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (f : Multiplicative (Fin τ.rank → ZMod p)) :
    ((ggTBJXRootDiagModel τ p ζ hζ hfullp f : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootDiagUnit τ (ggTBJXa p τ ζ f) :=
  rfl

private theorem ggTBJXAux_rootDiag_eq (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (f : Multiplicative (Fin τ.rank → ZMod p)) :
    ggTBJXRootDiagModel τ p ζ hζ hfullp f =
      TableBExc.torusPowEltP hfullp hζ (Multiplicative.toAdd f) :=
  Subtype.ext rfl

theorem ggTBJXRootDiagModel_injective (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K) :
    Function.Injective (ggTBJXRootDiagModel τ p ζ hζ hfullp) := by
  intro f g hfg
  rw [ggTBJXAux_rootDiag_eq, ggTBJXAux_rootDiag_eq] at hfg
  exact Multiplicative.toAdd.injective
    ((TableBExc.bijective_torusPowEltP hfullp hζo hζ).2.1 hfg)

theorem ggTBJXRootDiagModel_range (p : ℕ) [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K) :
    (ggTBJXRootDiagModel τ p ζ hζ hfullp).range = TableBExc.torusPow τ K p := by
  obtain ⟨hmem, -, hsurj⟩ := TableBExc.bijective_torusPowEltP hfullp hζo hζ
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    rw [ggTBJXAux_rootDiag_eq]
    exact hmem _
  · intro hx
    obtain ⟨v, hv⟩ := hsurj x hx
    exact ⟨Multiplicative.ofAdd v, by rw [ggTBJXAux_rootDiag_eq]; exact hv⟩

end RootDiag

theorem ggTBJX_stdModel
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* ↥(adjointGroup τ K)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p τ.rank ↥(adjointGroup τ K)
      (Set.range (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))) L' ψ₀ A) :
    ∃ (ζ : Kˣ) (ψ : L' →* ModGL τ K) (σ : Multiplicative (Fin τ.rank → ZMod p) →* L')
      (Θ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A),
      GGTBJXStd p τ ζ ψ σ ∧ ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := by
  classical
  obtain ⟨hψ0, hker0, hperf0, hAe0, hAI0, hr0, h3_0, -⟩ := hA
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := τ) (K := K)
  have hG : GGTorusWeylGenElt p τ.rank ↥(adjointGroup τ K) :=
    ExcWeylGen.ggTorusWeylGenElt_adjoint hp hp2 hpq hdet hV hT
  have hI : Set.range (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) ⊆
      Set.range (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) :=
    fun _ hx => hx
  obtain ⟨k, τ', σ, s, hτinj, hψσ, hΘσ, -⟩ :=
    exists_weylGenModel hp hp2 hI hZ hG hψ0 hker0 hperf0 hAe0 hAI0 hr0 h3_0
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  set E : Subgroup ↥(adjointGroup τ K) := τ'.range with hE
  have hEab : IsElemAbelian p E := by
    rw [hE]
    exact isElemAbelian_range (fun a b => mul_comm a b)
      (fun a => pow_eq_one_of_multiplicative_fin_zmod a) τ'
  have hcardE : Nat.card E = Nat.card A := by
    rw [hE]
    exact Nat.card_congr ((MonoidHom.ofInjective hτinj).toEquiv.symm.trans s.toEquiv)
  have hrE : p ^ τ.rank ≤ Nat.card E := by rw [hcardE]; exact hr0
  obtain ⟨g, hg⟩ := hT E hEab hrE
  have hcardp : Nat.card E = p ^ τ.rank := by
    have h1 : Nat.card E = Nat.card (E.map (MulAut.conj g).toMonoidHom) :=
      Nat.card_congr (E.equivMapOfInjective (MulAut.conj g).toMonoidHom
        fun _ _ h => (MulAut.conj g).injective h).toEquiv
    rw [h1, hg, hV]
  have hcardA : Nat.card (Multiplicative (Fin k → ZMod p)) = p ^ τ.rank := by
    rw [Nat.card_congr s.toEquiv, ← hcardE, hcardp]
  have hk : k = τ.rank := Nat.pow_right_injective hp.two_le (by
    change p ^ k = p ^ τ.rank
    rw [← CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod k]
    exact hcardA)
  subst hk
  set χ : Multiplicative (Fin τ.rank → ZMod p) →* ↥(adjointGroup τ K) :=
    chevTorus τ ζ hζ with hχdef
  have hχinj : Function.Injective χ := by
    rw [hχdef]
    exact chevTorus_injective hζo hζ hdet
  have hχr : χ.range = TableBExc.torusPow τ K p := by
    rw [hχdef]
    exact TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  set τ₀ : Multiplicative (Fin τ.rank → ZMod p) →* ↥(adjointGroup τ K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp χ with hτ₀def
  have hτ₀inj : Function.Injective τ₀ := by
    rw [hτ₀def]
    exact (MulAut.conj g⁻¹).injective.comp hχinj
  have hτ₀range : τ₀.range = E := by
    rw [hτ₀def, MonoidHom.range_comp, hχr,
      show TableBExc.torusPow τ K p = E.map (MulAut.conj g).toMonoidHom from hg.symm,
      Subgroup.map_map]
    have h2 : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id ↥(adjointGroup τ K) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [h2, Subgroup.map_id]
  obtain ⟨γ, hγ⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτinj hτ₀inj
    (hE.symm.trans hτ₀range.symm)
  set χ' : Multiplicative (Fin τ.rank → ZMod p) →* ↥(adjointGroup τ K) :=
    ggTBJXRootDiagModel τ p ζ hζ hfullp with hχ'def
  have hχ'inj : Function.Injective χ' := by
    rw [hχ'def]
    exact ggTBJXRootDiagModel_injective p ζ hζ hζo hfullp
  have hχ'r : χ'.range = TableBExc.torusPow τ K p := by
    rw [hχ'def]
    exact ggTBJXRootDiagModel_range p ζ hζ hζo hfullp
  obtain ⟨ε, hε⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hχ'inj hχinj (hχ'r.trans hχr.symm)
  let ψ : L' →* ModGL τ K :=
    (adjointGroup τ K).subtype.comp ((MulAut.conj g).toMonoidHom.comp ψ₀)
  have hψ_apply : ∀ l : L', ψ l = (((MulAut.conj g) (ψ₀ l) : ↥(adjointGroup τ K)) :
      ModGL τ K) := fun l => rfl
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
      have hmapTop : (⊤ : Subgroup ↥(adjointGroup τ K)).map
          (adjointGroup τ K).subtype = adjointGroup τ K := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩; exact y.2
        · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
      show (((adjointGroup τ K).subtype.comp
        ((MulAut.conj g).toMonoidHom.comp ψ₀)).range) = adjointGroup τ K
      rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ0,
        Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, hmapTop]
    ·
      intro f
      show ψ (σ ((ε.trans γ.symm) f)) = rootDiagUnit τ (ggTBJXa p τ ζ f)
      have hεf : χ (ε f) = χ' f := by
        have h := MonoidHom.ext_iff.mp hε f
        rw [MonoidHom.comp_apply] at h
        exact h
      have hτδ : τ' ((ε.trans γ.symm) f) = g⁻¹ * χ' f * g := by
        have hδ : (ε.trans γ.symm) f = γ.symm (ε f) := rfl
        calc τ' ((ε.trans γ.symm) f)
            = τ₀ (γ ((ε.trans γ.symm) f)) :=
                (MonoidHom.ext_iff.mp hγ ((ε.trans γ.symm) f)).symm
          _ = τ₀ (ε f) := by rw [hδ, MulEquiv.apply_symm_apply]
          _ = g⁻¹ * χ (ε f) * g := by
                rw [hτ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
                group
          _ = g⁻¹ * χ' f * g := by rw [hεf]
      have hconj : (MulAut.conj g) (τ' ((ε.trans γ.symm) f)) = χ' f := by
        rw [hτδ, MulAut.conj_apply]
        group
      rw [hψ_apply, hψσ ((ε.trans γ.symm) f)]
      rw [congrArg Subtype.val hconj, hχ'def, ggTBJXRootDiagModel_apply]
  ·
    intro f
    show ((s ((ε.trans γ.symm) f) : ↥A) : MulAut L') =
      MulAut.conj (σ ((ε.trans γ.symm) f))
    exact hΘσ ((ε.trans γ.symm) f)

theorem ggTBJX_typeFacts
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : τ = .E6 → p ≠ 3) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K - 1) :
    IsUnit ((τ.cartan.det : ℤ) : ZMod p) ∧
      Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank ∧ GGExcToralRankInput τ K p ∧
      ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hτ with rfl | rfl | rfl
  · have hp3' : p ≠ 3 := hp3 rfl
    refine ⟨?_, TableBExc.card_torusPow_E6 hp hp3' hpq,
      TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3' hpq,
      TableBExc.fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3'))⟩
    rw [det_cartan_E6]
    have h3 : ((3 : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      have h' : p ∣ 3 := by exact_mod_cast h
      exact hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
    exact Ne.isUnit h3
  · refine ⟨?_, CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_torusPow_E7_of_dvd hp hp2 hpq,
      CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.ggExcToralRankInput_of_odd_dvd (Or.inl rfl) hp
        hp2 hpq,
      CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.rootDiagUnit_mem_torusGroup_E7_of_pow_eq_one hp
        hp2⟩
    rw [det_cartan_E7]
    have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      have h' : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    exact Ne.isUnit h2
  · refine ⟨?_, CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_torusPow_E8_of_dvd hp hpq,
      CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.ggExcToralRankInput_of_odd_dvd (Or.inr rfl) hp
        hp2 hpq,
      fun a _ => CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_E8 a⟩
    rw [det_cartan_E8, Int.cast_one]
    exact isUnit_one

end CFSG.StandardType

end
