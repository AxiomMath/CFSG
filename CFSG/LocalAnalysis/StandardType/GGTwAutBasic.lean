module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGKGAAutomizer
public import CFSG.LocalAnalysis.StandardType.GGKGARank

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTw_pow_eq_one_of_lift {p : ℕ} {R L' : Type} [Group R] [Group L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {a : MulAut L'} {φ : MulAut R}
    (hφ : ∀ l : L', φ (ψ l) = ψ (a l)) (ha : a ^ p = 1) : φ ^ p = 1 := by
  have hpow : ∀ (n : ℕ) (l : L'), (φ ^ n) (ψ l) = ψ ((a ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hpow p l, ha]
  simp

theorem ggTorusRankLE_of_elemAbelian {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (h : GGElemAbelianRankLE R p r) : GGTorusRankLE p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI φ hφI (ggTw_pow_eq_one_of_lift hψ hφ (hA.2 a ha))
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  rw [← hcardE]
  exact h E hEab

theorem ggTorusSCRank_of_selfCentRankGE {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSelfCentRankGE p r R) : GGTorusSCRank p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hsc
  have h3 := ggTorusSCRank_of_selfCent (I := {φ ∈ I | φ ^ p = 1}) hp
    (fun φ hφ => hI φ hφ.1 hφ.2) hZ hcp h
  refine h3 L' ψ hψ hker hperf A hA (fun a ha => ?_) hsc
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  exact ⟨φ, ⟨hφI, ggTw_pow_eq_one_of_lift hψ hφ (hA.2 a ha)⟩, hφ⟩

theorem ggTwTorus_recipe_of_pieces {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (hS : GGTorusSignedEltSC p R) (hU : GGElemAbelianRankLE R p r)
    (hL : GGSelfCentRankGE p r R) :
    GGTorusAutCardSC p R I r (2 ^ r * r.factorial) := by
  have hU' := ggTorusRankLE_of_elemAbelian hZ hI hU
  have hL' := ggTorusSCRank_of_selfCentRankGE hp hZ hI hcp hL
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have hrk : p ^ r ≤ Nat.card A := hL' L' ψ hψ hker hperf A hA hAI hsc
  have hup : Nat.card A ≤ p ^ r := hU' L' ψ hψ hker hperf A hA hAI
  have hAI' : ∀ a ∈ A, ∃ φ ∈ {φ ∈ I | φ ^ p = 1}, ∀ l : L', φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    exact ⟨φ, ⟨hφI, ggTw_pow_eq_one_of_lift hψ hφ (hA.2 a ha)⟩, hφ⟩
  obtain ⟨k, Θ, -, -, hsgn, hperm, hsp⟩ := exists_signedModelSC (I := {φ ∈ I | φ ^ p = 1}) hp hp2
    (fun φ hφ => hI φ hφ.1 hφ.2) hZ hcp hS hψ hker hperf hA hAI' h3 hsc
  have hk : k = r := KGA.kga_k_eq hp Θ hrk hup
  subst hk
  exact ⟨hrk, KGA.kga_card_automizer hp hp2 Θ hsgn hperm hsp⟩

theorem ggTw_cast_three_ne_zero {K : Type} [Field K] [CharP K 2] : ((3 : ℕ) : K) ≠ 0 := by
  intro hzero
  have h := (CharP.cast_eq_zero_iff K 2 3).mp hzero
  omega

end CFSG.StandardType

end
