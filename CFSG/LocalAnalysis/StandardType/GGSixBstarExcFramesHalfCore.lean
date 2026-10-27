module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFramesHalf

open ExcFrames

section Base

variable {τ : Tag} {K L : Type} [Field K] [Field L]

@[expose] noncomputable def adjBaseChange (ι : K →+* L) : adjointGroup τ K →* adjointGroup τ L :=
  ((baseChangeGL ι).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ L)
    fun x => baseChangeGL_mem_adjointGroup ι x.2

theorem coe_adjBaseChange (ι : K →+* L) (x : adjointGroup τ K) :
    (adjBaseChange ι x : ModGL τ L) = baseChangeGL ι (x : ModGL τ K) :=
  rfl

theorem adjBaseChange_injective (ι : K →+* L) : Function.Injective (adjBaseChange (τ := τ) ι) := by
  intro x y h
  have h' : (adjBaseChange ι x : ModGL τ L) = adjBaseChange ι y := congrArg Subtype.val h
  rw [coe_adjBaseChange, coe_adjBaseChange] at h'
  exact Subtype.ext (baseChangeGL_injective ι h')

end Base

section Frame

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] {p : ℕ} [Fact p.Prime]


theorem exists_weylFrame_half {G : Type} [Group G] (ι : K →+* L)
    (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Lˣ} (hζo : orderOf ζ = p)
    (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ) (c : adjointGroup τ L)
    {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hc : ((Bs.comap χ).map (adjBaseChange ι)).map (MulAut.conj c).toMonoidHom =
      TableBExc.torusPow τ L p)
    (hfix : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 → ∃ y : adjointGroup τ L,
      ∀ x ∈ Bs.comap χ, adjBaseChange ι (α x) = y * adjBaseChange ι x * y⁻¹) :
    ∃ ι' : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι' ∧ ι'.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι' (Multiplicative.ofAdd s) * g⁻¹ =
            ι' (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  classical
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  set β : adjointGroup τ K →* adjointGroup τ L := adjBaseChange ι with hβdef
  have hβ : Function.Injective β := adjBaseChange_injective ι
  set E := Bs.comap χ with hE
  set V := TableBExc.torusPow τ L p with hV
  have hF1 : ∀ x : adjointGroup τ K, x ∈ E ↔ c * β x * c⁻¹ ∈ V := by
    intro x
    constructor
    · intro hx
      rw [← hc]
      exact ⟨β x, ⟨x, hx, rfl⟩, rfl⟩
    · intro hx
      rw [← hc] at hx
      obtain ⟨_, ⟨x', hx', rfl⟩, hxx⟩ := hx
      have h1 : c * β x' * c⁻¹ = c * β x * c⁻¹ := hxx
      have h2 : β x' = β x := mul_left_cancel (mul_right_cancel h1)
      rw [← hβ h2]
      exact hx'
  have hF2 : ∀ v ∈ V, ∃ x ∈ E, c * β x * c⁻¹ = v := by
    intro v hv
    rw [← hc] at hv
    obtain ⟨_, ⟨x, hx, rfl⟩, hxv⟩ := hv
    exact ⟨x, hx, hxv⟩
  set t : (Fin τ.rank → ZMod p) → adjointGroup τ L := fun s =>
    ⟨frameDiag ζ hζ s, frameDiag_mem_adjointGroup hfull ζ hζ s⟩ with ht
  have htV : ∀ s, t s ∈ V := fun s => mem_torusPow_iff_coe.mpr (frameDiag_mem hfull ζ hζ s)
  have hfh : ∀ s, frameHom hfull ζ hζ c s = c⁻¹ * t (Multiplicative.toAdd s) * c := fun _ => rfl
  have hrng : ∀ s, frameHom hfull ζ hζ c s ∈ β.range := by
    intro s
    obtain ⟨x, -, hx⟩ := hF2 _ (htV (Multiplicative.toAdd s))
    refine ⟨x, ?_⟩
    rw [hfh, ← hx]
    group
  set Ψ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
    (MonoidHom.ofInjective hβ).symm.toMonoidHom.comp
      ((frameHom hfull ζ hζ c).codRestrict β.range hrng) with hΨ
  have hβΨ : ∀ s : Fin τ.rank → ZMod p, β (Ψ (.ofAdd s)) = c⁻¹ * t s * c := by
    intro s
    have h1 := MonoidHom.ofInjective_apply hβ (x := Ψ (.ofAdd s))
    rw [← h1, hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  have hctc : ∀ s : Fin τ.rank → ZMod p, c * β (Ψ (.ofAdd s)) * c⁻¹ = t s := by
    intro s
    rw [hβΨ]
    group
  have hΨE : ∀ s : Fin τ.rank → ZMod p, Ψ (.ofAdd s) ∈ E := fun s =>
    (hF1 _).mpr (by rw [hctc]; exact htV s)
  refine ⟨χ.comp Ψ, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : Ψ x = Ψ y := hχ hxy
    have h2 : β (Ψ (.ofAdd (Multiplicative.toAdd x))) = β (Ψ (.ofAdd (Multiplicative.toAdd y))) :=
      congrArg β h1
    rw [hβΨ, hβΨ] at h2
    have h3 : t (Multiplicative.toAdd x) = t (Multiplicative.toAdd y) :=
      mul_left_cancel (mul_right_cancel h2)
    exact Multiplicative.toAdd.injective
      (frameDiag_injective hζo hζ hdet (congrArg Subtype.val h3))
  · ext b
    constructor
    · rintro ⟨s, rfl⟩
      exact hΨE (Multiplicative.toAdd s)
    · intro hb
      obtain ⟨x, rfl⟩ := hBsR hb
      have hx : x ∈ E := hb
      have hxV := (hF1 x).mp hx
      obtain ⟨s, hs⟩ := exists_frameDiag_of_mem hζo hζ hdet (mem_torusPow_iff_coe.mp hxV)
      have hts : t s = c * β x * c⁻¹ := Subtype.ext hs
      refine ⟨.ofAdd s, ?_⟩
      show χ (Ψ (.ofAdd s)) = χ x
      congr 1
      apply hβ
      rw [hβΨ, hts]
      group
  · intro g hgN hgB hgp
    obtain ⟨α, hα⟩ := exists_inducedAut χ hχ hgN
    have hαp : α ^ p = 1 := inducedAut_pow_eq_one χ hχ hα hgp
    obtain ⟨y, hy⟩ := hfix α hαp
    have hαE : ∀ x ∈ E, α x ∈ E := by
      intro x hx
      have h1 : χ x ∈ Bs := hx
      have h2 : g * χ x * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB _).mp h1
      show χ (α x) ∈ Bs
      rw [hα]
      exact h2
    have hiter : ∀ j : ℕ, ∀ x ∈ E, (α ^ j) x ∈ E := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih => intro x hx; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hαE x hx)
    set a : adjointGroup τ L := c * y * c⁻¹ with ha
    have hconj : ∀ x ∈ E, a * (c * β x * c⁻¹) * a⁻¹ = c * β (α x) * c⁻¹ := by
      intro x hx
      rw [hy x hx, ha]
      group
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hnorm : ∀ v : adjointGroup τ L, v ∈ V ↔ a * v * a⁻¹ ∈ V := by
      intro v
      constructor
      · intro hv
        obtain ⟨x, hx, rfl⟩ := hF2 v hv
        rw [hconj x hx]
        exact (hF1 _).mp (hαE x hx)
      · intro hv
        obtain ⟨x', hx', hx'v⟩ := hF2 _ hv
        set x := (α ^ (p - 1)) x' with hxdef
        have hxE : x ∈ E := hiter _ _ hx'
        have hαx : α x = x' := by
          rw [hxdef, ← MulAut.mul_apply, mul_pow_sub_one hp0, hαp, MulAut.one_apply]
        have h1 : a * (c * β x * c⁻¹) * a⁻¹ = a * v * a⁻¹ := by
          rw [hconj x hxE, hαx, hx'v]
        have h2 : c * β x * c⁻¹ = v := mul_left_cancel (mul_right_cancel h1)
        rw [← h2]
        exact (hF1 x).mp hxE
    obtain ⟨w, hw⟩ := exists_weyl_of_normalizes hnorm
    refine ⟨w, fun s => ?_⟩
    have h1 : a * t s * a⁻¹ = t (TableBExc.torusAct τ p w s) := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (a : ModGL τ L) * frameDiag ζ hζ s * (a : ModGL τ L)⁻¹ =
        frameDiag ζ hζ (TableBExc.torusAct τ p w s)
      rw [hw _ (frameDiag_mem hfull ζ hζ s), canonicalRep_conj_frameDiag]
    have h2 : α (Ψ (.ofAdd s)) = Ψ (.ofAdd (TableBExc.torusAct τ p w s)) := by
      apply hβ
      have h3 := hconj _ (hΨE s)
      rw [hctc, h1] at h3
      rw [hβΨ, h3]
      group
    show g * χ (Ψ (.ofAdd s)) * g⁻¹ = χ (Ψ (.ofAdd (TableBExc.torusAct τ p w s)))
    rw [← hα, h2]

end Frame

end ExcFramesHalf

end CFSG.StandardType
