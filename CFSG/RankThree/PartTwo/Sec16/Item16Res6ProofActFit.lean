module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActK
public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActLin
import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement IsMulCommutative

section Restrict

variable {S X : Type*} [Group S] [Group X]

@[expose] noncomputable def restrictAct (φ : S →* MulAut X) (H : Subgroup X)
    (hH : ∀ s, H.map (φ s).toMonoidHom = H) : S →* MulAut ↥H where
  toFun s := ((φ s).subgroupMap H).trans (MulEquiv.subgroupCongr (hH s))
  map_one' := by
    ext x
    show (φ 1) (x : X) = x
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    ext x
    show (φ (a * b)) (x : X) = (φ a) ((φ b) x)
    rw [map_mul]
    rfl

theorem restrictAct_apply (φ : S →* MulAut X) (H : Subgroup X)
    (hH : ∀ s, H.map (φ s).toMonoidHom = H) (s : S) (x : ↥H) :
    ((restrictAct φ H hH s x : ↥H) : X) = φ s x :=
  rfl

theorem map_eq_of_characteristic (φ : S →* MulAut X) (H : Subgroup X) [hH : H.Characteristic]
    (s : S) : H.map (φ s).toMonoidHom = H :=
  (Subgroup.characteristic_iff_map_eq.mp hH) (φ s)

theorem fix_of_range_eq_bot (φ : S →* MulAut X) (H : Subgroup X)
    (hH : ∀ s, H.map (φ s).toMonoidHom = H) (hbot : (restrictAct φ H hH).range = ⊥) (s : S)
    {x : X} (hx : x ∈ H) : φ s x = x := by
  have h1 : restrictAct φ H hH s = 1 := by
    have h2 : restrictAct φ H hH s ∈ (restrictAct φ H hH).range := ⟨s, rfl⟩
    rw [hbot] at h2
    exact Subgroup.mem_bot.mp h2
  have h3 := congrArg (fun σ : MulAut ↥H => ((σ ⟨x, hx⟩ : ↥H) : X)) h1
  simpa [restrictAct_apply] using h3

end Restrict

theorem fix_pCore {X S : Type} [Group X] [Finite X] [Group S] [Finite S] (hS : ActHyp S)
    (φ : S →* MulAut X) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 2) (s : S) {x : X}
    (hx : x ∈ CFSG.pCore r X) : φ s x = x := by
  obtain ⟨hSp, -, hSinv⟩ := hS
  set P := CFSG.pCore r X with hPdef
  have hPinv : ∀ s, P.map (φ s).toMonoidHom = P := map_eq_of_characteristic φ P
  set ρ := restrictAct φ P hPinv with hρ
  refine fix_of_range_eq_bot φ P hPinv ?_ s hx
  have hPp : IsPGroup r ↥P := CFSG.pCore_isPGroup
  by_cases hnt : Nontrivial ↥P
  swap
  ·
    rw [not_nontrivial_iff_subsingleton] at hnt
    rw [eq_bot_iff]
    intro σ _
    rw [Subgroup.mem_bot]
    ext y
    exact congrArg Subtype.val (Subsingleton.elim _ _)
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 hPp
  have hDinv : ∀ s, D.map (ρ s).toMonoidHom = D := map_eq_of_characteristic ρ D
  set ρD := restrictAct ρ D hDinv with hρD
  have hDp : IsPGroup r ↥D := hPp.to_subgroup D
  have hexp : ∀ d : ↥D, d ^ r = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  have hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    intro a ha b _ c hc
    have h := hDcomm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
    exact (Subgroup.mem_centralizer_iff.mp h.2 c hc).symm
  have hclass : commutator ↥D ≤ Subgroup.center ↥D := Sec3.commutator_le_center_of_forall hDcl
  obtain ⟨hchar, hVcomm, -, hVelem, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have : Finite (Additive (↥D ⧸ frattini ↥D)) := inferInstanceAs (Finite (↥D ⧸ frattini ↥D))
  have : FiniteDimensional (ZMod r) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  let E : MulAut (↥D ⧸ frattini ↥D) →* Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap r
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (↥D ⧸ frattini ↥D)) (q : ↥D ⧸ frattini ↥D),
      E σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let qD := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)
  let ψ : S →* (Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)))ˣ :=
    (E.comp (qD.comp ρD)).toHomUnits
  have hψ : ∀ s, ((ψ s : (Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
      Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D))) = E (qD (ρD s)) := fun _ => rfl
  have hrankD : CFSG.pRank r ↥(fixedSubgroupOf (1 : MulAut ↥D)) ≤ 2 :=
    calc CFSG.pRank r ↥(fixedSubgroupOf (1 : MulAut ↥D))
        ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥P) :=
          SuzukiSectionProof.pRank_le_of_le hr.out.one_lt (le_top : D ≤ ⊤) _
      _ ≤ CFSG.Open.pRank r (⊤ : Subgroup X) :=
          CFSG.SectionRank.pRank_top_le_of_injective hr.out.one_lt P.subtype P.subtype_injective
      _ ≤ 2 := hrank
  have hdim : Module.finrank (ZMod r) (Additive (↥D ⧸ frattini ↥D)) ≤ 2 := by
    have h := Sec3.finrank_eigenspace_le_two_of_pRank_le_two hr2 hDp hexp hclass
      (σ := 1) (one_pow 2) hrankD 1 (fun _ => rfl)
    have htop : (1 : Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D))).eigenspace 1 = ⊤ := by
      ext v
      simp
    rw [htop, finrank_top] at h
    exact h
  have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr.out hr2
  have hψbot : ψ.range = ⊥ := by
    refine hSinv _ ψ ?_
    rintro h ⟨s₀, rfl⟩ hh g -
    have := hSp
    have hdet := det_eq_one_of_isPerfect ψ s₀
    have hsq : ((ψ s₀ : (Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
        Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D))) * (ψ s₀ : _) = 1 := by
      rw [← Units.val_mul, hh, Units.val_one]
    rcases eq_one_or_eq_neg_one h2 hdim hsq hdet with h1 | h1
    · have hu : ψ s₀ = 1 := Units.ext h1
      rw [hu, one_mul, mul_one]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, h1]
      exact (Commute.neg_one_left
        (g : Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)))).eq
  have hker : ρD.range ≤ qD.ker := by
    rintro _ ⟨s₀, rfl⟩
    rw [MonoidHom.mem_ker]
    have h1 : ψ s₀ = 1 := by
      have h3 : ψ s₀ ∈ ψ.range := ⟨s₀, rfl⟩
      rw [hψbot] at h3
      exact Subgroup.mem_bot.mp h3
    have h4 : E (qD (ρD s₀)) = 1 := by rw [← hψ, h1, Units.val_one]
    ext y
    have h5 := congrArg (fun f : Module.End (ZMod r) (Additive (↥D ⧸ frattini ↥D)) =>
      Additive.toMul (f (Additive.ofMul y))) h4
    simpa [hE] using h5
  have := hSp
  have hρDbot : ρD.range = ⊥ :=
    eq_bot_of_isPerfect_of_isPGroup (Group.IsPerfect.range ρD) (isPGroup_of_le_ker hDp hker)
  have hfixD : ρ.range ≤ fixingSubgroup (MulAut ↥P) (D : Set ↥P) := by
    rintro _ ⟨s₀, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro d hd
    have h1 := fix_of_range_eq_bot ρ D hDinv hρDbot s₀ hd
    exact h1
  exact eq_bot_of_isPerfect_of_isPGroup (Group.IsPerfect.range ρ) (hDfix.to_le hfixD)

end CFSG.RankThree.PartTwo.Sec16.Res6Act
