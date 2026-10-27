module

public import CFSG.Quasithin.EmptyFaithful.S146zGen
public import CFSG.Quasithin.EmptyFaithful.S146E6
public import CFSG.Quasithin.EmptyFaithful.S146E3
public import CFSG.Quasithin.EmptyFaithful.S146E7
public import CFSG.Quasithin.EmptyFaithful.S146F22

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Ctx

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.ofCtx24 (S : Setting146 G T M) (hctx : Ctx24 T M K U₁ U₂ s u)
    (hKeq : K = perfectCore (mcOf T)) (hL3 : KbarIsL3Two K) (hinv : IsInvU T M (mcOf T) u) :
    FCtx T M K U₁ U₂ s u := by
  obtain ⟨c19, -, c23, hKc, -, -, hdec, hchoice⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTH : T ≤ mcOf T := hG.1.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact c23.1.2
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hKc hL3 hdec
  obtain ⟨huU, hunc, hTU₁⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
    rcases hchoice with ⟨-, huU, hunc, hT⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
    · exact ⟨huU, hunc, hT⟩
    · exact absurd (hKn (hTH ht)) htn
  have huZ : u ∉ quasithinOmegaOneCenter T := by
    intro hu
    apply hunc
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hu) le_rfl).trans
      (S145.commutator_le_of_le_normalizer hSec.KZ)
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hout : KbarInducesOuter K s := by
    rcases hdec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
    · exact ho
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  exact
    { hKc := hKc
      hKeq := hKeq
      hKn := hKn
      hHKT := hHKT
      hsimple := hsimple
      hL3 := hL3
      h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
      hSec := hSec
      hQK := hQK
      hQ' := fun p hp w hw => S.comm_mem_Z hG (hU₁U hw) (hQK hp)
      huU := huU
      huZ := huZ
      hU₁U := hU₁U
      hU₂U := hU₂U
      hs := hdec.mem.1
      hsK := hdec.mem.2
      hout := hout
      hU₂ := hdec.conj
      hsup := hdec.sup
      hZU₂ := hdec.Z₂
      hTU₁ := hTU₁
      hinv := hinv
      hc23 := c23 }

end Ctx

section Swap

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.hsZ (c : FCtx T M K U₁ U₂ s u) : s ∈ Subgroup.normalizer (Zz : Set G) :=
  Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T c.hs)

theorem FCtx.inf_U₂_eq (c : FCtx T M K U₁ U₂ s u) : U₁ ⊓ U₂ = Zz :=
  le_antisymm c.inf_U₂_le (le_inf c.hSec.le c.hZU₂)

theorem FCtx.irr₂ (c : FCtx T M K U₁ U₂ s u) {W : Subgroup G} (hZW : Zz ≤ W) (hWU : W ≤ U₂)
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) : W = Zz ∨ W = U₂ := by
  set W' : Subgroup G := conjSub s⁻¹ W with hW'
  have hsZ := c.hsZ
  have hZW' : Zz ≤ W' := by
    intro z hz
    rw [hW', mem_conjSub]
    have : s * z * s⁻¹ ∈ Zz := (Subgroup.mem_normalizer_iff.mp hsZ z).mp hz
    have e : (s⁻¹)⁻¹ * z * s⁻¹ = s * z * s⁻¹ := by group
    rw [e]
    exact hZW this
  have hW'U : W' ≤ U₁ := by
    intro x hx
    have h1 : (s⁻¹)⁻¹ * x * s⁻¹ ∈ W := mem_conjSub.mp hx
    have h2 : (s⁻¹)⁻¹ * x * s⁻¹ ∈ conjSub s U₁ := c.hU₂ ▸ hWU h1
    have h3 : s⁻¹ * ((s⁻¹)⁻¹ * x * s⁻¹) * s ∈ U₁ := mem_conjSub.mp h2
    have e : s⁻¹ * ((s⁻¹)⁻¹ * x * s⁻¹) * s = x := by group
    rwa [e] at h3
  have hKW' : K ≤ Subgroup.normalizer (W' : Set G) := by
    intro k hk
    apply mem_normalizer_of_conjSub_eq
    have hk' : s⁻¹ * k * s ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ c.hsK) k).mp hk
      simpa using this
    have e : k * s⁻¹ = s⁻¹ * (s * k * s⁻¹) := by group
    rw [hW', ← conjSub_mul, e, conjSub_mul]
    have hsk : s * k * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp c.hsK k).mp hk
    rw [conjSub_eq_of_mem_normalizer (hKW hsk)]
  have hWW : W = conjSub s W' := by
    rw [hW', ← conjSub_mul, mul_inv_cancel, conjSub_one]
  rcases c.hSec.irr W' hZW' hW'U hKW' with h | h
  · left
    rw [hWW, h]
    exact conjSub_eq_of_mem_normalizer hsZ
  · right
    rw [hWW, h]
    exact c.hU₂.symm


omit [Finite G] in
theorem conjSub_commutator' (a : G) (A B : Subgroup G) :
    conjSub a ⁅A, B⁆ = ⁅conjSub a A, conjSub a B⁆ := by
  unfold conjSub
  exact Subgroup.map_commutator _ _ _

theorem FCtx.mem_normalizer_sup (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (ha : a ∈ mcOf T) : a ∈ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact ha
  have haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ ha
  have haK : a ∈ Subgroup.normalizer (K : Set G) := c.hKn ha
  apply mem_normalizer_of_conjSub_eq
  rw [← c.hsup, conjSub_sup, conjSub_commutator', conjSub_eq_of_mem_normalizer haU,
    conjSub_eq_of_mem_normalizer haK, conjSub_eq_of_mem_normalizer haZ]

theorem FCtx.normalizer_or (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (ha : a ∈ mcOf T) : conjSub a U₁ = U₁ ∨ conjSub a U₁ = U₂ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  set X := conjSub a U₁ with hX
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact ha
  have haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ ha
  have hZX : Zz ≤ X := by
    have := conjSub_mono a c.hSec.le
    rwa [conjSub_eq_of_mem_normalizer haZ] at this
  have hXU : X ≤ uOfL22 T M := by
    have := conjSub_mono a c.hU₁U
    rwa [conjSub_eq_of_mem_normalizer haU] at this
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := le_normalizer_conjSub (c.hKn ha) c.hSec.KU
  have hcardX : Nat.card X = Nat.card U₁ := natCard_conjSub_eq a U₁
  have hcard2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
  have hXsup : X ≤ U₁ ⊔ U₂ := by
    have := conjSub_mono a (le_sup_left : U₁ ≤ U₁ ⊔ U₂)
    rwa [conjSub_eq_of_mem_normalizer (FCtx.mem_normalizer_sup S c ha)] at this
  have hcommXU₁ : ∀ x ∈ U₁, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure (c.hU₁U hx) (hXU hy)
  have hKinf₁ : K ≤ Subgroup.normalizer ((X ⊓ U₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.hSec.KU hk⟩
  rcases c.hSec.irr (X ⊓ U₁) (le_inf hZX c.hSec.le) inf_le_right hKinf₁ with h1 | h1
  ·
    have hKinf₂ : K ≤ Subgroup.normalizer ((X ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.le_normalizer_U₂ hk⟩
    rcases c.irr₂ (le_inf hZX c.hZU₂) inf_le_right hKinf₂ with h2 | h2
    ·
      exfalso
      have hZinf := c.inf_U₂_eq
      obtain ⟨hc1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ X hcommXU₁
      rw [inf_comm, h1] at hc1
      obtain ⟨hc2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
        (fun x hx y hy => S.comm_of_mem_conjClosure (c.hU₁U hx) (c.hU₂U hy))
      rw [hZinf] at hc2
      have hle : U₁ ⊔ X ≤ U₁ ⊔ U₂ := sup_le le_sup_left hXsup
      have hZpos : 0 < Nat.card Zz := Nat.card_pos
      have hcardsup : Nat.card ↥(U₁ ⊔ U₂) ≤ Nat.card ↥(U₁ ⊔ X) := by
        have e1 : Nat.card ↥(U₁ ⊔ X) * Nat.card Zz = Nat.card U₁ * Nat.card X := hc1
        have e2 : Nat.card ↥(U₁ ⊔ U₂) * Nat.card Zz = Nat.card U₁ * Nat.card U₂ := hc2
        have : Nat.card ↥(U₁ ⊔ U₂) * Nat.card Zz ≤ Nat.card ↥(U₁ ⊔ X) * Nat.card Zz := by
          rw [e1, e2, hcard2, hcardX]
        exact Nat.le_of_mul_le_mul_right this hZpos
      have hEq : U₁ ⊔ X = U₁ ⊔ U₂ := Subgroup.eq_of_le_of_card_ge hle hcardsup
      have hU₂le : conjSub s U₁ ≤ U₁ ⊔ X := by
        rw [← c.hU₂, hEq]
        exact le_sup_right
      have hUsup : U₁ ⊔ X ≤ uOfL22 T M := sup_le c.hU₁U hXU
      have hDN : X ≤ Subgroup.normalizer (Zz : Set G) := by
        refine hXU.trans ?_
        exact S.conjClosure_le_normalizer_Z hG
      refine c.hSec.false_of_decomp c.hsimple c.hQ' c.h168 c.hsK c.hsZ c.hout hDN hKX
        (c.hU₂ ▸ c.hZU₂) ?_ ?_ hU₂le ?_ ?_
      · rw [inf_comm]; exact h1.le
      · rw [← c.hU₂, inf_comm]; exact h2.le
      · intro x hx y hy
        have e : x * y * x⁻¹ * y⁻¹ = 1 := by
          rw [S.comm_of_mem_conjClosure (hUsup hx) (hUsup hy)]; group
        rw [e]; exact Subgroup.one_mem _
      · intro x hx
        rw [isElemAbelian_pow_eq_one hUab (hUsup hx)]
        exact Subgroup.one_mem _
    · right
      have hle : U₂ ≤ X := inf_eq_right.mp h2
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardX, hcard2])).symm
  · left
    have hle : U₁ ≤ X := inf_eq_right.mp h1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardX])).symm


end Swap

section Trans

open CFSG.Quasithin.L3 CFSG.SectionRank.Ccomm

theorem exists_mulAut_apply_eq {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 8)
    {v w : W} (hv : v ≠ 1) (hw : w ≠ 1) : ∃ σ : MulAut W, σ v = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq (n := 3)
    (by rw [hcard]; norm_num)
  set v' : Vec := Multiplicative.toAdd (e₀ v) with hv'
  set w' : Vec := Multiplicative.toAdd (e₀ w) with hw'
  have hv0 : v' ≠ 0 := by
    intro h
    apply hv
    apply e₀.injective
    rw [map_one]
    exact toAdd_eq_zero.mp h
  have hw0 : w' ≠ 0 := by
    intro h
    apply hw
    apply e₀.injective
    rw [map_one]
    exact toAdd_eq_zero.mp h
  obtain ⟨γ, hγ⟩ := act_trans v' w' hv0 hw0
  let τ : MulAut (Multiplicative Vec) :=
    (mulAutEquivGL (p := 2) 3).symm (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ)
  have hτ : ∀ x : Multiplicative Vec,
      Multiplicative.toAdd (τ x) = act γ (Multiplicative.toAdd x) := by
    intro x
    have h := mulAutEquivGL_mulVec (p := 2) 3 τ (Multiplicative.toAdd x)
    rw [ofAdd_toAdd] at h
    have h2 : mulAutEquivGL (p := 2) 3 τ = CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ :=
      (mulAutEquivGL (p := 2) 3).apply_symm_apply _
    rw [h2, L3Stab.slEquivGL_coe] at h
    exact h.symm
  refine ⟨(e₀.trans τ).trans e₀.symm, ?_⟩
  show e₀.symm (τ (e₀ v)) = w
  have h1 : τ (e₀ v) = e₀ w := by
    apply Multiplicative.toAdd.injective
    rw [hτ]
    exact hγ
  rw [h1]
  exact e₀.symm_apply_apply w

end Trans

section TildeElt

variable {G : Type} [Group G] {Z U X : Subgroup G}

theorem secRho_tildeElt (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) (y : G) (hy : y ∈ U) (hy' : (x : G) * y * (x : G)⁻¹ ∈ U) :
    secRho hXZ hXU x (tildeElt hU y hy) = tildeElt hU ((x : G) * y * (x : G)⁻¹) hy' := by
  apply Subtype.ext
  simp only [secRho_coe, tildeElt]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tildeElt_eq_iff (hU : U ≤ Subgroup.normalizer (Z : Set G)) {y y' : G} (hy : y ∈ U)
    (hy' : y' ∈ U) : tildeElt hU y hy = tildeElt hU y' hy' ↔ y⁻¹ * y' ∈ Z := by
  constructor
  · intro h
    have h1 := congrArg (fun w : ↥(tildeOf Z U) => (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z)) h
    exact secMk_eq_secMk_iff.mp (by simpa [tildeElt] using h1)
  · intro h
    apply Subtype.ext
    simp only [tildeElt]
    exact secMk_eq_secMk_iff.mpr h

end TildeElt

section Inner

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.nontriv₁ (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {h : G}
    (hh : h ∈ mcOf T) (hU : conjSub h U₁ = U₁) (hQ : h ∉ pCoreOf 2 (mcOf T)) :
    ∃ x ∈ U₁, h * x * h⁻¹ * x⁻¹ ∉ Zz := by
  by_contra hcon
  push Not at hcon
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨k, hk, q, hq, rfl⟩ := c.exists_mul S hh (mem_normalizer_of_conjSub_eq hU)
  apply hQ
  have hkc : k ∈ centralizerMod Zz K U₁ := by
    refine ⟨hk, c.hSec.KZ hk, fun x hx => ?_⟩
    have hx' : x ∈ uOfL22 T M := c.hU₁U hx
    have hz₁ : q⁻¹ * x * q * x⁻¹ ∈ Zz := by
      have := S.comm_mem_Z hG hx' (Subgroup.inv_mem _ hq)
      simpa [commutatorElement_def] using this
    have hy₁ : q⁻¹ * x * q ∈ U₁ := by
      have e : q⁻¹ * x * q = (q⁻¹ * x * q * x⁻¹) * x := by group
      rw [e]
      exact U₁.mul_mem (c.hSec.le hz₁) hx
    have h1 := hcon (q⁻¹ * x * q) hy₁
    have e2 : k * x * k⁻¹ * x⁻¹ =
        ((k * q) * (q⁻¹ * x * q) * (k * q)⁻¹ * (q⁻¹ * x * q)⁻¹) * (q⁻¹ * x * q * x⁻¹) := by
      group
    rw [e2]
    exact Subgroup.mul_mem _ h1 hz₁
  have hkQ := c.hQK (c.hSec.centralizerMod_le c.hsimple c.hQ' hkc)
  exact (pCoreOf 2 (mcOf T)).mul_mem hkQ hq

theorem FCtx.conjSub_U₂ (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (ha : a ∈ mcOf T) (haU : conjSub a U₁ = U₁) : conjSub a U₂ = U₂ := by
  apply conjSub_eq_of_mem_normalizer
  exact c.mem_normalizer_of_mem S c.le_normalizer_U₂ c.hZU₂ c.hU₂U ha (mem_normalizer_of_conjSub_eq haU)

theorem FCtx.nontriv₂ (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {h : G}
    (hh : h ∈ mcOf T) (hU : conjSub h U₁ = U₁) (hQ : h ∉ pCoreOf 2 (mcOf T)) :
    ∃ x ∈ U₂, h * x * h⁻¹ * x⁻¹ ∉ Zz := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have hh₂ := c.conjSub_U₂ S hh hU
  set h' := s⁻¹ * h * s with hh'
  have hh'H : h' ∈ mcOf T := (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem hsH) hh) hsH
  have hh'Q : h' ∉ pCoreOf 2 (mcOf T) := by
    intro hq
    apply hQ
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hsH) h').mp hq
    have e : s * h' * s⁻¹ = h := by rw [hh']; group
    rwa [e] at this
  have hh'U : conjSub h' U₁ = U₁ := by
    have e1 : conjSub h' U₁ = conjSub s⁻¹ (conjSub h (conjSub s U₁)) := by
      rw [hh', mul_assoc, conjSub_mul, conjSub_mul]
    rw [e1, ← c.hU₂, hh₂, c.hU₂, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  obtain ⟨x', hx', hx'Z⟩ := c.nontriv₁ S hh'H hh'U hh'Q
  refine ⟨s * x' * s⁻¹, ?_, fun hZ => hx'Z ?_⟩
  · rw [c.hU₂]; exact mul_mem_conjSub hx'
  · have hsZ := c.hsZ
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsZ) _).mp hZ
    have e : h' * x' * h'⁻¹ * x'⁻¹ = s⁻¹ * (h * (s * x' * s⁻¹) * h⁻¹ * (s * x' * s⁻¹)⁻¹) * s := by
      rw [hh']; group
    rw [e]
    simpa using h1


theorem FCtx.exists_decomp3 (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ uOfL22 T M) : ∃ y ∈ U₁, ∃ r₂ ∈ U₂, ∃ d ∈ cuOf T M, x = y * (r₂ * d) := by
  obtain ⟨y, hy, r, hr, rfl⟩ := c.exists_decomp S hx
  have hcomm : ∀ a ∈ U₂, ∀ b ∈ cuOf T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure (c.hU₂U ha) (cuOf_le T M hb)
  have hN : U₂ ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute hcomm
  have hr' : r ∈ ((U₂ ⊔ cuOf T M : Subgroup G) : Set G) := hr
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hr'
  obtain ⟨r₂, hr₂, d, hd, rfl⟩ := Set.mem_mul.mp hr'
  exact ⟨y, hy, r₂, hr₂, d, hd, rfl⟩

theorem FCtx.inner_struct (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (haH : a ∈ mcOf T) (ha2 : a * a = 1) (haU : conjSub a U₁ = U₁)
    (haQ : a ∉ pCoreOf 2 (mcOf T)) :
    (∃ x₁ ∈ U₁, a * x₁ * a⁻¹ * x₁⁻¹ ∉ Zz) ∧
    ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, ∀ x ∈ uOfL22 T M,
      a * x * a⁻¹ * x⁻¹ ∈ (Zz ⊔ Subgroup.zpowers u₁) ⊔ Subgroup.zpowers u₂ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  refine ⟨c.nontriv₁ S haH haU haQ, ?_⟩
  have haU₂ := c.conjSub_U₂ S haH haU
  have haN₁ : a ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq haU
  have haN₂ : a ∈ Subgroup.normalizer (U₂ : Set G) := mem_normalizer_of_conjSub_eq haU₂
  have haNU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ haH
  have haZ : ∀ z ∈ Zz, a * z * a⁻¹ = z := fun z hz => by
    have h1 := S146T.comm_Z haH hz
    calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [h1]
      _ = z := by group
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have hsqU : ∀ x ∈ uOfL22 T M, x * x = 1 := fun x hx => by
    have := isElemAbelian_pow_eq_one hUab hx
    simpa [pow_two] using this
  have haEU : ∀ x ∈ uOfL22 T M, a * x * a⁻¹ ∈ uOfL22 T M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haNU x).mp hx
  have hcard₂ : Subgroup.relIndex Zz U₂ = 8 := by
    have h1 := Subgroup.relIndex_mul_card Zz U₁
    have h2 := Subgroup.relIndex_mul_card Zz U₂
    rw [inf_eq_left.mpr c.hSec.le] at h1
    rw [inf_eq_left.mpr c.hZU₂] at h2
    have hc2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
    have hZpos : 0 < Nat.card Zz := Nat.card_pos
    rw [c.hSec.card] at h1
    rw [hc2, ← h1] at h2
    exact Nat.eq_of_mul_eq_mul_right hZpos h2
  obtain ⟨u₁, hu₁, hst₁⟩ := exists_u_of_relIndex_eight (E := U₁) (Z := Zz) (a := a)
    (fun x hx y hy => hcommU x (c.hU₁U hx) y (c.hU₁U hy)) (fun x hx => hsqU x (c.hU₁U hx))
    c.hSec.le (fun x hx => (Subgroup.mem_normalizer_iff.mp haN₁ x).mp hx) ha2 haZ c.hSec.card
  obtain ⟨u₂, hu₂, hst₂⟩ := exists_u_of_relIndex_eight (E := U₂) (Z := Zz) (a := a)
    (fun x hx y hy => hcommU x (c.hU₂U hx) y (c.hU₂U hy)) (fun x hx => hsqU x (c.hU₂U hx))
    c.hZU₂ (fun x hx => (Subgroup.mem_normalizer_iff.mp haN₂ x).mp hx) ha2 haZ hcard₂
  refine ⟨u₁, hu₁, u₂, hu₂, fun x hx => ?_⟩
  set N : Subgroup G := (Zz ⊔ Subgroup.zpowers u₁) ⊔ Subgroup.zpowers u₂ with hN
  have hZN : Zz ≤ N := le_sup_left.trans le_sup_left
  have hu₁N : u₁ ∈ N := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₁))
  have hu₂N : u₂ ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂)
  obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := c.exists_decomp3 S hx
  have hyU := c.hU₁U hy
  have hr₂U := c.hU₂U hr₂
  have hdU := cuOf_le T M hd
  have hr₂dU : r₂ * d ∈ uOfL22 T M := (uOfL22 T M).mul_mem hr₂U hdU
  rw [comm_mul_of_abelian hcommU haEU hyU hr₂dU, comm_mul_of_abelian hcommU haEU hr₂U hdU]
  have f1 : a * y * a⁻¹ * y⁻¹ ∈ N := by
    rcases hst₁ y hy with h | h
    · exact hZN h
    · have e : a * y * a⁻¹ * y⁻¹ = ((a * y * a⁻¹ * y⁻¹) * u₁⁻¹) * u₁ := by group
      rw [e]; exact N.mul_mem (hZN h) hu₁N
  have f2 : a * r₂ * a⁻¹ * r₂⁻¹ ∈ N := by
    rcases hst₂ r₂ hr₂ with h | h
    · exact hZN h
    · have e : a * r₂ * a⁻¹ * r₂⁻¹ = ((a * r₂ * a⁻¹ * r₂⁻¹) * u₂⁻¹) * u₂ := by group
      rw [e]; exact N.mul_mem (hZN h) hu₂N
  have f3 : a * d * a⁻¹ * d⁻¹ ∈ N := by
    apply hZN
    have h1 := (mem_cuOf.mp hd).2.2 a haH
    have e : a * d * a⁻¹ * d⁻¹ = (d * a * d⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ h1
  exact N.mul_mem f1 (N.mul_mem f2 f3)


theorem FCtx.index_gt_two (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (haH : a ∈ mcOf T) (ha2 : a * a = 1) (haU : conjSub a U₁ = U₁)
    (haQ : a ∉ pCoreOf 2 (mcOf T)) :
    2 < (centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a)).relIndex (uOfL22 T M) := by
  classical
  by_contra hcon
  push Not at hcon
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have haNU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ haH
  have haEU : ∀ x ∈ uOfL22 T M, a * x * a⁻¹ ∈ uOfL22 T M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haNU x).mp hx
  have haU₂ := c.conjSub_U₂ S haH haU
  have haN₁ : a ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq haU
  have haN₂ : a ∈ Subgroup.normalizer (U₂ : Set G) := mem_normalizer_of_conjSub_eq haU₂
  set C := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) with hC
  have hpos : 0 < C.relIndex (uOfL22 T M) := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have hdvd : C.relIndex (uOfL22 T M) ∣ 2 := by
    interval_cases hn : C.relIndex (uOfL22 T M)
    · exact one_dvd _
    · exact dvd_refl _
  obtain ⟨b, hbU, hb⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd
  obtain ⟨x₁, hx₁, hx₁Z⟩ := c.nontriv₁ S haH haU haQ
  obtain ⟨x₂, hx₂, hx₂Z⟩ := c.nontriv₂ S haH haU haQ
  have hnC : ∀ x, a * x * a⁻¹ * x⁻¹ ∉ Zz → x ∉ C := fun x hx hxC =>
    hx ((mem_centralizerMod_zpowers_iff ha2).mp hxC).2.2
  have h1 : x₁ * b ∈ C := (hb x₁ (c.hU₁U hx₁)).resolve_right (hnC x₁ hx₁Z)
  have h2 : x₂ * b ∈ C := (hb x₂ (c.hU₂U hx₂)).resolve_right (hnC x₂ hx₂Z)
  have h3 : x₁ * x₂⁻¹ ∈ C := by
    have := C.mul_mem h1 (C.inv_mem h2)
    have e : x₁ * b * (x₂ * b)⁻¹ = x₁ * x₂⁻¹ := by group
    rwa [e] at this
  have h4 := ((mem_centralizerMod_zpowers_iff ha2).mp h3).2.2
  rw [comm_mul_of_abelian hcommU haEU (c.hU₁U hx₁) ((uOfL22 T M).inv_mem (c.hU₂U hx₂))] at h4
  have hq : x₂ * (a * x₂⁻¹ * a⁻¹) = (a * x₂⁻¹ * a⁻¹) * x₂ :=
    hcommU _ (c.hU₂U hx₂) _ (haEU _ ((uOfL22 T M).inv_mem (c.hU₂U hx₂)))
  have e5 : a * x₂⁻¹ * a⁻¹ * (x₂⁻¹)⁻¹ = (a * x₂ * a⁻¹ * x₂⁻¹)⁻¹ := by
    calc a * x₂⁻¹ * a⁻¹ * (x₂⁻¹)⁻¹ = (a * x₂⁻¹ * a⁻¹) * x₂ := by group
      _ = x₂ * (a * x₂⁻¹ * a⁻¹) := hq.symm
      _ = (a * x₂ * a⁻¹ * x₂⁻¹)⁻¹ := by group
  rw [e5] at h4
  have hw₁ : a * x₁ * a⁻¹ * x₁⁻¹ ∈ U₁ :=
    U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₁ x₁).mp hx₁) (U₁.inv_mem hx₁)
  have hw₂ : a * x₂ * a⁻¹ * x₂⁻¹ ∈ U₂ :=
    U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp haN₂ x₂).mp hx₂) (U₂.inv_mem hx₂)
  have hw₁₂ : a * x₁ * a⁻¹ * x₁⁻¹ ∈ U₂ := by
    have e : a * x₁ * a⁻¹ * x₁⁻¹ = ((a * x₁ * a⁻¹ * x₁⁻¹) * (a * x₂ * a⁻¹ * x₂⁻¹)⁻¹) *
        (a * x₂ * a⁻¹ * x₂⁻¹) := by group
    rw [e]; exact U₂.mul_mem (c.hZU₂ h4) hw₂
  exact hx₁Z (c.inf_U₂_eq ▸ ⟨hw₁, hw₁₂⟩)

theorem FCtx.not_swap (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {a : G}
    (haH : a ∈ mcOf T) (ha2 : a * a = 1) (hswap : conjSub a U₁ = U₂) :
    8 ≤ (centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a)).relIndex (uOfL22 T M) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  set C := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) with hC
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact haH
  have hCU₁ : C ⊓ U₁ ≤ Zz := by
    rintro x ⟨hxC, hx₁⟩
    have h1 := ((mem_centralizerMod_zpowers_iff ha2).mp hxC).2.2
    have hax : a * x * a⁻¹ ∈ U₂ := by rw [← hswap]; exact mul_mem_conjSub hx₁
    have hax₁ : a * x * a⁻¹ ∈ U₁ := by
      have e : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
      rw [e]; exact U₁.mul_mem (c.hSec.le h1) hx₁
    have hZ : a * x * a⁻¹ ∈ Zz := c.inf_U₂_eq ▸ ⟨hax₁, hax⟩
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haZ) _).mp hZ
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h3
  have h1 : (C ⊓ U₁).relIndex U₁ ≤ C.relIndex (uOfL22 T M) :=
    relIndex_inf_le_relIndex c.hU₁U (centralizerMod_le_left _ _ _) (fun x hx y hy =>
      S.comm_of_mem_conjClosure (centralizerMod_le_left _ _ _ hx) (c.hU₁U hy))
  have h2 : Subgroup.relIndex Zz U₁ ∣ (C ⊓ U₁).relIndex U₁ :=
    Subgroup.relIndex_dvd_of_le_left U₁ hCU₁
  have hpos : 0 < (C ⊓ U₁).relIndex U₁ := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have := Nat.le_of_dvd hpos h2
  rw [c.hSec.card] at this
  omega

end Inner

section QMove

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem conj_mem_centralizer' {Q : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hx : x ∈ Subgroup.centralizer (Q : Set G)) : g * x * g⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.mp hx _ h1
  calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [h2]
    _ = (g * x * g⁻¹) * q := by group

theorem FCtx.inf_centralizer_Q (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    (U₁ ⊔ U₂) ⊓ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ≤ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have hQN : mcOf T ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) := le_normalizer_pCoreOf 2 (mcOf T)
  set Q := pCoreOf 2 (mcOf T) with hQ
  set C := Subgroup.centralizer (Q : Set G) with hC
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk =>
    normalizer_le_normalizer_centralizer' (hQN (hKH hk))
  have hZC : Zz ≤ C := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact S146T.comm_Z (pCoreOf_le 2 (mcOf T) hq) hz
  have hnot : ¬ U₁ ≤ C := fun h => c.hinv.not_central (h c.huU)
  have hE₁ : U₁ ⊓ C ≤ Zz := c.hSec.inf_le_of_not_le hKC hZC hnot
  have hE₂ : U₂ ⊓ C ≤ Zz := by
    rintro x ⟨hx2, hxC⟩
    have hx1 : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ hx2)
    have hxC' : s⁻¹ * x * s ∈ C := by
      have h1 := conj_mem_centralizer' (Subgroup.inv_mem _ (hQN hsH)) hxC
      simpa using h1
    have h1 : s⁻¹ * x * s ∈ Zz := hE₁ ⟨hx1, hxC'⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp c.hsZ _).mp h1
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at h2
  set E := (U₁ ⊔ U₂) ⊓ C with hE
  have hEsup : E ≤ U₁ ⊔ U₂ := inf_le_left
  have hEU : E ≤ uOfL22 T M := hEsup.trans (sup_le c.hU₁U c.hU₂U)
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := fun k hk => by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, hKC hk⟩
    exact le_normalizer_sup_of_le (fun k hk => c.hSec.KU hk) c.le_normalizer_U₂ hk
  have hE₁' : U₁ ⊓ E ≤ Zz := fun x hx => hE₁ ⟨hx.1, hx.2.2⟩
  have hE₂' : conjSub s U₁ ⊓ E ≤ Zz := fun x hx => hE₂ ⟨c.hU₂ ▸ hx.1, hx.2.2⟩
  set X := U₁ ⊔ E with hX
  have hXU : X ≤ uOfL22 T M := sup_le c.hU₁U hEU
  have hZX : Zz ≤ X := c.hSec.le.trans le_sup_left
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := fun k hk =>
    le_normalizer_sup_of_le (fun k hk => c.hSec.KU hk) hKE hk
  have hKXU₂ : K ≤ Subgroup.normalizer ((X ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.le_normalizer_U₂ hk⟩
  rcases c.irr₂ (le_inf hZX c.hZU₂) inf_le_right hKXU₂ with h | h
  ·
    have hcommXU₂ : ∀ x ∈ X, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy =>
      S.comm_of_mem_conjClosure (hXU hx) (c.hU₂U hy)
    obtain ⟨hc1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X U₂ hcommXU₂
    rw [h] at hc1
    obtain ⟨hc2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
      (fun x hx y hy => S.comm_of_mem_conjClosure (c.hU₁U hx) (c.hU₂U hy))
    rw [c.inf_U₂_eq] at hc2
    have hle : X ⊔ U₂ ≤ U₁ ⊔ U₂ := sup_le (sup_le le_sup_left hEsup) le_sup_right
    have hcard := Subgroup.card_le_of_le hle
    have hZpos : 0 < Nat.card Zz := Nat.card_pos
    have hU₂pos : 0 < Nat.card U₂ := Nat.card_pos
    have hcard2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
    have hXle : Nat.card X ≤ Nat.card U₁ := by
      have h3 : Nat.card X * Nat.card U₂ ≤ Nat.card U₁ * Nat.card U₂ := by
        have : Nat.card ↥(X ⊔ U₂) * Nat.card Zz ≤ Nat.card ↥(U₁ ⊔ U₂) * Nat.card Zz :=
          Nat.mul_le_mul_right _ hcard
        rw [hc1, hc2] at this
        exact this
      exact Nat.le_of_mul_le_mul_right h3 hU₂pos
    have hXeq : U₁ = X := Subgroup.eq_of_le_of_card_ge le_sup_left hXle
    intro x hx
    apply hE₁
    refine ⟨?_, hx.2⟩
    rw [hXeq]
    exact Subgroup.mem_sup_right hx
  ·
    exfalso
    have hle : U₂ ≤ X := inf_eq_right.mp h
    have hUsup : U₁ ⊔ E ≤ uOfL22 T M := hXU
    have hDN : E ≤ Subgroup.normalizer (Zz : Set G) := hEU.trans (S.conjClosure_le_normalizer_Z hG)
    refine c.hSec.false_of_decomp c.hsimple c.hQ' c.h168 c.hsK c.hsZ c.hout hDN hKE
      (c.hU₂ ▸ c.hZU₂) hE₁' hE₂' (c.hU₂ ▸ hle) ?_ ?_
    · intro x hx y hy
      have e : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [S.comm_of_mem_conjClosure (hUsup hx) (hUsup hy)]; group
      rw [e]; exact Subgroup.one_mem _
    · intro x hx
      rw [isElemAbelian_pow_eq_one hUab (hUsup hx)]
      exact Subgroup.one_mem _

theorem FCtx.exists_q_move (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ U₁ ⊔ U₂) (hxZ : x ∉ Zz) :
    ∃ q ∈ pCoreOf 2 (mcOf T), ∃ z' ∈ Zz, z' ≠ 1 ∧ q * x * q⁻¹ = x * z' := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hxC : x ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := fun h =>
    hxZ (c.inf_centralizer_Q S ⟨hx, h⟩)
  rw [Subgroup.mem_centralizer_iff] at hxC
  push Not at hxC
  obtain ⟨q, hq, hqx⟩ := hxC
  have hxU : x ∈ uOfL22 T M := sup_le c.hU₁U c.hU₂U hx
  have hcomm := S.comm_mem_Z hG hxU hq
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  refine ⟨q, hq, ⁅q, x⁆, hcomm, ?_, ?_⟩
  · intro h1
    apply hqx
    rw [commutatorElement_def] at h1
    calc q * x = (q * x * q⁻¹ * x⁻¹) * (x * q) := by group
      _ = x * q := by rw [h1, one_mul]
  · have h1 : x * ⁅q, x⁆ = ⁅q, x⁆ * x := S.comm_of_mem_conjClosure hxU (hZU hcomm)
    calc q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
      _ = ⁅q, x⁆ * x := by rw [commutatorElement_def]
      _ = x * ⁅q, x⁆ := h1.symm

theorem FCtx.pure_conj (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ U₁ ∨ x ∈ U₂) (hxZ : x ∉ Zz) : ∃ h ∈ mcOf T, h * u * h⁻¹ = x := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have key : ∀ x₁ ∈ U₁, x₁ ∉ Zz → ∃ h ∈ mcOf T, h * u * h⁻¹ = x₁ := by
    intro x₁ hx₁ hx₁Z
    have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := c.hSec.norm
    have hel := c.hSec.isElemAbelian_tilde
    have hcommW : ∀ a b : ↥(tildeOf Zz U₁), a * b = b * a :=
      fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2)
    have hsqW : ∀ a : ↥(tildeOf Zz U₁), a ^ 2 = 1 := fun a =>
      Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
    have hne1 : ∀ y (hy : y ∈ U₁), y ∉ Zz → tildeElt hUZ y hy ≠ 1 := by
      intro y hy hyZ h
      apply hyZ
      have h1 := congrArg
        (fun w : ↥(tildeOf Zz U₁) => (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
      exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
    obtain ⟨ψ, hψ⟩ := exists_mulAut_apply_eq hcommW hsqW c.hSec.card_tilde
      (hne1 u c.huU c.huZ) (hne1 x₁ hx₁ hx₁Z)
    obtain ⟨k, hk⟩ := c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 ψ
    have hkU : (k : G) * u * (k : G)⁻¹ ∈ U₁ :=
      (Subgroup.mem_normalizer_iff.mp (c.hSec.KU k.2) u).mp c.huU
    have h1 : secRho c.hSec.KZ c.hSec.KU k (tildeElt hUZ u c.huU) = tildeElt hUZ x₁ hx₁ := by
      have hrho : c.hSec.rho k = secRho c.hSec.KZ c.hSec.KU k := rfl
      rw [← hrho, hk]
      exact hψ
    rw [secRho_tildeElt c.hSec.KZ c.hSec.KU hUZ k u c.huU hkU] at h1
    have hz'' : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ ∈ Zz := (tildeElt_eq_iff hUZ hkU hx₁).mp h1
    have hx₀Z : (k : G) * u * (k : G)⁻¹ ∉ Zz := by
      intro hZ
      apply c.huZ
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (c.hSec.KZ k.2)) _).mp hZ
      have e : (k : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) * (k : G)⁻¹⁻¹ = u := by group
      rwa [e] at this
    have hkH : (k : G) ∈ mcOf T := hKH k.2
    by_cases hz1 : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ = 1
    · refine ⟨k, hkH, ?_⟩
      have : x₁ = (k : G) * u * (k : G)⁻¹ := by
        have e : x₁ = ((k : G) * u * (k : G)⁻¹) * (((k : G) * u * (k : G)⁻¹)⁻¹ * x₁) := by group
        rw [e, hz1, mul_one]
      exact this.symm
    · obtain ⟨q, hq, z', hz', hz'1, hqz⟩ := c.exists_q_move S
        (Subgroup.mem_sup_left hkU) hx₀Z
      have hzz : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ = z' :=
        S.Z_eq_of_iff hz'' hz' (by simp only [hz1, hz'1])
      refine ⟨q * k, (mcOf T).mul_mem (pCoreOf_le 2 (mcOf T) hq) hkH, ?_⟩
      have e : x₁ = ((k : G) * u * (k : G)⁻¹) * z' := by
        rw [← hzz]; group
      calc (q * k) * u * (q * k)⁻¹ = q * ((k : G) * u * (k : G)⁻¹) * q⁻¹ := by group
        _ = ((k : G) * u * (k : G)⁻¹) * z' := hqz
        _ = x₁ := e.symm
  rcases hx with hx | hx
  · exact key x hx hxZ
  · have hx' : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ hx)
    have hx'Z : s⁻¹ * x * s ∉ Zz := by
      intro hZ
      apply hxZ
      have := (Subgroup.mem_normalizer_iff.mp c.hsZ _).mp hZ
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at this
    obtain ⟨h', hh', hh'u⟩ := key _ hx' hx'Z
    refine ⟨s * h', (mcOf T).mul_mem hsH hh', ?_⟩
    calc (s * h') * u * (s * h')⁻¹ = s * (h' * u * h'⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * x * s) * s⁻¹ := by rw [hh'u]
      _ = x := by group

end QMove

end CFSG.Quasithin
