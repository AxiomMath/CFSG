module

public import CFSG.Quasithin.EmptyFaithful.S146zThreeC
public import CFSG.Quasithin.EmptyFaithful.S146xRk

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section CCtx

variable {G : Type} [Group G]

structure CCtx [Finite G] (T M K U₁ U₂ : Subgroup G) (s : G) : Prop where
  hKc : K ∈ cComp (mcOf T)
  hsimple : IsSimpleGroup (KBar K)
  hL3 : KbarIsL3Two K
  h168 : (pCoreOf 2 K).relIndex K = 168
  hSec : Sec8 K (quasithinOmegaOneCenter T) U₁
  hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T
  hU₁U : U₁ ≤ uOfL22 T M
  hU₂U : U₂ ≤ uOfL22 T M
  hs : s ∈ T
  hsK : s ∈ Subgroup.normalizer (K : Set G)
  hout : KbarInducesOuter K s
  hU₂ : U₂ = conjSub s U₁
  hsup : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂
  hZU₂ : quasithinOmegaOneCenter T ≤ U₂

variable [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem CCtx.ofDecomp (S : Setting146 G T M) (c19 : Conc14619 T M) (hKc : K ∈ cComp (mcOf T))
    (hL3 : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s) : CCtx T M K U₁ U₂ s := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hKc
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hKc hL3 hdec
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hout : KbarInducesOuter K s := by
    rcases hdec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
    · exact ho
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  exact
    { hKc := hKc
      hsimple := hsimple
      hL3 := hL3
      h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
      hSec := hSec
      hQ' := fun p hp w hw => S.comm_mem_Z hG (hU₁U hw) (hQK hp)
      hU₁U := hU₁U
      hU₂U := hU₂U
      hs := hdec.mem.1
      hsK := hdec.mem.2
      hout := hout
      hU₂ := hdec.conj
      hsup := hdec.sup
      hZU₂ := hdec.Z₂ }

theorem CCtx.hsZ (c : CCtx T M K U₁ U₂ s) : s ∈ Subgroup.normalizer (Zz : Set G) :=
  Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T c.hs)

theorem CCtx.conjSub_ne (c : CCtx T M K U₁ U₂ s) : conjSub s U₁ ≠ U₁ := by
  intro heq
  have hsU : s ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq heq
  have hsZ := c.hsZ
  set X : Subgroup G := K ⊔ Subgroup.zpowers s with hX
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) :=
    sup_le c.hSec.KZ (Subgroup.zpowers_le.mpr hsZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) :=
    sup_le c.hSec.KU (Subgroup.zpowers_le.mpr hsU)
  have hsX : s ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  refine c.hSec.false_of_twisted c.hsimple c.hQ' c.h168 c.hsK c.hout (secRho hXZ hXU ⟨s, hsX⟩) ?_
  intro k
  have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
  have hk' : s * (k : G) * s⁻¹ ∈ X := X.mul_mem (X.mul_mem hsX hkX) (X.inv_mem hsX)
  have e1 : c.hSec.rho k = secRho hXZ hXU ⟨k, hkX⟩ :=
    secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU rfl
  have e2 : c.hSec.rho (conjAct K ⟨s, c.hsK⟩ k) = secRho hXZ hXU ⟨s * (k : G) * s⁻¹, hk'⟩ :=
    secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU (conjAct_apply_coe' K ⟨s, c.hsK⟩ k)
  rw [e1, e2]
  have e3 : (⟨s * (k : G) * s⁻¹, hk'⟩ : ↥X) = ⟨s, hsX⟩ * ⟨k, hkX⟩ * ⟨s, hsX⟩⁻¹ := Subtype.ext rfl
  rw [e3, map_mul, map_mul, map_inv]

theorem CCtx.le_normalizer_U₂ (c : CCtx T M K U₁ U₂ s) : K ≤ Subgroup.normalizer (U₂ : Set G) := by
  rw [c.hU₂]
  exact le_normalizer_conjSub c.hsK c.hSec.KU

theorem CCtx.inf_U₂_le (c : CCtx T M K U₁ U₂ s) : U₁ ⊓ U₂ ≤ Zz := by
  have hKD : K ≤ Subgroup.normalizer ((U₁ ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨c.hSec.KU hk, c.le_normalizer_U₂ hk⟩
  rcases c.hSec.irr (U₁ ⊓ U₂) (le_inf c.hSec.le c.hZU₂) inf_le_left hKD with h | h
  · exact h.le
  · exfalso
    have hle : U₁ ≤ U₂ := inf_eq_left.mp h
    have hcard : Nat.card U₂ ≤ Nat.card U₁ := by
      rw [c.hU₂, natCard_conjSub_eq]
    have h12 : U₁ = U₂ := Subgroup.eq_of_le_of_card_ge hle hcard
    exact c.conjSub_ne (c.hU₂.symm.trans h12.symm)

theorem CCtx.inf_U₂_eq (c : CCtx T M K U₁ U₂ s) : U₁ ⊓ U₂ = Zz :=
  le_antisymm c.inf_U₂_le (le_inf c.hSec.le c.hZU₂)


theorem CCtx.irr₂ (c : CCtx T M K U₁ U₂ s) {W : Subgroup G} (hZW : Zz ≤ W) (hWU : W ≤ U₂)
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

theorem CCtx.mem_normalizer_sup (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) :
    a ∈ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  rw [← c.hsup, conjSub_sup, conjSub_commutator', conjSub_eq_of_mem_normalizer haU,
    conjSub_eq_of_mem_normalizer haK, conjSub_eq_of_mem_normalizer haZ]

theorem CCtx.sub_eq_or (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {X : Subgroup G}
    (hZX : Zz ≤ X) (hXsup : X ≤ U₁ ⊔ U₂) (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hcardX : Nat.card X = Nat.card U₁) : X = U₁ ∨ X = U₂ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hcard2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
  have hXU : X ≤ uOfL22 T M := hXsup.trans (sup_le c.hU₁U c.hU₂U)
  have hcommXU₁ : ∀ x ∈ U₁, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure (c.hU₁U hx) (hXU hy)
  have hKinf₁ : K ≤ Subgroup.normalizer ((X ⊓ U₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.hSec.KU hk⟩
  rcases c.hSec.irr (X ⊓ U₁) (le_inf hZX c.hSec.le) inf_le_right hKinf₁ with h1 | h1
  · have hKinf₂ : K ≤ Subgroup.normalizer ((X ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.le_normalizer_U₂ hk⟩
    rcases c.irr₂ (le_inf hZX c.hZU₂) inf_le_right hKinf₂ with h2 | h2
    · exfalso
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
      have hDN : X ≤ Subgroup.normalizer (Zz : Set G) :=
        hXU.trans (S.conjClosure_le_normalizer_Z hG)
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

theorem CCtx.normalizer_or (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) :
    conjSub a U₁ = U₁ ∨ conjSub a U₁ = U₂ := by
  refine c.sub_eq_or S ?_ ?_ (le_normalizer_conjSub haK c.hSec.KU) (natCard_conjSub_eq a U₁)
  · have := conjSub_mono a c.hSec.le
    rwa [conjSub_eq_of_mem_normalizer haZ] at this
  · have := conjSub_mono a (le_sup_left : U₁ ≤ U₁ ⊔ U₂)
    rwa [conjSub_eq_of_mem_normalizer (c.mem_normalizer_sup haK haU haZ)] at this

theorem CCtx.ne_U₂ (c : CCtx T M K U₁ U₂ s) : U₁ ≠ U₂ := by
  intro h
  exact c.conjSub_ne (c.hU₂.symm.trans h.symm)

theorem CCtx.conjSub_U₂ (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) (haU₁ : conjSub a U₁ = U₁) :
    conjSub a U₂ = U₂ := by
  have hZY : Zz ≤ conjSub a U₂ := by
    have := conjSub_mono a c.hZU₂
    rwa [conjSub_eq_of_mem_normalizer haZ] at this
  have hY : conjSub a U₂ ≤ U₁ ⊔ U₂ := by
    have := conjSub_mono a (le_sup_right : U₂ ≤ U₁ ⊔ U₂)
    rwa [conjSub_eq_of_mem_normalizer (c.mem_normalizer_sup haK haU haZ)] at this
  have hcard : Nat.card (conjSub a U₂) = Nat.card U₁ := by
    rw [natCard_conjSub_eq, c.hU₂, natCard_conjSub_eq]
  rcases c.sub_eq_or S hZY hY (le_normalizer_conjSub haK c.le_normalizer_U₂) hcard with h | h
  · exfalso
    have : conjSub a U₂ = conjSub a U₁ := by rw [h, haU₁]
    exact c.ne_U₂ ((conjSub_inj a).mp this).symm
  · exact h


omit [Finite G] in
theorem secRho_eq_one_of_comm {Z U X : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    {x : ↥X} (h : ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z) : secRho hXZ hXU x = 1 := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x', hx', hxw⟩ := mem_secImg.mp w.2
  have hw : w = tildeElt hU (x' : G) hx' := Subtype.ext hxw.symm
  rw [MulAut.one_apply, hw]
  exact (secRho_apply_tildeElt_iff hXZ hXU hU x (x' : G) hx').mpr (h _ hx')

omit [Finite G] in
theorem mulAut_eq_one_of_central {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (h8 : Nat.card W = 8)
    (ψ : MulAut W) (hψ : ∀ φ : MulAut W, φ * ψ = ψ * φ) : ψ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq
    (n := 3) (by rw [h8]; norm_num)
  let Φ : MulAut W ≃* MulAut (Multiplicative CFSG.Quasithin.L3.Vec) := MulAut.congr e₀
  let Ψ := Φ.trans (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 3)
  have hc : Ψ ψ ∈ Subgroup.center CFSG.QuasithinUnique.Setup.Family.GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨φ, rfl⟩ := Ψ.surjective g
    rw [← map_mul, ← map_mul, hψ φ]
  rw [CFSG.QuasithinUnique.Setup.Family.center_GL32, Subgroup.mem_bot] at hc
  exact Ψ.injective (hc.trans (map_one Ψ).symm)

theorem CCtx.centralizes_of_trivial₁ (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haZ : a ∈ Subgroup.normalizer (Zz : Set G))
    (haU₁ : a ∈ Subgroup.normalizer (U₁ : Set G)) (h : ∀ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∈ Zz) :
    ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  intro k hk
  have hcK : a * k * a⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp haK k).mp hk) (K.inv_mem hk)
  have htriv := acts_trivially_commutator haZ haU₁ (c.hSec.KZ hk) (c.hSec.KU hk) h
  exact c.hSec.centralizerMod_le c.hsimple c.hQ' ⟨hcK, c.hSec.KZ hcK, htriv⟩

theorem CCtx.trivial₁_of_centralizes (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haZ : a ∈ Subgroup.normalizer (Zz : Set G))
    (haU₁ : a ∈ Subgroup.normalizer (U₁ : Set G))
    (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : ∀ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∈ Zz := by
  classical
  set X : Subgroup G := K ⊔ Subgroup.zpowers a with hX
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) := sup_le c.hSec.KZ (Subgroup.zpowers_le.mpr haZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) := sup_le c.hSec.KU (Subgroup.zpowers_le.mpr haU₁)
  have haX : a ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hel := c.hSec.isElemAbelian_tilde
  have hψ : secRho hXZ hXU ⟨a, haX⟩ = 1 := by
    refine mulAut_eq_one_of_central (fun x y => Subtype.ext (isElemAbelian_comm hel x.2 y.2))
      (fun x => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel x.2))
      c.hSec.card_tilde _ (fun φ => ?_)
    obtain ⟨k, hk⟩ := c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 φ
    have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
    have e1 : c.hSec.rho k = secRho hXZ hXU ⟨k, hkX⟩ := secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU rfl
    rw [← hk, e1, ← map_mul, ← map_mul]
    have hoK : a * (k : G) * a⁻¹ * (k : G)⁻¹ ∈ K := K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp haK k).mp k.2) (K.inv_mem k.2)
    have hoX : a * (k : G) * a⁻¹ * (k : G)⁻¹ ∈ X := Subgroup.mem_sup_left hoK
    have ho1 : secRho hXZ hXU ⟨a * (k : G) * a⁻¹ * (k : G)⁻¹, hoX⟩ = 1 :=
      secRho_eq_one_of_comm hXZ hXU (c.hSec.norm.trans le_rfl)
        (x := ⟨a * (k : G) * a⁻¹ * (k : G)⁻¹, hoX⟩) (fun u hu => c.hQ' _ (h k k.2) u hu)
    have e2 : (⟨a, haX⟩ : ↥X) * ⟨k, hkX⟩ =
        ⟨a * (k : G) * a⁻¹ * (k : G)⁻¹, hoX⟩ * (⟨k, hkX⟩ * ⟨a, haX⟩) := by
      apply Subtype.ext
      show a * (k : G) = a * (k : G) * a⁻¹ * (k : G)⁻¹ * ((k : G) * a)
      group
    rw [e2]
    have e3 : secRho hXZ hXU (⟨a * (k : G) * a⁻¹ * (k : G)⁻¹, hoX⟩ * (⟨k, hkX⟩ * ⟨a, haX⟩)) =
        secRho hXZ hXU (⟨k, hkX⟩ * ⟨a, haX⟩) := by rw [map_mul, ho1, one_mul]
    exact e3.symm
  intro w hw
  exact commutator_mem_of_secRho_eq_one hXZ hXU c.hSec.norm hψ hw


theorem CCtx.trivial_both (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) (haU₁ : conjSub a U₁ = U₁)
    (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    (∀ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∈ Zz) ∧ (∀ w ∈ U₂, a * w * a⁻¹ * w⁻¹ ∈ Zz) := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have hsU : s ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hsH
  have h1 := c.trivial₁_of_centralizes haK haZ (mem_normalizer_of_conjSub_eq haU₁) h
  refine ⟨h1, fun w hw => ?_⟩
  set a' := s⁻¹ * a * s with ha'
  have ha'K : a' ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ c.hsK) haK) c.hsK
  have ha'Z : a' ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ c.hsZ) haZ) c.hsZ
  have haU₂ := c.conjSub_U₂ S haK haU haZ haU₁
  have ha'U₁ : conjSub a' U₁ = U₁ := by
    rw [ha', mul_assoc, conjSub_mul, conjSub_mul, ← c.hU₂, haU₂, c.hU₂, ← conjSub_mul,
      inv_mul_cancel, conjSub_one]
  have ha'cent : ∀ k ∈ K, a' * k * a'⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro k hk
    have hk' : s * k * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp c.hsK k).mp hk
    have h2 := h _ hk'
    have e : a' * k * a'⁻¹ * k⁻¹ =
        s⁻¹ * (a * (s * k * s⁻¹) * a⁻¹ * (s * k * s⁻¹)⁻¹) * s := by rw [ha']; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (normalizer_le_normalizer_pCoreOf 2 K c.hsK)) _).mp h2
    simpa using this
  have h3 := c.trivial₁_of_centralizes ha'K ha'Z (mem_normalizer_of_conjSub_eq ha'U₁) ha'cent
  have hw' : s⁻¹ * w * s ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ hw)
  have h4 := h3 _ hw'
  have e : a * w * a⁻¹ * w⁻¹ = s * (a' * (s⁻¹ * w * s) * a'⁻¹ * (s⁻¹ * w * s)⁻¹) * s⁻¹ := by
    rw [ha']; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp c.hsZ _).mp h4

theorem CCtx.false_of_swap (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haZ : a ∈ Subgroup.normalizer (Zz : Set G))
    (hsw : conjSub a U₁ = U₂) (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : False := by
  classical
  have hsZ := c.hsZ
  set z := a⁻¹ * s with hz
  have hzU₁ : conjSub z U₁ = U₁ := by
    rw [hz, conjSub_mul, ← c.hU₂, ← hsw, conjSub_conjSub_inv]
  have hzU : z ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq hzU₁
  have hzZ : z ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ haZ) hsZ
  set X : Subgroup G := K ⊔ Subgroup.zpowers z with hX
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) :=
    sup_le c.hSec.KZ (Subgroup.zpowers_le.mpr hzZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) :=
    sup_le c.hSec.KU (Subgroup.zpowers_le.mpr hzU)
  have hzX : z ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine c.hSec.false_of_twisted c.hsimple c.hQ' c.h168 c.hsK c.hout (secRho hXZ hXU ⟨z, hzX⟩) ?_
  intro k
  have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
  set k' := s * (k : G) * s⁻¹ with hk'
  have hk'K : k' ∈ K := (Subgroup.mem_normalizer_iff.mp c.hsK k).mp k.2
  have hk'X : k' ∈ X := Subgroup.mem_sup_left hk'K
  have e1 : c.hSec.rho k = secRho hXZ hXU ⟨k, hkX⟩ :=
    secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU rfl
  have e2 : c.hSec.rho (conjAct K ⟨s, c.hsK⟩ k) = secRho hXZ hXU ⟨k', hk'X⟩ :=
    secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU (conjAct_apply_coe' K ⟨s, c.hsK⟩ k)
  rw [e1, e2]
  have hoO : a⁻¹ * k' * a * k'⁻¹ ∈ pCoreOf 2 K := by
    have h1 := h k' hk'K
    have e : a⁻¹ * k' * a * k'⁻¹ = a⁻¹ * (a * k' * a⁻¹ * k'⁻¹)⁻¹ * a := by group
    rw [e]
    have haO := normalizer_le_normalizer_pCoreOf 2 K haK
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haO) _).mp
      ((pCoreOf 2 K).inv_mem h1)
    simpa using this
  have hoK : a⁻¹ * k' * a * k'⁻¹ ∈ K := pCoreOf_le 2 K hoO
  have hoX : a⁻¹ * k' * a * k'⁻¹ ∈ X := Subgroup.mem_sup_left hoK
  have ho1 : secRho hXZ hXU ⟨a⁻¹ * k' * a * k'⁻¹, hoX⟩ = 1 :=
    secRho_eq_one_of_comm hXZ hXU c.hSec.norm (x := ⟨a⁻¹ * k' * a * k'⁻¹, hoX⟩)
      (fun u hu => c.hQ' _ hoO u hu)
  have e3 : (⟨z, hzX⟩ * ⟨k, hkX⟩ * ⟨z, hzX⟩⁻¹ : ↥X) =
      ⟨a⁻¹ * k' * a * k'⁻¹, hoX⟩ * ⟨k', hk'X⟩ := by
    apply Subtype.ext
    show z * (k : G) * z⁻¹ = a⁻¹ * k' * a * k'⁻¹ * k'
    rw [hz, hk']
    group
  have e4 : secRho hXZ hXU (⟨z, hzX⟩ * ⟨k, hkX⟩ * ⟨z, hzX⟩⁻¹) =
      secRho hXZ hXU ⟨z, hzX⟩ * secRho hXZ hXU ⟨k, hkX⟩ * (secRho hXZ hXU ⟨z, hzX⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← e4, e3, map_mul, ho1, one_mul]

theorem CCtx.trivial_of_centralizes (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G))
    (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    ∀ y ∈ U₁ ⊔ U₂, a * y * a⁻¹ * y⁻¹ ∈ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have haEU : ∀ x ∈ uOfL22 T M, a * x * a⁻¹ ∈ uOfL22 T M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haU x).mp hx
  rcases c.normalizer_or S haK haU haZ with hin | hsw
  · obtain ⟨h1, h2⟩ := c.trivial_both S haK haU haZ hin h
    intro y hy
    have hN₁₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
      le_normalizer_of_forall_commute fun x hx y hy =>
        S.comm_of_mem_conjClosure (c.hU₁U hx) (c.hU₂U hy)
    have hy' : y ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₁₂] at hy'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hy'
    rw [comm_mul_of_abelian hcommU haEU (c.hU₁U hy₁) (c.hU₂U hy₂)]
    exact Subgroup.mul_mem _ (h1 y₁ hy₁) (h2 y₂ hy₂)
  · exact (c.false_of_swap haK haZ hsw h).elim


theorem CCtx.rank_le_two (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {X : Subgroup G}
    (hXH : X ≤ mcOf T) (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXab : IsElemAbelian 2 X) :
    mIdx X (centralizerMod Zz X (U₁ ⊔ U₂)) ≤ 2 := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hXU : X ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun e he =>
    le_normalizer_conjClosure _ _ (hXH he)
  let Φ : ↥X →* MulAut (KBar K) := (kbarActHom K).comp (Subgroup.inclusion hXK)
  have hΦmk : ∀ (x : ↥X) (k : ↥K), Φ x (QuotientGroup.mk k) =
      QuotientGroup.mk (conjAutOn K (x : G) (hXK x.2) k) := fun x k =>
    kbarActHom_mk K (Subgroup.inclusion hXK x) k
  have hcommX : ∀ x y : ↥X, x * y = y * x := fun x y =>
    Subtype.ext (isElemAbelian_comm hXab x.2 y.2)
  have hsqX : ∀ x : ↥X, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using isElemAbelian_pow_eq_one hXab x.2)
  have hEA : CFSG.IsElementaryAbelian 2 ↥(Φ.range) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, x, rfl⟩ := a
      obtain ⟨b, y, rfl⟩ := b
      apply Subtype.ext
      show Φ x * Φ y = Φ y * Φ x
      rw [← map_mul, ← map_mul, hcommX]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
      obtain ⟨a, x, rfl⟩ := a
      apply Subtype.ext
      show (Φ x) ^ 2 = 1
      rw [← map_pow, hsqX, map_one]
  have hcard4 : Nat.card Φ.range ≤ 2 ^ 2 := card_le_four_of_kbarIsL3Two c.hL3 Φ.range
  have hker : Φ.ker ≤ (centralizerMod Zz X (U₁ ⊔ U₂)).subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : Φ x = 1 := hx
    have hcomm : ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      have h1 := congrArg (fun α : MulAut (KBar K) => α (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) hx1
      simp only [hΦmk, MulAut.one_apply] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      have h3 : k⁻¹ * ((x : G) * k * (x : G)⁻¹) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h2
      have h4 : k * (k⁻¹ * ((x : G) * k * (x : G)⁻¹)) * k⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h3
      have e : (x : G) * k * (x : G)⁻¹ * k⁻¹ = k * (k⁻¹ * ((x : G) * k * (x : G)⁻¹)) * k⁻¹ := by
        group
      rw [e]
      exact h4
    exact ⟨x.2, hXZ x.2, c.trivial_of_centralizes S (hXK x.2) (hXU x.2) (hXZ x.2) hcomm⟩
  have hdvd : (centralizerMod Zz X (U₁ ⊔ U₂)).relIndex X ∣ Nat.card Φ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  have hpos : 0 < Nat.card Φ.range := Nat.card_pos
  have hle4 : (centralizerMod Zz X (U₁ ⊔ U₂)).relIndex X ≤ 4 :=
    (Nat.le_of_dvd hpos hdvd).trans (by simpa using hcard4)
  unfold mIdx
  have hne : (centralizerMod Zz X (U₁ ⊔ U₂)).relIndex X ≠ 0 :=
    (Nat.pos_of_dvd_of_pos hdvd hpos).ne'
  generalize (centralizerMod Zz X (U₁ ⊔ U₂)).relIndex X = n at hle4 hne
  have h1 : padicValNat 2 n ≤ Nat.log 2 n := padicValNat_le_nat_log n
  have h2 : Nat.log 2 n < 3 := Nat.log_lt_of_lt_pow hne (by omega : n < 2 ^ 3)
  omega

theorem CCtx.not_swap (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) (ha2 : a * a = 1) (hsw : conjSub a U₁ = U₂) :
    8 ≤ (centralizerMod Zz (U₁ ⊔ U₂) (Subgroup.zpowers a)).relIndex (U₁ ⊔ U₂) := by
  classical
  set C := centralizerMod Zz (U₁ ⊔ U₂) (Subgroup.zpowers a) with hC
  have hCU₁ : C ⊓ U₁ ≤ Zz := by
    rintro x ⟨hxC, hx₁⟩
    have h1 := ((mem_centralizerMod_zpowers_iff ha2).mp hxC).2.2
    have hax : a * x * a⁻¹ ∈ U₂ := by rw [← hsw]; exact mul_mem_conjSub hx₁
    have hax₁ : a * x * a⁻¹ ∈ U₁ := by
      have e : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
      rw [e]; exact U₁.mul_mem (c.hSec.le h1) hx₁
    have hZ : a * x * a⁻¹ ∈ Zz := c.inf_U₂_eq ▸ ⟨hax₁, hax⟩
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haZ) _).mp hZ
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h3
  have h1 : (C ⊓ U₁).relIndex U₁ ≤ C.relIndex (U₁ ⊔ U₂) :=
    relIndex_inf_le_relIndex le_sup_left (centralizerMod_le_left _ _ _) (fun x hx y hy =>
      S.comm_of_mem_conjClosure (sup_le c.hU₁U c.hU₂U (centralizerMod_le_left _ _ _ hx)) (c.hU₁U hy))
  have h2 : Subgroup.relIndex Zz U₁ ∣ (C ⊓ U₁).relIndex U₁ :=
    Subgroup.relIndex_dvd_of_le_left U₁ hCU₁
  have hpos : 0 < (C ⊓ U₁).relIndex U₁ := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have := Nat.le_of_dvd hpos h2
  rw [c.hSec.card] at this
  omega



theorem CCtx.exists_k (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {x : G}
    (haK : x ∈ Subgroup.normalizer (K : Set G)) (haU : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : x ∈ Subgroup.normalizer (Zz : Set G)) (hx₁ : conjSub x U₁ = U₁) :
    ∃ k ∈ K, ∀ y ∈ U₁ ⊔ U₂, ((k : G)⁻¹ * x) * y * ((k : G)⁻¹ * x)⁻¹ * y⁻¹ ∈ Zz := by
  classical
  have hxU₁ : x ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq hx₁
  set X : Subgroup G := K ⊔ Subgroup.zpowers x with hX
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) := sup_le c.hSec.KZ (Subgroup.zpowers_le.mpr haZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) := sup_le c.hSec.KU (Subgroup.zpowers_le.mpr hxU₁)
  have hxX : x ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 (secRho hXZ hXU ⟨x, hxX⟩)
  have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
  have e1 : c.hSec.rho k = secRho hXZ hXU ⟨k, hkX⟩ :=
    secRho_congr c.hSec.KZ c.hSec.KU hXZ hXU rfl
  have hkx : secRho hXZ hXU ⟨k, hkX⟩ = secRho hXZ hXU ⟨x, hxX⟩ := by rw [← e1, hk]
  set a := (k : G)⁻¹ * x with ha
  have haX : a ∈ X := X.mul_mem (X.inv_mem hkX) hxX
  have haK' : a ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer k.2)) haK
  have haU' : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_normalizer_conjClosure _ _
      ((le_of_mem_cComp c.hKc) k.2))) haU
  have haZ' : a ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (c.hSec.KZ k.2)) haZ
  have hρa : secRho hXZ hXU ⟨a, haX⟩ = 1 := by
    have : (⟨a, haX⟩ : ↥X) = ⟨k, hkX⟩⁻¹ * ⟨x, hxX⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, hkx, inv_mul_cancel]
  have htriv : ∀ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∈ Zz := fun w hw =>
    commutator_mem_of_secRho_eq_one hXZ hXU c.hSec.norm hρa hw
  have hcent := c.centralizes_of_trivial₁ haK' haZ' (hXU haX) htriv
  exact ⟨(k : G), k.2, c.trivial_of_centralizes S haK' haU' haZ' hcent⟩


theorem CCtx.exists_sigma (c : CCtx T M K U₁ U₂ s) :
    ∃ σ : MulAut (MulAut ↥(tildeOf Zz U₁)),
      (∀ k : ↥K, σ (c.hSec.rho k) = c.hSec.rho (conjAct K ⟨s⁻¹, Subgroup.inv_mem _ c.hsK⟩ k)) ∧
      ∀ g : MulAut ↥(tildeOf Zz U₁), σ ≠ MulAut.conj g := by
  classical
  have hsurj : Function.Surjective c.hSec.rho := fun ψ =>
    c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 ψ
  set ρ := c.hSec.rho with hρ
  set ν : MulAut ↥K := conjAct K ⟨s⁻¹, Subgroup.inv_mem _ c.hsK⟩ with hν
  have hνcoe : ∀ k : ↥K, ((ν k : ↥K) : G) = s⁻¹ * (k : G) * s := fun k => by
    have := conjAct_apply_coe' K ⟨s⁻¹, Subgroup.inv_mem _ c.hsK⟩ k
    simpa using this
  have hker : ∀ k : ↥K, ρ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    constructor
    · intro h
      exact c.hSec.centralizerMod_le c.hsimple c.hQ' (c.hSec.mem_centralizerMod_of_rho_eq_one h)
    · intro h
      exact secRho_eq_one_of_comm c.hSec.KZ c.hSec.KU c.hSec.norm (x := k)
        (fun u hu => c.hQ' _ h u hu)
  have hpc : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x : G, x ∈ pCoreOf 2 K ↔ g * x * g⁻¹ ∈ pCoreOf 2 K :=
    fun g hg x => Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K hg) x
  have hνker : ∀ k : ↥K, ρ k = 1 ↔ ρ (ν k) = 1 := by
    intro k
    rw [hker, hker, hνcoe]
    have := hpc s⁻¹ (Subgroup.inv_mem _ c.hsK) (k : G)
    simpa using this
  have hmap : ρ.ker.map ν.toMonoidHom = ρ.ker := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩
      exact (hνker k').mp hk'
    · intro hk
      refine ⟨ν.symm k, ?_, by simp⟩
      have := (hνker (ν.symm k)).mpr (by simpa using hk)
      exact this
  let ε := QuotientGroup.quotientKerEquivOfSurjective ρ hsurj
  let ν' := QuotientGroup.congr ρ.ker ρ.ker ν hmap
  have hεmk : ∀ k : ↥K, ε (QuotientGroup.mk k) = ρ k := fun k => rfl
  have hσ : ∀ k : ↥K, (ε.symm.trans (ν'.trans ε)) (ρ k) = ρ (ν k) := by
    intro k
    show ε (ν' (ε.symm (ρ k))) = ρ (ν k)
    have h1 : ε.symm (ρ k) = QuotientGroup.mk k := by
      rw [MulEquiv.symm_apply_eq]; exact (hεmk k).symm
    have h2 : ν' (QuotientGroup.mk k) = QuotientGroup.mk (ν k) :=
      QuotientGroup.congr_mk ρ.ker ρ.ker ν hmap k
    rw [h1, h2, hεmk]
  refine ⟨ε.symm.trans (ν'.trans ε), hσ, ?_⟩
  intro g hg
  obtain ⟨k₀, hk₀⟩ := hsurj g
  have hrel : ∀ k : ↥K, ρ (ν k) = ρ k₀ * ρ k * (ρ k₀)⁻¹ := by
    intro k
    rw [← hσ k, hg, MulAut.conj_apply, hk₀]
  have hcent : ∀ x ∈ K, (s * (k₀ : G)) * x * (s * (k₀ : G))⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
    intro x hx
    have h1 : ρ (ν ⟨x, hx⟩ * (k₀ * ⟨x, hx⟩ * k₀⁻¹)⁻¹) = 1 := by
      rw [map_mul, map_inv, hrel]
      simp only [map_mul, map_inv]
      group
    have h2 := (hker _).mp h1
    have h3 : ((ν ⟨x, hx⟩ * (k₀ * ⟨x, hx⟩ * k₀⁻¹)⁻¹ : ↥K) : G) =
        (s⁻¹ * x * s) * ((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹ := by
      show ((ν ⟨x, hx⟩ : ↥K) : G) * ((k₀ * ⟨x, hx⟩ * k₀⁻¹ : ↥K) : G)⁻¹ = _
      rw [hνcoe]
      rfl
    rw [h3] at h2
    have e : (s * (k₀ : G)) * x * (s * (k₀ : G))⁻¹ * x⁻¹ =
        s * ((s⁻¹ * x * s) * ((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹)⁻¹ * s⁻¹ := by group
    rw [e]
    have := (hpc s c.hsK _).mp ((pCoreOf 2 K).inv_mem h2)
    exact this
  obtain ⟨x, hx, hxn⟩ := c.hout ((k₀ : G)⁻¹) (K.inv_mem k₀.2)
  apply hxn
  have := hcent x hx
  simpa [commutatorElement_def] using this


omit [Finite G] in
theorem secRho_eq_of_comm {Z U X : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    {g h : ↥X}
    (H : ∀ u ∈ U, ((h⁻¹ * g : ↥X) : G) * u * ((h⁻¹ * g : ↥X) : G)⁻¹ * u⁻¹ ∈ Z) :
    secRho hXZ hXU g = secRho hXZ hXU h := by
  have h1 := secRho_eq_one_of_comm hXZ hXU hU (x := h⁻¹ * g) H
  rw [map_mul, map_inv] at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem CCtx.conjSub_s_inner (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) (haU₁ : conjSub a U₁ = U₁) :
    conjSub (s⁻¹ * a * s) U₁ = U₁ := by
  have haU₂ := c.conjSub_U₂ S haK haU haZ haU₁
  rw [mul_assoc, conjSub_mul, conjSub_mul, ← c.hU₂, haU₂, c.hU₂, ← conjSub_mul, inv_mul_cancel,
    conjSub_one]

theorem CCtx.comm_conj_s (c : CCtx T M K U₁ U₂ s) {t : G}
    (ht : ∀ u ∈ U₂, t * u * t⁻¹ * u⁻¹ ∈ Zz) : ∀ u ∈ U₁, (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹ * u⁻¹ ∈ Zz := by
  intro u hu
  have hu₂ : s * u * s⁻¹ ∈ U₂ := by rw [c.hU₂]; exact mul_mem_conjSub hu
  have h1 := ht _ hu₂
  have e : (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹ * u⁻¹ =
      s⁻¹ * (t * (s * u * s⁻¹) * t⁻¹ * (s * u * s⁻¹)⁻¹) * s := by group
  rw [e]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ c.hsZ) _).mp h1
  simpa using this

end CCtx

end CFSG.Quasithin.ThreeC
