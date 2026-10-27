module

public import CFSG.Quasithin.EmptyFaithful.S146E4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G]

structure FCtx [Finite G] (T M K U₁ U₂ : Subgroup G) (s u : G) : Prop where
  hKc : K ∈ cComp (mcOf T)
  hKeq : K = perfectCore (mcOf T)
  hKn : mcOf T ≤ Subgroup.normalizer (K : Set G)
  hHKT : mcOf T = K ⊔ T
  hsimple : IsSimpleGroup (KBar K)
  hL3 : KbarIsL3Two K
  h168 : (pCoreOf 2 K).relIndex K = 168
  hSec : Sec8 K (quasithinOmegaOneCenter T) U₁
  hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T)
  hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T
  huU : u ∈ U₁
  huZ : u ∉ quasithinOmegaOneCenter T
  hU₁U : U₁ ≤ uOfL22 T M
  hU₂U : U₂ ≤ uOfL22 T M
  hs : s ∈ T
  hsK : s ∈ Subgroup.normalizer (K : Set G)
  hout : KbarInducesOuter K s
  hU₂ : U₂ = conjSub s U₁
  hsup : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂
  hZU₂ : quasithinOmegaOneCenter T ≤ U₂
  hTU₁ : T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u
  hinv : IsInvU T M (mcOf T) u
  hc23 : Conc14623 T M

variable [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

theorem FCtx.ofBData (S : Setting146 G T M) (hd : BData146 T M K U₁ U₂ s u) :
    FCtx T M K U₁ U₂ s u := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKc : K ∈ cComp (mcOf T) := hd.hK
  obtain ⟨hinv, hL3, hKeq, -⟩ := hd.c24
  have hsimple : IsSimpleGroup (KBar K) := (hd.c19 (mcOf T) hG).2 K hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTH : T ≤ mcOf T := hG.1.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact hd.c23.1.2
  obtain ⟨hSec, hU₁U, hU₂U⟩ := S.sec8_of_decomp hKc hL3 hd.dec
  obtain ⟨huU, hunc, hTU₁⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
    rcases hd.choice with ⟨-, huU, hunc, hT⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
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
    rcases hd.dec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
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
      hs := hd.dec.mem.1
      hsK := hd.dec.mem.2
      hout := hout
      hU₂ := hd.dec.conj
      hsup := hd.dec.sup
      hZU₂ := hd.dec.Z₂
      hTU₁ := hTU₁
      hinv := hinv
      hc23 := hd.c23 }

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.mem_pCoreOf_of_secRho_eq_one (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    {X : Subgroup G} (hXH : X ≤ mcOf T) (hXZ : X ≤ Subgroup.normalizer (Zz : Set G))
    (hXU : X ≤ Subgroup.normalizer (U₁ : Set G)) {y : ↥X} (hy : secRho hXZ hXU y = 1) :
    (y : G) ∈ pCoreOf 2 (mcOf T) := by
  have hyH : (y : G) ∈ mcOf T := hXH y.2
  refine mem_pCoreOf_of_commutator_mem c.hKc c.hsimple c.hKn S.hyp.sylow.1 c.hHKT hyH
    fun k hk => ?_
  have htriv := acts_trivially_commutator (hXZ y.2) (hXU y.2) (c.hSec.KZ hk) (c.hSec.KU hk)
    (fun w hw => commutator_mem_of_secRho_eq_one hXZ hXU c.hSec.norm hy hw)
  have hcK : (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ K := by
    have h3 := (Subgroup.mem_normalizer_iff.mp (c.hKn hyH) k).mp hk
    exact K.mul_mem h3 (K.inv_mem hk)
  have hcen : (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ centralizerMod Zz K U₁ :=
    ⟨hcK, c.hSec.KZ hcK, htriv⟩
  exact c.hQK (c.hSec.centralizerMod_le c.hsimple c.hQ' hcen)

theorem FCtx.exists_mul (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {h : G}
    (hh : h ∈ mcOf T) (hU : h ∈ Subgroup.normalizer (U₁ : Set G)) :
    ∃ k ∈ K, ∃ q ∈ pCoreOf 2 (mcOf T), h = k * q := by
  have hNZ : Subgroup.normalizer (Zz : Set G) = mcOf T := S.normalizer_Z
  have hhZ : h ∈ Subgroup.normalizer (Zz : Set G) := by rw [hNZ]; exact hh
  set X : Subgroup G := K ⊔ Subgroup.zpowers h with hX
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) :=
    sup_le c.hSec.KZ (Subgroup.zpowers_le.mpr hhZ)
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) :=
    sup_le c.hSec.KU (Subgroup.zpowers_le.mpr hU)
  have hXH : X ≤ mcOf T := sup_le hKH (Subgroup.zpowers_le.mpr hh)
  have hhX : h ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  obtain ⟨k, hk⟩ := c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 (secRho hXZ hXU ⟨h, hhX⟩)
  have hkX : (k : G) ∈ X := Subgroup.mem_sup_left k.2
  have hkr : secRho hXZ hXU ⟨k, hkX⟩ = secRho hXZ hXU ⟨h, hhX⟩ := by
    rw [← hk]
    exact secRho_congr hXZ hXU c.hSec.KZ c.hSec.KU rfl
  have hq : secRho hXZ hXU (⟨k, hkX⟩⁻¹ * ⟨h, hhX⟩) = 1 := by
    rw [map_mul, map_inv, hkr, inv_mul_cancel]
  have hqQ := c.mem_pCoreOf_of_secRho_eq_one S hXH hXZ hXU hq
  refine ⟨k, k.2, (k : G)⁻¹ * h, hqQ, ?_⟩
  group

omit [Finite G] in
theorem le_normalizer_sup_of_le {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_sup, conjSub_eq_of_mem_normalizer (hA hx), conjSub_eq_of_mem_normalizer (hB hx)]

theorem FCtx.mem_normalizer_of_mem (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    {A : Subgroup G} (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hZA : Zz ≤ A)
    (hAU : A ≤ uOfL22 T M) {h : G} (hh : h ∈ mcOf T)
    (hU : h ∈ Subgroup.normalizer (U₁ : Set G)) : h ∈ Subgroup.normalizer (A : Set G) := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have key : ∀ g ∈ mcOf T, g ∈ Subgroup.normalizer (U₁ : Set G) → ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
    intro g hg hgU y hy
    obtain ⟨k, hk, q, hq, rfl⟩ := c.exists_mul S hg hgU
    have h1 : q * y * q⁻¹ ∈ A := by
      have hc : q * y * q⁻¹ * y⁻¹ ∈ Zz := S.comm_mem_Z hG (hAU hy) hq
      have e : q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact A.mul_mem (hZA hc) hy
    have h2 := (Subgroup.mem_normalizer_iff.mp (hKA hk) _).mp h1
    have e : k * q * y * (k * q)⁻¹ = k * (q * y * q⁻¹) * k⁻¹ := by group
    rw [e]
    exact h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key h hh hU x hx, fun hx => ?_⟩
  have h3 := key h⁻¹ ((mcOf T).inv_mem hh) (Subgroup.inv_mem _ hU) _ hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at h3

omit [Finite G] in
theorem natCard_conjSub_eq (g : G) (A : Subgroup G) : Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem FCtx.conjSub_ne (c : FCtx T M K U₁ U₂ s u) : conjSub s U₁ ≠ U₁ := by
  intro heq
  have hsU : s ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq heq
  have hsZ : s ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T c.hs)
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

theorem FCtx.le_normalizer_U₂ (c : FCtx T M K U₁ U₂ s u) :
    K ≤ Subgroup.normalizer (U₂ : Set G) := by
  rw [c.hU₂]
  exact le_normalizer_conjSub c.hsK c.hSec.KU

theorem FCtx.inf_U₂_le (c : FCtx T M K U₁ U₂ s u) : U₁ ⊓ U₂ ≤ Zz := by
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

omit [Finite G] in
@[expose] def cuOf (T M : Subgroup G) : Subgroup G :=
  centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)

omit [Finite G] in
@[expose] def uxOf (T M U₂ : Subgroup G) : Subgroup G := U₂ ⊔ cuOf T M

omit [Finite G] in
theorem cuOf_le (T M : Subgroup G) : cuOf T M ≤ uOfL22 T M := centralizerMod_le_left _ _ _

omit [Finite G] in
theorem mem_cuOf {T M : Subgroup G} {y : G} :
    y ∈ cuOf T M ↔ y ∈ uOfL22 T M ∧ y ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ∧
      ∀ h ∈ mcOf T, y * h * y⁻¹ * h⁻¹ ∈ quasithinOmegaOneCenter T := Iff.rfl

theorem FCtx.le_normalizer_cuOf (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    K ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) := by
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hV₁ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := by
    intro x hx
    rw [S.normalizer_Z]
    exact hx
  exact fun k hk => le_normalizer_centralizerMod (H := mcOf T) hV₁
    (le_normalizer_conjClosure _ _) Subgroup.le_normalizer (hKH hk)

theorem FCtx.le_normalizer_uxOf (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    K ≤ Subgroup.normalizer ((uxOf T M U₂ : Subgroup G) : Set G) :=
  le_normalizer_sup_of_le c.le_normalizer_U₂ (c.le_normalizer_cuOf S)

theorem Setting146.comm_of_mem_conjClosure (S : Setting146 G T M) {x y : G}
    (hx : x ∈ uOfL22 T M) (hy : y ∈ uOfL22 T M) : x * y = y * x :=
  isElemAbelian_comm (S.lemma_14_5_15_two S.isHTM_mcOf) hx hy

theorem FCtx.sup_inf_cuOf_le (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    (U₁ ⊔ U₂) ⊓ cuOf T M ≤ Zz := by
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hsZ : s ∈ Subgroup.normalizer (Zz : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T c.hs)
  intro y ⟨hy1, hy2⟩
  refine c.hSec.mem_of_fixed_sup c.hsK hsZ c.hU₂ c.hZU₂ c.le_normalizer_U₂ ?_ hy1 ?_
  · intro x hx y hy
    exact S.comm_of_mem_conjClosure (sup_le c.hU₁U c.hU₂U hx) (sup_le c.hU₁U c.hU₂U hy)
  · intro k hk
    exact (mem_cuOf.mp hy2).2.2 k (hKH hk)

theorem FCtx.inf_uxOf_le (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    U₁ ⊓ uxOf T M U₂ ≤ Zz := by
  intro y ⟨hy1, hy2⟩
  have hcomm : ∀ a ∈ U₂, ∀ b ∈ cuOf T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure (c.hU₂U ha) (cuOf_le T M hb)
  have hN : U₂ ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute hcomm
  have hy' : y ∈ ((U₂ ⊔ cuOf T M : Subgroup G) : Set G) := hy2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
  obtain ⟨y₂, hy₂, d, hd, rfl⟩ := hy'
  have hdZ : d ∈ Zz := by
    have hd1 : d ∈ U₁ ⊔ U₂ := by
      have e : d = y₂⁻¹ * (y₂ * d) := by group
      rw [e]
      exact (U₁ ⊔ U₂).mul_mem ((U₁ ⊔ U₂).inv_mem (Subgroup.mem_sup_right hy₂))
        (Subgroup.mem_sup_left hy1)
    exact c.sup_inf_cuOf_le S ⟨hd1, hd⟩
  have hyU₂ : y₂ * d ∈ U₂ := U₂.mul_mem hy₂ (c.hZU₂ hdZ)
  exact c.inf_U₂_le ⟨hy1, hyU₂⟩

end Ctx

end CFSG.Quasithin
