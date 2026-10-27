module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.ClassicalGroups.Symplectic.StatedSpTransport
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal
  CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.ClassicalGroups.Alternating (Lsp)
open QuadraticMap
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G]

theorem conj_mem_of_le_normalizer {R P : Subgroup G} (h : R ≤ Subgroup.normalizer (P : Set G)) :
    ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P :=
  fun _ hr x hx => (Subgroup.mem_normalizer_iff.mp (h hr) x).mp hx

theorem exists_mulVec_eq_of_range {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {R : Subgroup G} {X : Subgroup (GL ι K)} (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    {x y : ι → K} (h : ∃ A ∈ X, ((A : GL ι K) : Matrix ι ι K) *ᵥ x = y) :
    ∃ r : ↥R, ((φ r : GL ι K) : Matrix ι ι K) *ᵥ x = y := by
  obtain ⟨A, hA, hAx⟩ := h
  rw [← hφ] at hA
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hA
  exact ⟨r, hAx⟩

theorem map_subgroupOf_eq_of_mem_sup_iff {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {R N L : Subgroup G} (φ : ↥R →* GL ι K) (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R)
    (hL : L ≤ R) {S : Subgroup (GL ι K)} (hS : S ≤ φ.range)
    (h : ∀ r : ↥R, (r : G) ∈ L ⊔ N ↔ φ r ∈ S) : (L.subgroupOf R).map φ = S := by
  have hNn : (N.subgroupOf R).Normal := by rw [← hNφ]; exact MonoidHom.normal_ker φ
  ext B
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (h l).mp (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hl))
  · intro hB
    obtain ⟨r, rfl⟩ := hS hB
    have hr : (r : G) ∈ L ⊔ N := (h r).mpr hB
    have hr' : r ∈ L.subgroupOf R ⊔ N.subgroupOf R := by
      rw [← Subgroup.subgroupOf_sup hL hN]
      exact Subgroup.mem_subgroupOf.mpr hr
    obtain ⟨l, hl, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hr'
    refine ⟨l, hl, ?_⟩
    have hn1 : φ n = 1 := by rw [← MonoidHom.mem_ker, hNφ]; exact hn
    rw [map_mul, hn1, mul_one]

theorem exists_sectionModule_ker {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {R N P I : Subgroup G} {φ : ↥R →* GL ι K} (hNφ : φ.ker = N.subgroupOf R) (h : SecHyp R P I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : DistribMulAction ↥R M)
      (κ : ↥P →* Multiplicative M), IsSecMod R P I M κ ∧ ∀ x ∈ φ.ker, ∀ a : M, x • a = a := by
  obtain ⟨M, iM, iA, κ, hκ⟩ := exists_sectionModule h
  refine ⟨M, iM, iA, κ, hκ, fun x hx a => ?_⟩
  rw [hNφ] at hx
  have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd a)
  have hact := hκ.act x y ⟨x * y * (x : G)⁻¹, h.normP x x.2 y y.2⟩ rfl
  have heq : κ ⟨x * y * (x : G)⁻¹, h.normP x x.2 y y.2⟩ = κ y := by
    rw [hκ.eq_iff]
    simpa [commutatorElement_def, mul_assoc] using hN x hxN y y.2
  rw [heq, hy, toAdd_ofAdd] at hact
  exact (Multiplicative.ofAdd.injective hact).symm

section Wrappers

variable [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {R N P I L₁ L₂ A₁ A₂ : Subgroup G}

theorem stroth_2_1_ii_secSp {m : ℕ} (hm : 1 ≤ m) (φ : ↥R →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K) (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = LspGL m K u) (hL₂ : (L₂.subgroupOf R).map φ = LspGL m K u') :
    ∃ n : ℕ, Nat.card P = Nat.card I * Nat.card K ^ (2 ^ m * n) := by
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  obtain ⟨n, hn⟩ := stroth_2_1_ii_of_hom φ hφ hm hκ.two hker huu' hL₁ hL₂
    (isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂)
  exact ⟨n, by rw [natCard_eq_of_isSecMod hsec.le hκ, hn]⟩

end Wrappers

section Conj

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {R : Subgroup G}
  {X : Subgroup (GL ι K)} {H : Type*} [Group H]

theorem map_conjSubgroup_subgroupOf (e : X ≃* H) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (r₀ : ↥R) {L : Subgroup G} {S S' : Subgroup H}
    (hS : ∀ h : H, h ∈ S' ↔
      (e ⟨φ r₀, hφ ▸ MonoidHom.mem_range.mpr ⟨r₀, rfl⟩⟩)⁻¹ * h *
        e ⟨φ r₀, hφ ▸ MonoidHom.mem_range.mpr ⟨r₀, rfl⟩⟩ ∈ S)
    (hL : (L.subgroupOf R).map φ = matrixOf X e S) :
    ((conjSubgroup (r₀ : G) L).subgroupOf R).map φ = matrixOf X e S' := by
  ext B
  rw [mem_matrixOf_conj_iff (e := e) (S := S) (S' := S') ⟨φ r₀, hφ ▸ MonoidHom.mem_range.mpr
    ⟨r₀, rfl⟩⟩ hS B, ← hL]
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : (r₀ : G)⁻¹ * x * r₀ ∈ R := R.mul_mem (R.mul_mem (R.inv_mem r₀.2) x.2) r₀.2
    refine ⟨⟨(r₀ : G)⁻¹ * x * r₀, hmem⟩, hx, ?_⟩
    have e : (⟨(r₀ : G)⁻¹ * x * r₀, hmem⟩ : ↥R) = r₀⁻¹ * x * r₀ := rfl
    rw [e, map_mul, map_mul, map_inv]
  · rintro ⟨y, hy, hyB⟩
    refine ⟨r₀ * y * r₀⁻¹, ?_, ?_⟩
    · show (r₀ : G)⁻¹ * ((r₀ : G) * (y : G) * (r₀ : G)⁻¹) * r₀ ∈ L
      have e : (r₀ : G)⁻¹ * ((r₀ : G) * (y : G) * (r₀ : G)⁻¹) * r₀ = y := by group
      rw [e]
      exact hy
    · have : φ r₀ * φ y * (φ r₀)⁻¹ = B := by
        rw [hyB]
        group
      simpa using this

end Conj

section Generation

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {X : Subgroup (GL ι K)}
  {R N L₁ L₂ : Subgroup G}

theorem le_sup_of_map_sup (φ : ↥R →* GL ι K) (hφ : φ.range = X) (hNφ : φ.ker = N.subgroupOf R)
    (hsup : (L₁.subgroupOf R).map φ ⊔ (L₂.subgroupOf R).map φ = X) :
    R ≤ N ⊔ (L₁ ⊔ L₂) := by
  intro x hx
  have hφx : φ ⟨x, hx⟩ ∈ ((L₁.subgroupOf R) ⊔ (L₂.subgroupOf R)).map φ := by
    rw [Subgroup.map_sup, hsup, ← hφ]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hφx
  have hk : (⟨x, hx⟩ : ↥R) * y⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hyx, mul_inv_cancel]
  rw [hNφ, Subgroup.mem_subgroupOf] at hk
  have hle : (L₁.subgroupOf R) ⊔ (L₂.subgroupOf R) ≤ (L₁ ⊔ L₂).subgroupOf R :=
    sup_le (fun z hz => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz)))
      (fun z hz => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hz)))
  have hy' : (y : G) ∈ L₁ ⊔ L₂ := Subgroup.mem_subgroupOf.mp (hle hy)
  have hx' : x = ((⟨x, hx⟩ * y⁻¹ : ↥R) : G) * y := by simp
  rw [hx']
  exact Subgroup.mul_mem_sup hk hy'

theorem le_sup_secSp {m : ℕ} (φ : ↥R →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K) (hNφ : φ.ker = N.subgroupOf R) {u u' : Fin m ⊕ Fin m → K}
    (huu' : spForm m K u u' ≠ 0) (hL₁ : (L₁.subgroupOf R).map φ = LspGL m K u)
    (hL₂ : (L₂.subgroupOf R).map φ = LspGL m K u') : R ≤ N ⊔ (L₁ ⊔ L₂) :=
  le_sup_of_map_sup φ hφ hNφ (by rw [hL₁, hL₂]; exact LspGL_sup_eq huu')

theorem le_sup_secOmega {Q : QuadraticForm K (ι → K)} (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) (φ : ↥R →* GL ι K)
    (hφ : φ.range = X) (hNφ : φ.ker = N.subgroupOf R) {u u' : ι → K} (hu : Q u = 0)
    (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u)
    (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u') : R ≤ N ⊔ (L₁ ⊔ L₂) :=
  le_sup_of_map_sup φ hφ hNφ (by rw [hL₁, hL₂]; exact E.LomGL_sup_eq hQ hu hu' huu')

end Generation

section Wrappers2

variable [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {R N P I L₁ A₁ : Subgroup G}

theorem stroth_2_2_secSp {m : ℕ} {Z V : Subgroup G} (hm : 2 ≤ m) (hK : 2 < Nat.card K)
    (φ : ↥R →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (hNφ : φ.ker = N.subgroupOf R)
    (hsec : SecHyp R P Z) (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ Z) (hZV : Z ≤ V) (hVP : V ≤ P)
    (hact : SectionAct K R V Z φ (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)))
    (hRP : ∀ r ∈ R, ∀ x ∈ P, ⁅r, x⁆ ∈ V) (hind : IsIndecSec R P Z) :
    Nat.card P ≤ Nat.card K * Nat.card V := by
  obtain ⟨hnorm, hZn, ψ, hψ⟩ := hact
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  haveI := hZn
  let κV : ↥V →* Multiplicative M := κ.comp (Subgroup.inclusion hVP)
  have hκV : ∀ v : ↥V, κV v = 1 ↔ (v : G) ∈ Z := fun v => hκ.ker ⟨v, hVP v.2⟩
  have hle : Z.subgroupOf V ≤ κV.ker := fun v hv =>
    (hκV v).mpr (Subgroup.mem_subgroupOf.mp hv)
  let Λ : ↥V ⧸ Z.subgroupOf V →* Multiplicative M := QuotientGroup.lift (Z.subgroupOf V) κV hle
  have hΛ : ∀ v : ↥V, Λ (QuotientGroup.mk v) = κV v := fun v => rfl
  let ι : (Fin m ⊕ Fin m → K) →+ M := AddMonoidHom.mk'
    (fun a => Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd a)))) (fun a b => by
      show Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd (a + b)))) =
        Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd a))) +
          Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd b)))
      rw [ofAdd_add, map_mul, map_mul, toAdd_mul])
  have hι : ∀ q, ι (Multiplicative.toAdd (ψ q)) = Multiplicative.toAdd (Λ q) := fun q => by
    show Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ q))))) = _
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hinj : Function.Injective ι := by
    intro a b hab
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd a))
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd b))
    have h1 : κV v = κV w := by
      have := congrArg Multiplicative.ofAdd hab
      change Multiplicative.ofAdd (Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd a)))) =
        Multiplicative.ofAdd (Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd b)))) at this
      rwa [ofAdd_toAdd, ofAdd_toAdd, ← hv, ← hw, hΛ, hΛ] at this
    have h2 : κV (v⁻¹ * w) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : QuotientGroup.mk v = (QuotientGroup.mk w : ↥V ⧸ Z.subgroupOf V) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr ((hκV _).mp h2)
    rw [hv, hw] at h3
    exact Multiplicative.ofAdd.injective (ψ.symm.injective h3)
  have hcb : ∀ (x : ↥R) (v : ↥V), (x : G) * v * (x : G)⁻¹ ∈ V := fun x v =>
    (Subgroup.mem_normalizer_iff.mp (hnorm x.2) v).mp v.2
  have hιeq : ∀ (x : ↥R) (a : Fin m ⊕ Fin m → K),
      ι ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ a) = x • ι a := by
    intro x a
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd a))
    have ha : a = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
      rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hw := hψ x v ⟨(x : G) * v * (x : G)⁻¹, hcb x v⟩ rfl
    rw [ha, ← hw, hι, hι, hΛ, hΛ]
    have hact := hκ.act x ⟨v, hVP v.2⟩ ⟨(x : G) * v * (x : G)⁻¹, hVP (hcb x v)⟩ rfl
    show Multiplicative.toAdd (κ ⟨(x : G) * v * (x : G)⁻¹, hVP (hcb x v)⟩) =
      x • Multiplicative.toAdd (κ ⟨v, hVP v.2⟩)
    rw [hact, toAdd_ofAdd]
  have htriv : ∀ (x : ↥R) (a : M), x • a - a ∈ ι.range := by
    intro x a
    obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hyx : (x : G) * y * (x : G)⁻¹ ∈ P := hsec.normP x x.2 y y.2
    have hcomm : ⁅(x : G), (y : G)⁆ ∈ V := hRP x x.2 y y.2
    have hact := hκ.act x y ⟨(x : G) * y * (x : G)⁻¹, hyx⟩ rfl
    refine ⟨Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨⁅(x : G), (y : G)⁆, hcomm⟩)), ?_⟩
    rw [hι, hΛ]
    have e1 : κV ⟨⁅(x : G), (y : G)⁆, hcomm⟩ =
        κ ⟨(x : G) * y * (x : G)⁻¹, hyx⟩ * (κ y)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e1, hact, hy, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
    exact (sub_eq_add_neg _ _).symm
  have hindec : ∀ A A' : AddSubgroup M, (∀ x : ↥R, ∀ a ∈ A, x • a ∈ A) →
      (∀ x : ↥R, ∀ a ∈ A', x • a ∈ A') → IsCompl A A' → A = ⊥ ∨ A' = ⊥ := by
    intro A A' hA hA' hc
    obtain ⟨U, hZU, hUP, rfl⟩ := exists_secSub_eq hsec.le hκ A
    obtain ⟨U', hZU', hU'P, rfl⟩ := exists_secSub_eq hsec.le hκ A'
    by_contra hcon
    push Not at hcon
    apply hind
    have hinv : ∀ (W : Subgroup G) (hZW : Z ≤ W) (hWP : W ≤ P),
        (∀ x : ↥R, ∀ a ∈ secSub κ W, x • a ∈ secSub κ W) →
          ∀ r ∈ R, conjSubgroup r W = W := by
      intro W hZW hWP hW r hr
      rw [conjSubgroup_eq_self_iff_secSub hsec hκ ⟨r, hr⟩ hZW hWP]
      refine le_antisymm (fun a ⟨b, hb, hba⟩ => hba ▸ hW ⟨r, hr⟩ b hb) (fun a ha => ?_)
      refine ⟨(⟨r, hr⟩ : ↥R)⁻¹ • a, hW _ a ha, ?_⟩
      show (⟨r, hr⟩ : ↥R) • (⟨r, hr⟩ : ↥R)⁻¹ • a = a
      rw [smul_inv_smul]
    refine ⟨U, U', hZU, hUP, hZU', hU'P, ?_, ?_, ?_, ?_, fun r hr =>
      ⟨hinv U hZU hUP hA r hr, hinv U' hZU' hU'P hA' r hr⟩⟩
    · intro h
      exact hcon.1 (by rw [h]; exact secSub_eq_bot hκ)
    · intro h
      exact hcon.2 (by rw [h]; exact secSub_eq_bot hκ)
    · rw [← secSub_inj hκ (hZU.trans le_sup_left) (sup_le hUP hU'P) hsec.le le_rfl,
        secSub_sup hUP hU'P, secSub_eq_top hκ]
      exact hc.sup_eq_top
    · rw [← secSub_inj hκ (le_inf hZU hZU') (inf_le_left.trans hUP) le_rfl hsec.le,
        secSub_inf hκ hZU, hc.inf_eq_bot, secSub_eq_bot hκ]
  have hb := stroth_2_2_of_hom φ hφ hK hm hκ.two hker ι hinj hιeq htriv hindec
  have hP := natCard_eq_of_isSecMod hsec.le hκ
  have hV : Nat.card V = Nat.card (Fin m ⊕ Fin m → K) * Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h1
    have h2 : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card (Fin m ⊕ Fin m → K) :=
      Nat.card_congr (ψ.toEquiv.trans Multiplicative.toAdd)
    rw [h1, h2]
  calc Nat.card P = Nat.card Z * Nat.card M := by rw [hP]
    _ ≤ Nat.card Z * (Nat.card K * Nat.card (Fin m ⊕ Fin m → K)) := Nat.mul_le_mul_left _ hb
    _ = Nat.card K * Nat.card V := by rw [hV]; ring

end Wrappers2

section OmegaWrappers

variable [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
  [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
  {R N P I L₁ L₂ A₁ A₂ : Subgroup G}

theorem stroth_2_1_ii_secOmegaMinus (E : ElemMatrixIso Q X) {m : ℕ} (hm : 2 ≤ m) (h : IsMinus Q m)
    (φ : ↥R →* GL ι K) (hφ : φ.range = X) (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u') :
    ∃ n : ℕ, Nat.card P = Nat.card I * Nat.card K ^ (2 ^ m * n) := by
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  obtain ⟨n, hn⟩ := stroth_2_1_ii_omegaMinus_of_hom E φ hφ hm h hκ.two hker hu hu' huu' hL₁ hL₂
    (isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂)
  exact ⟨n, by rw [natCard_eq_of_isSecMod hsec.le hκ, hn]⟩

theorem stroth_2_1_ii_secOmegaPlus (E : ElemMatrixIso Q X) {m : ℕ} (hm : 3 ≤ m) (h : IsPlus Q m)
    (φ : ↥R →* GL ι K) (hφ : φ.range = X) (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u') :
    ∃ n : ℕ, Nat.card P = Nat.card I * Nat.card K ^ (2 ^ (m - 1) * n) := by
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  obtain ⟨n, hn⟩ := stroth_2_1_ii_omegaPlus_of_hom E φ hφ hm h hκ.two hker hu hu' huu' hL₁ hL₂
    (isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂)
  exact ⟨n, by rw [natCard_eq_of_isSecMod hsec.le hκ, hn]⟩

end OmegaWrappers

end CFSG.RankThree.GF2n.Stroth80
