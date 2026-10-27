module

public import CFSG.Quasithin.EmptyFaithful.SBc5SL2
public import CFSG.Quasithin.EmptyFaithful.SBc5BlockAux
public import CFSG.Quasithin.EmptyFaithful.SBc5Common
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.SBc5SL2
open scoped commutatorElement

namespace SBc5

section Block

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem zel_mul (s l l' : X) :
    s * (l * l') * s⁻¹ * (l * l')⁻¹ = (s * l * s⁻¹ * l⁻¹) * (l * (s * l' * s⁻¹ * l'⁻¹) * l⁻¹) := by
  group

omit [Finite X] in
theorem xm_injective {F : Type} [Field F] : Function.Injective (xm (F := F)) := by
  intro s t h
  have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [xm] using this

theorem autCent_of_lin2 {L B : Subgroup X} {m : ℕ} (hm : 1 < m) (hS : IsShort2 L)
    (hlin : IsLin2Type L m)
    (hB : ∃ P : Subgroup X, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set X))
    (hY : ¬ oPrimeResidualOf 3 B ≤ pCoreOf 2 L) {s : X} (hs : s ∈ Subgroup.normalizer (L : Set X))
    (hc : ∀ y ∈ oPrimeResidualOf 3 B, s * y = y * s) : ∀ l ∈ L, s * l = l * s := by
  classical
  obtain ⟨F, hFfield, hFfin, hFcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hFfinite : Finite F := Finite.of_fintype F
  have hcardF : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hFcard]
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hcardF
  obtain ⟨P, hP, hBP⟩ := hB
  have hBL : B ≤ L := hBP ▸ inf_le_left
  have hPL : P ≤ L := hP.1
  have hQP : pCoreOf 2 L ≤ P := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP
  have hker : ∀ x : ↥L, x ∈ α.ker ↔ (x : X) ∈ pCoreOf 2 L := fun x => by
    rw [hαk]
    exact AppC.mem_pCore_iff_mem_blockQ x
  have hperf : commutator ↥L = ⊤ := by
    have hq3 := hS.2.2.2.1
    have hcard4 : 4 ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv]
      have h1 : Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
        Nat.card_le_card_of_injective (xm (F := F)) xm_injective
      have h2 : 4 ≤ Nat.card F := by
        rw [hcardF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      exact h2.trans h1
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hq3.resolve_right (by omega)
    have hcomm : commutator (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := hq.1.commutator_eq_top
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply C1GN.isShort2_eq_top_of_sup_pCore hS (commutator ↥L)
    have hmap : (commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
      have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
      show (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L).map _ = ⊤
      rw [h1]
      exact hcomm
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (commutator ↥L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  set P' : Subgroup ↥L := P.subgroupOf L with hP'def
  have hP' : IsSylowTwoOf P' (⊤ : Subgroup ↥L) := isSylowTwoOf_subgroupOf_top hP
  have hkerP' : α.ker ≤ P' := fun x hx => hQP ((hker x).1 hx)
  have hPbar : IsSylowTwoOf (P'.map α) (⊤ : Subgroup (SL2 F)) :=
    isSylowTwoOf_map_surjective α hαs hP'
  have hUp : IsSylowTwoOf (Uplus F) (⊤ : Subgroup (SL2 F)) := isSylowTwoOf_Uplus (by omega) hcardF
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hUp hPbar
  let c : SL2 F →* SL2 F := (MulAut.conj g⁻¹).toMonoidHom
  have hc_apply : ∀ x : SL2 F, c x = g⁻¹ * x * g := fun x => by
    simp [c]
  let α₁ : ↥L →* SL2 F := c.comp α
  have hα₁s : Function.Surjective α₁ := (MulAut.conj g⁻¹).surjective.comp hαs
  have hα₁k : α₁.ker = α.ker := by
    ext x
    simp only [MonoidHom.mem_ker, α₁, MonoidHom.comp_apply, hc_apply]
    constructor
    · intro h
      have := congrArg (fun y => g * y * g⁻¹) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  have hα₁P : P'.map α₁ = Uplus F := by
    have e : P'.map α₁ = (P'.map α).map c := (Subgroup.map_map _ _ _).symm
    rw [e, hg]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hc_apply]
      exact B6.mem_conjSub.mp hx
    · intro hy
      refine ⟨g * y * g⁻¹, B6.mem_conjSub.mpr (by
        have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rw [e]
        exact hy), ?_⟩
      rw [hc_apply]
      group
  have hα₁B : (Subgroup.normalizer (P' : Set ↥L)).map α₁ = Tplus F := by
    have := map_normalizer_eq_of_ker_le α₁ hα₁s (hα₁k ▸ hkerP')
    rw [this, hα₁P, normalizer_Uplus]
  set Bn : Subgroup ↥L := Subgroup.normalizer (P' : Set ↥L) with hBn
  set Y' : Subgroup ↥L := oPrimeResidualOf 3 Bn with hY'
  have hBn_map : Bn.map L.subtype = B := by
    have h1 : B.subgroupOf L = Bn := by
      ext x
      rw [Subgroup.mem_subgroupOf, hBP, Subgroup.mem_inf, hBn]
      rw [mem_normalizer_subgroupOf_iff hPL]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← h1]
    exact Subgroup.map_subgroupOf_eq_of_le hBL
  have hYmap : Y'.map L.subtype = oPrimeResidualOf 3 B := by
    rw [hY', SBd3T.map_oPrimeResidualOf L.subtype 3 Nat.prime_three Bn, hBn_map]
  have hYmem : ∀ y : ↥L, y ∈ Y' → (y : X) ∈ oPrimeResidualOf 3 B := fun y hy => by
    rw [← hYmap]
    exact ⟨y, hy, rfl⟩
  have hYmem' : ∀ y : ↥L, (y : X) ∈ oPrimeResidualOf 3 B → y ∈ Y' := fun y hy => by
    rw [← hYmap] at hy
    obtain ⟨y', hy', e⟩ := hy
    have : y' = y := Subtype.ext e
    rw [← this]
    exact hy'
  have hYα : Y'.map α₁ = oPrimeResidualOf 3 (Tplus F) := by
    rw [hY', SBd3T.map_oPrimeResidualOf α₁ 3 Nat.prime_three Bn, hα₁B]
  obtain ⟨y₀, hy₀Y, hy₀Q⟩ : ∃ y : ↥L, y ∈ Y' ∧ y ∉ α.ker := by
    by_contra hno
    push Not at hno
    apply hY
    intro x hx
    have hxL : x ∈ L := hBL (oPrimeResidualOf_le 3 B hx)
    exact (hker ⟨x, hxL⟩).1 (hno ⟨x, hxL⟩ (hYmem' ⟨x, hxL⟩ hx))
  have hne : oPrimeResidualOf 3 (Tplus F) ≠ ⊥ := by
    intro hbot
    apply hy₀Q
    rw [← hα₁k, MonoidHom.mem_ker]
    have : α₁ y₀ ∈ Y'.map α₁ := Subgroup.mem_map_of_mem α₁ hy₀Y
    rw [hYα, hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hUplus, a, ha, hda⟩ := o3_Tplus hne
  have hxY : ∀ t : F, ∃ y ∈ Y', α₁ y = xm t := fun t => by
    have : xm t ∈ Y'.map α₁ := hYα ▸ hUplus (xm_mem_Uplus t)
    obtain ⟨y, hy, e⟩ := this
    exact ⟨y, hy, e⟩
  obtain ⟨h, hhY, hh⟩ : ∃ y ∈ Y', α₁ y = dm a := by
    have : dm a ∈ Y'.map α₁ := hYα ▸ hda
    obtain ⟨y, hy, e⟩ := this
    exact ⟨y, hy, e⟩
  have hσmem : ∀ l : ↥L, s * (l : X) * s⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp hs l).1 l.2
  let σ : ↥L →* ↥L :=
    { toFun := fun l => ⟨s * (l : X) * s⁻¹, hσmem l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show s * ((a : X) * (b : X)) * s⁻¹ = (s * (a : X) * s⁻¹) * (s * (b : X) * s⁻¹)
        group) }
  have hσ_apply : ∀ l : ↥L, ((σ l : ↥L) : X) = s * (l : X) * s⁻¹ := fun l => rfl
  have hσker : ∀ q : ↥L, q ∈ α.ker → σ q ∈ α.ker := by
    intro q hq
    rw [hker] at hq ⊢
    have hsQ : s ∈ Subgroup.normalizer (blockQ L : Set X) := C1.mem_normalizer_blockQ hs
    exact (Subgroup.mem_normalizer_iff.mp hsQ (q : X)).1 hq
  have hle : α₁.ker ≤ (α₁.comp σ).ker := fun q hq => by
    rw [hα₁k] at hq
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have := hσker q hq
    rw [← hα₁k] at this
    exact this
  let σbar : SL2 F →* SL2 F := (MonoidHom.liftOfSurjective α₁ hα₁s) ⟨α₁.comp σ, hle⟩
  have hσbar : ∀ l : ↥L, σbar (α₁ l) = α₁ (σ l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α₁ (Function.surjInv hα₁s)
      (Function.rightInverse_surjInv hα₁s) ⟨α₁.comp σ, hle⟩ l
  have hfixY : ∀ y : ↥L, y ∈ Y' → σ y = y := fun y hy => Subtype.ext (by
    rw [hσ_apply, hc (y : X) (hYmem y hy), mul_inv_cancel_right])
  have hxσ : ∀ t : F, σbar (xm t) = xm t := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hxY t
    rw [← hyt, hσbar, hfixY y hy]
  have hdσ : σbar (dm a) = dm a := by
    rw [← hh, hσbar, hfixY h hhY]
  have hid : ∀ x : SL2 F, σbar x = x := hom_eq_id σbar hxσ ha hdσ
  have hzQ : ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ blockQ L := by
    intro l hl
    have h1 : α₁ (σ ⟨l, hl⟩) = α₁ ⟨l, hl⟩ := by rw [← hσbar, hid]
    have h2 : σ ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L)⁻¹ ∈ α₁.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hα₁k, hker] at h2
    exact h2
  have hzU : ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ blockU L :=
    C1.commutator_mem_blockU_of_mem_blockQ hS hzQ
  have hUN : L ≤ Subgroup.normalizer (blockU L : Set X) := C1.le_normalizer_blockU L
  let zU : ↥L → ↥(blockU L) := fun l => ⟨s * (l : X) * s⁻¹ * (l : X)⁻¹, hzU l l.2⟩
  let cj : ↥L → ↥(blockU L) → ↥(blockU L) := fun l u =>
    ⟨(l : X) * (u : X) * (l : X)⁻¹, (Subgroup.mem_normalizer_iff.mp (hUN l.2) u).1 u.2⟩
  let ζ : ↥L → (Fin 2 → F) := fun l => Multiplicative.toAdd (β (zU l))
  have hzUmul : ∀ l l' : ↥L, zU (l * l') = zU l * cj l (zU l') := fun l l' => Subtype.ext (by
    show s * ((l : X) * (l' : X)) * s⁻¹ * ((l : X) * (l' : X))⁻¹ = _
    exact zel_mul s l l')
  have hζ : ∀ l l' : ↥L, ζ (l * l') = ζ l + (α l : Matrix (Fin 2) (Fin 2) F).mulVec (ζ l') := by
    intro l l'
    show Multiplicative.toAdd (β (zU (l * l'))) = _
    rw [hzUmul, map_mul, toAdd_mul]
    congr 1
    exact hβe l (zU l') (cj l (zU l')) rfl
  let ζ₁ : ↥L → (Fin 2 → F) := fun l =>
    ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (ζ l)
  have hgg : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have hα₁coe : ∀ l : ↥L, ((α₁ l : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) := fun l => by
    show ((c (α l) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hc_apply]
    simp [Matrix.SpecialLinearGroup.coe_mul]
  have hζ₁ : ∀ l l' : ↥L, ζ₁ (l * l') = ζ₁ l + (α₁ l : Matrix (Fin 2) (Fin 2) F).mulVec (ζ₁ l') := by
    intro l l'
    have e : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.mul_assoc _ ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F), hgg, Matrix.mul_one]
    simp only [ζ₁]
    rw [hζ, Matrix.mulVec_add, hα₁coe, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  have hzUy : ∀ y : ↥L, y ∈ Y' → zU y = 1 := fun y hy => Subtype.ext (by
    show s * (y : X) * s⁻¹ * (y : X)⁻¹ = 1
    rw [hc (y : X) (hYmem y hy), mul_inv_cancel_right, mul_inv_cancel])
  have hζY : ∀ y : ↥L, y ∈ Y' → ζ₁ y = 0 := fun y hy => by
    simp only [ζ₁, ζ, hzUy y hy, map_one, toAdd_one, Matrix.mulVec_zero]
  have hζ₁ker : ∀ q : ↥L, q ∈ α.ker → ζ₁ q = 0 := by
    intro q hq
    have hqP' : q ∈ P' := hkerP' hq
    have hqB : q⁻¹ ∈ Bn := Bn.inv_mem (Subgroup.le_normalizer hqP')
    have h1 : q⁻¹ * h * q⁻¹⁻¹ ∈ Y' := oPrimeResidualOf_conj_mem 3 hqB hhY
    have hcq : q⁻¹ * h * q * h⁻¹ ∈ Y' := by
      have : q⁻¹ * h * q * h⁻¹ = (q⁻¹ * h * q⁻¹⁻¹) * h⁻¹ := by simp
      rw [this]
      exact Y'.mul_mem h1 (Y'.inv_mem hhY)
    have e1 : h * q * h⁻¹ = q * (q⁻¹ * h * q * h⁻¹) := by group
    have e2 : ζ₁ (h * q * h⁻¹) = (α₁ h : Matrix (Fin 2) (Fin 2) F).mulVec (ζ₁ q) := by
      rw [mul_assoc, hζ₁ h (q * h⁻¹), hζ₁ q h⁻¹, hζY h hhY, hζY h⁻¹ (Y'.inv_mem hhY)]
      simp
    have e3 : ζ₁ (q * (q⁻¹ * h * q * h⁻¹)) = ζ₁ q := by
      rw [hζ₁ q _, hζY _ hcq]
      simp
    rw [e1, e3] at e2
    apply eq_zero_of_fixed_dm ha
    rw [← hh]
    exact e2.symm
  let ζbar : SL2 F → (Fin 2 → F) := fun x => ζ₁ (Function.surjInv hα₁s x)
  have hζbar : ∀ l : ↥L, ζbar (α₁ l) = ζ₁ l := by
    intro l
    have e : α₁ (Function.surjInv hα₁s (α₁ l)) = α₁ l := Function.surjInv_eq hα₁s _
    have hq : l⁻¹ * Function.surjInv hα₁s (α₁ l) ∈ α.ker := by
      rw [← hα₁k, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    have := hζ₁ l (l⁻¹ * Function.surjInv hα₁s (α₁ l))
    rw [mul_inv_cancel_left, hζ₁ker _ hq, Matrix.mulVec_zero, add_zero] at this
    exact this
  have hcoc : ∀ x y : SL2 F,
      ζbar (x * y) = ζbar x + (x : Matrix (Fin 2) (Fin 2) F).mulVec (ζbar y) := by
    intro x y
    obtain ⟨l, rfl⟩ := hα₁s x
    obtain ⟨l', rfl⟩ := hα₁s y
    rw [← map_mul, hζbar, hζbar, hζbar]
    exact hζ₁ l l'
  have hxζ : ∀ t : F, ζbar (xm t) = 0 := fun t => by
    obtain ⟨y, hy, hyt⟩ := hxY t
    rw [← hyt, hζbar]
    exact hζY y hy
  have hdζ : ζbar (dm a) = 0 := by
    rw [← hh, hζbar]
    exact hζY h hhY
  have hzero : ∀ x : SL2 F, ζbar x = 0 := cocycle_eq_zero ζbar hcoc hxζ ha hdζ
  have hζ0 : ∀ l : ↥L, ζ l = 0 := by
    intro l
    have h1 : ζ₁ l = 0 := by rw [← hζbar, hzero]
    have h2 : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (ζ₁ l) = ζ l := by
      simp only [ζ₁, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
    rw [← h2, h1, Matrix.mulVec_zero]
  have hzZ : ∀ l : ↥L, s * (l : X) * s⁻¹ * (l : X)⁻¹ ∈ blockZ L := by
    intro l
    have h1 : β (zU l) = 1 := toAdd_eq_zero.mp (hζ0 l)
    have h2 : zU l ∈ β.ker := h1
    rw [hβk] at h2
    exact h2
  have hcent : ∀ l l' : ↥L, (l : X) * (s * (l' : X) * s⁻¹ * (l' : X)⁻¹) =
      (s * (l' : X) * s⁻¹ * (l' : X)⁻¹) * (l : X) := fun l l' =>
    Subgroup.mem_centralizer_iff.mp (hzZ l').2 l l.2
  let ω : ↥L →* ↥(blockZ L) :=
    { toFun := fun l => ⟨s * (l : X) * s⁻¹ * (l : X)⁻¹, hzZ l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l l' => Subtype.ext (by
        show s * ((l : X) * (l' : X)) * s⁻¹ * ((l : X) * (l' : X))⁻¹ = _
        rw [zel_mul, hcent l l', mul_inv_cancel_right]
        rfl) }
  have hZcomm : ∀ u v : ↥(blockZ L), u * v = v * u := fun u v => Subtype.ext (by
    have hu : (u : X) ∈ blockU L := (inf_le_left : blockZ L ≤ blockU L) u.2
    have hv : (v : X) ∈ blockQ L :=
      C1.blockU_le_blockQ hS ((inf_le_left : blockZ L ≤ blockU L) v.2)
    exact C1.blockU_comm hS _ hu _ hv)
  have hωker : commutator ↥L ≤ ω.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker]
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [hZcomm (ω x) (ω y)]
    group
  intro l hl
  have h1 : ω ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : ↥L) ∈ ω.ker := hωker (by rw [hperf]; exact Subgroup.mem_top _)
    exact this
  have h3 : s * l * s⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h1
  calc s * l = (s * l * s⁻¹ * l⁻¹) * (l * s) := by group
    _ = l * s := by rw [h3, one_mul]

end Block

end SBc5

end CFSG.Quasithin
