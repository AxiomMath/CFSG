module

public import CFSG.Quasithin.EmptyFaithful.SBc5Block

public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C2Aux
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.SBc5SL2 CFSG.Quasithin.SBc5
open scoped commutatorElement

section Borel

variable {X : Type} [Group X] [Finite X]

theorem autCent_of_borel {L B : Subgroup X} {m : ℕ} (hm : 1 < m) (hS : IsShort2 L)
    (hlin : IsLin2Type L m)
    (hB : ∃ P : Subgroup X, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set X))
    {s : X} (hs : s ∈ Subgroup.normalizer (L : Set X))
    (hc : ∀ y ∈ B, s * y = y * s) : ∀ l ∈ L, s * l = l * s := by
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
  have hBn_map : Bn.map L.subtype = B := by
    have h1 : B.subgroupOf L = Bn := by
      ext x
      rw [Subgroup.mem_subgroupOf, hBP, Subgroup.mem_inf, hBn]
      rw [mem_normalizer_subgroupOf_iff hPL]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← h1]
    exact Subgroup.map_subgroupOf_eq_of_le hBL
  have hYmem : ∀ y : ↥L, y ∈ Bn → (y : X) ∈ B := fun y hy => by
    rw [← hBn_map]
    exact ⟨y, hy, rfl⟩
  have hYα : Bn.map α₁ = Tplus F := hα₁B
  obtain ⟨a, ha⟩ : ∃ a : Fˣ, a ≠ 1 := by
    have hcardU : 1 < Nat.card Fˣ := by
      have h1 : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
      have h2 : 4 ≤ Nat.card F := by
        rw [hcardF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.1 hcardU
    exact exists_ne 1
  have hxY : ∀ t : F, ∃ y ∈ Bn, α₁ y = xm t := fun t => by
    have : xm t ∈ Bn.map α₁ := hYα ▸ Uplus_le_Tplus (xm_mem_Uplus t)
    obtain ⟨y, hy, e⟩ := this
    exact ⟨y, hy, e⟩
  obtain ⟨h, hhY, hh⟩ : ∃ y ∈ Bn, α₁ y = dm a := by
    have : dm a ∈ Bn.map α₁ := hYα ▸ dm_mem_Tplus a
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
  have hfixY : ∀ y : ↥L, y ∈ Bn → σ y = y := fun y hy => Subtype.ext (by
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
  have hgg : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have hα₁coe : ∀ l : ↥L, ((α₁ l : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) := fun l => by
    show ((c (α l) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hc_apply]
    simp [Matrix.SpecialLinearGroup.coe_mul]
  have hζ₁ : ∀ l l' : ↥L,
      ζ₁ (l * l') = ζ₁ l + (α₁ l : Matrix (Fin 2) (Fin 2) F).mulVec (ζ₁ l') := by
    intro l l'
    have e : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) *
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (α l : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.mul_assoc _ ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F), hgg, Matrix.mul_one]
    simp only [ζ₁]
    rw [hζ, Matrix.mulVec_add, hα₁coe, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  have hzUy : ∀ y : ↥L, y ∈ Bn → zU y = 1 := fun y hy => Subtype.ext (by
    show s * (y : X) * s⁻¹ * (y : X)⁻¹ = 1
    rw [hc (y : X) (hYmem y hy), mul_inv_cancel_right, mul_inv_cancel])
  have hζY : ∀ y : ↥L, y ∈ Bn → ζ₁ y = 0 := fun y hy => by
    simp only [ζ₁, ζ, hzUy y hy, map_one, toAdd_one, Matrix.mulVec_zero]
  have hζ₁ker : ∀ q : ↥L, q ∈ α.ker → ζ₁ q = 0 := by
    intro q hq
    have hqP' : q ∈ P' := hkerP' hq
    have hqB : q⁻¹ ∈ Bn := Bn.inv_mem (Subgroup.le_normalizer hqP')
    have hqB' : q ∈ Bn := Subgroup.le_normalizer hqP'
    have hcq : q⁻¹ * h * q * h⁻¹ ∈ Bn :=
      Bn.mul_mem (Bn.mul_mem (Bn.mul_mem hqB hhY) hqB') (Bn.inv_mem hhY)
    have e1 : h * q * h⁻¹ = q * (q⁻¹ * h * q * h⁻¹) := by group
    have e2 : ζ₁ (h * q * h⁻¹) = (α₁ h : Matrix (Fin 2) (Fin 2) F).mulVec (ζ₁ q) := by
      rw [mul_assoc, hζ₁ h (q * h⁻¹), hζ₁ q h⁻¹, hζY h hhY, hζY h⁻¹ (Bn.inv_mem hhY)]
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
end Borel

section Block

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_commute_sylow {K L P : Subgroup G} (hK : CharTwo K)
    (hL : IsBlock2 K L) (hP : IsSylowTwoOf P L) {v : G} (hvK : v ∈ K)
    (hvP : ∀ p ∈ P, v * p = p * v) : v ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hvN
  have hL' : IsBlock2 K (conjByElt v L) := IsBlock2.conjByElt_of_mem hL hvK
  have hne : L ≠ conjByElt v L := by
    intro he
    apply hvN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 he.symm
  have hcomm := distinctBlocksCommuteStatement K L (conjByElt v L) hK hL hL' hne
  have hPL' : P ≤ conjByElt v L := by
    intro p hp
    rw [mem_conjByElt]
    have e : v⁻¹ * p * v = p := by
      rw [mul_assoc, ← hvP p hp, inv_mul_cancel_left]
    rw [e]
    exact hP.1 hp
  have hPc : ∀ p ∈ P, ∀ l ∈ L, l * p = p * l := by
    intro p hp l hl
    have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm hl
    exact (Subgroup.mem_centralizer_iff.1 h1 p (hPL' hp)).symm
  have hQP : pCoreOf 2 L ≤ P := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP
  have hU : blockU L = ⊥ := by
    unfold blockU blockQ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hPc q (hQP hq) l hl
  have hlt := hL.1.2.2.2.2.1
  rw [hU] at hlt
  exact absurd hlt (not_lt_bot)

omit [Finite G] in
theorem card_quot_ne_three_of_lin2 {L : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 3 := by
  obtain ⟨F, hFfield, hFfin, hFcard, α, hαs, hαk, -⟩ := hlin
  have hcardF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFcard]
  rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv]
  have h1 : Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Nat.card_le_card_of_injective (xm (F := F)) xm_injective
  have h2 : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem commute_of_le_of_isPGroup {T M V K R : Subgroup G}
    (hQ : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) (K ⊓ M))
    (hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hRK : R ≤ K ⊓ M) (hR : IsPGroup 2 R) :
    ∀ v ∈ V, ∀ r ∈ R, v * r = r * v := by
  intro v hv r hr
  obtain ⟨x, hx, hRx⟩ := F7.isSylowTwoOf_exists_conj_le hQ hRK hR
  have hrx : x⁻¹ * r * x ∈ T ⊓ Subgroup.centralizer (V : Set G) := mem_conjSub.1 (hRx hr)
  have hvx : x⁻¹ * v * x ∈ V := by
    have := (Subgroup.mem_normalizer_iff''.1 (hKN hx) v).1 hv
    exact this
  have hc := Subgroup.mem_centralizer_iff.1 hrx.2 _ hvx
  calc v * r = x * ((x⁻¹ * v * x) * (x⁻¹ * r * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * r * x) * (x⁻¹ * v * x)) * x⁻¹ := by rw [hc]
    _ = r * v := by group

theorem commute_of_relIndex_le_two {V C : Subgroup G} (hV : IsElemAbelian 2 V)
    (hidx : C.relIndex V ≤ 2) {x : G} (hxo : Odd (orderOf x))
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hxC : ∀ c ∈ C, x * c = c * x) :
    ∀ v ∈ V, v * x = x * v := by
  intro v hv
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hV.1
    exact setLike_mul_comm ha hb
  have hw : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxN v).1 hv
  have hcC : v⁻¹ * (x * v * x⁻¹) ∈ C := by
    by_cases hvC : v ∈ C
    · have e : x * v * x⁻¹ = v := by rw [hxC v hvC, mul_inv_cancel_right]
      rw [e, inv_mul_cancel]
      exact C.one_mem
    · have hwC : x * v * x⁻¹ ∉ C := by
        intro hwC
        apply hvC
        have e : v = x⁻¹ * (x * v * x⁻¹) * x := by group
        have e2 : x⁻¹ * (x * v * x⁻¹) * x = x * v * x⁻¹ := by
          rw [mul_assoc, ← hxC _ hwC, inv_mul_cancel_left]
        rw [e, e2]
        exact hwC
      have hidx2 : (C.subgroupOf V).index = 2 := by
        have h1 : (C.subgroupOf V).index ≠ 1 := by
          intro h1
          apply hvC
          have := Subgroup.index_eq_one.1 h1
          have hv' : (⟨v, hv⟩ : ↥V) ∈ C.subgroupOf V := this ▸ Subgroup.mem_top _
          exact hv'
        have h0 : (C.subgroupOf V).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have h2 : (C.subgroupOf V).index ≤ 2 := hidx
        omega
      have key := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨v, hv⟩ : ↥V)⁻¹)
        (b := ⟨x * v * x⁻¹, hw⟩)).2
      have hv' : (⟨v, hv⟩ : ↥V)⁻¹ ∉ C.subgroupOf V := by
        intro h1
        apply hvC
        have := (C.subgroupOf V).inv_mem h1
        rw [inv_inv] at this
        exact this
      have hw' : (⟨x * v * x⁻¹, hw⟩ : ↥V) ∉ C.subgroupOf V := hwC
      exact key ⟨fun h => absurd h hv', fun h => absurd h hw'⟩
  set c := v⁻¹ * (x * v * x⁻¹) with hcdef
  have hcx : x * c = c * x := hxC c hcC
  have hxv : x * v * x⁻¹ = v * c := by rw [hcdef, mul_inv_cancel_left]
  have hpow : ∀ k : ℕ, x ^ k * v * (x ^ k)⁻¹ = v * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : x * c ^ k = c ^ k * x := (Commute.pow_right hcx k).eq
      calc x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ = x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = x * (v * c ^ k) * x⁻¹ := by rw [ih]
        _ = (x * v * x⁻¹) * (x * c ^ k * x⁻¹) := by group
        _ = v * c * c ^ k := by rw [hxv, hck, mul_inv_cancel_right]
        _ = v * c ^ (k + 1) := by rw [pow_succ', mul_assoc]
  have h1 := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hck : c ^ orderOf x = 1 := by
    have := congrArg (fun y => v⁻¹ * y) h1
    simpa using this.symm
  have hc2 : c ^ 2 = 1 := hV.2 c (V.mul_mem (V.inv_mem hv) hw)
  obtain ⟨k, hk⟩ := hxo
  have hc1 : c = 1 := by
    have : c ^ orderOf x = c := by
      rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [← this, hck]
  have e : x * v * x⁻¹ = v := by rw [hxv, hc1, mul_one]
  calc v * x = (x * v * x⁻¹) * x := by rw [e]
    _ = x * v := by group

theorem centralizes_of_lin2_block {T M V K L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T)
    (hQK : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) K)
    (hQM : T ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hK : CharTwo K) (hL : IsBlock2 K L)
    {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) (hBor : IsBorelOfBlock L (L ⊓ (K ⊓ M)))
    (hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) :
    ∀ v ∈ V, ∀ l ∈ L, v * l = l * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQKM : IsSylowTwoOf Q (K ⊓ M) := A4.isSylowTwoOf_mono hQK (le_inf hQK.1 hQM) inf_le_left
  have hVQ : V ≤ Q := fun v hv => ⟨hVT hv, Subgroup.mem_centralizer_iff.2 fun w hw => by
    have := hV.1
    exact setLike_mul_comm hw hv⟩
  have hLK : L ≤ K := hL.2.1
  unfold IsBorelOfBlock at hBor
  split_ifs at hBor with h3
  · exact absurd h3 (card_quot_ne_three_of_lin2 hn hlin)
  obtain ⟨P, hP, hBP⟩ := hBor
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = L ⊓ Subgroup.normalizer (P : Set G) := ⟨_, rfl⟩
  rw [← hBdef] at hBP
  have hOL : pCoreOf 2 L ≤ K ⊓ M := by
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 K :=
      Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hLK hL.2.2
    have h2 : pCoreOf 2 K ≤ Q := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQK
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLK) ((h1.trans h2).trans hQM)
  have hBKM : B ≤ K ⊓ M := by
    rw [← hBP]
    exact sup_le inf_le_right hOL
  have hBL : B ≤ L := hBdef ▸ inf_le_left
  have hV2 := fun (R : Subgroup G) (hR : R ≤ K ⊓ M) (hR2 : IsPGroup 2 R) =>
    commute_of_le_of_isPGroup hQKM hKN hR hR2
  have hPB : P ≤ B := hBdef ▸ le_inf hP.1 Subgroup.le_normalizer
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv =>
    mem_normalizer_of_commute_sylow hK hL hP (hQK.1 (hVQ hv))
      (hV2 P (hPB.trans hBKM) hP.2.1 v hv)
  have hodd : ∀ x ∈ B, Odd (orderOf x) → ∀ v ∈ V, v * x = x * v := by
    intro x hx hxo
    refine commute_of_relIndex_le_two hV hidx hxo (hKN (hBKM hx)) ?_
    intro c hc
    exact (Subgroup.mem_centralizer_iff.1 hc.2 x (hBL hx))
  have hVB : ∀ y ∈ B, ∀ v ∈ V, v * y = y * v := by
    intro y hy v hv
    obtain ⟨a, b, hab, -, ⟨e, hae⟩, hbo, haz, hbz⟩ := F6.exists_mul_eq_pPart Nat.prime_two y
    have hzB : Subgroup.zpowers y ≤ B := Subgroup.zpowers_le.2 hy
    have ha2 : IsPGroup 2 (Subgroup.zpowers a) := by
      rintro ⟨_, k, rfl⟩
      refine ⟨e, Subtype.ext ?_⟩
      show (a ^ k) ^ 2 ^ e = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hae, one_zpow]
    have hva : v * a = a * v := hV2 (Subgroup.zpowers a)
      ((Subgroup.zpowers_le.2 (hzB haz)).trans hBKM) ha2 v hv a (Subgroup.mem_zpowers a)
    have hbodd : Odd (orderOf b) := by
      rw [Nat.odd_iff]
      have := Nat.Coprime.symm hbo
      rcases Nat.even_or_odd (orderOf b) with he | ho
      · exfalso
        have h2 : 2 ∣ orderOf b := even_iff_two_dvd.1 he
        exact absurd (Nat.Coprime.coprime_dvd_left h2 this.symm) (by decide)
      · exact Nat.odd_iff.1 ho
    have hvb : v * b = b * v := hodd b (hzB hbz) hbodd v hv
    rw [← hab]
    calc v * (a * b) = a * (v * b) := by rw [← mul_assoc, hva, mul_assoc]
      _ = a * b * v := by rw [hvb, mul_assoc]
  intro v hv l hl
  exact autCent_of_borel hn hL.1 hlin ⟨P, hP, hBdef⟩ (hVN v hv) (fun y hy => hVB y hy v hv) l hl

end Block

end E6
end CFSG.Quasithin
