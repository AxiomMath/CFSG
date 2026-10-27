module

public import CFSG.Quasithin.Background.SmithD39TwoMult
public import CFSG.Quasithin.Background.SmithD39TwoWit
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.F918XY
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.GoldschmidtD35CoreOff3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Factor
public import CFSG.Quasithin.EmptyFaithful.SmithD391FF
public import CFSG.Quasithin.EmptyFaithful.SmithD391XW
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Walter.J1
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
open scoped Pointwise

section Orbit

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def orbSum (B : Subgroup Γ) (J : Subgroup Q) : Subgroup Q := ⨆ t : ↥B, (t : Γ) • J

theorem smul_le_orbSum {B : Subgroup Γ} (J : Subgroup Q) {t : Γ} (ht : t ∈ B) :
    t • J ≤ orbSum B J :=
  le_iSup (fun t : ↥B => (t : Γ) • J) ⟨t, ht⟩

theorem le_orbSum (B : Subgroup Γ) (J : Subgroup Q) : J ≤ orbSum B J := by
  have := smul_le_orbSum (B := B) J B.one_mem
  rwa [one_smul] at this

theorem orbSum_mono {B B' : Subgroup Γ} (h : B ≤ B') (J : Subgroup Q) :
    orbSum B J ≤ orbSum B' J :=
  iSup_le fun t => smul_le_orbSum J (h t.2)

theorem smul_mem_orbSum {B : Subgroup Γ} {J : Subgroup Q} {b : Γ} (hb : b ∈ B) {q : Q}
    (hq : q ∈ orbSum B J) : b • q ∈ orbSum B J := by
  refine Subgroup.iSup_induction (fun t : ↥B => (t : Γ) • J)
    (C := fun x => b • x ∈ orbSum B J) hq (fun t x hx => ?_) ?_ ?_
  · have h1 := Subgroup.smul_mem_pointwise_smul x b _ hx
    rw [smul_smul] at h1
    exact smul_le_orbSum J (B.mul_mem hb t.2) h1
  · rw [smul_one]
    exact one_mem _
  · intro x y hx hy
    rw [smul_mul']
    exact mul_mem hx hy

@[expose] def stabIn (A : Subgroup Γ) (J : Subgroup Q) : Subgroup Γ :=
  A ⊓ MulAction.stabilizer Γ J

theorem mem_stabIn {A : Subgroup Γ} {J : Subgroup Q} {t : Γ} :
    t ∈ stabIn A J ↔ t ∈ A ∧ t • J = J :=
  Iff.rfl

theorem orbSum_stabIn (A : Subgroup Γ) (J : Subgroup Q) : orbSum (stabIn A J) J = J :=
  le_antisymm (iSup_le fun t => (mem_stabIn.1 t.2).2.le) (le_orbSum _ J)

private def extendBy {A : Subgroup Γ} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) {B : Subgroup Γ} (hBA : B ≤ A) {a : Γ} (ha : a ∈ A) :
    Subgroup Γ where
  carrier := {x | x ∈ B ∨ a⁻¹ * x ∈ B}
  mul_mem' := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA2 a ha])
    have hmemA : ∀ x, x ∈ B ∨ a⁻¹ * x ∈ B → x ∈ A := by
      rintro x (hx | hx)
      · exact hBA hx
      · have := A.mul_mem ha (hBA hx)
        rwa [mul_inv_cancel_left] at this
    intro x y hx hy
    have hxA := hmemA x hx
    have hyA := hmemA y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (B.mul_mem hx hy)
    · right
      have h1 : a⁻¹ * (x * y) = x * (a⁻¹ * y) := by
        rw [← mul_assoc, ← mul_assoc, hAc a⁻¹ (A.inv_mem ha) x hxA]
      rw [h1]
      exact B.mul_mem hx hy
    · right
      rw [← mul_assoc]
      exact B.mul_mem hx hy
    · left
      have h1 : x * y = (a⁻¹ * x) * (a⁻¹ * y) := by
        rw [hinv, mul_assoc, ← mul_assoc x a y, hAc x hxA a ha, mul_assoc, ← mul_assoc a a,
          ← pow_two, hA2 a ha, one_mul]
      rw [h1]
      exact B.mul_mem hx hy
  one_mem' := Or.inl B.one_mem
  inv_mem' := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA2 a ha])
    rintro x (hx | hx)
    · exact Or.inl (B.inv_mem hx)
    · right
      have hxA : x ∈ A := by
        have := A.mul_mem ha (hBA hx)
        rwa [mul_inv_cancel_left] at this
      have h1 : a⁻¹ * x⁻¹ = (a⁻¹ * x)⁻¹ := by
        rw [mul_inv_rev, inv_inv, hinv, hAc a ha x⁻¹ (A.inv_mem hxA)]
      show a⁻¹ * x⁻¹ ∈ B
      rw [h1]
      exact B.inv_mem hx

private theorem mem_extendBy {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} {x : Γ} :
    x ∈ extendBy hAc hA2 hBA ha ↔ x ∈ B ∨ a⁻¹ * x ∈ B :=
  Iff.rfl

private theorem card_extendBy [Finite Γ] {A : Subgroup Γ}
    {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ}
    {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} (haB : a ∉ B) :
    Nat.card ↥(extendBy hAc hA2 hBA ha) = 2 * Nat.card ↥B := by
  classical
  have e : ↥(extendBy hAc hA2 hBA ha) ≃ ↥B ⊕ ↥B :=
    { toFun := fun x => if h : (x : Γ) ∈ B then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨a⁻¹ * x, (mem_extendBy.1 x.2).resolve_left h⟩
      invFun := fun y => match y with
        | Sum.inl b => ⟨b, mem_extendBy.2 (Or.inl b.2)⟩
        | Sum.inr b => ⟨a * b, mem_extendBy.2 (Or.inr (by rw [inv_mul_cancel_left]; exact b.2))⟩
      left_inv := fun x => by
        by_cases h : (x : Γ) ∈ B
        · simp only [h, dite_true]
        · simp only [h, dite_false, mul_inv_cancel_left]
      right_inv := fun y => by
        rcases y with b | b
        · simp only [b.2, dite_true]
        · have hab : a * (b : Γ) ∉ B := fun h => haB (by
            have := B.mul_mem h (B.inv_mem b.2)
            rwa [mul_inv_cancel_right] at this)
          simp only [hab, dite_false, inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_sum, two_mul]

private theorem rk_extendBy [Finite Γ] {A : Subgroup Γ}
    {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ}
    {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} (haB : a ∉ B) :
    rk ↥(extendBy hAc hA2 hBA ha) = rk ↥B + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [card_extendBy haB, padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self,
    add_comm]

theorem smul_orbSum (B : Subgroup Γ) (J : Subgroup Q) (a : Γ) :
    a • orbSum B J = ⨆ t : ↥B, (a * (t : Γ)) • J := by
  apply le_antisymm
  · have h1 : orbSum B J ≤ a⁻¹ • ⨆ t : ↥B, (a * (t : Γ)) • J := by
      refine iSup_le fun t => ?_
      have h2 : (t : Γ) • J = a⁻¹ • ((a * (t : Γ)) • J) := by
        rw [smul_smul, inv_mul_cancel_left]
      rw [h2]
      exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)).2
        (le_iSup (fun t : ↥B => (a * (t : Γ)) • J) t)
    have h3 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2 h1
    rwa [smul_inv_smul] at h3
  · refine iSup_le fun t => ?_
    rw [← smul_smul]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2 (smul_le_orbSum J t.2)

private theorem orbSum_extendBy {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A}
    (J : Subgroup Q) :
    orbSum (extendBy hAc hA2 hBA ha) J = orbSum B J ⊔ a • orbSum B J := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rcases mem_extendBy.1 t.2 with ht | ht
    · exact (smul_le_orbSum J ht).trans le_sup_left
    · have h1 : (t : Γ) • J = a • ((a⁻¹ * t) • J) := by rw [smul_smul, mul_inv_cancel_left]
      rw [h1]
      exact ((Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2
        (smul_le_orbSum J ht)).trans le_sup_right
  · refine sup_le (orbSum_mono (fun x hx => mem_extendBy.2 (Or.inl hx)) J) ?_
    rw [smul_orbSum]
    refine iSup_le fun t => smul_le_orbSum J (mem_extendBy.2 (Or.inr ?_))
    rw [inv_mul_cancel_left]
    exact t.2

variable {K : Subgroup Γ}

theorem normalizes_normalizer (K : Subgroup Γ) :
    XMod.Normalizes ↥K ↥(Subgroup.normalizer (K : Set Γ)) Q := by
  intro t a
  refine ⟨⟨(t : Γ) * a * (t : Γ)⁻¹, conj_mem_of_mem_normalizer t.2 a.2⟩, fun q => ?_⟩
  change (t : Γ) • (a : Γ) • q = ((t : Γ) * a * (t : Γ)⁻¹) • (t : Γ) • q
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem mem_normalizer_of_conj {A : Subgroup Γ} (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    {a : Γ} (ha : a ∈ A) : a ∈ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => hAK a ha k hk, fun hk => ?_⟩
  have := hAK a⁻¹ (A.inv_mem ha) _ hk
  simpa [mul_assoc] using this

theorem isInv_orbSum {B : Subgroup Γ} (hBK : B ≤ Subgroup.normalizer (K : Set Γ))
    {J : Subgroup Q} (hJ : XMod.IsInv ↥K J) : XMod.IsInv ↥K (orbSum B J) :=
  XMod.isInv_iSup fun t => isModInv_smul (hBK t.2) hJ

variable [Finite Q] {A : Subgroup Γ}

theorem orbSum_inf_smul_eq_bot (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) {J : Subgroup Q}
    (hJ : XMod.IsIrr ↥K J) (hhom : ∀ t ∈ A, XMod.Iso ↥K (t • J) J → t • J = J)
    {B : Subgroup Γ} (hBA : B ≤ A) (hstab : stabIn A J ≤ B) {a : Γ} (ha : a ∈ A) (haB : a ∉ B) :
    orbSum B J ⊓ a • orbSum B J = ⊥ := by
  have hAN : A ≤ Subgroup.normalizer (K : Set Γ) := fun x hx => mem_normalizer_of_conj hAK hx
  have hN := normalizes_normalizer (Q := Q) K
  have hirr : ∀ t ∈ A, XMod.IsIrr ↥K (t • J) := fun t ht => isIrr_smul hN ⟨t, hAN ht⟩ hJ
  have hinv1 : XMod.IsInv ↥K (orbSum B J) := isInv_orbSum (hBA.trans hAN) hJ.1
  have hinv2 : XMod.IsInv ↥K (a • orbSum B J) := isModInv_smul (hAN ha) hinv1
  by_contra hne
  obtain ⟨J', hJ'X, hJ'⟩ := exists_isIrr_le (hinv1.inf hinv2) hne
  obtain ⟨⟨t, ht⟩, hiso1⟩ := exists_iso_of_le_iSup (S := fun t : ↥B => (t : Γ) • J)
    (fun t => hirr _ (hBA t.2)) hJ' (hJ'X.trans inf_le_left)
  have h2 : J' ≤ ⨆ t : ↥B, (a * (t : Γ)) • J := by
    rw [← smul_orbSum]
    exact hJ'X.trans inf_le_right
  obtain ⟨⟨t', ht'⟩, hiso2⟩ := exists_iso_of_le_iSup (S := fun t : ↥B => (a * (t : Γ)) • J)
    (fun t => hirr _ (A.mul_mem ha (hBA t.2))) hJ' h2
  have hiso : XMod.Iso ↥K (t • J) ((a * t') • J) := (XMod.Iso.symm hJ'.1 hiso1).trans hiso2
  have hiso3 := XMod.iso_smul hN ⟨t⁻¹, hAN (A.inv_mem (hBA ht))⟩ hiso
  change XMod.Iso ↥K (t⁻¹ • t • J) (t⁻¹ • (a * t') • J) at hiso3
  rw [smul_smul, smul_smul, inv_mul_cancel, one_smul] at hiso3
  have hmem : t⁻¹ * (a * t') ∈ A := A.mul_mem (A.inv_mem (hBA ht)) (A.mul_mem ha (hBA ht'))
  have h4 := hhom _ hmem (XMod.Iso.symm hJ.1 hiso3)
  have h5 : t⁻¹ * (a * t') ∈ B := hstab ⟨hmem, h4⟩
  apply haB
  have := B.mul_mem (B.mul_mem ht h5) (B.inv_mem ht')
  rwa [mul_inv_cancel_left, mul_inv_cancel_right] at this

theorem nB_orbit [Finite Γ] (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) {J : Subgroup Q}
    (hJ : XMod.IsIrr ↥K J) (hhom : ∀ t ∈ A, XMod.Iso ↥K (t • J) J → t • J = J) :
    rk ↥(orbSum A J) = 2 ^ (rk ↥A - rk ↥(stabIn A J)) * rk ↥J ∧
      nB A (orbSum A J) + rk ↥J =
        2 ^ (rk ↥A - rk ↥(stabIn A J)) * rk ↥J + nB (stabIn A J) J := by
  set A₀ := stabIn A J with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA2 x x.2)⟩
  have key : ∀ n : ℕ, n ≤ rk ↥A - rk ↥A₀ → ∃ B : Subgroup Γ, A₀ ≤ B ∧ B ≤ A ∧
      rk ↥B = rk ↥A₀ + n ∧ rk ↥(orbSum B J) = 2 ^ n * rk ↥J ∧
        nB B (orbSum B J) + rk ↥J = 2 ^ n * rk ↥J + nB A₀ J := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨A₀, le_rfl, hA₀A, by omega, ?_, ?_⟩ <;> rw [hA₀, orbSum_stabIn] <;> ring
    | succ n ih =>
      intro hn
      obtain ⟨B, h0B, hBA, hrkB, hrkY, hnB⟩ := ih (by omega)
      have hlt : B < A := by
        refine lt_of_le_of_ne hBA fun h => ?_
        rw [h] at hrkB
        omega
      obtain ⟨a, ha, haB⟩ := IsConcreteLE.exists_of_lt hlt
      set B' := extendBy hAc hA2 hBA ha with hB'
      have hBB' : B ≤ B' := fun x hx => mem_extendBy.2 (Or.inl hx)
      have hB'A : B' ≤ A := by
        intro x hx
        rcases mem_extendBy.1 hx with hx | hx
        · exact hBA hx
        · have := A.mul_mem ha (hBA hx)
          rwa [mul_inv_cancel_left] at this
      have haB' : a ∈ B' := mem_extendBy.2 (Or.inr (by rw [inv_mul_cancel]; exact B.one_mem))
      have hdisj := orbSum_inf_smul_eq_bot hAK hJ hhom hBA h0B ha haB
      have hsum := orbSum_extendBy (hAc := hAc) (hA2 := hA2) (hBA := hBA) (ha := ha) J
      rw [← hB'] at hsum
      have hrk2 : rk ↥(orbSum B' J) = 2 * rk ↥(orbSum B J) := by
        have h1 := rk_sup_add_rk_inf (orbSum B J) (a • orbSum B J)
        rw [hdisj, rk_bot, rk_smul] at h1
        rw [hsum]
        omega
      have hidx := nB_index_two (A := B') (A' := B) haB' (hA2 a ha)
        (fun x hx y hy => hAc x (hB'A hx) y (hB'A hy)) hBB'
        (fun x hx => mem_extendBy.1 hx) (P' := orbSum B J)
        (fun b q hq => smul_mem_orbSum b.2 hq) hdisj
      refine ⟨B', h0B.trans hBB', hB'A, by rw [hB', rk_extendBy haB, hrkB]; ring, ?_, ?_⟩
      · rw [hrk2, hrkY]
        ring
      · rw [hsum, hidx, hrkY]
        have : 2 ^ (n + 1) * rk ↥J = 2 ^ n * rk ↥J + 2 ^ n * rk ↥J := by ring
        omega
  have hrkA₀ : rk ↥A₀ ≤ rk ↥A := rk_mono hA₀A
  obtain ⟨B, -, hBA, hrkB, hrkY, hnB⟩ := key (rk ↥A - rk ↥A₀) le_rfl
  have hBeq : B = A := by
    refine Subgroup.eq_of_le_of_card_ge hBA ?_
    rw [card_eq_two_pow_of_isPGroup hAp, card_eq_two_pow_of_isPGroup (hAp.to_le hBA)]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hBeq] at hrkY hnB
  exact ⟨hrkY, hnB⟩

omit [Finite Q] in
theorem normalizes_of_conj (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) :
    XMod.Normalizes ↥K ↥A Q := by
  intro t a
  refine ⟨⟨(t : Γ) * a * (t : Γ)⁻¹, hAK t t.2 a a.2⟩, fun q => ?_⟩
  change (t : Γ) • (a : Γ) • q = ((t : Γ) * a * (t : Γ)⁻¹) • (t : Γ) • q
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem exists_irr_small [Finite Γ] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) {Y : Subgroup Q} (hY : XMod.IsIrr ↥(K ⊔ A) Y)
    (hKY : ∃ k ∈ K, ∃ y ∈ Y, k • y ≠ y) (hAY : ∃ a ∈ A, ∃ y ∈ Y, a • y ≠ y)
    (hr : 3 * nB A Y ≤ rk ↥A - rk ↥(A ⊓ fixingSubgroup Γ (Y : Set Q))) :
    ∃ J : Subgroup Q, J ≤ Y ∧ XMod.IsIrr ↥K J ∧ XMod.commOf ↥K J = J ∧
      rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q)) < rk ↥(stabIn A J) ∧
      3 * nB (stabIn A J) J ≤
        rk ↥(stabIn A J) - rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q)) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set Γ) := fun x hx => mem_normalizer_of_conj hAK hx
  have hNA := normalizes_of_conj (Q := Q) hAK
  have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA2 x x.2)⟩
  have hYK : XMod.IsInv ↥K Y := fun k y hy => hY.1 ⟨k, le_sup_left (α := Subgroup Γ) k.2⟩ y hy
  have hYA : ∀ a ∈ A, ∀ y ∈ Y, a • y ∈ Y := fun a ha y hy =>
    hY.1 ⟨a, le_sup_right (α := Subgroup Γ) ha⟩ y hy
  have hYirr : ∀ J : Subgroup Q, J ≤ Y → XMod.IsInv ↥K J → (∀ a ∈ A, ∀ y ∈ J, a • y ∈ J) →
      J = ⊥ ∨ J = Y := by
    intro J hJY hJK hJA
    have hJinv : XMod.IsInv ↥(K ⊔ A) J := fun g y hy =>
      smul_mem_of_mem_sup (A := K) (Λ := A) (fun k hk y hy => hJK ⟨k, hk⟩ y hy) hJA g.2 y hy
    exact hY.2.2 J hJinv bot_le hJY
  have hCYK : Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) = ⊥ := by
    rcases hYirr (Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q)) inf_le_left
      (fun k y hy => ⟨hYK k y hy.1, trivial, fun k' => by
        change (k' : Γ) • (k : Γ) • y = (k : Γ) • y
        have h1 : (k : Γ) • y = y := hy.2.2 k
        rw [h1]
        exact hy.2.2 k'⟩)
      (fun a ha y hy => ⟨hYA a ha y hy.1, trivial, fun k => by
        change (k : Γ) • a • y = a • y
        have h1 : (a⁻¹ * k * a) • y = y := hy.2.2 ⟨a⁻¹ * k * a, by
          have := hAK a⁻¹ (A.inv_mem ha) k k.2
          rwa [inv_inv] at this⟩
        have h2 : (k : Γ) • a • y = a • ((a⁻¹ * k * a) • y) := by
          rw [smul_smul, smul_smul]
          congr 1
          group
        rw [h2, h1]⟩) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk, y, hy, hky⟩ := hKY
      have : y ∈ Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) := by rw [h]; exact hy
      exact hky (this.2.2 ⟨k, hk⟩)
  have hYne : Y ≠ ⊥ := by
    intro h
    obtain ⟨k, -, y, hy, hky⟩ := hKY
    rw [h, Subgroup.mem_bot] at hy
    rw [hy, smul_one] at hky
    exact hky rfl
  obtain ⟨J₀, hJ₀Y, hJ₀⟩ := exists_isIrr_le hYK hYne
  obtain ⟨J, hJle, hJ, -, hhc⟩ := XMod.exists_isHomComp_of_isIrr hQ hNA hAp hJ₀
  have hhom : ∀ t ∈ A, XMod.Iso ↥K (t • J) J → t • J = J := fun t ht hiso =>
    (XMod.forall_iso_smul_eq_iff_isHomComp hNA hJ).2 hhc ⟨t, ht⟩ hiso
  have hJY : J ≤ Y := by
    refine hJle.trans (iSup_le fun t => ?_)
    intro q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    have h1 := hYA _ t.2 _ (hJ₀Y hq)
    change (t : Γ) • ((t : Γ)⁻¹ • q) ∈ Y at h1
    rwa [smul_inv_smul] at h1
  have horb : orbSum A J = Y := by
    have hle : orbSum A J ≤ Y := by
      refine iSup_le fun t => ?_
      intro q hq
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
      have h1 := hYA _ t.2 _ (hJY hq)
      rwa [smul_inv_smul] at h1
    rcases hYirr _ hle (isInv_orbSum hAN hJ.1) (fun a ha q hq => smul_mem_orbSum ha hq) with
      h | h
    · exfalso
      have := le_orbSum A J
      rw [h] at this
      exact hJ.2.1.ne' (le_bot_iff.1 this)
    · exact h
  have hcomm : XMod.commOf ↥K J = J := by
    rcases hJ.2.2 _ (XMod.isInv_commOf J) bot_le (XMod.commOf_le_of_isInv hJ.1) with h | h
    · exfalso
      have h1 : J ≤ Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) :=
        le_inf hJY (XMod.commOf_eq_bot_iff.1 h)
      rw [hCYK] at h1
      exact hJ.2.1.ne' (le_bot_iff.1 h1)
    · exact h
  set A₀ := stabIn A J with hA₀
  have hcent : A ⊓ fixingSubgroup Γ (Y : Set Q) = A₀ ⊓ fixingSubgroup Γ (J : Set Q) := by
    apply le_antisymm
    · rintro a ⟨ha, hfix⟩
      have hfix' := (mem_fixingSubgroup_iff Γ).1 hfix
      refine ⟨⟨ha, ?_⟩, (mem_fixingSubgroup_iff Γ).2 fun y hy => hfix' y (hJY hy)⟩
      show a • J = J
      ext q
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hq
        have h1 := hfix' _ (hJY hq)
        rw [smul_inv_smul] at h1
        rw [h1]
        exact hq
      · intro hq
        rw [inv_smul_eq_iff.2 (hfix' q (hJY hq)).symm]
        exact hq
    · rintro a ⟨⟨ha, -⟩, hfix⟩
      have hfix' := (mem_fixingSubgroup_iff Γ).1 hfix
      refine ⟨ha, (mem_fixingSubgroup_iff Γ).2 fun y hy => ?_⟩
      rw [← horb] at hy
      have hle : orbSum A J ≤ XMod.fixed ↥(Subgroup.zpowers a) (⊤ : Subgroup Q) := by
        refine iSup_le fun t => ?_
        intro q hq
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
        refine mem_fixed_zpowers_iff.2 ?_
        have h1 := hfix' _ hq
        calc a • q = a • ((t : Γ) • ((t : Γ)⁻¹ • q)) := by rw [smul_inv_smul]
          _ = (t : Γ) • (a • ((t : Γ)⁻¹ • q)) := by rw [smul_smul, hAc a ha t t.2, mul_smul]
          _ = q := by rw [h1, smul_inv_smul]
      exact mem_fixed_zpowers_iff.1 (hle hy)
  obtain ⟨hrkY, hnB⟩ := nB_orbit hAK hAc hA2 hJ hhom
  rw [horb, ← hA₀] at hrkY hnB
  rw [hcent] at hr
  have hv : 0 < rk ↥J := by
    rcases Nat.eq_zero_or_pos (rk ↥J) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hJ.2.1.ne'
    · exact h
  have hc : rk ↥(A₀ ⊓ fixingSubgroup Γ (J : Set Q)) ≤ rk ↥A₀ := rk_mono inf_le_left
  have hA₀le : rk ↥A₀ ≤ rk ↥A := rk_mono inf_le_left
  have hpow : rk ↥A - rk ↥A₀ < 2 ^ (rk ↥A - rk ↥A₀) := Nat.lt_two_pow_self
  have h2 : (rk ↥A - rk ↥A₀) + rk ↥J ≤ 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J := by
    have h3 : (rk ↥A - rk ↥A₀ + 1) * rk ↥J ≤ 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J :=
      Nat.mul_le_mul_right _ hpow
    have h4 : rk ↥A - rk ↥A₀ ≤ (rk ↥A - rk ↥A₀) * rk ↥J := Nat.le_mul_of_pos_right _ hv
    nlinarith
  generalize 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J = P at h2 hnB
  refine ⟨J, hJY, hJ, hcomm, ?_, ?_⟩
  swap
  · rw [← hA₀]
    omega
  rw [← hA₀]
  by_contra hle
  have hj : rk ↥A = rk ↥A₀ := by omega
  apply hAY.elim
  intro a ⟨ha, y, hy, hay⟩
  have hfull : A ⊓ fixingSubgroup Γ (Y : Set Q) = A := by
    have hAp' : IsPGroup 2 ↥(A ⊓ fixingSubgroup Γ (Y : Set Q)) := hAp.to_le inf_le_left
    refine (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)
    rw [card_eq_two_pow_of_isPGroup hAp, card_eq_two_pow_of_isPGroup hAp', hcent]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have : a ∈ A ⊓ fixingSubgroup Γ (Y : Set Q) := by rw [hfull]; exact ha
  exact hay ((mem_fixingSubgroup_iff Γ).1 this.2 y hy)

end Orbit

section Restrict

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def resJ (S : Subgroup Γ) (J : Subgroup Q) (hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J) :
    ↥S →* MulAut ↥J where
  toFun s :=
    { toFun := fun j => ⟨(s : Γ) • (j : Q), hS s s.2 j j.2⟩
      invFun := fun j => ⟨(s : Γ)⁻¹ • (j : Q), hS _ (S.inv_mem s.2) j j.2⟩
      left_inv := fun j => Subtype.ext (inv_smul_smul (s : Γ) (j : Q))
      right_inv := fun j => Subtype.ext (smul_inv_smul (s : Γ) (j : Q))
      map_mul' := fun j j' => Subtype.ext (smul_mul' (s : Γ) (j : Q) j') }
  map_one' := MulEquiv.ext fun j => Subtype.ext (one_smul Γ (j : Q))
  map_mul' s s' := MulEquiv.ext fun j => Subtype.ext (mul_smul (s : Γ) s' (j : Q))

theorem resJ_apply {S : Subgroup Γ} {J : Subgroup Q} {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J}
    (s : ↥S) (j : ↥J) : ((resJ S J hS s j : ↥J) : Q) = (s : Γ) • (j : Q) :=
  rfl

theorem resJ_of_le {S S' : Subgroup Γ} {J : Subgroup Q} {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J}
    {hS' : ∀ s ∈ S', ∀ j ∈ J, s • j ∈ J} (hle : S ≤ S') (s : ↥S) :
    resJ S J hS s = resJ S' J hS' ⟨s, hle s.2⟩ :=
  MulEquiv.ext fun _ => rfl

theorem range_resJ_mono {S S' : Subgroup Γ} {J : Subgroup Q} {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J}
    {hS' : ∀ s ∈ S', ∀ j ∈ J, s • j ∈ J} (hle : S ≤ S') :
    (resJ S J hS).range ≤ (resJ S' J hS').range := by
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨s, hle s.2⟩, (resJ_of_le hle s).symm⟩

theorem map_fixV_range_resJ {S : Subgroup Γ} {J : Subgroup Q}
    {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J} :
    (fixV (resJ S J hS).range).map J.subtype = J ⊓ XMod.fixed ↥S (⊤ : Subgroup Q) := by
  ext q
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2, trivial, fun s => ?_⟩
    have := congrArg Subtype.val (hj _ ⟨s, rfl⟩)
    exact this
  · rintro ⟨hqJ, -, hq⟩
    refine ⟨⟨q, hqJ⟩, fun x hx => ?_, rfl⟩
    obtain ⟨s, rfl⟩ := hx
    exact Subtype.ext (hq s)

theorem rk_fixV_range_resJ {S : Subgroup Γ} {J : Subgroup Q}
    {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J} :
    rk ↥(fixV (resJ S J hS).range) = rk ↥(J ⊓ XMod.fixed ↥S (⊤ : Subgroup Q)) := by
  unfold rk
  rw [← map_fixV_range_resJ, Subgroup.card_map_of_injective J.subtype_injective]

theorem rk_range_resJ [Finite Γ] {S : Subgroup Γ} {J : Subgroup Q}
    {hS : ∀ s ∈ S, ∀ j ∈ J, s • j ∈ J} :
    rk ↥(resJ S J hS).range + rk ↥(S ⊓ fixingSubgroup Γ (J : Set Q)) = rk ↥S := by
  have : Finite ↥(resJ S J hS).range :=
    Finite.of_surjective _ (resJ S J hS).rangeRestrict_surjective
  have h1 := Subgroup.card_mul_index (resJ S J hS).ker
  rw [Subgroup.index_ker] at h1
  have hker : Nat.card ↥(resJ S J hS).ker = Nat.card ↥(S ⊓ fixingSubgroup Γ (J : Set Q)) := by
    have hkeq : (resJ S J hS).ker = (S ⊓ fixingSubgroup Γ (J : Set Q)).subgroupOf S := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        refine ⟨s.2, (mem_fixingSubgroup_iff Γ).2 fun j hj => ?_⟩
        have := congrArg (fun φ : MulAut ↥J => ((φ ⟨j, hj⟩ : ↥J) : Q)) h
        exact this
      · intro h
        exact MulEquiv.ext fun j => Subtype.ext ((mem_fixingSubgroup_iff Γ).1 h.2 j j.2)
    rw [hkeq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  unfold rk
  rw [← h1, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hker, add_comm]

end Restrict

section Offender

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_offender_of_ratio (hV : ∀ v : V, v ^ 2 = 1) {X B : Subgroup (MulAut V)}
    (hBX : B ≤ X) (hB : IsElemAbelian2 B) (hpos : 0 < rk ↥B)
    (hr : 3 * rkIdx (fixV B) ≤ rk ↥B) :
    (∃ F : Subgroup (MulAut V), IsFFStarOffender X F) ∧
      qOf X ≤ ((1 / 3 : ℚ) : WithTop ℚ) := by
  classical
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 b b.2)⟩
  have hVp : IsPGroup 2 V := isPGroup_two_of_sq_eq_one hV
  have hcard : ∀ C : Subgroup (MulAut V), C ≤ B →
      Nat.card ↥C * Nat.card ↥(fixV C) = 2 ^ (rk ↥C + rk ↥(fixV C)) := by
    intro C hC
    rw [card_eq_two_pow_of_isPGroup (hBp.to_le hC), card_eq_two_pow hV (fixV C), pow_add]
  have hidx : ∀ C : Subgroup (MulAut V), rk ↥(fixV C) + rkIdx (fixV C) = rk V :=
    fun C => rk_add_rkIdx (fixV C)
  have : Nonempty {C : Subgroup (MulAut V) // C ≤ B} := ⟨⟨⊥, bot_le⟩⟩
  obtain ⟨⟨E, hEB⟩, hEmax⟩ := Finite.exists_max
    (fun C : {C : Subgroup (MulAut V) // C ≤ B} => Nat.card ↥C.1 * Nat.card ↥(fixV C.1))
  have hEmax' : ∀ C : Subgroup (MulAut V), C ≤ B →
      rk ↥C + rk ↥(fixV C) ≤ rk ↥E + rk ↥(fixV E) := by
    intro C hC
    have h1 := hEmax ⟨C, hC⟩
    simp only at h1
    rw [hcard C hC, hcard E hEB] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have hBE := hEmax' B le_rfl
  have hBidx := hidx B
  have hEidx := hidx E
  have hrkE : rk ↥E ≤ rk ↥B := rk_mono hEB
  have hEne : E ≠ ⊥ := by
    intro hE
    have h1 := hEmax' ⊥ bot_le
    rw [hE] at hBE
    have hfixbot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rw [rk_bot, hfixbot, rk_top] at hBE
    omega
  have hEoff : IsFFStarOffender X E := by
    refine ⟨hEB.trans hBX, hEne, ⟨fun a ha b hb => hB.1 a (hEB ha) b (hEB hb),
      fun a ha => hB.2 a (hEB ha)⟩, fun C hC => ?_⟩
    have h1 := hEmax ⟨C, hC.trans hEB⟩
    exact h1
  obtain ⟨F, hFE, hFoff, hFq, hFcard, -, -⟩ := exists_quadratic_offender_le hV hEoff
  have hFB : F ≤ B := hFE.trans hEB
  have hFrk : rk ↥F + rk ↥(fixV F) = rk ↥E + rk ↥(fixV E) := by
    rw [hcard F hFB, hcard E hEB] at hFcard
    exact Nat.pow_right_injective le_rfl hFcard
  have hFidx := hidx F
  have hrkF : rk ↥F ≤ rk ↥E := rk_mono hFE
  refine ⟨⟨F, hFoff⟩, ?_⟩
  have hFpos : 0 < rk ↥F := by
    rcases Nat.eq_zero_or_pos (rk ↥F) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup (hBp.to_le hFB)).1 h) hFoff.2.1
    · exact h
  have h3 : 3 * rkIdx (fixV F) ≤ rk ↥F := by omega
  have hA2 : IsA2 X F := ⟨hFoff.1, hFoff.2.1, hFoff.2.2.1⟩
  refine kq_le_iff.2 ⟨F, hA2, (isQuadratic_iff_commSeries_two F).1 hFq, ?_⟩
  unfold rAV
  have hFq' : (0 : ℚ) < (rk ↥F : ℚ) := by exact_mod_cast hFpos
  rw [div_le_iff₀ hFq']
  have : (3 * rkIdx (fixV F) : ℚ) ≤ (rk ↥F : ℚ) := by exact_mod_cast h3
  linarith

end Offender

section Case9

variable {V : Type} [CommGroup V] [Finite V]

theorem case9_of_qOf_le {G L A : Subgroup (MulAut V)} (h : B42Conclusion G L A)
    (hq : qOf G ≤ ((1 / 3 : ℚ) : WithTop ℚ)) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ BinaryNaturalSL L ⊤ ⊥ n 1 := by
  have key : ∀ c : ℚ, qOf G = (c : WithTop ℚ) → c ≤ 1 / 3 := fun c hc => by
    rw [hc] at hq
    exact WithTop.coe_le_coe.1 hq
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨-, -, -, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, n, hn, hBN, -⟩ := h
    exact ⟨n, hn, hBN⟩
  · obtain ⟨-, ⟨-, -, -, h1⟩ | ⟨-, -, h1⟩⟩ := h
    · have := key _ h1; norm_num at this
    · have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this

end Case9

theorem exists_noncyclic_of_range {Γ G : Type*} [Group Γ] [Finite Γ] [Group G] [Finite G]
    {K : Subgroup Γ} (ρ : ↥K →* G) {u w : G} (hu : u ∈ ρ.range) (hw : w ∈ ρ.range)
    (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1) (huw : u * w = w * u) (hu1 : u ≠ 1)
    (hwu : w ∉ Subgroup.zpowers u) :
    ∃ P : Subgroup Γ, P ≤ K ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup G := Subgroup.closure ({u, w} : Set G) with hE
  have hS3 : ∀ x ∈ ({u, w} : Set G), x ^ 3 = 1 := by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hu3, hw3]
  have hSc : ∀ a ∈ ({u, w} : Set G), ∀ b ∈ ({u, w} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [rfl, huw, huw.symm, rfl]
  have huE : u ∈ E := Subgroup.subset_closure (Set.mem_insert u _)
  have hwE : w ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)
  have hEp : IsPGroup 3 ↥E := fun g =>
    ⟨1, Subtype.ext (by simpa using S1417.pow_eq_one_of_mem_closure_comm hS3 hSc g.2)⟩
  have hEnc : ¬ IsCyclic ↥E := by
    refine S1417.not_isCyclic_of_four_cubes (α := (⟨u, huE⟩ : ↥E)) (β := ⟨w, hwE⟩)
      (Subtype.ext (by simpa using hu3)) (Subtype.ext (by simpa using hw3))
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => ?_) (fun h => ?_) (fun h => ?_)
    · apply hwu
      have : w = 1 := congrArg Subtype.val h
      rw [this]
      exact Subgroup.one_mem _
    · apply hwu
      have : w = u := congrArg Subtype.val h
      rw [this]
      exact Subgroup.mem_zpowers u
    · apply hwu
      have : w = u⁻¹ := by simpa using congrArg Subtype.val h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
  have hEle : E ≤ ρ.range := by
    rw [hE, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    exacts [hu, hw]
  set P₀ : Subgroup ↥K := E.comap ρ with hP₀
  let ψ : ↥P₀ →* ↥E := (ρ.comp P₀.subtype).codRestrict E (fun p => p.2)
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨k, hk⟩ := hEle e.2
    refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
    show ρ k ∈ E
    rw [hk]
    exact e.2
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥P₀) := Sylow.nonempty
  set T : Sylow 3 ↥E := S.mapSurjective hψ with hT
  have hTtop : (T : Subgroup ↥E) = ⊤ :=
    (T.is_maximal' (hEp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hSsurj : Function.Surjective (ψ.comp (S : Subgroup ↥P₀).subtype) := by
    intro e
    have he : e ∈ (T : Subgroup ↥E) := by rw [hTtop]; trivial
    rw [hT, Sylow.coe_mapSurjective] at he
    obtain ⟨s, hs, rfl⟩ := he
    exact ⟨⟨s, hs⟩, rfl⟩
  have hSnc : ¬ IsCyclic ↥(S : Subgroup ↥P₀) := fun hc =>
    hEnc (isCyclic_of_surjective _ hSsurj)
  set P : Subgroup Γ := ((S : Subgroup ↥P₀).map P₀.subtype).map K.subtype with hP
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hP]
    exact (Subgroup.map_le_range _ _).trans (by rw [Subgroup.range_subtype])
  · exact (S.isPGroup'.map _).map _
  · intro hc
    have e1 := (S : Subgroup ↥P₀).equivMapOfInjective P₀.subtype P₀.subtype_injective
    have e2 := ((S : Subgroup ↥P₀).map P₀.subtype).equivMapOfInjective K.subtype
      K.subtype_injective
    exact hSnc (isCyclic_of_surjective (e1.trans e2).symm.toMonoidHom
      (e1.trans e2).symm.surjective)

section B4

variable {Γ : Type} [Group Γ] {K A₀ : Subgroup Γ}

theorem exists_mul_of_mem_sup (hAK : ∀ a ∈ A₀, ∀ k ∈ K, a * k * a⁻¹ ∈ K) {g : Γ}
    (hg : g ∈ K ⊔ A₀) : ∃ k ∈ K, ∃ a ∈ A₀, g = k * a := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, A₀.one_mem, (mul_one x).symm⟩
    · exact ⟨1, K.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, K.one_mem, 1, A₀.one_mem, (one_mul 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, a, ha, rfl⟩ := hx
    obtain ⟨k', hk', a', ha', rfl⟩ := hy
    exact ⟨k * (a * k' * a⁻¹), K.mul_mem hk (hAK a ha k' hk'), a * a', A₀.mul_mem ha ha',
      by group⟩
  | inv x _ hx =>
    obtain ⟨k, hk, a, ha, rfl⟩ := hx
    have h1 := hAK a⁻¹ (A₀.inv_mem ha) k⁻¹ (K.inv_mem hk)
    exact ⟨a⁻¹ * k⁻¹ * a⁻¹⁻¹, h1, a⁻¹, A₀.inv_mem ha, by group⟩

theorem sq_mem_of_mem_sup (hAK : ∀ a ∈ A₀, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hA2 : ∀ a ∈ A₀, a ^ 2 = 1) {g : Γ} (hg : g ∈ K ⊔ A₀) : g ^ 2 ∈ K := by
  obtain ⟨k, hk, a, ha, rfl⟩ := exists_mul_of_mem_sup hAK hg
  have h1 : (k * a) ^ 2 = k * (a * k * a⁻¹) * a ^ 2 := by rw [pow_two, pow_two]; group
  rw [h1, hA2 a ha, mul_one]
  exact K.mul_mem hk (hAK a ha k hk)

theorem sup_le_normalizer (hAK : ∀ a ∈ A₀, ∀ k ∈ K, a * k * a⁻¹ ∈ K) :
    K ⊔ A₀ ≤ Subgroup.normalizer (K : Set Γ) :=
  sup_le Subgroup.le_normalizer fun _ ha => mem_normalizer_of_conj hAK ha

variable [Finite Γ] {Q : Type} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q]
  {J : Subgroup Q}

omit [Finite Γ] in
theorem b4Hyp_resJ (hA21 : AsA21SQTKSection) (hΓ : IsQuotientOfSQTKTC Γ)
    (hQ : ∀ q : Q, q ^ 2 = 1) (hK : CFSG.IsQuasisimple ↥K)
    (hAK : ∀ a ∈ A₀, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hA2 : ∀ a ∈ A₀, a ^ 2 = 1)
    (hJ : XMod.IsIrr ↥K J) (hJc : XMod.commOf ↥K J = J) (hJK : ∀ k ∈ K, ∀ j ∈ J, k • j ∈ J)
    (hJKA : ∀ g ∈ K ⊔ A₀, ∀ j ∈ J, g • j ∈ J) :
    B4Hyp (resJ (K ⊔ A₀) J hJKA).range (resJ K J hJK).range := by
  classical
  set X := (resJ (K ⊔ A₀) J hJKA).range with hX
  set Kb := (resJ K J hJK).range with hKb
  have hKbX : Kb ≤ X := range_resJ_mono le_sup_left
  have hN := sup_le_normalizer hAK
  have hJ2 : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQ j)
  have hn : ∀ y ∈ X, ∀ l ∈ Kb, y * l * y⁻¹ ∈ Kb := by
    rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩
    have hgk : (g : Γ) * k * (g : Γ)⁻¹ ∈ K := conj_mem_of_mem_normalizer (hN g.2) k.2
    refine ⟨⟨_, hgk⟩, ?_⟩
    rw [resJ_of_le (hS' := hJKA) le_sup_left k, resJ_of_le (hS' := hJKA) le_sup_left ⟨_, hgk⟩,
      ← map_inv, ← map_mul, ← map_mul]
    rfl
  have h2 : ∀ y ∈ X, ∃ e : ℕ, y ^ 2 ^ e ∈ Kb := by
    rintro _ ⟨g, rfl⟩
    have hg2 : (g : Γ) ^ 2 ∈ K := sq_mem_of_mem_sup hAK hA2 g.2
    refine ⟨1, ⟨⟨_, hg2⟩, ?_⟩⟩
    rw [resJ_of_le (hS' := hJKA) le_sup_left ⟨_, hg2⟩, pow_one, ← map_pow]
    rfl
  have hnt : ∃ k : ↥K, (resJ K J hJK).rangeRestrict k ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : J ≤ XMod.fixed ↥K (⊤ : Subgroup Q) := by
      intro j hj
      refine ⟨trivial, fun k => ?_⟩
      have := congrArg (fun φ : ↥Kb => (((φ : MulAut ↥J) ⟨j, hj⟩ : ↥J) : Q)) (hall k)
      exact this
    have h3 := XMod.commOf_eq_bot_iff.2 h1
    rw [hJc] at h3
    exact hJ.2.1.ne' h3
  have hKbq : CFSG.IsQuasisimple ↥Kb :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hK
      (resJ K J hJK).rangeRestrict_surjective hnt
  have hirr : XMod.IsIrrSec ↥Kb (⊥ : Subgroup ↥J) ⊤ := by
    refine ⟨?_, fun S hS _ _ => ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro h
      apply hJ.2.1.ne'
      rw [eq_bot_iff]
      intro q hq
      have : (⟨q, hq⟩ : ↥J) ∈ (⊤ : Subgroup ↥J) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · have hT : XMod.IsInv ↥K (S.map J.subtype) := by
        rintro k _ ⟨s, hs, rfl⟩
        refine ⟨(resJ K J hJK k) s, hS ⟨_, k, rfl⟩ s hs, rfl⟩
      rcases hJ.2.2 _ hT bot_le (Subgroup.map_subtype_le S) with h | h
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective S J.subtype_injective).1 h
      · right
        rw [eq_top_iff]
        intro j _
        have : (j : Q) ∈ S.map J.subtype := by rw [h]; exact j.2
        obtain ⟨s, hs, he⟩ := this
        rwa [show s = j from Subtype.ext he] at hs
  have hq := B1Red.isQuasisimple_to_open hKbq
  have hO2 : CFSG.Open.pCoreOf 2 X = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hQle : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hnot : ¬ Kb ≤ CFSG.Open.pCoreOf 2 X := by
      intro hle
      have hnil := (hQ2.to_le hle).isNilpotent
      have : Group.IsPerfect ↥Kb := ⟨hq.1⟩
      have : Nontrivial ↥Kb := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact Group.IsPerfect.not_isNilpotent ↥Kb hnil
    have hcomm := B1Red.commute_of_normal_not_le hq
      (fun n hn' l hl => hn n (hQle hn') l hl)
      (fun l hl n hn' => B1Red.conj_mem_pCoreOf (hKbX hl) hn') hnot
    have hodd : Odd (Nat.card ↥(XMod.eqvAut ↥Kb ↥J)) :=
      InternalSec.odd_card_eqvAut_of_irr hJ2 hirr
        (InternalSec.exists_noncomm_of_isQuasisimple hKbq)
    rw [eq_bot_iff]
    intro q hq'
    have hqe : q ∈ XMod.eqvAut ↥Kb ↥J := by
      intro a p
      exact congrArg (fun f : MulAut ↥J => f p) (hcomm q hq' a a.2)
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq'⟩
    have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥Kb ↥J)) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥Kb ↥J)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
      (orderOf_dvd_natCard _)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (orderOf_eq_one_iff.1 hord))
  have hgf : CFSG.Open.quasithinGenFitting X = Kb :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hKbX hn hq h2 hO2
  have hsqtk : SQTKGroup ↥X := by
    obtain ⟨S, _, _, hSQT, hKS, φ, hφ⟩ := hΓ
    have hS : SQTKGroup S := ⟨hSQT, hKS⟩
    set H : Subgroup S := (K ⊔ A₀).comap φ with hH
    let π : ↥H →* ↥X := (resJ (K ⊔ A₀) J hJKA).rangeRestrict.comp
      ((φ.comp H.subtype).codRestrict (K ⊔ A₀) fun h => h.2)
    have hπ : Function.Surjective π := by
      rintro ⟨_, ⟨g, rfl⟩⟩
      obtain ⟨s, hs⟩ := hφ g
      refine ⟨⟨s, show φ s ∈ K ⊔ A₀ by rw [hs]; exact g.2⟩, ?_⟩
      apply Subtype.ext
      show resJ (K ⊔ A₀) J hJKA ⟨φ s, _⟩ = resJ (K ⊔ A₀) J hJKA g
      congr 1
      exact Subtype.ext hs
    set Lb : Subgroup ↥X := Kb.subgroupOf X with hLb
    have hLbn : Lb.Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hn g g.2 x hx⟩
    have hLq : CFSG.IsQuasisimple ↥Lb :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKbX).symm hKbq
    have hlayer : CFSG.layer ↥Lb = ⊤ := B5.layer_eq_top_of_quasisimple hLq
    have h2' : IsPGroup 2 (↥X ⧸ Lb) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨e, he⟩ := h2 y y.2
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact he
    exact hA21 S hS H ↥X π hπ Lb hlayer h2'
  exact ⟨hsqtk, hgf.symm, hKbq, hirr⟩

end B4

theorem isQuotientOfSQTKTC_subgroup {X : Type*} [Group X] (hX : IsQuotientOfSQTKTC X)
    (H : Subgroup X) : IsQuotientOfSQTKTC ↥H := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hX
  refine ⟨↥(H.comap φ), inferInstance, inferInstance, fun q hq hq2 => ?_, hK.subgroup _,
    (φ.comp (H.comap φ).subtype).codRestrict H (fun s => s.2), fun h => ?_⟩
  · exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt _
      (H.comap φ).subtype_injective).trans (hSQT q hq hq2)
  · obtain ⟨s, hs⟩ := hφ h
    exact ⟨⟨s, show φ s ∈ H by rw [hs]; exact h.2⟩, Subtype.ext hs⟩

theorem isQuotientOfSQTKTC_of_le {G : Type*} [Group G] {M H : Subgroup G}
    (hM : IsQuotientOfSQTKTC ↥M) (hHM : H ≤ M) : IsQuotientOfSQTKTC ↥H := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := isQuotientOfSQTKTC_subgroup hM (H.subgroupOf M)
  exact ⟨S, inferInstance, inferInstance, hSQT, hK,
    (Subgroup.subgroupOfEquivOfLe hHM).toMonoidHom.comp φ,
    (Subgroup.subgroupOfEquivOfLe hHM).surjective.comp hφ⟩

theorem exists_noncyclic_three_of_clif (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : IsQuotientOfSQTKTC Γ)
    {Q : Type} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {K A : Subgroup Γ} (hK : CFSG.IsQuasisimple ↥K)
    (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {Y : Subgroup Q} (hY : XMod.IsIrr ↥(K ⊔ A) Y)
    (hKY : ∃ k ∈ K, ∃ y ∈ Y, k • y ≠ y) (hAY : ∃ a ∈ A, ∃ y ∈ Y, a • y ≠ y)
    (hr : 3 * nB A Y ≤ rk ↥A - rk ↥(A ⊓ fixingSubgroup Γ (Y : Set Q))) :
    ∃ P : Subgroup Γ, P ≤ K ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P := by
  classical
  obtain ⟨J, -, hJ, hJc, hpos, hrat⟩ := exists_irr_small hQ hAK hAc hA2 hY hKY hAY hr
  have hstab : ∀ a ∈ stabIn A J, a • J = J := fun a ha => (mem_stabIn.1 ha).2
  have hA₀A : stabIn A J ≤ A := inf_le_left
  generalize stabIn A J = A₀ at hpos hrat hstab hA₀A
  have hAK₀ : ∀ a ∈ A₀, ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun a ha => hAK a (hA₀A ha)
  have hA2₀ : ∀ a ∈ A₀, a ^ 2 = 1 := fun a ha => hA2 a (hA₀A ha)
  have hJK : ∀ k ∈ K, ∀ j ∈ J, k • j ∈ J := fun k hk j hj => hJ.1 ⟨k, hk⟩ j hj
  have hJA₀ : ∀ a ∈ A₀, ∀ j ∈ J, a • j ∈ J := by
    intro a ha j hj
    rw [← hstab a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hj
  have hJKA : ∀ g ∈ K ⊔ A₀, ∀ j ∈ J, g • j ∈ J := fun g hg j hj =>
    smul_mem_of_mem_sup (A := K) (Λ := A₀) hJK hJA₀ hg j hj
  have hB4 := b4Hyp_resJ hA21 hΓ hQ hK hAK₀ hA2₀ hJ hJc hJK hJKA
  have hJ2 : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQ j)
  have hAbX : (resJ A₀ J hJA₀).range ≤ (resJ (K ⊔ A₀) J hJKA).range :=
    range_resJ_mono le_sup_right
  have hAbel : IsElemAbelian2 (resJ A₀ J hJA₀).range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc a (hA₀A a.2) b (hA₀A b.2))
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by simpa using hA2₀ a a.2)
      rw [this, map_one]
  have hrkAb := rk_range_resJ (S := A₀) (J := J) (hS := hJA₀)
  have hfixAb := rk_fixV_range_resJ (S := A₀) (J := J) (hS := hJA₀)
  have hidx := rk_add_rkIdx (fixV (resJ A₀ J hJA₀).range)
  have hpos' : 0 < rk ↥(resJ A₀ J hJA₀).range := by omega
  have hratio : 3 * rkIdx (fixV (resJ A₀ J hJA₀).range) ≤ rk ↥(resJ A₀ J hJA₀).range := by
    unfold nB at hrat
    have h1 : rk ↥(J ⊓ XMod.fixed ↥A₀ (⊤ : Subgroup Q)) ≤ rk ↥J := rk_mono inf_le_left
    omega
  obtain ⟨⟨F, hF⟩, hqle⟩ := exists_offender_of_ratio hJ2 hAbX hAbel hpos' hratio
  have hconcl := hB42 ↥J hJ2 _ _ hB4 F hF
  obtain ⟨n, hn, hBN⟩ := case9_of_qOf_le hconcl hqle
  obtain ⟨u, hu, w, hw, hu3, hw3, huw, hu1, hwu⟩ := exists_e9_of_binaryNaturalSL45 hn hBN
  exact exists_noncyclic_of_range (resJ K J hJK) hu hw hu3 hw3 huw hu1 hwu

end CFSG.Quasithin.SmithD39Two
