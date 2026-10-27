module

public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
import CFSG.GroupTheory.SupCommute
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
import CFSG.RankThree.GF2n.Tim79a34CXW
import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.GF2n.Stroth80
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
  {C : Subgroup G}

private theorem wOf_sup_elemAbelian [Finite G] (h : BigEndHyp M V Q P H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hCel : Assembly.IsElemAbelian 2 C) : Assembly.IsElemAbelian 2 (wOf V H ⊔ C) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  refine IsElemAbelian.sup_of_commute hc.wOf_isElemAbelian hCel ?_
  intro w hw c hc'
  exact (hCW c hc' w hw).symm

private theorem wOf_sup_normalizer [Finite G] (h : BigEndHyp M V Q P H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) :
    xOf V H ≤ Subgroup.normalizer ((wOf V H ⊔ C : Subgroup G) : Set G) ∧
      (∀ x ∈ xOf V H, ∀ y ∈ wOf V H ⊔ C, ⁅x, y⁆ ∈ wOf V H) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hXnormW : xOf V H ≤ Subgroup.normalizer (wOf V H : Set G) :=
    (xOf_le_H hVH).trans (H_le_normalizer_wOf V H)
  have hmem : ∀ y : G, y ∈ wOf V H ⊔ C ↔ ∃ w ∈ wOf V H, ∃ c ∈ C, w * c = y :=
    fun y => CFSG.mem_sup_of_commute (fun w hw c hc' => (hCW c hc' w hw).symm)
  have hnorm : xOf V H ≤ Subgroup.normalizer ((wOf V H ⊔ C : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨w, hw, c, hc', rfl⟩ := (hmem y).mp hy
    have hw' : x * w * x⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (hXnormW hx) w).mp hw
    have hcomm : x * c * x⁻¹ = ⁅x, c⁆ * c := by
      rw [commutatorElement_def]
      group
    have hprod : (x * w * x⁻¹) * (x * c * x⁻¹) ∈ wOf V H ⊔ C := by
      rw [hcomm, ← mul_assoc]
      exact Subgroup.mul_mem_sup ((wOf V H).mul_mem hw' (hXC c hc' x hx)) hc'
    have e : x * (w * c) * x⁻¹ = (x * w * x⁻¹) * (x * c * x⁻¹) := by group
    rw [e]
    exact hprod
  refine ⟨hnorm, ?_⟩
  intro x hx y hy
  obtain ⟨w, hw, c, hc', rfl⟩ := (hmem y).mp hy
  have hw' : x * w * x⁻¹ ∈ wOf V H :=
    (Subgroup.mem_normalizer_iff.mp (hXnormW hx) w).mp hw
  have hcomm : ⁅x, w * c⁆ = (x * w * x⁻¹) * ⁅x, c⁆ * w⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hcomm]
  exact (wOf V H).mul_mem ((wOf V H).mul_mem hw' (hXC c hc' x hx)) ((wOf V H).inv_mem hw)

private theorem wOf_sup_invariant_inf [Finite G] (h : BigEndHyp M V Q P H)
    (hirrW : ∀ S : Subgroup G, S ≤ wOf V H →
      (∀ x ∈ xOf V H, ∀ s ∈ S, x * s * x⁻¹ ∈ S) → S = ⊥ ∨ S = wOf V H)
    {A : Subgroup G} (hconj : ∀ r ∈ xOf V H, conjSubgroup r A = A) :
    A ⊓ wOf V H = ⊥ ∨ A ⊓ wOf V H = wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hXnormW : xOf V H ≤ Subgroup.normalizer (wOf V H : Set G) :=
    (xOf_le_H hVH).trans (H_le_normalizer_wOf V H)
  refine hirrW (A ⊓ wOf V H) inf_le_right ?_
  intro x hx s hs
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [← hconj x hx]
    exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using hs.1)
  · exact (Subgroup.mem_normalizer_iff.mp (hXnormW hx) s).mp hs.2

private theorem wOf_sup_eq_bot_of_inf_bot [Finite G] (h : BigEndHyp M V Q P H)
    {C : Subgroup G} (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H)
    (hCX : ∀ z : G, (∀ x ∈ xOf V H, z * x = x * z) → z = 1)
    {A : Subgroup G} (hA : A ≤ wOf V H ⊔ C)
    (hconj : ∀ r ∈ xOf V H, conjSubgroup r A = A) (hbot : A ⊓ wOf V H = ⊥) :
    A = ⊥ := by
  obtain ⟨-, hXcomW₁⟩ := wOf_sup_normalizer (M := M) (V := V) (Q := Q) (P := P)
    (H := H) (C := C) h hCW hXC
  rw [eq_bot_iff]
  intro a ha
  have hcomm : ∀ x ∈ xOf V H, a * x = x * a := by
    intro x hx
    have hcA : x * a * x⁻¹ ∈ A := by
      rw [← hconj x hx]
      exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using ha)
    have hcAW : ⁅x, a⁆ ∈ wOf V H := hXcomW₁ x hx a (hA ha)
    have hcAA : ⁅x, a⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem hcA (A.inv_mem ha)
    have h1 : ⁅x, a⁆ = 1 := by
      have hmem : ⁅x, a⁆ ∈ A ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨hcAA, hcAW⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h2 : x * a = a * x := by
      rw [commutatorElement_eq_one_iff_commute] at h1
      exact h1.eq
    exact h2.symm
  exact Subgroup.mem_bot.mpr (hCX a hcomm)

private theorem wOf_sup_indecomposable [Finite G] (h : BigEndHyp M V Q P H)
    {C : Subgroup G} (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H)
    (hCX : ∀ z : G, (∀ x ∈ xOf V H, z * x = x * z) → z = 1)
    (hirrW : ∀ S : Subgroup G, S ≤ wOf V H →
      (∀ x ∈ xOf V H, ∀ s ∈ S, x * s * x⁻¹ ∈ S) → S = ⊥ ∨ S = wOf V H) :
    IsIndecSec (xOf V H) (wOf V H ⊔ C) ⊥ := by
  have hWne : wOf V H ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(V ⊓ wOf V H) = 1 := by
      rw [hbot, inf_bot_eq]
      simp
    have h2 : qBar V H = 1 := by rw [← h.module, h1]
    have h3 : 4 ≤ (1 : ℕ) := h2 ▸ h.q_big
    norm_num at h3
  rintro ⟨A₁, A₂, -, hA₁, -, hA₂, hA₁ne, hA₂ne, -, hinf, hinv⟩
  have hdec₁ := wOf_sup_invariant_inf h hirrW (fun r hr => (hinv r hr).1)
  have hdec₂ := wOf_sup_invariant_inf h hirrW (fun r hr => (hinv r hr).2)
  rcases hdec₁ with h₁ | h₁
  · exact hA₁ne (wOf_sup_eq_bot_of_inf_bot h hCW hXC hCX hA₁
      (fun r hr => (hinv r hr).1) h₁)
  · rcases hdec₂ with h₂ | h₂
    · exact hA₂ne (wOf_sup_eq_bot_of_inf_bot h hCW hXC hCX hA₂
        (fun r hr => (hinv r hr).2) h₂)
    · have hle₁ : wOf V H ≤ A₁ := h₁ ▸ inf_le_left
      have hle₂ : wOf V H ≤ A₂ := h₂ ▸ inf_le_left
      have hle : wOf V H ≤ (⊥ : Subgroup G) := by
        rw [← hinf]
        exact le_inf hle₁ hle₂
      exact hWne (le_antisymm hle bot_le)

private theorem wOf_sup_secHyp [Finite G] (h : BigEndHyp M V Q P H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H)
    (hCel : Assembly.IsElemAbelian 2 C) :
    SecHyp (xOf V H) (wOf V H ⊔ C) ⊥ ∧
      (∀ n ∈ wOf V H, ∀ y ∈ wOf V H ⊔ C, ⁅n, y⁆ ∈ (⊥ : Subgroup G)) := by
  obtain ⟨hXnormW₁, -⟩ := wOf_sup_normalizer (M := M) (V := V) (Q := Q) (P := P)
    (H := H) (C := C) h hCW hXC
  have helem := wOf_sup_elemAbelian (M := M) (V := V) (Q := Q) (P := P) (H := H)
    (C := C) h hCW hCel
  have hsec : SecHyp (xOf V H) (wOf V H ⊔ C) ⊥ := by
    refine ⟨bot_le, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_def, helem.comm hx hy]
      group
    · intro x hx
      rw [Subgroup.mem_bot, pow_two]
      exact helem.mul_self_eq_one hx
    · intro r hr y hy
      exact (Subgroup.mem_normalizer_iff.mp (hXnormW₁ hr) y).mp hy
    · intro r hr y hy
      rw [Subgroup.mem_bot] at hy ⊢
      rw [hy]
      group
  refine ⟨hsec, ?_⟩
  intro n hn y hy
  rw [Subgroup.mem_bot, commutatorElement_def, helem.comm (Subgroup.mem_sup_left hn) hy]
  group

private theorem natural_range_ker [Finite G] (hVH : V ≤ H)
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H) :
    let K := GaloisField 2 f
    let φ : ↥(xOf V H) →* GL (Fin n ⊕ Fin n) K :=
      (StatedSp n K).subtype.comp (Φ.symm.toMonoidHom.comp (xToXbar hVH))
    φ.range = StatedSp n K ∧ φ.ker = (wOf V H).subgroupOf (xOf V H) := by
  intro K φ
  have hrange : φ.range = StatedSp n K := by
    dsimp only [φ]
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (xToXbar_surjective hVH), Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (MulEquiv.surjective Φ.symm), Subgroup.map_top,
      Subgroup.range_subtype]
  refine ⟨hrange, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have h1 : Φ.symm (xToXbar hVH x) = 1 := Subtype.ext hx
    have h2 : xToXbar hVH x = 1 := Φ.symm.injective (by simpa using h1)
    exact (cxw_xToXbar_eq_one hVH x).mp h2
  · intro hx
    have h1 : xToXbar hVH x = 1 := (cxw_xToXbar_eq_one hVH x).mpr hx
    have h2 : Φ.symm (xToXbar hVH x) = 1 := by rw [h1]; exact map_one _
    change ((StatedSp n K).subtype (Φ.symm (xToXbar hVH x)) : GL (Fin n ⊕ Fin n) K) = 1
    rw [h2]
    rfl

private theorem nat_sectionAct_iso
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)) :
    ∃ eW : ↥(wOf V H) ⧸ (⊥ : Subgroup G).subgroupOf (wOf V H) ≃*
        Multiplicative (Fin n ⊕ Fin n → GaloisField 2 f),
      ∀ v : ↥(wOf V H),
        Multiplicative.toAdd (eW (QuotientGroup.mk v)) = ψ.symm (Additive.ofMul v) := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (wOf V H))).trans
      (QuotientGroup.quotientBot.trans (ψ.symm.toMultiplicative)), ?_⟩
  intro v
  dsimp only [MulEquiv.trans_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  change Multiplicative.toAdd ((ψ.symm.toMultiplicative)
    (Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.quotientBot (QuotientGroup.mk v : ↥(wOf V H) ⧸ ⊥))))) =
    ψ.symm (Additive.ofMul v)
  rw [show QuotientGroup.quotientBot (QuotientGroup.mk v : ↥(wOf V H) ⧸ ⊥) = v from rfl]
  rw [AddEquiv.toMultiplicative_apply_apply]
  rfl

private theorem nat_sectionAct (hVH : V ≤ H)
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
    (hNat : BigNatCfg V H hVH Φ ψ) :
    SectionAct (GaloisField 2 f) (xOf V H) (wOf V H) ⊥
      ((StatedSp n (GaloisField 2 f)).subtype.comp (Φ.symm.toMonoidHom.comp (xToXbar hVH)))
      (fun g => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
  let K := GaloisField 2 f
  let φ : ↥(xOf V H) →* GL (Fin n ⊕ Fin n) K :=
    (StatedSp n K).subtype.comp (Φ.symm.toMonoidHom.comp (xToXbar hVH))
  have hnorm : xOf V H ≤ Subgroup.normalizer (wOf V H : Set G) :=
    (xOf_le_H hVH).trans (H_le_normalizer_wOf V H)
  obtain ⟨eW, heW⟩ := nat_sectionAct_iso (n := n) (f := f) ψ
  refine ⟨hnorm, inferInstance, eW, ?_⟩
  intro s v w hw
  rw [heW w, heW v]
  have hmat : ((φ s : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      SpExtras.mat n K (Φ.symm (xToXbar hVH s)) := rfl
  change ψ.symm (Additive.ofMul w) =
    ((φ s : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      ψ.symm (Additive.ofMul v)
  rw [hmat]
  apply ψ.injective
  rw [AddEquiv.apply_symm_apply]
  have h := hNat.equiv s (ψ.symm (Additive.ofMul v))
  have hcoord : ((Additive.toMul (ψ (ψ.symm (Additive.ofMul v))) : ↥(wOf V H)) : G) =
      (v : G) := by
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [hcoord] at h
  have h2 : (Additive.toMul (ψ (SpExtras.mat n K (Φ.symm (xToXbar hVH s)) *ᵥ
      ψ.symm (Additive.ofMul v))) : ↥(wOf V H)) = w := by
    apply Subtype.ext
    rw [h, hw]
  rw [← h2]
  rfl

private theorem card_sup_le_q_mul [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {C : Subgroup G}
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) (hCel : Assembly.IsElemAbelian 2 C)
    (hCX : ∀ z : G, (∀ x ∈ xOf V H, z * x = x * z) → z = 1)
    (hirrW : ∀ S : Subgroup G, S ≤ wOf V H →
      (∀ x ∈ xOf V H, ∀ s ∈ S, x * s * x⁻¹ ∈ S) → S = ⊥ ∨ S = wOf V H) :
    Nat.card ↥(wOf V H ⊔ C) ≤ qBar V H * Nat.card ↥(wOf V H) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, f, Φ, ψ, hn, hf, hequiv, ⟨_, _, _, _, _⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  have hf0 : f ≠ 0 := by
    intro hq
    have h1 : 2 ^ f = 1 := by rw [hq, pow_zero]
    have hqb : 4 ≤ qBar V H := h.q_big
    rw [← hf, h1] at hqb
    omega
  have hKcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hKbig : 2 < Nat.card (GaloisField 2 f) := by
    rw [hKcard]
    exact lt_of_lt_of_le (by norm_num) h.q_big
  have hsec := (wOf_sup_secHyp (M := M) (V := V) (Q := Q) (P := P) (H := H) (C := C)
    h hCW hXC hCel).1
  have hNsec := (wOf_sup_secHyp (M := M) (V := V) (Q := Q) (P := P) (H := H) (C := C)
    h hCW hXC hCel).2
  have hXcomW₁ := (wOf_sup_normalizer (M := M) (V := V) (Q := Q) (P := P) (H := H) (C := C)
    h hCW hXC).2
  have hind := wOf_sup_indecomposable (M := M) (V := V) (Q := Q) (P := P) (H := H) (C := C)
    h hCW hXC hCX hirrW
  let K := GaloisField 2 f
  let φ : ↥(xOf V H) →* GL (Fin n ⊕ Fin n) K :=
    (StatedSp n K).subtype.comp (Φ.symm.toMonoidHom.comp (xToXbar hVH))
  obtain ⟨hφrange, hφker⟩ := natural_range_ker (n := n) (f := f) (V := V) (H := H) hVH Φ
  have hact := nat_sectionAct (n := n) (f := f) (V := V) (H := H) hVH Φ ψ hNat
  have hcardW : Nat.card ↥(wOf V H ⊔ C) ≤ Nat.card K * Nat.card ↥(wOf V H) :=
    stroth_2_2_secSp (m := n) (Z := ⊥) (V := wOf V H) (R := xOf V H)
      (N := wOf V H) (P := wOf V H ⊔ C) hn hKbig φ hφrange hφker hsec hNsec
      bot_le le_sup_left hact hXcomW₁ hind
  rwa [hKcard] at hcardW

theorem BigEndHyp.relIndex_le_qBar [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {C : Subgroup G} (hQPC : P ⊔ C = Q)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c)
    (hXC : ∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) (hCel : Assembly.IsElemAbelian 2 C)
    (hCWP : C ⊓ wOf V H ≤ P) (hCX : ∀ z : G, (∀ x ∈ xOf V H, z * x = x * z) → z = 1)
    (hirrW : ∀ S : Subgroup G, S ≤ wOf V H → (∀ x ∈ xOf V H, ∀ s ∈ S, x * s * x⁻¹ ∈ S) →
      S = ⊥ ∨ S = wOf V H) :
    P.relIndex Q ≤ qBar V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hcardW := card_sup_le_q_mul h hZ hCW hXC hCel hCX hirrW
  have hPQ : P ≤ Q := hQPC ▸ le_sup_left
  have hCQ : C ≤ Q := hQPC ▸ le_sup_right
  have hQM : Q ≤ M := hc.Q_le_M
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) := hQM.trans hc.M_le_normalizer_P
  have hCnormP : C ≤ Subgroup.normalizer (P : Set G) := hCQ.trans hQnormP
  have hrelPQ : P.relIndex Q = (P ⊓ C).relIndex C := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := C) (K := P) hCnormP).2
    rwa [sup_comm, hQPC, inf_comm] at h
  have hWC : wOf V H ≤ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro c hc'
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hCW c hc' w hw).symm
  have hWnormC : wOf V H ≤ Subgroup.normalizer (C : Set G) :=
    hWC.trans (Subgroup.centralizer_le_normalizer (C : Set G))
  have hrelWW₁ : (wOf V H).relIndex (wOf V H ⊔ C) = (C ⊓ wOf V H).relIndex C := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := wOf V H) (K := C) hWnormC).1
    rwa [inf_comm] at h
  have hleWP : C ⊓ wOf V H ≤ C ⊓ P := le_inf inf_le_left hCWP
  have hle : (P ⊓ C).relIndex C ≤ (C ⊓ wOf V H).relIndex C := by
    rw [inf_comm]
    exact Subgroup.relIndex_le_of_le_left hleWP (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  have hrel_le_q : (wOf V H).relIndex (wOf V H ⊔ C) ≤ qBar V H := by
    have hmul := Subgroup.relIndex_mul_card (wOf V H) (wOf V H ⊔ C)
    rw [inf_eq_left.mpr le_sup_left] at hmul
    have h1 : (wOf V H).relIndex (wOf V H ⊔ C) * Nat.card ↥(wOf V H) ≤
        qBar V H * Nat.card ↥(wOf V H) := by
      rw [hmul]
      exact hcardW
    exact Nat.le_of_mul_le_mul_right h1 (Nat.card_pos (α := ↥(wOf V H)))
  calc P.relIndex Q = (P ⊓ C).relIndex C := hrelPQ
    _ ≤ (C ⊓ wOf V H).relIndex C := hle
    _ = (wOf V H).relIndex (wOf V H ⊔ C) := hrelWW₁.symm
    _ ≤ qBar V H := hrel_le_q

end CFSG.RankThree.GF2n.Tim79a
