module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item143Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def KL3SigmaAutE9 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (r f : ℕ) [Fact r.Prime], r ≠ 3 → 1 ≤ f →
    IsLThreeEpsAt Q r f → ¬ Sec4.IsoLThreePi Q r f →
    ∀ E : Subgroup (MulAut Q), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∃ e ∈ E, e ≠ 1 ∧ ∃ H : Subgroup Q, (∀ x ∈ H, e x = x) ∧ ¬ Group.IsSolvable ↥H

@[expose] noncomputable def KS158CentSolvR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    Sec8.IsZ3PGLThreePi (lBarA c L A) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
    ∀ a ∈ A, a ∉ Subgroup.zpowers c →
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({a} : Set G))

namespace Proof15Res6

section Fixed

theorem exists_fixedPoint_of_iterate_eq_id' {S : Type*} [Finite S] {p : ℕ} (hp : p.Prime)
    (φ : S → S) (hφ : φ^[p] = id) (hS : ¬ p ∣ Nat.card S) : ∃ s, φ s = s := by
  classical
  have := Fintype.ofFinite S
  have : Fact p.Prime := ⟨hp⟩
  let f : Function.End S := φ
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact hφ
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  by_contra hno
  have h0 : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨s, hs⟩ => hno ⟨s, hs⟩⟩
  rw [h0] at h
  apply hS
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.mp h)

variable {I' P : Type*} [Group I'] [Group P]

theorem card_fibre' (ψ : I' →* P) (y₀ : I') :
    Nat.card {y : I' // ψ y = ψ y₀} = Nat.card ψ.ker :=
  Nat.card_congr
    { toFun := fun y => ⟨y₀⁻¹ * y.1, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, y.2, inv_mul_cancel]⟩
      invFun := fun k => ⟨y₀ * k.1, by
        rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }

theorem exists_fixed_lift' [Finite I'] {p : ℕ} (hp : p.Prime) (ψ : I' →* P)
    (hψ : Function.Surjective ψ) (hnd : ¬ p ∣ Nat.card ψ.ker) (σ : MulAut I') (hσp : σ ^ p = 1)
    (β : MulAut P) (hσβ : ∀ y, ψ (σ y) = β (ψ y)) {t : P} (ht : β t = t) :
    ∃ y : I', σ y = y ∧ ψ y = t := by
  obtain ⟨y₀, rfl⟩ := hψ t
  let φ : {y : I' // ψ y = ψ y₀} → {y : I' // ψ y = ψ y₀} :=
    fun s => ⟨σ s.1, by rw [hσβ, s.2, ht]⟩
  have hiter : ∀ (n : ℕ) (s : {y : I' // ψ y = ψ y₀}), (φ^[n] s).1 = (σ ^ n) s.1 := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih s]
  have hφ : φ^[p] = id := by
    funext s
    apply Subtype.ext
    rw [hiter, hσp]
    rfl
  obtain ⟨s, hs⟩ := exists_fixedPoint_of_iterate_eq_id' hp φ hφ (by rwa [card_fibre'])
  exact ⟨s.1, congrArg Subtype.val hs, s.2⟩

end Fixed

end Proof15Res6

section Prover


theorem step158InnerSigmaR_of_kfacts (h134 : Item134) (h48 : Sec4.Item4_8)
    (hK1 : KL3SigmaAutE9) (hK2 : KS158CentSolvR) : Step158InnerSigmaR := by
  intro G _ _ A c L hR p e _ he hL3 hPGL htype X hX hXL r f e' _ hf he' hiso hε hpi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h14 := hR.toSec14Std
  have hNHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty h14 (Proof15Res6.isEmpty_j2_of_isoLThreePi hL3)
  have hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ :=
    fun B hB => lB_eq_bot_of_not_allPointsHJ' h134 h48 h14 hNHJ hB
  have hA := hR.isElemAbelian
  have hA27 := hR.card_eq
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp h14.zpowers_mem_omegaA
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have hr3 : r ≠ 3 := by
    rintro rfl
    have h0 : 3 ^ (f * e') % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (Nat.mul_pos hf he').ne')
    rcases hiso with ⟨h1, -⟩ | ⟨h2, -⟩ <;> omega
  have hcX : ∀ x ∈ X, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt h14.mem_lA.1 (hXL hx))
  set N := CFSG.pPrimeCore 3 ↥X with hN
  set ρ : ↥A →* MulAut (↥X ⧸ N) :=
    (quotMulAut N).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)) with hρ
  have hρc : ρ ⟨c, hcA⟩ = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.one_apply]
      change ((X.normalizerMonoidHom ⟨c, hAX hcA⟩ x : ↥X) : ↥X ⧸ N) = (x : ↥X ⧸ N)
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change c * (x : G) * c⁻¹ = x
      rw [← hcX x x.2, mul_inv_cancel_right]
  have hX3 : 3 ∣ Nat.card X :=
    (Proof1515.three_dvd_card_of_mem_scriptY4 hX).trans (Subgroup.card_quotient_dvd_card _)
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hN3' : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
  have hcT : c ∈ Proof15Res6.actTriv X (pPrimeCoreOf 3 X) := by
    refine ⟨(hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) hcA, fun x hx => ?_⟩
    have heq : ⁅x, c⁆ = 1 := by
      rw [commutatorElement_def, hcX x hx]
      group
    rw [heq]
    exact one_mem _
  have hker : ∀ a : ↥A, ρ a = 1 → (a : G) ∈ Subgroup.zpowers c := by
    intro a ha
    have haT : (a : G) ∈ Proof15Res6.actTriv X (pPrimeCoreOf 3 X) := by
      refine ⟨(hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) a.2, fun x hx => ?_⟩
      set x' : ↥X := ⟨x, hx⟩ with hx'
      set σ := X.normalizerMonoidHom ⟨(a : G), hAX a.2⟩ with hσ
      have h1 : ((x'⁻¹ : ↥X) : ↥X ⧸ N) = ((σ x'⁻¹ : ↥X) : ↥X ⧸ N) := by
        have h2 := congrArg (fun τ : MulAut (↥X ⧸ N) => τ ((x'⁻¹ : ↥X) : ↥X ⧸ N)) ha
        simp only [MulAut.one_apply] at h2
        exact h2.symm
      rw [QuotientGroup.eq, inv_inv] at h1
      refine ⟨x' * σ x'⁻¹, h1, ?_⟩
      change (x : G) * ((a : G) * x⁻¹ * (a : G)⁻¹) = ⁅x, (a : G)⁆
      rw [commutatorElement_def]
      group
    exact Proof15Res6.mem_zpowers_of_mem_actTriv hA hA27 hLB hX.2.2.1
      (le_normalizer_pPrimeCoreOf 3 X) hN3' hX3 hcA a.2 hc1 hcT haT
  have hkerEq : ρ.ker = (Subgroup.zpowers c).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · exact hker a
    · intro ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hak : a = (⟨c, hcA⟩ : ↥A) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [hak, map_zpow, hρc, one_zpow]
  have hkcard : Nat.card ρ.ker = 3 := by
    rw [hkerEq, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcA)).toEquiv]
    exact hc3
  have hcard : Nat.card ρ.range = 9 := by
    have h : Nat.card ρ.range * Nat.card ρ.ker = 27 := by
      rw [← hA27, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker).symm
    rw [hkcard] at h
    omega
  have hAtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup ↥A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext (hA.2 a a.2)⟩
    exact congrArg Subtype.val (hA.1.is_comm.comm (a : ↥A) (b : ↥A))
  have hEab : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact isElemAbelian_map_hom hAtop ρ
  obtain ⟨β, hβ, hβ1, H, hHfix, hHns⟩ :=
    hK1 (↥X ⧸ N) r f hr3 hf hε hpi ρ.range hEab hcard
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hβ
  have ha : (a : G) ∉ Subgroup.zpowers c := by
    intro hac
    apply hβ1
    have h1 : a ∈ ρ.ker := by
      rw [hkerEq, Subgroup.mem_subgroupOf]
      exact hac
    exact MonoidHom.mem_ker.mp h1
  set σ := X.normalizerMonoidHom ⟨(a : G), hAX a.2⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨(a : G), hAX a.2⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA.2 a a.2)
    rw [h1, map_one]
  have hHle : H ≤ ((X ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' N) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Proof15Res6.exists_fixed_lift' Nat.prime_three
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact hN3) σ hσ3 (ρ a) (fun y => rfl) (hHfix t ht)
    refine ⟨y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨y.2, ?_⟩
    have h1 : ((σ y : ↥X) : G) = (y : G) := congrArg Subtype.val hy
    rw [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    change (a : G) * (y : G) * (a : G)⁻¹ = y at h1
    show (y : G) ∈ Subgroup.centralizer ({(a : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : G) * a = (a : G) * (y : G) * (a : G)⁻¹ * a := by rw [h1]
      _ = a * y := by group
  have hK := hK2 G A c L hR p e he hL3 hPGL htype (a : G) a.2 ha
  apply hHns
  have hle : X ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≤
      L ⊓ Subgroup.centralizer ({(a : G)} : Set G) := inf_le_inf_right _ hXL
  have h1 : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ({(a : G)} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have h2 : Group.IsSolvable
      ↥((X ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf X) := by
    set e₂ := Subgroup.subgroupOfEquivOfLe
      (inf_le_left : X ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≤ X) with he₂
    exact Group.isSolvable_of_isSolvable_injective (f := e₂.toMonoidHom) e₂.injective
  have h3 : Group.IsSolvable ↥(((X ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' N)) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHle)

end Prover

section Consumers


theorem step158InnerRank_of_kfacts (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hK1 : KL3SigmaAutE9) (hK2 : KS158CentSolvR) : Step158InnerRank :=
  step158InnerRank_of_res6 h134 h48 h148 (step158InnerSigmaR_of_kfacts h134 h48 hK1 hK2)

theorem item158Y0R_of_kfacts
    (h131 : Item131) (h138 : Item138N) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) (hK1 : KL3SigmaAutE9) (hK2 : KS158CentSolvR) (hC : Step158CartanP) :
    Item158Y0R :=
  item158Y0R_of_res6 h131 h138 h134 h48 h148 (step158InnerSigmaR_of_kfacts h134 h48 hK1 hK2) hC

end Consumers

end CFSG.RankThree.PartTwo.Sec15
