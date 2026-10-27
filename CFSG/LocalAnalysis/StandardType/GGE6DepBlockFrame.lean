module

public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Prime.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private lemma ggPow3_eq_one (Bs : Subgroup G) (hBs : IsElemAbelian 3 Bs) (x : ↥Bs) :
    x ^ 3 = 1 := by
  apply Subtype.ext
  simpa using hBs.2 (x : G) x.2

private def ggFixSub {B : Type*} [Group B] (φ : MulAut B) : Subgroup B where
  carrier := {b | φ b = b}
  one_mem' := map_one φ
  mul_mem' := by
    intro a b ha hb
    show φ (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    show φ a⁻¹ = a⁻¹
    rw [map_inv, ha]

private lemma mem_ggFixSub {B : Type*} [Group B] {φ : MulAut B} {b : B} :
    b ∈ ggFixSub φ ↔ φ b = b :=
  Iff.rfl

private lemma ggNe_one_of_reflection {B : Type*} [Group B] [Finite B] {φ : MulAut B}
    (hr : Nat.card {b : B // φ b = b} * 3 = Nat.card B) : φ ≠ 1 := by
  intro h
  haveI : Nonempty B := ⟨1⟩
  have hcard : Nat.card {b : B // φ b = b} = Nat.card B := by
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv (fun b => by rw [h]; rfl)
  rw [hcard] at hr
  have hpos : 0 < Nat.card B := Nat.card_pos
  omega

private lemma ggRefl_centre_ne_one {B : Type*} [Group B] {φ : MulAut B} (hne : φ ≠ 1)
    {c : B} (hc : ∀ b : B, φ b * b⁻¹ ∈ Subgroup.zpowers c) : c ≠ 1 := by
  intro h
  apply hne
  ext b
  show φ b = b
  have hb : φ b * b⁻¹ ∈ Subgroup.zpowers (1 : B) := by
    rw [← h]
    exact hc b
  rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hb
  exact mul_inv_eq_one.mp hb

private lemma ggMul_inv_factor {B : Type*} [Group B] [IsMulCommutative B]
    (f : B → B) (hf : ∀ x y : B, f (x * y) = f x * f y) (x y : B) :
    f (x * y) * (x * y)⁻¹ = (f x * x⁻¹) * (f y * y⁻¹) := by
  rw [hf, mul_inv_rev]
  calc f x * f y * (y⁻¹ * x⁻¹)
      = f x * ((f y * y⁻¹) * x⁻¹) := by group
    _ = f x * (x⁻¹ * (f y * y⁻¹)) := by rw [mul_comm' (f y * y⁻¹) x⁻¹]
    _ = f x * x⁻¹ * (f y * y⁻¹) := by group

private lemma ggEq_one_of_fixes_centre {B : Type*} [Group B] [Finite B] [IsMulCommutative B]
    (hpow : ∀ x : B, x ^ 3 = 1) {φ : MulAut B} (hφ2 : φ ^ 2 = 1) {c : B}
    (hc : ∀ b : B, φ b * b⁻¹ ∈ Subgroup.zpowers c) (hfix : φ c = c) : φ = 1 := by
  have hfixall : ∀ x ∈ Subgroup.zpowers c, φ x = x := by
    have hle : Subgroup.zpowers c ≤ ggFixSub φ :=
      Subgroup.zpowers_le.2 (by rw [mem_ggFixSub]; exact hfix)
    intro x hx
    exact hle hx
  ext b
  show φ b = b
  have hm_mem : φ b * b⁻¹ ∈ Subgroup.zpowers c := hc b
  have hm_fix : φ (φ b * b⁻¹) = φ b * b⁻¹ := hfixall _ hm_mem
  have hphiφ : φ (φ b) = b := by
    have h := congrArg (fun f : MulAut B => f b) hφ2
    simpa [pow_two] using h
  have hb_eq : φ b = (φ b * b⁻¹) * b := by group
  have hm2 : (φ b * b⁻¹) ^ 2 = 1 := by
    have key : b = (φ b * b⁻¹) * (φ b * b⁻¹) * b := by
      calc b = φ (φ b) := hphiφ.symm
        _ = φ ((φ b * b⁻¹) * b) := by conv_lhs => rw [hb_eq]
        _ = φ (φ b * b⁻¹) * φ b := by rw [map_mul]
        _ = (φ b * b⁻¹) * φ b := by rw [hm_fix]
        _ = (φ b * b⁻¹) * ((φ b * b⁻¹) * b) := by rw [← hb_eq]
        _ = (φ b * b⁻¹) * (φ b * b⁻¹) * b := by group
    have hmm : (φ b * b⁻¹) * (φ b * b⁻¹) = 1 := by
      have h : (φ b * b⁻¹) * (φ b * b⁻¹) * b = 1 * b := by
        rw [one_mul]
        exact key.symm
      exact mul_right_cancel h
    simpa [pow_two] using hmm
  have hm3 : (φ b * b⁻¹) ^ 3 = 1 := hpow _
  have hm1 : φ b * b⁻¹ = 1 := by
    calc φ b * b⁻¹ = (φ b * b⁻¹) ^ 3 * ((φ b * b⁻¹) ^ 2)⁻¹ := by group
      _ = 1 * 1⁻¹ := by rw [hm3, hm2]
      _ = 1 := by simp
  exact mul_inv_eq_one.mp hm1

private lemma ggRefl_centre_inv {B : Type*} [Group B] [Finite B] [IsMulCommutative B]
    (hpow : ∀ x : B, x ^ 3 = 1) {φ : MulAut B} (hφ2 : φ ^ 2 = 1) (hne : φ ≠ 1)
    {c : B} (hc : ∀ b : B, φ b * b⁻¹ ∈ Subgroup.zpowers c) : φ c = c⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := ggRefl_centre_ne_one hne hc
  have hc3 : c ^ 3 = 1 := hpow c
  have hmem : φ c ∈ Subgroup.zpowers c := by
    have h1 : φ c * c⁻¹ ∈ Subgroup.zpowers c := hc c
    have h2 : (φ c * c⁻¹) * c ∈ Subgroup.zpowers c :=
      (Subgroup.zpowers c).mul_mem h1 (Subgroup.mem_zpowers c)
    have h3 : (φ c * c⁻¹) * c = φ c := by group
    rwa [h3] at h2
  have hmemrange := (mem_zpowers_iff_mem_range_orderOf (x := c) (y := φ c)).mp hmem
  rw [orderOf_eq_prime hc3 hc1] at hmemrange
  rw [Finset.mem_image] at hmemrange
  obtain ⟨n, hnmem, hn⟩ := hmemrange
  have hnlt : n < 3 := Finset.mem_range.mp hnmem
  interval_cases n
  · exfalso
    apply hc1
    have hphi : φ c = 1 := by rw [← hn]; simp
    exact φ.injective (by rw [hphi, map_one])
  · exfalso
    apply hne
    apply ggEq_one_of_fixes_centre hpow hφ2 hc
    rw [← hn]; simp
  · have hc2 : c ^ 2 = c⁻¹ := by
      have h : c * c ^ 2 = 1 := by rw [← pow_succ']; exact hc3
      exact eq_inv_of_mul_eq_one_right h
    rw [← hn, hc2]

theorem ggIsReflection_eq_of_centre {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    {Aut : Subgroup (MulAut ↥Bs)} (hNT : ∀ φ ∈ Aut, ¬ GGIsTransvection 3 φ)
    {φ φ' : MulAut ↥Bs} (hφ : φ ∈ Aut) (hφ' : φ' ∈ Aut) (hr : GGIsReflection 3 φ)
    (hr' : GGIsReflection 3 φ') {c : ↥Bs} (hc : GGReflCentre φ c) (hc' : GGReflCentre φ' c) :
    φ = φ' := by
  classical
  haveI hcomm : IsMulCommutative ↥Bs := hBs.1
  have hpow : ∀ x : ↥Bs, x ^ 3 = 1 := fun x => ggPow3_eq_one Bs hBs x
  have hneφ : φ ≠ 1 := ggNe_one_of_reflection hr.2
  have hneφ' : φ' ≠ 1 := ggNe_one_of_reflection hr'.2
  have hcφ : φ c = c⁻¹ := ggRefl_centre_inv hpow hr.1 hneφ hc
  have hcφ' : φ' c = c⁻¹ := ggRefl_centre_inv hpow hr'.1 hneφ' hc'
  have hτc : (φ' * φ) c = c := by
    rw [MulAut.mul_apply, hcφ, map_inv, hcφ', inv_inv]
  have hmem : ∀ b : ↥Bs, (φ' * φ) b * b⁻¹ ∈ Subgroup.zpowers c := by
    intro b
    have h1 : φ' (φ b) * (φ b)⁻¹ ∈ Subgroup.zpowers c := hc' (φ b)
    have h2 : φ b * b⁻¹ ∈ Subgroup.zpowers c := hc b
    have h3 : (φ' (φ b) * (φ b)⁻¹) * (φ b * b⁻¹) ∈ Subgroup.zpowers c :=
      (Subgroup.zpowers c).mul_mem h1 h2
    have h4 : (φ' (φ b) * (φ b)⁻¹) * (φ b * b⁻¹) = (φ' * φ) b * b⁻¹ := by
      rw [MulAut.mul_apply]
      group
    rwa [h4] at h3
  let μ : ↥Bs →* ↥(Subgroup.zpowers c) :=
    MonoidHom.mk' (fun b => ⟨(φ' * φ) b * b⁻¹, hmem b⟩) (by
      intro x y
      apply Subtype.ext
      show (φ' * φ) (x * y) * (x * y)⁻¹ =
        ((φ' * φ) x * x⁻¹) * ((φ' * φ) y * y⁻¹)
      have hf : ∀ u v : ↥Bs, (φ' * φ) (u * v) = (φ' * φ) u * (φ' * φ) v := by
        intro u v
        rw [MulAut.mul_apply, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
      exact ggMul_inv_factor (φ' * φ) hf x y)
  have hker : μ.ker = ggFixSub (φ' * φ) := by
    ext b
    rw [MonoidHom.mem_ker, mem_ggFixSub]
    constructor
    · intro h
      have hb : (φ' * φ) b * b⁻¹ = 1 := congrArg Subtype.val h
      exact mul_inv_eq_one.mp hb
    · intro h
      apply Subtype.ext
      show (φ' * φ) b * b⁻¹ = 1
      rw [h, mul_inv_cancel]
  have hrange_dvd : Nat.card μ.range ∣ 3 := by
    have h1 : Nat.card μ.range ∣ Nat.card (⊤ : Subgroup ↥(Subgroup.zpowers c)) :=
      Subgroup.card_dvd_of_le le_top
    rw [Subgroup.card_top, Nat.card_zpowers, orderOf_eq_prime (hpow c) (ggRefl_centre_ne_one hneφ hc)]
      at h1
    exact h1
  have hrange_cases : Nat.card μ.range = 1 ∨ Nat.card μ.range = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hrange_dvd
  by_cases hcase : Nat.card μ.range = 1
  · have hker_top : μ.ker = ⊤ := by
      apply (Subgroup.index_eq_one).mp
      rw [Subgroup.index_ker, hcase]
    have hτ1 : φ' * φ = 1 := by
      apply DFunLike.ext
      intro b
      have hb : b ∈ μ.ker := by rw [hker_top]; trivial
      have hb' : μ b = 1 := (MonoidHom.mem_ker).mp hb
      have hb'' : (φ' * φ) b * b⁻¹ = 1 := congrArg Subtype.val hb'
      exact mul_inv_eq_one.mp hb''
    have hφsq : φ * φ = 1 := by simpa [pow_two] using hr.1
    exact mul_right_cancel (by rw [hτ1, hφsq])
  · have hcase3 : Nat.card μ.range = 3 := by
      rcases hrange_cases with h | h
      · exact absurd h hcase
      · exact h
    have hτmem : φ' * φ ∈ Aut := Aut.mul_mem hφ' hφ
    have htrans : GGIsTransvection 3 (φ' * φ) := by
      constructor
      · have hcardker : Nat.card {b : ↥Bs // (φ' * φ) b = b} = Nat.card ↥μ.ker := by
          apply Nat.card_congr
          exact Equiv.subtypeEquivRight (fun b => by rw [hker, mem_ggFixSub])
        rw [hcardker]
        have hcm : Nat.card μ.ker * μ.ker.index = Nat.card ↥Bs :=
          Subgroup.card_mul_index (H := μ.ker)
        have hidx3 : μ.ker.index = 3 := by rw [Subgroup.index_ker, hcase3]
        rw [hidx3] at hcm
        exact hcm
      · intro b
        have hfixall : ∀ x ∈ Subgroup.zpowers c, (φ' * φ) x = x := by
          have hle : Subgroup.zpowers c ≤ ggFixSub (φ' * φ) :=
            Subgroup.zpowers_le.2 (by rw [mem_ggFixSub]; exact hτc)
          intro x hx
          exact hle hx
        have hfix_b : (φ' * φ) ((φ' * φ) b * b⁻¹) = (φ' * φ) b * b⁻¹ :=
          hfixall _ (hmem b)
        calc (φ' * φ) (b⁻¹ * (φ' * φ) b)
            = (φ' * φ) ((φ' * φ) b * b⁻¹) := by rw [mul_comm' (b⁻¹) ((φ' * φ) b)]
          _ = (φ' * φ) b * b⁻¹ := hfix_b
          _ = b⁻¹ * (φ' * φ) b := by rw [mul_comm' ((φ' * φ) b) (b⁻¹)]
    exact absurd htrans (hNT (φ' * φ) hτmem)

theorem three_pow_three_le_card_ggFixedByCentres {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card ↥Bs = 3 ^ 5) {Aut : Subgroup (MulAut ↥Bs)}
    (hNT : ∀ φ ∈ Aut, ¬ GGIsTransvection 3 φ) {a b : ↥Bs} (hab : GGCorootOrth 3 Aut a b) :
    3 ^ 3 ≤ Nat.card ↥(ggFixedByCentres 3 Aut {a, b}) := by
  obtain ⟨-, φ, hφ, ψ, hψ, hrφ, hcφ, hrψ, hcψ, -⟩ := hab
  have hle : ggFixSub φ ⊓ ggFixSub ψ ≤ ggFixedByCentres 3 Aut {a, b} := by
    intro x hx
    intro θ hθ hrθ hcentre
    obtain ⟨d, hdS, hdc⟩ := hcentre
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdS
    rcases hdS with rfl | rfl
    · have hθφ : θ = φ := ggIsReflection_eq_of_centre hBs hNT hθ hφ hrθ hrφ hdc hcφ
      rw [hθφ]
      exact hx.1
    · have hθψ : θ = ψ := ggIsReflection_eq_of_centre hBs hNT hθ hψ hrθ hrψ hdc hcψ
      rw [hθψ]
      exact hx.2
  have hidxφ : (ggFixSub φ).index = 3 := by
    have h1 : Nat.card (ggFixSub φ) * (ggFixSub φ).index = Nat.card ↥Bs :=
      Subgroup.card_mul_index (H := ggFixSub φ)
    have h2 : Nat.card (ggFixSub φ) * 3 = Nat.card ↥Bs := hrφ.2
    have h3 : Nat.card (ggFixSub φ) * (ggFixSub φ).index = Nat.card (ggFixSub φ) * 3 := by
      rw [h1, h2]
    have hpos : 0 < Nat.card (ggFixSub φ) := by
      haveI : Nonempty ↥(ggFixSub φ) := ⟨1⟩
      exact Nat.card_pos
    exact Nat.mul_left_cancel hpos h3
  have hidxψ : (ggFixSub ψ).index = 3 := by
    have h1 : Nat.card (ggFixSub ψ) * (ggFixSub ψ).index = Nat.card ↥Bs :=
      Subgroup.card_mul_index (H := ggFixSub ψ)
    have h2 : Nat.card (ggFixSub ψ) * 3 = Nat.card ↥Bs := hrψ.2
    have h3 : Nat.card (ggFixSub ψ) * (ggFixSub ψ).index = Nat.card (ggFixSub ψ) * 3 := by
      rw [h1, h2]
    have hpos : 0 < Nat.card (ggFixSub ψ) := by
      haveI : Nonempty ↥(ggFixSub ψ) := ⟨1⟩
      exact Nat.card_pos
    exact Nat.mul_left_cancel hpos h3
  have hidxle : (ggFixSub φ ⊓ ggFixSub ψ).index ≤ 9 := by
    calc (ggFixSub φ ⊓ ggFixSub ψ).index ≤ (ggFixSub φ).index * (ggFixSub ψ).index :=
          Subgroup.index_inf_le
      _ = 3 * 3 := by rw [hidxφ, hidxψ]
      _ = 9 := by norm_num
  have hcardX : Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) * (ggFixSub φ ⊓ ggFixSub ψ).index =
      Nat.card ↥Bs := Subgroup.card_mul_index (H := ggFixSub φ ⊓ ggFixSub ψ)
  have hcardB : Nat.card ↥Bs = 243 := by rw [hcard]; norm_num
  have hge : 27 ≤ Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) := by
    have h1 : Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) * (ggFixSub φ ⊓ ggFixSub ψ).index = 243 := by
      rw [hcardX, hcardB]
    have h2 : Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) * (ggFixSub φ ⊓ ggFixSub ψ).index ≤
        Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) * 9 := Nat.mul_le_mul_left _ hidxle
    have h3 : 243 ≤ Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) * 9 := by
      rw [← h1]
      exact h2
    omega
  have hcard_le : Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) ≤
      Nat.card ↥(ggFixedByCentres 3 Aut {a, b}) := Subgroup.card_le_of_le hle
  calc 3 ^ 3 = 27 := by norm_num
    _ ≤ Nat.card ↥(ggFixSub φ ⊓ ggFixSub ψ) := hge
    _ ≤ Nat.card ↥(ggFixedByCentres 3 Aut {a, b}) := hcard_le

end CFSG.StandardType

end
