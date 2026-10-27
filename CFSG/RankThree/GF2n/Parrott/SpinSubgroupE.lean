module

public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Data
public import CFSG.RankThree.GF2n.Parrott.CaseIIIndex
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.SpinFixedS
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}
variable {ψ : ↥(H z) →* A45} {κ : G → V}

@[expose] def kappaPre (hκ : IsSpinCoord ψ κ) (W : AddSubgroup V) : Subgroup G where
  carrier := {j | j ∈ J z ∧ κ j ∈ W}
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [hκ.add a ha.1 b hb.1]; exact W.add_mem ha.2 hb.2⟩
  one_mem' := ⟨one_mem _, by rw [hκ.kappa_one]; exact W.zero_mem⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [hκ.kappa_inv ha.1]; exact ha.2⟩

theorem kappaPre_le_J (hκ : IsSpinCoord ψ κ) (W : AddSubgroup V) : kappaPre hκ W ≤ J z :=
  fun _ hj => hj.1

theorem z_mem_kappaPre (hκ : IsSpinCoord ψ κ) (W : AddSubgroup V) (hzJ : z ∈ J z) :
    z ∈ kappaPre hκ W := by
  refine ⟨hzJ, ?_⟩
  rw [(hκ.eq_zero_iff z hzJ).mpr (Or.inr rfl)]
  exact W.zero_mem

private noncomputable def zp (z : G) (a : ZMod 2) : G := if a = 0 then 1 else z

private theorem zp_zero (z : G) : zp z 0 = 1 := by simp [zp]

private theorem zp_one (z : G) : zp z 1 = z := by simp [zp]

private theorem zp_add (hz2 : z * z = 1) (a a' : ZMod 2) : zp z (a + a') = zp z a * zp z a' := by
  have h : ∀ a a' : ZMod 2, (a = 0 ∧ a' = 0) ∨ (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) ∨
      (a = 1 ∧ a' = 1) := by decide
  rcases h a a' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [zp_zero]
  · simp [zp_zero, zp_one]
  · simp [zp_zero, zp_one]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, zp_zero, zp_one, hz2]

private theorem zp_injective (hz1 : z ≠ 1) {a a' : ZMod 2} (h : zp z a = zp z a') : a = a' := by
  have hc : ∀ a a' : ZMod 2, (a = 0 ∧ a' = 0) ∨ (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) ∨
      (a = 1 ∧ a' = 1) := by decide
  rcases hc a a' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [zp_zero, zp_one] at h
    exact absurd h.symm hz1
  · rw [zp_zero, zp_one] at h
    exact absurd h hz1
  · rfl

theorem H_mul_z_comm {y : G} (hy : y ∈ H z) : y * z = z * y :=
  Subgroup.mem_centralizer_singleton_iff.mp hy

theorem exists_action_functional (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    {x : G} (hx : x ∈ H z) (U : AddSubgroup V)
    (hU : ∀ u ∈ U, ((rhoA (ψ ⟨x, hx⟩) : GL8) : Mat8) *ᵥ u = u) :
    ∃ ℓ : V → ZMod 2, (∀ u ∈ U, ∀ u' ∈ U, ℓ (u + u') = ℓ u + ℓ u') ∧
      ∀ j ∈ J z, κ j ∈ U → x * j * x⁻¹ = if ℓ (κ j) = 0 then j else j * z := by
  classical
  have hJn : ∀ j ∈ J z, x * j * x⁻¹ ∈ J z := fun j hj =>
    (mem_normalizer_iff.mp (J_le_normalizer_A hx) j).mp hj
  have hxz : x * z * x⁻¹ = z := by
    rw [H_mul_z_comm hx]
    group
  let ℓ : V → ZMod 2 := fun u =>
    if ∃ j ∈ J z, κ j = u ∧ x * j * x⁻¹ = j then 0 else 1
  have hspec : ∀ j ∈ J z, κ j ∈ U → x * j * x⁻¹ = j * zp z (ℓ (κ j)) := by
    intro j hj hjU
    have hfix : κ (x * j * x⁻¹) = κ j := by
      rw [hκ.act x hx j hj]
      exact hU _ hjU
    rcases (hκ.kappa_eq_iff hj (hJn j hj)).mp hfix with e | e
    · have h0 : ℓ (κ j) = 0 := by
        simp only [ℓ]
        rw [if_pos ⟨j, hj, rfl, e⟩]
      rw [h0, zp_zero, mul_one]
      exact e
    · have h1 : ℓ (κ j) = 1 := by
        simp only [ℓ]
        rw [if_neg]
        rintro ⟨j', hj', hκj', hxj'⟩
        rcases (hκ.kappa_eq_iff hj hj').mp hκj' with e' | e'
        · rw [e'] at hxj'
          rw [hxj'] at e
          exact hz1 (mul_left_cancel (a := j) (by rw [mul_one]; exact e)).symm
        · rw [e'] at hxj'
          have h2 : x * (j * z) * x⁻¹ = j := by
            calc x * (j * z) * x⁻¹ = (x * j * x⁻¹) * (x * z * x⁻¹) := by group
              _ = (j * z) * z := by rw [e, hxz]
              _ = j := by rw [mul_assoc, hz2, mul_one]
          rw [h2] at hxj'
          exact hz1 (mul_left_cancel (a := j) (by rw [mul_one]; exact hxj')).symm
      rw [h1, zp_one]
      exact e
  refine ⟨ℓ, ?_, fun j hj hjU => ?_⟩
  swap
  · rw [hspec j hj hjU]
    by_cases h0 : ℓ (κ j) = 0
    · rw [h0, zp_zero, mul_one, if_pos rfl]
    · have h1 : ℓ (κ j) = 1 := by
        have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact this _ h0
      rw [if_neg h0, h1, zp_one]
  intro u hu u' hu'
  obtain ⟨j, hj, rfl⟩ := hκ.surj u
  obtain ⟨j', hj', rfl⟩ := hκ.surj u'
  have hjj : j * j' ∈ J z := mul_mem hj hj'
  have hκjj : κ (j * j') = κ j + κ j' := hκ.add j hj j' hj'
  have h1 := hspec j hj hu
  have h2 := hspec j' hj' hu'
  have h3 := hspec (j * j') hjj (by rw [hκjj]; exact U.add_mem hu hu')
  have hzj' : zp z (ℓ (κ j)) * j' = j' * zp z (ℓ (κ j)) := by
    by_cases h : ℓ (κ j) = 0
    · rw [h, zp_zero, one_mul, mul_one]
    · have : ℓ (κ j) = 1 := by
        have h' := ZMod.val_lt (ℓ (κ j))
        have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact this _ h
      rw [this, zp_one]
      exact (H_mul_z_comm (J_le_H hj')).symm
  have h4 : x * (j * j') * x⁻¹ = j * j' * (zp z (ℓ (κ j)) * zp z (ℓ (κ j'))) := by
    calc x * (j * j') * x⁻¹ = (x * j * x⁻¹) * (x * j' * x⁻¹) := by group
      _ = (j * zp z (ℓ (κ j))) * (j' * zp z (ℓ (κ j'))) := by rw [h1, h2]
      _ = j * (zp z (ℓ (κ j)) * j') * zp z (ℓ (κ j')) := by group
      _ = j * (j' * zp z (ℓ (κ j))) * zp z (ℓ (κ j')) := by rw [hzj']
      _ = j * j' * (zp z (ℓ (κ j)) * zp z (ℓ (κ j'))) := by group
  rw [← zp_add hz2] at h4
  rw [hκjj] at h3
  rw [h3] at h4
  exact zp_injective hz1 (mul_left_cancel h4)

theorem J_conj_formula (hκ : IsSpinCoord ψ κ) (hz : z * z = 1) {j f : G} (hj : j ∈ J z)
    (hf : f ∈ J z) : j * f * j⁻¹ = if b (κ j) (κ f) = 0 then f else f * z := by
  have h := hκ.comm j hj f hf
  by_cases hb : b (κ j) (κ f) = 0
  · rw [if_pos hb] at h ⊢
    calc j * f * j⁻¹ = (j * f * j⁻¹ * f⁻¹) * f := by group
      _ = f := by rw [h, one_mul]
  · rw [if_neg hb] at h ⊢
    calc j * f * j⁻¹ = (j * f * j⁻¹ * f⁻¹) * f := by group
      _ = z * f := by rw [h]
      _ = f * z := (H_mul_z_comm (J_le_H hf)).symm

theorem J_conj_z (hz : z * z = 1) {j : G} (hj : j ∈ J z) : j * z * j⁻¹ = z := by
  rw [H_mul_z_comm (J_le_H hj)]
  group

@[expose] noncomputable def spinFixF (hκ : IsSpinCoord ψ κ) : Subgroup G := kappaPre hκ spinFixS

@[expose] noncomputable def spinFixE (hκ : IsSpinCoord ψ κ) : Subgroup G :=
  H z ⊓ Subgroup.centralizer (spinFixF hκ : Set G)

theorem mem_spinFixE_iff (hκ : IsSpinCoord ψ κ) (x : G) :
    x ∈ spinFixE hκ ↔ x ∈ H z ∧ ∀ f ∈ spinFixF hκ, f * x = x * f := by
  unfold spinFixE
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem spinFixF_le_J (hκ : IsSpinCoord ψ κ) : spinFixF hκ ≤ J z := kappaPre_le_J hκ _

theorem z_mem_spinFixF (hκ : IsSpinCoord ψ κ) (hzJ : z ∈ J z) : z ∈ spinFixF hκ :=
  z_mem_kappaPre hκ _ hzJ

theorem spinFixF_comm (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) {f f' : G} (hf : f ∈ spinFixF hκ)
    (hf' : f' ∈ spinFixF hκ) : f * f' = f' * f := by
  rw [hκ.commute_iff hz1 hf.1 hf'.1]
  have h1 := spinFixS_singular _ (spinFixS.add_mem hf.2 hf'.2)
  have h2 := spinFixS_singular _ hf.2
  have h3 := spinFixS_singular _ hf'.2
  unfold b
  rw [h1, h2, h3]
  decide

theorem spinFixF_sq (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) {f : G} (hf : f ∈ spinFixF hκ) :
    f * f = 1 :=
  (hκ.mul_self_eq_one_iff hz1 hf.1).mpr (spinFixS_singular _ hf.2)

theorem spinFixF_le_spinFixE (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) : spinFixF hκ ≤ spinFixE hκ :=
  fun f hf => (mem_spinFixE_iff hκ f).mpr
    ⟨J_le_H (spinFixF_le_J hκ hf), fun f' hf' => spinFixF_comm hκ hz1 hf' hf⟩

theorem spinFixE_inf_J (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) : spinFixE hκ ⊓ J z = spinFixF hκ := by
  apply le_antisymm
  · intro j hj
    obtain ⟨hjE, hjJ⟩ := Subgroup.mem_inf.mp hj
    refine ⟨hjJ, spinFixS_perp _ fun u hu => ?_⟩
    obtain ⟨f, hfJ, rfl⟩ := hκ.surj u
    have hf : f ∈ spinFixF hκ := ⟨hfJ, hu⟩
    have hc := ((mem_spinFixE_iff hκ j).mp hjE).2 f hf
    exact (hκ.commute_iff hz1 hjJ hfJ).mp hc.symm
  · exact le_inf (spinFixF_le_spinFixE hκ hz1) (spinFixF_le_J hκ)

theorem spinFixE_le_H (hκ : IsSpinCoord ψ κ) : spinFixE hκ ≤ H z := inf_le_left

theorem card_spinFixF (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) :
    Nat.card (spinFixF hκ) = 2 ^ 5 := by
  have hz := orderOf_z_A h
  have hzJ := z_mem_J_A h
  let φ : ↥(spinFixF hκ) →* Multiplicative V :=
    { toFun := fun f => Multiplicative.ofAdd (κ (f : G))
      map_one' := by
        show Multiplicative.ofAdd (κ ((1 : ↥(spinFixF hκ)) : G)) = 1
        rw [Subgroup.coe_one, hκ.kappa_one]
        rfl
      map_mul' := fun f f' => by
        show Multiplicative.ofAdd (κ ((f * f' : ↥(spinFixF hκ)) : G)) = _
        rw [Subgroup.coe_mul, hκ.add f (spinFixF_le_J hκ f.2) f' (spinFixF_le_J hκ f'.2)]
        rfl }
  have hker : φ.ker = (Subgroup.zpowers z).subgroupOf (spinFixF hκ) := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz]
    have h0 : φ f = 1 ↔ κ (f : G) = 0 := by
      show Multiplicative.ofAdd (κ (f : G)) = 1 ↔ _
      exact ⟨fun h => h, fun h => h⟩
    rw [h0, hκ.eq_zero_iff _ (spinFixF_le_J hκ f.2)]
  have hrange : Nat.card φ.range = Nat.card spinFixS := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative V), ?_⟩
        invFun := fun v => ⟨Multiplicative.ofAdd (v : V), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨f, hf⟩ := x.2
      rw [← hf]
      exact f.2.2
    · obtain ⟨j, hj, hjv⟩ := hκ.surj (v : V)
      exact ⟨⟨j, ⟨hj, by rw [hjv]; exact v.2⟩⟩, by
        show Multiplicative.ofAdd (κ j) = _
        rw [hjv]⟩
    · intro x
      rfl
    · intro v
      rfl
  have hcardker : Nat.card φ.ker = 2 := by
    rw [hker]
    have hle : Subgroup.zpowers z ≤ spinFixF hκ := Subgroup.zpowers_le.mpr (z_mem_spinFixF hκ hzJ)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hz]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hcardker, hrange, card_spinFixS] at h
  omega

theorem z_ne_one_A (h : Tim79a.ParrottHypA z) : z ≠ 1 := fun e => by
  have h2 := orderOf_z_A h
  rw [e, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem z_mul_self_A (h : Tim79a.ParrottHypA z) : z * z = 1 := by
  have h1 := pow_orderOf_eq_one z
  rwa [orderOf_z_A h, pow_two] at h1

theorem rho_mem_spinFixS_of_mem_normalizer {a : A45}
    (ha : a ∈ Subgroup.normalizer (sQA45 : Set A45)) {v : V} (hv : v ∈ spinFixS) :
    ((rhoA a : GL8) : Mat8) *ᵥ v ∈ spinFixS := by
  intro s hs
  have hinv : a⁻¹ ∈ Subgroup.normalizer (sQA45 : Set A45) := inv_mem ha
  have h1 : a⁻¹ * s * a⁻¹⁻¹ ∈ sQA45 := (mem_normalizer_iff.mp hinv s).mp hs
  rw [inv_inv] at h1
  exact spinFixes_mulVec_of_conj (hv _ h1)

theorem conj_mem_spinFixF (hκ : IsSpinCoord ψ κ) {x : G} (hx : x ∈ H z)
    (hN : ψ ⟨x, hx⟩ ∈ Subgroup.normalizer (sQA45 : Set A45)) {f : G} (hf : f ∈ spinFixF hκ) :
    x * f * x⁻¹ ∈ spinFixF hκ := by
  have hJn : x * f * x⁻¹ ∈ J z := (mem_normalizer_iff.mp (J_le_normalizer_A hx) f).mp hf.1
  refine ⟨hJn, ?_⟩
  rw [hκ.act x hx f hf.1]
  exact rho_mem_spinFixS_of_mem_normalizer hN hf.2

theorem conj_mem_spinFixE (hκ : IsSpinCoord ψ κ) {x : G} (hx : x ∈ H z)
    (hN : ψ ⟨x, hx⟩ ∈ Subgroup.normalizer (sQA45 : Set A45)) {e : G} (he : e ∈ spinFixE hκ) :
    x * e * x⁻¹ ∈ spinFixE hκ := by
  have hxi : x⁻¹ ∈ H z := inv_mem hx
  have hNi : ψ ⟨x⁻¹, hxi⟩ ∈ Subgroup.normalizer (sQA45 : Set A45) := by
    have : (⟨x⁻¹, hxi⟩ : ↥(H z)) = ⟨x, hx⟩⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem hN
  rw [mem_spinFixE_iff] at he ⊢
  refine ⟨mul_mem (mul_mem hx he.1) hxi, fun f hf => ?_⟩
  have hf0 : x⁻¹ * f * x⁻¹⁻¹ ∈ spinFixF hκ := conj_mem_spinFixF hκ hxi hNi hf
  rw [inv_inv] at hf0
  have h1 := he.2 _ hf0
  calc f * (x * e * x⁻¹) = x * ((x⁻¹ * f * x) * e) * x⁻¹ := by group
    _ = x * (e * (x⁻¹ * f * x)) * x⁻¹ := by rw [h1]
    _ = (x * e * x⁻¹) * f := by group

theorem qH_mem_sQA45_of_mem_spinFixE (hκ : IsSpinCoord ψ κ) {x : G} (hx : x ∈ H z)
    (hxE : x ∈ spinFixE hκ) : ψ ⟨x, hx⟩ ∈ sQA45 := by
  refine mem_sQA45_of_fixes_spinFixS _ fun u hu => ?_
  obtain ⟨f, hfJ, rfl⟩ := hκ.surj u
  have hf : f ∈ spinFixF hκ := ⟨hfJ, hu⟩
  have hc : f * x = x * f := ((mem_spinFixE_iff hκ x).mp hxE).2 f hf
  have h1 := hκ.act x hx f hfJ
  have h2 : x * f * x⁻¹ = f := by rw [← hc]; group
  rw [h2] at h1
  exact h1.symm

theorem exists_spinFixE_over (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) {s : A45}
    (hs : s ∈ sQA45) : ∃ (x : G) (hx : x ∈ H z), x ∈ spinFixE hκ ∧ ψ ⟨x, hx⟩ = s := by
  have hz1 := z_ne_one_A h
  have hz2 := z_mul_self_A h
  obtain ⟨x₀, hx₀⟩ := hκ.surjective s
  obtain ⟨ℓ, hadd, hspec⟩ := exists_action_functional hκ hz1 hz2 x₀.2 spinFixS
    (fun u hu => by
      have : ψ ⟨(x₀ : G), x₀.2⟩ = s := hx₀
      rw [this]
      exact hu s hs)
  obtain ⟨c, hc⟩ := exists_vector_represents_spinFixS ℓ hadd
  obtain ⟨j, hj, hjc⟩ := hκ.surj c
  have hjH : j ∈ H z := J_le_H hj
  have hxH : j * (x₀ : G) ∈ H z := mul_mem hjH x₀.2
  refine ⟨j * (x₀ : G), hxH, ?_, ?_⟩
  · rw [mem_spinFixE_iff]
    refine ⟨hxH, fun f hf => ?_⟩
    have h1 := hspec f hf.1 hf.2
    have h2 := J_conj_formula hκ hz2 hj hf.1
    have hℓ : ℓ (κ f) = b c (κ f) := hc _ hf.2
    rw [hjc] at h2
    have h3 : (j * (x₀ : G)) * f * (j * (x₀ : G))⁻¹ = f := by
      calc (j * (x₀ : G)) * f * (j * (x₀ : G))⁻¹ = j * ((x₀ : G) * f * (x₀ : G)⁻¹) * j⁻¹ := by
            group
        _ = f := by
          rw [h1]
          by_cases hb : b c (κ f) = 0
          · rw [hℓ, if_pos hb, h2, if_pos hb]
          · rw [hℓ, if_neg hb]
            calc j * (f * z) * j⁻¹ = (j * f * j⁻¹) * (j * z * j⁻¹) := by group
              _ = (f * z) * z := by rw [h2, if_neg hb, J_conj_z hz2 hj]
              _ = f := by rw [mul_assoc, hz2, mul_one]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · have hj1 : ψ ⟨j, hjH⟩ = 1 := (hκ.eq_one_iff ⟨j, hjH⟩).mpr hj
    have : (⟨j * (x₀ : G), hxH⟩ : ↥(H z)) = ⟨j, hjH⟩ * x₀ := rfl
    rw [this, map_mul, hj1, one_mul]
    exact hx₀

theorem mem_normalizer_spinFixE_iff (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) {x : G}
    (hx : x ∈ H z) :
    x ∈ Subgroup.normalizer (spinFixE hκ : Set G) ↔
      ψ ⟨x, hx⟩ ∈ Subgroup.normalizer (sQA45 : Set A45) := by
  constructor
  · intro hN
    rw [mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      obtain ⟨e, he, heE, hψ⟩ := exists_spinFixE_over h hκ hs
      have h1 : x * e * x⁻¹ ∈ spinFixE hκ := (mem_normalizer_iff.mp hN e).mp heE
      have hH : x * e * x⁻¹ ∈ H z := spinFixE_le_H hκ h1
      have h2 := qH_mem_sQA45_of_mem_spinFixE hκ hH h1
      have h3 : (⟨x * e * x⁻¹, hH⟩ : ↥(H z)) = ⟨x, hx⟩ * ⟨e, he⟩ * ⟨x, hx⟩⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv, hψ] at h2
      exact h2
    · intro hs
      obtain ⟨e, he, heE, hψ⟩ := exists_spinFixE_over h hκ hs
      have hxi : x⁻¹ ∈ Subgroup.normalizer (spinFixE hκ : Set G) := inv_mem hN
      have h1 : x⁻¹ * e * x⁻¹⁻¹ ∈ spinFixE hκ := (mem_normalizer_iff.mp hxi e).mp heE
      have hH : x⁻¹ * e * x⁻¹⁻¹ ∈ H z := spinFixE_le_H hκ h1
      have h2 := qH_mem_sQA45_of_mem_spinFixE hκ hH h1
      have h3 : (⟨x⁻¹ * e * x⁻¹⁻¹, hH⟩ : ↥(H z)) = ⟨x, hx⟩⁻¹ * ⟨e, he⟩ * ⟨x, hx⟩ := by
        apply Subtype.ext
        simp
      rw [h3, map_mul, map_mul, map_inv, hψ] at h2
      have h4 : (ψ ⟨x, hx⟩)⁻¹ * (ψ ⟨x, hx⟩ * s * (ψ ⟨x, hx⟩)⁻¹) * ψ ⟨x, hx⟩ = s := by group
      rw [h4] at h2
      exact h2
  · intro hN
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact conj_mem_spinFixE hκ hx hN he
    · intro he
      have hxi : x⁻¹ ∈ H z := inv_mem hx
      have hNi : ψ ⟨x⁻¹, hxi⟩ ∈ Subgroup.normalizer (sQA45 : Set A45) := by
        have : (⟨x⁻¹, hxi⟩ : ↥(H z)) = ⟨x, hx⟩⁻¹ := rfl
        rw [this, map_inv]
        exact inv_mem hN
      have := conj_mem_spinFixE hκ hxi hNi he
      rwa [inv_inv, show x⁻¹ * (x * e * x⁻¹) * x = e by group] at this

theorem J_le_normalizer_spinFixE (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) :
    J z ≤ Subgroup.normalizer (spinFixE hκ : Set G) := fun j hj =>
  (mem_normalizer_spinFixE_iff h hκ (J_le_H hj)).mpr (by
    rw [(hκ.eq_one_iff ⟨j, J_le_H hj⟩).mpr hj]
    exact one_mem _)

section Counting

variable (D : QuotientData (z := z) (J_subgroupOf_normal z))

theorem imageQA45_spinFixE (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord (qH D) κ) :
    imageQA45 D (spinFixE_le_H hκ) = sQA45 := by
  ext a
  rw [mem_imageQA45_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact qH_mem_sQA45_of_mem_spinFixE hκ _ hk
  · intro ha
    obtain ⟨x, hx, hxE, hψ⟩ := exists_spinFixE_over h hκ ha
    exact ⟨x, hxE, hψ⟩

theorem card_spinFixE (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord (qH D) κ) :
    Nat.card (spinFixE hκ) = 2 ^ 9 := by
  have h1 := card_eq_card_inf_J_mul_card_imageQA45 D (spinFixE_le_H hκ)
  rw [spinFixE_inf_J hκ (z_ne_one_A h), card_spinFixF h hκ, imageQA45_spinFixE D h hκ,
    card_sQA45] at h1
  omega

theorem relIndex_spinFixE (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord (qH D) κ) :
    (spinFixE hκ).relIndex (Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z) = 1920 := by
  have hMH : Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z ≤ H z := inf_le_right
  have hEM : spinFixE hκ ≤ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z :=
    le_inf Subgroup.le_normalizer (spinFixE_le_H hκ)
  have hMJ : (Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z) ⊓ J z = J z :=
    inf_eq_right.mpr (le_inf (J_le_normalizer_spinFixE h hκ) J_le_H)
  have himg : imageQA45 D hMH = Subgroup.normalizer (sQA45 : Set A45) := by
    ext a
    rw [mem_imageQA45_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (mem_normalizer_spinFixE_iff h hκ (hMH hk)).mp (Subgroup.mem_inf.mp hk).1
    · intro ha
      obtain ⟨x, hx⟩ := hκ.surjective a
      refine ⟨x, Subgroup.mem_inf.mpr ⟨(mem_normalizer_spinFixE_iff h hκ x.2).mpr ?_, x.2⟩, hx⟩
      have : qH D ⟨(x : G), x.2⟩ = a := hx
      rw [this]
      exact ha
  have h1 := card_eq_card_inf_J_mul_card_imageQA45 D hMH
  rw [hMJ, card_J_A h, himg, card_normalizer_sQA45] at h1
  have h2 := Subgroup.relIndex_mul_card (spinFixE hκ)
    (Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z)
  rw [inf_eq_left.mpr hEM, card_spinFixE D h hκ, h1] at h2
  omega

theorem sQA45_le_Q : sQA45 ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  unfold sQA45
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact u_mem_Q
  · exact mul_mem alpha1_mem_Q alpha2_mem_Q
  · exact mul_mem beta1_mem_Q beta2_mem_Q
  · exact t_mem_Q

theorem commutator_le_map_P_H : ⁅H z, H z⁆ ≤ (P_H D).map (H z).subtype := by
  have hidx := index_P_H D
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨⁅(⟨a, ha⟩ : ↥(H z)), ⟨b, hb⟩⁆, ?_, by simp [commutatorElement_def]⟩
  rw [SetLike.mem_coe, commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
    Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem spinFixE_le_commutator (h : Tim79a.ParrottHypA z)
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hκ : IsSpinCoord (qH D) κ) : spinFixE hκ ≤ ⁅H z, H z⁆ := by
  have hH2 := relIndex_commutator_of_not_equalityBranch_A h D hIII
  have hle := commutator_le_map_P_H D
  have hsub : (P_H D).map (H z).subtype ≤ H z := Subgroup.map_subtype_le _
  have htop : (⊤ : Subgroup ↥(H z)).map (H z).subtype = H z := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hP2 : ((P_H D).map (H z).subtype).relIndex (H z) = 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective (P_H D) ⊤ (H z).subtype_injective
    rw [htop, Subgroup.relIndex_top_right, index_P_H D] at h1
    exact h1
  have h1 := Subgroup.relIndex_mul_relIndex ⁅H z, H z⁆ ((P_H D).map (H z).subtype) (H z) hle hsub
  rw [hH2, hP2] at h1
  have h2 : ⁅H z, H z⁆.relIndex ((P_H D).map (H z).subtype) = 1 := by omega
  have heq := Subgroup.relIndex_eq_one.mp h2
  intro x hxE
  have hx : x ∈ H z := spinFixE_le_H hκ hxE
  have hP : (⟨x, hx⟩ : ↥(H z)) ∈ P_H D :=
    (mem_P_H_iff D _).mpr (sQA45_le_Q (qH_mem_sQA45_of_mem_spinFixE hκ hx hxE))
  exact heq ⟨⟨x, hx⟩, hP, rfl⟩

end Counting

theorem isElemAbelian_spinFixE_inf_J (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) :
    IsElemAbelian 2 (spinFixE hκ ⊓ J z) := by
  have hz1 := z_ne_one_A h
  rw [spinFixE_inf_J hκ hz1]
  exact ⟨⟨⟨fun a b => Subtype.ext (spinFixF_comm hκ hz1 a.2 b.2)⟩⟩, fun a ha => by
    rw [pow_two]
    exact spinFixF_sq hκ hz1 ha⟩

theorem z_mem_spinFixE (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) : z ∈ spinFixE hκ :=
  spinFixF_le_spinFixE hκ (z_ne_one_A h) (z_mem_spinFixF hκ (z_mem_J_A h))

theorem spinFixE_eq_inf_centralizer (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) :
    spinFixE hκ = H z ⊓ Subgroup.centralizer ((spinFixE hκ ⊓ J z : Subgroup G) : Set G) := by
  rw [spinFixE_inf_J hκ (z_ne_one_A h)]
  rfl

end CFSG.RankThree.GF2n.Parrott
