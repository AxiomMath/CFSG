module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelAlgebra
public import CFSG.RankThree.GF2n.Tim79Hyper
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section GT2

variable (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q)

include H hgV hgQ

theorem gt2 {n : ℕ} (D : MulData V (conjSubgroup g V) Q (GaloisField 2 n)) {τ : G}
    {a : GaloisField 2 n} (hτH : τ ∈ Q ⊔ conjSubgroup g Q)
    (hτU : τ ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G)) (ha : a ≠ 1)
    (hψ : ∀ u ∈ conjSubgroup g V, D.ψ (τ * u * τ⁻¹) = a⁻¹ * D.ψ u)
    (Y : Subgroup G) (hYτ : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) (hVY : V ≤ Y)
    (hY : ∀ u ∈ conjSubgroup g V, u ∈ Y → u = 1) {l : G} (hlY : l ∈ Y)
    (hlL : l ∈ Q ⊓ conjSubgroup g Q) : τ * l * τ⁻¹ * l⁻¹ ∈ V := by
  obtain ⟨u, hu, l₁, hl₁, hl, hτl₁⟩ := H.exists_split hgV hgQ D hτH hτU ha hψ hlL
  have huQ : u ∈ Q := hgQ hu
  have hcent : u * (τ * l₁ * τ⁻¹ * l₁⁻¹) = (τ * l₁ * τ⁻¹ * l₁⁻¹) * u := H.V_central hτl₁ huQ |>.symm
  have e : τ * l * τ⁻¹ * l⁻¹ = (τ * u * τ⁻¹ * u⁻¹) * (τ * l₁ * τ⁻¹ * l₁⁻¹) := by
    have e1 : τ * l * τ⁻¹ * l⁻¹ =
        (τ * u * τ⁻¹) * (τ * l₁ * τ⁻¹ * l₁⁻¹) * u⁻¹ := by rw [hl]; group
    rw [e1]
    have e2 : (τ * u * τ⁻¹) * (τ * l₁ * τ⁻¹ * l₁⁻¹) * u⁻¹ =
        (τ * u * τ⁻¹ * u⁻¹) * (u * (τ * l₁ * τ⁻¹ * l₁⁻¹) * u⁻¹) := by group
    rw [e2, hcent]
    group
  have hτu : τ * u * τ⁻¹ ∈ conjSubgroup g V := (Subgroup.mem_normalizer_iff.mp hτU u).mp hu
  have hcu : τ * u * τ⁻¹ * u⁻¹ ∈ conjSubgroup g V :=
    Subgroup.mul_mem _ hτu (Subgroup.inv_mem _ hu)
  have hY1 : τ * u * τ⁻¹ * u⁻¹ ∈ Y := by
    have h1 : τ * l * τ⁻¹ * l⁻¹ ∈ Y :=
      Subgroup.mul_mem _ (hYτ l hlY) (Subgroup.inv_mem _ hlY)
    have h2 : (τ * u * τ⁻¹ * u⁻¹) = (τ * l * τ⁻¹ * l⁻¹) * (τ * l₁ * τ⁻¹ * l₁⁻¹)⁻¹ := by
      rw [e]; group
    rw [h2]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hVY hτl₁))
  have h1 : τ * u * τ⁻¹ * u⁻¹ = 1 := hY _ hcu hY1
  have hu1 : u = 1 := by
    have h2 : τ * u * τ⁻¹ = u := by
      have := congrArg (· * u) h1
      simpa using this
    have h3 := hψ u hu
    rw [h2] at h3
    have h4 : (1 - a⁻¹) * D.ψ u = 0 := by linear_combination h3
    have hne : (1 - a⁻¹) ≠ 0 := sub_ne_zero.mpr fun h => ha (inv_eq_one.mp h.symm)
    exact D.ψ_inj u hu ((mul_eq_zero.mp h4).resolve_left hne)
  rw [e, h1, one_mul]
  exact hτl₁

end GT2


section Trans

variable {K : Type} [Field K]

def transC (τ : G) (C : Set (Subgroup G)) : Set (Subgroup G) :=
  {U | ∃ U₀ ∈ C, U = conjSubgroup τ U₀}

theorem transC_mul (g h : G) (C : Set (Subgroup G)) :
    transC (g * h) C = transC g (transC h C) := by
  ext U
  constructor
  · rintro ⟨U₀, hU₀, rfl⟩
    exact ⟨conjSubgroup h U₀, ⟨U₀, hU₀, rfl⟩, by rw [conjSubgroup_mul]⟩
  · rintro ⟨U₁, ⟨U₀, hU₀, rfl⟩, rfl⟩
    exact ⟨U₀, hU₀, by rw [conjSubgroup_mul]⟩

theorem transC_one (C : Set (Subgroup G)) : transC 1 C = C := by
  ext U
  constructor
  · rintro ⟨U₀, hU₀, rfl⟩
    rwa [conjSubgroup_one]
  · intro hU
    exact ⟨U, hU, (conjSubgroup_one U).symm⟩

theorem conj_mem_classOf {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) {γ : G → K} {U : Subgroup G}
    (hU : U ∈ classOf V Q γ) :
    conjSubgroup τ U ∈ classOf V Q (fun v => γ (τ⁻¹ * v * τ)) := by
  obtain ⟨⟨g, hg⟩, hUQ, hUV, D, c, σ, hc, hcσ⟩ := hU
  refine ⟨⟨τ * g, by rw [hg, conjSubgroup_mul]⟩, ?_, ?_, D.conjData hV hQ, c, σ, hc, ?_⟩
  · intro x hx
    have h1 : τ⁻¹ * x * τ ∈ U := mem_conjSubgroup.mp hx
    have h2 : τ * (τ⁻¹ * x * τ) * τ⁻¹ ∈ Q := (mem_iff_conj_of_normalizer hQ _).mp (hUQ h1)
    rwa [show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x by group] at h2
  · intro h
    apply hUV
    have h1 : conjSubgroup τ⁻¹ (conjSubgroup τ U) = U := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h2 : conjSubgroup τ⁻¹ V = V := conjSubgroup_eq_self_iff.mpr (inv_mem hV)
    rw [← h1, h, h2]
  · intro v hv
    exact hcσ _ ((mem_iff_conj_inv_of_normalizer hV v).mp hv)

theorem transC_classOf {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (γ : G → K) :
    transC τ (classOf V Q γ) = classOf V Q (fun v => γ (τ⁻¹ * v * τ)) := by
  ext U
  constructor
  · rintro ⟨U₀, hU₀, rfl⟩
    exact conj_mem_classOf hV hQ hU₀
  · intro hU
    have h1 := conj_mem_classOf (inv_mem hV) (inv_mem hQ) hU
    refine ⟨conjSubgroup τ⁻¹ U, ?_, ?_⟩
    · have : (fun v => (fun v => γ (τ⁻¹ * v * τ)) (τ⁻¹⁻¹ * v * τ⁻¹)) = γ := by
        funext v
        simp only [inv_inv]
        congr 1
        group
      rwa [this] at h1
    · rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]

theorem exists_period (τ : G) {N : ℕ} (hN : 0 < N) (hτN : τ ^ N = 1) (C : Set (Subgroup G)) :
    ∃ d, 0 < d ∧ d ∣ N ∧ transC (τ ^ d) C = C ∧
      ∀ i, 0 < i → i < d → transC (τ ^ i) C ≠ C := by
  classical
  have hex : ∃ k, 0 < k ∧ transC (τ ^ k) C = C := ⟨N, hN, by rw [hτN, transC_one]⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2, ?_⟩
  · set d := Nat.find hex with hd
    have hdq : ∀ q : ℕ, transC (τ ^ (d * q)) C = C := by
      intro q
      induction q with
      | zero => simp [transC_one]
      | succ q ih =>
        rw [mul_add, mul_one, pow_add, transC_mul, (Nat.find_spec hex).2, ih]
    have hr : transC (τ ^ (N % d)) C = C := by
      have h1 : transC (τ ^ N) C = C := by rw [hτN, transC_one]
      have h2 : τ ^ N = τ ^ (N % d) * τ ^ (d * (N / d)) := by
        rw [← pow_add, Nat.mod_add_div]
      rw [h2, transC_mul, hdq] at h1
      exact h1
    by_contra hnd
    have hmod : N % d ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt N (Nat.find_spec hex).1) ⟨Nat.pos_of_ne_zero hmod, hr⟩
  · intro i hi hid hC
    exact Nat.find_min hex hid ⟨hi, hC⟩


theorem gammaCompat_of_stable {n : ℕ} (hn : 2 ≤ n) {U₁ U₂ : Subgroup G}
    (D₁ : MulData V U₁ Q (GaloisField 2 n)) (D₂ : MulData V U₂ Q (GaloisField 2 n))
    {τ : G} {a : GaloisField 2 n} (hτV : τ ∈ Subgroup.normalizer (V : Set G))
    (hτQ : τ ∈ Subgroup.normalizer (Q : Set G))
    (hord : orderOf a = Nat.card (GaloisField 2 n) - 1)
    (hγ : ∀ v ∈ V, D₁.γ (τ * v * τ⁻¹) = a * D₁.γ v)
    (hg : ∃ g : G, U₂ = conjSubgroup g V) (hUQ : U₂ ≤ Q) (hUV : U₂ ≠ V)
    (hstab : transC τ (classOf V Q D₂.γ) = classOf V Q D₂.γ) :
    GammaCompat V D₁.γ D₂.γ := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hK3 : 3 ≤ Nat.card (GaloisField 2 n) := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hord
    omega
  have hU₂ : U₂ ∈ classOf V Q D₂.γ := mem_classOf_self D₂ hg hUQ hUV
  have hcl : classOf V Q (fun v => D₂.γ (τ⁻¹ * v * τ)) = classOf V Q D₂.γ := by
    rw [← transC_classOf hτV hτQ, hstab]
  have hU₂' : U₂ ∈ classOf V Q (fun v => D₂.γ (τ⁻¹ * v * τ)) := by rw [hcl]; exact hU₂
  obtain ⟨-, -, -, D'', c, σ, hc, hcσ⟩ := hU₂'
  have hA : GammaCompat V (fun v => D₂.γ (τ⁻¹ * v * τ)) D''.γ := ⟨c, σ, hc, hcσ⟩
  have hB : GammaCompat V D''.γ D₂.γ := MulData.compat_same D'' D₂
  obtain ⟨c₃, σ₃, hc₃, hcσ₃⟩ := (hA.trans hB).symm
  set θ := MulData.thetaHom D₁ D₂ with hθdef
  have hθb : Function.Bijective θ := MulData.thetaHom_bijective D₁ D₂
  have hrel : ∀ x, θ (a⁻¹ * x) = c₃ * σ₃ (θ x) := by
    intro x
    set v := D₁.vinv x with hv
    have hvV : v ∈ V := D₁.vinv_mem x
    have hx : D₁.γ v = x := D₁.γ_vinv x
    have hτv : τ⁻¹ * v * τ ∈ V := (mem_iff_conj_inv_of_normalizer hτV v).mp hvV
    have h1 : D₁.γ (τ⁻¹ * v * τ) = a⁻¹ * x := by
      rw [← hx]
      exact gamma_conj_inv hτV ha0 hγ hvV
    have h2 : θ (a⁻¹ * x) = D₂.γ (τ⁻¹ * v * τ) := by
      rw [← h1]
      exact MulData.thetaHom_γ D₁ D₂ hτv
    rw [h2, show D₂.γ (τ⁻¹ * v * τ) = c₃ * σ₃ (D₂.γ v) from hcσ₃ v hvV, ← hx,
      MulData.thetaHom_γ D₁ D₂ hvV]
  have hord' : orderOf a⁻¹ = Nat.card (GaloisField 2 n) - 1 := by
    rw [orderOf_inv_field, hord]
  obtain ⟨σ', hσ'⟩ := semilinear_of_conj hK3 hord' θ hθb c₃ σ₃ hrel
  have hθ1 : θ 1 ≠ 0 := fun h0 => one_ne_zero (hθb.1 (by rw [h0, map_zero]))
  refine ⟨θ 1, σ', hθ1, fun v hv => ?_⟩
  rw [← MulData.thetaHom_γ D₁ D₂ hv]
  exact hσ' _

end Trans


section Model

variable {K : Type} [Field K] [CharP K 2] {γ : G → K} (C : ModelCtx V Q γ)

@[expose] def jf (γ : G → K) (Q : Subgroup G) (x : G) : ↥Q → K := fun y => γ ⁅x, (y : G)⁆

@[expose] def Top (Q : Subgroup G) (a : K) (τ : G) (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q) :
    (↥Q → K) →ₗ[K] (↥Q → K) where
  toFun φ := fun y => a * φ ⟨τ⁻¹ * y * τ, hτ y y.2⟩
  map_add' φ ψ := by ext y; simp [mul_add]
  map_smul' c φ := by ext y; simp [mul_left_comm]

include C

theorem jf_mul {x x' : G} (hx : x ∈ Q) (hx' : x' ∈ Q) :
    jf γ Q (x * x') = jf γ Q x + jf γ Q x' := by
  ext y
  exact C.γ_comm_mul_left hx hx' y.2

theorem jf_one : jf γ Q 1 = 0 := by
  ext y
  simp [jf, C.γ_one]

theorem jf_V {v : G} (hv : v ∈ V) : jf γ Q v = 0 := by
  ext y
  simp [jf, C.comm_eq_one_left hv y.2, C.γ_one]

theorem jf_of_commute {x : G} {y : ↥Q} (h : x * (y : G) = (y : G) * x) : jf γ Q x y = 0 := by
  simp [jf, commutatorElement_eq_one_iff_mul_comm.mpr h, C.γ_one]

theorem jf_additive_right {x : G} (hx : x ∈ Q) (y y' : ↥Q) :
    jf γ Q x (y * y') = jf γ Q x y + jf γ Q x y' := by
  show γ ⁅x, ((y * y' : ↥Q) : G)⁆ = γ ⁅x, (y : G)⁆ + γ ⁅x, (y' : G)⁆
  rw [show ((y * y' : ↥Q) : G) = (y : G) * (y' : G) from rfl,
    ← C.γ_comm_symm hx (Q.mul_mem y.2 y'.2), ← C.γ_comm_symm hx y.2,
    ← C.γ_comm_symm hx y'.2]
  exact C.γ_comm_mul_left y.2 y'.2 hx

theorem Top_jf {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {x : G} (hx : x ∈ Q) :
    Top Q a τ hτ (jf γ Q x) = jf γ Q (τ * x * τ⁻¹) := by
  ext y
  show a * γ ⁅x, τ⁻¹ * (y : G) * τ⁆ = γ ⁅τ * x * τ⁻¹, (y : G)⁆
  have h1 : ⁅x, τ⁻¹ * (y : G) * τ⁆ ∈ V := C.comm_mem x hx _ (hτ y y.2)
  have e : ⁅τ * x * τ⁻¹, (y : G)⁆ = τ * ⁅x, τ⁻¹ * (y : G) * τ⁆ * τ⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, hγ _ h1]

theorem Top_pow_jf {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q)
    (hτ' : ∀ y ∈ Q, τ * y * τ⁻¹ ∈ Q)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {x : G} (hx : x ∈ Q) (k : ℕ) :
    (Top Q a τ hτ ^ k) (jf γ Q x) = jf γ Q (τ ^ k * x * (τ ^ k)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk : τ ^ k * x * (τ ^ k)⁻¹ ∈ Q := by
      clear ih
      induction k with
      | zero => simpa using hx
      | succ k ih' =>
        have := hτ' _ ih'
        rwa [show τ * (τ ^ k * x * (τ ^ k)⁻¹) * τ⁻¹ = τ ^ (k + 1) * x * (τ ^ (k + 1))⁻¹ by
          rw [pow_succ']; group] at this
    rw [pow_succ', Module.End.mul_apply, ih, Top_jf C hτ hγ hxk]
    congr 1
    rw [pow_succ']; group

end Model

end CFSG.RankThree.GF2n.Stroth80.FieldModel
