module

public import CFSG.Quasithin.EmptyFaithful.S146zNCount
public import CFSG.Quasithin.EmptyFaithful.S146zCtx

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

structure PCtx {G : Type} [Group G] [Finite G] (T M K U₁ U₂ : Subgroup G) (s u : G) : Prop
    extends ThreeC.CCtx T M K U₁ U₂ s where
  huU : u ∈ U₁
  huZ : u ∉ quasithinOmegaOneCenter T
  hinv : IsInvU T M (mcOf T) u

section QMove

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem PCtx.inf_centralizer_Q (S : Setting146 G T M) (c : PCtx T M K U₁ U₂ s u) :
    (U₁ ⊔ U₂) ⊓ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ≤ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have hQN : mcOf T ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) := le_normalizer_pCoreOf 2 (mcOf T)
  set Q := pCoreOf 2 (mcOf T) with hQ
  set C := Subgroup.centralizer (Q : Set G) with hC
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk =>
    normalizer_le_normalizer_centralizer' (hQN (hKH hk))
  have hZC : Zz ≤ C := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact S146T.comm_Z (pCoreOf_le 2 (mcOf T) hq) hz
  have hnot : ¬ U₁ ≤ C := fun h => c.hinv.not_central (h c.huU)
  have hE₁ : U₁ ⊓ C ≤ Zz := c.hSec.inf_le_of_not_le hKC hZC hnot
  have hE₂ : U₂ ⊓ C ≤ Zz := by
    rintro x ⟨hx2, hxC⟩
    have hx1 : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ hx2)
    have hxC' : s⁻¹ * x * s ∈ C := by
      have h1 := conj_mem_centralizer' (Subgroup.inv_mem _ (hQN hsH)) hxC
      simpa using h1
    have h1 : s⁻¹ * x * s ∈ Zz := hE₁ ⟨hx1, hxC'⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp c.hsZ _).mp h1
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at h2
  set E := (U₁ ⊔ U₂) ⊓ C with hE
  have hEsup : E ≤ U₁ ⊔ U₂ := inf_le_left
  have hEU : E ≤ uOfL22 T M := hEsup.trans (sup_le c.hU₁U c.hU₂U)
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := fun k hk => by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, hKC hk⟩
    exact le_normalizer_sup_of_le (fun k hk => c.hSec.KU hk) c.le_normalizer_U₂ hk
  have hE₁' : U₁ ⊓ E ≤ Zz := fun x hx => hE₁ ⟨hx.1, hx.2.2⟩
  have hE₂' : conjSub s U₁ ⊓ E ≤ Zz := fun x hx => hE₂ ⟨c.hU₂ ▸ hx.1, hx.2.2⟩
  set X := U₁ ⊔ E with hX
  have hXU : X ≤ uOfL22 T M := sup_le c.hU₁U hEU
  have hZX : Zz ≤ X := c.hSec.le.trans le_sup_left
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := fun k hk =>
    le_normalizer_sup_of_le (fun k hk => c.hSec.KU hk) hKE hk
  have hKXU₂ : K ≤ Subgroup.normalizer ((X ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKX hk, c.le_normalizer_U₂ hk⟩
  rcases c.irr₂ (le_inf hZX c.hZU₂) inf_le_right hKXU₂ with h | h
  ·
    have hcommXU₂ : ∀ x ∈ X, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy =>
      S.comm_of_mem_conjClosure (hXU hx) (c.hU₂U hy)
    obtain ⟨hc1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X U₂ hcommXU₂
    rw [h] at hc1
    obtain ⟨hc2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
      (fun x hx y hy => S.comm_of_mem_conjClosure (c.hU₁U hx) (c.hU₂U hy))
    rw [c.inf_U₂_eq] at hc2
    have hle : X ⊔ U₂ ≤ U₁ ⊔ U₂ := sup_le (sup_le le_sup_left hEsup) le_sup_right
    have hcard := Subgroup.card_le_of_le hle
    have hZpos : 0 < Nat.card Zz := Nat.card_pos
    have hU₂pos : 0 < Nat.card U₂ := Nat.card_pos
    have hcard2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
    have hXle : Nat.card X ≤ Nat.card U₁ := by
      have h3 : Nat.card X * Nat.card U₂ ≤ Nat.card U₁ * Nat.card U₂ := by
        have : Nat.card ↥(X ⊔ U₂) * Nat.card Zz ≤ Nat.card ↥(U₁ ⊔ U₂) * Nat.card Zz :=
          Nat.mul_le_mul_right _ hcard
        rw [hc1, hc2] at this
        exact this
      exact Nat.le_of_mul_le_mul_right h3 hU₂pos
    have hXeq : U₁ = X := Subgroup.eq_of_le_of_card_ge le_sup_left hXle
    intro x hx
    apply hE₁
    refine ⟨?_, hx.2⟩
    rw [hXeq]
    exact Subgroup.mem_sup_right hx
  ·
    exfalso
    have hle : U₂ ≤ X := inf_eq_right.mp h
    have hUsup : U₁ ⊔ E ≤ uOfL22 T M := hXU
    have hDN : E ≤ Subgroup.normalizer (Zz : Set G) := hEU.trans (S.conjClosure_le_normalizer_Z hG)
    refine c.hSec.false_of_decomp c.hsimple c.hQ' c.h168 c.hsK c.hsZ c.hout hDN hKE
      (c.hU₂ ▸ c.hZU₂) hE₁' hE₂' (c.hU₂ ▸ hle) ?_ ?_
    · intro x hx y hy
      have e : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [S.comm_of_mem_conjClosure (hUsup hx) (hUsup hy)]; group
      rw [e]; exact Subgroup.one_mem _
    · intro x hx
      rw [isElemAbelian_pow_eq_one hUab (hUsup hx)]
      exact Subgroup.one_mem _

theorem PCtx.exists_q_move (S : Setting146 G T M) (c : PCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ U₁ ⊔ U₂) (hxZ : x ∉ Zz) :
    ∃ q ∈ pCoreOf 2 (mcOf T), ∃ z' ∈ Zz, z' ≠ 1 ∧ q * x * q⁻¹ = x * z' := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hxC : x ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := fun h =>
    hxZ (c.inf_centralizer_Q S ⟨hx, h⟩)
  rw [Subgroup.mem_centralizer_iff] at hxC
  push Not at hxC
  obtain ⟨q, hq, hqx⟩ := hxC
  have hxU : x ∈ uOfL22 T M := sup_le c.hU₁U c.hU₂U hx
  have hcomm := S.comm_mem_Z hG hxU hq
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  refine ⟨q, hq, ⁅q, x⁆, hcomm, ?_, ?_⟩
  · intro h1
    apply hqx
    rw [commutatorElement_def] at h1
    calc q * x = (q * x * q⁻¹ * x⁻¹) * (x * q) := by group
      _ = x * q := by rw [h1, one_mul]
  · have h1 : x * ⁅q, x⁆ = ⁅q, x⁆ * x := S.comm_of_mem_conjClosure hxU (hZU hcomm)
    calc q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
      _ = ⁅q, x⁆ * x := by rw [commutatorElement_def]
      _ = x * ⁅q, x⁆ := h1.symm

theorem PCtx.pure_conj (S : Setting146 G T M) (c : PCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ U₁ ∨ x ∈ U₂) (hxZ : x ∉ Zz) : ∃ h ∈ mcOf T, h * u * h⁻¹ = x := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have key : ∀ x₁ ∈ U₁, x₁ ∉ Zz → ∃ h ∈ mcOf T, h * u * h⁻¹ = x₁ := by
    intro x₁ hx₁ hx₁Z
    have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := c.hSec.norm
    have hel := c.hSec.isElemAbelian_tilde
    have hcommW : ∀ a b : ↥(tildeOf Zz U₁), a * b = b * a :=
      fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2)
    have hsqW : ∀ a : ↥(tildeOf Zz U₁), a ^ 2 = 1 := fun a =>
      Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
    have hne1 : ∀ y (hy : y ∈ U₁), y ∉ Zz → tildeElt hUZ y hy ≠ 1 := by
      intro y hy hyZ h
      apply hyZ
      have h1 := congrArg
        (fun w : ↥(tildeOf Zz U₁) => (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
      exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
    obtain ⟨ψ, hψ⟩ := exists_mulAut_apply_eq hcommW hsqW c.hSec.card_tilde
      (hne1 u c.huU c.huZ) (hne1 x₁ hx₁ hx₁Z)
    obtain ⟨k, hk⟩ := c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 ψ
    have hkU : (k : G) * u * (k : G)⁻¹ ∈ U₁ :=
      (Subgroup.mem_normalizer_iff.mp (c.hSec.KU k.2) u).mp c.huU
    have h1 : secRho c.hSec.KZ c.hSec.KU k (tildeElt hUZ u c.huU) = tildeElt hUZ x₁ hx₁ := by
      have hrho : c.hSec.rho k = secRho c.hSec.KZ c.hSec.KU k := rfl
      rw [← hrho, hk]
      exact hψ
    rw [secRho_tildeElt c.hSec.KZ c.hSec.KU hUZ k u c.huU hkU] at h1
    have hz'' : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ ∈ Zz := (tildeElt_eq_iff hUZ hkU hx₁).mp h1
    have hx₀Z : (k : G) * u * (k : G)⁻¹ ∉ Zz := by
      intro hZ
      apply c.huZ
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (c.hSec.KZ k.2)) _).mp hZ
      have e : (k : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) * (k : G)⁻¹⁻¹ = u := by group
      rwa [e] at this
    have hkH : (k : G) ∈ mcOf T := hKH k.2
    by_cases hz1 : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ = 1
    · refine ⟨k, hkH, ?_⟩
      have : x₁ = (k : G) * u * (k : G)⁻¹ := by
        have e : x₁ = ((k : G) * u * (k : G)⁻¹) * (((k : G) * u * (k : G)⁻¹)⁻¹ * x₁) := by group
        rw [e, hz1, mul_one]
      exact this.symm
    · obtain ⟨q, hq, z', hz', hz'1, hqz⟩ := c.exists_q_move S
        (Subgroup.mem_sup_left hkU) hx₀Z
      have hzz : ((k : G) * u * (k : G)⁻¹)⁻¹ * x₁ = z' :=
        S.Z_eq_of_iff hz'' hz' (by simp only [hz1, hz'1])
      refine ⟨q * k, (mcOf T).mul_mem (pCoreOf_le 2 (mcOf T) hq) hkH, ?_⟩
      have e : x₁ = ((k : G) * u * (k : G)⁻¹) * z' := by
        rw [← hzz]; group
      calc (q * k) * u * (q * k)⁻¹ = q * ((k : G) * u * (k : G)⁻¹) * q⁻¹ := by group
        _ = ((k : G) * u * (k : G)⁻¹) * z' := hqz
        _ = x₁ := e.symm
  rcases hx with hx | hx
  · exact key x hx hxZ
  · have hx' : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ hx)
    have hx'Z : s⁻¹ * x * s ∉ Zz := by
      intro hZ
      apply hxZ
      have := (Subgroup.mem_normalizer_iff.mp c.hsZ _).mp hZ
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at this
    obtain ⟨h', hh', hh'u⟩ := key _ hx' hx'Z
    refine ⟨s * h', (mcOf T).mul_mem hsH hh', ?_⟩
    calc (s * h') * u * (s * h')⁻¹ = s * (h' * u * h'⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * x * s) * s⁻¹ := by rw [hh'u]
      _ = x := by group


theorem PCtx.pure_not_conj (S : Setting146 G T M) (h4 : Stage1463Four) (c : PCtx T M K U₁ U₂ s u)
    {x : G} (hx : x ∈ U₁ ∨ x ∈ U₂) (hxZ : x ∉ Zz) :
    ∀ (y z : G), z ∈ Zz → z ≠ 1 → y * z * y⁻¹ ≠ x := by
  intro y z hz hz1 hyz
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨h, hh, hhu⟩ := c.pure_conj S hx hxZ
  apply (h4 G T M S (mcOf T) hG u c.hinv).2.2 (h⁻¹ * y) z hz hz1
  calc (h⁻¹ * y) * z * (h⁻¹ * y)⁻¹ = h⁻¹ * (y * z * y⁻¹) * h := by group
    _ = h⁻¹ * x * h := by rw [hyz]
    _ = u := by rw [← hhu]; group

end QMove

end CFSG.Quasithin.ThreeD
