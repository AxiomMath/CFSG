module

public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofModel
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofA6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156Res4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree Subgroup Equiv
open CFSG.RankThree.Native.ONTriple
open scoped commutatorElement

variable {X : Type} [Group X]

@[expose] def liftSignal (K : Subgroup X) (ρ : ↥K →* Perm (Fin 6)) (V : Subgroup (Perm (Fin 6)))
    (hker : ∀ k : ↥K, ρ k = 1 → (k : X) ∈ center X) (hZ3 : ∀ z ∈ center X, z ^ 3 = 1)
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) : Subgroup X where
  carrier := {x | ∃ hx : x ∈ K, ρ ⟨x, hx⟩ ∈ V ∧ x ^ 2 = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxV, hx2⟩ ⟨hy, hyV, hy2⟩
    have hρxy : ρ ⟨x * y, mul_mem hx hy⟩ = ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ := by
      rw [← map_mul]
      rfl
    refine ⟨mul_mem hx hy, by rw [hρxy]; exact mul_mem hxV hyV, ?_⟩
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
    have huK : x * y * x⁻¹ * y⁻¹ ∈ K := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    have hρu : ρ ⟨x * y * x⁻¹ * y⁻¹, huK⟩ = 1 := by
      have e : ρ ⟨x * y * x⁻¹ * y⁻¹, huK⟩ =
          ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ * (ρ ⟨x, hx⟩)⁻¹ * (ρ ⟨y, hy⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, hVc _ hxV _ hyV]
      group
    have huZ : x * y * x⁻¹ * y⁻¹ ∈ center X := hker _ hρu
    have hu3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := hZ3 _ huZ
    rw [hxi, hyi] at huZ hu3
    have hxu : x * (x * y * x * y) * x⁻¹ = (x * y * x * y)⁻¹ := by
      rw [hxi]
      calc x * (x * y * x * y) * x = x ^ 2 * (y * x * y * x) := by rw [sq]; group
        _ = y * x * y * x := by rw [hx2, one_mul]
        _ = y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ := by rw [hxi, hyi]
        _ = (x * y * x * y)⁻¹ := by group
    have hcen : x * (x * y * x * y) * x⁻¹ = x * y * x * y := by
      rw [mem_center_iff.mp huZ x, mul_inv_cancel_right]
    have hu2 : (x * y * x * y) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [← hcen]
      rw [hxu, mul_inv_cancel]
    have hco : Nat.Coprime 2 3 := by norm_num
    have hu1 := (pow_gcd_eq_one (a := x * y * x * y)).mpr ⟨hu2, hu3⟩
    rw [hco.gcd_eq_one, pow_one] at hu1
    rw [sq, show x * y * (x * y) = x * y * x * y by group, hu1]
  one_mem' := ⟨one_mem K, by
    rw [show (⟨1, one_mem K⟩ : ↥K) = 1 from rfl, map_one]
    exact one_mem V, one_pow 2⟩
  inv_mem' := by
    rintro x ⟨hx, hxV, hx2⟩
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
    rw [hxi]
    exact ⟨hx, hxV, hx2⟩

section Lift

variable {K : Subgroup X} {ρ : ↥K →* Perm (Fin 6)} {V : Subgroup (Perm (Fin 6))}
  {hker : ∀ k : ↥K, ρ k = 1 → (k : X) ∈ center X} {hZ3 : ∀ z ∈ center X, z ^ 3 = 1}
  {hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v}

theorem liftSignal_le : liftSignal K ρ V hker hZ3 hVc ≤ K := fun _ ⟨hx, _, _⟩ => hx

theorem liftSignal_sq : ∀ r ∈ liftSignal K ρ V hker hZ3 hVc, r ^ 2 = 1 :=
  fun _ ⟨_, _, h⟩ => h

theorem exists_mem_liftSignal (hρ : ρ.range = alternatingGroup (Fin 6))
    (hVA : V ≤ alternatingGroup (Fin 6)) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ∀ v ∈ V, ∃ r : ↥K, (r : X) ∈ liftSignal K ρ V hker hZ3 hVc ∧ ρ r = v := by
  intro v hv
  have hvA : v ∈ ρ.range := hρ ▸ hVA hv
  obtain ⟨k, hk⟩ := hvA
  have hk2 : ρ (k ^ 2) = 1 := by rw [map_pow, hk, hV2 v hv]
  have hkZ := hker _ hk2
  have hρk3 : ρ (k ^ 3) = v := by
    rw [map_pow, hk, pow_succ, hV2 v hv, one_mul]
  refine ⟨k ^ 3, ⟨(k ^ 3).2, ?_, ?_⟩, hρk3⟩
  · rw [show (⟨((k ^ 3 : ↥K) : X), (k ^ 3).2⟩ : ↥K) = k ^ 3 from rfl, hρk3]
    exact hv
  · rw [Subgroup.coe_pow, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul,
      ← Subgroup.coe_pow]
    exact hZ3 _ hkZ

theorem conj_mem_liftSignal (k₀ : ↥K) (hk₀ : ρ k₀ ∈ normalizer (V : Set (Perm (Fin 6)))) :
    ∀ r ∈ liftSignal K ρ V hker hZ3 hVc,
      (k₀ : X) * r * (k₀ : X)⁻¹ ∈ liftSignal K ρ V hker hZ3 hVc := by
  rintro r ⟨hr, hrV, hr2⟩
  have hmem : (k₀ : X) * r * (k₀ : X)⁻¹ ∈ K := mul_mem (mul_mem k₀.2 hr) (inv_mem k₀.2)
  refine ⟨hmem, ?_, ?_⟩
  · have e : ρ ⟨(k₀ : X) * r * (k₀ : X)⁻¹, hmem⟩ = ρ k₀ * ρ ⟨r, hr⟩ * (ρ k₀)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (mem_normalizer_iff.mp hk₀ _).mp hrV
  · rw [sq, show (k₀ : X) * r * (k₀ : X)⁻¹ * ((k₀ : X) * r * (k₀ : X)⁻¹) =
      (k₀ : X) * (r * r) * (k₀ : X)⁻¹ by group, ← sq, hr2, mul_one, mul_inv_cancel]

end Lift

section Rho

variable {K : Subgroup X} {ρ : ↥K →* Perm (Fin 6)}

theorem center_eq_ker_of_rho (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X) : center ↥K = ρ.ker := by
  ext k
  rw [MonoidHom.mem_ker]
  constructor
  · intro hk
    have hmem : ρ k ∈ alternatingGroup (Fin 6) := hρ ▸ ⟨k, rfl⟩
    have hc : (⟨ρ k, hmem⟩ : ↥(alternatingGroup (Fin 6))) ∈
        center ↥(alternatingGroup (Fin 6)) := by
      rw [mem_center_iff]
      rintro ⟨σ, hσ⟩
      rw [← hρ] at hσ
      obtain ⟨k', rfl⟩ := hσ
      apply Subtype.ext
      show ρ k' * ρ k = ρ k * ρ k'
      rw [← map_mul, ← map_mul, mem_center_iff.mp hk k']
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc
    exact congrArg Subtype.val hc
  · intro hk
    rw [hker] at hk
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hk g)

theorem isTripleCover_of_rho (hZK : center X ≤ K) (hZ3 : Nat.card (center X) = 3)
    (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X) :
    Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) := by
  have hc := center_eq_ker_of_rho hρ hker
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hρ))⟩⟩
  have hk : ρ.ker = (center X).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, hker, mem_subgroupOf]
  rw [hc, hk, Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv, hZ3]

theorem le_of_three_elements (hZ3 : ∀ z ∈ center X, z ^ 3 = 1)
    (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X) {H : Subgroup X}
    (hH : ∀ x ∈ K, (∃ e : ℕ, x ^ 3 ^ e = 1) → x ∈ H) : K ≤ H := by
  have h3c : alternatingGroup (Fin 6) ≤ (H.subgroupOf K).map ρ := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, closure_le]
    intro σ hσ
    have hσ' : σ.IsThreeCycle := hσ
    have hσA : σ ∈ ρ.range := hρ ▸ Equiv.Perm.mem_alternatingGroup.mpr hσ'.sign
    obtain ⟨k, rfl⟩ := hσA
    refine ⟨k, ?_, rfl⟩
    have hk3 : ρ (k ^ 3) = 1 := by rw [map_pow, ← hσ'.orderOf, pow_orderOf_eq_one]
    have hkZ := (hker _).mp hk3
    have h9 : (k : X) ^ 3 ^ 2 = 1 := by
      rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ← Subgroup.coe_pow]
      exact hZ3 _ hkZ
    exact mem_subgroupOf.mpr (hH k k.2 ⟨2, h9⟩)
  intro x hx
  have hρx : ρ ⟨x, hx⟩ ∈ alternatingGroup (Fin 6) := hρ ▸ ⟨_, rfl⟩
  obtain ⟨h, hh, hhx⟩ := h3c hρx
  have hz : ((h⁻¹ * ⟨x, hx⟩ : ↥K) : X) ∈ center X :=
    (hker _).mp (by rw [map_mul, map_inv, hhx, inv_mul_cancel])
  have hzH : ((h⁻¹ * ⟨x, hx⟩ : ↥K) : X) ∈ H :=
    hH _ (h⁻¹ * ⟨x, hx⟩).2 ⟨1, by rw [pow_one]; exact hZ3 _ hz⟩
  have e : x = (h : X) * ((h⁻¹ * ⟨x, hx⟩ : ↥K) : X) := by simp
  rw [e]
  exact mul_mem (mem_subgroupOf.mp hh) hzH

theorem le_of_signals (hperf : Group.IsPerfect ↥K)
    (hZ3 : ∀ z ∈ center X, z ^ 3 = 1) (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X) {t : Perm (Fin 6)}
    (htA : t ∈ alternatingGroup (Fin 6)) (ht3 : t ^ 3 = 1) {H : Subgroup X}
    (hH : ∀ (V : Subgroup (Perm (Fin 6))) (hV : IsA6Signal t V),
      liftSignal K ρ V (fun k => (hker k).mp) hZ3 hV.2.1 ≤ H) : K ≤ H := by
  have hgen : alternatingGroup (Fin 6) ≤ (H.subgroupOf K).map ρ := by
    refine (alternatingGroup_le_closure_signal htA ht3).trans ?_
    rw [closure_le]
    rintro x ⟨V, hV, hxV⟩
    obtain ⟨r, hrR, hrx⟩ := exists_mem_liftSignal (hker := fun k => (hker k).mp) (hZ3 := hZ3)
      (hVc := hV.2.1) hρ hV.1 hV.2.2.1 x hxV
    exact ⟨r, mem_subgroupOf.mpr (hH V hV hrR), hrx⟩
  have hdec : ∀ k : ↥K, ∃ h : ↥K, (h : X) ∈ H ∧ ((h⁻¹ * k : ↥K) : X) ∈ center X := by
    intro k
    have hρk : ρ k ∈ alternatingGroup (Fin 6) := hρ ▸ ⟨k, rfl⟩
    obtain ⟨h, hh, hhk⟩ := hgen hρk
    exact ⟨h, mem_subgroupOf.mp hh, (hker _).mp (by rw [map_mul, map_inv, hhk, inv_mul_cancel])⟩
  have hcomm : commutator ↥K ≤ H.subgroupOf K := by
    rw [commutator_def, commutator_le]
    intro k₁ _ k₂ _
    obtain ⟨h₁, hh₁, hz₁⟩ := hdec k₁
    obtain ⟨h₂, hh₂, hz₂⟩ := hdec k₂
    set z₁ := h₁⁻¹ * k₁ with hz₁def
    set z₂ := h₂⁻¹ * k₂ with hz₂def
    have hz₁' : z₁ ∈ center ↥K := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hz₁ g)
    have hz₂' : z₂ ∈ center ↥K := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hz₂ g)
    have e₁ : k₁ = h₁ * z₁ := by rw [hz₁def]; group
    have e₂ : k₂ = h₂ * z₂ := by rw [hz₂def]; group
    have hc : ⁅k₁, k₂⁆ = ⁅h₁, h₂⁆ := by
      rw [e₁, e₂, commutatorElement_def, commutatorElement_def]
      have c1 := mem_center_iff.mp hz₁'
      have c2 := mem_center_iff.mp hz₂'
      calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹
          = h₁ * (z₁ * h₂) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * (h₂ * z₁) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by rw [c1 h₂]
        _ = h₁ * h₂ * (z₁ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * z₂ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by
          rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [← c1 z₂]; group]
        _ = h₁ * h₂ * (z₂ * h₁⁻¹) * z₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * (h₁⁻¹ * z₂) * z₂⁻¹ * h₂⁻¹ := by rw [c2 h₁⁻¹]
        _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by group
    rw [hc, mem_subgroupOf, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := hcomm (hperf.commutator_eq_top ▸ mem_top _)
  exact mem_subgroupOf.mp this

end Rho

theorem exists_cover_on
    [Finite X] (ψ : X ≃* GM) (hZ3 : Nat.card (center X) = 3) {B : Subgroup X}
    (hB : Late.IsE27 B) {c : X} (hc : c ∈ B) :
    ∃ K : Subgroup X, K ≤ centralizer ({c} : Set X) ∧ B ≤ normalizer (K : Set X) ∧
      center X ≤ K ∧ Group.IsPerfect ↥K ∧ Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) ∧
      (∀ H : Subgroup X, (∀ x ∈ K, (∃ e : ℕ, x ^ 3 ^ e = 1) → x ∈ H) → K ≤ H) ∧
      (∀ H : Subgroup X, (∀ R : Subgroup X, R ≤ K → B ≤ normalizer (R : Set X) →
        (∀ r ∈ R, r ^ 2 = 1) → R ≤ H) → K ≤ H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := hB.1.2
  have hZexp : ∀ z ∈ center X, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := center X) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hZB : center X ≤ B := by
    have hB' := Sec13.ON134.isE27_map hB ψ.toMonoidHom ψ.injective
    obtain ⟨z₀, hz₀B, hz₀⟩ := zG_mem_E27 hB'
    intro z hzZ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ((Sec13.ON134.mem_center_iff_model ψ).1 hzZ)
    have hz₀' : ψ z₀ = zG := hz₀
    have e : z = z₀ ^ k := by
      apply ψ.injective
      rw [map_zpow, hz₀', hk]
    rw [e]
    exact zpow_mem hz₀B k
  obtain ⟨b, hbB, hbz, hcb⟩ : ∃ b ∈ B, b ∉ center X ∧ c ∈ zpowers b ⊔ center X := by
    by_cases hcz : c ∈ center X
    · have hne : ¬ B ≤ center X := by
        intro hle
        have := Subgroup.card_le_of_le hle
        rw [hB.2, hZ3] at this
        omega
      obtain ⟨b, hbB, hbz⟩ := Set.not_subset.mp hne
      exact ⟨b, hbB, hbz, mem_sup_right hcz⟩
    · exact ⟨c, hc, hcz, mem_sup_left (mem_zpowers c)⟩
  have hb3 : b ^ 3 = 1 := hB3 b hbB
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  obtain ⟨K, hC, hinf, hZK, ρ, hρ, hker⟩ := exists_centralizer_eq ψ hb3 hbz
  have hKb : K ≤ centralizer ({b} : Set X) := hC ▸ le_sup_right
  have hbK : b ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hKb hk)
  have hKc : K ≤ centralizer ({c} : Set X) := by
    have hle : zpowers b ⊔ center X ≤ centralizer (K : Set X) :=
      sup_le (zpowers_le.mpr hbK) (Subgroup.center_le_centralizer _)
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (hle hcb) k hk
  have hBCb : B ≤ centralizer ({b} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hBc x hx b hbB)
  have hbN : zpowers b ≤ normalizer (K : Set X) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hbK)
  have hBsup : B ≤ zpowers b ⊔ K := hC ▸ hBCb
  have hBN : B ≤ normalizer (K : Set X) := hBsup.trans (sup_le hbN Subgroup.le_normalizer)
  have hperf := isPerfect_of_centralizer_eq ψ hZ3 hb3 hbz hKb hinf hZK hρ hker
  have hTC := isTripleCover_of_rho hZK hZ3 hρ hker
  refine ⟨K, hKc, hBN, hZK, hperf, hTC, fun H hH => le_of_three_elements hZexp hρ hker hH, ?_⟩
  intro H hH
  have hdecB : ∀ g ∈ B, ∃ k₀ : ↥K, (k₀ : X) ∈ B ∧
      ∀ k ∈ K, g * k * g⁻¹ = (k₀ : X) * k * (k₀ : X)⁻¹ := by
    intro g hg
    have hg' : g ∈ ((zpowers b ⊔ K : Subgroup X) : Set X) := hBsup hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbN] at hg'
    obtain ⟨u, hu, k₀, hk₀, rfl⟩ := hg'
    have hu' : u ∈ B := zpowers_le.mpr hbB hu
    have huc : ∀ w ∈ K, u * w = w * u := by
      intro w hw
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
      exact (Commute.zpow_left
        (show Commute b w from (mem_centralizer_singleton_iff.mp (hKb hw)).symm) i).eq
    have hg2 : u * k₀ ∈ B := hg
    refine ⟨⟨k₀, hk₀⟩, ?_, fun k hk => ?_⟩
    · show k₀ ∈ B
      have e : k₀ = u⁻¹ * (u * k₀) := by group
      rw [e]
      exact mul_mem (inv_mem hu') hg2
    · have hw : k₀ * k * k₀⁻¹ ∈ K := mul_mem (mul_mem hk₀ hk) (inv_mem hk₀)
      calc u * k₀ * k * (u * k₀)⁻¹ = u * (k₀ * k * k₀⁻¹) * u⁻¹ := by group
        _ = k₀ * k * k₀⁻¹ := by rw [huc _ hw, mul_inv_cancel_right]
  set E : Subgroup ↥K := B.subgroupOf K with hE
  set T₀ := E.map ρ with hT₀
  have hBK9 : Nat.card (B ⊓ K : Subgroup X) * 3 ≤ 27 := by
    have hc1 : IsMulCommutative (B ⊓ K : Subgroup X) :=
      ⟨⟨fun x y => Subtype.ext (hBc x x.2.1 y y.2.1)⟩⟩
    have hbBK : b ∈ centralizer ((B ⊓ K : Subgroup X) : Set X) :=
      mem_centralizer_iff.mpr fun w hw => hBc w hw.1 b hbB
    have hbnot : b ∉ B ⊓ K := by
      intro hb
      have hbb : b ∈ zpowers b ⊓ K := ⟨mem_zpowers b, hb.2⟩
      rw [hinf] at hbb
      exact hb1 hbb
    obtain ⟨hcard, -, -⟩ :=
      card_sup_zpowers_three hc1 (fun w hw => hB3 w hw.1) hbBK hb3 hb1 hbnot
    rw [← hcard, ← hB.2]
    exact Subgroup.card_le_of_le (sup_le inf_le_left (zpowers_le.mpr hbB))
  have hEcard : Nat.card E = Nat.card (B ⊓ K : Subgroup X) := by
    rw [hE, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective K.subtype_injective]
  have hkerE : ρ.ker ≤ E := fun k hk => mem_subgroupOf.mpr (hZB ((hker k).mp hk))
  have hkercard : Nat.card ρ.ker = 3 := by
    rw [← center_eq_ker_of_rho hρ hker]
    exact hTC.1
  have hT₀card : Nat.card T₀ * 3 = Nat.card E := by
    have h1 := Subgroup.relIndex_mul_card ρ.ker E
    rw [Subgroup.relIndex_ker, inf_eq_left.mpr hkerE, hkercard] at h1
    exact h1
  have hT₀le : Nat.card T₀ ≤ 3 := by omega
  obtain ⟨t, htA, ht3, hT₀t⟩ : ∃ t ∈ alternatingGroup (Fin 6), t ^ 3 = 1 ∧ T₀ ≤ zpowers t := by
    by_cases hT : T₀ = ⊥
    · exact ⟨1, one_mem _, one_pow 3, by rw [hT]; exact bot_le⟩
    obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨e, heE, rfl⟩ := htT
    have he3 : ρ e ^ 3 = 1 := by
      rw [← map_pow]
      have : e ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hB3 _ (mem_subgroupOf.mp heE))
      rw [this, map_one]
    refine ⟨ρ e, hρ ▸ ⟨e, rfl⟩, he3, ?_⟩
    have hle : zpowers (ρ e) ≤ T₀ := zpowers_le.mpr ⟨e, heE, rfl⟩
    have hcard : Nat.card T₀ ≤ Nat.card (zpowers (ρ e)) := by
      rw [Nat.card_zpowers, orderOf_eq_prime he3 ht1']
      exact hT₀le
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm.le
  refine le_of_signals hperf hZexp hρ hker htA ht3 fun V hV => ?_
  refine hH _ liftSignal_le ?_ liftSignal_sq
  intro g hg
  obtain ⟨k₀, hk₀B, hk₀⟩ := hdecB g hg
  have hρk₀ : ρ k₀ ∈ normalizer (V : Set (Perm (Fin 6))) := by
    have hk₀T : ρ k₀ ∈ T₀ := ⟨k₀, mem_subgroupOf.mpr hk₀B, rfl⟩
    exact zpowers_le.mpr hV.2.2.2 (hT₀t hk₀T)
  refine mem_normalizer_of_conj_le (hB3 g hg) fun r hr => ?_
  rw [hk₀ r (liftSignal_le hr)]
  exact conj_mem_liftSignal k₀ hρk₀ r hr

end CFSG.RankThree.PartTwo.Sec15.Proof156Res4
