module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6C
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

open CFSG.Quasithin.G11 CFSG.Open CFSG.Quasithin.G8 CFSG.Quasithin.SzN31
open CFSG.Quasithin.SzN31.SmD6 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure Ctx0 (Γ A : Subgroup (GLV V)) : Prop where
  hyp : G94Hyp Γ A 2
  hd : Module.finrank (ZMod 2) V = 6
  three : ∀ S : Subgroup (GLV V), S ≤ Γ → IsPGroup 3 S → Nat.card S ≤ 27

variable {Γ A : Subgroup (GLV V)}

theorem Ctx0.A_le_centralizer (hC : Ctx0 Γ A) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) := by
  by_contra hnot
  have h4 := (counting_prime_ge_five hC.hyp hp h5 hnot).2.2
  have h6 := hC.hd
  omega


theorem Ctx0.inf_centralizer_eq_bot (hC : Ctx0 Γ A) :
    A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)) = ⊥ :=
  g94_inf_centralizer_pCoreOf_three_eq_bot hC.hyp fun _ hp h5 => hC.A_le_centralizer hp h5


theorem Ctx0.pCoreOf_three_ne_bot (hC : Ctx0 Γ A) : pCoreOf 3 Γ ≠ ⊥ := by
  intro h
  have hA : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)) := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      rw [h, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      rw [hx]
      simp
    rwa [hC.inf_centralizer_eq_bot] at this
  have h1 := hC.hyp.A_card
  rw [hA, Subgroup.card_bot] at h1
  omega


theorem Ctx0.exists_frame (hC : Ctx0 Γ A) :
    ∃ Fr : Frame V (Fin 2), (∀ i, Fr.x i ∈ pCoreOf 3 Γ) ∧ (∀ i, Fr.x i ≠ 1) ∧ (∀ i, Fr.p i = 3) ∧
      ∀ i, Fr.a i ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_linearEquiv_zmod2 V
  have hyp := hC.hyp
  have hYp : IsPGroup 3 (pCoreOf 3 Γ) := isPGroup_pCoreOf 3 Γ
  have h81 : G81 (pCoreOf 3 Γ) A A :=
    { elemAbelian := hyp.A_elem
      le_pGroup := le_rfl
      pGroup := isPGroup_of_isElemAbelian hyp.A_elem
      le_normalizer := fun a ha => le_normalizer_pCoreOf 3 Γ (hyp.A_le ha)
      nilpotent := hYp.isNilpotent
      odd := odd_card_pCoreOf Nat.prime_three (by norm_num) Γ
      ne_bot := hC.pCoreOf_three_ne_bot }
  obtain ⟨Hs, q, hH, hAle, -, hx⟩ := g8_6 h81 hyp.A_ne hyp.A_card hC.inf_centralizer_eq_bot
  choose x hxY hxH hxo using hx
  obtain ⟨Fr, hFx, hFp, hFa⟩ :=
    exists_frame_of_dihedralFamily hH hyp.A_elem hAle hyp.A_card x hxH hxo
  have hq : ∀ i, q i = 3 := fun i =>
    G8.prime_orderOf_eq_of_mem_pGroup hYp (hxY i) (hxo i) (hH.prime i)
  refine ⟨Fr, fun i => by rw [congrFun hFx i]; exact hxY i, fun i h1 => ?_,
    fun i => by rw [congrFun hFp i]; exact hq i, fun i => (hFa i).1⟩
  have h2 := hxo i
  rw [← congrFun hFx i, h1, orderOf_one, hq i] at h2
  exact absurd h2 (by norm_num)


theorem Ctx0.fixedSpace_eq_bot (hC : Ctx0 Γ A) : fixedSpace (pCoreOf 3 Γ) = ⊥ :=
  g94_fixedSpace_pCoreOf_eq_bot hC.hyp hC.pCoreOf_three_ne_bot


omit [Finite V] in
theorem Ctx0.card_le (hC : Ctx0 Γ A) : Nat.card (pCoreOf 3 Γ) ≤ 27 :=
  hC.three _ (pCoreOf_le 3 Γ) (isPGroup_pCoreOf 3 Γ)


theorem Ctx0.exists_frame_elements (hC : Ctx0 Γ A) :
    ∃ x₀ x₁ a₀ a₁ : GLV V, x₀ ∈ pCoreOf 3 Γ ∧ x₁ ∈ pCoreOf 3 Γ ∧ a₀ ∈ A ∧ a₁ ∈ A ∧
      x₀ ^ 3 = 1 ∧ x₁ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ x₁ ≠ 1 ∧ x₀ * x₁ = x₁ * x₀ ∧ a₀ * a₀ = 1 ∧
      a₁ * a₁ = 1 ∧ a₀ * x₀ * a₀⁻¹ = x₀⁻¹ ∧ a₁ * x₁ * a₁⁻¹ = x₁⁻¹ ∧ a₀ * x₁ = x₁ * a₀ ∧
      a₁ * x₀ = x₀ * a₁ ∧ x₁ ∉ Subgroup.zpowers x₀ := by
  obtain ⟨Fr, hFxP, hFx1, hFp, hFaA⟩ := hC.exists_frame
  have h3 : ∀ i, Fr.x i ^ 3 = 1 := fun i => by
    have := Fr.xpow i
    rwa [hFp i] at this
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hx1a0 : Fr.a 0 * Fr.x 1 = Fr.x 1 * Fr.a 0 := (Fr.xa 1 0 h10).symm
  have hx0a1 : Fr.a 1 * Fr.x 0 = Fr.x 0 * Fr.a 1 := (Fr.xa 0 1 h01).symm
  refine ⟨Fr.x 0, Fr.x 1, Fr.a 0, Fr.a 1, hFxP 0, hFxP 1, hFaA 0, hFaA 1, h3 0, h3 1, hFx1 0,
    hFx1 1, Fr.xx 0 1 h01, Fr.asq 0, Fr.asq 1, Fr.conj 0, Fr.conj 1, hx1a0, hx0a1, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hconj : Fr.a 0 * Fr.x 1 * (Fr.a 0)⁻¹ = Fr.x 1 := by
    rw [hx1a0]; group
  have h2 : Fr.a 0 * Fr.x 1 * (Fr.a 0)⁻¹ = (Fr.x 1)⁻¹ := by
    rw [← hk]
    have := map_zpow (MulAut.conj (Fr.a 0)) (Fr.x 0) k
    simp only [MulAut.conj_apply] at this
    rw [this, Fr.conj 0, inv_zpow]
  have hsq : Fr.x 1 * Fr.x 1 = 1 := by
    have h3' : Fr.x 1 = (Fr.x 1)⁻¹ := hconj.symm.trans h2
    calc Fr.x 1 * Fr.x 1 = Fr.x 1 * (Fr.x 1)⁻¹ := by rw [← h3']
      _ = 1 := mul_inv_cancel _
  apply hFx1 1
  calc Fr.x 1 = Fr.x 1 ^ 3 * (Fr.x 1 * Fr.x 1)⁻¹ := by group
    _ = 1 := by rw [h3 1, hsq]; simp


theorem Ctx0.nine_le_card (hC : Ctx0 Γ A) : 9 ≤ Nat.card (pCoreOf 3 Γ) := by
  obtain ⟨x₀, x₁, a₀, a₁, hx₀, hx₁, -, -, h30, -, hne0, -, -, -, -, -, -, -, -, hne⟩ :=
    hC.exists_frame_elements
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (isPGroup_pCoreOf 3 Γ).exists_card_eq
  by_contra hlt
  push Not at hlt
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h2
    omega
  have hord : orderOf x₀ = 3 := orderOf_eq_prime h30 hne0
  have hz : Nat.card (Subgroup.zpowers x₀) = 3 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers x₀ ≤ pCoreOf 3 Γ := (Subgroup.zpowers_le).2 hx₀
  have hcard : Nat.card (pCoreOf 3 Γ) ≤ Nat.card (Subgroup.zpowers x₀) := by
    rw [hk, hz]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  exact hne ((Subgroup.eq_of_le_of_card_ge hle hcard) ▸ hx₁)


theorem Ctx0.simple_or_planes (hC : Ctx0 Γ A) :
    (∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) ∨
      ∃ W : Fin 3 → Submodule (ZMod 2) V, ThreePlanes Γ (CFSG.Open.pCoreOf 3 Γ) W := by
  classical
  have hirr := hC.hyp.irreducible
  have hPn : ∀ γ ∈ Γ, ∀ n ∈ CFSG.Open.pCoreOf 3 Γ, γ * n * γ⁻¹ ∈ CFSG.Open.pCoreOf 3 Γ :=
    pCoreOf_normal_conj 3 Γ
  have hP3 : IsPGroup 3 (CFSG.Open.pCoreOf 3 Γ) := isPGroup_pCoreOf 3 Γ
  have hfix : fixedSpace (CFSG.Open.pCoreOf 3 Γ) = ⊥ := hC.fixedSpace_eq_bot
  have hex : ∃ n, ∃ U : Submodule (ZMod 2) V, U ≠ ⊥ ∧ Invariant (CFSG.Open.pCoreOf 3 Γ) U ∧
      Module.finrank (ZMod 2) U = n := ⟨_, ⊤, hirr.ne_bot, invariant_top _, rfl⟩
  obtain ⟨W, hWne, hWinv, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U ≠ ⊥ →
      Nat.find hex ≤ Module.finrank (ZMod 2) U := fun U h1 h2 => Nat.find_min' hex ⟨U, h2, h1, rfl⟩
  generalize Nat.find hex = n at hWn hmin
  have hdvd : 3 ∣ 2 ^ n - 1 := by
    rw [← hWn]
    exact pgroup_dvd_two_pow Nat.prime_three _ hP3 W hWinv (fun v hvW hv => by
      have hv' : v ∈ fixedSpace (CFSG.Open.pCoreOf 3 Γ) := fun q hq => hv q hq
      rw [hfix] at hv'
      exact (Submodule.mem_bot (ZMod 2)).1 hv')
  have heven : Even n := by
    by_contra h
    exact not_three_dvd_two_pow_sub_one_of_odd (Nat.not_even_iff_odd.1 h) hdvd
  have hnpos : 0 < n := by
    rw [← hWn]
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    exact Nat.pos_of_ne_zero fun h => hWne (Submodule.finrank_eq_zero.1 h)
  have hn6 : n ≤ 6 := by
    rw [← hWn, ← hC.hd]
    exact Submodule.finrank_le W
  have hn4 : n ≠ 4 := by
    intro h4
    have hodd := odd_card_pCoreOf Nat.prime_three (by norm_num) Γ
    have hnd : ¬ 2 ∣ Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) := by
      have := Nat.odd_iff.1 hodd
      omega
    obtain ⟨U', hU'inv, hcompl⟩ := exists_invariant_isCompl_of_odd hnd hWinv
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hC.hd, hWn, h4] at hsum
    have hU'ne : U' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hsum
      omega
    have := hmin U' hU'inv hU'ne
    omega
  have hn : n = 2 ∨ n = 6 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hn with rfl | rfl
  · exact Or.inr (exists_threePlanes hirr hPn hC.hd hWinv hWn hmin)
  · left
    intro U hUinv
    by_cases hU : U = ⊥
    · exact Or.inl hU
    · right
      apply Submodule.eq_top_of_finrank_eq
      have h1 := hmin U hUinv hU
      have h2 : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le U
      rw [hC.hd] at h2 ⊢
      omega


theorem Ctx0.nonabelian_of_simple (hC : Ctx0 Γ A)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) :
    ∃ u ∈ CFSG.Open.pCoreOf 3 Γ, ∃ v ∈ CFSG.Open.pCoreOf 3 Γ, u * v ≠ v * u := by
  by_contra hab
  push Not at hab
  obtain ⟨x₀, x₁, a₀, a₁, hx₀, hx₁, -, -, h30, h31, hne0, hne1, hcomm, -, -, -, -, -, -, hne⟩ :=
    hC.exists_frame_elements
  have hfpf : ∀ h ∈ CFSG.Open.pCoreOf 3 Γ, h ≠ 1 → ∀ v, h v = v → v = 0 := by
    intro h hh hne1 v hv
    have hinv : Invariant (CFSG.Open.pCoreOf 3 Γ) (fixSp V h ⊤) := fun p hp u hu =>
      fixSp_invariant (hab p hp h hh) (fun _ _ => Submodule.mem_top) u hu
    rcases hs _ hinv with h0 | h1
    · have : v ∈ fixSp V h ⊤ := mem_fixSp.2 ⟨Submodule.mem_top, hv⟩
      rw [h0] at this
      exact (Submodule.mem_bot (ZMod 2)).1 this
    · exfalso
      apply hne1
      ext u
      have : u ∈ fixSp V h ⊤ := by rw [h1]; exact Submodule.mem_top
      exact (mem_fixSp.1 this).2
  have hne01 : x₀ * x₁ ≠ 1 := by
    intro h
    apply hne
    have : x₁ = x₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x₀)
  have hP := (CFSG.Open.pCoreOf 3 Γ).mul_mem hx₀ hx₁
  have hc : Commute x₀ x₁ := hcomm
  have h3 : (x₀ * x₁) ^ 3 = 1 := by rw [hc.mul_pow, h30, h31, one_mul]
  have heq := eq_of_fpf_commuting hcomm h30 h31 h3 (hfpf x₀ hx₀ hne0) (hfpf x₁ hx₁ hne1)
    (hfpf _ hP hne01)
  exact hne (heq ▸ Subgroup.mem_zpowers x₀)


theorem Ctx0.card_eq_27 (hC : Ctx0 Γ A)
    (hnc : ∃ u ∈ CFSG.Open.pCoreOf 3 Γ, ∃ v ∈ CFSG.Open.pCoreOf 3 Γ, u * v ≠ v * u) :
    Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) = 27 := by
  have h27 := hC.card_le
  by_contra hne
  have h9 : Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) ≤ 9 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (isPGroup_pCoreOf 3 Γ).exists_card_eq
    have hk3 : k ≤ 2 := by
      by_contra hlt
      have h3 : 3 ≤ k := by omega
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h3
      omega
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 9 := by norm_num
  obtain ⟨u, hu, v, hv, huv⟩ := hnc
  exact huv (congrArg Subtype.val (commutative_of_card_le_nine (isPGroup_pCoreOf 3 Γ) h9
    ⟨u, hu⟩ ⟨v, hv⟩))


end CFSG.Quasithin.SzG11G94
