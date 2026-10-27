module

public import CFSG.Quasithin.H13.NQCatT3Red
public import Certificates.Certificate7157
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open Equiv CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique

@[expose] def a7T0 (hc : A7T3.stmt) : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {x | (x : Perm (Fin 7)) ∈ A7T3.T0l}
  mul_mem' {_ _} ha hb := hc.1 _ ha _ hb
  one_mem' := List.mem_cons_self
  inv_mem' {_} ha := hc.2.1 _ ha

theorem card_a7T0 (hc : A7T3.stmt) : Nat.card ↥(a7T0 hc) = 8 := by
  have e : ↥(a7T0 hc) ≃ {σ : Perm (Fin 7) // σ ∈ A7T3.T0l.toFinset} :=
    { toFun := fun x => ⟨(x : alternatingGroup (Fin 7)), List.mem_toFinset.mpr x.2⟩
      invFun := fun σ => ⟨⟨σ.1, Equiv.Perm.mem_alternatingGroup.mpr
          (hc.2.2.2.1 _ (List.mem_toFinset.mp σ.2))⟩, List.mem_toFinset.mp σ.2⟩
      left_inv := fun x => rfl
      right_inv := fun σ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hc.2.2.1]
  rfl

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

@[expose] noncomputable def a7T0Sylow (hc : A7T3.stmt) : Sylow 2 (alternatingGroup (Fin 7)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card (n := 3) (by rw [card_a7T0 hc]; norm_num) :
    IsPGroup 2 ↥(a7T0 hc)).toSylow (by
      have h1 := Subgroup.card_mul_index (a7T0 hc)
      rw [card_a7T0 hc, card_alt7] at h1
      omega)

theorem a7_conclusion (hc : A7T3.stmt) {P : Type} [Group P] (ψ : P ≃* alternatingGroup (Fin 7))
    {T : Subgroup P} (hT2 : IsPGroup 2 ↥T) (hTi : ¬ 2 ∣ T.index) {x : P}
    (hx3 : ∃ k : ℕ, x ^ (3 ^ k) = 1)
    (hperm : ∀ t ∈ T, ∀ y ∈ Subgroup.zpowers x, ∃ y' ∈ Subgroup.zpowers x, ∃ t' ∈ T,
      t * y = y' * t') :
    x ^ 3 = 1 ∧ ∃ t ∈ T, t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Finite.of_equiv _ ψ.toEquiv.symm
  let TS : Sylow 2 P := hT2.toSylow hTi
  let T' : Sylow 2 (alternatingGroup (Fin 7)) := TS.mapSurjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (a7T0Sylow hc) T'
  have hmemT' : ∀ y : alternatingGroup (Fin 7), y ∈ (T' : Subgroup (alternatingGroup (Fin 7))) ↔
      g⁻¹ * y * g ∈ a7T0 hc := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    rfl
  have hmemT : ∀ y : P, y ∈ T ↔ g⁻¹ * ψ y * g ∈ a7T0 hc := by
    intro y
    rw [← hmemT' (ψ y)]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy⟩
      rw [← ψ.injective hyy]
      exact hy'
  set σ : alternatingGroup (Fin 7) := g⁻¹ * ψ x * g with hσ
  have hconj : ∀ n : ℤ, σ ^ n = g⁻¹ * ψ (x ^ n) * g := by
    intro n
    have h := conj_zpow (i := n) (a := g⁻¹) (b := ψ x)
    rw [inv_inv] at h
    rw [hσ, h, map_zpow]
  have hconjN : ∀ n : ℕ, σ ^ n = g⁻¹ * ψ (x ^ n) * g := by
    intro n
    have h := conj_pow (i := n) (a := g⁻¹) (b := ψ x)
    rw [inv_inv] at h
    rw [hσ, h, map_pow]
  have hσ9 : (σ : Perm (Fin 7)) ^ 9 = 1 := by
    obtain ⟨k, hk⟩ := hx3
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ 2520 := by
      rw [← card_alt7, ← Nat.card_congr ψ.toEquiv]
      exact orderOf_dvd_natCard x
    have h3 : orderOf x ∣ 9 := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
      rw [hj'] at h2 ⊢
      have : j ≤ 2 := by
        by_contra hj2
        have : 3 ^ 3 ∣ 2520 := (pow_dvd_pow 3 (by omega)).trans h2
        revert this
        decide
      exact pow_dvd_pow 3 this
    have h4 : x ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
    have h5 : σ ^ 9 = 1 := by
      rw [hconjN 9, h4, map_one, mul_one, inv_mul_cancel]
    exact congrArg Subtype.val h5
  have hσs : Perm.sign (σ : Perm (Fin 7)) = 1 := Equiv.Perm.mem_alternatingGroup.mp σ.2
  obtain ⟨hσ3, hinv⟩ := hc.2.2.2.2 _ hσs hσ9
  have hσ3' : σ ^ 3 = 1 := Subtype.ext hσ3
  have hx3' : x ^ 3 = 1 := by
    have := hconjN 3
    rw [hσ3'] at this
    apply ψ.injective
    rw [map_one]
    have h1 : ψ (x ^ 3) = g * (g⁻¹ * ψ (x ^ 3) * g) * g⁻¹ := by group
    rw [h1, ← this]
    group
  refine ⟨hx3', ?_⟩
  have hperm' : A7T3.permT0 (σ : Perm (Fin 7)) := by
    intro t ht
    let tA : alternatingGroup (Fin 7) :=
      ⟨t, Equiv.Perm.mem_alternatingGroup.mpr (hc.2.2.2.1 t ht)⟩
    have htT : ψ.symm (g * tA * g⁻¹) ∈ T := by
      rw [hmemT, MulEquiv.apply_symm_apply]
      show (g⁻¹ * (g * tA * g⁻¹) * g : alternatingGroup (Fin 7)) ∈ a7T0 hc
      rw [show g⁻¹ * (g * tA * g⁻¹) * g = tA by group]
      exact ht
    obtain ⟨y', hy', t', ht', he⟩ := hperm _ htT x (Subgroup.mem_zpowers x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have ht'0 := (hmemT t').mp ht'
    refine ⟨⟨(j % 3).toNat, by omega⟩, (g⁻¹ * ψ t' * g : alternatingGroup (Fin 7)), ht'0, ?_⟩
    have e1 : tA * σ = σ ^ j * (g⁻¹ * ψ t' * g) := by
      have h2 := congrArg (fun z => g⁻¹ * ψ z * g) he
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      rw [hconj j, hσ]
      calc tA * (g⁻¹ * ψ x * g) = g⁻¹ * (g * tA * g⁻¹ * ψ x) * g := by group
        _ = g⁻¹ * (ψ (x ^ j) * ψ t') * g := h2
        _ = g⁻¹ * ψ (x ^ j) * g * (g⁻¹ * ψ t' * g) := by group
    have e2 : σ ^ j = σ ^ ((j % 3).toNat : ℕ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      conv_lhs => rw [← Int.emod_add_mul_ediv j 3, zpow_add, zpow_mul]
      rw [show (σ ^ (3 : ℤ)) = 1 by rw [zpow_ofNat]; exact hσ3', one_zpow, mul_one]
    rw [e2] at e1
    exact congrArg Subtype.val e1
  obtain ⟨t₀, ht₀, hinv₀⟩ := hinv hperm'
  let tA : alternatingGroup (Fin 7) :=
    ⟨t₀, Equiv.Perm.mem_alternatingGroup.mpr (hc.2.2.2.1 t₀ ht₀)⟩
  refine ⟨ψ.symm (g * tA * g⁻¹), ?_, ?_⟩
  · rw [hmemT, MulEquiv.apply_symm_apply]
    show (g⁻¹ * (g * tA * g⁻¹) * g : alternatingGroup (Fin 7)) ∈ a7T0 hc
    rw [show g⁻¹ * (g * tA * g⁻¹) * g = tA by group]
    exact ht₀
  · have h1 : tA * σ * tA⁻¹ = σ⁻¹ := Subtype.ext hinv₀
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    have h2 : ψ x = g * σ * g⁻¹ := by rw [hσ]; group
    rw [h2]
    calc g * tA * g⁻¹ * (g * σ * g⁻¹) * (g * tA * g⁻¹)⁻¹ = g * (tA * σ * tA⁻¹) * g⁻¹ := by group
      _ = (g * σ * g⁻¹)⁻¹ := by rw [h1]; group

theorem oddInner_alt7 (α : MulAut (alternatingGroup (Fin 7))) (hα : Odd (orderOf α)) :
    ∃ x : alternatingGroup (Fin 7), α = MulAut.conj x := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  obtain ⟨σ, rfl⟩ := hb.2 α
  have hσo : Odd (orderOf σ) := by
    rwa [orderOf_injective _ hb.1 σ] at hα
  have hσ : σ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : Perm.sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hσo
      rw [h, hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
      exact absurd h1 (by decide)
  refine ⟨⟨σ, hσ⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  simp [MulAut.conjNormal_apply]

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_a7 (h : Star513 Q R S B D)
    (hQ : IsAlt 7 ↥Q ∨ IsHat ↥Q (alternatingGroup (Fin 7)))
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    (∀ d ∈ D, d ^ 3 ∈ Subgroup.centralizer (Q : Set A)) ∧
      ∃ t ∈ S ⊓ Q, ∀ d ∈ D, t * d * t⁻¹ * d ∈ Subgroup.centralizer (Q : Set A) := by
  have hc : A7T3.stmt := of_decide_eq_true Certificates.certificate7157
  obtain ⟨⟨ψ⟩, hperf⟩ : Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* alternatingGroup (Fin 7)) ∧
      Group.IsPerfect ↥Q := by
    rcases hQ with hA | ⟨hqs, -, ⟨e⟩⟩
    · obtain ⟨e⟩ : Nonempty (↥Q ≃* alternatingGroup (Fin 7)) := hA
      have hA7 : Group.IsPerfect (alternatingGroup (Fin 7)) :=
        Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
      have hZ : Subgroup.center ↥Q = ⊥ := by
        have h1 := Subgroup.map_center_eq e
        rw [alternatingGroup.center_eq_bot (by simp)] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
      exact ⟨⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩,
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
    · exact ⟨⟨e⟩, hqs.1⟩
  have hQperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hperf
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot ↥Q _ hperf
  have hinn : ∀ α : MulAut (↥Q ⧸ Subgroup.center ↥Q), Odd (orderOf α) →
      ∃ x, α = MulAut.conj x := by
    intro α hα
    obtain ⟨y, hy⟩ := oddInner_alt7 (MulAut.congr ψ α) (by rwa [MulEquiv.orderOf_eq])
    refine ⟨ψ.symm y, MulEquiv.ext fun z => ?_⟩
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) => ψ.symm (f (ψ z))) hy
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply, map_mul, map_inv] at h1
    rw [MulAut.conj_apply]
    exact h1
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨x, hx, k, hxk⟩ := iPart_eq_zpowers e hcen hinn h hD3
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hperm := perm_D e hinn h hcen
  rw [hx] at hperm
  obtain ⟨hx3, t, ht, htx⟩ := a7_conclusion hc ψ hT2 hTi ⟨k, hxk⟩ hperm
  obtain ⟨t₀, ht₀Q, ht₀S, rfl⟩ := (mem_pImg Q e).1 ht
  exact ⟨pow_three_mem_centralizer e hinn h hQperf hx hx3,
    t₀, ht₀S, conj_mul_mem_centralizer e hinn h hQperf hx ht₀Q htx⟩

end CFSG.Quasithin.H13.NQCat.T3
