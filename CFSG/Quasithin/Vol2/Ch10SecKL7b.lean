module

public import CFSG.Quasithin.Vol2.Ch10SecKL7a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix Pointwise

@[expose] def tU : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 1; 0, 0, 1]

theorem det_tU : tU.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem tU_sq_ne_one : tU * tU ≠ 1 := by decide

theorem tU_pow_four : tU * tU * (tU * tU) = 1 := by decide

theorem exists_card_of_isPGroup (H : Subgroup SL32) (hH : IsPGroup 2 H) :
    ∃ j ≤ 3, Nat.card H = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hH
  have hdvd : 2 ^ j ∣ 168 := hj ▸ card_SL32 ▸ Subgroup.card_subgroup_dvd_card H
  refine ⟨j, ?_, hj⟩
  by_contra h
  have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega : 4 ≤ j)).trans hdvd
  norm_num at this

theorem card_le_four_of_sq_eq_one (E : Subgroup SL32) (hE : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun a => ⟨1, Subtype.ext (by simpa using hE a a.2)⟩
  obtain ⟨k, hk3, hk⟩ := exists_card_of_isPGroup E hp
  rcases (show k ≤ 2 ∨ k = 3 by omega) with h2 | rfl
  · rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  · exfalso
    obtain ⟨P, hEP⟩ := hp.exists_le_sylow
    obtain ⟨j, hj3, hj⟩ := exists_card_of_isPGroup (P : Subgroup SL32) P.isPGroup'
    have hEq : E = (P : Subgroup SL32) := by
      refine Subgroup.eq_of_le_of_card_ge hEP ?_
      rw [hj, hk]
      exact Nat.pow_le_pow_right (by norm_num) hj3
    set u : SL32 := mkSL tU det_tU with hu_def
    have hu2 : ¬ u ^ 2 ^ 1 = 1 := fun h => tU_sq_ne_one (by
      have := congrArg mat h
      rwa [pow_one, pow_two, mat_mul, mat_one, hu_def, mat_mkSL] at this)
    have hu4 : u ^ 2 ^ (1 + 1) = 1 := by
      apply ext_mat
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two, mat_mul, mat_mul,
        hu_def, mat_mkSL, mat_one, tU_pow_four]
    have hord : orderOf u = 2 ^ (1 + 1) := orderOf_eq_prime_pow hu2 hu4
    have hup : IsPGroup 2 (Subgroup.zpowers u) := IsPGroup.of_card (n := 1 + 1)
      (by rw [Nat.card_zpowers, hord])
    obtain ⟨Q, hQ⟩ := hup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL32 Q P
    have hmem : MulAut.conj g • u ∈ (P : Subgroup SL32) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers u))
    have hsq := hE _ (hEq ▸ hmem)
    rw [MulAut.smul_def, ← map_pow, MulEquiv.map_eq_one_iff] at hsq
    exact hu2 (by rwa [pow_one])

theorem card_M3 : Nat.card M3 = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

@[expose] def actN (n : ℕ) (γ : SL32) : (Fin n → M3) →* (Fin n → M3) :=
  MonoidHom.compLeft (act γ) (Fin n)

theorem actN_apply (n : ℕ) (γ : SL32) (v : Fin n → M3) (i : Fin n) :
    actN n γ v i = act γ (v i) := rfl

theorem card_invariant : ∀ (n : ℕ) (V : Subgroup (Fin n → M3)),
    (∀ γ : SL32, ∀ v ∈ V, actN n γ v ∈ V) → ∃ k, Nat.card V = 8 ^ k
  | 0, V, _ => ⟨0, by simp⟩
  | n + 1, V, hV => by
      let f : ↥V →* M3 := (Pi.evalMonoidHom (fun _ : Fin (n + 1) => M3) 0).comp V.subtype
      let tl : (Fin (n + 1) → M3) →* (Fin n → M3) :=
        MonoidHom.pi fun i => Pi.evalMonoidHom (fun _ : Fin (n + 1) => M3) i.succ
      let t : ↥f.ker →* (Fin n → M3) := tl.comp (V.subtype.comp f.ker.subtype)
      have ht : Function.Injective t := by
        intro x y hxy
        have hx0 : ((x : ↥V) : Fin (n + 1) → M3) 0 = 1 := x.2
        have hy0 : ((y : ↥V) : Fin (n + 1) → M3) 0 = 1 := y.2
        apply Subtype.ext
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [hx0, hy0]
        · exact congrFun hxy i
      obtain ⟨k, hk⟩ := card_invariant n t.range (by
        rintro γ _ ⟨x, rfl⟩
        have hx : actN (n + 1) γ (x : ↥V) ∈ V := hV γ _ (x : ↥V).2
        have hx0 : f ⟨_, hx⟩ = 1 := by
          show act γ (((x : ↥V) : Fin (n + 1) → M3) 0) = 1
          rw [show ((x : ↥V) : Fin (n + 1) → M3) 0 = 1 from x.2, map_one]
        exact ⟨⟨⟨_, hx⟩, hx0⟩, rfl⟩)
      have hcard := Subgroup.card_mul_index f.ker
      rw [Subgroup.index_ker, Nat.card_congr (MonoidHom.ofInjective ht).toEquiv, hk] at hcard
      rcases invariant_eq_bot_or_top f.range (by
          rintro γ _ ⟨x, rfl⟩
          exact ⟨⟨_, hV γ _ x.2⟩, rfl⟩) with h | h
      · refine ⟨k, ?_⟩
        rw [← hcard, h, Subgroup.card_bot, mul_one]
      · refine ⟨k + 1, ?_⟩
        rw [← hcard, h, Subgroup.card_top, card_M3, pow_succ]

theorem card_fixM (γ : SL32) :
    Nat.card (fixM γ) = Fintype.card {v : Fin 3 → ZMod 2 // mat γ *ᵥ v = v} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (x : M3), ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  · exact congrArg Multiplicative.toAdd (mem_fixM.1 x.2)
  · exact mem_fixM.2 (by rw [act_apply, toAdd_ofAdd, v.2])

@[expose] noncomputable def cdM (γ : SL32) : ℕ := padicValNat 2 (fixM γ).index

theorem index_fixM (γ : SL32) : (fixM γ).index = 2 ^ cdM γ := by
  have hd : (fixM γ).index ∣ 2 ^ 3 := by
    have := Subgroup.index_dvd_card (fixM γ)
    rwa [card_M3] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [cdM, hm, padicValNat.prime_pow]

theorem card_fixM_mul (γ : SL32) : Nat.card (fixM γ) * 2 ^ cdM γ = 8 := by
  rw [← index_fixM, Subgroup.card_mul_index, card_M3]

theorem eq_one_of_cdM_eq_zero (γ : SL32) (h : cdM γ = 0) : γ = 1 := by
  have h1 : (fixM γ).index = 1 := by rw [index_fixM, h, pow_zero]
  exact eq_one_of_fixM_eq_top γ (Subgroup.index_eq_one.1 h1)

theorem sq_eq_one_of_cdM_eq_one (γ : SL32) (h : cdM γ = 1) : γ ^ 2 = 1 :=
  sq_eq_one_of_index_two γ (by rw [index_fixM, h, pow_one])

theorem cdM_one : cdM 1 = 0 := by
  have h := card_fixM_mul 1
  have h1 : fixM 1 = ⊤ := eq_top_iff.2 fun x _ => mem_fixM.2 (act_one' x)
  rw [h1, Subgroup.card_top, card_M3] at h
  have : 2 ^ cdM 1 = 2 ^ 0 := by omega
  exact Nat.pow_right_injective le_rfl this

@[expose] def tA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

theorem det_tA : tA.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem tA_sq : tA * tA = 1 := by decide

theorem tQ_sq : tQ * tQ = 1 := by decide

theorem tA_tQ_comm : tA * tQ = tQ * tA := by decide

theorem tA_ne_one : tA ≠ 1 := by decide

theorem tQ_ne_one : tQ ≠ 1 := by decide

theorem tA_ne_tQ : tA ≠ tQ := by decide

theorem tAQ_ne_one : tA * tQ ≠ 1 := by decide

theorem fix_tA : ∀ v : Fin 3 → ZMod 2, tA *ᵥ v = v ↔ v 2 = 0 := by decide

theorem fix_tQ : ∀ v : Fin 3 → ZMod 2, tQ *ᵥ v = v ↔ v 2 = 0 := by decide

theorem fix_tAQ : ∀ v : Fin 3 → ZMod 2, (tA * tQ) *ᵥ v = v ↔ v 2 = 0 := by decide

theorem card_fix_tA : Fintype.card {v : Fin 3 → ZMod 2 // tA *ᵥ v = v} = 4 := by decide

@[expose] noncomputable def gA : SL32 := mkSL tA det_tA

@[expose] noncomputable def gQ : SL32 := mkSL tQ det_tQ

theorem fixM_eq_of_mat {γ δ : SL32} (h : ∀ v, mat γ *ᵥ v = v ↔ mat δ *ᵥ v = v) :
    fixM γ = fixM δ := by
  ext x
  simp only [mem_fixM, act_apply]
  constructor
  · intro hx
    rw [← ofAdd_toAdd x] at hx ⊢
    rw [toAdd_ofAdd] at hx ⊢
    exact congrArg Multiplicative.ofAdd ((h _).1 (Multiplicative.ofAdd.injective hx))
  · intro hx
    rw [← ofAdd_toAdd x] at hx ⊢
    rw [toAdd_ofAdd] at hx ⊢
    exact congrArg Multiplicative.ofAdd ((h _).2 (Multiplicative.ofAdd.injective hx))

theorem fixM_gQ : fixM gQ = fixM gA :=
  fixM_eq_of_mat fun v => (fix_tQ v).trans (fix_tA v).symm

theorem fixM_gAQ : fixM (gA * gQ) = fixM gA :=
  fixM_eq_of_mat fun v => by
    rw [mat_mul]
    exact (fix_tAQ v).trans (fix_tA v).symm

theorem cdM_gA : cdM gA = 1 := by
  have h := card_fixM_mul gA
  rw [card_fixM, show mat gA = tA from rfl, card_fix_tA] at h
  have : 2 ^ cdM gA = 2 ^ 1 := by omega
  exact Nat.pow_right_injective le_rfl this

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
