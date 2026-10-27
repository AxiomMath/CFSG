module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitAltNatural
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Lem26A8

open CFSG.Quasithin CFSG.Quasithin.H13.Orbit Equiv

@[expose] def stabU (u : G6.PermMod 8) : Subgroup (alternatingGroup (Fin 8)) where
  carrier := {γ | G6.permAct 8 (γ : Perm (Fin 8)) u = u}
  one_mem' := by
    show G6.permAct 8 ((1 : alternatingGroup (Fin 8)) : Perm (Fin 8)) u = u
    rw [OneMemClass.coe_one, map_one]
    rfl
  mul_mem' := fun {a b} ha hb => by
    show G6.permAct 8 ((a * b : alternatingGroup (Fin 8)) : Perm (Fin 8)) u = u
    rw [MulMemClass.coe_mul, map_mul, MulAut.mul_apply]
    rw [show G6.permAct 8 (b : Perm (Fin 8)) u = u from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    show G6.permAct 8 ((a⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) u = u
    have ha' : G6.permAct 8 (a : Perm (Fin 8)) u = u := ha
    conv_lhs => rw [← ha']
    rw [InvMemClass.coe_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem mem_stabU {u : G6.PermMod 8} {γ : alternatingGroup (Fin 8)} :
    γ ∈ stabU u ↔ G6.permAct 8 (γ : Perm (Fin 8)) u = u := Iff.rfl

@[expose, reducible] noncomputable def act8 : MulAction (alternatingGroup (Fin 8)) (G6.PermMod 8) :=
  MulAction.compHom (G6.PermMod 8) ((G6.permAct 8).comp (alternatingGroup (Fin 8)).subtype)

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_wt {k : ℕ} (hk : k = 2 ∨ k = 6) :
    Nat.card {x : G6.PermMod 8 // wtP x = k} = 28 := by
  have e : {x : G6.PermMod 8 // wtP x = k} ≃ {x : ↥(G6.coreMod 8) // wtP (x : G6.PermMod 8) = k} :=
    { toFun := fun x => ⟨⟨x.1, (mem_coreMod_iff _).2 (by rw [x.2]; rcases hk with rfl | rfl <;>
        decide)⟩, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  refine (card_coreMod_wt (n := 8) (fun j => j = k)).trans ?_
  rcases hk with rfl | rfl <;> decide +kernel

theorem card_stabU {u : G6.PermMod 8} (hu : wtP u = 2 ∨ wtP u = 6) :
    Nat.card (stabU u) = 720 := by
  classical
  let _ : MulAction (alternatingGroup (Fin 8)) (G6.PermMod 8) := act8
  have horb : MulAction.orbit (alternatingGroup (Fin 8)) u = {x | wtP x = wtP u} := by
    ext x
    constructor
    · rintro ⟨γ, rfl⟩
      exact wtP_permAct _ u
    · intro hx
      obtain ⟨σ, hσ, he⟩ := exists_alt_permAct_eq (by norm_num : 3 ≤ 8) hx.symm
      exact ⟨⟨σ, hσ⟩, he⟩
  have hst : MulAction.stabilizer (alternatingGroup (Fin 8)) u = stabU u := by
    ext γ
    rfl
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (alternatingGroup (Fin 8)) u
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_alt_eight, hst] at h
  have h2 : Nat.card (MulAction.orbit (alternatingGroup (Fin 8)) u) = 28 := by
    rw [horb]
    exact card_wt hu
  rw [h2] at h
  omega

@[expose] def T8 : Fin 16 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 0, 2, 3, 4, 5, 7, 6],
    ![1, 0, 3, 4, 5, 2, 6, 7],
    ![0, 1, 3, 4, 5, 2, 7, 6],
    ![0, 1, 4, 5, 2, 3, 6, 7],
    ![1, 0, 4, 5, 2, 3, 7, 6],
    ![1, 0, 5, 2, 3, 4, 6, 7],
    ![0, 1, 5, 2, 3, 4, 7, 6],
    ![1, 0, 2, 5, 4, 3, 6, 7],
    ![0, 1, 2, 5, 4, 3, 7, 6],
    ![1, 0, 4, 3, 2, 5, 6, 7],
    ![0, 1, 4, 3, 2, 5, 7, 6],
    ![0, 1, 3, 2, 5, 4, 6, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![0, 1, 5, 4, 3, 2, 6, 7],
    ![1, 0, 5, 4, 3, 2, 7, 6]]

@[expose] def T8inv : Fin 16 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 0, 2, 3, 4, 5, 7, 6],
    ![1, 0, 5, 2, 3, 4, 6, 7],
    ![0, 1, 5, 2, 3, 4, 7, 6],
    ![0, 1, 4, 5, 2, 3, 6, 7],
    ![1, 0, 4, 5, 2, 3, 7, 6],
    ![1, 0, 3, 4, 5, 2, 6, 7],
    ![0, 1, 3, 4, 5, 2, 7, 6],
    ![1, 0, 2, 5, 4, 3, 6, 7],
    ![0, 1, 2, 5, 4, 3, 7, 6],
    ![1, 0, 4, 3, 2, 5, 6, 7],
    ![0, 1, 4, 3, 2, 5, 7, 6],
    ![0, 1, 3, 2, 5, 4, 6, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![0, 1, 5, 4, 3, 2, 6, 7],
    ![1, 0, 5, 4, 3, 2, 7, 6]]

@[expose] def M16 : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14],
    ![2, 3, 4, 5, 6, 7, 0, 1, 12, 13, 14, 15, 10, 11, 8, 9],
    ![3, 2, 5, 4, 7, 6, 1, 0, 13, 12, 15, 14, 11, 10, 9, 8],
    ![4, 5, 6, 7, 0, 1, 2, 3, 10, 11, 8, 9, 14, 15, 12, 13],
    ![5, 4, 7, 6, 1, 0, 3, 2, 11, 10, 9, 8, 15, 14, 13, 12],
    ![6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 8, 9, 10, 11],
    ![7, 6, 1, 0, 3, 2, 5, 4, 15, 14, 13, 12, 9, 8, 11, 10],
    ![8, 9, 14, 15, 10, 11, 12, 13, 0, 1, 4, 5, 6, 7, 2, 3],
    ![9, 8, 15, 14, 11, 10, 13, 12, 1, 0, 5, 4, 7, 6, 3, 2],
    ![10, 11, 12, 13, 8, 9, 14, 15, 4, 5, 0, 1, 2, 3, 6, 7],
    ![11, 10, 13, 12, 9, 8, 15, 14, 5, 4, 1, 0, 3, 2, 7, 6],
    ![12, 13, 8, 9, 14, 15, 10, 11, 2, 3, 6, 7, 0, 1, 4, 5],
    ![13, 12, 9, 8, 15, 14, 11, 10, 3, 2, 7, 6, 1, 0, 5, 4],
    ![14, 15, 10, 11, 12, 13, 8, 9, 6, 7, 2, 3, 4, 5, 0, 1],
    ![15, 14, 11, 10, 13, 12, 9, 8, 7, 6, 3, 2, 5, 4, 1, 0]]

theorem T8_left : ∀ k x, T8inv k (T8 k x) = x := by decide +kernel

theorem T8_right : ∀ k x, T8 k (T8inv k x) = x := by decide +kernel

theorem T8_mul : ∀ i j x, T8 i (T8 j x) = T8 (M16 i j) x := by decide +kernel

theorem T8_inj : ∀ i j, (∀ x, T8 i x = T8 j x) → i = j := by decide +kernel

@[expose] def tab (k : Fin 16) : Perm (Fin 8) := ⟨T8 k, T8inv k, T8_left k, T8_right k⟩

theorem tab_sign : ∀ k, Perm.sign (tab k) = 1 := by decide +kernel

theorem tab_inv_apply (k : Fin 16) (x : Fin 8) : (tab k)⁻¹ x = T8inv k x := rfl

theorem tab_mul (i j : Fin 16) : tab i * tab j = tab (M16 i j) :=
  Equiv.ext fun x => T8_mul i j x

theorem tab_injective : Function.Injective tab := fun i j h =>
  T8_inj i j fun x => congrArg (fun σ : Perm (Fin 8) => σ x) h

theorem tab_zero : tab 0 = 1 := Equiv.ext fun x => by revert x; decide

theorem exists_tab_inv (i : Fin 16) : ∃ j, (tab i)⁻¹ = tab j := by
  refine ⟨![0, 1, 6, 7, 4, 5, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15] i, Equiv.ext fun x => ?_⟩
  rw [tab_inv_apply]
  revert i x
  decide +kernel

@[expose] def S0 : Subgroup (alternatingGroup (Fin 8)) where
  carrier := {γ | ∃ k, (γ : Perm (Fin 8)) = tab k}
  one_mem' := ⟨0, tab_zero.symm⟩
  mul_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨M16 i j, by rw [MulMemClass.coe_mul, hi, hj, tab_mul]⟩
  inv_mem' := by
    rintro a ⟨i, hi⟩
    obtain ⟨j, hj⟩ := exists_tab_inv i
    exact ⟨j, by rw [InvMemClass.coe_inv, hi, hj]⟩

theorem tab_mem (k : Fin 16) : tab k ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.mpr (tab_sign k)

theorem card_S0 : Nat.card S0 = 16 := by
  let f : Fin 16 → S0 := fun k => ⟨⟨tab k, tab_mem k⟩, k, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => tab_injective ?_, ?_⟩
    · exact congrArg (fun x : S0 => ((x : alternatingGroup (Fin 8)) : Perm (Fin 8))) h
    · rintro ⟨γ, k, hk⟩
      exact ⟨k, Subtype.ext (Subtype.ext hk.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def u0 : G6.PermMod 8 := Multiplicative.ofAdd ![1, 1, 0, 0, 0, 0, 0, 0]

@[expose] def q0 : G6.PermMod 8 := Multiplicative.ofAdd ![0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def vec (a b c : ZMod 2) : G6.PermMod 8 := Multiplicative.ofAdd ![a, a, b, b, b, b, c, c]

theorem permAct_tab_apply (k : Fin 16) (w : G6.PermMod 8) (i : Fin 8) :
    Multiplicative.toAdd (G6.permAct 8 (tab k) w) i = Multiplicative.toAdd w (T8inv k i) := rfl

theorem tab_fix_u0 : ∀ k, G6.permAct 8 (tab k) u0 = u0 := by
  intro k
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_tab_apply]
  revert k i
  decide +kernel

theorem tab_fix_q0 : ∀ k, G6.permAct 8 (tab k) q0 = q0 := by
  intro k
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_tab_apply]
  revert k i
  decide +kernel

theorem S0_le_stabU : S0 ≤ stabU u0 := by
  rintro γ ⟨k, hk⟩
  rw [mem_stabU, hk]
  exact tab_fix_u0 k

theorem eq_vec_of_fix {w : G6.PermMod 8} (h2 : G6.permAct 8 (tab 2) w = w)
    (h1 : G6.permAct 8 (tab 1) w = w) :
    w = vec (Multiplicative.toAdd w 0) (Multiplicative.toAdd w 2) (Multiplicative.toAdd w 6) := by
  have e2 : ∀ i, Multiplicative.toAdd w (T8inv 2 i) = Multiplicative.toAdd w i := fun i => by
    rw [← permAct_tab_apply, h2]
  have e1 : ∀ i, Multiplicative.toAdd w (T8inv 1 i) = Multiplicative.toAdd w i := fun i => by
    rw [← permAct_tab_apply, h1]
  have a0 : Multiplicative.toAdd w 1 = Multiplicative.toAdd w 0 := e2 0
  have a2 : Multiplicative.toAdd w 5 = Multiplicative.toAdd w 2 := e2 2
  have a3 : Multiplicative.toAdd w 2 = Multiplicative.toAdd w 3 := e2 3
  have a4 : Multiplicative.toAdd w 3 = Multiplicative.toAdd w 4 := e2 4
  have b6 : Multiplicative.toAdd w 7 = Multiplicative.toAdd w 6 := e1 6
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · rfl
  · exact a0
  · rfl
  · exact a3.symm
  · exact a4.symm.trans a3.symm
  · exact a2
  · rfl
  · exact b6

theorem wtP_vec : ∀ a b c : ZMod 2,
    wtP (vec a b c) = 2 * (if a = 0 then 0 else 1) + 4 * (if b = 0 then 0 else 1) +
      2 * (if c = 0 then 0 else 1) := by
  decide +kernel

theorem vec_mem_closure (a b c : ZMod 2) :
    vec a b c ∈ Subgroup.closure {u0, q0, G6.allOnes 8} := by
  have hu : u0 ∈ Subgroup.closure ({u0, q0, G6.allOnes 8} : Set (G6.PermMod 8)) :=
    Subgroup.subset_closure (by simp)
  have hq : q0 ∈ Subgroup.closure ({u0, q0, G6.allOnes 8} : Set (G6.PermMod 8)) :=
    Subgroup.subset_closure (by simp)
  have h1 : G6.allOnes 8 ∈ Subgroup.closure ({u0, q0, G6.allOnes 8} : Set (G6.PermMod 8)) :=
    Subgroup.subset_closure (by simp)
  have key : ∀ a b c : ZMod 2, vec a b c =
      u0 ^ (a + b).val * q0 ^ (c + b).val * G6.allOnes 8 ^ b.val := by
    decide +kernel
  rw [key]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _)
    (Subgroup.pow_mem _ hq _)) (Subgroup.pow_mem _ h1 _)

theorem vec_wt_two :
    ∀ a b c : ZMod 2, wtP (vec a b c) = 2 → vec a b c = u0 ∨ vec a b c = q0 := by
  decide +kernel

theorem wtP_u0 : wtP u0 = 2 := by decide +kernel

theorem wtP_q0 : wtP q0 = 2 := by decide +kernel

theorem q0_ne_u0 : q0 ≠ u0 := by decide +kernel

theorem permAct_allOnes (σ : Perm (Fin 8)) : G6.permAct 8 σ (G6.allOnes 8) = G6.allOnes 8 :=
  rfl

theorem exists_conj_S0 {S : Subgroup (alternatingGroup (Fin 8))} (hS : S ≤ stabU u0)
    (hc : Nat.card S = 16) : ∃ n ∈ stabU u0, ∀ s, s ∈ S ↔ n * s * n⁻¹ ∈ S0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := stabU u0 with hK
  have hK720 : Nat.card K = 720 := card_stabU (Or.inl wtP_u0)
  have hsyl : ∀ H : Subgroup (alternatingGroup (Fin 8)), H ≤ K → Nat.card H = 16 →
      ∃ P : Sylow 2 K, (P : Subgroup K) = H.subgroupOf K := by
    intro H hHK hH
    have hc' : Nat.card (H.subgroupOf K) = 16 := by
      rw [← hH]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
    have hp : IsPGroup 2 (H.subgroupOf K) := IsPGroup.of_card (n := 4) (by rw [hc']; norm_num)
    have hi : (H.subgroupOf K).index = 45 := by
      have := Subgroup.card_mul_index (H.subgroupOf K)
      rw [hc', hK720] at this
      omega
    exact ⟨hp.toSylow (by rw [hi]; decide), IsPGroup.toSylow_coe _ _⟩
  obtain ⟨P, hP⟩ := hsyl S hS hc
  obtain ⟨P₀, hP₀⟩ := hsyl S0 S0_le_stabU card_S0
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K P P₀
  refine ⟨n, n.2, fun s => ?_⟩
  by_cases hsK : s ∈ K
  · have key : (n * ⟨s, hsK⟩ * n⁻¹ : K) ∈ (P₀ : Subgroup K) ↔
        (⟨s, hsK⟩ : K) ∈ (P : Subgroup K) := by
      rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [hP₀, hP, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
    simpa using key.symm
  · have h1 : s ∉ S := fun h => hsK (hS h)
    have h2 : n * s * n⁻¹ ∉ S0 := by
      intro h
      apply hsK
      have h3 : n⁻¹ * (n * s * n⁻¹) * n ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem n.2) (S0_le_stabU h)) n.2
      simpa [mul_assoc] using h3
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem pa_mul (a b : alternatingGroup (Fin 8)) (w : G6.PermMod 8) :
    G6.permAct 8 ((a * b : alternatingGroup (Fin 8)) : Perm (Fin 8)) w =
      G6.permAct 8 (a : Perm (Fin 8)) (G6.permAct 8 (b : Perm (Fin 8)) w) := by
  rw [MulMemClass.coe_mul, map_mul, MulAut.mul_apply]

theorem pa_one (w : G6.PermMod 8) :
    G6.permAct 8 ((1 : alternatingGroup (Fin 8)) : Perm (Fin 8)) w = w := by
  rw [OneMemClass.coe_one, map_one, MulAut.one_apply]

theorem pa_inv_pa (a : alternatingGroup (Fin 8)) (w : G6.PermMod 8) :
    G6.permAct 8 ((a⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8))
      (G6.permAct 8 (a : Perm (Fin 8)) w) = w := by
  rw [← pa_mul, inv_mul_cancel, pa_one]

theorem pa_pa_inv (a : alternatingGroup (Fin 8)) (w : G6.PermMod 8) :
    G6.permAct 8 (a : Perm (Fin 8))
      (G6.permAct 8 ((a⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w) = w := by
  rw [← pa_mul, mul_inv_cancel, pa_one]

theorem fixed_of_card_two {u : G6.PermMod 8} (hu : wtP u = 2)
    {S : Subgroup (alternatingGroup (Fin 8))} (hSu : S ≤ stabU u) (hS : Nat.card S = 16) :
    (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) → Even (wtP w)) ∧
    ∃ q, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) q = q) ∧ wtP q = 2 ∧ q ≠ u ∧
      (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) →
        w ∈ Subgroup.closure {u, q, G6.allOnes 8}) ∧
      (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) → wtP w = 2 → w = u ∨ w = q) := by
  obtain ⟨σ, hσ, hσu⟩ := exists_alt_permAct_eq (by norm_num : 3 ≤ 8) (wtP_u0.trans hu.symm)
  set σ₁ : alternatingGroup (Fin 8) := ⟨σ, hσ⟩ with hσ₁
  have hσ₁u : G6.permAct 8 (σ₁ : Perm (Fin 8)) u0 = u := hσu
  set S' := S.map (MulAut.conj σ₁⁻¹).toMonoidHom with hS'
  have hmemS' : ∀ x, x ∈ S' ↔ σ₁ * x * σ₁⁻¹ ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hS'u : S' ≤ stabU u0 := by
    intro x hx
    have h1 : G6.permAct 8 ((σ₁ * x * σ₁⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) u = u :=
      hSu ((hmemS' x).mp hx)
    rw [mem_stabU]
    have e : x = σ₁⁻¹ * (σ₁ * x * σ₁⁻¹) * σ₁ := by group
    rw [e, pa_mul, pa_mul, hσ₁u, h1, ← hσ₁u, pa_inv_pa]
  have hS'c : Nat.card S' = 16 := by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj σ₁⁻¹).injective, hS]
  obtain ⟨n, hn, hnS⟩ := exists_conj_S0 hS'u hS'c
  set τ : alternatingGroup (Fin 8) := σ₁ * n⁻¹ with hτ
  have hS0 : ∀ s ∈ S, τ⁻¹ * s * τ ∈ S0 := by
    intro s hs
    have h1 : σ₁⁻¹ * s * σ₁ ∈ S' := (hmemS' _).mpr (by simpa [mul_assoc] using hs)
    have h2 := (hnS _).mp h1
    have e : τ⁻¹ * s * τ = n * (σ₁⁻¹ * s * σ₁) * n⁻¹ := by rw [hτ]; group
    rw [e]
    exact h2
  have hS0' : ∀ s ∈ S0, τ * s * τ⁻¹ ∈ S := by
    intro s hs
    have h1 : n⁻¹ * s * n ∈ S' := (hnS _).mpr (by simpa [mul_assoc] using hs)
    have h2 := (hmemS' _).mp h1
    have e : τ * s * τ⁻¹ = σ₁ * (n⁻¹ * s * n) * σ₁⁻¹ := by rw [hτ]; group
    rw [e]
    exact h2
  have hτu : G6.permAct 8 (τ : Perm (Fin 8)) u0 = u := by
    have hn' : G6.permAct 8 ((n⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) u0 = u0 :=
      (stabU u0).inv_mem hn
    rw [hτ, pa_mul, hn', hσ₁u]
  have hfix0 : ∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) →
      w = G6.permAct 8 (τ : Perm (Fin 8)) (vec
        (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w) 0)
        (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w) 2)
        (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w)
          6)) := by
    intro w hw
    have hfix : ∀ k, G6.permAct 8 (tab k)
        (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w) =
        G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) w := by
      intro k
      have hk := hw _ (hS0' ⟨tab k, tab_mem k⟩ ⟨k, rfl⟩)
      have e : (⟨tab k, tab_mem k⟩ : alternatingGroup (Fin 8)) =
          τ⁻¹ * (τ * ⟨tab k, tab_mem k⟩ * τ⁻¹) * τ := by group
      have e2 : G6.permAct 8 (tab k) = G6.permAct 8
          (((⟨tab k, tab_mem k⟩ : alternatingGroup (Fin 8))) : Perm (Fin 8)) := rfl
      rw [e2, e, pa_mul, pa_mul, pa_pa_inv, hk]
    rw [← eq_vec_of_fix (hfix 2) (hfix 1), pa_pa_inv]
  refine ⟨fun w hw => ?_, G6.permAct 8 (τ : Perm (Fin 8)) q0, fun s hs => ?_, ?_, ?_,
    fun w hw => ?_, fun w hw hw2 => ?_⟩
  · rw [hfix0 w hw, wtP_permAct, wtP_vec]
    split_ifs <;> decide
  · have e : s = τ * (τ⁻¹ * s * τ) * τ⁻¹ := by group
    obtain ⟨k, hk⟩ := hS0 s hs
    rw [e, pa_mul, pa_mul, pa_inv_pa, hk, tab_fix_q0]
  · rw [wtP_permAct, wtP_q0]
  · intro h
    apply q0_ne_u0
    have h1 := congrArg (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8))) h
    rwa [pa_inv_pa, ← hτu, pa_inv_pa] at h1
  · rw [hfix0 w hw]
    have hmap := Subgroup.mem_map_of_mem (G6.permAct 8 (τ : Perm (Fin 8))).toMonoidHom
      (vec_mem_closure (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) :
        Perm (Fin 8)) w) 0) (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) :
        Perm (Fin 8)) w) 2) (Multiplicative.toAdd (G6.permAct 8 ((τ⁻¹ : alternatingGroup (Fin 8)) :
        Perm (Fin 8)) w) 6))
    rw [MonoidHom.map_closure] at hmap
    have himg : ((G6.permAct 8 (τ : Perm (Fin 8))).toMonoidHom '' {u0, q0, G6.allOnes 8} :
        Set (G6.PermMod 8)) = {u, G6.permAct 8 (τ : Perm (Fin 8)) q0, G6.allOnes 8} := by
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hτu, permAct_allOnes]
    rw [himg] at hmap
    exact hmap
  · have h1 := hfix0 w hw
    have h2 := hw2
    rw [h1, wtP_permAct] at h2
    rcases vec_wt_two _ _ _ h2 with h3 | h3
    · left
      rw [h1, h3, hτu]
    · right
      rw [h1, h3]

theorem fixed_of_card {u : G6.PermMod 8} (hu : wtP u = 2 ∨ wtP u = 6)
    {S : Subgroup (alternatingGroup (Fin 8))} (hSu : S ≤ stabU u) (hS : Nat.card S = 16) :
    (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) → Even (wtP w)) ∧
    ∃ q, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) q = q) ∧ wtP q = wtP u ∧ q ≠ u ∧
      (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) →
        w ∈ Subgroup.closure {u, q, G6.allOnes 8}) ∧
      (∀ w, (∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) w = w) → wtP w = wtP u →
        w = u ∨ w = q) := by
  rcases hu with hu | hu
  · obtain ⟨h1, q, hq, hq2, hqu, hcl, hwt⟩ := fixed_of_card_two hu hSu hS
    exact ⟨h1, q, hq, hq2.trans hu.symm, hqu, hcl, fun w hw h => hwt w hw (h.trans hu)⟩
  ·
    set u' := u * G6.allOnes 8 with hu'
    have hwt' : wtP u' = 2 := by rw [hu', wtP_mul_allOnes, hu]
    have hSu' : S ≤ stabU u' := by
      intro s hs
      rw [mem_stabU, hu', map_mul, permAct_allOnes, hSu hs]
    obtain ⟨h1, q, hq, hq2, hqu, hcl, hwt⟩ := fixed_of_card_two hwt' hSu' hS
    have hfix1 : ∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) (q * G6.allOnes 8) = q * G6.allOnes 8 :=
      fun s hs => by rw [map_mul, permAct_allOnes, hq s hs]
    have hcanc : ∀ x : G6.PermMod 8, x * G6.allOnes 8 * G6.allOnes 8 = x := fun x => by
      rw [mul_assoc, allOnes_mul_self, mul_one]
    refine ⟨h1, q * G6.allOnes 8, hfix1, by rw [wtP_mul_allOnes, hq2, hu], ?_, ?_, ?_⟩
    · intro h
      apply hqu
      rw [hu', ← h, hcanc]
    · intro w hw
      have h2 := hcl w hw
      have hle : Subgroup.closure ({u', q, G6.allOnes 8} : Set (G6.PermMod 8)) ≤
          Subgroup.closure {u, q * G6.allOnes 8, G6.allOnes 8} := by
        rw [Subgroup.closure_le]
        have hu1 : u ∈ Subgroup.closure ({u, q * G6.allOnes 8, G6.allOnes 8} :
            Set (G6.PermMod 8)) := Subgroup.subset_closure (by simp)
        have hq1 : q * G6.allOnes 8 ∈ Subgroup.closure ({u, q * G6.allOnes 8, G6.allOnes 8} :
            Set (G6.PermMod 8)) := Subgroup.subset_closure (by simp)
        have h11 : G6.allOnes 8 ∈ Subgroup.closure ({u, q * G6.allOnes 8, G6.allOnes 8} :
            Set (G6.PermMod 8)) := Subgroup.subset_closure (by simp)
        intro x hx
        rcases hx with h | h | h
        · rw [h]
          exact Subgroup.mul_mem _ hu1 h11
        · rw [h]
          have h3 := Subgroup.mul_mem _ hq1 h11
          rwa [hcanc] at h3
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          exact h11
      exact hle h2
    · intro w hw hw6
      have hw1 : ∀ s ∈ S, G6.permAct 8 (s : Perm (Fin 8)) (w * G6.allOnes 8) = w * G6.allOnes 8 :=
        fun s hs => by rw [map_mul, permAct_allOnes, hw s hs]
      rcases hwt (w * G6.allOnes 8) hw1 (by rw [wtP_mul_allOnes, hw6, hu]) with h | h
      · left
        rw [← hcanc w, h, hu', hcanc]
      · right
        rw [← hcanc w, h]

end CFSG.Quasithin.H13.Lem26A8
