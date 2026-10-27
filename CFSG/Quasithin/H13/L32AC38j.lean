module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.EmptyFaithful.S153EB6A

public section

namespace CFSG.Quasithin.H13.L32A.C

open Equiv

theorem exists_three_of_factorType {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    (h : G64.FactorType K) : ∃ e ∈ K, e ^ 3 = 1 ∧ e ≠ 1 := by
  have key : ∀ {M : Type} [Group M], (↥K ≃* M) → (∃ m : M, m ^ 3 = 1 ∧ m ≠ 1) →
      ∃ e ∈ K, e ^ 3 = 1 ∧ e ≠ 1 := by
    intro M _ φ ⟨m, hm3, hm1⟩
    refine ⟨((φ.symm m : ↥K) : MulAut W), (φ.symm m).2, ?_, ?_⟩
    · have h3 : (φ.symm m) ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
      have := congrArg Subtype.val h3
      simpa using this
    · intro h1
      apply hm1
      have : φ.symm m = 1 := Subtype.ext h1
      simpa using congrArg φ this
  have hsl : ∀ n : ℕ, (∃ s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), s ^ 3 = 1 ∧ s ≠ 1) →
      ∃ m : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)), m ^ 3 = 1 ∧ m ≠ 1 := by
    intro n ⟨s, hs3, hs1⟩
    refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2) s, ?_, ?_⟩
    · rw [← map_pow, hs3, map_one]
    · intro h1
      apply hs1
      simpa using
        congrArg (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).symm h1
  have h2 : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), s ^ 3 = 1 ∧ s ≠ 1 := by
    decide +kernel
  have h3 : ∃ s : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), s ^ 3 = 1 ∧ s ≠ 1 := by
    decide +kernel
  have h5 : ∃ s : Perm (Fin 5), s ^ 3 = 1 ∧ s ≠ 1 :=
    ⟨swap 0 1 * swap 1 2, by decide, by decide⟩
  rcases h with h | h | h
  · obtain ⟨φ⟩ := h
    exact key φ (hsl 2 h2)
  · obtain ⟨φ⟩ := h
    exact key φ (hsl 3 h3)
  · obtain ⟨φ⟩ := h
    exact key φ h5

theorem sl2_comm_ne : ∀ s r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), s ^ 2 = 1 → s ≠ 1 →
    r ^ 3 = 1 → s * r = r * s → r = 1 := by
  decide +kernel

@[expose] def ι5 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def c5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def e0123 : G6.PermMod 5 := Multiplicative.ofAdd ![1, 1, 1, 1, 0]

@[expose] def T05 : Subgroup (Perm (Fin 5)) := Subgroup.centralizer {ι5}

theorem mem_T05 {σ : Perm (Fin 5)} : σ ∈ T05 ↔ σ * ι5 = ι5 * σ :=
  Subgroup.mem_centralizer_singleton_iff

theorem c5_mem_T05 : c5 ∈ T05 := mem_T05.mpr (by decide)

theorem card_T05 : Nat.card ↥T05 = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun σ => mem_T05 (σ := σ))),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem T05_isPGroup : IsPGroup 2 ↥T05 :=
  IsPGroup.of_card (n := 3) (by rw [card_T05]; norm_num)

theorem T05_index : ¬ 2 ∣ T05.index := by
  have h := T05.card_mul_index
  rw [card_T05, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h15 : T05.index = 15 := by
    have : (8 : ℕ) * T05.index = 8 * 15 := by rw [h]; decide
    omega
  rw [h15]
  decide

theorem fix_c5 : ∀ m : G6.PermMod 5, G6.permAct 5 c5 m = m →
    (∑ i, Multiplicative.toAdd m i = 0) → m = 1 ∨ m = e0123 := by
  decide +kernel

theorem nodup_five : ∀ y : Perm (Fin 5), y ^ 3 = 1 → G6.permAct 5 y e0123 ≠ e0123 →
    [1, e0123, G6.permAct 5 y e0123, e0123 * G6.permAct 5 y e0123,
      G6.permAct 5 y (e0123 * G6.permAct 5 y e0123)].Nodup := by
  decide +kernel

theorem exists_two_triples {n : ℕ} (hn : 8 ≤ n) (x : Fin n → ZMod 2) :
    ∃ a b c d e f : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
      d ∉ ({a, b, c} : Finset (Fin n)) ∧ e ∉ ({a, b, c} : Finset (Fin n)) ∧
      f ∉ ({a, b, c} : Finset (Fin n)) ∧ x a = x b ∧ x a = x c ∧ x d = x e ∧ x d = x f := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, h1, h2⟩ :=
    S153EB6.exists_three_agree (K := ZMod 2) (by simp) n (by omega) x
  have hs : 5 ≤ ((Finset.univ : Finset (Fin n)) \ {a, b, c}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (Finset.univ : Finset (Fin n)) \ {a, b, c}) (t := (Finset.univ : Finset (ZMod 2)))
    (f := x) (n := 2) (fun _ _ => Finset.mem_univ _) (by simp; omega)
  obtain ⟨d, e, f, hd, he, hf, hde, hdf, hef⟩ := Finset.two_lt_card_iff.1 hy
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hd he hf
  exact ⟨a, b, c, d, e, f, hab, hac, hbc, hde, hdf, hef, hd.1, he.1, hf.1, h1, h2,
    hd.2.trans he.2.symm, hd.2.trans hf.2.symm⟩

theorem permAct_cyc3_fix {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (m : G6.PermMod n) (hmb : Multiplicative.toAdd m a = Multiplicative.toAdd m b)
    (hmc : Multiplicative.toAdd m a = Multiplicative.toAdd m c) :
    G6.permAct n (swap a b * swap b c) m = m := by
  obtain ⟨hia, hib, hic, hio⟩ := S153EB6.cyc3_inv hab hac hbc
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  by_cases h1 : i = a
  · subst h1; rw [hia]; exact hmc.symm
  by_cases h2 : i = b
  · subst h2; rw [hib]; exact hmb
  by_cases h3 : i = c
  · subst h3; rw [hic]; exact hmb.symm.trans hmc
  rw [hio i h1 h2 h3]

theorem cyc3_apply_of_ne {n : ℕ} {a b c x : Fin n} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    (swap a b * swap b c) x = x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc, swap_apply_of_ne_of_ne hxa hxb]

theorem cyc3_commute {n : ℕ} {a b c d e f : Fin n}
    (hd : d ∉ ({a, b, c} : Finset (Fin n))) (he : e ∉ ({a, b, c} : Finset (Fin n)))
    (hf : f ∉ ({a, b, c} : Finset (Fin n))) :
    Commute (swap a b * swap b c) (swap d e * swap e f) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd he hf
  refine Perm.Disjoint.commute fun x => ?_
  by_cases hxa : x = a
  · subst hxa
    exact Or.inr (cyc3_apply_of_ne (Ne.symm hd.1) (Ne.symm he.1) (Ne.symm hf.1))
  by_cases hxb : x = b
  · subst hxb
    exact Or.inr (cyc3_apply_of_ne (Ne.symm hd.2.1) (Ne.symm he.2.1) (Ne.symm hf.2.1))
  by_cases hxc : x = c
  · subst hxc
    exact Or.inr (cyc3_apply_of_ne (Ne.symm hd.2.2) (Ne.symm he.2.2) (Ne.symm hf.2.2))
  exact Or.inl (cyc3_apply_of_ne hxa hxb hxc)

theorem cyc3_pow_apply_eq {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {k : ZMod 3} (h : ((swap a b * swap b c) ^ k.val) a = a) : k = 0 := by
  have hlt : k.val < 3 := ZMod.val_lt k
  have h1 : (swap a b * swap b c) a = b := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]
  have h2 : (swap a b * swap b c) b = c := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hv : k.val = 0 := by
    interval_cases hk : k.val
    · rfl
    · exfalso
      rw [pow_one, h1] at h
      exact hab h.symm
    · exfalso
      rw [pow_two, Perm.mul_apply, h1, h2] at h
      exact hac h.symm
  exact (ZMod.val_eq_zero k).mp hv

theorem cyc3_indep {n : ℕ} {a b c d e f : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hd : d ∉ ({a, b, c} : Finset (Fin n))) (he : e ∉ ({a, b, c} : Finset (Fin n)))
    (hf : f ∉ ({a, b, c} : Finset (Fin n))) (i j : ZMod 3)
    (h : (swap a b * swap b c) ^ i.val * (swap d e * swap e f) ^ j.val = 1) : i = 0 ∧ j = 0 := by
  have hd' := hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd' he hf
  have hfixa : ∀ k : ℕ, ((swap d e * swap e f) ^ k) a = a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Perm.mul_apply, cyc3_apply_of_ne (Ne.symm hd'.1) (Ne.symm he.1)
        (Ne.symm hf.1), ih]
  have hfixd : ∀ k : ℕ, ((swap a b * swap b c) ^ k) d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Perm.mul_apply, cyc3_apply_of_ne hd'.1 hd'.2.1 hd'.2.2, ih]
  have ha := congrArg (fun σ : Perm (Fin n) => σ a) h
  simp only [Perm.mul_apply, hfixa, Perm.coe_one, id_eq] at ha
  have hi := cyc3_pow_apply_eq hab hac hbc ha
  refine ⟨hi, ?_⟩
  rw [hi, ZMod.val_zero, pow_zero, one_mul] at h
  have hd2 := congrArg (fun σ : Perm (Fin n) => σ d) h
  simp only [Perm.coe_one, id_eq] at hd2
  exact cyc3_pow_apply_eq hde hdf hef hd2

end CFSG.Quasithin.H13.L32A.C
