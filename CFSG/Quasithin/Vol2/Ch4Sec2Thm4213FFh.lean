module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.FFh

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {m : ℕ}

theorem permWeight_mul (σ τ : Equiv.Perm (Fin m)) (x : ↥(evenWeight m)) :
    permWeight m (σ * τ) x = permWeight m σ (permWeight m τ x) := by
  apply Subtype.ext
  funext i
  rfl

theorem permWeight_one (x : ↥(evenWeight m)) : permWeight m 1 x = x := by
  apply Subtype.ext
  funext i
  rfl

@[expose] def pwHom (m : ℕ) (σ : Equiv.Perm (Fin m)) : ↥(evenWeight m) →+ ↥(evenWeight m) where
  toFun := permWeight m σ
  map_zero' := by
    apply Subtype.ext
    funext i
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    funext i
    rfl

theorem constWeight_le_comap (σ : Equiv.Perm (Fin m)) :
    constWeight m ≤ (constWeight m).comap (pwHom m σ) := fun _ hx _ _ => hx _ _

@[expose] def hAct (m : ℕ) (σ : Equiv.Perm (Fin m)) : AltHeart m →+ AltHeart m :=
  QuotientAddGroup.map _ _ (pwHom m σ) (constWeight_le_comap σ)

theorem hAct_mk (σ : Equiv.Perm (Fin m)) (x : ↥(evenWeight m)) :
    hAct m σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (permWeight m σ x) := rfl

theorem hAct_mul (σ τ : Equiv.Perm (Fin m)) (u : AltHeart m) :
    hAct m (σ * τ) u = hAct m σ (hAct m τ u) := by
  induction u using QuotientAddGroup.induction_on with
  | H x => rw [hAct_mk, hAct_mk, hAct_mk, permWeight_mul]

theorem hAct_one (u : AltHeart m) : hAct m 1 u = u := by
  induction u using QuotientAddGroup.induction_on with
  | H x => rw [hAct_mk, permWeight_one]

@[expose] def heartAut (m : ℕ) : Equiv.Perm (Fin m) →* MulAut (Multiplicative (AltHeart m)) where
  toFun σ :=
    { toFun := fun u => Multiplicative.ofAdd (hAct m σ (Multiplicative.toAdd u))
      invFun := fun u => Multiplicative.ofAdd (hAct m σ⁻¹ (Multiplicative.toAdd u))
      left_inv := fun u => by
        show Multiplicative.ofAdd (hAct m σ⁻¹ (hAct m σ (Multiplicative.toAdd u))) = u
        rw [← hAct_mul, inv_mul_cancel, hAct_one]
        rfl
      right_inv := fun u => by
        show Multiplicative.ofAdd (hAct m σ (hAct m σ⁻¹ (Multiplicative.toAdd u))) = u
        rw [← hAct_mul, mul_inv_cancel, hAct_one]
        rfl
      map_mul' := fun u w => by
        show Multiplicative.ofAdd
          (hAct m σ (Multiplicative.toAdd u + Multiplicative.toAdd w)) = _
        rw [map_add]
        rfl }
  map_one' := by
    ext u
    show Multiplicative.ofAdd (hAct m 1 (Multiplicative.toAdd u)) = u
    rw [hAct_one]
    rfl
  map_mul' σ τ := by
    ext u
    show Multiplicative.ofAdd (hAct m (σ * τ) (Multiplicative.toAdd u)) = _
    rw [hAct_mul]
    rfl

theorem heartAut_apply (σ : Equiv.Perm (Fin m)) (u : Multiplicative (AltHeart m)) :
    heartAut m σ u = Multiplicative.ofAdd (hAct m σ (Multiplicative.toAdd u)) := rfl

theorem mem_constWeight_iff (i₀ : Fin m) {x : ↥(evenWeight m)} :
    x ∈ constWeight m ↔ ∀ i, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) i₀ :=
  ⟨fun h i => h i i₀, fun h i j => (h i).trans (h j).symm⟩

theorem mk_eq_mk_iff (i₀ : Fin m) {x y : ↥(evenWeight m)} :
    (QuotientAddGroup.mk x : AltHeart m) = QuotientAddGroup.mk y ↔
      ∀ i, (x : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) i =
        (x : Fin m → ZMod 2) i₀ + (y : Fin m → ZMod 2) i₀ := by
  rw [QuotientAddGroup.eq, mem_constWeight_iff i₀]
  have hval : ∀ i, ((-x + y : ↥(evenWeight m)) : Fin m → ZMod 2) i =
      (x : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) i := by
    intro i
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
    rw [ZMod.neg_eq_self_mod_two]
  simp only [hval]

theorem heartAut_mk_eq_iff (i₀ : Fin m) (σ : Equiv.Perm (Fin m)) (x : ↥(evenWeight m)) :
    heartAut m σ (Multiplicative.ofAdd (QuotientAddGroup.mk x)) =
        Multiplicative.ofAdd (QuotientAddGroup.mk x) ↔
      ∀ i, (x : Fin m → ZMod 2) (σ⁻¹ i) + (x : Fin m → ZMod 2) i =
        (x : Fin m → ZMod 2) (σ⁻¹ i₀) + (x : Fin m → ZMod 2) i₀ := by
  rw [heartAut_apply, toAdd_ofAdd, hAct_mk]
  exact (Multiplicative.ofAdd.injective.eq_iff).trans (mk_eq_mk_iff i₀)

theorem card_evenWeight (hm : 1 ≤ m) : Nat.card ↥(evenWeight m) * 2 = 2 ^ m := by
  have hs : Function.Surjective (AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i)
      (fun _ _ => Finset.sum_add_distrib)) := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    simp
  have h := AddSubgroup.card_mul_index (evenWeight m)
  rw [evenWeight, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top,
    Nat.card_zmod] at h
  rw [evenWeight, h, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin]

theorem card_constWeight (hm : 2 ≤ m) (he : Even m) : Nat.card ↥(constWeight m) = 2 := by
  have hones : (fun _ => (1 : ZMod 2)) ∈ evenWeight m := by
    show ∑ _i : Fin m, (1 : ZMod 2) = 0
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    obtain ⟨r, hr⟩ := he
    rw [hr, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let o : ↥(constWeight m) := ⟨⟨fun _ => 1, hones⟩, fun _ _ => rfl⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨0, o, fun h => ?_, ?_⟩
  · have := congrArg (fun y : ↥(constWeight m) => ((y : ↥(evenWeight m)) : Fin m → ZMod 2) i₀) h
    simp [o] at this
  · ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hy : ∀ i, ((y : ↥(evenWeight m)) : Fin m → ZMod 2) i =
        ((y : ↥(evenWeight m)) : Fin m → ZMod 2) i₀ := fun i => y.2 i i₀
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide)
        (((y : ↥(evenWeight m)) : Fin m → ZMod 2) i₀) with h0 | h1
    · left
      apply Subtype.ext
      apply Subtype.ext
      funext i
      show ((y : ↥(evenWeight m)) : Fin m → ZMod 2) i = (0 : ZMod 2)
      rw [hy i, h0]
    · right
      apply Subtype.ext
      apply Subtype.ext
      funext i
      show ((y : ↥(evenWeight m)) : Fin m → ZMod 2) i = (1 : ZMod 2)
      rw [hy i, h1]

theorem card_altHeart (hm : 2 ≤ m) (he : Even m) : Nat.card (AltHeart m) * 4 = 2 ^ m := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (constWeight m)
  rw [card_constWeight hm he] at h
  rw [← card_evenWeight (by omega), h]
  ring

theorem sum_pair6 :
    ∀ a b : Fin 6, ∑ i, ((Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2)) i = 0 := by
  decide +kernel

@[expose] def pairVec6 (a b : Fin 6) : ↥(evenWeight 6) :=
  ⟨(Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2), AddMonoidHom.mem_ker.mpr (sum_pair6 a b)⟩

theorem three_cycle_add6 : ∀ (x : Fin 6 → ZMod 2) (i j k : Fin 6), i ≠ j → j ≠ k → i ≠ k →
    x i = 1 → x k = 1 → x j = 0 → ∀ m : Fin 6,
    x m + x ((Equiv.swap i j * Equiv.swap j k)⁻¹ m) =
      ((Pi.single j 1 + Pi.single k 1 : Fin 6 → ZMod 2)) m := by
  decide +kernel

theorem exists_three6 : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → ¬ (∀ i j, x i = x j) →
    ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i = 1 ∧ x k = 1 ∧ x j = 0 := by
  decide +kernel

theorem decomp_pairs6 : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    x = ∑ i, (if i ≠ 0 ∧ x i = 1 then (Pi.single 0 1 + Pi.single i 1 : Fin 6 → ZMod 2) else 0) := by
  decide +kernel

theorem permWeight_pairVec6 (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    permWeight 6 σ (pairVec6 a b) = pairVec6 (σ a) (σ b) := by
  apply Subtype.ext
  funext m
  show (Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2) (σ⁻¹ m) =
    (Pi.single (σ a) 1 + Pi.single (σ b) 1 : Fin 6 → ZMod 2) m
  have h1 : (σ⁻¹ m = a) ↔ (m = σ a) := Equiv.Perm.inv_eq_iff_eq
  have h2 : (σ⁻¹ m = b) ↔ (m = σ b) := Equiv.Perm.inv_eq_iff_eq
  simp only [Pi.add_apply, Pi.single_apply, h1, h2]

theorem exists_alt6_pair {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : alternatingGroup (Fin 6), (σ : Equiv.Perm (Fin 6)) a = c ∧
      (σ : Equiv.Perm (Fin 6)) b = d := by
  have h6 := alternatingGroup.isMultiplyPretransitive (Fin 6)
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 6) - 2) (by simp) (by simp)
  let x : Fin 2 ↪ Fin 6 := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin 6 := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) x y
  refine ⟨g, ?_, ?_⟩
  · exact congrArg (fun z : Fin 2 ↪ Fin 6 => z 0) hg
  · exact congrArg (fun z : Fin 2 ↪ Fin 6 => z 1) hg

theorem heart6_eq_bot_or_top (X : AddSubgroup (AltHeart 6))
    (hX : ∀ σ : alternatingGroup (Fin 6), ∀ x : ↥(evenWeight 6),
      (QuotientAddGroup.mk x : AltHeart 6) ∈ X →
        (QuotientAddGroup.mk (permWeight 6 (σ : Equiv.Perm (Fin 6)) x) : AltHeart 6) ∈ X) :
    X = ⊥ ∨ X = ⊤ := by
  by_cases hb : X = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨y, hyX⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hb
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hy0' : (QuotientAddGroup.mk x : AltHeart 6) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hc : ¬ ∀ i j, (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) j := by
    intro hc
    apply hy0'
    rw [QuotientAddGroup.eq_zero_iff]
    exact hc
  obtain ⟨i, j, k, hij, hjk, hik, hi, hk, hj⟩ :=
    exists_three6 x (AddMonoidHom.mem_ker.mp x.2) hc
  let τ : alternatingGroup (Fin 6) := ⟨Equiv.swap i j * Equiv.swap j k, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
      Equiv.Perm.sign_swap hjk]
    decide⟩
  have hpair : (QuotientAddGroup.mk (pairVec6 j k) : AltHeart 6) ∈ X := by
    have h1 := X.add_mem hyX (hX τ x hyX)
    have h2 : x + permWeight 6 (τ : Equiv.Perm (Fin 6)) x = pairVec6 j k := by
      apply Subtype.ext
      funext m
      exact three_cycle_add6 x i j k hij hjk hik hi hk hj m
    rw [← QuotientAddGroup.mk_add, h2] at h1
    exact h1
  have hall : ∀ a b : Fin 6, a ≠ b → (QuotientAddGroup.mk (pairVec6 a b) : AltHeart 6) ∈ X := by
    intro a b hab
    obtain ⟨σ, hσa, hσb⟩ := exists_alt6_pair hjk hab
    have h1 := hX σ _ hpair
    rwa [permWeight_pairVec6, hσa, hσb] at h1
  rw [eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hw : w = ∑ i, (if i ≠ 0 ∧ (w : Fin 6 → ZMod 2) i = 1 then pairVec6 0 i else 0) := by
    apply Subtype.ext
    push_cast
    convert decomp_pairs6 w (AddMonoidHom.mem_ker.mp w.2) using 2 with i
    split_ifs <;> rfl
  set X' : AddSubgroup ↥(evenWeight 6) := X.comap (QuotientAddGroup.mk' (constWeight 6)) with hX'
  have hmem : ∀ v, v ∈ X' ↔ (QuotientAddGroup.mk v : AltHeart 6) ∈ X := fun v => Iff.rfl
  rw [← hmem, hw]
  refine _root_.sum_mem fun i _ => ?_
  split_ifs with h
  · exact (hmem _).mpr (hall 0 i (Ne.symm h.1))
  · exact X'.zero_mem

end CFSG.Quasithin.H13.Ch4.FFh
