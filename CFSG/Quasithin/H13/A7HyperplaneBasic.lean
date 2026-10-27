module

public import CFSG.Quasithin.SteinbergCBEvenWeightGeometry
public import CFSG.Quasithin.SteinbergCBConstantWeight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Module Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB

variable {G : Type*} [Group G]

theorem fun_add_self_eq_zero (e : Fin 7 → ZMod 2) : e + e = 0 :=
  funext fun i => zmod_two_add_self (e i)

theorem zmodTwo_eq_zero_or_one : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by
  decide

theorem finrank_evenWeight_seven : finrank (ZMod 2) (evenWeight 7) = 6 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (sumForm 7)
  have h2 : LinearMap.range (sumForm 7) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    change ∑ i, Pi.single (0 : Fin 7) c i = c
    rw [Finset.sum_pi_single']
    simp
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  change finrank (ZMod 2) (LinearMap.ker (sumForm 7)) = 6
  omega

theorem nat_card_evenWeight_seven : Nat.card (evenWeight 7) = 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_evenWeight_seven]
  norm_num

theorem single_add_single_apply_eq_one {i j m : Fin 7} (hij : i ≠ j) :
    (Pi.single i 1 + Pi.single j 1 : Fin 7 → ZMod 2) m = 1 ↔ m = i ∨ m = j := by
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hi : m = i
  · subst hi
    simp [hij]
  · by_cases hj : m = j
    · subst hj
      simp [hi]
    · simp [hi, hj]

theorem eq_one_of_permAct7_fix {σ : Perm (Fin 7)}
    (h : ∀ x ∈ evenWeight 7, permAct7 σ x = x) : σ = 1 := by
  have key : ∀ i : Fin 7, σ⁻¹ i = i := by
    intro i
    have hne : ∀ k : Fin 7, k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 1 ≠ k + 2 := by decide
    obtain ⟨h1, h2, h12⟩ := hne i
    have hmem : ∀ j : Fin 7, j ≠ i → σ⁻¹ i = i ∨ σ⁻¹ i = j := by
      intro j hj
      have hx := h _ (pair_mem_evenWeight i j)
      have := congrFun hx i
      rw [permAct7_apply] at this
      have hii : (Pi.single i 1 + Pi.single j 1 : Fin 7 → ZMod 2) i = 1 :=
        (single_add_single_apply_eq_one hj.symm).2 (Or.inl rfl)
      rw [hii] at this
      exact (single_add_single_apply_eq_one hj.symm).1 this
    rcases hmem (i + 1) h1 with e | e
    · exact e
    · rcases hmem (i + 2) h2 with e' | e'
      · exact e'
      · exact absurd (e.symm.trans e') h12
  have : σ⁻¹ = 1 := Perm.ext key
  rw [← inv_inv σ, this, inv_one]

@[expose] def vec {P : Subgroup G} (ψ : P ≃* Multiplicative (evenWeight 7)) (x : P) :
    Fin 7 → ZMod 2 :=
  ((Multiplicative.toAdd (ψ x) : evenWeight 7) : Fin 7 → ZMod 2)

section Coord

variable {P : Subgroup G} (ψ : P ≃* Multiplicative (evenWeight 7))

theorem vec_mul (x y : P) : vec ψ (x * y) = vec ψ x + vec ψ y := by
  simp [vec, map_mul, toAdd_mul]

theorem vec_one : vec ψ 1 = 0 := by
  simp [vec]

theorem vec_inv (x : P) : vec ψ x⁻¹ = vec ψ x := by
  have h := vec_mul ψ x⁻¹ x
  rw [inv_mul_cancel, vec_one] at h
  have h2 := fun_add_self_eq_zero (vec ψ x)
  calc vec ψ x⁻¹ = vec ψ x⁻¹ + (vec ψ x + vec ψ x) := by rw [h2, add_zero]
    _ = (vec ψ x⁻¹ + vec ψ x) + vec ψ x := by abel
    _ = vec ψ x := by rw [← h, zero_add]

theorem vec_mem (x : P) : vec ψ x ∈ evenWeight 7 :=
  (Multiplicative.toAdd (ψ x)).2

theorem vec_injective : Function.Injective (vec ψ) := by
  intro x y h
  apply ψ.injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h

theorem vec_eq_zero_iff (x : P) : vec ψ x = 0 ↔ x = 1 := by
  rw [← vec_one ψ]
  exact (vec_injective ψ).eq_iff

theorem exists_vec_eq {e : Fin 7 → ZMod 2} (he : e ∈ evenWeight 7) : ∃ x : P, vec ψ x = e :=
  ⟨ψ.symm (Multiplicative.ofAdd ⟨e, he⟩), by simp [vec]⟩

theorem sq_eq_one_of_vec (ψ : P ≃* Multiplicative (evenWeight 7)) (x : P) : x * x = 1 := by
  rw [← vec_eq_zero_iff ψ, vec_mul, fun_add_self_eq_zero]

theorem mul_comm_of_vec (ψ : P ≃* Multiplicative (evenWeight 7)) (x y : P) : x * y = y * x := by
  apply vec_injective ψ
  rw [vec_mul, vec_mul, add_comm]

theorem nat_card_of_vec (ψ : P ≃* Multiplicative (evenWeight 7)) : Nat.card P = 64 := by
  rw [Nat.card_congr ψ.toEquiv, ← nat_card_evenWeight_seven]
  rfl

@[expose] def IsCoordAct (n : G) (σ : Perm (Fin 7)) : Prop :=
  ∀ x y : P, (y : G) = n * x * n⁻¹ → vec ψ y = permAct7 σ (vec ψ x)

@[expose] def imgSub (S : Subgroup G) : Submodule (ZMod 2) (Fin 7 → ZMod 2) where
  carrier := {e | ∃ x : P, (x : G) ∈ S ∧ vec ψ x = e}
  add_mem' := fun {e f} he hf => by
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨y, hy, rfl⟩ := hf
    exact ⟨x * y, S.mul_mem hx hy, vec_mul ψ x y⟩
  zero_mem' := ⟨1, S.one_mem, vec_one ψ⟩
  smul_mem' := fun c e he => by
    obtain ⟨x, hx, rfl⟩ := he
    rcases zmodTwo_eq_zero_or_one c with rfl | rfl
    · exact ⟨1, S.one_mem, by rw [vec_one, zero_smul]⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

theorem mem_imgSub {S : Subgroup G} {e : Fin 7 → ZMod 2} :
    e ∈ imgSub ψ S ↔ ∃ x : P, (x : G) ∈ S ∧ vec ψ x = e :=
  Iff.rfl

theorem nat_card_imgSub (S : Subgroup G) :
    Nat.card (imgSub ψ S) = Nat.card (P ⊓ S : Subgroup G) := by
  let F : (P ⊓ S : Subgroup G) → imgSub ψ S := fun x =>
    ⟨vec ψ ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩,
      ⟨⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩, (Subgroup.mem_inf.1 x.2).2, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => ?_, fun e => ?_⟩
    · have h0 := congrArg (fun e : imgSub ψ S => (e : Fin 7 → ZMod 2)) h
      have h1 := vec_injective ψ h0
      exact Subtype.ext (congrArg (fun z : P => (z : G)) h1)
    · obtain ⟨x, hx, hxe⟩ := e.2
      exact ⟨⟨(x : G), Subgroup.mem_inf.2 ⟨x.2, hx⟩⟩, Subtype.ext hxe⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm

theorem card_inf_le_eight {S : Subgroup G}
    (h : ∀ x : P, (x : G) ∈ S → x ≠ 1 → hammingNorm (vec ψ x) = 4) :
    Nat.card (P ⊓ S : Subgroup G) ≤ 8 := by
  have hW : ∀ u ∈ imgSub ψ S, u ≠ 0 → hammingNorm u = 4 := by
    rintro _ ⟨x, hx, rfl⟩ hne
    exact h x hx (fun h1 => hne (by rw [h1, vec_one]))
  have hdim := A7_binary_constant_weight_support_equation.2.1 (imgSub ψ S) hW
  rw [← nat_card_imgSub, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  calc 2 ^ finrank (ZMod 2) (imgSub ψ S) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hdim
    _ = 8 := by norm_num

theorem IsCoordAct.unique {n : G} (hn : n ∈ normalizer (P : Set G))
    {σ τ : Perm (Fin 7)} (hσ : IsCoordAct ψ n σ) (hτ : IsCoordAct ψ n τ) : σ = τ := by
  have key : ∀ e ∈ evenWeight 7, permAct7 σ e = permAct7 τ e := by
    intro e he
    obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
    let y : P := ⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn x).1 x.2⟩
    rw [← hσ x y rfl, ← hτ x y rfl]
  have h1 : τ⁻¹ * σ = 1 := by
    apply eq_one_of_permAct7_fix
    intro e he
    rw [permAct7_mul, key e he, ← permAct7_mul, inv_mul_cancel, permAct7_one]
  rw [← inv_mul_eq_one.1 h1]

@[expose] noncomputable def coordRep {A : Subgroup G} (hAN : A ≤ normalizer (P : Set G))
    (hA : ∀ a ∈ A, ∃ σ, IsCoordAct ψ a σ) : A →* Perm (Fin 7) where
  toFun a := Classical.choose (hA a a.2)
  map_one' := by
    have h := Classical.choose_spec (hA 1 (one_mem _))
    refine IsCoordAct.unique ψ (one_mem _) h fun x y hxy => ?_
    have : y = x := Subtype.ext (by rw [hxy]; group)
    rw [this, permAct7_one]
  map_mul' a b := by
    have hab := Classical.choose_spec (hA (a * b : A) (a * b).2)
    have ha := Classical.choose_spec (hA a a.2)
    have hb := Classical.choose_spec (hA b b.2)
    refine IsCoordAct.unique ψ (hAN (a * b).2) hab fun x z hxz => ?_
    let y : P := ⟨(b : G) * x * (b : G)⁻¹, (mem_normalizer_iff.1 (hAN b.2) x).1 x.2⟩
    have hz : (z : G) = (a : G) * y * (a : G)⁻¹ := by
      rw [hxz]
      simp only [y, Subgroup.coe_mul, mul_inv_rev]
      group
    rw [ha y z hz, hb x y rfl, permAct7_mul]

theorem coordRep_spec {A : Subgroup G} (hAN : A ≤ normalizer (P : Set G))
    (hA : ∀ a ∈ A, ∃ σ, IsCoordAct ψ a σ) (a : A) : IsCoordAct ψ a (coordRep ψ hAN hA a) :=
  Classical.choose_spec (hA a a.2)

theorem coordRep_eq_one_iff {A : Subgroup G} (hAN : A ≤ normalizer (P : Set G))
    (hA : ∀ a ∈ A, ∃ σ, IsCoordAct ψ a σ) (a : A) :
    coordRep ψ hAN hA a = 1 ↔ (a : G) ∈ centralizer (P : Set G) := by
  have hspec := coordRep_spec ψ hAN hA a
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    let y : P := ⟨(a : G) * x * (a : G)⁻¹, (mem_normalizer_iff.1 (hAN a.2) x).1 hx⟩
    have h1 := hspec ⟨x, hx⟩ y rfl
    rw [h, permAct7_one] at h1
    have h2 : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val (vec_injective ψ h1)
    calc x * a = (a : G) * x * (a : G)⁻¹ * a := by rw [h2]
      _ = a * x := by group
  · intro h
    refine IsCoordAct.unique ψ (hAN a.2) hspec fun x y hxy => ?_
    have : y = x := Subtype.ext (by rw [hxy, ← mem_centralizer_iff.1 h x x.2]; group)
    rw [this, permAct7_one]

end Coord

end CFSG.Quasithin.H13.A7
