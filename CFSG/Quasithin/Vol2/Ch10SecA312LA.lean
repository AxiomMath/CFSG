module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312LF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L (modO2EquivOfHom sl2EquivStatedProj sl2_isSimple
  sl2_nonabelian dInf_eq_perfectCore exists_finset_card_four exists_conj_of_isSylowTwoOf)
open Matrix

theorem card_eq_of_sl2_equiv {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (e : SpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K') :
    Nat.card K = Nat.card K' := by
  have h := Nat.card_congr e.toEquiv
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h2 : 1 < Nat.card K' := Finite.one_lt_card
  have key : ∀ a b : ℕ, 1 < a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have hle : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
    have hpos : 0 < b ^ 2 - 1 := by
      have : 1 < b ^ 2 := by nlinarith
      omega
    calc a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) := Nat.mul_le_mul_left a hle
      _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab hpos
  rcases lt_trichotomy (Nat.card K) (Nat.card K') with hlt | heq | hgt
  · exact absurd h (key _ _ h1 hlt).ne
  · exact heq
  · exact absurd h.symm (key _ _ h2 hgt).ne

theorem exists_sl2_of_isPSL {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hK : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hn1 hcard
  refine ⟨?_, K, hF, hFin, hK, hcard, ⟨e.trans sl2EquivStatedProj.symm⟩⟩
  by_contra hlt
  have h1 : n = 1 := by omega
  subst h1
  exact hne rfl

theorem nonabelian_of_isPSL {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := exists_sl2_of_isPSL h
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a, b, hab⟩ := sl2_nonabelian hK4
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa using this

theorem not_isPSL_of_subsingleton {n : ℕ} {X : Type} [Group X] [Subsingleton X] :
    ¬ IsPSL 2 2 n X := fun h => by
  obtain ⟨a, b, hab⟩ := nonabelian_of_isPSL h
  exact hab (Subsingleton.elim _ _)

theorem subsingleton_modO2_of_eq_bot {S : Type} [Group S] {B : Subgroup S} (h : B = ⊥) :
    Subsingleton (ModO2 B) := by
  subst h
  exact QuotientGroup.mk_surjective.subsingleton

theorem exists_modO2_equiv_of_residual {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) {Q : Subgroup S} (hQ : IsParabolic2 ⊤ Q) (hQtop : Q ≠ ⊤)
    (hne : perfectCore Q ≠ ⊥) :
    ∃ j, Nonempty (ModO2 (perfectCore Q) ≃* ModO2 (perfectCore (P j))) := by
  obtain ⟨-, S', hS', hN⟩ := hQ
  have hS'Q : S' ≤ Q := fun s hs => hN ⟨trivial, Subgroup.le_normalizer hs⟩
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hS' hU
  have hUQ : U ≤ Q.map (MulAut.conj g).toMonoidHom := hg ▸ Subgroup.map_mono hS'Q
  have hQtop' : Q.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    refine hQtop (eq_top_iff.2 fun x _ => ?_)
    have hx : (MulAut.conj g).toMonoidHom x ∈ Q.map (MulAut.conj g).toMonoidHom :=
      h ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hxy⟩ := hx
    rwa [(MulAut.conj g).injective hxy] at hy
  have hcore : perfectCore (Q.map (MulAut.conj g).toMonoidHom) =
      (perfectCore Q).map (MulAut.conj g).toMonoidHom := (map_perfectCore _ Q).symm
  have hns : ¬ Group.IsSolvable ↥(Q.map (MulAut.conj g).toMonoidHom) := by
    rw [isSolvable_iff_perfectCore_eq_bot, hcore]
    exact fun h => hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 h)
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 _ hUQ hQtop' hns
  have hd' : perfectCore (Q.map (MulAut.conj g).toMonoidHom) = perfectCore (P j) := by
    rw [← dInf_eq_perfectCore, ← dInf_eq_perfectCore, hd]
  exact ⟨j, ⟨A312.modO2Equiv (((perfectCore Q).equivMapOfInjective _
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (hcore.symm.trans hd')))⟩⟩

@[expose] def LeviField (f : ℕ) {S : Type} [Group S] (P : Subgroup S) : Prop :=
  perfectCore P = ⊥ ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ), Nat.card K = 2 ^ m ∧
      f ∣ m ∧ 2 ≤ m ∧ ∃ g : ↥(perfectCore P) →* SpecialLinearGroup (Fin 2) K,
        Function.Surjective g ∧ IsPGroup 2 g.ker) ∨
    ∀ n, ¬ IsPSL 2 2 n (ModO2 (perfectCore P))

theorem dvd_of_leviField {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) {f : ℕ} (hL : ∀ j, LeviField f (P j)) {Q : Subgroup S}
    (hQ : IsParabolic2 ⊤ Q) (hQtop : Q ≠ ⊤) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (perfectCore Q))) : f ∣ n := by
  have hne : perfectCore Q ≠ ⊥ := fun h => by
    have := subsingleton_modO2_of_eq_bot h
    exact not_isPSL_of_subsingleton hn
  obtain ⟨j, ⟨e⟩⟩ := exists_modO2_equiv_of_residual hU hP hQ hQtop hne
  have hn' : IsPSL 2 2 n (ModO2 (perfectCore (P j))) := IsPSL.of_mulEquiv e hn
  rcases hL j with hbot | ⟨K, _, _, _, m, hK, hfm, hm, g, hg, hker⟩ | hnot
  · have := subsingleton_modO2_of_eq_bot hbot
    exact absurd hn' not_isPSL_of_subsingleton
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have := sl2_isSimple hK4
    obtain ⟨-, K', _, _, _, hK', ⟨e₂⟩⟩ := exists_sl2_of_isPSL hn'
    have hcard := card_eq_of_sl2_equiv
      (e₂.symm.trans (modO2EquivOfHom (sl2_nonabelian hK4) g hg hker))
    rw [hK', hK] at hcard
    rw [Nat.pow_right_injective (le_refl 2) hcard]
    exact hfm
  · exact absurd hn' (hnot n)

end CFSG.Quasithin.Vol2.Ch10.A312LF
