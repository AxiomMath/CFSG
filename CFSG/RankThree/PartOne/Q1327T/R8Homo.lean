module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.GroupTheory.WeirSylow.Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG

abbrev Homo (p a m : ℕ) : Type := Fin m → Multiplicative (ZMod (p ^ a))

theorem isElementaryAbelian_of_le {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsElementaryAbelian p A) (h : B ≤ A) : IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_le hA h

theorem card_pow_eq_one_cyclic {p a : ℕ} [Fact p.Prime] (ha : 1 ≤ a) :
    Nat.card {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1} = p := by
  classical
  have hp := (Fact.out : p.Prime)
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hpa : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hle : Nat.card {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1} ≤ p := by
    have h := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ a))) (n := p) hp.pos
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (by rw [hpa]; exact dvd_pow_self p (by omega))
  have hgp : g ^ p = 1 := by
    have h1 := pow_orderOf_eq_one g
    rw [hg] at h1
    exact h1
  have hge : p ≤ Nat.card {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1} := by
    have hinj : Function.Injective
        (fun i : Fin p => (⟨g ^ (i : ℕ), by rw [← pow_mul, mul_comm, pow_mul, hgp, one_pow]⟩ :
          {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1})) := by
      intro i j hij
      have h1 : g ^ (i : ℕ) = g ^ (j : ℕ) := congrArg Subtype.val hij
      have := pow_injOn_Iio_orderOf (x := g) (by rw [hg]; exact i.2) (by rw [hg]; exact j.2) h1
      exact Fin.ext this
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  omega

theorem card_torsion_homo {p a : ℕ} [Fact p.Prime] (ha : 1 ≤ a) (m : ℕ) :
    Nat.card {x : Homo p a m // x ^ p = 1} = p ^ m := by
  have e : {x : Homo p a m // x ^ p = 1} ≃
      (Fin m → {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1}) :=
    (Equiv.subtypeEquivRight (fun x => by simp [funext_iff])).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_pow_eq_one_cyclic ha]

theorem nonempty_sigmaModel_mulEquiv_homo {p : ℕ} [Fact p.Prime] {e a N : ℕ} (hlt : N / e < p) :
    Nonempty (CFSG.GroupTheory.WeirSylow.sigmaModel p e a N ≃* Homo p a (N / e)) := by
  by_cases h0 : N / e = 0
  · have hd : Nat.digits p (N / e) = [] := by rw [h0]; simp
    have key : ∀ L : List ℕ, L = [] →
        Nonempty (((i : Fin L.length) → Fin L[i] →
          CFSG.GroupTheory.WeirSylow.wreathTower p (Multiplicative (ZMod (p ^ a))) i) ≃*
            Homo p a (N / e)) := by
      intro L hL
      subst hL
      have : IsEmpty (Fin ([] : List ℕ).length) := inferInstanceAs (IsEmpty (Fin 0))
      have : IsEmpty (Fin (N / e)) := by rw [h0]; infer_instance
      exact ⟨{ toEquiv := Equiv.ofUnique _ _
               map_mul' := fun _ _ => Subsingleton.elim _ _ }⟩
    exact key _ hd
  · have hd : Nat.digits p (N / e) = [N / e] := Nat.digits_of_lt p _ h0 hlt
    have key : ∀ (L : List ℕ) (m : ℕ), L = [m] →
        Nonempty (((i : Fin L.length) → Fin L[i] →
          CFSG.GroupTheory.WeirSylow.wreathTower p (Multiplicative (ZMod (p ^ a))) i) ≃*
            Homo p a m) := by
      intro L m hL
      subst hL
      let _ : Unique (Fin ([m] : List ℕ).length) := inferInstanceAs (Unique (Fin 1))
      exact ⟨MulEquiv.piUnique (fun i : Fin ([m] : List ℕ).length => Fin ([m] : List ℕ)[i] →
        CFSG.GroupTheory.WeirSylow.wreathTower p (Multiplicative (ZMod (p ^ a))) i)⟩
    exact key _ _ hd

theorem false_of_homocyclic_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {F : Subgroup G} [hF : IsElementaryAbelian p F] (hFc : Nat.card F = p ^ 2) {r : ℕ}
    (hB : ∀ D : Subgroup G, IsElementaryAbelian p D → F ≤ D →
      D ≤ Subgroup.centralizer (F : Set G) → Nat.card D ≤ p ^ (r + 2))
    (hS : ∀ S : Sylow p G, ∃ m a : ℕ, 1 ≤ a ∧ Nonempty ((S : Subgroup G) ≃* Homo p a m) ∧
      (m < 2 ∨ r + 2 < m)) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hFp : IsPGroup p F := IsElementaryAbelian.isPGroup p F
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  obtain ⟨m, a, ha, ⟨φ⟩, hm⟩ := hS S
  have hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x := by
    intro x hx y hy
    have h : (⟨x, hx⟩ : (S : Subgroup G)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    exact congrArg Subtype.val h
  let D : Subgroup G :=
    { carrier := {x | x ∈ (S : Subgroup G) ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        rw [(show Commute x y from hcomm x hx.1 y hy.1).mul_pow, hx.2, hy.2, mul_one]⟩
      one_mem' := ⟨Subgroup.one_mem _, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hDel : IsElementaryAbelian p D := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · exact Subtype.ext (hcomm a.1 a.2.1 b.1 b.2.1)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
      exact x.2.2
  have hFD : F ≤ D := fun f hf =>
    ⟨hFS hf, elemPow_eq_one_of_isElementaryAbelian (A := F) f hf⟩
  have hDc : D ≤ Subgroup.centralizer (F : Set G) := by
    intro d hd f hf
    exact hcomm f (hFS hf) d hd.1
  let ψ : D ≃ {x : Homo p a m // x ^ p = 1} :=
    { toFun := fun d => ⟨φ ⟨d, d.2.1⟩, by
        rw [← map_pow]
        have : (⟨(d : G), d.2.1⟩ : (S : Subgroup G)) ^ p = 1 := Subtype.ext d.2.2
        rw [this, map_one]⟩
      invFun := fun y => ⟨(φ.symm y : G), (φ.symm y).2, by
        have h1 : φ ((φ.symm y.1) ^ p) = 1 := by
          rw [map_pow, MulEquiv.apply_symm_apply]
          exact y.2
        have h2 : (φ.symm y.1) ^ p = 1 := φ.injective (by rw [h1, map_one])
        exact congrArg Subtype.val h2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  have hDcard : Nat.card D = p ^ m := by
    rw [Nat.card_congr ψ, card_torsion_homo ha]
  have h1 : Nat.card F ≤ Nat.card D := Subgroup.card_le_of_le hFD
  have h2 := hB D hDel hFD hDc
  rw [hFc, hDcard] at h1
  rw [hDcard] at h2
  have h3 : 2 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have h4 : m ≤ r + 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  omega

end CFSG.RankThree.PartOne.Q1327T.R8
