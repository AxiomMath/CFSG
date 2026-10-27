module

public import CFSG.Timmesfeld.Orders.ExceptionalTwisted

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

@[expose] def d4i (n : Fin 4) : Fin TwistTag.D4.tag.rank := n

theorem d4i_cases (i : Fin TwistTag.D4.tag.rank) :
    i = d4i 0 ∨ i = d4i 1 ∨ i = d4i 2 ∨ i = d4i 3 := by
  revert i
  decide

section Compat

variable {K : Type} [Field K]

theorem map_units_eq_pow {σ : K →+* K} {q : ℕ} (hσc : ∀ c, σ c = c ^ q) (u : Kˣ) :
    Units.map σ.toMonoidHom u = u ^ q :=
  Units.ext (by simp [hσc])

theorem compat_D4_eq_one {σ : K →+* K} {q : ℕ} (hq : 0 < q) (hσc : ∀ c, σ c = c ^ q) {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ q - 1) {c : Fin TwistTag.D4.tag.rank → Kˣ}
    (hc : c ∈ compatSubgroup (t := TwistTag.D4) σ) (hcp : c ^ p = 1) (h0 : c (d4i 0) = 1) :
    c = 1 := by
  have hperm0 : TwistTag.D4.perm (d4i 0) = d4i 1 := by decide
  have hperm1 : TwistTag.D4.perm (d4i 1) = d4i 3 := by decide
  have hperm2 : TwistTag.D4.perm (d4i 2) = d4i 2 := by decide
  have h1 : c (d4i 1) = 1 := by
    have := (mem_compatSubgroup σ).1 hc (d4i 0)
    rw [hperm0, h0, map_units_eq_pow hσc, one_pow] at this
    exact this
  have h3 : c (d4i 3) = 1 := by
    have := (mem_compatSubgroup σ).1 hc (d4i 1)
    rw [hperm1, h1, map_units_eq_pow hσc, one_pow] at this
    exact this
  have h2 : c (d4i 2) = 1 := by
    have h2q : c (d4i 2) = c (d4i 2) ^ q := by
      have := (mem_compatSubgroup σ).1 hc (d4i 2)
      rw [hperm2, map_units_eq_pow hσc] at this
      exact this
    have hq1 : c (d4i 2) ^ (q - 1) = 1 := by
      have h' : c (d4i 2) * c (d4i 2) ^ (q - 1) = c (d4i 2) * 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hq, ← h2q, mul_one]
      exact mul_left_cancel h'
    have hp2 : c (d4i 2) ^ p = 1 := by simpa using congrFun hcp (d4i 2)
    have hcop : Nat.Coprime p (q - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    have : orderOf (c (d4i 2)) ∣ Nat.gcd p (q - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp2) (orderOf_dvd_of_pow_eq_one hq1)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  funext i
  rcases d4i_cases i with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem eq_one_of_pow_eq_one_of_not_dvd [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K - 1) {u : Kˣ} (hu : u ^ p = 1) : u = 1 := by
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
  have h1 : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [Nat.card_units] at h1
  have : orderOf u ∣ Nat.gcd p (Nat.card K - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu) h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

end Compat

section Torus

variable {K : Type} [Field K] [Finite K]

theorem coordHom_injective_D4 (hodd : Odd (Nat.card K - 1)) :
    Function.Injective ((torusGroup TwistTag.D4.tag K).subtype.comp
      (torusCoordHom TwistTag.D4.tag K)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hbot : (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker = ⊥ :=
    (Subgroup.card_eq_one).1 (card_ker_zpowMatrix_D4_eq_one (K := K) hodd)
  have hker : c ∈ (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker := by
    rw [MonoidHom.mem_ker, ← torusCoordHom_eq_one_iff]
    exact Subtype.ext hc
  rw [hbot, Subgroup.mem_bot] at hker
  exact hker

end Torus

section TorusEmbedding

variable {K : Type} [Field K] [Finite K]

theorem exists_injective_of_le_graphFixedRootTorus_D4 (σ : K →+* K) (hσ : Function.Surjective σ)
    {q : ℕ} (hq : 0 < q) (hσc : ∀ c, σ c = c ^ q) (hodd : Odd (Nat.card K - 1)) {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ q - 1)
    {P : Subgroup (ModGL TwistTag.D4.tag K)} (hP : P ≤ graphFixedRootTorus TwistTag.D4 K σ)
    (hPp : ∀ x ∈ P, x ^ p = 1) :
    ∃ g : P →* Kˣ, Function.Injective g ∧ ∀ x, g x ^ p = 1 := by
  set f : (Fin TwistTag.D4.tag.rank → Kˣ) →* ModGL TwistTag.D4.tag K :=
    (torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K) with hf
  have hfinj : Function.Injective f := coordHom_injective_D4 hodd
  rw [graphFixedRootTorus_eq_compatTorus hσ] at hP
  have hPc : ∀ x ∈ P, ∃ c ∈ compatSubgroup (t := TwistTag.D4) σ, f c = x := fun x hx => hP hx
  choose! d hdc hdf using hPc
  have hd : ∀ x ∈ P, ∀ y ∈ P, d (x * y) = d x * d y := fun x hx y hy => hfinj (by
    rw [map_mul, hdf _ (mul_mem hx hy), hdf _ hx, hdf _ hy])
  have hd1 : d 1 = 1 := hfinj (by rw [map_one, hdf _ (one_mem P)])
  let g : P →* Kˣ :=
    { toFun := fun x => d x.1 (d4i 0)
      map_one' := by
        show d 1 (d4i 0) = 1
        rw [hd1]
        rfl
      map_mul' := fun x y => by
        show d (x.1 * y.1) (d4i 0) = d x.1 (d4i 0) * d y.1 (d4i 0)
        rw [hd _ x.2 _ y.2]
        rfl }
  refine ⟨g, ?_, fun x => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hdx : d x.1 = 1 := by
      refine compat_D4_eq_one hq hσc hp hpq (hdc _ x.2) ?_ hx
      refine hfinj ?_
      rw [map_pow, hdf _ x.2, hPp _ x.2, map_one]
    have : (x : ModGL TwistTag.D4.tag K) = 1 := by
      rw [← hdf _ x.2, hdx, map_one]
    exact Subtype.ext this
  · have h := hPp _ x.2
    have hdp : d x.1 ^ p = 1 := hfinj (by rw [map_pow, hdf _ x.2, h, map_one])
    have := congrFun hdp (d4i 0)
    simpa [g] using this

end TorusEmbedding

end CFSG.RankThree.PartOne.KFU
