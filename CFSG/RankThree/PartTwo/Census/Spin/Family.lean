module

public import CFSG.RankThree.PartTwo.Census.Spin.Witness

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti

theorem family_witness {M : Type*} [Group M] {H : Subgroup M} {p k : ℕ}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {A : κ → Type*} [∀ a, AddCommGroup (A a)]
    (ϕ : ∀ a, Multiplicative (A a) →* M)
    (hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v))
    (hD : ∀ a u, ϕ a u ∈ ⁅H, H⁆) (hp : ∀ a (u : A a), p • u = 0)
    (hcard : Nat.card (∀ a, Multiplicative (A a)) = p ^ k)
    (y : κ → M) (hy : ∀ a, y a ∈ ⁅H, H⁆) (hdet : ∀ a u, Commute (ϕ a u) (y a) → u = 1)
    (hoff : ∀ a b, a ≠ b → ∀ u, Commute (ϕ b u) (y a))
    (t : M) (htD : t ∈ ⁅H, H⁆) (ht2 : t ^ 2 = 1) (htz : ∃ g ∈ ⁅H, H⁆, t * g ≠ g * t)
    (ht : ∀ a u, Commute t (ϕ a u)) :
    HasWitness (DerivedCentralQuotient H) p k := by
  set θ := MonoidHom.noncommPiCoprod ϕ hcomm
  have hdetect : ∀ e, (∀ a, Commute (θ e) (y a)) → e = 1 := by
    intro e he
    funext a
    have hsplit : e = Pi.mulSingle (M := fun i => Multiplicative (A i)) a (e a) *
        Function.update e a 1 := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [hb]
    have hrest : Commute (θ (Function.update e a 1)) (y a) := by
      rw [← Finset.univ_prod_mulSingle (Function.update e a 1)]
      have hmul : ∀ z z', Commute (θ z) (y a) → Commute (θ z') (y a) →
          Commute (θ (z * z')) (y a) := fun z z' hz hz' => by
        rw [map_mul]
        exact hz.mul_left hz'
      have hone : Commute (θ 1) (y a) := by
        rw [map_one]
        exact Commute.one_left _
      refine Finset.prod_induction _ (fun z => Commute (θ z) (y a)) hmul hone fun b _ => ?_
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, map_one]
        exact Commute.one_left _
      · exact hoff a b (Ne.symm hb) _
    have h1 := he a
    rw [hsplit, map_mul, MonoidHom.noncommPiCoprod_mulSingle] at h1
    have h3 : Commute (ϕ a (e a)) (y a) := by
      have e1 := h1.eq
      have e2 := hrest.eq
      refine mul_right_cancel (b := θ (Function.update e a 1)) ?_
      rw [mul_assoc, ← e2, ← mul_assoc, e1, mul_assoc]
    exact hdet a _ h3
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    exact (Subgroup.mem_bot).mpr (hdetect e fun a => by rw [he]; exact Commute.one_left _)
  refine exists_quotient_witness_of_commute (E := θ.range) (t := t) ⟨⟨fun a b => ?_⟩⟩ ?_ ?_ ?_
    htD ht2 ?_ htz ?_
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : M) * (b : M) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := by
      funext a
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (e a)) = Multiplicative.ofAdd 0
      rw [hp]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, hcard]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    exact hD a u
  · rintro _ ⟨e, rfl⟩ hz
    rw [hdetect e fun a => hz _ (hy a), map_one]
  · rintro _ ⟨e, rfl⟩
    exact (MonoidHom.commute_noncommPiCoprod ϕ (fun a u => ht a u) e).eq.symm

end CFSG.RankThree.PartTwo.Census.Spin
