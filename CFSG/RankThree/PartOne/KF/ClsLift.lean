module

public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PerfectCover Subgroup

theorem commute_of_central_commute {S S' X L : Type} [Group S] [Group S'] [Group X] [Group L]
    [Group.IsPerfect S] (π : L →* X) (hker : π.ker ≤ center L) (a : S →* L) (b : S' →* L)
    (hcomm : ∀ A B, π (a A) * π (b B) = π (b B) * π (a A)) (A : S) (B : S') :
    a A * b B = b B * a A := by
  set y := b B with hy
  have hz : ∀ A : S, a A * y * (a A)⁻¹ * y⁻¹ ∈ center L := by
    intro A
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h := hcomm A B
    rw [← hy] at h
    rw [h]
    group
  have hcen : ∀ A : S, ∀ g : L, g * (a A * y * (a A)⁻¹ * y⁻¹) = (a A * y * (a A)⁻¹ * y⁻¹) * g :=
    fun A => Subgroup.mem_center_iff.mp (hz A)
  let c : S →* center L :=
    { toFun := fun A => ⟨a A * y * (a A)⁻¹ * y⁻¹, hz A⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro A A'
        apply Subtype.ext
        have h1 : a A' * y * (a A')⁻¹ = (a A' * y * (a A')⁻¹ * y⁻¹) * y := by group
        have h2 : a A * y * (a A)⁻¹ = (a A * y * (a A)⁻¹ * y⁻¹) * y := by group
        have h3 := hcen A' (a A)
        change a (A * A') * y * (a (A * A'))⁻¹ * y⁻¹ =
          (a A * y * (a A)⁻¹ * y⁻¹) * (a A' * y * (a A')⁻¹ * y⁻¹)
        calc a (A * A') * y * (a (A * A'))⁻¹ * y⁻¹
            = a A * (a A' * y * (a A')⁻¹) * (a A)⁻¹ * y⁻¹ := by rw [map_mul]; group
          _ = a A * ((a A' * y * (a A')⁻¹ * y⁻¹) * y) * (a A)⁻¹ * y⁻¹ := by rw [← h1]
          _ = (a A * (a A' * y * (a A')⁻¹ * y⁻¹)) * y * (a A)⁻¹ * y⁻¹ := by group
          _ = ((a A' * y * (a A')⁻¹ * y⁻¹) * a A) * y * (a A)⁻¹ * y⁻¹ := by rw [h3]
          _ = (a A' * y * (a A')⁻¹ * y⁻¹) * (a A * y * (a A)⁻¹ * y⁻¹) := by group
          _ = (a A * y * (a A)⁻¹ * y⁻¹) * (a A' * y * (a A')⁻¹ * y⁻¹) := by
            exact hcen A (a A' * y * (a A')⁻¹ * y⁻¹) }
  have hc : commutator S ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [Group.IsPerfect.commutator_eq_top (G := S)] at hc
  have hA : c A = 1 := MonoidHom.mem_ker.mp (hc (Subgroup.mem_top A))
  have h1 : a A * y * (a A)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hA
  have h2 : a A * y * (a A)⁻¹ = y := mul_inv_eq_one.mp h1
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem exists_lift_of_coprime {S X L : Type} [Group S] [Group X] [Group L] [Group.IsPerfect S]
    (ψ : S →* X) (π : L →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ center L) {a b : ℕ}
    (hab : Nat.Coprime a b) (hM : ∀ m ∈ hopfMultiplier S, m ^ a = 1)
    (hZ : ∀ z ∈ π.ker, z ^ b = 1) : ∃ σ : S →* L, π.comp σ = ψ := by
  let P : Subgroup (S × L) :=
    MonoidHom.eqLocus (ψ.comp (MonoidHom.fst S L)) (π.comp (MonoidHom.snd S L))
  have hP : ∀ x : S × L, x ∈ P ↔ ψ x.1 = π x.2 := fun x => Iff.rfl
  let p₁ : P →* S := (MonoidHom.fst S L).comp P.subtype
  have hp₁ : Function.Surjective p₁ := by
    intro s
    obtain ⟨l, hl⟩ := hπ (ψ s)
    exact ⟨⟨(s, l), (hP _).2 hl.symm⟩, rfl⟩
  have hp₁ker : ∀ x : P, p₁ x = 1 → (x : S × L).1 = 1 ∧ (x : S × L).2 ∈ π.ker := by
    intro x hx
    have h1 : (x : S × L).1 = 1 := hx
    refine ⟨h1, ?_⟩
    have h2 := (hP _).1 x.2
    rw [h1, map_one] at h2
    exact MonoidHom.mem_ker.mpr h2.symm
  have hp₁c : p₁.ker ≤ center P := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp₁ker x (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · change (y : S × L).1 * (x : S × L).1 = (x : S × L).1 * (y : S × L).1
      rw [h1, one_mul, mul_one]
    · change (y : S × L).2 * (x : S × L).2 = (x : S × L).2 * (y : S × L).2
      exact (Subgroup.mem_center_iff.mp (hker h2) _)
  let Φ : HopfCover S →* P := hopfLift p₁ hp₁ hp₁c
  have hΦ : ∀ m ∈ hopfMultiplier S, Φ m = 1 := by
    intro m hm
    have h1 : p₁ (Φ m) = 1 := by
      have := congrArg (fun f : HopfCover S →* S => f m) (comp_hopfLift p₁ hp₁ hp₁c)
      exact this.trans (MonoidHom.mem_ker.mp hm)
    obtain ⟨h2, h3⟩ := hp₁ker (Φ m) h1
    have hpa : (Φ m) ^ a = 1 := by rw [← map_pow, hM m hm, map_one]
    have hpb : (Φ m) ^ b = 1 := by
      apply Subtype.ext
      apply Prod.ext
      · change ((Φ m : P) : S × L).1 ^ b = 1
        rw [h2, one_pow]
      · change ((Φ m : P) : S × L).2 ^ b = 1
        exact hZ _ h3
    have hdvd : orderOf (Φ m) ∣ Nat.gcd a b :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpa) (orderOf_dvd_of_pow_eq_one hpb)
    rw [hab.gcd_eq_one, Nat.dvd_one] at hdvd
    exact orderOf_eq_one_iff.mp hdvd
  have hsurj : Function.Surjective (hopfCoverMap S) := hopfCoverMap_surjective
  let e : HopfCover S ⧸ (hopfCoverMap S).ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  let Φ' : HopfCover S ⧸ (hopfCoverMap S).ker →* P :=
    QuotientGroup.lift (hopfCoverMap S).ker Φ fun m hm => hΦ m hm
  refine ⟨(MonoidHom.snd S L).comp (P.subtype.comp (Φ'.comp e.symm.toMonoidHom)), ?_⟩
  ext x
  obtain ⟨u, rfl⟩ := hsurj x
  have hs : e.symm (hopfCoverMap S u) = (u : HopfCover S ⧸ (hopfCoverMap S).ker) :=
    e.symm_apply_eq.mpr rfl
  have h1 := (hP _).1 (Φ u).2
  have h2 : p₁ (Φ u) = hopfCoverMap S u := by
    have := congrArg (fun f : HopfCover S →* S => f u) (comp_hopfLift p₁ hp₁ hp₁c)
    exact this
  show π (((Φ' (e.symm (hopfCoverMap S u)) : P) : S × L).2) = ψ (hopfCoverMap S u)
  rw [hs]
  change π (((Φ u : P) : S × L).2) = ψ (hopfCoverMap S u)
  rw [← h2]
  exact h1.symm

end CFSG.RankThree.PartOne.KFU
