module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin

namespace SBc9

section Averaging

private theorem exists_transfer_hom {X A : Type} [Group X] [Finite X] [CommGroup A]
    (act : X → A →* A) (hmul : ∀ x y a, act (x * y) a = act x (act y a))
    {P : Subgroup X} (B : Subgroup A)
    (hB : ∀ p ∈ P, ∀ a, act p a * a⁻¹ ∈ B) :
    ∃ τ : A →* A ⧸ B, (∀ x a, τ (act x a) = τ a) ∧
      ∀ a, (∀ x, act x a = a) → τ a = QuotientGroup.mk (a ^ P.index) := by
  classical
  have : Fintype (X ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (X ⧸ P) = P.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  let F : A → X → A ⧸ B := fun a x => QuotientGroup.mk (act x⁻¹ a)
  have hFmul : ∀ a b x, F (a * b) x = F a x * F b x := fun a b x => by
    simp only [F, map_mul, QuotientGroup.mk_mul]
  have hFone : ∀ x, F 1 x = 1 := fun x => by
    simp only [F, map_one, QuotientGroup.mk_one]
  have hFcoset : ∀ a x p, p ∈ P → F a (x * p) = F a x := fun a x p hp => by
    have h1 : act (x * p)⁻¹ a = act p⁻¹ (act x⁻¹ a) := by rw [mul_inv_rev, hmul]
    show (QuotientGroup.mk (act (x * p)⁻¹ a) : A ⧸ B) = QuotientGroup.mk (act x⁻¹ a)
    rw [QuotientGroup.eq, h1]
    have h2 := B.inv_mem (hB p⁻¹ (P.inv_mem hp) (act x⁻¹ a))
    rwa [mul_inv_rev, inv_inv, mul_comm] at h2
  have hperm : ∀ a g, ∏ i : X ⧸ P, F a (g * i.out) = ∏ i : X ⧸ P, F a i.out := by
    intro a g
    have h1 : ∀ i : X ⧸ P, F a (g * i.out) = F a (g • i).out := fun i => by
      have hq : (QuotientGroup.mk (g • i).out : X ⧸ P) = QuotientGroup.mk (g * i.out) := by
        rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      calc F a (g * i.out)
          = F a ((g • i).out * ((g • i).out⁻¹ * (g * i.out))) := by rw [mul_inv_cancel_left]
        _ = F a (g • i).out := hFcoset _ _ _ (QuotientGroup.eq.mp hq)
    simp_rw [h1]
    exact Equiv.prod_comp (MulAction.toPerm g) (fun i : X ⧸ P => F a i.out)
  refine ⟨{ toFun := fun a => ∏ i : X ⧸ P, F a i.out
            map_one' := by simp only [hFone, Finset.prod_const_one]
            map_mul' := fun a b => by simp only [hFmul, Finset.prod_mul_distrib] }, ?_, ?_⟩
  · intro l a
    have h1 : ∀ x, F (act l a) x = F a (l⁻¹ * x) := fun x => by
      simp only [F, ← hmul, mul_inv_rev, inv_inv]
    show ∏ i : X ⧸ P, F (act l a) i.out = ∏ i : X ⧸ P, F a i.out
    simp_rw [h1]
    exact hperm a l⁻¹
  · intro a ha
    show ∏ i : X ⧸ P, F a i.out = QuotientGroup.mk (a ^ P.index)
    have h1 : ∀ x, F a x = QuotientGroup.mk a := fun x => by
      simp only [F, ha]
    simp_rw [h1]
    rw [Finset.prod_const, Finset.card_univ, hcard, QuotientGroup.mk_pow]

end Averaging

section Coinvariants

theorem inf_centralizer_le_commutator_of_odd_index {G : Type} [Group G] [Finite G] {L P Q : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQ2 : ∀ x ∈ Q, x * x = 1) (hPL : P ≤ L) (hodd : ¬ 2 ∣ P.relIndex L)
    (hQL : ⁅Q, L⁆ = Q) :
    Q ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅Q, P⁆ := by
  have _ := hPL
  have hconjQ : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := fun l hl q hq =>
    (Subgroup.mem_set_normalizer_iff.mp (hLQ hl) q).mp hq
  let _ : CommGroup ↥Q :=
    { (inferInstance : Group ↥Q) with mul_comm := fun a b => Subtype.ext (hQc a a.2 b b.2) }
  let act : ↥L → ↥Q →* ↥Q := fun l =>
    MonoidHom.mk' (fun q : ↥Q => (⟨(l : G) * q * (l : G)⁻¹, hconjQ l l.2 q q.2⟩ : ↥Q))
      (fun a b => Subtype.ext (by simp [mul_assoc]))
  have hmul : ∀ x y a, act (x * y) a = act x (act y a) := fun x y a =>
    Subtype.ext (by simp [act, mul_assoc])
  have hB : ∀ p ∈ P.subgroupOf L, ∀ a : ↥Q, act p a * a⁻¹ ∈ (⁅Q, P⁆).subgroupOf Q := by
    intro p hp a
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hp) a.2
  obtain ⟨τ, hτact, hτfix⟩ :=
    exists_transfer_hom (P := P.subgroupOf L) act hmul ((⁅Q, P⁆).subgroupOf Q) hB
  have hker : ⁅Q, L⁆ ≤ τ.ker.map Q.subtype := by
    refine Subgroup.commutator_le.mpr fun q hq l hl => ?_
    refine ⟨⟨q, hq⟩ * (act ⟨l, hl⟩ ⟨q, hq⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hτact, mul_inv_cancel]
    · simp [act, commutatorElement_def, mul_assoc]
  have hτ1 : ∀ (z : G) (hz : z ∈ Q), τ ⟨z, hz⟩ = 1 := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hker (hQL.ge hz)
    have hw' : w = ⟨z, hz⟩ := Subtype.ext hwz
    rwa [hw'] at hw
  intro z hz
  obtain ⟨hzQ, hzc⟩ := hz
  have hfix : ∀ x : ↥L, act x ⟨z, hzQ⟩ = ⟨z, hzQ⟩ := fun x => Subtype.ext (by
    have hx := Subgroup.mem_centralizer_iff.mp hzc x x.2
    show (x : G) * z * (x : G)⁻¹ = z
    rw [hx, mul_inv_cancel_right])
  have h1 := hτfix ⟨z, hzQ⟩ hfix
  rw [hτ1 z hzQ, eq_comm, QuotientGroup.eq_one_iff] at h1
  have h2 : z ^ P.relIndex L ∈ ⁅Q, P⁆ := Subgroup.mem_subgroupOf.mp h1
  obtain ⟨k, hk⟩ : Odd (P.relIndex L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hpow : z ^ P.relIndex L = z := by
    rw [hk, pow_succ, pow_mul, sq, hQ2 z hzQ, one_pow, one_mul]
  rwa [hpow] at h2

end Coinvariants

end SBc9

end CFSG.Quasithin
