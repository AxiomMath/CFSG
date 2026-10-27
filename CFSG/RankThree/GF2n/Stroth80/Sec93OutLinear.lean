module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSL
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem mem_of_sq_mem_of_odd_relIndex {G : Type*} [Group G] (H K : Subgroup G) [H.Normal]
    (hodd : Odd (H.relIndex K)) {g : G} (hg : g ∈ K) (hg2 : g ^ 2 ∈ H) : g ∈ H := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : g ^ H.relIndex K ∈ H := Subgroup.pow_relIndex_mem H hg
  have hg' : g = ((g ^ 2)⁻¹) ^ k * g ^ H.relIndex K := by
    rw [hk, inv_pow, ← pow_mul, pow_succ, pow_mul]
    group
  rw [hg']
  exact H.mul_mem (H.pow_mem (H.inv_mem hg2) k) h1

theorem card_elemAbelian_outer_le {P : Type} [Group P] [Finite P]
    (N C : Subgroup (MulAut P)) [N.Normal] (hInn : OuterAutomorphisms.inner P ≤ N)
    (hodd : Odd ((OuterAutomorphisms.inner P).relIndex N))
    (hdec : ∀ α : MulAut P, ∃ i ∈ N, ∃ c ∈ C, α = i * c) (hNC : N ⊓ C = ⊥)
    (A : Subgroup (Outer P)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ Nat.card {c : MulAut P // c ∈ C ∧ c ^ 2 = 1} := by
  classical
  haveI : Finite (MulAut P) := Finite.of_injective (fun f : MulAut P => (f : P → P))
    DFunLike.coe_injective
  let π : MulAut P →* Outer P := QuotientGroup.mk' (OuterAutomorphisms.inner P)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (OuterAutomorphisms.inner P)
  choose α hα using fun a : A => hπ (a : Outer P)
  choose i hiN c hcC hdecomp using fun a : A => hdec (α a)
  have hc2 : ∀ a : A, c a ^ 2 = 1 := by
    intro a
    have h1 : π (α a) ^ 2 = 1 := by
      rw [hα a]
      exact hA.2 _ a.2
    have h2 : α a ^ 2 ∈ OuterAutomorphisms.inner P := by
      have h2' : π (α a ^ 2) = 1 := by
        rw [map_pow]
        exact h1
      exact (QuotientGroup.eq_one_iff _).1 h2'
    have h3 : c a ^ 2 ∈ N := by
      have : c a ^ 2 = (i a * (c a * i a * (c a)⁻¹))⁻¹ * α a ^ 2 := by
        rw [hdecomp a, pow_two (i a * c a), pow_two (c a)]
        group
      rw [this]
      exact N.mul_mem (N.inv_mem (N.mul_mem (hiN a) (by
        have := (inferInstance : N.Normal).conj_mem (i a) (hiN a) (c a)
        simpa [mul_assoc] using this))) (hInn h2)
    have h4 : c a ^ 2 ∈ N ⊓ C := ⟨h3, C.pow_mem (hcC a) 2⟩
    rw [hNC, Subgroup.mem_bot] at h4
    exact h4
  let f : A → {c : MulAut P // c ∈ C ∧ c ^ 2 = 1} := fun a => ⟨c a, hcC a, hc2 a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hcab : c a = c b := congrArg Subtype.val hab
    have hβ : α b * (α a)⁻¹ = i b * (i a)⁻¹ := by
      rw [hdecomp a, hdecomp b, hcab]
      group
    have hβN : α b * (α a)⁻¹ ∈ N := by
      rw [hβ]
      exact N.mul_mem (hiN b) (N.inv_mem (hiN a))
    have hπβ : π (α b * (α a)⁻¹) = (b : Outer P) * (a : Outer P)⁻¹ := by
      rw [map_mul, map_inv, hα a, hα b]
    have hsq : (b : Outer P) * (a : Outer P)⁻¹ * ((b : Outer P) * (a : Outer P)⁻¹) = 1 := by
      have hab' : (a : Outer P)⁻¹ * (b : Outer P) = (b : Outer P) * (a : Outer P)⁻¹ := by
        have h1 : (a : Outer P) * (b : Outer P) = (b : Outer P) * (a : Outer P) :=
          hA.comm a.2 b.2
        calc (a : Outer P)⁻¹ * (b : Outer P)
            = (a : Outer P)⁻¹ * ((b : Outer P) * (a : Outer P)) * (a : Outer P)⁻¹ := by group
          _ = (a : Outer P)⁻¹ * ((a : Outer P) * (b : Outer P)) * (a : Outer P)⁻¹ := by rw [h1]
          _ = (b : Outer P) * (a : Outer P)⁻¹ := by group
      have ha2 : (a : Outer P) * (a : Outer P) = 1 := hA.mul_self_eq_one a.2
      have hb2 : (b : Outer P) * (b : Outer P) = 1 := hA.mul_self_eq_one b.2
      calc (b : Outer P) * (a : Outer P)⁻¹ * ((b : Outer P) * (a : Outer P)⁻¹)
          = (b : Outer P) * ((a : Outer P)⁻¹ * (b : Outer P)) * (a : Outer P)⁻¹ := by group
        _ = (b : Outer P) * ((b : Outer P) * (a : Outer P)⁻¹) * (a : Outer P)⁻¹ := by rw [hab']
        _ = ((b : Outer P) * (b : Outer P)) * ((a : Outer P)⁻¹ * (a : Outer P)⁻¹) := by group
        _ = 1 := by
          have : (a : Outer P)⁻¹ * (a : Outer P)⁻¹ = 1 := by
            have := congrArg (fun x => x⁻¹) ha2
            simpa [mul_inv_rev] using this
          rw [hb2, this, one_mul]
    have hβ2 : (α b * (α a)⁻¹) ^ 2 ∈ OuterAutomorphisms.inner P := by
      have h2' : π ((α b * (α a)⁻¹) ^ 2) = 1 := by
        rw [map_pow, hπβ, pow_two]
        exact hsq
      exact (QuotientGroup.eq_one_iff _).1 h2'
    have hβi : α b * (α a)⁻¹ ∈ OuterAutomorphisms.inner P :=
      mem_of_sq_mem_of_odd_relIndex (OuterAutomorphisms.inner P) N hodd hβN hβ2
    have h1 : π (α b * (α a)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hβi
    rw [hπβ] at h1
    apply Subtype.ext
    exact (mul_inv_eq_one.1 h1).symm
  exact Nat.card_le_card_of_injective f hf

open CFSG.StandardType.AutPSL CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_involutions_compl_le {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] :
    Nat.card {c : MulAut (projectiveSL n K) //
      c ∈ (compl : Subgroup (MulAut (projectiveSL n K))) ∧ c ^ 2 = 1} ≤ 4 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hk
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact k.pos.ne')
  haveI : Fintype (RingAut K) := Fintype.ofFinite _
  have hp : Nat.card {σ : RingAut K // σ * σ = 1} ≤ 2 := by
    have h := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa [pow_two] using h
  set X := {c : MulAut (projectiveSL n K) //
    c ∈ (compl : Subgroup (MulAut (projectiveSL n K))) ∧ c ^ 2 = 1} with hX
  have hex : ∀ c : X, ∃ σ : RingAut K, σ * σ = 1 ∧
      (c.1 = fieldAut n K σ ∨ c.1 = fieldAut n K σ * graphAut) :=
    fun c => involution_compl hn c.2.1 c.2.2
  choose σ hσ using hex
  let g : X → {σ : RingAut K // σ * σ = 1} × Bool := fun c =>
    (⟨σ c, (hσ c).1⟩, !decide (c.1 = fieldAut n K (σ c)))
  have hg : Function.Injective g := by
    intro c c' h
    simp only [g, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨hs, hb⟩ := h
    apply Subtype.ext
    by_cases h1 : c.1 = fieldAut n K (σ c)
    · have h2 : c'.1 = fieldAut n K (σ c') := by
        by_contra h2
        simp [h1, h2] at hb
      rw [h1, h2, hs]
    · have h2 : c'.1 ≠ fieldAut n K (σ c') := by
        intro h2
        simp [h1, h2] at hb
      rcases (hσ c).2 with h3 | h3
      · exact absurd h3 h1
      rcases (hσ c').2 with h4 | h4
      · exact absurd h4 h2
      rw [h3, h4, hs]
  calc Nat.card X ≤ Nat.card ({σ : RingAut K // σ * σ = 1} × Bool) :=
        Nat.card_le_card_of_injective g hg
    _ = Nat.card {σ : RingAut K // σ * σ = 1} * 2 := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    _ ≤ 4 := by omega

theorem card_elemAbelian_outer_projectiveSL_le {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] (A : Subgroup (Outer (projectiveSL n K))) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  haveI := inndiag_normal (n := n) (K := K) hn
  exact (card_elemAbelian_outer_le (inndiag (n := n) (K := K)) compl inn_le_inndiag
    odd_relIndex_inn_inndiag (exists_mul_compl hn) (inndiag_inf_compl hn) A hA).trans
    (card_involutions_compl_le (by omega))

theorem card_elemAbelian_outer_le_four_of_psl {S : Type} [Group S] {m f : ℕ} (hm : 3 ≤ m)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : S ≃* StatedProj (StatedSL m K)) (A : Subgroup (Outer S)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let e' : S ≃* projectiveSL m K :=
    e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj m K).symm
  obtain ⟨ε⟩ : Nonempty (Outer S ≃* Outer (projectiveSL m K)) :=
    ⟨CFSG.ComponentClassification.OuterAutomorphisms.equivalence e'⟩
  have h1 := card_elemAbelian_outer_projectiveSL_le hm (A.map ε.toMonoidHom)
    (IsElemAbelian.map hA _)
  have h2 : Nat.card (A.map ε.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ε.injective
  rwa [h2] at h1

end CFSG.RankThree.GF2n.Stroth80
