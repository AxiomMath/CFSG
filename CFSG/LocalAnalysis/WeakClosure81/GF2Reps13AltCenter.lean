module

public import CFSG.Quasithin.H13.A5Triple

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Quasithin CFSG.Quasithin.H13.A5 Equiv
open scoped commutatorElement

section Center

variable {X : Type} [Group X] [Finite X]

theorem commutatorElement_ne_one_of_nine (hperf : commutator X = ⊤)
    (hZ3 : Nat.card (Subgroup.center X) = 3) (h81 : ¬ 81 ∣ Nat.card X) {x y : X}
    (hx3 : x ^ 3 ∈ Subgroup.center X) (hy3 : y ^ 3 ∈ Subgroup.center X)
    (hxy : ⁅x, y⁆ ∈ Subgroup.center X)
    (h9 : ∀ i j i' j' : Fin 3, (QuotientGroup.mk (x ^ (i : ℕ) * y ^ (j : ℕ)) :
      X ⧸ Subgroup.center X) = QuotientGroup.mk (x ^ (i' : ℕ) * y ^ (j' : ℕ)) →
        i = i' ∧ j = j') :
    ⁅x, y⁆ ≠ 1 := by
  intro hc
  have hxy' : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp hc
  have hZpow : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center X))
    rw [hZ3] at this
    have h := orderOf_dvd_iff_pow_eq_one.mp this
    exact congrArg Subtype.val h
  obtain ⟨⟨z₀, hz₀⟩, hz₀1'⟩ : ∃ z₀ : ↥(Subgroup.center X), z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card ↥(Subgroup.center X) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀1' (Subtype.ext h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz₀3 : orderOf z₀ = 3 := orderOf_eq_prime (hZpow z₀ hz₀) hz₀1
  have hcommA : ({x, y} ∪ (Subgroup.center X : Set X)).Pairwise Commute := by
    intro a ha c hc _
    rcases ha with ha | ha <;> rcases hc with hc | hc
    · rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
      · exact Commute.refl _
      · exact hxy'
      · exact hxy'.symm
      · exact Commute.refl _
    · exact (Subgroup.mem_center_iff.mp hc a)
    · exact (Subgroup.mem_center_iff.mp ha c).symm
    · exact (Subgroup.mem_center_iff.mp hc a)
  have hAc := Subgroup.isMulCommutative_closure hcommA
  obtain ⟨A, hA, hA9, hxA, hyA, hzA⟩ : ∃ A : Subgroup X, IsMulCommutative A ∧
      (∀ a ∈ A, a ^ 9 = 1) ∧ x ∈ A ∧ y ∈ A ∧ z₀ ∈ A := by
    have hx9 : x ^ 9 = 1 := by
      rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ hx3]
    have hy9 : y ^ 9 = 1 := by
      rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ hy3]
    refine ⟨Subgroup.closure ({x, y} ∪ (Subgroup.center X : Set X)), hAc, ?_,
      Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_insert x {y})),
      Subgroup.subset_closure
        (Set.mem_union_left _ (Set.mem_insert_of_mem x (Set.mem_singleton y))),
      Subgroup.subset_closure (Set.mem_union_right _ hz₀)⟩
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · rcases ha with rfl | rfl
        · exact hx9
        · exact hy9
      · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZpow _ ha, one_pow]
    | one => exact one_pow 9
    | mul a c ha hc iha ihc =>
      have hac : Commute a c := by
        have := hAc.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩
        exact congrArg Subtype.val this
      rw [hac.mul_pow, iha, ihc, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hAp : IsPGroup 3 A := fun a => ⟨2, Subtype.ext (by simpa using hA9 a a.2)⟩
  have hge : 27 ≤ Nat.card A := by
    have hinj := injective_27 hz₀ hz₀3 h9
    have hmemA : ∀ t : Fin 3 × Fin 3 × Fin 3,
        x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z₀ ^ (t.2.2 : ℕ) ∈ A := fun t =>
      A.mul_mem (A.mul_mem (A.pow_mem hxA _) (A.pow_mem hyA _)) (A.pow_mem hzA _)
    have h1 := Nat.card_le_card_of_injective
      (fun t => (⟨_, hmemA t⟩ : ↥A)) (fun t t' h => hinj (congrArg Subtype.val h))
    rw [Nat.card_eq_fintype_card (α := Fin 3 × Fin 3 × Fin 3)] at h1
    simpa using h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hdvd : 3 ^ m ∣ Nat.card X := by
    rw [← hm]
    exact Subgroup.card_subgroup_dvd_card A
  have hm3 : m = 3 := by
    have hm4 : m < 4 := by
      by_contra h
      exact h81 ((Nat.pow_dvd_pow 3 (by omega : 4 ≤ m)).trans hdvd)
    rw [hm] at hge
    interval_cases m <;> first | rfl | (norm_num at hge)
  have hidx : Nat.card X = 27 * A.index := by
    have h1 := A.card_mul_index
    rw [hm, hm3] at h1
    norm_num at h1
    omega
  have h3idx : ¬ 3 ∣ A.index := by
    rintro ⟨t, ht⟩
    exact h81 ⟨t, by rw [hidx, ht]; ring⟩
  apply false_of_transfer hperf A hA hz₀
  intro h
  exact h3idx (hz₀3 ▸ orderOf_dvd_iff_pow_eq_one.mpr h)

omit [Finite X] in
private theorem conj_mul_central {u : X} (hu : u ∈ Subgroup.center X) (w a : X) :
    w * (u * a) * w⁻¹ = u * (w * a * w⁻¹) := by
  have := Subgroup.mem_center_iff.mp hu w
  calc w * (u * a) * w⁻¹ = (w * u) * a * w⁻¹ := by group
    _ = (u * w) * a * w⁻¹ := by rw [this]
    _ = u * (w * a * w⁻¹) := by group

omit [Finite X] in
private theorem conj_zpow_eq {x₀ y₀ c : X} (hc : c ∈ Subgroup.center X)
    (h : y₀ * x₀ * y₀⁻¹ = c⁻¹ * x₀) (k : ℤ) :
    y₀ ^ k * x₀ * (y₀ ^ k)⁻¹ = c ^ (-k) * x₀ := by
  have hinv : y₀⁻¹ * x₀ * y₀ = c * x₀ := by
    have h1 : x₀ = y₀⁻¹ * (c⁻¹ * x₀) * y₀ := by rw [← h]; group
    have h2 : y₀⁻¹ * (c⁻¹ * x₀) * y₀ = c⁻¹ * (y₀⁻¹ * x₀ * y₀) := by
      simpa using conj_mul_central (Subgroup.inv_mem _ hc) y₀⁻¹ x₀
    calc y₀⁻¹ * x₀ * y₀ = c * (c⁻¹ * (y₀⁻¹ * x₀ * y₀)) := by group
      _ = c * x₀ := by rw [← h2, ← h1]
  induction k with
  | zero => simp
  | succ k ih =>
    calc y₀ ^ ((k : ℤ) + 1) * x₀ * (y₀ ^ ((k : ℤ) + 1))⁻¹
        = y₀ * (y₀ ^ (k : ℤ) * x₀ * (y₀ ^ (k : ℤ))⁻¹) * y₀⁻¹ := by group
      _ = y₀ * (c ^ (-(k : ℤ)) * x₀) * y₀⁻¹ := by rw [ih]
      _ = c ^ (-(k : ℤ)) * (y₀ * x₀ * y₀⁻¹) :=
          conj_mul_central (Subgroup.zpow_mem _ hc _) y₀ x₀
      _ = c ^ (-(k : ℤ)) * (c⁻¹ * x₀) := by rw [h]
      _ = c ^ (-((k : ℤ) + 1)) * x₀ := by group
  | pred k ih =>
    calc y₀ ^ (-(k : ℤ) - 1) * x₀ * (y₀ ^ (-(k : ℤ) - 1))⁻¹
        = y₀⁻¹ * (y₀ ^ (-(k : ℤ)) * x₀ * (y₀ ^ (-(k : ℤ)))⁻¹) * y₀ := by group
      _ = y₀⁻¹ * (c ^ (-(-(k : ℤ))) * x₀) * y₀ := by rw [ih]
      _ = c ^ (-(-(k : ℤ))) * (y₀⁻¹ * x₀ * y₀) := by
          simpa using conj_mul_central (Subgroup.zpow_mem _ hc (-(-(k : ℤ)))) y₀⁻¹ x₀
      _ = c ^ (-(-(k : ℤ))) * (c * x₀) := by rw [hinv]
      _ = c ^ (-(-(k : ℤ) - 1)) * x₀ := by group

end Center

section Aux

variable {X : Type} [Group X] [Finite X]

private theorem exists_pair_aux {Q : Type} [Group Q] (hperf : commutator X = ⊤)
    (hZ3 : Nat.card (Subgroup.center X) = 3) (h81 : ¬ 81 ∣ Nat.card X)
    (e : X ⧸ Subgroup.center X ≃* Q) (s r : Q) (hs : s ^ 3 = 1) (hr : r ^ 3 = 1)
    (hsr : s * r = r * s)
    (h9 : ∀ i j i' j' : Fin 3, s ^ (i : ℕ) * r ^ (j : ℕ) = s ^ (i' : ℕ) * r ^ (j' : ℕ) →
      i = i' ∧ j = j') :
    ∃ x y : X, e (QuotientGroup.mk x) = s ∧ e (QuotientGroup.mk y) = r ∧
      x ^ 3 ∈ Subgroup.center X ∧ y ^ 3 ∈ Subgroup.center X ∧
      ⁅x, y⁆ ∈ Subgroup.center X ∧ ⁅x, y⁆ ≠ 1 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm s)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm r)
  have hex : e (QuotientGroup.mk x) = s := by rw [hx, MulEquiv.apply_symm_apply]
  have hey : e (QuotientGroup.mk y) = r := by rw [hy, MulEquiv.apply_symm_apply]
  have hx3 : x ^ 3 ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    apply e.injective
    rw [map_pow, hex, map_one]
    exact hs
  have hy3 : y ^ 3 ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    apply e.injective
    rw [map_pow, hey, map_one]
    exact hr
  have hcomm : e (QuotientGroup.mk ⁅x, y⁆) =
      ⁅e (QuotientGroup.mk x), e (QuotientGroup.mk y)⁆ :=
    map_commutatorElement (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) x y
  have hxy : ⁅x, y⁆ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    apply e.injective
    rw [hcomm, hex, hey, map_one]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hsr
  have h9' : ∀ i j i' j' : Fin 3, (QuotientGroup.mk (x ^ (i : ℕ) * y ^ (j : ℕ)) :
      X ⧸ Subgroup.center X) = QuotientGroup.mk (x ^ (i' : ℕ) * y ^ (j' : ℕ)) →
        i = i' ∧ j = j' := fun i j i' j' h => by
    apply h9
    have h' := congrArg e h
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_pow, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_pow, hex, hey] at h'
    exact h'
  exact ⟨x, y, hex, hey, hx3, hy3, hxy,
    commutatorElement_ne_one_of_nine hperf hZ3 h81 hx3 hy3 hxy h9'⟩

omit [Finite X] in
private theorem exists_conj_aux {Q : Type} [Group Q] (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* Q) {x₀ y₀ x : X}
    (hcZ : ⁅x₀, y₀⁆ ∈ Subgroup.center X) (hc1 : ⁅x₀, y₀⁆ ≠ 1)
    (hconj : IsConj (e (QuotientGroup.mk x₀)) (e (QuotientGroup.mk x))) :
    ∃ g : X, g * x₀ * g⁻¹ = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm c)
  have hg' : e (QuotientGroup.mk g) = c := by rw [hg, MulEquiv.apply_symm_apply]
  have hmk : (QuotientGroup.mk (g * x₀ * g⁻¹) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk x := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hg']
    exact hc
  obtain ⟨u, hu, hwu⟩ : ∃ u ∈ Subgroup.center X, g * x₀ * g⁻¹ = x * u :=
    ⟨x⁻¹ * (g * x₀ * g⁻¹), QuotientGroup.eq.mp hmk.symm, by group⟩
  have hzc : (⟨u, hu⟩ : ↥(Subgroup.center X)) ∈
      Subgroup.zpowers (⟨⁅x₀, y₀⁆, hcZ⟩ : ↥(Subgroup.center X)) :=
    mem_zpowers_of_prime_card hZ3 (fun h => hc1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
  have hk' : ⁅x₀, y₀⁆ ^ k = u := by
    have := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_zpow] at this
  have h1 : y₀ * x₀ * y₀⁻¹ = ⁅x₀, y₀⁆⁻¹ * x₀ := by rw [commutatorElement_def]; group
  have hy := conj_zpow_eq hcZ h1 k
  refine ⟨g * y₀ ^ k, ?_⟩
  calc g * y₀ ^ k * x₀ * (g * y₀ ^ k)⁻¹
      = g * (y₀ ^ k * x₀ * (y₀ ^ k)⁻¹) * g⁻¹ := by group
    _ = g * (⁅x₀, y₀⁆ ^ (-k) * x₀) * g⁻¹ := by rw [hy]
    _ = ⁅x₀, y₀⁆ ^ (-k) * (g * x₀ * g⁻¹) :=
        conj_mul_central (Subgroup.zpow_mem _ hcZ _) g x₀
    _ = u⁻¹ * (x * u) := by rw [zpow_neg, hk', hwu]
    _ = x := by rw [Subgroup.mem_center_iff.mp hu x]; group

omit [Finite X] in
private theorem not_81_dvd_card {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) : ¬ 81 ∣ Nat.card X := by
  rcases hn with rfl | rfl <;>
  · have h1 := (Subgroup.center X).card_mul_index
    rw [hZ3, Subgroup.index, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin] at h1
    rw [← h1]
    decide

end Aux

section Center

variable {X : Type} [Group X] [Finite X]

theorem inv_center_of_not_inner_seven (hperf : commutator X = ⊤)
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)) (α : MulAut X)
    (hout : ∀ y : X, α ≠ MulAut.conj y) : ∀ z ∈ Subgroup.center X, α z = z⁻¹ := by
  have h81 := not_81_dvd_card (n := 7) (Or.inr rfl) hZ3 e
  have hZα : (Subgroup.center X).map (α : X →* X) = Subgroup.center X :=
    Subgroup.map_center_eq α
  let αb : (X ⧸ Subgroup.center X) ≃* (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) α hZα
  have hαb : ∀ x : X, αb (QuotientGroup.mk x) = QuotientGroup.mk (α x) := fun x =>
    QuotientGroup.congr_mk (Subgroup.center X) (Subgroup.center X) α hZα x
  let γ : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e αb
  have hγ : ∀ u : X ⧸ Subgroup.center X, γ (e u) = e (αb u) := fun u => by
    show e (αb (e.symm (e u))) = e (αb u)
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨σ, hσ⟩ :=
    _root_.CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
      (Or.inr le_rfl) γ
  have hασ : ∀ x : X, ((e (QuotientGroup.mk (α x)) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) = σ * ((e (QuotientGroup.mk x) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) * σ⁻¹ := fun x => by
    rw [← hαb, ← hγ]
    exact hσ _
  by_cases hsg : Perm.sign σ = 1
  ·
    exfalso
    obtain ⟨y, hy⟩ :=
      QuotientGroup.mk_surjective (e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hsg⟩)
    apply hout y
    refine eq_conj_of_mk_eq hperf α y fun x => ?_
    apply e.injective
    apply Subtype.ext
    rw [hασ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, map_mul,
      map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  ·
    have hsgn : Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left hsg
    have hτ : σ⁻¹ * swap 0 1 ∈ alternatingGroup (Fin 7) := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hsgn, Perm.sign_swap (by decide)]
      decide
    obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ⁻¹ * swap 0 1, hτ⟩)
    let β : MulAut X := α * MulAut.conj t
    have hβz : ∀ z ∈ Subgroup.center X, β z = α z := fun z hz => by
      show α (t * z * t⁻¹) = α z
      rw [show t * z * t⁻¹ = z by rw [Subgroup.mem_center_iff.mp hz t]; group]
    have hββ : ∀ x : X, ((e (QuotientGroup.mk (β x)) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) = swap 0 1 * ((e (QuotientGroup.mk x) : alternatingGroup (Fin 7)) :
          Perm (Fin 7)) * (swap 0 1)⁻¹ := fun x => by
      show ((e (QuotientGroup.mk (α (t * x * t⁻¹))) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) = _
      rw [hασ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht, map_mul,
        map_mul, map_inv, MulEquiv.apply_symm_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    obtain ⟨x, y, hex, hey, hx3, hy3, hcZ, hc1⟩ := exists_pair_aux hperf hZ3 h81 e
      (⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 7))
      ⟨swap 3 4 * swap 3 5, Perm.mem_alternatingGroup.mpr (by decide)⟩ (by decide)
      (by decide) (by decide) (by decide)
    have hβx : (QuotientGroup.mk (β x) : X ⧸ Subgroup.center X) = QuotientGroup.mk x⁻¹ := by
      apply e.injective
      apply Subtype.ext
      rw [hββ, QuotientGroup.mk_inv, map_inv, hex]
      decide
    have hβy : (QuotientGroup.mk (β y) : X ⧸ Subgroup.center X) = QuotientGroup.mk y := by
      apply e.injective
      apply Subtype.ext
      rw [hββ, hey]
      decide
    have hz₁ : x * β x ∈ Subgroup.center X := by
      have := QuotientGroup.eq.mp hβx.symm
      rwa [inv_inv] at this
    have hz₂ : y⁻¹ * β y ∈ Subgroup.center X := QuotientGroup.eq.mp hβy.symm
    have hβc : β ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
      rw [map_commutatorElement]
      have e1 : β x = x⁻¹ * (x * β x) := by group
      have e2 : β y = y * (y⁻¹ * β y) := by group
      rw [e1, e2, commutator_mul_central_left hz₁, commutator_mul_central_right hz₂,
        commutator_inv_left_of_central hcZ]
    intro z hz
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hzc : (⟨z, hz⟩ : ↥(Subgroup.center X)) ∈
        Subgroup.zpowers (⟨⁅x, y⁆, hcZ⟩ : ↥(Subgroup.center X)) :=
      mem_zpowers_of_prime_card hZ3 (fun h => hc1 (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
    have hk' : ⁅x, y⁆ ^ k = z := by
      have := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_zpow] at this
    rw [← hβz z hz, ← hk', map_zpow, hβc, inv_zpow]

end Center

section ThreeCycle

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem exists_conj_of_isThreeCycle (hn : n = 6 ∨ n = 7) (hperf : commutator X = ⊤)
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) {x x' : X}
    (hx : ((e x : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle)
    (hx' : ((e x' : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle) :
    ∃ g : X, g * x * g⁻¹ = x' := by
  have h81 := not_81_dvd_card hn hZ3 e
  have h5 : 5 ≤ Nat.card (Fin n) := by rcases hn with rfl | rfl <;> simp
  have key : ∀ s r : alternatingGroup (Fin n), s ^ 3 = 1 → r ^ 3 = 1 → s * r = r * s →
      (∀ i j i' j' : Fin 3, s ^ (i : ℕ) * r ^ (j : ℕ) = s ^ (i' : ℕ) * r ^ (j' : ℕ) →
        i = i' ∧ j = j') → ((s : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle →
      ∃ g : X, g * x * g⁻¹ = x' := by
    intro s r hs hr hsr h9 hs3
    obtain ⟨x₀, y₀, hex, -, -, -, hcZ, hc1⟩ := exists_pair_aux hperf hZ3 h81 e s r hs hr hsr h9
    obtain ⟨g₁, h₁⟩ := exists_conj_aux hZ3 e hcZ hc1 (x := x)
      (by rw [hex]; exact alternatingGroup.isThreeCycle_isConj h5 hs3 hx)
    obtain ⟨g₂, h₂⟩ := exists_conj_aux hZ3 e hcZ hc1 (x := x')
      (by rw [hex]; exact alternatingGroup.isThreeCycle_isConj h5 hs3 hx')
    exact ⟨g₂ * g₁⁻¹, by rw [← h₂, ← h₁]; group⟩
  rcases hn with rfl | rfl
  · exact key ⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.mpr (by decide)⟩
      ⟨swap 3 4 * swap 3 5, Perm.mem_alternatingGroup.mpr (by decide)⟩ (by decide)
      (by decide) (by decide) (by decide)
      (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))
  · exact key ⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.mpr (by decide)⟩
      ⟨swap 3 4 * swap 3 5, Perm.mem_alternatingGroup.mpr (by decide)⟩ (by decide)
      (by decide) (by decide) (by decide)
      (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))

end ThreeCycle

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
