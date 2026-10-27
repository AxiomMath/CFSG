module

public import CFSG.Walter.ReeOrder.WardLocal.Hall2

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

section General

variable {G : Type} [Group G] [Fintype G]

theorem card_conj_image_mul_le (X : Subgroup G) :
    ((Finset.univ ×ˢ ((Finset.univ.filter (· ∈ X)).erase 1)).image
        (fun p : G × G => p.1 * p.2 * p.1⁻¹)).card *
      Nat.card (Subgroup.normalizer (X : Set G)) ≤ Nat.card G * (Nat.card X - 1) := by
  set s : Finset (G × G) := Finset.univ ×ˢ ((Finset.univ.filter (· ∈ X)).erase 1) with hs
  have hscard : s.card = Nat.card G * (Nat.card X - 1) := by
    rw [hs, Finset.card_product, Finset.card_univ (α := G), Finset.card_erase_of_mem (by simp),
      card_filter_eq, ← Nat.card_eq_fintype_card (α := G)]
  rw [← hscard, mul_comm]
  apply Finset.mul_card_image_le_card
  intro b hb
  obtain ⟨⟨g, x⟩, hgx, rfl⟩ := Finset.mem_image.mp hb
  simp only [hs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_erase,
    Finset.mem_filter] at hgx
  obtain ⟨hx1, hxX⟩ := hgx
  rw [← card_filter_eq]
  refine Finset.card_le_card_of_injOn (fun n => (g * n, n⁻¹ * x * n)) ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hn
    simp only [hs, Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_erase, Finset.mem_filter, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h
      apply hx1
      have := congrArg (fun t => n * t * n⁻¹) h
      simpa [mul_assoc] using this
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hxX
      simpa using this
    · group
  · intro n _ n' _ h
    simp only [Prod.mk.injEq] at h
    exact mul_left_cancel h.1

theorem sum_normSq_eq (x : G) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, Complex.normSq (χ x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h := sum_irr_mul_conj x x
  simp only [IsConj.refl, ↓reduceIte] at h
  have := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] at this
  exact this

omit [Fintype G] in
theorem card_mul_relIndex [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← (H.subgroupOf K).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

end General

namespace WardL

variable {L : Type} [Group L] [Fintype L] {q : ℕ} (W : WardL L q (-1))

theorem pow_J'_mul {ρ : L} (hρ : ρ ∈ W.So) : (W.J' * ρ) ^ Nat.card W.So = W.J' := by
  have hc : Commute W.J' ρ := (W.So_comm ρ hρ).symm
  have hodd : Odd (Nat.card W.So) := by
    have h := W.So_card
    have hq := W.q_mod
    have : (Nat.card W.So : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)
  have h2 : W.J' ^ 2 = 1 := by rw [← W.orderOf_J', pow_orderOf_eq_one]
  obtain ⟨t, ht⟩ := hodd
  rw [hc.mul_pow, ht, pow_succ, pow_mul, h2, one_pow, one_mul,
    show ρ ^ (2 * t + 1) = ρ ^ Nat.card W.So by rw [ht]]
  have : ρ ^ Nat.card W.So = 1 := by
    have h' := congrArg Subtype.val (pow_card_eq_one' (G := W.So) (x := ⟨ρ, hρ⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
  rw [this, mul_one]

include W in
theorem four_mul_card_even :
    Nat.card L ≤ 4 * (Finset.univ.filter fun y : L => Even (orderOf y)).card := by
  set s := (Finset.univ : Finset L) ×ˢ (Finset.univ.filter (· ∈ W.So)) with hs
  set f : L × L → L := fun p => p.1 * (W.J' * p.2) * p.1⁻¹ with hf
  have hsub : s.image f ⊆ Finset.univ.filter fun y : L => Even (orderOf y) := by
    intro y hy
    obtain ⟨⟨g, ρ⟩, hgρ, rfl⟩ := Finset.mem_image.mp hy
    simp only [hs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hgρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf]
    rw [show g * (W.J' * ρ) * g⁻¹ = MulAut.conj g (W.J' * ρ) from rfl, MulEquiv.orderOf_eq]
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hJ := pow_J'_mul W hgρ
    have hdvd : orderOf W.J' ∣ orderOf (W.J' * ρ) := by
      have := orderOf_pow_dvd (x := W.J' * ρ) (Nat.card W.So)
      rwa [hJ] at this
    rw [W.orderOf_J'] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hfib : ∀ b ∈ s.image f, (s.filter fun p => f p = b).card ≤ q + 1 := by
    intro b hb
    obtain ⟨⟨g₀, ρ₀⟩, hgρ₀, rfl⟩ := Finset.mem_image.mp hb
    have hcJ : (Nat.card (Subgroup.centralizer ({W.J'} : Set L)) : ℤ) = q + 1 := by
      have := W.card_centralizer_J'; linarith
    have hcJ' : Nat.card (Subgroup.centralizer ({W.J'} : Set L)) = q + 1 := by
      exact_mod_cast hcJ
    rw [← hcJ', ← card_filter_eq]
    refine Finset.card_le_card_of_injOn (fun p => g₀⁻¹ * p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, hs, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨hρ, hfp⟩ := hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      simp only [hs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hgρ₀
      have h1 := congrArg (· ^ Nat.card W.So) hfp
      simp only [hf] at h1
      rw [show p.1 * (W.J' * p.2) * p.1⁻¹ = MulAut.conj p.1 (W.J' * p.2) from rfl,
        show g₀ * (W.J' * ρ₀) * g₀⁻¹ = MulAut.conj g₀ (W.J' * ρ₀) from rfl, ← map_pow,
        ← map_pow, pow_J'_mul W hρ, pow_J'_mul W hgρ₀, MulAut.conj_apply,
        MulAut.conj_apply] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g₀⁻¹ * p.1 * W.J' = g₀⁻¹ * (p.1 * W.J' * p.1⁻¹) * p.1 := by group
        _ = g₀⁻¹ * (g₀ * W.J' * g₀⁻¹) * p.1 := by rw [h1]
        _ = W.J' * (g₀⁻¹ * p.1) := by group
    · intro p hp p' hp' h
      simp only [Finset.coe_filter, hs, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_filter, Set.mem_ofPred_eq] at hp hp'
      have h1 : p.1 = p'.1 := mul_left_cancel h
      have h2 : f p = f p' := hp.2.trans hp'.2.symm
      simp only [hf, h1] at h2
      have h3 : W.J' * p.2 = W.J' * p'.2 := by
        have := congrArg (fun t => p'.1⁻¹ * t * p'.1) h2
        simpa [mul_assoc] using this
      exact Prod.ext h1 (mul_left_cancel h3)
  have hle := Finset.card_le_mul_card_image s (q + 1) hfib
  have hscard : s.card = Nat.card L * Nat.card W.So := by
    rw [hs, Finset.card_product, Finset.card_univ (α := L), card_filter_eq,
      ← Nat.card_eq_fintype_card (α := L)]
  have hSo : 4 * Nat.card W.So = q + 1 := by have := W.So_card; omega
  have hcard := Finset.card_le_card hsub
  rw [hscard, ← hSo] at hle
  have hpos : 0 < Nat.card W.So := Nat.card_pos
  have : Nat.card L * Nat.card W.So ≤ (4 * (Finset.univ.filter fun y : L =>
      Even (orderOf y)).card) * Nat.card W.So := by
    calc Nat.card L * Nat.card W.So ≤ 4 * Nat.card W.So * (s.image f).card := hle
      _ ≤ 4 * Nat.card W.So * (Finset.univ.filter fun y : L => Even (orderOf y)).card :=
          Nat.mul_le_mul_left _ hcard
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

include W in
theorem four_mul_card_odd :
    4 * (Finset.univ.filter fun y : L => Odd (orderOf y)).card ≤ 3 * Nat.card L := by
  have h := four_mul_card_even W
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset L))
    (fun y : L => Even (orderOf y))
  have hodd : (Finset.univ.filter fun y : L => Odd (orderOf y)) =
      Finset.univ.filter fun y : L => ¬ Even (orderOf y) := by
    ext y; simp [Nat.not_even_iff_odd]
  rw [hodd]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsplit
  omega

omit [Fintype L] in
theorem comm_of_cyclic {H : Subgroup L} (hH : IsCyclic H) {a b : L} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a := by
  obtain ⟨g, hg⟩ := hH.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h := congrArg Subtype.val ((Commute.zpow_zpow_self g i j).eq)
  simp only [Subgroup.coe_mul] at h
  rwa [hi, hj] at h

include W in
theorem isConj_inv_Ro {ρ : L} (hρ : ρ ∈ W.Ro) (hρ1 : ρ ≠ 1) : IsConj ρ ρ⁻¹ := by
  by_contra hnc
  have h := sum_irr_mul_conj ρ ρ⁻¹
  simp only [hnc, ite_false] at h
  have hreal : ∀ θ ∈ (irreducibles_finite L).toFinset, starRingEnd ℂ (θ ρ) = θ ρ := by
    intro θ hθ
    rw [Set.Finite.mem_toFinset] at hθ
    obtain ⟨h2, h3, h4, hS⟩ := W.val_Ro ρ hρ hρ1
    rcases (W.mem_irr_iff θ).mp hθ with rfl | rfl | rfl | rfl | hR | hS'
    · simp
    · rw [h2]; simp
    · rw [h3]; simp
    · rw [h4]; simp
    · have := congrFun (W.conj_R θ hR) ρ; simpa using this
    · rw [hS θ hS']; simp
  have h2 : ∀ θ ∈ (irreducibles_finite L).toFinset,
      θ ρ * starRingEnd ℂ (θ ρ⁻¹) = (Complex.normSq (θ ρ) : ℂ) := by
    intro θ hθ
    have hθ' := hθ
    rw [Set.Finite.mem_toFinset] at hθ'
    rw [inv_eq_conj hθ' ρ, RCLike.conj_conj, ← Complex.mul_conj, hreal θ hθ]
  rw [Finset.sum_congr rfl h2] at h
  have h' : ∑ θ ∈ (irreducibles_finite L).toFinset, Complex.normSq (θ ρ) = 0 := by
    exact_mod_cast h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => Complex.normSq_nonneg (θ ρ))).mp h' 1
    (by rw [Set.Finite.mem_toFinset]; exact W.one_mem)
  simp at h1

include W in
theorem centralizer_So_le {s : L} (hs : s ∈ W.So) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set L) ≤ Subgroup.centralizer ({W.J'} : Set L) := by
  have hterm : ∀ θ ∈ (irreducibles_finite L).toFinset,
      Complex.normSq (θ s) = Complex.normSq (θ (W.J' * s)) := by
    intro θ hθ
    rw [Set.Finite.mem_toFinset] at hθ
    obtain ⟨h2, h3, h4, hR⟩ := W.val_So s hs hs1
    obtain ⟨h2', h3', h4', hR'⟩ := W.val_J'So s hs
    rcases (W.mem_irr_iff θ).mp hθ with rfl | rfl | rfl | rfl | hθR | hθS
    · simp
    · rw [h2, h2']; simp
    · rw [h3, h3']; simp
    · rw [h4, h4']
    · rw [hR θ hθR, hR' θ hθR]
    · have hs1' : (⟨s, hs⟩ : W.So) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
      have e1 := W.valS_So θ hθS ⟨s, hs⟩ hs1'
      have e2 := W.valS_J'So θ hθS ⟨s, hs⟩
      simp only at e1 e2
      rw [e1, e2, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
      have : Complex.normSq ((W.eps θ : ℤ) : ℂ) = 1 := by
        rcases W.eps_eq θ hθS with he | he <;> rw [he] <;> simp
      rw [this, mul_one]
  have hcard : Nat.card (Subgroup.centralizer ({s} : Set L)) =
      Nat.card (Subgroup.centralizer ({W.J' * s} : Set L)) := by
    have h1 := sum_normSq_eq s
    have h2 := sum_normSq_eq (W.J' * s)
    rw [Finset.sum_congr rfl hterm, h2] at h1
    exact_mod_cast h1.symm
  have hpow : (W.J' * s) ^ (Nat.card W.So + 1) = s := by
    rw [pow_succ, pow_J'_mul W hs, ← mul_assoc, ← sq, ← W.orderOf_J', pow_orderOf_eq_one,
      one_mul]
  have hle : Subgroup.centralizer ({W.J' * s} : Set L) ≤ Subgroup.centralizer ({s} : Set L) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hpow]
    exact (Commute.pow_right hy _).eq
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  intro y hy
  rw [← heq] at hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  rw [← pow_J'_mul W hs]
  exact (Commute.pow_right hy _).eq

include W in
theorem conj_mem_So {y ρ : L} (hy : y * W.J' = W.J' * y) (hρ : ρ ∈ W.So) :
    y * ρ * y⁻¹ ∈ W.So := by
  apply W.centralizer_J'
  · have hρJ := W.So_comm ρ hρ
    have hy' : y⁻¹ * W.J' = W.J' * y⁻¹ := by
      calc y⁻¹ * W.J' = y⁻¹ * (W.J' * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * W.J') * y⁻¹ := by rw [hy]
        _ = W.J' * y⁻¹ := by group
    calc y * ρ * y⁻¹ * W.J' = y * ρ * (W.J' * y⁻¹) := by rw [mul_assoc, hy']
      _ = y * (ρ * W.J') * y⁻¹ := by group
      _ = y * (W.J' * ρ) * y⁻¹ := by rw [hρJ]
      _ = (y * W.J') * ρ * y⁻¹ := by group
      _ = W.J' * (y * ρ * y⁻¹) := by rw [hy]; group
  · rw [show y * ρ * y⁻¹ = MulAut.conj y ρ from rfl, MulEquiv.orderOf_eq]
    have hodd : Odd (Nat.card W.So) := by
      have h := W.So_card
      have hq := W.q_mod
      have : (Nat.card W.So : ℤ) % 2 = 1 := by omega
      exact Nat.odd_iff.mpr (by exact_mod_cast this)
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hρ)

end WardL

theorem card_cls {G : Type} [Group G] [Fintype G] (x : G) :
    (cls x).card = Nat.card (ConjClasses.mk x).carrier := by
  have : (ConjClasses.mk x).carrier = ↑(cls x) := by
    ext g
    simp [cls, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [CharP K 3] in
include S in
theorem not_four_dvd (x : G) : ¬ 4 ∣ orderOf x := by
  intro h4
  have hyo : orderOf (x ^ (orderOf x / 4)) = 4 := by
    rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) h4) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h4), Nat.div_div_self h4 (orderOf_pos x).ne']
  set y := x ^ (orderOf x / 4) with hy
  have hy2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow' y (by norm_num), hyo]; norm_num
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.involution_conj _ hy2)
  have hz2 : c * y * c⁻¹ * (c * y * c⁻¹) = S.J := by rw [← hc, sq]; group
  have hzJ : c * y * c⁻¹ * S.J = S.J * (c * y * c⁻¹) := by rw [← hz2]; group
  obtain ⟨w, hw | hw⟩ := S.centralizer _ hzJ
  · exact S.J_not_mem (w * w) (by rw [map_mul, ← hw, hz2])
  · have : S.J * S.κ w * (S.J * S.κ w) = S.κ w * S.κ w := by
      calc S.J * S.κ w * (S.J * S.κ w) = S.J * (S.κ w * S.J) * S.κ w := by group
        _ = S.J * (S.J * S.κ w) * S.κ w := by rw [S.κ_comm w]
        _ = (S.J * S.J) * S.κ w * S.κ w := by group
        _ = S.κ w * S.κ w := by rw [S.J_mul, one_mul]
    exact S.J_not_mem (w * w) (by rw [map_mul, ← this, ← hw, hz2])

omit [CharP K 3] in
include S in
theorem even_decomp {x : G} (hx : Even (orderOf x)) :
    ∃ t u : G, t * u = x ∧ orderOf t = 2 ∧ u * t = t * u ∧ Odd (orderOf u) := by
  obtain ⟨o', ho'⟩ := hx
  have hodd : Odd o' := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨j, hj⟩ := h
    exact not_four_dvd (S := S) x ⟨j, by omega⟩
  have hpos : 0 < o' := by have := orderOf_pos x; omega
  refine ⟨x ^ o', x ^ (o' + 1), ?_, ?_, ?_, ?_⟩
  · rw [← pow_add, show o' + (o' + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  · rw [orderOf_pow_of_dvd hpos.ne' ⟨2, by omega⟩, ho', ← two_mul, Nat.mul_div_cancel _ hpos]
  · exact (Commute.pow_pow_self x (o' + 1) o').eq
  · apply Odd.of_dvd_nat hodd
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨j, hj⟩ := hodd
    rw [← pow_mul, show (o' + 1) * o' = orderOf x * (j + 1) by rw [hj] at ho' ⊢; nlinarith,
      pow_mul, pow_orderOf_eq_one, one_pow]

omit [CharP K 3] in
theorem card_odd_centralizer_J :
    (Finset.univ.filter fun u : G => u * S.J = S.J * u ∧ Odd (orderOf u)).card =
      (Finset.univ.filter fun y : PSL(2, K) => Odd (orderOf y)).card := by
  rw [← Finset.card_image_of_injective _ S.κ_inj]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hu, hodd⟩
    obtain ⟨y, rfl⟩ := S.odd_mem_κ hu hodd
    exact ⟨y, by rwa [S.orderOf_κ] at hodd, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨S.κ_comm y, by rwa [S.orderOf_κ]⟩

omit [CharP K 3] in
theorem card_odd_centralizer_conj {t c : G} (hc : c * t * c⁻¹ = S.J) :
    (Finset.univ.filter fun u : G => u * t = t * u ∧ Odd (orderOf u)).card =
      (Finset.univ.filter fun u : G => u * S.J = S.J * u ∧ Odd (orderOf u)).card := by
  refine Finset.card_nbij' (fun u => c * u * c⁻¹) (fun v => c⁻¹ * v * c) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    constructor
    · rw [← hc]
      calc c * u * c⁻¹ * (c * t * c⁻¹) = c * (u * t) * c⁻¹ := by group
        _ = c * (t * u) * c⁻¹ := by rw [hu.1]
        _ = c * t * c⁻¹ * (c * u * c⁻¹) := by group
    · rw [show c * u * c⁻¹ = MulAut.conj c u from rfl, MulEquiv.orderOf_eq]
      exact hu.2
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have ht : t = c⁻¹ * S.J * c := by rw [← hc]; group
    constructor
    · rw [ht]
      calc c⁻¹ * v * c * (c⁻¹ * S.J * c) = c⁻¹ * (v * S.J) * c := by group
        _ = c⁻¹ * (S.J * v) * c := by rw [hv.1]
        _ = c⁻¹ * S.J * c * (c⁻¹ * v * c) := by group
    · rw [show c⁻¹ * v * c = MulAut.conj c⁻¹ v by simp,
        MulEquiv.orderOf_eq]
      exact hv.2
  · intro u _; simp only; group
  · intro v _; simp only; group

omit [CharP K 3] in
include S hq in
theorem card_even_le :
    8 * (Finset.univ.filter fun x : G => Even (orderOf x)).card ≤ 3 * Nat.card G := by
  set F : G → Finset G := fun t =>
    (Finset.univ.filter fun u : G => u * t = t * u ∧ Odd (orderOf u)).image (t * ·) with hF
  have hsub : (Finset.univ.filter fun x : G => Even (orderOf x)) ⊆ (cls S.J).biUnion F := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨t, u, rfl, ht, hut, hu⟩ := even_decomp (S := S) hx
    refine Finset.mem_biUnion.mpr ⟨t, mem_cls.mpr (S.involution_conj t ht), ?_⟩
    exact Finset.mem_image.mpr ⟨u, by simp [hut, hu], rfl⟩
  have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hterm : ∀ t ∈ cls S.J, (F t).card ≤
      (Finset.univ.filter fun y : PSL(2, K) => Odd (orderOf y)).card := by
    intro t ht
    obtain ⟨c, hc⟩ := isConj_iff.mp (mem_cls.mp ht)
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [card_odd_centralizer_conj hc, card_odd_centralizer_J]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, smul_eq_mul] at hsum
  have hL := WardL.four_mul_card_odd S.W
  have hcls := card_conjClass_mul_card_centralizer S.J
  rw [← card_cls] at hcls
  have hCJ := S.card_C
  have hWc := S.W.card
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hCJ' : Nat.card (Subgroup.centralizer ({S.J} : Set G)) = 2 * Nat.card PSL(2, K) := by
    have h : ((Nat.card (Subgroup.centralizer ({S.J} : Set G)) : ℕ) : ℂ) =
        ((2 * Nat.card PSL(2, K) : ℕ) : ℂ) := by
      rw [hCJ, hWc]; push_cast [Nat.one_le_pow 2 q (by omega)]; ring
    exact_mod_cast h
  rw [hCJ'] at hcls
  calc 8 * (Finset.univ.filter fun x : G => Even (orderOf x)).card
      ≤ 8 * ((cls S.J).card * (Finset.univ.filter fun y : PSL(2, K) => Odd (orderOf y)).card) :=
        Nat.mul_le_mul_left _ (hle.trans hsum)
    _ = 2 * (cls S.J).card * (4 * (Finset.univ.filter fun y : PSL(2, K) =>
        Odd (orderOf y)).card) := by ring
    _ ≤ 2 * (cls S.J).card * (3 * Nat.card PSL(2, K)) := Nat.mul_le_mul_left _ hL
    _ = 3 * ((cls S.J).card * (2 * Nat.card PSL(2, K))) := by ring
    _ = 3 * Nat.card G := by rw [hcls]

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_three_le :
    (Finset.univ.filter fun x : G => x ≠ 1 ∧ ∃ i : ℕ, orderOf x = 3 ^ i).card ≤
      (q ^ 3 + 1) * (q ^ 3 - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hsub : (Finset.univ.filter fun x : G => x ≠ 1 ∧ ∃ i : ℕ, orderOf x = 3 ^ i) ⊆
      (Finset.univ : Finset (Sylow 3 G)).biUnion
        (fun Q => (Finset.univ.filter (· ∈ (Q : Subgroup G))).erase 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hx1, i, hi⟩ := hx
    have hp : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := i)
      (by rw [Nat.card_zpowers, hi])
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    exact Finset.mem_biUnion.mpr ⟨Q, Finset.mem_univ _,
      Finset.mem_erase.mpr ⟨hx1, by simp [hQ (Subgroup.mem_zpowers x)]⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hterm : ∀ Q ∈ (Finset.univ : Finset (Sylow 3 G)),
      ((Finset.univ.filter (· ∈ (Q : Subgroup G))).erase 1).card = q ^ 3 - 1 := by
    intro Q _
    rw [Finset.card_erase_of_mem (by simp), card_filter_eq, card_sylow3 hq hG Q]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hN := card_normalizer hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c
  have hidx := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [hN, hG] at hidx
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hpos : 0 < q ^ 3 * (q - 1) := by
    have : 2 ≤ q := by rw [hq]; exact le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
    have : 0 < q - 1 := by omega
    positivity
  have hI : (Subgroup.normalizer (P : Set G)).index = q ^ 3 + 1 := by
    have : q ^ 3 * (q - 1) * (Subgroup.normalizer (P : Set G)).index =
        q ^ 3 * (q - 1) * (q ^ 3 + 1) := by rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hset : ((sylP hq hG hPc : Sylow 3 G) : Set G) = (P : Set G) :=
    congrArg (fun H : Subgroup G => (H : Set G)) (coe_sylP hq hG hPc)
  rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer (sylP hq hG hPc : Sylow 3 G),
    hset, hI]

omit [CharP K 3] in
theorem centralizer_Ro_eq {ρ : PSL(2, K)} (hρ : ρ ∈ S.W.Ro) (hρ1 : ρ ≠ 1) :
    Subgroup.centralizer ({ρ} : Set PSL(2, K)) = S.W.Ro := by
  have hle : S.W.Ro ≤ Subgroup.centralizer ({ρ} : Set PSL(2, K)) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (WardL.comm_of_cyclic S.W.Ro_cyclic hr hρ)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [S.W.Ro_centralizer ρ hρ hρ1])).symm

omit [CharP K 3] in
theorem odd_mem_κRo {ρ : PSL(2, K)} (hρ : ρ ∈ S.W.Ro) (hρ1 : ρ ≠ 1) {y : G}
    (hy : y * S.κ ρ = S.κ ρ * y) (hodd : Odd (orderOf y)) : y ∈ S.W.Ro.map S.κ := by
  have hJ : y * S.J = S.J * y := by
    apply S.normalizer rfl ρ hρ hρ1 y
    rw [show y⁻¹ * S.κ ρ * y = S.κ ρ by rw [mul_assoc, ← hy, ← mul_assoc, inv_mul_cancel,
      one_mul]]
    exact Subgroup.mem_zpowers _
  obtain ⟨w, rfl⟩ := S.odd_mem_κ hJ hodd
  refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
  rw [← centralizer_Ro_eq hρ hρ1, Subgroup.mem_centralizer_singleton_iff]
  apply S.κ_inj
  rw [map_mul, map_mul]
  exact hy

omit [CharP K 3] in
include hq in
theorem two_mul_le_card_normalizer_Ro :
    2 * (q - 1) ≤ Nat.card (Subgroup.normalizer ((S.W.Ro.map S.κ : Subgroup G) : Set G)) := by
  obtain ⟨⟨ρ₀, hρ₀⟩, hgen⟩ := S.W.Ro_cyclic.exists_generator
  have hRo := S.W.Ro_card
  have hq27 := S.q_ge
  have hRo' : 2 * Nat.card S.W.Ro = q - 1 := by omega
  have hρ₀1 : ρ₀ ≠ 1 := by
    rintro rfl
    have : ∀ x : S.W.Ro, x = 1 := fun x => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
      rw [← hi]; ext; simp
    have h1 : Nat.card S.W.Ro = 1 := by
      rw [Nat.card_eq_one_iff_unique]; exact ⟨⟨fun a b => (this a).trans (this b).symm⟩, ⟨1⟩⟩
    omega
  have hmem : ∀ ρ ∈ S.W.Ro, ∃ i : ℤ, ρ = ρ₀ ^ i := fun ρ hρ => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨ρ, hρ⟩)
    have h := congrArg Subtype.val hi
    rw [Subgroup.coe_zpow] at h
    exact ⟨i, h.symm⟩
  set N := Subgroup.normalizer ((S.W.Ro.map S.κ : Subgroup G) : Set G) with hN
  set C := Subgroup.centralizer ({S.κ ρ₀} : Set G) with hC
  have hCc : Nat.card C = q - 1 := by
    have h := S.card_centralizer_κR' hρ₀ hρ₀1
    have : ((Nat.card C : ℕ) : ℂ) = ((2 * Nat.card S.W.Ro : ℕ) : ℂ) := by rw [h]; push_cast; ring
    rw [← hRo']; exact_mod_cast this
  have hCN : C ≤ N := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨i, rfl⟩ := hmem ρ hρ
    have hc' : c * S.κ ρ₀ = S.κ ρ₀ * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [map_zpow, show c * S.κ ρ₀ ^ i * c⁻¹ = S.κ ρ₀ ^ i by
      rw [((Commute.zpow_right hc' i)).eq, mul_inv_cancel_right]]
    exact Subgroup.mem_map.mpr ⟨ρ₀ ^ i, Subgroup.zpow_mem _ hρ₀ i, by rw [map_zpow]⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (WardL.isConj_inv_Ro S.W hρ₀ hρ₀1)
  have hgN : S.κ g ∈ N := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨i, rfl⟩ := hmem ρ hρ
    refine Subgroup.mem_map.mpr ⟨g * ρ₀ ^ i * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [show g * ρ₀ ^ i * g⁻¹ = (g * ρ₀ * g⁻¹) ^ i by
      rw [show g * ρ₀ * g⁻¹ = MulAut.conj g ρ₀ from rfl, ← map_zpow]; rfl, hg]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ hρ₀) i
  have hgC : S.κ g ∉ C := by
    intro h
    have h' := Subgroup.mem_centralizer_singleton_iff.mp h
    have : ρ₀⁻¹ = ρ₀ := by
      rw [← hg]
      apply S.κ_inj
      rw [map_mul, map_mul, map_inv, h', mul_inv_cancel_right]
    have hsq : ρ₀ ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← this]; exact inv_mul_cancel ρ₀
    have hodd : Odd (orderOf ρ₀) := S.orderOf_Ro_odd hρ₀
    have h2 := orderOf_dvd_of_pow_eq_one hsq
    have h1 : orderOf ρ₀ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact hρ₀1 (orderOf_eq_one_iff.mp h1)
  have hlt : C < N := lt_of_le_of_ne hCN (fun h => hgC (h ▸ hgN))
  have hdvd := Subgroup.card_dvd_of_le hCN
  have hlt' := Subgroup.card_lt_of_lt hlt
  obtain ⟨t, ht⟩ := hdvd
  have ht2 : 2 ≤ t := by
    rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with h | h | h
    · rw [h, mul_zero] at ht; exact absurd ht Nat.card_pos.ne'
    · rw [h, mul_one] at ht; omega
    · exact h
  rw [ht, hCc]
  nlinarith

omit [CharP K 3] in
include hG in
theorem mem_image_Ro {x : G} (hodd : Odd (orderOf x)) {r : ℕ} (hr : r.Prime)
    (hrR : r ∣ Nat.card S.W.Ro) (hrx : r ∣ orderOf x) :
    x ∈ ((Finset.univ ×ˢ ((Finset.univ.filter (· ∈ S.W.Ro.map S.κ)).erase 1)).image
      (fun p : G × G => p.1 * p.2 * p.1⁻¹)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x ^ (orderOf x / r) := ⟨_, rfl⟩
  have hyo : orderOf y = r := by rw [hy]; exact exists_pow_orderOf_eq hr hrx
  obtain ⟨g, ρ, hρ, hρ1, hg⟩ := exists_conj_Ro hG hyo hrR
  have hxy : x * y = y * x := by rw [hy]; exact (Commute.self_pow x _).eq
  have hcomm : g⁻¹ * x * g * S.κ ρ = S.κ ρ * (g⁻¹ * x * g) := by
    rw [← hg]
    calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hxy]
      _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
  have hodd' : Odd (orderOf (g⁻¹ * x * g)) := by rw [orderOf_conj']; exact hodd
  have hmem := odd_mem_κRo hρ hρ1 hcomm hodd'
  have hx1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    have : x = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hrx
    exact hr.one_lt.ne' (Nat.dvd_one.mp hrx)
  refine Finset.mem_image.mpr ⟨(g, g⁻¹ * x * g), ?_, by
    show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_erase.mpr ⟨hx1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩⟩

omit [CharP K 3] in
include hq in
theorem So_arith :
    4 * Nat.card S.W.So = q + 1 ∧ Odd (Nat.card S.W.So) ∧ Nat.Coprime (Nat.card S.W.So) q ∧
      Nat.Coprime (Nat.card S.W.So) (q - 1) := by
  have h := S.W.So_card
  have hq8 := S.W.q_mod
  have h4 : 4 * Nat.card S.W.So = q + 1 := by omega
  have hodd : Odd (Nat.card S.W.So) := by
    have : (Nat.card S.W.So : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hcq : Nat.Coprime (q + 1) q := Nat.isCoprime_iff_coprime.mp ⟨1, -1, by push_cast; ring⟩
  have hdvd : Nat.card S.W.So ∣ q + 1 := ⟨4, by omega⟩
  refine ⟨h4, hodd, Nat.Coprime.coprime_dvd_left hdvd hcq, ?_⟩
  apply Nat.coprime_of_dvd
  intro r hr hr1 hr2
  have hr3 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub (hr1.trans hdvd) hr2
  rw [show q + 1 - (q - 1) = 2 by omega] at hr3
  have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr3
  subst this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hr1)

omit [CharP K 3] in
include hq hG in
theorem ppart_So (hm : q = 3 * m ^ 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrS : r ∣ Nat.card S.W.So) : r ^ (Nat.card G).factorization r ∣ Nat.card S.W.So := by
  obtain ⟨h4, hodd, hcq, hcq1⟩ := So_arith hq (S := S)
  obtain ⟨-, -, c3, -, -, -⟩ := hall_coprime hm (m_odd hq hm)
  rw [mul_comm (q + 1 - 3 * m), ← hall_mul hm] at c3
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hcard : Nat.card G = Nat.card S.W.So * (4 * q ^ 3 * (q - 1) * (q ^ 2 - q + 1)) := by
    rw [hG]
    have : (Nat.card S.W.So : ℤ) * 4 = q + 1 := by
      exact_mod_cast (by omega : Nat.card S.W.So * 4 = q + 1)
    zify [hq1, hq2]
    linear_combination (-((q : ℤ) ^ 3 * ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + 1))) * this
  rw [hcard]
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  refine ordProj_dvd_of_not_dvd Nat.card_pos ?_ ?_
  · have : 0 < q - 1 := by omega
    have : 0 < q ^ 2 - q + 1 := by omega
    positivity
  · intro h
    have hcop : ∀ n, Nat.Coprime (Nat.card S.W.So) n → ¬ r ∣ n := fun n hn hrn =>
      hr.one_lt.ne' (Nat.dvd_one.mp (by
        rw [← Nat.Coprime.gcd_eq_one hn]; exact Nat.dvd_gcd hrS hrn))
    have hdvd : Nat.card S.W.So ∣ q + 1 := ⟨4, by omega⟩
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · have h4' : r ∣ 2 ^ 2 := by norm_num; exact h
          exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4'))
        · exact hcop q hcq (hr.dvd_of_dvd_pow h)
      · exact hcop _ hcq1 h
    · exact hcop _ (Nat.Coprime.coprime_dvd_left hdvd c3.symm) h

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_κSo_le (hm : q = 3 * m ^ 2) {σ : PSL(2, K)} (hσ : σ ∈ S.W.So)
    (hσ1 : σ ≠ 1) :
    Subgroup.centralizer ({S.κ σ} : Set G) ≤ Subgroup.centralizer ({S.J} : Set G) := by
  set C := Subgroup.centralizer ({S.κ σ} : Set G) with hC
  set D := C ⊓ Subgroup.centralizer ({S.J} : Set G) with hD
  obtain ⟨hSo4, hSoodd, hSoq, hSoq1⟩ := So_arith hq (S := S)
  have hσo : orderOf σ ∣ Nat.card S.W.So := Subgroup.orderOf_dvd_natCard _ hσ
  have hσ_of : ∀ n : ℕ, Nat.Coprime (Nat.card S.W.So) n → orderOf σ ∣ n → False := by
    intro n hn hdvd
    have : orderOf σ = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hσo hn) hdvd
    exact hσ1 (orderOf_eq_one_iff.mp this)
  have hdvdq : Nat.card S.W.So ∣ q + 1 := ⟨4, by omega⟩
  obtain ⟨-, -, c3, -, -, -⟩ := hall_coprime hm (m_odd hq hm)
  have hcm : Nat.Coprime (Nat.card S.W.So) (q + 1 - 3 * m) :=
    Nat.Coprime.coprime_dvd_left hdvdq
      (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) c3.symm)
  have hcp : Nat.Coprime (Nat.card S.W.So) (q + 1 + 3 * m) :=
    Nat.Coprime.coprime_dvd_left hdvdq
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) c3.symm)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card C → r ≠ 2 → r ∣ Nat.card S.W.So := by
    intro r hr hrC hr2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) r hrC
    have hz' : orderOf (z : G) = r := by rw [Subgroup.orderOf_coe]; exact hz
    have hzσ : (z : G) * S.κ σ = S.κ σ * z := Subgroup.mem_centralizer_singleton_iff.mp z.2
    have hσz : S.κ σ ∈ Subgroup.centralizer ({(z : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzσ.symm
    have hσdvd : orderOf σ ∣ Nat.card (Subgroup.centralizer ({(z : G)} : Set G)) := by
      rw [← S.orderOf_κ]; exact Subgroup.orderOf_dvd_natCard _ hσz
    have hzodd : Odd (orderOf (z : G)) := by rw [hz']; exact hr.odd_of_ne_two hr2
    have hr3 : r ≠ 3 := by
      rintro rfl
      have hd := B.card_centralizer_dvd hq hG hzodd (by rw [hz'])
      exact hσ_of _ (Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hSoodd)
        (Nat.Coprime.pow_right 3 hSoq)) (hσdvd.trans hd)
    have hra : ¬ r ∣ q + 1 - 3 * m := fun hra => by
      obtain ⟨hc, -⟩ := B.centralizer_minus hq hK hG hP1P hPc hPn hN1c hm hzodd hr hra
        (by rw [hz'])
      rw [hc] at hσdvd
      exact hσ_of _ hcm hσdvd
    have hrb : ¬ r ∣ q + 1 + 3 * m := fun hrb => by
      obtain ⟨hc, -⟩ := B.centralizer_plus hq hK hG hP1P hPc hPn hN1c hm hzodd hr hrb
        (by rw [hz'])
      rw [hc] at hσdvd
      exact hσ_of _ hcp hσdvd
    have hrq1 : ¬ r ∣ q - 1 := by
      intro hrq
      have hRo := S.W.Ro_card
      have hRo' : q - 1 = 2 * Nat.card S.W.Ro := by omega
      have hrR : r ∣ Nat.card S.W.Ro := by
        rw [hRo'] at hrq
        exact (Nat.Coprime.dvd_of_dvd_mul_left
          ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) hrq)
      obtain ⟨g, ρ, hρ, hρ1, hg⟩ := exists_conj_Ro hG hz' hrR
      have hcR : Nat.card (Subgroup.centralizer ({S.κ ρ} : Set G)) = q - 1 := by
        have h := S.card_centralizer_κR' hρ hρ1
        have : ((Nat.card (Subgroup.centralizer ({S.κ ρ} : Set G)) : ℕ) : ℂ) =
            ((2 * Nat.card S.W.Ro : ℕ) : ℂ) := by rw [h]; push_cast; ring
        rw [hRo']; exact_mod_cast this
      have hmem : g⁻¹ * S.κ σ * g ∈ Subgroup.centralizer ({S.κ ρ} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
        calc g⁻¹ * S.κ σ * g * (g⁻¹ * z * g) = g⁻¹ * (S.κ σ * z) * g := by group
          _ = g⁻¹ * (z * S.κ σ) * g := by rw [hzσ]
          _ = g⁻¹ * z * g * (g⁻¹ * S.κ σ * g) := by group
      have h1 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [orderOf_conj', S.orderOf_κ, hcR] at h1
      exact hσ_of _ hSoq1 h1
    have hrG : r ∣ Nat.card G := hrC.trans (Subgroup.card_subgroup_dvd_card C)
    rw [card_G_hall hq hG hm] at hrG
    have hrq : ¬ r ∣ q := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow (hq ▸ h)))
    have hrq' : r ∣ q + 1 := by
      rcases (Nat.Prime.dvd_mul hr).mp hrG with h | h
      · exact absurd h hra
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
            · exact absurd (hr.dvd_of_dvd_pow h) hrq
            · exact absurd h hrq1
          · exact h
        · exact absurd h hrb
    rw [← hSo4] at hrq'
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right 2 ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
      (by rw [show 4 = 2 ^ 2 by norm_num] at hrq'; exact hrq'))
  have hSoD : Nat.card S.W.So ∣ Nat.card D := by
    have hle : S.W.So.map S.κ ≤ D := by
      rintro _ ⟨ρ, hρ, rfl⟩
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        Subgroup.mem_centralizer_singleton_iff.mpr (S.κ_comm ρ)⟩
      rw [← map_mul, ← map_mul, WardL.comm_of_cyclic S.W.So_cyclic hρ hσ]
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective S.κ_inj] at this
  have hJC : S.J ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (S.κ_comm σ).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJp : IsPGroup 2 (Subgroup.zpowers (⟨S.J, hJC⟩ : C)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, S.orderOf_J, pow_one])
  obtain ⟨T, hT⟩ := hJp.exists_le_sylow
  have hsq : ∀ u ∈ (T : Subgroup C), (u : G) * u = 1 := by
    intro u hu
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at hn
    have hn' : orderOf (u : G) = 2 ^ n := by rw [Subgroup.orderOf_coe]; exact hn
    have hn1 : n ≤ 1 := by
      by_contra h
      have h4 : 4 ∣ 2 ^ n := by
        rw [show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
      exact not_four_dvd (S := S) (u : G) (hn' ▸ h4)
    have : orderOf (u : G) ∣ 2 := by
      rw [hn']; exact Nat.pow_dvd_pow 2 hn1 |>.trans (by norm_num)
    rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp this
  have hJT : (⟨S.J, hJC⟩ : C) ∈ (T : Subgroup C) := hT (Subgroup.mem_zpowers _)
  have hTD : (T : Subgroup C) ≤ D.subgroupOf C := by
    intro t ht
    rw [Subgroup.mem_subgroupOf]
    refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have e1 := hsq t ht
    have e2 : S.J * S.J = 1 := S.J_mul
    have e4 := hsq _ ((T : Subgroup C).mul_mem hJT ht)
    simp only [Subgroup.coe_mul] at e4
    calc (t : G) * S.J = t * S.J * ((S.J * t) * (S.J * t)) := by rw [e4, mul_one]
      _ = t * (S.J * S.J) * t * (S.J * t) := by group
      _ = t * t * (S.J * t) := by rw [e2]; group
      _ = S.J * t := by rw [e1]; group
  have h2part : 2 ^ (Nat.card C).factorization 2 ∣ Nat.card D := by
    rw [← T.card_eq_multiplicity, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : D ≤ C)).toEquiv]
    exact Subgroup.card_dvd_of_le hTD
  have hdvd : Nat.card C ∣ Nat.card D := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
    intro r
    by_cases hr : r.Prime
    · by_cases hr2 : r = 2
      · subst hr2
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2part
      · by_cases hrC : r ∣ Nat.card C
        · have hrSo := hprime r hr hrC hr2
          have h1 : (Nat.card C).factorization r ≤ (Nat.card G).factorization r :=
            (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
              (Subgroup.card_subgroup_dvd_card C) r
          have h2 : (Nat.card G).factorization r ≤ (Nat.card S.W.So).factorization r :=
            (Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').mp
              (ppart_So hq hG hm hr hr2 hrSo)
          have h3 : (Nat.card S.W.So).factorization r ≤ (Nat.card D).factorization r :=
            (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hSoD r
          omega
        · rw [Nat.factorization_eq_zero_of_not_dvd hrC]; exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hr]; exact Nat.zero_le _
  have heq : D = C := Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos hdvd)
  intro x hx
  have hxD : x ∈ D := heq ▸ hx
  exact hxD.2

include B hq hK hG hP1P hPc hPn hN1c in
theorem odd_mem_κSo (hm : q = 3 * m ^ 2) {σ : PSL(2, K)} (hσ : σ ∈ S.W.So) (hσ1 : σ ≠ 1)
    {y : G} (hy : y * S.κ σ = S.κ σ * y) (hodd : Odd (orderOf y)) : y ∈ S.W.So.map S.κ := by
  have hyC : y ∈ Subgroup.centralizer ({S.κ σ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hJ := Subgroup.mem_centralizer_singleton_iff.mp
    (B.centralizer_κSo_le hq hK hG hP1P hPc hPn hN1c hm hσ hσ1 hyC)
  obtain ⟨w, rfl⟩ := S.odd_mem_κ hJ hodd
  refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
  have hwσ : w ∈ Subgroup.centralizer ({σ} : Set PSL(2, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply S.κ_inj
    rw [map_mul, map_mul]; exact hy
  have hwJ := Subgroup.mem_centralizer_singleton_iff.mp (WardL.centralizer_So_le S.W hσ hσ1 hwσ)
  apply S.W.centralizer_J' w hwJ
  rwa [S.orderOf_κ] at hodd

omit [CharP K 3] in
include S in
theorem six_mul_le_card_normalizer_So :
    6 * (q + 1) ≤ Nat.card (Subgroup.normalizer ((S.W.So.map S.κ : Subgroup G) : Set G)) := by
  set N := Subgroup.normalizer ((S.W.So.map S.κ : Subgroup G) : Set G) with hN
  set H := N ⊓ Subgroup.centralizer ({S.J} : Set G) with hH
  have hJN : S.J ∈ N := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← S.κ_comm ρ, mul_inv_cancel_right]
    exact Subgroup.mem_map_of_mem _ hρ
  have hκN : ∀ y, y * S.W.J' = S.W.J' * y → S.κ y ∈ N := by
    intro y hy
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (WardL.conj_mem_So S.W hy hρ)
  have hHc : 2 * (q + 1) ≤ Nat.card H := by
    have hCJ' : (Nat.card (Subgroup.centralizer ({S.W.J'} : Set PSL(2, K))) : ℤ) = q + 1 := by
      have := S.W.card_centralizer_J'; linarith
    have hCJ'' : Nat.card (Subgroup.centralizer ({S.W.J'} : Set PSL(2, K))) = q + 1 := by
      exact_mod_cast hCJ'
    have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    have e : 2 * (q + 1) =
        Nat.card (Bool × Subgroup.centralizer ({S.W.J'} : Set PSL(2, K))) := by
      rw [Nat.card_prod, hb, hCJ'']
    rw [e]
    refine Nat.card_le_card_of_injective
      (fun p => ⟨(if p.1 then S.J else 1) * S.κ p.2, ?_⟩) ?_
    · have hy := Subgroup.mem_centralizer_singleton_iff.mp p.2.2
      refine ⟨N.mul_mem ?_ (hκN _ hy), Subgroup.mul_mem _ ?_
        (Subgroup.mem_centralizer_singleton_iff.mpr (S.κ_comm _))⟩
      · split_ifs
        · exact hJN
        · exact N.one_mem
      · split_ifs
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · exact Subgroup.one_mem _
    · rintro ⟨b, y⟩ ⟨b', y'⟩ h
      have h' : (if b then S.J else 1) * S.κ y = (if b' then S.J else 1) * S.κ y' :=
        congrArg Subtype.val h
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h'
      · exact Prod.ext rfl (Subtype.ext (S.κ_inj h'))
      · exact absurd h'.symm (S.J_mul_ne y' y)
      · exact absurd h' (S.J_mul_ne y y')
      · exact Prod.ext rfl (Subtype.ext (S.κ_inj (mul_left_cancel h')))
  have hAN : S.A ∈ N := by
    have hA' : S.A⁻¹ ∈ N := by
      apply mem_normalizer_of_conj_mem
      intro x hx
      obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨ρ', hρ', h'⟩ := S.A_So ρ hρ
      rw [inv_inv, h']
      exact Subgroup.mem_map_of_mem _ hρ'
    simpa using N.inv_mem hA'
  have hAJ : S.A * S.J ≠ S.J * S.A := by
    intro h
    apply S.J_not_mem S.W.J'
    rw [← S.A_J, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hA3 : S.A ^ 3 = 1 := by rw [← S.orderOf_A, pow_orderOf_eq_one]
  have hidx : 3 ≤ H.relIndex N := by
    have hpos : 0 < H.relIndex N := by
      have := card_mul_relIndex (inf_le_left : H ≤ N)
      rcases Nat.eq_zero_or_pos (H.relIndex N) with h0 | h0
      · rw [h0, mul_zero] at this; exact absurd this.symm Nat.card_pos.ne'
      · exact h0
    have h1 : H.relIndex N ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      exact hAJ (Subgroup.mem_centralizer_singleton_iff.mp (hle hAN).2)
    have h2 : H.relIndex N ≠ 2 := by
      intro h2
      have hsq := Subgroup.mul_self_mem_of_index_two h2 ⟨S.A, hAN⟩
      rw [Subgroup.mem_subgroupOf] at hsq
      have hA2 : S.A * S.A ∈ Subgroup.centralizer ({S.J} : Set G) := hsq.2
      apply hAJ
      have : S.A = (S.A * S.A) * (S.A * S.A) := by
        calc S.A = S.A ^ 3 * S.A := by rw [hA3, one_mul]
          _ = (S.A * S.A) * (S.A * S.A) := by rw [pow_three]; group
      rw [this]
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mul_mem _ hA2 hA2)
    omega
  have hcard := card_mul_relIndex (inf_le_left : H ≤ N)
  rw [← hcard]
  nlinarith

include B hq hK hG hP1P hPc hPn hN1c in
theorem mem_image_So (hm : q = 3 * m ^ 2) {x : G} (hodd : Odd (orderOf x)) {r : ℕ}
    (hr : r.Prime) (hrS : r ∣ Nat.card S.W.So) (hrx : r ∣ orderOf x) :
    x ∈ ((Finset.univ ×ˢ ((Finset.univ.filter (· ∈ S.W.So.map S.κ)).erase 1)).image
      (fun p : G × G => p.1 * p.2 * p.1⁻¹)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hSoodd, -, -⟩ := So_arith hq (S := S)
  have hr2 : r ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr hSoodd) (even_iff_two_dvd.mpr hrS)
  obtain ⟨y, hy⟩ : ∃ y, y = x ^ (orderOf x / r) := ⟨_, rfl⟩
  have hyo : orderOf y = r := by rw [hy]; exact exists_pow_orderOf_eq hr hrx
  have hH : r ^ (Nat.card G).factorization r ∣ Nat.card (S.W.So.map S.κ) := by
    rw [Subgroup.card_map_of_injective S.κ_inj]; exact ppart_So hq hG hm hr hr2 hrS
  have hyp : IsPGroup r (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hyo, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_full _ hH hyp
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.mp hg
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one] at hσg
    have : y = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) hσg.symm
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  have hxy : x * y = y * x := by rw [hy]; exact (Commute.self_pow x _).eq
  have hcomm : g⁻¹ * x * g * S.κ σ = S.κ σ * (g⁻¹ * x * g) := by
    rw [hσg]
    calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hxy]
      _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
  have hodd' : Odd (orderOf (g⁻¹ * x * g)) := by rw [orderOf_conj']; exact hodd
  have hmem := B.odd_mem_κSo hq hK hG hP1P hPc hPn hN1c hm hσ hσ1 hcomm hodd'
  have hx1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    have : x = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hrx
    exact hr.one_lt.ne' (Nat.dvd_one.mp hrx)
  refine Finset.mem_image.mpr ⟨(g, g⁻¹ * x * g), ?_, by
    show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_erase.mpr ⟨hx1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩⟩

omit [CharP K 3] in
include hq hG in
theorem mem_image_hall {M : Subgroup G} (hm : q = 3 * m ^ 2) {n : ℕ}
    (hn : n = q + 1 - 3 * m ∨ n = q + 1 + 3 * m) (hMc : Nat.card M = n)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) {x : G} {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hpx : p ∣ orderOf x) :
    x ∈ ((Finset.univ ×ˢ ((Finset.univ.filter (· ∈ M)).erase 1)).image
      (fun p : G × G => p.1 * p.2 * p.1⁻¹)) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_hall hq hG hm hn hMc hcen hp hpn hpx
  have hx1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    have : x = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hpx
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpx)
  refine Finset.mem_image.mpr ⟨(g, g⁻¹ * x * g), ?_, by
    show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_erase.mpr ⟨hx1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩⟩⟩

omit [CharP K 3] in
include B hq hG in
theorem three_elem_of_odd {x : G} (hodd : Odd (orderOf x)) (h3 : 3 ∣ orderOf x) :
    ∃ i : ℕ, orderOf x = 3 ^ i := by
  obtain ⟨e, b, hb3, hxb⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have he : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    rw [this, pow_zero, one_mul] at hxb
    exact hb3 (hxb ▸ h3)
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [mul_zero] at hxb; exact (orderOf_pos x).ne' hxb
  have hz : orderOf (x ^ b) = 3 ^ e := by
    rw [orderOf_pow_of_dvd hb0 ⟨3 ^ e, by rw [hxb]; ring⟩, hxb,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
  have hzodd : Odd (orderOf (x ^ b)) := by rw [hz]; exact Odd.pow (by decide)
  have hz3 : 3 ∣ orderOf (x ^ b) := by rw [hz]; exact dvd_pow_self 3 (by omega)
  have hd := B.card_centralizer_dvd hq hG hzodd hz3
  have hxz : x ∈ Subgroup.centralizer ({x ^ b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.self_pow x b).eq
  have h1 := (Subgroup.orderOf_dvd_natCard _ hxz).trans hd
  have hbdvd : b ∣ 2 * q ^ 3 := (Dvd.intro_left _ hxb.symm).trans h1
  have hbodd : Odd b := Odd.of_dvd_nat hodd (Dvd.intro_left _ hxb.symm)
  have hb2 : Nat.Coprime b 2 := Nat.coprime_two_right.mpr hbodd
  have hb3' : Nat.Coprime b 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3).symm
  have hbq : Nat.Coprime b (2 * q ^ 3) := by
    rw [hq, ← pow_mul]
    exact Nat.Coprime.mul_right hb2 (Nat.Coprime.pow_right _ hb3')
  have hb1 : b = 1 := Nat.Coprime.eq_one_of_dvd hbq hbdvd
  exact ⟨e, by rw [hxb, hb1, mul_one]⟩

end Block

end CFSG.Walter.WardLocal
