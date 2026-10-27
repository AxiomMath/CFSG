module

public import CFSG.Walter.ReeOrder.WardLocal.Perm
public import CFSG.Walter.ReeOrder.WardLocal.NP

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem three_dvd_of_mem {P : Subgroup G} (hP : IsPGroup 3 P) {u : G} (hu : u ∈ P)
    (hu1 : u ≠ 1) : 3 ∣ orderOf u := by
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hN
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hN; exact absurd hN hu1
  · rw [hN]; exact dvd_pow_self 3 h0.ne'

omit [Fintype G] in
theorem exists_conj_of_inf_eq_bot {P : Subgroup G} [Finite P] {w : G}
    (hwN : w ∈ Subgroup.normalizer (P : Set G))
    (hC : P ⊓ Subgroup.centralizer ({w} : Set G) = ⊥) {u : G} (hu : u ∈ P) :
    ∃ v ∈ P, u * w = v * w * v⁻¹ := by
  have hmem : ∀ v : P, (v : G) * w * (v : G)⁻¹ * w⁻¹ ∈ P := by
    intro v
    have h1 : w * (v : G)⁻¹ * w⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hwN _).mp (P.inv_mem v.2)
    have := P.mul_mem v.2 h1
    simpa [mul_assoc] using this
  let φ : P → P := fun v => ⟨_, hmem v⟩
  have hinj : Function.Injective φ := by
    intro v v' h
    have h' : (v : G) * w * (v : G)⁻¹ * w⁻¹ = (v' : G) * w * (v' : G)⁻¹ * w⁻¹ :=
      congrArg Subtype.val h
    have h1 : (v : G) * w * (v : G)⁻¹ = (v' : G) * w * (v' : G)⁻¹ := by
      simpa using congrArg (· * w) h'
    have hc : (v' : G)⁻¹ * v ∈ P ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine ⟨P.mul_mem (P.inv_mem v'.2) v.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (v' : G)⁻¹ * v * w = (v' : G)⁻¹ * ((v : G) * w * (v : G)⁻¹) * v := by group
        _ = (v' : G)⁻¹ * ((v' : G) * w * (v' : G)⁻¹) * v := by rw [h1]
        _ = w * ((v' : G)⁻¹ * v) := by group
    rw [hC, Subgroup.mem_bot] at hc
    apply Subtype.ext
    have := congrArg (fun z => (v' : G) * z) hc
    simpa using this
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
  refine ⟨v, v.2, ?_⟩
  have : (v : G) * w * (v : G)⁻¹ * w⁻¹ = u := congrArg Subtype.val hv
  rw [← this]; group

omit [Fintype G] in
theorem mem_conj_smul_iff {H : Subgroup G} {g x : G} :
    x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

omit [Fintype G] in
theorem mem_normalizer_of_conj {P Q : Subgroup G} {g : G} (hQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P)
    {n : G} : n ∈ Subgroup.normalizer (Q : Set G) ↔
      g⁻¹ * n * g ∈ Subgroup.normalizer (P : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, hQ]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group,
      show g⁻¹ * (n * (g * y * g⁻¹) * n⁻¹) * g = g⁻¹ * n * g * y * (g⁻¹ * n * g)⁻¹ by group]
      at this
  · intro h y
    have := h (g⁻¹ * y * g)
    rwa [show g⁻¹ * n * g * (g⁻¹ * y * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * y * n⁻¹) * g by group]
      at this

theorem sum_conj {P Q : Subgroup G} {g : G} (hQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P) (f : G → ℂ) :
    ∑ x ∈ Finset.univ.filter (· ∈ Q), f x =
      ∑ y ∈ Finset.univ.filter (· ∈ P), f (g * y * g⁻¹) := by
  refine Finset.sum_nbij' (fun x => g⁻¹ * x * g) (fun y => g * y * g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (hQ x).mp hx
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hQ]; simpa [mul_assoc] using hy
  · intro x _; group
  · intro y _; group
  · intro x _; congr 1; group

theorem card_filter_eq (H : Subgroup G) :
    (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
  simp [Fintype.card_subtype]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [CharP K 3] in
theorem xi3_class (g x : G) : B.ξ₃ (g * x * g⁻¹) = B.ξ₃ x :=
  blocksVChar_isClassFunction (AddSubgroup.subset_closure B.irr_3) x g

omit [CharP K 3] in
theorem xi3_one : B.ξ₃ 1 = (q : ℂ) ^ 3 := by
  rw [← deg_eq B.irr_3, B.deg_3]; push_cast; ring

omit [CharP K 3] in
theorem xi3_J : B.ξ₃ S.J = q := by
  have h1 : B.ξ₃ ∈ S.S1 := by rw [B.hS1]; simp
  have h2 : B.ξ₃ ∈ S.S2 := by rw [B.hS2]; simp
  rw [S.J_val_P B.irr_3 (Or.inl h1), ← S.agree12 h1 h2, ← S.agree13 h1 B.ξ₃_S3, B.d1_3]
  push_cast; ring

omit [CharP K 3] in
theorem xi3_involution {t : G} (ht : orderOf t = 2) : B.ξ₃ t = q := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.involution_conj t ht)
  rw [← B.xi3_J, ← hc, B.xi3_class]

omit [CharP K 3] in
include hq hK in
theorem exists_conj_Ro_of_mem {S : WardSetup G PSL(2, K) q (-1)} {y : PSL(2, K)}
    (hy : y ∈ Subgroup.zpowers (dgen K)) (hy1 : y ≠ 1) :
    ∃ g r : PSL(2, K), r ∈ S.W.Ro ∧ r ≠ 1 ∧ y = g * r * g⁻¹ ∧ Odd (orderOf r) := by
  have hRo : 2 * Nat.card S.W.Ro + 1 = q := by have := S.W.Ro_card; omega
  have hcR := card_RR (S := S) hK hq
  have hord : orderOf y ∣ Nat.card S.W.Ro := by
    obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hy
    have h1 : Nat.card S.W.Ro = Nat.card (RR S) := by omega
    rw [h1, RR, Subgroup.card_map_of_injective S.κ_inj, Nat.card_zpowers]
    exact orderOf_pow_dvd j
  obtain ⟨g, hg⟩ := S.W.Ro_conj _ hord
  refine ⟨g, g⁻¹ * y * g, hg, ?_, by group, ?_⟩
  · intro h; apply hy1
    have := congrArg (fun t => g * t * g⁻¹) h
    simpa [mul_assoc] using this
  · obtain ⟨k', hk', hodd⟩ := Block.q_half hq
    have hRk : Nat.card S.W.Ro = k' := by omega
    have : orderOf (g⁻¹ * y * g) = orderOf y := by
      rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by group, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [this]
    exact Odd.of_dvd_nat hodd (hRk ▸ hord)

include hq hK in
omit [CharP K 3] in
theorem xi3_kappa {y : PSL(2, K)} (hy : y ∈ Subgroup.zpowers (dgen K)) (hy1 : y ≠ 1) :
    B.ξ₃ (S.κ y) = 1 := by
  obtain ⟨g, r, hr, hr1, rfl, -⟩ := exists_conj_Ro_of_mem (S := S) hq hK hy hy1
  have h1 : B.ξ₃ ∈ S.S1 := by rw [B.hS1]; simp
  rw [map_mul, map_mul, map_inv, B.xi3_class, D.τ_NE (D.S1_NE h1) hr hr1, B.z_3]
  simp

include hq hK in
omit [CharP K 3] in
theorem xi3_J_kappa {y : PSL(2, K)} (hy : y ∈ Subgroup.zpowers (dgen K)) (hy1 : y ≠ 1) :
    B.ξ₃ (S.J * S.κ y) = 1 := by
  obtain ⟨g, r, hr, hr1, rfl, hro⟩ := exists_conj_Ro_of_mem (S := S) hq hK hy hy1
  have h1 : B.ξ₃ ∈ S.S1 := by rw [B.hS1]; simp
  have he : S.J * S.κ (g * r * g⁻¹) = S.κ g * (S.J * S.κ r) * (S.κ g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    calc S.J * (S.κ g * S.κ r * (S.κ g)⁻¹) = (S.J * S.κ g) * S.κ r * (S.κ g)⁻¹ := by group
      _ = (S.κ g * S.J) * S.κ r * (S.κ g)⁻¹ := by rw [S.κ_comm' g]
      _ = S.κ g * (S.J * S.κ r) * (S.κ g)⁻¹ := by group
  rw [he, B.xi3_class]
  have hσ : B.ξ₃ (S.J * S.κ r) = S.σ B.ξ₃ r := rfl
  obtain ⟨hR, hS⟩ := S.P_rows B.irr_3 (Or.inl h1)
  obtain ⟨h2, h3, -, -⟩ := S.W.val_Ro r hr hr1
  rw [hσ, S.σ_decomp B.irr_3 hro, h2, h3, B.d1_3,
    Finset.sum_eq_zero (fun θ hθ => by rw [hR θ hθ]; simp),
    Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp)]
  simp

include hq hK in
omit [CharP K 3] in
theorem xi3_WW {w : G} (hw : w ∈ WW S) (hw1 : w ≠ 1) (hwJ : w ≠ S.J) : B.ξ₃ w = 1 := by
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hw)
  simp only at hw1 hwJ ⊢
  rw [wgen_pow, ← map_pow] at hw1 hwJ ⊢
  have hd : dgen K ^ i ∈ Subgroup.zpowers (dgen K) :=
    Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i
  rcases Nat.even_or_odd i with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hJ : S.J ^ (t + t) = 1 := by rw [← two_mul, pow_mul, sq, S.J_mul, one_pow]
    rw [hJ, one_mul] at hw1 ⊢
    exact B.xi3_kappa hq hK hd (fun h => hw1 (by rw [h, map_one]))
  · have hJ : S.J ^ (2 * t + 1) = S.J := by
      rw [pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul]
    rw [hJ] at hwJ ⊢
    exact B.xi3_J_kappa hq hK hd (fun h => hwJ (by rw [h, map_one, mul_one]))

include B hq hK hG hP1P hPc hPn hN1c in
theorem normalizer_eq' : Subgroup.normalizer (P : Set G) = NN1 S :=
  normalizer_eq_NN1 hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c

include B hq hK hG hPn in
theorem J_mem_normalizer : S.J ∈ Subgroup.normalizer (P : Set G) :=
  NN1_le_normalizer hPn (J_mem_normalizer_PP1 hq (B.hcT hq hK hG))

include B hq hG hPc in
omit [CharP K 3] in
theorem xi3_P {u : G} (hu : u ∈ P) (hu1 : u ≠ 1) : B.ξ₃ u = 0 :=
  B.xi3_eq_zero hq hG (three_dvd_of_mem (isPGroup_P hq hPc) hu hu1)

include hq hPc in
omit [CharP K 3] in
theorem orderOf_mul_J {u : G} (hu : u ∈ P) (h : S.J * u * S.J = u⁻¹) : orderOf (u * S.J) = 2 := by
  apply orderOf_eq_prime
  · rw [sq]
    calc u * S.J * (u * S.J) = u * (S.J * u * S.J) := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  · intro h1
    have hJ : S.J = u⁻¹ := by
      have := congrArg (fun z => u⁻¹ * z) h1
      simpa using this
    have hJP : S.J ∈ P := hJ ▸ P.inv_mem hu
    have h3 := three_dvd_of_mem (isPGroup_P hq hPc) hJP S.J_ne
    rw [S.orderOf_J] at h3
    omega

include B hq hK hG hPc hPn in
theorem xi3_mul_J {u : G} (hu : u ∈ P) (h : ¬ S.J * u * S.J = u⁻¹) : B.ξ₃ (u * S.J) = 0 := by
  apply B.xi3_eq_zero hq hG
  have hJN := B.J_mem_normalizer hq hK hG hPn
  have hJu : S.J * u * S.J ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp hJN u).mp hu
    rwa [S.J_inv] at this
  have h2 : (u * S.J) ^ 2 ∈ P := by
    rw [sq, show u * S.J * (u * S.J) = u * (S.J * u * S.J) by group]
    exact P.mul_mem hu hJu
  have h21 : (u * S.J) ^ 2 ≠ 1 := by
    intro h1
    apply h
    rw [sq, show u * S.J * (u * S.J) = u * (S.J * u * S.J) by group] at h1
    have := congrArg (fun z => u⁻¹ * z) h1
    simpa using this
  exact (three_dvd_of_mem (isPGroup_P hq hPc) h2 h21).trans (orderOf_pow_dvd 2)

include B hq hK hG hP1P hPc hPn hN1c in
theorem xi3_mul_W {u w : G} (hu : u ∈ P) (hw : w ∈ WW S) (hw1 : w ≠ 1) (hwJ : w ≠ S.J) :
    B.ξ₃ (u * w) = 1 := by
  have hwN : w ∈ Subgroup.normalizer (P : Set G) := by
    rw [B.normalizer_eq' hq hK hG hP1P hPc hPn hN1c]
    exact WW_le_normalizer_PP1 hq (B.hcT hq hK hG) hw
  have : Finite P := inferInstance
  obtain ⟨v, -, hv⟩ := exists_conj_of_inf_eq_bot hwN (inf_centralizer_WW hq hK hPc hw hw1 hwJ) hu
  rw [hv, B.xi3_class, B.xi3_WW hq hK hw hw1 hwJ]

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_coset {w : G} (hw : w ∈ WW S) :
    ∑ u ∈ Finset.univ.filter (· ∈ P), B.ξ₃ (u * w) = (q : ℂ) ^ 3 := by
  by_cases hw1 : w = 1
  · subst hw1
    simp only [mul_one]
    rw [Finset.sum_eq_single (1 : G)]
    · exact B.xi3_one
    · intro u hu hu1
      exact B.xi3_P hq hG hPc (Finset.mem_filter.mp hu).2 hu1
    · intro h; exact absurd (by simp) h
  by_cases hwJ : w = S.J
  · subst hwJ
    have hval : ∀ u ∈ Finset.univ.filter (· ∈ P), B.ξ₃ (u * S.J) =
        if S.J * u * S.J = u⁻¹ then (q : ℂ) else 0 := by
      intro u hu
      have huP := (Finset.mem_filter.mp hu).2
      split_ifs with h
      · exact B.xi3_involution (orderOf_mul_J hq hPc huP h)
      · exact B.xi3_mul_J hq hK hG hPc hPn huP h
    rw [Finset.sum_congr rfl hval, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    have hJN := B.J_mem_normalizer hq hK hG hPn
    have hinv := card_inverted_mul P S.J_mul (fun h hh => by
      have := (Subgroup.mem_normalizer_iff.mp hJN h).mp hh
      rwa [S.J_inv] at this) (by rw [hPc, hq, ← pow_mul]; exact Odd.pow (by decide))
    rw [inf_centralizer_J hq hK (B.hcT hq hK hG) hP1P hPc, card_FF, hK, hPc] at hinv
    have hq0 : 0 < q := by rw [hq]; positivity
    have hc : (Finset.univ.filter fun h : G => h ∈ P ∧ S.J * h * S.J = h⁻¹).card = q ^ 2 := by
      have : (Finset.univ.filter fun h : G => h ∈ P ∧ S.J * h * S.J = h⁻¹).card * q = q ^ 2 * q :=
        by rw [hinv]; ring
      exact Nat.eq_of_mul_eq_mul_right hq0 this
    rw [hc]
    push_cast
    ring
  · have hval : ∀ u ∈ Finset.univ.filter (· ∈ P), B.ξ₃ (u * w) = 1 := fun u hu =>
      B.xi3_mul_W hq hK hG hP1P hPc hPn hN1c (Finset.mem_filter.mp hu).2 hw hw1 hwJ
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_eq, hPc]
    push_cast; ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem image_mul_eq :
    ((Finset.univ.filter (· ∈ P)) ×ˢ (Finset.univ.filter (· ∈ WW S))).image
      (fun p : G × G => p.1 * p.2) = Finset.univ.filter (· ∈ Subgroup.normalizer (P : Set G)) ∧
    Set.InjOn (fun p : G × G => p.1 * p.2)
      ((Finset.univ.filter (· ∈ P)) ×ˢ (Finset.univ.filter (· ∈ WW S)) : Finset (G × G)) := by
  have hcT := B.hcT hq hK hG
  have hA := B.card_AA hq hK hG
  have hC1 : ∀ x : G, Odd (orderOf x) → 3 ∣ orderOf x →
      Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 3 :=
    fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2)
      ((Finset.univ.filter (· ∈ P)) ×ˢ (Finset.univ.filter (· ∈ WW S)) : Finset (G × G)) := by
    rintro ⟨u, w⟩ huw ⟨u', w'⟩ huw' h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq] at huw huw'
    simp only at h
    have h1 : u'⁻¹ * u = w' * w⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * w) * w⁻¹ := by group
        _ = u'⁻¹ * (u' * w') * w⁻¹ := by rw [h]
        _ = w' * w⁻¹ := by group
    have hmem : u'⁻¹ * u ∈ P ⊓ WW S :=
      ⟨P.mul_mem (P.inv_mem huw'.1) huw.1, h1 ▸ (WW S).mul_mem huw'.2 ((WW S).inv_mem huw.2)⟩
    rw [inf_WW hq hK hPc, Subgroup.mem_bot] at hmem
    have hu : u = u' := by
      have := congrArg (fun z => u' * z) hmem
      simpa using this
    subst hu
    have hw : w = w' := mul_left_cancel h
    rw [hw]
  refine ⟨?_, hinj⟩
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨⟨u, w⟩, huw, rfl⟩ := Finset.mem_image.mp hn
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at huw ⊢
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer huw.1)
      (WW_le_normalizer hq hK hcT hG hA hC1 hP1P hPc hPn hN1c huw.2)
  · rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_filter_eq, card_filter_eq,
      card_filter_eq, card_normalizer hq hK hcT hG hA hC1 hP1P hPc hPn hN1c, hPc, card_WW hq hK]

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_normalizer :
    ∑ n ∈ Finset.univ.filter (· ∈ Subgroup.normalizer (P : Set G)), B.ξ₃ n =
      Nat.card (Subgroup.normalizer (P : Set G)) := by
  obtain ⟨himg, hinj⟩ := B.image_mul_eq hq hK hG hP1P hPc hPn hN1c
  rw [← himg, Finset.sum_image hinj, Finset.sum_product, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun w hw => B.sum_coset hq hK hG hP1P hPc hPn hN1c
    (Finset.mem_filter.mp hw).2, Finset.sum_const, nsmul_eq_mul, card_filter_eq, card_WW hq hK,
    card_normalizer hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
      (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c]
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  push_cast [Nat.cast_sub hq1]
  ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem xi3_cases {n : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    n = 1 ∨ orderOf n = 2 ∨ B.ξ₃ n = 0 ∨ B.ξ₃ n = 1 := by
  obtain ⟨himg, -⟩ := B.image_mul_eq hq hK hG hP1P hPc hPn hN1c
  have hn' : n ∈ Finset.univ.filter (· ∈ Subgroup.normalizer (P : Set G)) := by simp [hn]
  rw [← himg] at hn'
  obtain ⟨⟨u, w⟩, huw, rfl⟩ := Finset.mem_image.mp hn'
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at huw
  obtain ⟨hu, hw⟩ := huw
  by_cases hw1 : w = 1
  · subst hw1
    rw [mul_one]
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · exact Or.inr (Or.inr (Or.inl (B.xi3_P hq hG hPc hu hu1)))
  by_cases hwJ : w = S.J
  · subst hwJ
    by_cases h : S.J * u * S.J = u⁻¹
    · exact Or.inr (Or.inl (orderOf_mul_J hq hPc hu h))
    · exact Or.inr (Or.inr (Or.inl (B.xi3_mul_J hq hK hG hPc hPn hu h)))
  · exact Or.inr (Or.inr (Or.inr (B.xi3_mul_W hq hK hG hP1P hPc hPn hN1c hu hw hw1 hwJ)))

end Block

end CFSG.Walter.WardLocal
