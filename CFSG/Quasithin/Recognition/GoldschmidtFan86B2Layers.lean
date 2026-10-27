module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Coprime

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

structure CoprimeLayer (x : G) (M N : Subgroup G) : Prop where
  pow_five : x ^ 5 = 1
  le : N ≤ M
  normal : (N.subgroupOf M).Normal
  xM : ∀ m ∈ M, x * m * x⁻¹ ∈ M
  xN : ∀ n ∈ N, x * n * x⁻¹ ∈ N
  finite : Finite M
  pgroup : IsPGroup 2 M

namespace CoprimeLayer

variable {x : G} {M N : Subgroup G}

theorem le_normalizer (h : CoprimeLayer x M N) : M ≤ Subgroup.normalizer (N : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).1 h.normal

theorem conj_mem (h : CoprimeLayer x M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) :
    m * n * m⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.1 (h.le_normalizer hm) n).1 hn

theorem finite_N (h : CoprimeLayer x M N) : Finite N := by
  have := h.finite
  exact Finite.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)

theorem pgroup_N (h : CoprimeLayer x M N) : IsPGroup 2 N := h.pgroup.to_le h.le

theorem exists_card_eq (h : CoprimeLayer x M N) : ∃ k, Nat.card N = 2 ^ k := by
  have := h.finite_N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.pgroup_N.exists_card_eq


theorem mem_conj_fix (h : CoprimeLayer x M N) {m : G} (hm : m ∈ M)
    (hc : x * m * x⁻¹ * m⁻¹ ∈ N) {n : G} (hn : n ∈ N) :
    m⁻¹ * (x * (m * n) * x⁻¹) ∈ N := by
  have h1 : m⁻¹ * (x * m * x⁻¹ * m⁻¹) * m ∈ N := by
    have := h.conj_mem (Subgroup.inv_mem M hm) hc
    simpa using this
  have h2 : x * n * x⁻¹ ∈ N := h.xN n hn
  have h3 : m⁻¹ * (x * (m * n) * x⁻¹) =
      (m⁻¹ * (x * m * x⁻¹ * m⁻¹) * m) * (x * n * x⁻¹) := by group
  rw [h3]
  exact Subgroup.mul_mem N h1 h2

theorem exists_fixed (h : CoprimeLayer x M N) {m : G} (hm : m ∈ M)
    (hc : x * m * x⁻¹ * m⁻¹ ∈ N) : ∃ n ∈ N, x * (m * n) * x⁻¹ = m * n := by
  classical
  have hfin := h.finite_N
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : Function.End N := fun n => ⟨m⁻¹ * (x * (m * (n : G)) * x⁻¹), h.mem_conj_fix hm hc n.2⟩
  have hpow : ∀ (k : ℕ) (n : N),
      (((f ^ k) n : N) : G) = m⁻¹ * (x ^ k * (m * (n : G)) * (x ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro n; simp; rfl
    | succ k ih =>
      intro n
      rw [pow_succ]
      show (((f ^ k) (f n) : N) : G) = _
      rw [ih]
      show m⁻¹ * (x ^ k * (m * (m⁻¹ * (x * (m * (n : G)) * x⁻¹))) * (x ^ k)⁻¹) = _
      have e : x ^ (k + 1) = x ^ k * x := pow_succ x k
      rw [e]
      group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext n
    apply Subtype.ext
    rw [pow_one, hpow, h.pow_five]
    simp
    rfl
  have := Fintype.ofFinite N
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := N) hf
  have hmod' : Nat.card N ≡ Nat.card (Function.fixedPoints f) [MOD 5] := by
    simpa only [Fintype.card_eq_nat_card] using hmod
  obtain ⟨k, hk⟩ := h.exists_card_eq
  have hne : Nat.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0, hk] at hmod'
    have h5 : 5 ∣ 2 ^ k := (Nat.modEq_zero_iff_dvd).1 hmod'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    omega
  have hpos : 0 < Nat.card (Function.fixedPoints f) := Nat.pos_of_ne_zero hne
  obtain ⟨⟨n, hn⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  refine ⟨n, n.2, ?_⟩
  have hfn : f n = n := hn
  have := congrArg (fun y : N => (y : G)) hfn
  simp only [f] at this
  calc x * (m * (n : G)) * x⁻¹ = m * (m⁻¹ * (x * (m * (n : G)) * x⁻¹)) := by group
    _ = m * n := by rw [this]

end CoprimeLayer

@[expose] def prodCent (x : G) (M N : Subgroup G) : Subgroup G :=
  N ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ M)

theorem le_prodCent (x : G) (M N : Subgroup G) : N ≤ prodCent x M N := le_sup_left

theorem cent_le_prodCent (x : G) (M N : Subgroup G) :
    Subgroup.centralizer ({x} : Set G) ⊓ M ≤ prodCent x M N := le_sup_right

theorem relIndex_sup_right_of_le_normalizer {H K : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hLE).toEquiv.symm

theorem relIndex_inf_left_of_le {C M N : Subgroup G} (hNM : N ≤ M) :
    (C ⊓ M).relIndex N = C.relIndex N := by
  unfold Subgroup.relIndex
  congr 1
  ext n
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNM n.2⟩⟩

namespace CoprimeLayer

variable {x : G} {M N : Subgroup G}

theorem prodCent_le (h : CoprimeLayer x M N) : prodCent x M N ≤ M :=
  sup_le h.le inf_le_right

theorem relIndex_centralizer_eq_mul (h : CoprimeLayer x M N) :
    (Subgroup.centralizer ({x} : Set G)).relIndex M =
      (prodCent x M N).relIndex M * (Subgroup.centralizer ({x} : Set G)).relIndex N := by
  have hfin := h.finite
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hC'M : C ⊓ M ≤ M := inf_le_right
  have hC'D : C ⊓ M ≤ prodCent x M N := cent_le_prodCent x M N
  have hDM : prodCent x M N ≤ M := h.prodCent_le
  have hND : N ≤ prodCent x M N := le_prodCent x M N
  have hnorm : C ⊓ M ≤ Subgroup.normalizer (N : Set G) := hC'M.trans h.le_normalizer
  have e1 : N.relIndex (prodCent x M N) = N.relIndex (C ⊓ M) := by
    have : prodCent x M N = (C ⊓ M) ⊔ N := sup_comm _ _
    rw [this]
    exact relIndex_sup_right_of_le_normalizer hnorm
  have hA1 := Subgroup.relIndex_mul_relIndex (N ⊓ (C ⊓ M)) N (prodCent x M N) inf_le_left hND
  have hA2 := Subgroup.relIndex_mul_relIndex (N ⊓ (C ⊓ M)) (C ⊓ M) (prodCent x M N)
    inf_le_right hC'D
  have e2 : (N ⊓ (C ⊓ M)).relIndex (C ⊓ M) = N.relIndex (C ⊓ M) :=
    Subgroup.inf_relIndex_right N (C ⊓ M)
  have e3 : (N ⊓ (C ⊓ M)).relIndex N = C.relIndex N := by
    rw [Subgroup.inf_relIndex_left N (C ⊓ M)]
    exact relIndex_inf_left_of_le h.le
  have hne : N.relIndex (C ⊓ M) ≠ 0 := by
    have : Finite (C ⊓ M : Subgroup G) :=
      Finite.of_injective (Subgroup.inclusion hC'M) (Subgroup.inclusion_injective hC'M)
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have key : (C ⊓ M).relIndex (prodCent x M N) = C.relIndex N := by
    rw [e3, e1] at hA1
    rw [e2] at hA2
    have h5 : N.relIndex (C ⊓ M) * (C ⊓ M).relIndex (prodCent x M N) =
        N.relIndex (C ⊓ M) * C.relIndex N := by
      rw [hA2, ← hA1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h5
  have tower := Subgroup.relIndex_mul_relIndex (C ⊓ M) (prodCent x M N) M hC'D hDM
  rw [key, Subgroup.inf_relIndex_right C M] at tower
  rw [← tower, mul_comm]

end CoprimeLayer

end CFSG.Quasithin.Fan86
