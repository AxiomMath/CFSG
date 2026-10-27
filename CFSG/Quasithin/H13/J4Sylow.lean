module

public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Quasithin.H13.J4Words
public meta import CFSG.Sporadic.Schreier.J4SData
public import CFSG.Quasithin.H13.J4SylowInputs
public import Certificates.Certificate7021
public import Certificates.Certificate2168
public import Certificates.Certificate2177
public import Certificates.Certificate2182
public import Certificates.Certificate3084

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native

theorem fixedGenCols_eq : fixedGenCols = [0, 1] :=
  Certificates.certificate7021

theorem genCols_zero : ∀ i < 4, (generatorColumns[i]!)[0]! = 1 := by decide

theorem genCols_lt : ∀ i < 4, ∀ j < 11, (generatorColumns[i]!)[j]?.getD 0 < 2 ^ 11 := by
  decide

theorem N_comm' {a b : J} (ha : a ∈ N) (hb : b ∈ N) :
    a * b = b * a := by
  obtain ⟨i, -, rfl⟩ := exists_η_eq ha
  obtain ⟨k, -, rfl⟩ := exists_η_eq hb
  rw [← η_xor, ← η_xor, Nat.xor_comm]

theorem conj_mem_N_of_mem_U
    {g : J} (hg : g ∈ U) (a : ℕ) :
    g * η a * g⁻¹ ∈ N := by
  obtain ⟨e, he, rfl⟩ := mem_U_iff.1 hg
  rw [uElt_acts he a]
  exact η_mem_N _

theorem kgen_conj_eta_one (i : Fin 4)
    :
    kgen i * η 1 * (kgen i)⁻¹ = η 1 := by
  rw [kgen_acts i.2 1]
  congr 1
  have h := app11_two_pow (genCols_lt i i.2) (j := 0) (by norm_num)
  rw [pow_zero] at h
  rw [h, ← getElem!_eq_getD', genCols_zero i i.2]

theorem eta_one_comm_S0 {s : J}
    (hs : s ∈ S0) :
    s * η 1 = η 1 * s := by
  have key : S0 ≤ Subgroup.centralizer {η 1} := by
    rw [S0, Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro _ rfl
    · exact N_comm' (η_mem_N 1) (η_mem_N 4)
    · calc η 1 * kgen i = kgen i * η 1 * (kgen i)⁻¹ * kgen i := by rw [kgen_conj_eta_one i]
        _ = kgen i * η 1 := by group
  exact (Subgroup.mem_centralizer_iff.1 (key hs) (η 1) rfl).symm

theorem center_S0 :
    ((Subgroup.center S0).map S0.subtype : Set J) = {η 0, η 1} := by
  ext s
  simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Subgroup.coe_subtype,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs⟩, hc, rfl⟩
    show s = η 0 ∨ s = η 1
    rw [Subgroup.mem_center_iff] at hc
    have hcomm : ∀ t ∈ S0, t * s = s * t := by
      intro t ht
      have h1 := hc ⟨t, ht⟩
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact h1
    obtain ⟨n, hn, u, hu, rfl⟩ := exists_mul_of_mem_S0 hs
    have hact : ActsBy u (idRows 11) := by
      intro a
      rw [η_congr (toVecD_app11_idRows a)]
      have h1 := hcomm (η a) (N_le_S0 (η_mem_N a))
      have h2 : n * (u * η a * u⁻¹) = (u * η a * u⁻¹) * n :=
        N_comm' hn (conj_mem_N_of_mem_U hu a)
      have h3 : n * (u * η a * u⁻¹) * n⁻¹ = η a := by
        calc n * (u * η a * u⁻¹) * n⁻¹ = (n * u) * η a * (n * u)⁻¹ := by group
          _ = η a * (n * u) * (n * u)⁻¹ := by rw [← h1]
          _ = η a := by group
      calc u * η a * u⁻¹ = n * (u * η a * u⁻¹) * n⁻¹ := by rw [h2]; group
        _ = η a := h3
    have hu1 : u = 1 := eq_of_actsBy (U_le_K hu) (Subgroup.one_mem K) hact actsBy_one
    rw [hu1, mul_one]
    obtain ⟨i, hi, rfl⟩ := exists_η_eq hn
    have hfix : i ∈ fixedGenCols := by
      rw [fixedGenCols, List.mem_filter, List.mem_range]
      refine ⟨hi, ?_⟩
      rw [List.all_eq_true]
      intro k hk
      rw [List.mem_range] at hk
      rw [beq_iff_eq]
      have h1 : kgen k * (η i * u) = η i * u * kgen k := hcomm (kgen k) (kgen_mem_S0 ⟨k, hk⟩)
      have h2 : kgen k * η i * (kgen k)⁻¹ = η i := by
        rw [hu1, mul_one] at h1
        rw [h1]; group
      rw [kgen_acts hk i] at h2
      exact η_injOn (vecMulN_lt (genCols_lt k hk) _) hi h2
    rw [fixedGenCols_eq] at hfix
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfix
    rcases hfix with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [η_zero]; rfl
    · have hmem : η 1 ∈ S0 := N_le_S0 (η_mem_N 1)
      refine ⟨⟨η 1, hmem⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (eta_one_comm_S0 t.2)

theorem eta_one_ne_one : η 1 ≠ 1 := by
  rw [← η_zero]
  intro h
  exact absurd (η_injOn (by norm_num) (by norm_num) h) (by norm_num)

theorem card_center_S0 :
    Nat.card (Subgroup.center S0) = 2 := by
  have e := center_S0
  rw [Nat.card_congr (Subgroup.equivMapOfInjective _ S0.subtype
    (Subgroup.subtype_injective S0)).toEquiv, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq, e,
    Set.ncard_pair (Ne.symm (by rw [η_zero]; exact eta_one_ne_one))]

theorem card_center_sylow_of {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Subgroup G) (hS : Nat.card S = p ^ (Nat.card G).factorization p)
    (hZ : Nat.card (Subgroup.center S) = p) (T : Sylow p G) :
    Nat.card (Subgroup.center T) = p := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G (Sylow.ofCard S hS) T
  rw [← Nat.card_congr (Subgroup.centerCongr ((Sylow.ofCard S hS).equivSMul g)).toEquiv]
  exact hZ

theorem card_center_sylow_of_mulEquiv {G K : Type*} [Group G] [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (h : ∀ T : Sylow p G, Nat.card (Subgroup.center T) = p) (T : Sylow p K)
    (e : K ≃* G) : Nat.card (Subgroup.center T) = p := by
  have : Finite G := Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card ((T : Subgroup K).map e.toMonoidHom) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  have e' : (T : Subgroup K) ≃* (Sylow.ofCard _ hcard : Subgroup G) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  rw [Nat.card_congr (Subgroup.centerCongr e').toEquiv]
  exact h _

theorem card_center_sylow_J
    (T : Sylow 2 J) :
    Nat.card (Subgroup.center T) = 2 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J4J]; norm_num)
  exact card_center_sylow_of S0 (by rw [card_S0, factorization_card_J]) card_center_S0 T

theorem sylowTwo_centers :
    ((Subgroup.center S0).map S0.subtype : Set J) = {η 0, η 1} ∧ η 1 ≠ 1 ∧
      Nonempty (CFSG.Blueprint.NativeSporadic.J4 ≃* J) ∧
      (∀ T : Sylow 2 J, Nat.card (Subgroup.center T) = 2) ∧
      (∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.J4, Nat.card (Subgroup.center T) = 2) ∧
      ∀ (K : Type*) [Group K] [Finite K], Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.J4) →
        ∀ T : Sylow 2 K, Nat.card (Subgroup.center T) = 2 := by
  have hfin : Finite CFSG.Blueprint.NativeSporadic.J4 := fam_j4_simplicity.1
  have hJ4 : ∀ T : Sylow 2 CFSG.Blueprint.NativeSporadic.J4, Nat.card (Subgroup.center T) = 2 :=
    fun T => card_center_sylow_of_mulEquiv card_center_sylow_J T (seedEquiv j4Facts.mat)
  exact ⟨center_S0, eta_one_ne_one, ⟨seedEquiv j4Facts.mat⟩, card_center_sylow_J, hJ4,
    fun K _ _ ⟨f⟩ T => card_center_sylow_of_mulEquiv card_center_sylow_J T
      (f.trans (seedEquiv j4Facts.mat))⟩

end CFSG.Quasithin.H13.J4
