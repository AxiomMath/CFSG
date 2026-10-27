module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private theorem heisCnt_scalarAut_comm {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (s : V ≃ₗ[F] V) (hs : s ∈ scalarAut F V) (a : V ≃ₗ[F] V) : s * a = a * s := by
  obtain ⟨c, hc⟩ := mem_scalarAut_iff.mp hs
  ext v
  simp only [LinearEquiv.mul_apply, hc v, map_smul, hc (a v)]

private theorem heisCnt_scalarAut_conj {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (s a : V ≃ₗ[F] V) (hs : s ∈ scalarAut F V) : a * s * a⁻¹ = s := by
  have h := heisCnt_scalarAut_comm s hs a
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

private theorem heisCnt_pow_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {s : V ≃ₗ[F] V} {c : F} (hc : ∀ v, s v = c • v) (n : ℕ) (v : V) :
    (s ^ n) v = (c ^ n) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

private noncomputable def heisCnt_commHom {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] (φ : G →* (V ≃ₗ[F] V))
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) (z : G) :
    G →* (V ≃ₗ[F] V) where
  toFun g := φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹
  map_one' := by simp
  map_mul' g h := by
    have hh : φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹ ∈ scalarAut F V := hcomm h z
    have hg : φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹ ∈ scalarAut F V := hcomm g z
    have hAEh : φ g * (φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹)
        = (φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹) * φ g :=
      (heisCnt_scalarAut_comm _ hh (φ g)).symm
    have hanti : φ (g * h) * φ z * (φ (g * h))⁻¹ * (φ z)⁻¹
        = (φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹) * (φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹) := by
      rw [map_mul, mul_inv_rev]
      have step1 : φ g * φ h * φ z * ((φ h)⁻¹ * (φ g)⁻¹) * (φ z)⁻¹
          = φ g * (φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹) * φ z * (φ g)⁻¹ * (φ z)⁻¹ := by
        group
      rw [step1, hAEh]
      group
    rw [hanti]
    exact (heisCnt_scalarAut_comm (φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹) hg
      (φ h * φ z * (φ h)⁻¹ * (φ z)⁻¹)).symm

private theorem heisCnt_commHom_pow {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] {p : ℕ} (φ : G →* (V ≃ₗ[F] V))
    (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) (g z : G) :
    (heisCnt_commHom φ hcomm z g) ^ p = 1 := by
  have hE : (heisCnt_commHom φ hcomm z g) ∈ scalarAut F V := hcomm g z
  have hZ : φ z ^ p ∈ scalarAut F V := hpow z
  have hEZ : (heisCnt_commHom φ hcomm z g) * φ z = φ g * φ z * (φ g)⁻¹ := by
    show (φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹) * φ z = φ g * φ z * (φ g)⁻¹
    group
  have hcommEZ : Commute (heisCnt_commHom φ hcomm z g) (φ z) := heisCnt_scalarAut_comm _ hE (φ z)
  have hconj : (φ g * φ z * (φ g)⁻¹) ^ p = (φ z) ^ p := by
    rw [← MulAut.conj_apply (φ g) (φ z)]
    rw [← map_pow (MulAut.conj (φ g)) (φ z) p]
    rw [MulAut.conj_apply, heisCnt_scalarAut_conj ((φ z) ^ p) (φ g) hZ]
  have h1 : ((heisCnt_commHom φ hcomm z g) * φ z) ^ p = (φ g * φ z * (φ g)⁻¹) ^ p := by rw [hEZ]
  rw [hcommEZ.mul_pow p, hconj] at h1
  have h1' : (heisCnt_commHom φ hcomm z g) ^ p * (φ z) ^ p = 1 * (φ z) ^ p := by
    rw [h1, one_mul]
  exact mul_right_cancel h1'

private theorem heisCnt_ker_eq {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] (φ : G →* (V ≃ₗ[F] V))
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) (z : G) :
    (heisCnt_commHom φ hcomm z).ker
      = (Subgroup.centralizer ({φ z} : Set (V ≃ₗ[F] V))).comap φ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    change φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹ = 1 at h
    have h1 : φ g * φ z * (φ g)⁻¹ = φ z := by
      have := congrArg (fun u => u * φ z) h
      simpa [mul_assoc] using this
    have h2 : φ g * φ z = φ z * φ g := by
      have := congrArg (fun u => u * φ g) h1
      simpa [mul_assoc] using this
    exact h2.symm
  · intro h
    have hz : φ z * φ g = φ g * φ z := h (φ z) (Set.mem_singleton _)
    show φ g * φ z * (φ g)⁻¹ * (φ z)⁻¹ = 1
    rw [← hz]
    group

private theorem heisCnt_index_single {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] {p : ℕ} (hp : p ≠ 0) (φ : G →* (V ≃ₗ[F] V))
    (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) (z : G) :
    ((Subgroup.centralizer ({φ z} : Set (V ≃ₗ[F] V))).comap φ).index ≠ 0 ∧
      ((Subgroup.centralizer ({φ z} : Set (V ≃ₗ[F] V))).comap φ).index ≤ p := by
  classical
  let ε := heisCnt_commHom φ hcomm z
  have hker : ε.ker = (Subgroup.centralizer ({φ z} : Set (V ≃ₗ[F] V))).comap φ :=
    heisCnt_ker_eq φ hcomm z
  have hrange_le : ε.range ≤ scalarAut F V := by
    rintro s ⟨g, rfl⟩
    exact hcomm g z
  have hpow1 : ∀ g, (ε g) ^ p = 1 := fun g => heisCnt_commHom_pow φ hpow hcomm g z
  have hcard : Nat.card ε.range ≤ p ∧ Nat.card ε.range ≠ 0 := by
    by_cases hV : Subsingleton V
    · haveI : Subsingleton V := hV
      haveI : Subsingleton ε.range := inferInstance
      haveI : Finite ε.range := Finite.of_subsingleton
      have hle : Nat.card ε.range ≤ p := by
        have hle1 : Nat.card ε.range ≤ 1 :=
          (Finite.card_le_one_iff_subsingleton).mpr inferInstance
        exact le_trans hle1 (Nat.one_le_iff_ne_zero.mpr hp)
      exact ⟨hle, Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩⟩
    · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      let roots : Finset F := (Polynomial.nthRoots p (1 : F)).toFinset
      have hrootmem : ∀ c : F, c ∈ roots ↔ c ^ p = 1 := by
        intro c
        simp only [roots, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hp)]
      let f : ε.range → roots := fun s =>
        ⟨Classical.choose (mem_scalarAut_iff.mp (hrange_le s.2)),
          (hrootmem _).mpr (by
            let c := Classical.choose (mem_scalarAut_iff.mp (hrange_le s.2))
            have hc : ∀ v, s.val v = c • v :=
              Classical.choose_spec (mem_scalarAut_iff.mp (hrange_le s.2))
            obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp s.2
            have hpv : s.val ^ p = 1 := by rw [← hg]; exact hpow1 g
            obtain ⟨v, hv⟩ := exists_ne (0 : V)
            have hcv : c ^ p • v = v := by
              have := congrArg (fun e : V ≃ₗ[F] V => e v) hpv
              simpa [heisCnt_pow_apply hc p v] using this
            have hsub : (c ^ p - 1) • v = 0 := by
              rw [sub_smul, one_smul, hcv, sub_self]
            exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hv))⟩
      have hf : Function.Injective f := by
        intro s t hst
        have hchoose : Classical.choose (mem_scalarAut_iff.mp (hrange_le s.2))
            = Classical.choose (mem_scalarAut_iff.mp (hrange_le t.2)) := congrArg Subtype.val hst
        have hval : s.val = t.val := by
          ext v
          rw [Classical.choose_spec (mem_scalarAut_iff.mp (hrange_le s.2)) v,
            Classical.choose_spec (mem_scalarAut_iff.mp (hrange_le t.2)) v, hchoose]
        exact Subtype.ext hval
      have hne : Nat.card ε.range ≠ 0 :=
        Nat.card_ne_zero.mpr ⟨⟨1⟩, Finite.of_injective f hf⟩
      refine ⟨?_, hne⟩
      calc Nat.card ε.range ≤ Nat.card roots := Nat.card_le_card_of_injective f hf
        _ = roots.card := by simp
        _ ≤ (Polynomial.nthRoots p (1 : F)).card := Multiset.toFinset_card_le _
        _ ≤ p := Polynomial.card_nthRoots p (1 : F)
  have hindex : ε.ker.index = Nat.card ε.range := Subgroup.index_ker ε
  rw [hker] at hindex
  exact ⟨by rw [hindex]; exact hcard.2, by rw [hindex]; exact hcard.1⟩

private theorem heisCnt_centralizer_pair {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (x y : V ≃ₗ[F] V) :
    Subgroup.centralizer ({x, y} : Set (V ≃ₗ[F] V))
      = Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V))
        ⊓ Subgroup.centralizer ({y} : Set (V ≃ₗ[F] V)) := by
  ext s
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨h1, h2⟩ t (rfl | ht)
    · exact h1 _ rfl
    · exact h2 _ ht

theorem index_centralizer_pair_le {F V G : Type} [Field F] [AddCommGroup V] [Module F V] [Group G]
    {p : ℕ} (hp : p ≠ 0) (φ : G →* (V ≃ₗ[F] V)) (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) (x y : G) :
    ((Subgroup.centralizer ({φ x, φ y} : Set (V ≃ₗ[F] V))).comap φ).index ≠ 0 ∧
      ((Subgroup.centralizer ({φ x, φ y} : Set (V ≃ₗ[F] V))).comap φ).index ≤ p ^ 2 := by
  have hx := heisCnt_index_single hp φ hpow hcomm x
  have hy := heisCnt_index_single hp φ hpow hcomm y
  have hpair : (Subgroup.centralizer ({φ x, φ y} : Set (V ≃ₗ[F] V))).comap φ
      = (Subgroup.centralizer ({φ x} : Set (V ≃ₗ[F] V))).comap φ ⊓
        (Subgroup.centralizer ({φ y} : Set (V ≃ₗ[F] V))).comap φ := by
    rw [← Subgroup.comap_inf, ← heisCnt_centralizer_pair]
  refine ⟨?_, ?_⟩
  · rw [hpair]
    exact Subgroup.index_inf_ne_zero hx.1 hy.1
  · rw [hpair]
    calc ((Subgroup.centralizer ({φ x} : Set (V ≃ₗ[F] V))).comap φ ⊓
            (Subgroup.centralizer ({φ y} : Set (V ≃ₗ[F] V))).comap φ).index
        ≤ ((Subgroup.centralizer ({φ x} : Set (V ≃ₗ[F] V))).comap φ).index *
          ((Subgroup.centralizer ({φ y} : Set (V ≃ₗ[F] V))).comap φ).index :=
          Subgroup.index_inf_le
      _ ≤ p * p := Nat.mul_le_mul hx.2 hy.2
      _ = p ^ 2 := (pow_two p).symm

theorem index_le_mul_index_subgroupOf {G : Type} [Group G] (K H : Subgroup G)
    (hH : H.index ≠ 0) (hK : (K.subgroupOf H).index ≠ 0) :
    K.index ≠ 0 ∧ K.index ≤ H.index * (K.subgroupOf H).index := by
  have hrel : K.relIndex H ≠ 0 := hK
  have hinf : (K ⊓ H).relIndex H * H.index = (K ⊓ H).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have hinfrel : (K ⊓ H).relIndex H = K.relIndex H := Subgroup.inf_relIndex_right K H
  have hL : (K ⊓ H).index = K.relIndex H * H.index := by rw [← hinf, hinfrel]
  have hLne : (K ⊓ H).index ≠ 0 := by rw [hL]; exact Nat.mul_ne_zero hrel hH
  have hdvd : K.index ∣ (K ⊓ H).index := Subgroup.index_dvd_of_le inf_le_left
  have hKne : K.index ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact hLne (Nat.zero_dvd.mp hdvd)
  refine ⟨hKne, ?_⟩
  calc K.index ≤ (K ⊓ H).index := Nat.le_of_dvd (Nat.pos_of_ne_zero hLne) hdvd
    _ = K.relIndex H * H.index := hL
    _ = H.index * (K.subgroupOf H).index := Nat.mul_comm _ _

end CFSG.StandardType.ClassicalPosition.HeisRank
