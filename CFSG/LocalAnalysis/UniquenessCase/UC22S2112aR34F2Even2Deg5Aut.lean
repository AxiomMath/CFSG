module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.ComponentInitial

private theorem uc22s2112r34_deg5aut_pow_val_add {K : Type} [Field K] {u : Kˣ}
    (hu : orderOf u = 5) (a b : ZMod 5) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_mod_orderOf u (a.val + b.val), hu]

private noncomputable def uc22s2112r34_deg5aut_coord {K : Type} [Field K] (u : Kˣ)
    (hu : orderOf u = 5) : Multiplicative (Fin 4 → ZMod 5) →* (Fin 5 → Kˣ) :=
  { toFun := fun v i => if h : (i : ℕ) < 4 then u ^ (v.toAdd ⟨i, h⟩).val else 1
    map_one' := by
      funext i
      by_cases h : (i : ℕ) < 4
      · rw [dif_pos h]
        have h1 : (1 : Multiplicative (Fin 4 → ZMod 5)).toAdd = 0 := rfl
        rw [h1, Pi.zero_apply, ZMod.val_zero, pow_zero]
        rfl
      · rw [dif_neg h]
        rfl
    map_mul' := by
      intro a b
      funext i
      by_cases h : (i : ℕ) < 4
      · rw [dif_pos h, Pi.mul_apply, dif_pos h, dif_pos h]
        have h1 : (a * b).toAdd = a.toAdd + b.toAdd := rfl
        rw [h1, Pi.add_apply, uc22s2112r34_deg5aut_pow_val_add hu]
      · rw [dif_neg h, Pi.mul_apply, dif_neg h, dif_neg h, mul_one] }

private theorem uc22s2112r34_deg5aut_coord_lt {K : Type} [Field K] {u : Kˣ}
    (hu : orderOf u = 5) (v : Multiplicative (Fin 4 → ZMod 5)) {i : Fin 5}
    (h : (i : ℕ) < 4) :
    uc22s2112r34_deg5aut_coord u hu v i = u ^ (v.toAdd ⟨i, h⟩).val := dif_pos h

private theorem uc22s2112r34_deg5aut_coord_ge {K : Type} [Field K] {u : Kˣ}
    (hu : orderOf u = 5) (v : Multiplicative (Fin 4 → ZMod 5)) {i : Fin 5}
    (h : ¬ (i : ℕ) < 4) : uc22s2112r34_deg5aut_coord u hu v i = 1 := dif_neg h

private noncomputable def uc22s2112r34_deg5aut_diag {K : Type} [Field K] (u : Kˣ)
    (hu : orderOf u = 5) : Multiplicative (Fin 4 → ZMod 5) →* GL (Fin 5) K :=
  (Units.map (Matrix.diagonalRingHom (Fin 5) K).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin 5 => K)).symm.toMonoidHom.comp
      (uc22s2112r34_deg5aut_coord u hu))

private theorem uc22s2112r34_deg5aut_diag_apply {K : Type} [Field K] {u : Kˣ}
    (hu : orderOf u = 5) (v : Multiplicative (Fin 4 → ZMod 5)) (i : Fin 5) :
    ((uc22s2112r34_deg5aut_diag u hu v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
      ((uc22s2112r34_deg5aut_coord u hu v i : Kˣ) : K) := by
  rw [show ((uc22s2112r34_deg5aut_diag u hu v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal (((MulEquiv.piUnits (M := fun _ : Fin 5 => K)).symm
        (uc22s2112r34_deg5aut_coord u hu v) : (Fin 5 → K)ˣ) : Fin 5 → K) from rfl]
  rw [Matrix.diagonal_apply_eq]
  rfl

private theorem uc22s2112r34_deg5aut_eq_one_of_scalar {K : Type} [Field K] {u : Kˣ}
    (hu : orderOf u = 5) {v : Multiplicative (Fin 4 → ZMod 5)} {c : Kˣ}
    (h : (uc22s2112r34_deg5aut_diag u hu v : GL (Fin 5) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 5) c) :
    v = 1 := by
  have hc1 : c = 1 := by
    have h' := congrArg (fun A : GL (Fin 5) K =>
      ((A : Matrix (Fin 5) (Fin 5) K) ⟨4, by norm_num⟩ ⟨4, by norm_num⟩)) h
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      uc22s2112r34_deg5aut_diag_apply,
      uc22s2112r34_deg5aut_coord_ge hu v
        (by norm_num : ¬ ((⟨4, by norm_num⟩ : Fin 5) : ℕ) < 4)] at h'
    exact Units.ext h'.symm
  have hkey : ∀ i : Fin 4, u ^ (v.toAdd i).val = 1 := by
    intro i
    have hji : ((⟨i.val, by have := i.isLt; omega⟩ : Fin 5) : ℕ) < 4 := i.isLt
    have h' := congrArg (fun A : GL (Fin 5) K =>
      ((A : Matrix (Fin 5) (Fin 5) K) ⟨i.val, by have := i.isLt; omega⟩
        ⟨i.val, by have := i.isLt; omega⟩)) h
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      uc22s2112r34_deg5aut_diag_apply, uc22s2112r34_deg5aut_coord_lt hu v hji] at h'
    have h2 : ((u ^ (v.toAdd i).val : Kˣ) : K) = 1 := by
      rw [h', hc1]
      simp
    exact Units.ext (by simpa using h2)
  have hzero : v.toAdd = 0 := by
    funext i
    have hd := orderOf_dvd_of_pow_eq_one (hkey i)
    rw [hu] at hd
    have hlt := ZMod.val_lt (v.toAdd i)
    exact (ZMod.val_eq_zero _).1 (by omega)
  exact Multiplicative.toAdd.injective (by rw [hzero]; rfl)

private theorem uc22s2112r34_deg5aut_le_sup_zpowers {G : Type} [Group G] {I D : Subgroup G}
    {α : G} (hID : I ≤ D) (hαD : α ∈ D) (hαI : α ∉ I) (h1 : I.relIndex D ∣ 5) :
    D ≤ I ⊔ Subgroup.zpowers α := by
  have hJD : I ⊔ Subgroup.zpowers α ≤ D := sup_le hID (Subgroup.zpowers_le.2 hαD)
  have hrel := Subgroup.relIndex_mul_relIndex (H := I) (K := I ⊔ Subgroup.zpowers α) (L := D)
    le_sup_left hJD
  have hne : I.relIndex (I ⊔ Subgroup.zpowers α) ≠ 1 := by
    intro h
    exact hαI ((Subgroup.relIndex_eq_one.1 h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers α)))
  have hdvd : (I ⊔ Subgroup.zpowers α).relIndex D ∣ 5 :=
    (dvd_mul_left _ _).trans (hrel.symm ▸ h1)
  have hnot5 : (I ⊔ Subgroup.zpowers α).relIndex D ≠ 5 := by
    intro h5'
    rw [h5'] at hrel
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h1 with h | h <;> rw [h] at hrel <;>
      omega
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exact Subgroup.relIndex_eq_one.1 h
  · exact absurd h hnot5


private theorem uc22s2112r34_deg5aut_card_four :
    Nat.card (Multiplicative (Fin 4 → ZMod 5)) = 5 ^ 4 := by
  show Nat.card (Fin 4 → ZMod 5) = 5 ^ 4
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem uc22s2112r34_deg5aut_pow_five (a : Multiplicative (Fin 4 → ZMod 5)) :
    a ^ 5 = 1 := by
  have hsmul : ∀ x : ZMod 5, (5 : ℕ) • x = 0 := by decide
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  show (5 : ℕ) • a.toAdd = Multiplicative.toAdd 1
  rw [show (Multiplicative.toAdd (1 : Multiplicative (Fin 4 → ZMod 5))) = 0 from rfl]
  funext i
  exact hsmul (a.toAdd i)

private theorem uc22s2112r34_deg5aut_transport {X Y A : Type} [Group X] [Group Y] [Group A]
    (e : X ≃* Y) (α : MulAut X) (φ' : A →* MulAut Y) (hinj : Function.Injective φ')
    (hrange : φ'.range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner Y ⊔
      Subgroup.zpowers (MulAut.congr e α)) :
    ∃ φ : A →* MulAut X, Function.Injective φ ∧
      φ.range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner X ⊔
        Subgroup.zpowers α := by
  have hinner : (CFSG.ComponentClassification.OuterAutomorphisms.inner Y).map
      (MulAut.congr e).symm.toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    have h := congrArg (Subgroup.map (MulAut.congr e).symm.toMonoidHom)
      (CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e)
    rw [Subgroup.map_map,
      show ((MulAut.congr e).symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom) =
          MonoidHom.id (MulAut X)
        from MonoidHom.ext fun x => MulEquiv.symm_apply_apply (MulAut.congr e) x,
      Subgroup.map_id] at h
    exact h.symm
  refine ⟨(MulAut.congr e).symm.toMonoidHom.comp φ',
    (MulAut.congr e).symm.injective.comp hinj, ?_⟩
  rw [MonoidHom.range_comp]
  refine (Subgroup.map_mono hrange).trans ?_
  rw [Subgroup.map_sup, hinner, MonoidHom.map_zpowers,
    show (MulAut.congr e).symm.toMonoidHom (MulAut.congr e α) = α
      from MulEquiv.symm_apply_apply (MulAut.congr e) α]

private theorem uc22s2112r34_deg5aut_four_le_pRank {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {ψ : Multiplicative (Fin 4 → ZMod 5) →* G} (hψ : Function.Injective ψ)
    (hrange : ψ.range ≤ H) : 4 ≤ CFSG.Open.pRank 5 H :=
  CFSG.SectionRank.le_pRank_of_injective (p := 5) (k := 4) (by norm_num)
    (fun a b => mul_comm a b) uc22s2112r34_deg5aut_pow_five
    uc22s2112r34_deg5aut_card_four ψ hψ hrange

theorem deg5_exists_injective_linear {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ∣ p ^ f - 1) (h5f : ¬ 5 ∣ f)
    {α : MulAut (LinearFlag.projectiveSL 5 K)} (hα : α ^ 5 = 1)
    (hαI : α ∉ (MulAut.conj : LinearFlag.projectiveSL 5 K →*
      MulAut (LinearFlag.projectiveSL 5 K)).range) :
    ∃ φ : Multiplicative (Fin 4 → ZMod 5) →* MulAut (LinearFlag.projectiveSL 5 K),
      Function.Injective φ ∧
        φ.range ≤ (MulAut.conj : LinearFlag.projectiveSL 5 K →*
          MulAut (LinearFlag.projectiveSL 5 K)).range ⊔ Subgroup.zpowers α := by
  classical
  have hKfin : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hMfin : Finite (MulAut (LinearFlag.projectiveSL 5 K)) :=
    Finite.of_injective
      (fun e : MulAut (LinearFlag.projectiveSL 5 K) =>
        (e : LinearFlag.projectiveSL 5 K → LinearFlag.projectiveSL 5 K))
      fun a b hab => MulEquiv.ext (congrFun hab)
  have hR := (LinearFlag.automorphism_generation (K := K) (n := 5) (by norm_num)).1
  have h1 : (MulAut.conj : LinearFlag.projectiveSL 5 K →*
      MulAut (LinearFlag.projectiveSL 5 K)).range.relIndex
        (LinearFlag.linearAutGroup 5 K) ∣ 5 :=
    (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := 5) (by norm_num)).trans
      (Nat.gcd_dvd_left 5 (Nat.card K - 1))
  have hDn : (LinearFlag.linearAutGroup 5 K).Normal := by
    obtain ⟨-, -, hDnorm, -, -, -, -, -, -, -⟩ :=
      LinearFlag.standard_outer_quotients (n := 5) (K := K)
    rw [hR] at hDnorm
    exact ⟨fun d hd g => hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hDindex : (LinearFlag.linearAutGroup 5 K).index ∣ 2 * f := by
    have hDE : LinearFlag.linearAutGroup 5 K ≤ LinearFlag.semilinearAutGroup 5 K :=
      LinearFlag.linearAutGroup_le_semilinearAutGroup
    obtain ⟨-, -, -, -, -, -, -, hRE, -, -⟩ :=
      LinearFlag.standard_outer_quotients (n := 5) (K := K)
    rw [hR] at hRE
    have hE : LinearFlag.semilinearAutGroup 5 K =
        LinearFlag.linearAutGroup 5 K ⊔ (LinearFlag.fieldAut 5 K).range := by
      rw [LinearFlag.semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq,
        ← MonoidHom.coe_range, Subgroup.closure_eq]
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality hp hf hK
    have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have h2 : (LinearFlag.linearAutGroup 5 K).relIndex
        (LinearFlag.semilinearAutGroup 5 K) ∣ f := by
      rw [hE, Subgroup.relIndex_sup_left, ← hcard]
      refine (Subgroup.index_dvd_card _).trans ?_
      rw [← Subgroup.index_ker]
      exact Subgroup.index_dvd_card _
    have h3 : (LinearFlag.semilinearAutGroup 5 K).index ∣ 2 := by
      have hle : (LinearFlag.semilinearAutGroup 5 K).index ≤ 2 := by
        rwa [← Subgroup.relIndex_top_right]
      have h0 : (LinearFlag.semilinearAutGroup 5 K).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      rcases (by omega : (LinearFlag.semilinearAutGroup 5 K).index = 1 ∨
          (LinearFlag.semilinearAutGroup 5 K).index = 2) with h | h <;> rw [h]
      · exact one_dvd 2
    calc (LinearFlag.linearAutGroup 5 K).index
        = (LinearFlag.linearAutGroup 5 K).relIndex (LinearFlag.semilinearAutGroup 5 K) *
            (LinearFlag.semilinearAutGroup 5 K).index :=
          (Subgroup.relIndex_mul_index hDE).symm
      _ ∣ f * 2 := Nat.mul_dvd_mul h2 h3
      _ = 2 * f := by ring
  have hαD : α ∈ LinearFlag.linearAutGroup 5 K := by
    have := hDn
    have h5' : ¬ 5 ∣ 2 * f := by
      intro h
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h with h2 | h2
      · omega
      · exact h5f h2
    have hcop : Nat.Coprime (LinearFlag.linearAutGroup 5 K).index (orderOf α) := by
      have hord : orderOf α ∣ 5 := orderOf_dvd_of_pow_eq_one hα
      have h25 : Nat.Coprime (2 * f) 5 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 h5').symm
      exact (h25.coprime_dvd_left hDindex).coprime_dvd_right hord
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ α) m
  have hDleJ : LinearFlag.linearAutGroup 5 K ≤
      (MulAut.conj : LinearFlag.projectiveSL 5 K →*
        MulAut (LinearFlag.projectiveSL 5 K)).range ⊔ Subgroup.zpowers α :=
    uc22s2112r34_deg5aut_le_sup_zpowers
      (LinearFlag.standard_outer_quotients (n := 5) (K := K)).1 hαD hαI h1
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, orderOf u = 5 := by
    have hcardU : 5 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      exact h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact exists_prime_orderOf_dvd_card' 5 hcardU
  have hφinj : Function.Injective ((LinearFlag.conjAut 5 K).comp
      (uc22s2112r34_deg5aut_diag u hu)) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [MonoidHom.comp_apply] at hv
    obtain ⟨c, hc⟩ := (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (n := 5) (by norm_num)
      (uc22s2112r34_deg5aut_diag u hu v) 1 (by rw [map_one, mul_one]; exact hv)).2
    exact uc22s2112r34_deg5aut_eq_one_of_scalar hu hc.symm
  refine ⟨(LinearFlag.conjAut 5 K).comp (uc22s2112r34_deg5aut_diag u hu), hφinj, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hDleJ (LinearFlag.conjAut_mem_linearAutGroup (uc22s2112r34_deg5aut_diag u hu v))

theorem deg5_exists_injective_unitary {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (h5 : 5 ∣ p ^ f + 1) (h5f : ¬ 5 ∣ f)
    {α : MulAut (UnitaryHigher.primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))}
    (hα : α ^ 5 = 1)
    (hαI : α ∉ (MulAut.conj : UnitaryHigher.primeFormP h
      ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →* MulAut (UnitaryHigher.primeFormP h
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range) :
    ∃ φ : Multiplicative (Fin 4 → ZMod 5) →*
        MulAut (UnitaryHigher.primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)),
      Function.Injective φ ∧
        φ.range ≤ (MulAut.conj : UnitaryHigher.primeFormP h
          ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →* MulAut (UnitaryHigher.primeFormP h
            ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ⊔ Subgroup.zpowers α := by
  classical
  have hfin : Finite K := h.finite
  let C : Matrix (Fin 5) (Fin 5) K := ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  have hC : UnitaryHigher.IsPrimeFormGram (1 : GL (Fin 5) K) := UnitaryHigher.isPrimeFormGram_one
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ p ^ f = 2) := by omega
  obtain ⟨-, -, hker1, -, -, -, hFsurj', hFker, hDnorm, hinn, -⟩ :=
    UnitaryHigher.unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, -, hcardDI, -, -, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order h hn hq
  have hIDrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (UnitaryHigher.primeFormP h C)).relIndex (UnitaryHigher.primeFormD h C) = 5 := by
    rw [show (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (UnitaryHigher.primeFormP h C)).relIndex (UnitaryHigher.primeFormD h C) =
        Nat.card (UnitaryHigher.primeFormD h C ⧸
          (CFSG.ComponentClassification.OuterAutomorphisms.inner
            (UnitaryHigher.primeFormP h C)).subgroupOf (UnitaryHigher.primeFormD h C)) from rfl]
    rw [hcardDI, Nat.gcd_eq_left h5]
  have h1 : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (UnitaryHigher.primeFormP h C)).relIndex (UnitaryHigher.primeFormD h C) ∣ 5 := by
    rw [hIDrel]
  have hDn : (UnitaryHigher.primeFormD h C).Normal := hDnorm
  have hDindex : (UnitaryHigher.primeFormD h C).index = 2 * f := by
    rw [← hFker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hFsurj', Subgroup.card_top]
    exact (card_ringAut_and_isCyclic h.prime K h.card).1
  have hαD : α ∈ UnitaryHigher.primeFormD h C := by
    have h5' : ¬ 5 ∣ 2 * f := by
      intro hh
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 hh with h2 | h2
      · omega
      · exact h5f h2
    have hcop : Nat.Coprime (UnitaryHigher.primeFormD h C).index (orderOf α) := by
      have hord : orderOf α ∣ 5 := orderOf_dvd_of_pow_eq_one hα
      have h25 : Nat.Coprime (2 * f) 5 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 h5').symm
      have hdvd : (UnitaryHigher.primeFormD h C).index ∣ 2 * f := by rw [hDindex]
      exact (h25.coprime_dvd_left hdvd).coprime_dvd_right hord
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ α) m
  have hDleJ : UnitaryHigher.primeFormD h C ≤
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (UnitaryHigher.primeFormP h C)) ⊔ Subgroup.zpowers α := by
    refine uc22s2112r34_deg5aut_le_sup_zpowers
      (I := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (UnitaryHigher.primeFormP h C))
      (D := UnitaryHigher.primeFormD h C) ?_ hαD hαI h1
    intro x hx
    obtain ⟨s, hs⟩ := (hinn x).1 hx
    exact ⟨⟨s, s.2.1⟩, hs.symm⟩
  obtain ⟨x, hx⟩ : ∃ x : ↥((Units.map h.normHom).ker), orderOf x = 5 := by
    have hker : 5 ∣ Nat.card ↥((Units.map h.normHom).ker) := by
      rw [(unitary_field_norm h).2.2.1]
      exact h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact exists_prime_orderOf_dvd_card' 5 hker
  let u : Kˣ := (x : Kˣ)
  have hu : orderOf u = 5 := by
    change orderOf (x : Kˣ) = 5
    rw [Subgroup.orderOf_coe x]
    exact hx
  have hbarnorm : ∀ y : Kˣ, h.norm (y : K) = 1 → h.bar (y : K) * (y : K) = 1 := by
    intro y hy
    have h2 : h.norm (y : K) = (y : K) * h.bar (y : K) := rfl
    rw [h2] at hy
    rw [mul_comm]
    exact hy
  have hnorm_pow : ∀ k : ℕ, h.norm (((u ^ k : Kˣ) : K)) = 1 := fun k =>
    (h.mem_ker_normUnits).1 (Subgroup.pow_mem _ x.2 k)
  have hmemU : ∀ v : Multiplicative (Fin 4 → ZMod 5),
      uc22s2112r34_deg5aut_diag u hu v ∈ UnitaryHigher.primeFormUnitary h C := by
    intro v
    rw [UnitaryHigher.mem_primeFormUnitary]
    rw [show ((uc22s2112r34_deg5aut_diag u hu v : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal
          (fun i : Fin 5 => ((uc22s2112r34_deg5aut_coord u hu v i : Kˣ) : K)) from rfl]
    have hC1 : C = (1 : Matrix (Fin 5) (Fin 5) K) := rfl
    rw [hC1, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : (i : ℕ) < 4
    · rw [uc22s2112r34_deg5aut_coord_lt hu v hi]
      exact hbarnorm _ (hnorm_pow _)
    · rw [uc22s2112r34_deg5aut_coord_ge hu v hi, Units.val_one, map_one, one_mul]
  let φU : Multiplicative (Fin 4 → ZMod 5) →* UnitaryHigher.primeFormUnitary h C :=
    { toFun := fun v => ⟨uc22s2112r34_deg5aut_diag u hu v, hmemU v⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  let φ : Multiplicative (Fin 4 → ZMod 5) →* MulAut (UnitaryHigher.primeFormP h C) :=
    (UnitaryHigher.primeFormConjHom h C).comp φU
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hconj1 : ∀ A : UnitaryHigher.primeFormUnitary h C,
        UnitaryHigher.primeFormConjHom h C A = 1 ↔
          ∃ c : Kˣ, h.norm (c : K) = 1 ∧
            (A : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
      intro A
      have e := hker1 ⟨A, 1⟩
      rw [UnitaryHigher.primeFormPsi_apply, map_one, mul_one] at e
      rw [e]
      exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩
    obtain ⟨c, -, hc⟩ := (hconj1 ⟨_, hmemU v⟩).1 hv
    exact uc22s2112r34_deg5aut_eq_one_of_scalar hu hc
  refine ⟨φ, hφinj, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hDleJ ⟨⟨_, hmemU v⟩, rfl⟩

theorem four_le_pRank_of_not_inner_deg5 {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {p f : ℕ} (hp : p.Prime) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel X t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) (h5f : ¬ 5 ∣ f) {α : MulAut X} (hα : α ^ 5 = 1)
    (hαI : α ∉ (MulAut.conj : X →* MulAut X).range) :
    4 ≤ CFSG.Open.pRank 5 ((MulAut.conj : X →* MulAut X).range ⊔ Subgroup.zpowers α) := by
  classical
  have hXc : StatedClassicalModel X t 5 p f := hX.statedClassicalModel_of_ne_zero (by norm_num)
  have hf : 1 ≤ f := hX.admissible.2.1
  have hpow5 : ∀ {Y : Type} [Group Y] (e : X ≃* Y), MulAut.congr e α ^ 5 = 1 := by
    intro Y _ e
    rw [← map_pow (MulAut.congr e) α 5, hα, map_one]
  have hmem : ∀ {Y : Type} [Group Y] (e : X ≃* Y),
      MulAut.congr e α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := by
    intro Y _ e hmem
    have h := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
    rw [← h, Subgroup.mem_map] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    have hxa : x = α := (MulAut.congr e).injective hxe
    rw [hxa] at hx
    exact hαI hx
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hXc
    have h5' : 5 ∣ p ^ f - 1 := h5.trans (Nat.gcd_dvd_right 5 (p ^ f - 1))
    have eP : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) K :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 K).symm
    have e' : X ≃* LinearFlag.projectiveSL 5 K :=
      eP.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 K)
    obtain ⟨φ, hφ, hrange⟩ := deg5_exists_injective_linear hp hf hK h5' h5f
      (hpow5 e') (hmem e')
    obtain ⟨ψ, hψ, hψrange⟩ := uc22s2112r34_deg5aut_transport e' α φ hφ hrange
    exact uc22s2112r34_deg5aut_four_le_pRank hψ hψrange
  · obtain ⟨⟨-, -, hadm⟩, K, _, _, hK, ⟨e⟩⟩ := hXc
    have h5' : 5 ∣ p ^ f + 1 := h5.trans (Nat.gcd_dvd_right 5 (p ^ f + 1))
    have hq' : ¬(5 = 3 ∧ p ^ f = 2) := by omega
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have e' : X ≃* ClassicalGroups.UnitaryFlag.unitaryPSU h 5 :=
      e.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm
    obtain ⟨eT⟩ := (UnitaryHigher.unitary_full_diagonal_outer_order h (by norm_num) hq').1
    have eY : X ≃* UnitaryHigher.primeFormP h
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := e'.trans eT.symm
    obtain ⟨φ, hφ, hrange⟩ := deg5_exists_injective_unitary h h5' h5f (hpow5 eY) (hmem eY)
    obtain ⟨ψ, hψ, hψrange⟩ := uc22s2112r34_deg5aut_transport eY α φ hφ hrange
    exact uc22s2112r34_deg5aut_four_le_pRank hψ hψrange

end CFSG.LocalAnalysis.UniquenessCase.UC22
