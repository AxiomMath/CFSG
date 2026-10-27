module

public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem s148_W148BenderA_mem_borel_of_conjugate_eq {P : Subgroup K} {c : K}
    (h : CFSG.conjugate P c = P) : c ∈ borel P := by
  rw [CFSG.GH74.Uniqueness.Bender.borel, Subgroup.mem_normalizer_iff]
  intro x
  have hx : x ∈ P ↔ x ∈ CFSG.conjugate P c := by rw [h]
  rw [hx, mem_conjugate_iff_mul_inv]

theorem s148_W148BenderA_conjugate_eq_iff (P : Subgroup K) (c c' : K) :
    CFSG.conjugate P c = CFSG.conjugate P c' ↔ c' * c⁻¹ ∈ borel P := by
  constructor
  · intro h
    apply s148_W148BenderA_mem_borel_of_conjugate_eq
    rw [show CFSG.conjugate P (c' * c⁻¹) =
        CFSG.conjugate (CFSG.conjugate P c') c⁻¹ from (conjugate_conjugate P c' c⁻¹).symm,
      ← h, conjugate_conjugate, mul_inv_cancel]
    exact conjugate_eq_of_mem_borel (borel P).one_mem
  · intro h
    have hP : CFSG.conjugate (CFSG.conjugate P c') c⁻¹ = P := by
      rw [conjugate_conjugate]
      exact conjugate_eq_of_mem_borel h
    calc CFSG.conjugate P c =
          CFSG.conjugate (CFSG.conjugate (CFSG.conjugate P c') c⁻¹) c := by
          rw [hP]
      _ = CFSG.conjugate P c' := by
          rw [conjugate_conjugate, inv_mul_cancel]
          exact conjugate_eq_of_mem_borel (CFSG.GH74.Uniqueness.Bender.borel _).one_mem

theorem s148_W148BenderA_coe_smul_sylow (P : Sylow 2 K) (g : K) :
    ((g • P : Sylow 2 K) : Subgroup K) = CFSG.conjugate (P : Subgroup K) g⁻¹ := by
  ext y
  rw [mem_sylow_smul_iff, mem_conjugate_iff_mul_inv, inv_inv]

theorem rootCenter_conjugate (P : Subgroup K) (c : K) :
    rootCenter (CFSG.conjugate P c) = CFSG.conjugate (rootCenter P) c := by
  rw [CFSG.conjugate, rootCenter_map, CFSG.conjugate]

theorem borel_le_normalizer_rootCenter (P : Subgroup K) :
    borel P ≤ normalizer (rootCenter P : Set K) := by
  intro d hd
  exact Subgroup.mem_normalizer_fintype fun n hn => conj_mem_rootCenter hd hn

theorem exists_sylow_eq_rootCenter_of_benderType {n i e : ℕ}
    (h : BenderType K n i e) {A : Subgroup K} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 2 ^ n) : ∃ P : Sylow 2 K, A = rootCenter (P : Subgroup K) := by
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨P, hAP⟩ := hA2.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have hle : A ≤ rootCenter (P : Subgroup K) :=
    hc.elemAbelian_le_rootCenter hAP fun x hx => by simpa [pow_two] using hA.2 x hx
  have hcard' : Nat.card (rootCenter (P : Subgroup K)) = Nat.card A := by
    rw [hc.card_center, hcard]
  exact ⟨P, Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard')⟩

theorem exists_sylow_mem_rootCenter_of_benderType {n i e : ℕ}
    (h : BenderType K n i e) {u : K} (hu : u * u = 1) :
    ∃ S : Sylow 2 K, u ∈ rootCenter (S : Subgroup K) := by
  by_cases hu1 : u = 1
  · exact ⟨default, by rw [hu1]; exact (rootCenter _).one_mem⟩
  · obtain ⟨S, hS⟩ := (show IsPGroup 2 (Subgroup.zpowers u) from
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [sq]) hu1,
          pow_one])).exists_le_sylow
    obtain ⟨t, hc⟩ := h.exists_benderCore S
    exact ⟨S, hc.center_of_involution u (le_borel _ (hS (Subgroup.mem_zpowers u)))
      (orderOf_eq_prime (by rwa [sq]) hu1)⟩

theorem exists_involution_conjugate_eq_of_benderCore {q i e : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i e P t) {x : K} (hx : x ∉ borel P) :
    ∃ s : K, s * s = 1 ∧ s ∉ borel P ∧ CFSG.conjugate P s = CFSG.conjugate P x := by
  obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hx
  refine ⟨m⁻¹ * t * m, ?_, ?_, ?_⟩
  · rw [show m⁻¹ * t * m * (m⁻¹ * t * m) = m⁻¹ * (t * t) * m by group, hc.sq_eq_one]
    group
  · intro hs
    apply hc.not_mem
    have ht : t = m * (m⁻¹ * t * m) * m⁻¹ := by group
    rw [ht]
    exact (borel P).mul_mem ((borel P).mul_mem hm hs) ((borel P).inv_mem hm)
  · have hp' : CFSG.conjugate P p = P := conjugate_eq_of_mem_borel (le_borel P hp)
    have hm' : CFSG.conjugate P m⁻¹ = P :=
      conjugate_eq_of_mem_borel ((borel P).inv_mem hm)
    calc CFSG.conjugate P (m⁻¹ * t * m)
        = CFSG.conjugate (CFSG.conjugate P m⁻¹) (t * m) := by
          rw [show m⁻¹ * t * m = m⁻¹ * (t * m) by group, conjugate_conjugate]
      _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate P m⁻¹) t) m :=
          (conjugate_conjugate (CFSG.conjugate P m⁻¹) t m).symm
      _ = CFSG.conjugate (CFSG.conjugate P t) m := by rw [hm']
      _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate P p) t) m := by rw [hp']
      _ = CFSG.conjugate (CFSG.conjugate P p) (t * m) :=
          conjugate_conjugate (CFSG.conjugate P p) t m
      _ = CFSG.conjugate P (p * (t * m)) := conjugate_conjugate P p (t * m)
      _ = CFSG.conjugate P (p * t * m) := by rw [mul_assoc]

theorem mul_mul_eq_inv_of_mem_cartan {q i : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i 1 P t) {d : K} (hd : d ∈ cartan P t) : t * d * t = d⁻¹ :=
  (hc.mem_commutator_cartan_iff.mp (hc.cartan_eq_commutator rfl ▸ hd)).2

theorem exists_conjugate_eq_conjugate_eq_of_benderCore {q i e : ℕ} {P : Sylow 2 K} {t : K}
    (hc : BenderCore q i e (P : Subgroup K) t) {x : K} (hx : x ∉ borel (P : Subgroup K))
    {S₁ S₂ : Sylow 2 K} (hS : S₁ ≠ S₂) :
    ∃ c : K, CFSG.conjugate (P : Subgroup K) c = (S₁ : Subgroup K) ∧
      CFSG.conjugate (CFSG.conjugate (P : Subgroup K) x) c = (S₂ : Subgroup K) := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq K P S₁
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq K P S₂
  have hS₁ : (S₁ : Subgroup K) = CFSG.conjugate (P : Subgroup K) a⁻¹ := by
    rw [← ha, s148_W148BenderA_coe_smul_sylow]
  have hS₂ : (S₂ : Subgroup K) = CFSG.conjugate (P : Subgroup K) b⁻¹ := by
    rw [← hb, s148_W148BenderA_coe_smul_sylow]
  have h1 : (QuotientGroup.mk (1 : K) : K ⧸ borel (P : Subgroup K)) ≠
      QuotientGroup.mk x⁻¹ := by
    intro h
    exact hx (by simpa using QuotientGroup.eq.mp h)
  have h2 : (QuotientGroup.mk a : K ⧸ borel (P : Subgroup K)) ≠
      QuotientGroup.mk b := by
    intro h
    have hab : a⁻¹ * b ∈ borel (P : Subgroup K) := QuotientGroup.eq.mp h
    have hfix : (a⁻¹ * b) • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr
        (show a⁻¹ * b ∈ Subgroup.normalizer (P : Set K) from hab)
    have hb' : b • P = a • P := by
      rw [← mul_inv_cancel_left a b, mul_smul, hfix]
    exact hS (by rw [← ha, ← hb]; exact hb'.symm)
  obtain ⟨γ, hγ1, hγ2⟩ :=
    (MulAction.is_two_pretransitive_iff.mp hc.isMultiplyPretransitive) h1 h2
  have hγ1' : (QuotientGroup.mk γ : K ⧸ borel (P : Subgroup K)) = QuotientGroup.mk a := by
    simpa [MulAction.Quotient.smul_mk] using hγ1
  have hγ2' : (QuotientGroup.mk (γ * x⁻¹) : K ⧸ borel (P : Subgroup K)) =
      QuotientGroup.mk b := by
    simpa [MulAction.Quotient.smul_mk] using hγ2
  refine ⟨γ⁻¹, ?_, ?_⟩
  · rw [hS₁]
    exact (s148_W148BenderA_conjugate_eq_iff _ _ _).mpr
      (by simpa using QuotientGroup.eq.mp hγ1'.symm)
  · rw [hS₂, conjugate_conjugate]
    exact (s148_W148BenderA_conjugate_eq_iff _ _ _).mpr
      (by simpa [mul_inv_rev] using QuotientGroup.eq.mp hγ2'.symm)

end CFSG.LocalAnalysis.WeakClosure81
