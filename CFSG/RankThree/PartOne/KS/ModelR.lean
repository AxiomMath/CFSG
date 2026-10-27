module

public import CFSG.RankThree.PartOne.KS.Lines

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open scoped Pointwise commutatorElement

theorem autModel_of_conj_equiv {M : Type*} [Group M] {P R : Subgroup M} (hPR : P ≤ R)
    (hN : (P.subgroupOf R).Normal) (e : R ≃* MulAut P)
    (he : ∀ (x : R) (p : P), ((e x p : P) : M) = x * p * (x : M)⁻¹) : AutModel P R where
  le := hPR
  conj_mem := fun x hx p hp => by
    have := hN.conj_mem ⟨p, hPR hp⟩ (Subgroup.mem_subgroupOf.2 hp) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 this
  surj := fun α => by
    obtain ⟨x, hx⟩ := e.surjective α
    exact ⟨x, x.2, fun p => by rw [← hx]; exact he x p⟩
  inj := fun x hx hc => by
    have h1 : e ⟨x, hx⟩ = e 1 := by
      refine MulEquiv.ext fun p => Subtype.ext ?_
      rw [he, map_one, MulAut.one_apply]
      show x * (p : M) * x⁻¹ = p
      rw [hc p p.2]
      group
    exact congrArg Subtype.val (e.injective h1)

theorem eq_or_eq_of_card_le_two_mul {M : Type*} [Group M] [Finite M] {P R B : Subgroup M}
    (hPB : P ≤ B) (hBR : B ≤ R) (hidx : Nat.card R ≤ 2 * Nat.card P) : B = P ∨ B = R := by
  have h1 : Nat.card P ∣ Nat.card B := Subgroup.card_dvd_of_le hPB
  have h2 : Nat.card B ∣ Nat.card R := Subgroup.card_dvd_of_le hBR
  have hP : 0 < Nat.card P := Nat.card_pos
  have hB : 0 < Nat.card B := Nat.card_pos
  have hR : 0 < Nat.card R := Nat.card_pos
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; omega
    · exact h
  have hkm : k * m ≤ 2 := by
    have : Nat.card P * (k * m) ≤ Nat.card P * 2 := by
      calc Nat.card P * (k * m) = Nat.card R := by rw [← mul_assoc, ← hk, ← hm]
        _ ≤ 2 * Nat.card P := hidx
        _ = Nat.card P * 2 := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hP
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · left
    have : k = 1 := by omega
    subst this
    exact (Subgroup.eq_of_le_of_card_ge hPB (by omega)).symm
  · right
    have hm1 : m = 1 := by
      by_contra hne
      have : 2 ≤ m := by omega
      have : 2 * 2 ≤ k * m := Nat.mul_le_mul hk2 this
      omega
    subst hm1
    exact Subgroup.eq_of_le_of_card_ge hBR (by omega)

theorem mem_normalizer_of_mem_R {M : Type*} [Group M] [Finite M] {P R B : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) (hPB : P ≤ B) (hBR : B ≤ R) {g : M}
    (hg : g ∈ R) : g ∈ normalizer (B : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  rcases eq_or_eq_of_card_le_two_mul hPB hBR hidx with hB | hB
  · rw [hB]
    intro b
    constructor
    · exact fun hb => h.conj_mem g hg b hb
    · intro hb
      have := h.conj_mem g⁻¹ (R.inv_mem hg) _ hb
      simpa [mul_assoc] using this
  · rw [hB]
    intro b
    constructor
    · exact fun hb => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hb) (Subgroup.inv_mem _ hg)
    · intro hb
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hb) hg
      simpa [mul_assoc] using this

theorem map_conj_eq_self_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext z
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * z * g)
  simpa [mul_assoc] using this

theorem card_core_conj_normalizer {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) {g : M} (hg : g ∈ normalizer (B : Set M)) (y' : M) :
    Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({g * y' * g⁻¹} : Set M))) =
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y'} : Set M))) := by
  have hBconj : B.map (MulAut.conj g).toMonoidHom = B := map_conj_eq_self_of_mem_normalizer hg
  have hmap : (B ⊓ centralizer ({y'} : Set M)).map (MulAut.conj g).toMonoidHom =
      B ⊓ centralizer ({g * y' * g⁻¹} : Set M) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hBconj,
      map_centralizer_singleton_mulEquiv (MulAut.conj g) y']
    simp [MulAut.conj_apply]
  have h1 := SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv hp (MulAut.conj g)
    (B ⊓ centralizer ({y'} : Set M))
  rw [hmap] at h1
  rw [← h1]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem core_bot_of_lines_R {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {ι : Type*}
    {xs : ι → M} (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      ∀ B : Subgroup M, P ≤ B → B ≤ R →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({xs i} : Set M)) = ⊥) :
    ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M)) = ⊥ := by
  refine core_bot_of_lines hp hSyl hlines fun j B hPB hBR => ?_
  obtain ⟨i, ⟨g, hg, hgx⟩, hi⟩ := hrep j
  have h1 := card_core_conj_normalizer hp B (mem_normalizer_of_mem_R h hidx hPB hBR hg) (xs i)
  rw [hgx, hi B hPB hBR, Subgroup.card_bot] at h1
  exact Subgroup.card_eq_one.mp h1

theorem core_bot_of_record_five {M : Type*} [Group M] [Finite M] {P R C A B : Subgroup M} {x : M}
    (hC : C = centralizer ({x} : Set M) ⊓ R) (hAC : A ≤ C) (hAn : (A.subgroupOf C).Normal)
    (hAP : A ≤ P) (hAexp : Monoid.exponent A = 5) (hAcent : centralizer (A : Set M) ⊓ C ≤ A)
    (hPB : P ≤ B) (hBR : B ≤ R) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  have hAp : IsPGroup 5 A := fun g => ⟨1, by
    rw [pow_one, ← hAexp]
    exact Monoid.pow_exponent_eq_one g⟩
  have hCR : R ⊓ centralizer ({x} : Set M) = C := by rw [hC, inf_comm]
  refine line_core_bot_of_normal_pgroup Nat.prime_five (P := P) (R := R) hPB hBR hAP hAp
    (hAC.trans (hC.le.trans inf_le_left)) ?_ ?_
  · rw [hCR]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).1 hAn
  · rw [hCR, inf_comm]
    exact hAp.to_le hAcent

theorem core_bot_of_record_derived {M : Type*} [Group M] [Finite M] {P R C B : Subgroup M}
    {x : M} (hC : C = centralizer ({x} : Set M) ⊓ R) (hDs : IsSimpleGroup (⁅C, C⁆ : Subgroup M))
    (hDnab : ∃ g ∈ (⁅C, C⁆ : Subgroup M), ∃ h ∈ (⁅C, C⁆ : Subgroup M), g * h ≠ h * g)
    (hDP : (⁅C, C⁆ : Subgroup M) ≤ P)
    (hcard : Nat.card (centralizer ((⁅C, C⁆ : Subgroup M) : Set M) ⊓ C : Subgroup M) = 5)
    (hPB : P ≤ B) (hBR : B ≤ R) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  have hDq : IsQuasisimple (⁅C, C⁆ : Subgroup M) := by
    have := hDs
    obtain ⟨g, hg, h, hh, hne⟩ := hDnab
    exact isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩
  have hCR : R ⊓ centralizer ({x} : Set M) = C := by rw [hC, inf_comm]
  refine line_core_bot_of_normal_component Nat.prime_five (P := P) (R := R) hPB hBR hDP hDq
    (((commutator_self_le C).trans (hC.le.trans inf_le_left))) ?_ ?_
  · rw [hCR]
    exact le_normalizer_commutator_self C
  · rw [hCR, inf_comm]
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])

end CFSG.RankThree.PartOne
