module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem le_sup_of_pow_mem {X N T : Subgroup G} (hT : IsSylowTwoOf T X)
    (hNX : X ≤ Subgroup.normalizer (N : Set G)) (hNX' : N ≤ X)
    (hq : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : X ≤ N ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNT : N ⊔ T ≤ X := sup_le hNX' hT.1
  have hodd : ¬ 2 ∣ (N ⊔ T).relIndex X := by
    have h1 := Subgroup.relIndex_mul_relIndex T (N ⊔ T) X le_sup_right hNT
    intro hd
    have h2 : 2 ∣ T.relIndex (N ⊔ T) * (N ⊔ T).relIndex X := dvd_mul_of_dvd_right hd _
    rw [h1] at h2
    exact hT.2.2 h2
  have hpow : ∃ n : ℕ, N.relIndex X = 2 ^ n := by
    have hnorm : (N.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX').mpr hNX
    have hP : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := hq x x.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (show x ^ 2 ^ k ∈ N.subgroupOf X from hk)
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    exact ⟨n, by rw [Subgroup.relIndex, Subgroup.index, hn]⟩
  obtain ⟨n, hn⟩ := hpow
  have hdvd : (N ⊔ T).relIndex X ∣ N.relIndex X := by
    have h1 := Subgroup.relIndex_mul_relIndex N (N ⊔ T) X le_sup_left hNT
    exact Dvd.intro_left _ h1
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m = 0 := by
    by_contra hm0
    exact hodd (hm ▸ dvd_pow_self 2 hm0)
  rw [hm0, pow_zero] at hm
  exact Subgroup.relIndex_eq_one.mp hm

theorem isSylowTwoOf_inf_of_pow_mem {X N C T : Subgroup G} (hT : IsSylowTwoOf T X)
    (hNX : X ≤ Subgroup.normalizer (N : Set G)) (hNC : N ≤ C) (hCX : C ≤ X)
    (hq : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : IsSylowTwoOf (T ⊓ C) C := by
  have hNX' : N ≤ X := hNC.trans hCX
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hT.1.trans hNX
  have hXNT := le_sup_of_pow_mem hT hNX hNX' hq
  set P := T ⊓ C with hP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hTN
  have hCNP : C ≤ N ⊔ P := by
    intro x hx
    obtain ⟨n, hn, t, ht, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hTN).1 (hXNT (hCX hx))
    have htC : t ∈ C := by
      have := C.mul_mem (C.inv_mem (hNC hn)) hx
      simpa using this
    exact Subgroup.mul_mem_sup hn ⟨ht, htC⟩
  have hNPC : N ⊔ P = C := le_antisymm (sup_le hNC inf_le_right) hCNP
  set I := N ⊓ T with hI
  have hIN : I ≤ N := inf_le_left
  have hIP : I ≤ P := fun x hx => ⟨hx.2, hNC hx.1⟩
  have hNP : N ⊓ P = I := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.1⟩
    · intro hx
      exact ⟨hx.1, hx.2, hNC hx.1⟩
  have hIpos : 0 < I.relIndex P :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := I.subgroupOf P))
  have h1 : N.relIndex C = I.relIndex P := by
    have e1 : N.relIndex C = N.relIndex (P ⊔ N) := by rw [sup_comm, hNPC]
    have e2 := A4.relIndex_sup_eq_of_le_normalizer' (D := N) (T := P) hPN
    have e3 : N.relIndex P = I.relIndex P := by
      rw [← Subgroup.inf_relIndex_right N P, hNP]
    rw [e1, e2, e3]
  have h2 := Subgroup.relIndex_mul_relIndex I N C hIN hNC
  have h3 := Subgroup.relIndex_mul_relIndex I P C hIP inf_le_right
  have h4 : I.relIndex N = P.relIndex C := by
    apply Nat.eq_of_mul_eq_mul_left hIpos
    rw [h1] at h2
    rw [mul_comm (I.relIndex P) (I.relIndex N), h2, h3]
  have hSyl := A4.isSylowTwoOf_inf_normal hT hNX' hNX
  have hodd : ¬ 2 ∣ P.relIndex C := by
    rw [← h4]
    have : T ⊓ N = I := inf_comm T N
    rw [this] at hSyl
    exact hSyl.2.2
  exact ⟨inf_le_right, hT.2.1.to_inf_left, hodd⟩

theorem isSylowTwoOf_of_normalizer_le {X C P : Subgroup G} (hPC : IsSylowTwoOf P C) (hCX : C ≤ X)
    (hN : ∀ x ∈ X, x ∈ Subgroup.normalizer (P : Set G) → x ∈ C) : IsSylowTwoOf P X := by
  rw [A4.isSylowTwoOf_iff_maximal] at hPC ⊢
  obtain ⟨hPC1, hP2, hmaxC⟩ := hPC
  refine ⟨hPC1.trans hCX, hP2, fun Q hQX hQ hPQ => ?_⟩
  by_contra hQP
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hQP (h ▸ le_rfl))
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hPtop : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    apply hQP
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ P.subgroupOf Q := by rw [h]; exact Subgroup.mem_top _
    exact this
  obtain ⟨q, hq, hqP⟩ := IsConcreteLE.exists_of_lt (hnc _ hPtop)
  have hqN : (q : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhQ : h ∈ Q
    · have := (Subgroup.mem_normalizer_iff.mp hq) ⟨h, hhQ⟩
      exact this
    · constructor
      · intro hh
        exact absurd (hPQ.trans le_rfl |> fun _ => (hlt.le hh)) hhQ
      · intro hh
        apply absurd _ hhQ
        have h1 : (q : G) * h * (q : G)⁻¹ ∈ Q := hlt.le hh
        have := Q.mul_mem (Q.mul_mem (Q.inv_mem q.2) h1) q.2
        simpa [mul_assoc] using this
  have hqC : (q : G) ∈ C := hN q (hQX q.2) hqN
  have hP'Q : P ⊔ Subgroup.zpowers (q : G) ≤ Q := sup_le hlt.le (Subgroup.zpowers_le.mpr q.2)
  have hP'2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers (q : G)) := hQ.to_le hP'Q
  have hP'C : P ⊔ Subgroup.zpowers (q : G) ≤ C :=
    sup_le hPC1 (Subgroup.zpowers_le.mpr hqC)
  have hle := hmaxC _ hP'C hP'2 le_sup_left
  exact hqP (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

end Sylow

end S143

end CFSG.Quasithin
