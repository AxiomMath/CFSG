module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofFix
import CFSG.RankThree.PartTwo.Sec12.Item122
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Desc143X

theorem not_isSLThreePiAt_of_card_eq {X : Type} [Group X] (hX : Nat.card X = 1080) (q : ℕ) :
    ¬ Sec4.IsSLThreePiAt X q := by
  rintro ⟨F, _, _, ⟨hF, h3, ⟨e⟩⟩ | ⟨hF, h3, ⟨e⟩⟩⟩
  · have hc := Nat.card_congr e.toEquiv
    rw [hX, CFSG.SectionRank.OddCover.card_statedSL_three, hF] at hc
    have hq2 : 2 ≤ q := by
      rw [← hF]
      exact Finite.one_lt_card
    have hq : 4 ≤ q := by omega
    have h1 : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 15 ≤ q ^ 2 - 1 := by
      have := Nat.pow_le_pow_left hq 2
      omega
    have h4 : 63 ≤ q ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
    omega
  · have := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    have : Fact (ringChar F).Prime := ⟨hp⟩
    have hcardF : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    have hdvd : q ∣ ringChar F ^ (n : ℕ) := ⟨q, by rw [← hcardF, hF, sq]⟩
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have : CharP F (ringChar F) := ringChar.charP F
    have hc := Nat.card_congr e.toEquiv
    rw [hX, CFSG.SectionRank.OddCover.card_statedSU_three hF] at hc
    generalize ringChar F ^ m = Q at hc h3
    rcases (show Q = 2 ∨ 5 ≤ Q by omega) with rfl | hQ
    · norm_num at hc
    · have h1 : 125 ≤ Q ^ 3 := by
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
      have h2 : 24 ≤ Q ^ 2 - 1 := by
        have := Nat.pow_le_pow_left hQ 2
        omega
      have h4 : 126 ≤ Q ^ 3 + 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega

theorem false_of_isSLThreePiAt {K : Type} [Group K] [Finite K]
    (hθc : aschbacherSolvableCore 3 K ≤ Subgroup.center K)
    (h6 : Sec4.IsExtOf (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)))
    {q : ℕ} (hq : Sec4.IsSLThreePiAt K q) : False := by
  have hZ : Nat.card (Subgroup.center K) = 3 :=
    Sec12.card_center_eq_three_of_isSLThreePi ⟨q, hq⟩
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hdvd : Nat.card (aschbacherSolvableCore 3 K) ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le hθc
    rwa [hZ] at h1
  have hθ1 : Nat.card (aschbacherSolvableCore 3 K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exact (hθ3 (by rw [h])).elim
  have hK : Nat.card K = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K),
      KFacts.KS14.card_eq_of_isExtOf_alternating_six h6, hθ1]
  exact not_isSLThreePiAt_of_card_eq hK q hq

theorem false_of_isExtOf_seven {K : Type} [Group K] [Finite K]
    (h6 : Sec4.IsExtOf (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)))
    (h7 : Sec4.IsExtOf K (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) : False := by
  set θ := aschbacherSolvableCore 3 K with hθdef
  have hθn : θ.Normal := by
    obtain ⟨-, hc, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := K) Nat.prime_three
    have := hc
    exact Subgroup.normal_of_characteristic θ
  have h1080 : Nat.card (K ⧸ θ) = 1080 := KFacts.KS14.card_eq_of_isExtOf_alternating_six h6
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h7
  have hN3 : Nat.card N = 3 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hQ : Nat.card (K ⧸ N) = 2520 := by
    rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hK : Nat.card K = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hQ, hN3]
  have hKθ : Nat.card K = 1080 * Nat.card θ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ, h1080]
  have hθ7 : Nat.card θ = 7 := by omega
  have hs : IsSimpleGroup (K ⧸ N) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact eQ.isSimpleGroup
  have hn : (θ.map (QuotientGroup.mk' N)).Normal := hθn.map _ (QuotientGroup.mk'_surjective N)
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hle : θ ≤ N := by rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hθ7, hN3] at h1
    omega
  · have h1 := Subgroup.card_map_dvd θ (QuotientGroup.mk' N)
    rw [ht, Subgroup.card_top, hQ, hθ7] at h1
    omega

theorem item4_25Fix_of_le (h425 : Sec4.Item4_25Fix) {Γ : Type} [Group Γ] [Finite Γ]
    (C : Subgroup Γ) (hC4 : SectionFourHyp ↥C)
    (hCr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3) (hCθ : aschbacherSolvableCore 3 ↥C = ⊥)
    {A L K : Subgroup Γ} {d : Γ} (hAC : A ≤ C) (hLC : L ≤ C) (hA : Late.IsE27 A)
    (hW : ∀ g ∈ C, g ∈ Subgroup.normalizer (A : Set Γ) →
      g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ))
    (hLq : IsQuasisimple ↥L) (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {d}) (hKq : IsQuasisimple ↥K)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal)
    (htype : Sec4.IsExtOf (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)))
    (hcent : A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) = Subgroup.zpowers d) :
    K = L ∨ Nonempty (↥L ≃* Blueprint.NativeSporadic.J2) ∨
      (∃ p f : ℕ, Sec4.IsSLThreePiAt ↥K (p ^ f)) ∨
      Nonempty (↥L ≃* Blueprint.NativeSporadic.M24) ∨
      Sec4.IsExtOf ↥K (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)) := by
  have hdA : d ∈ A := by
    have h : d ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) := hcent ▸ Subgroup.mem_zpowers d
    exact h.1
  have hdC : d ∈ C := hAC hdA
  have hKC : K ≤ C := (hKL.trans inf_le_left).trans hLC
  set d' : ↥C := ⟨d, hdC⟩ with hd'def
  set L' : Subgroup ↥C := L.subgroupOf C with hL'def
  set A' : Subgroup ↥C := A.subgroupOf C with hA'def
  set K' : Subgroup ↥C := K.subgroupOf C with hK'def
  set M : Subgroup ↥C := L' ⊓ Subgroup.centralizer ({d'} : Set ↥C) with hMdef
  have hK'M : K' ≤ M := by
    intro x hx
    have hx' : (x : Γ) ∈ L ⊓ Subgroup.centralizer {d} := hKL hx
    refine ⟨hx'.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  set K₀ : Subgroup ↥M := K'.subgroupOf M with hK₀def
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hK'M).trans (Subgroup.subgroupOfEquivOfLe hKC)
  have hA' : Late.IsE27 A' := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
    · have h := congrArg Subtype.val
        (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
      simpa using h
    · simpa using hA.1.2 _ hx
    · rw [← hA.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hLn
  have hL' : IsComponent L' := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq,
    hL'n.isSubnormal⟩
  have hW' : Subgroup.normalizer (A' : Set ↥C) ≤
      Subgroup.normalizer (Subgroup.zpowers d' : Set ↥C) := by
    intro x hx
    have hxA : (x : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨z, hAC hz⟩).mp hz
        exact h1
      · intro hz
        have hzC : z ∈ C := by
          have h1 : (x : Γ) * z * (x : Γ)⁻¹ ∈ C := hAC hz
          have h2 := C.mul_mem (C.mul_mem (C.inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        exact (Subgroup.mem_normalizer_iff.mp hx ⟨z, hzC⟩).mpr hz
    have hxd := hW x x.2 hxA
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz : ∀ w : ↥C, w ∈ Subgroup.zpowers d' ↔ (w : Γ) ∈ Subgroup.zpowers d := by
      intro w
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, by simp [hd'def]⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa [hd'def] using hn)⟩
    rw [hz z, hz (x * z * x⁻¹)]
    simpa using Subgroup.mem_normalizer_iff.mp hxd (z : Γ)
  have hfmem : ∀ m : ↥M, ((m : ↥C) : Γ) ∈ L ⊓ Subgroup.centralizer {d} := by
    intro m
    refine ⟨m.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp m.2.2)
  let f : ↥M →* ↥(L ⊓ Subgroup.centralizer {d}) :=
    MonoidHom.codRestrict (C.subtype.comp M.subtype) (L ⊓ Subgroup.centralizer {d}) hfmem
  have hK₀eq : K₀ = (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).comap f := by
    ext m
    exact Iff.rfl
  have hK₀ : IsComponent K₀ := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq,
    hK₀eq ▸ hKsub.comap f⟩
  have hK'eq : K₀.map M.subtype = K' := Subgroup.map_subgroupOf_eq_of_le hK'M
  have htype' : Sec4.IsSLThreePi (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) (alternatingGroup (Fin 6))
        (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) (alternatingGroup (Fin 7))
        (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) Blueprint.NativeSporadic.M22
        (Multiplicative (ZMod 3)) :=
    Or.inr (Or.inl (Sec4.IsExtOf.of_mulEquiv (quotThetaEquiv eK).symm htype))
  have hcent' : A' ⊓ (K₀.map M.subtype ⊓
      Subgroup.centralizer ((K₀.map M.subtype : Subgroup ↥C) : Set ↥C)) =
      Subgroup.zpowers d' := by
    rw [hK'eq]
    ext x
    constructor
    · rintro ⟨hxA, hxK, hxc⟩
      have hx : (x : Γ) ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) := by
        refine ⟨hxA, hxK, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hxc ⟨k, hKC hk⟩ (show _ ∈ K' from hk)
        exact congrArg Subtype.val h1
      rw [hcent] at hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [hd'def] using hn)⟩
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hd : d ^ n ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) :=
        hcent ▸ zpow_mem (Subgroup.mem_zpowers d) n
      refine ⟨?_, ?_, ?_⟩
      · show ((d' ^ n : ↥C) : Γ) ∈ A
        simpa [hd'def] using hd.1
      · show ((d' ^ n : ↥C) : Γ) ∈ K
        simpa [hd'def] using hd.2.1
      · show d' ^ n ∈ Subgroup.centralizer (K' : Set ↥C)
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        have h1 := Subgroup.mem_centralizer_iff.mp hd.2.2 (k : Γ) hk
        simpa [hd'def] using h1
  rcases h425 ↥C hC4 A' hA' hCr hCθ L' hL' d' K₀ hK₀ (K₀.map M.subtype) rfl htype' hcent' hW'
    with h1 | ⟨-, ⟨φ⟩⟩ | ⟨p, f, hSL, -⟩ | ⟨⟨-, ⟨φ⟩⟩ | ⟨h7, -⟩, -⟩
  · left
    rw [hK'eq] at h1
    have h' := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left hKC, inf_of_le_left hLC] at h'
  · exact Or.inr (Or.inl ⟨eL.symm.trans φ⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨p, f, ?_⟩))
    obtain ⟨F, hF, hFf, hcase⟩ := hSL
    refine ⟨F, hF, hFf, ?_⟩
    rcases hcase with ⟨h1, h2, ⟨ψ⟩⟩ | ⟨h1, h2, ⟨ψ⟩⟩
    · exact Or.inl ⟨h1, h2, ⟨eK.symm.trans ψ⟩⟩
    · exact Or.inr ⟨h1, h2, ⟨eK.symm.trans ψ⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eL.symm.trans φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Sec4.IsExtOf.of_mulEquiv eK h7))))

end Desc143X

end CFSG.RankThree.PartTwo.Sec14
