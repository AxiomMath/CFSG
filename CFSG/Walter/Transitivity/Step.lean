module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.Walter.Transitivity.Family
import CFSG.Walter.Transitivity.OddCore
import CFSG.Walter.Transitivity.Coprime
import CFSG.Walter.Transitivity.Generation

public section

namespace CFSG.Walter.Transitivity

open CFSG

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {Q D : Subgroup G} {q : Nat.Primes}
    (hQ : IsPiSubgroup ({q} : Set Nat.Primes) Q) (hDQ : D ≤ Q) (hne : D ≠ Q) :
    ∃ x ∈ Q, x ∈ Subgroup.normalizer (D : Set G) ∧ x ∉ D := by
  have hlt : D.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hDQ (Subgroup.subgroupOf_eq_top.mp h))
  have h := normalizerCondition_of_isPiSubgroup_singleton hQ _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hDQ] at h
  obtain ⟨x, hxN, hxD⟩ := IsConcreteLE.exists_of_lt h
  exact ⟨x, x.2, hxN, hxD⟩

omit [Finite G] in
theorem exists_conjBy_of_bridge {X T Q₁ Q₂ Q₃ : Subgroup G} {π : Set Nat.Primes} {c : G}
    (hinner : ∀ R₁ ∈ section7HStarFamily X T π, ∀ R₂ ∈ section7HStarFamily X T π,
      Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
        ∃ k : (X ⊓ Subgroup.centralizer (T : Set G) : Subgroup G), R₂ = R₁.conjBy (k : G))
    (hQ₁ : Q₁ ∈ section7HStarFamily X T π) (hQ₂ : Q₂ ∈ section7HStarFamily X T π)
    (hQ₃ : Q₃ ∈ section7HStarFamily X T π) (hc : c ∈ X ⊓ Subgroup.centralizer (T : Set G))
    (h₁ : Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (Q₁ ⊓ Q₃ : Subgroup G))
    (h₂ : Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (Q₃.conjBy c ⊓ Q₂ : Subgroup G)) :
    ∃ k : (X ⊓ Subgroup.centralizer (T : Set G) : Subgroup G), Q₂ = Q₁.conjBy (k : G) :=
  exists_conjBy_trans (exists_conjBy_trans (hinner Q₁ hQ₁ Q₃ hQ₃ h₁) ⟨⟨c, hc⟩, rfl⟩)
    (hinner _ (conjBy_mem_section7HStarFamily hc.1 hc.2 hQ₃) Q₂ hQ₂ h₂)

theorem exists_conjBy_of_not_le_normalizer {X T Q₁ Q₂ : Subgroup G} {q : Nat.Primes}
    (hTX : T ≤ X)
    (houter : ∀ Y : Subgroup G, T ≤ Y → Nat.card Y < Nat.card X →
      ConjugationActionTransitiveOn (Y ⊓ Subgroup.centralizer (T : Set G))
        (section7HStarFamily Y T ({q} : Set Nat.Primes)))
    (hinner : ∀ R₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      ∀ R₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
        ∃ k : (X ⊓ Subgroup.centralizer (T : Set G) : Subgroup G), R₂ = R₁.conjBy (k : G))
    (hQ₁ : Q₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (h₁₂ : ¬ Q₁ ≤ Q₂) (h₂₁ : ¬ Q₂ ≤ Q₁)
    (hXD : ¬ X ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G)) :
    ∃ k : (X ⊓ Subgroup.centralizer (T : Set G) : Subgroup G), Q₂ = Q₁.conjBy (k : G) := by
  let D : Subgroup G := Q₁ ⊓ Q₂
  let Y : Subgroup G := X ⊓ Subgroup.normalizer (D : Set G)
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := le_normalizer_inf hQ₁.1.2.2 hQ₂.1.2.2
  have hTY : T ≤ Y := le_inf hTX hTD
  have hYX : Nat.card Y < Nat.card X :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hXD (h.symm.le.trans inf_le_right))
  have hTnY : T ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_inf (hTX.trans Subgroup.le_normalizer) (hTD.trans Subgroup.le_normalizer)
  have hgrow : ∀ {Q : Subgroup G}, Q ∈ section7HStarFamily X T ({q} : Set Nat.Primes) →
      D ≤ Q → D ≠ Q → Q ⊓ Y ∈ section7HFamily Y T ({q} : Set Nat.Primes) ∧
        Nat.card D < Nat.card (Q ⊓ Y : Subgroup G) := by
    intro Q hQ hDQ hne
    refine ⟨⟨inf_le_right, IsPiSubgroup.of_le inf_le_left hQ.1.2.1,
      le_normalizer_inf hQ.1.2.2 hTnY⟩, ?_⟩
    obtain ⟨x, hxQ, hxN, hxD⟩ := exists_mem_normalizer_not_mem hQ.1.2.1 hDQ hne
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne
      (le_inf hDQ (le_inf (hDQ.trans hQ.1.1) Subgroup.le_normalizer)) fun heq => ?_)
    exact hxD (heq.ge ⟨hxQ, hQ.1.1 hxQ, hxN⟩)
  obtain ⟨hF₁, hc₁⟩ := hgrow hQ₁ inf_le_left fun h => h₁₂ (h.symm.le.trans inf_le_right)
  obtain ⟨hF₂, hc₂⟩ := hgrow hQ₂ inf_le_right fun h => h₂₁ (h.symm.le.trans inf_le_left)
  obtain ⟨Q₁', hQ₁', hle₁⟩ := exists_mem_section7HStarFamily_of_mem_family hF₁
  obtain ⟨Q₂', hQ₂', hle₂⟩ := exists_mem_section7HStarFamily_of_mem_family hF₂
  obtain ⟨c, hc⟩ := houter Y hTY hYX Q₁' hQ₁' Q₂' hQ₂'
  obtain ⟨Q₃, hQ₃, hle₃⟩ := exists_mem_section7HStarFamily_of_mem_family
    (section7HFamily_mono (inf_le_left : Y ≤ X) hQ₁'.1)
  have hcX : (c : G) ∈ X ⊓ Subgroup.centralizer (T : Set G) := ⟨c.2.1.1, c.2.2⟩
  refine exists_conjBy_of_bridge hinner hQ₁ hQ₂ hQ₃ hcX
    (hc₁.trans_le (Subgroup.card_le_of_le (le_inf inf_le_left (hle₁.trans hle₃))))
    (hc₂.trans_le (Subgroup.card_le_of_le (le_inf ?_ inf_le_left)))
  rw [hc] at hle₂
  exact hle₂.trans (conjBy_mono _ hle₃)

theorem exists_conjBy_of_le_normalizer {X Q₁ Q₂ V : Subgroup G} {q : Nat.Primes}
    (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G)) (hTX : (T : Subgroup G) ≤ X)
    (hVT : V ≤ T) (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ 2 = 1)
    (hVcard : 8 ≤ Nat.card V)
    (hsolv : ∀ t : G, orderOf t = 2 → Group.IsSolvable (Subgroup.centralizer ({t} : Set G)))
    (hq : q.val ≠ 2)
    (hinner : ∀ R₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      ∀ R₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
        ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
          R₂ = R₁.conjBy (k : G))
    (hQ₁ : Q₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (h₁₂ : ¬ Q₁ ≤ Q₂) (h₂₁ : ¬ Q₂ ≤ Q₁)
    (hXD : X ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G)) :
    ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
      Q₂ = Q₁.conjBy (k : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.val.Prime := ⟨q.2⟩
  have hodd : ∀ {Q : Subgroup G}, IsPiSubgroup ({q} : Set Nat.Primes) Q →
      Nat.Coprime 2 (Nat.card Q) := by
    intro Q hQ
    obtain ⟨n, hn⟩ := (isPGroup_of_isPiSubgroup_singleton hQ).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two q.2).mpr (Ne.symm hq))
  have hDle : ∀ {Q : Subgroup G}, Q ∈ section7HStarFamily X T ({q} : Set Nat.Primes) →
      Q₁ ⊓ Q₂ ≤ Q := by
    intro Q hQ
    have hmem : Q ⊔ (Q₁ ⊓ Q₂) ∈ section7HFamily X T ({q} : Set Nat.Primes) := by
      refine ⟨sup_le hQ.1.1 (inf_le_left.trans hQ₁.1.1), ?_,
        le_normalizer_sup hQ.1.2.2 (le_normalizer_inf hQ₁.1.2.2 hQ₂.1.2.2)⟩
      exact isPiSubgroup_singleton_of_isPGroup
        ((isPGroup_of_isPiSubgroup_singleton hQ.1.2.1).to_sup_of_normal_right'
          (isPGroup_of_isPiSubgroup_singleton (IsPiSubgroup.of_le inf_le_left hQ₁.1.2.1))
          (hQ.1.1.trans hXD))
    exact le_sup_right.trans (hQ.2 _ le_sup_left hmem).le
  obtain ⟨v, hvV, hv1, hv₁, hv₂⟩ := exists_ne_one_centralizer_not_le (D := Q₁ ⊓ Q₂) hVcomm
    hVexp hVcard (hodd hQ₁.1.2.1) (hodd hQ₂.1.2.1) (hVT.trans hQ₁.1.2.2) (hVT.trans hQ₂.1.2.2)
    (fun h => h₁₂ (h.trans inf_le_right)) (fun h => h₂₁ (h.trans inf_le_left))
  let C : Subgroup G := Subgroup.centralizer ({v} : Set G)
  let Y : Subgroup G := X ⊓ C
  have : Group.IsSolvable C := hsolv v (orderOf_eq_prime (hVexp v hvV) hv1)
  have : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (inf_le_right : Y ≤ C))
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm (s := (T : Subgroup G)) ht (hVT hvV))
  have hTY : (T : Subgroup G) ≤ Y := le_inf hTX hTC
  have hTnC : (T : Subgroup G) ≤ Subgroup.normalizer (C : Set G) :=
    hTC.trans Subgroup.le_normalizer
  let K : Subgroup G := (pPrimeCore 2 Y).map Y.subtype
  have hKY : K ≤ Y := Subgroup.map_subtype_le _
  have hLK : ∀ {Q : Subgroup G}, Q ∈ section7HStarFamily X T ({q} : Set Nat.Primes) →
      Q ⊓ C ≤ K := fun hQ =>
    le_map_pPrimeCore_of_sylow_le_normalizer T hTY (inf_le_inf_right C hQ.1.1)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) (hodd hQ.1.2.1))
      (le_normalizer_inf hQ.1.2.2 hTnC)
  have hcop : Nat.Coprime (Nat.card (T : Subgroup G)) (Nat.card K) := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (coprime_card_map_pPrimeCore Y)
  obtain ⟨S, hSK, hSπ, hTS, hL₁S, c, hc, hL₂S⟩ := exists_conjBy_of_coprime_action
    (hTY.trans (le_normalizer_map_pPrimeCore Y))
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKY)) hcop
    (hLK hQ₁) (hLK hQ₂) (IsPiSubgroup.of_le inf_le_left hQ₁.1.2.1)
    (IsPiSubgroup.of_le inf_le_left hQ₂.1.2.1) (le_normalizer_inf hQ₁.1.2.2 hTnC)
    (le_normalizer_inf hQ₂.1.2.2 hTnC)
  obtain ⟨Q₃, hQ₃, hSQ₃⟩ := exists_mem_section7HStarFamily_of_mem_family
    (⟨hSK.trans (hKY.trans inf_le_left), hSπ, hTS⟩ :
      S ∈ section7HFamily X T ({q} : Set Nat.Primes))
  have hcX : c ∈ X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
    ⟨(hKY.trans inf_le_left) hc.1, hc.2⟩
  refine exists_conjBy_of_bridge hinner hQ₁ hQ₂ hQ₃ hcX ?_ ?_
  · refine Subgroup.card_lt_of_lt
      (lt_of_le_of_ne (le_inf inf_le_left (hDle hQ₃)) fun heq => hv₁ ?_)
    exact (le_inf inf_le_left (hL₁S.trans hSQ₃)).trans heq.ge
  · refine Subgroup.card_lt_of_lt (lt_of_le_of_ne
      (le_inf (hDle (conjBy_mem_section7HStarFamily hcX.1 hcX.2 hQ₃)) inf_le_right)
      fun heq => hv₂ ?_)
    exact (le_inf (hL₂S.trans (conjBy_mono c hSQ₃)) inf_le_left).trans heq.ge

theorem exists_conjBy_step {X Q₁ Q₂ V : Subgroup G} {q : Nat.Primes}
    (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G)) (hTX : (T : Subgroup G) ≤ X)
    (hVT : V ≤ T) (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ 2 = 1)
    (hVcard : 8 ≤ Nat.card V)
    (hsolv : ∀ t : G, orderOf t = 2 → Group.IsSolvable (Subgroup.centralizer ({t} : Set G)))
    (hq : q.val ≠ 2)
    (houter : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Nat.card Y < Nat.card X →
      ConjugationActionTransitiveOn (Y ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
        (section7HStarFamily Y T ({q} : Set Nat.Primes)))
    (hinner : ∀ R₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      ∀ R₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
        ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
          R₂ = R₁.conjBy (k : G))
    (hQ₁ : Q₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes)) :
    ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
      Q₂ = Q₁.conjBy (k : G) := by
  by_cases h₁₂ : Q₁ ≤ Q₂
  · exact ⟨1, by rw [hQ₁.2 Q₂ h₁₂ hQ₂.1]; exact (Subgroup.conjBy_one Q₁).symm⟩
  by_cases h₂₁ : Q₂ ≤ Q₁
  · exact ⟨1, by rw [hQ₂.2 Q₁ h₂₁ hQ₁.1]; exact (Subgroup.conjBy_one Q₂).symm⟩
  by_cases hXD : X ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G)
  · exact exists_conjBy_of_le_normalizer T hT hTX hVT hVcomm hVexp hVcard hsolv hq hinner hQ₁
      hQ₂ h₁₂ h₂₁ hXD
  · exact exists_conjBy_of_not_le_normalizer hTX houter hinner hQ₁ hQ₂ h₁₂ h₂₁ hXD

end CFSG.Walter.Transitivity
