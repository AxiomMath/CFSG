module

public import CFSG.Quasithin.H13.L32AM51a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_odd_T (S : Setting147 G T L V H) {π : ↥H →* Perm (Fin 8)}
    (hsurj : Function.Surjective π) :
    ∃ t, ∃ ht : t ∈ T, π ⟨t, le_sup_right.trans S.hz.1.1 ht⟩ ∉ alternatingGroup (Fin 8) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  by_contra hcon
  push Not at hcon
  set D := (T.subgroupOf H).map π with hD
  have hDA : D ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨⟨t, htH⟩, ht, rfl⟩
    exact hcon t (Subgroup.mem_subgroupOf.mp ht)
  have hDi : ¬ 2 ∣ D.index := fun h => hTsyl.2.2 (h.trans (Subgroup.index_map_dvd _ hsurj))
  have hD2 : IsPGroup 2 D :=
    (hTsyl.2.1.comap_of_injective H.subtype H.subtype_injective).map π
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have h1 := D.card_mul_index
  rw [hk, Alt8.card_perm8] at h1
  have hk7 : 2 ^ 7 ∣ 2 ^ k := by
    have h2 : 2 ^ 7 ∣ 2 ^ k * D.index := by rw [h1]; norm_num
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 7
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hDi)) h2
  have hdvd : Nat.card D ∣ 20160 := by
    rw [← Alt8.card_alt8]
    exact Subgroup.card_dvd_of_le hDA
  rw [hk] at hdvd
  have := hk7.trans hdvd
  norm_num at this

theorem not_inner_of_odd {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥H →* Perm (Fin 8)}
    (hker : π.ker = CFSG.Open.pCore 2 ↥H)
    (hπK : (π.comp (Subgroup.inclusion hKH)).range = alternatingGroup (Fin 8))
    {πK : ↥K →* Lin.SLn 4} (hπs : Function.Surjective πK)
    (hkerK : ∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K) {t : G} (ht : t ∈ H)
    (hodd : π ⟨t, ht⟩ ∉ alternatingGroup (Fin 8)) :
    indHom πK hπs hkerK hKn hHN ⟨t, ht⟩ ∉
      (MulAut.conj : Lin.SLn 4 →* MulAut (Lin.SLn 4)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := hπs g
  have hβ := indHom_apply πK hπs hkerK hKn hHN ⟨t, ht⟩
  have hpi1 : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → π x = 1 := by
    intro x hx
    rw [← MonoidHom.mem_ker, hker, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
    exact hx
  have hO2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) hHN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  set m : ↥H := ⟨(k : G)⁻¹ * t, H.mul_mem (H.inv_mem (hKH k.2)) ht⟩ with hm
  have hc : ∀ k' : ↥K, π m * π (Subgroup.inclusion hKH k') =
      π (Subgroup.inclusion hKH k') * π m := by
    intro k'
    have h1 : πK (conjK (hKn ht) k') = πK k * πK k' * (πK k)⁻¹ := by
      rw [← hβ, ← hg, MulAut.conj_apply]
    have hmem : (k : G)⁻¹ * ((t * k' * t⁻¹) * k) * (k' : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem k.2) (K.mul_mem (conjK (hKn ht) k').2 k.2))
        (K.inv_mem k'.2)
    have h2 : πK ⟨_, hmem⟩ = 1 := by
      have e : (⟨_, hmem⟩ : ↥K) = k⁻¹ * (conjK (hKn ht) k' * k) * k'⁻¹ := Subtype.ext (by
        simp [conjK_apply])
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := hpi1 ⟨_, hKH hmem⟩ (hO2 ((hkerK _).mp h2))
    have e2 : (⟨_, hKH hmem⟩ : ↥H) = m * Subgroup.inclusion hKH k' * m⁻¹ *
        (Subgroup.inclusion hKH k')⁻¹ := Subtype.ext (by simp [hm, mul_assoc])
    rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc π m * π (Subgroup.inclusion hKH k')
        = (π m * π (Subgroup.inclusion hKH k') * (π m)⁻¹ * (π (Subgroup.inclusion hKH k'))⁻¹) *
          (π (Subgroup.inclusion hKH k') * π m) := by group
      _ = π (Subgroup.inclusion hKH k') * π m := by rw [h3, one_mul]
  have hcen : π m ∈ Subgroup.centralizer (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hπK] at hx
    obtain ⟨k', rfl⟩ := hx
    exact (hc k').symm
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simp), Subgroup.mem_bot] at hcen
  apply hodd
  have e3 : (⟨t, ht⟩ : ↥H) = Subgroup.inclusion hKH k * m := Subtype.ext (by simp [hm])
  rw [e3, map_mul, hcen, mul_one, ← hπK]
  exact ⟨k, rfl⟩

theorem exists_coords51 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : l1 T L V ≤ K)
    (hP : IsPSL 4 2 1 (cStar K)) {π : ↥H →* Perm (Fin 8)} (hsurj : Function.Surjective π)
    (hker : π.ker = CFSG.Open.pCore 2 ↥H)
    (hπK : (π.comp (Subgroup.inclusion (le_of_mem_cComp hK))).range = alternatingGroup (Fin 8)) :
    ∃ πK : ↥K →* Lin.SLn 4, Function.Surjective πK ∧
      (∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2) ∧
      unitriangular 4 (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map πK = Lin.par 4 2 := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  obtain ⟨πK, hπs, hkerK, hD⟩ := exists_pi_sln hP hKH hKn hTsylH
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  obtain ⟨i₀, hi₀, hi₀n, hPi⟩ := exists_node h1222 h1332 h1334 S (by norm_num) hL1K hkerK hD
  obtain ⟨t₀, ht₀T, hodd⟩ := exists_odd_T S hsurj
  obtain ⟨hU, hPst⟩ := T_maps h1332 S hKn hHN hπs hkerK hD t₀ (hTH ht₀T) ht₀T
  refine ⟨πK, hπs, hkerK, hD, ?_⟩
  rcases Lin.aut_dichotomy (by norm_num) (indHom πK hπs hkerK hKn hHN ⟨t₀, hTH ht₀T⟩) hU with
    ⟨g, hg⟩ | hswap
  · exact absurd ⟨g, hg.symm⟩ (not_inner_of_odd hKH hKn hHN hker hπK hπs hkerK (hTH ht₀T) hodd)
  · have hP' : ∀ g ∈ Lin.par 4 i₀, indHom πK hπs hkerK hKn hHN ⟨t₀, hTH ht₀T⟩ g ∈
        Lin.par 4 i₀ := by
      rw [← hPi]
      exact hPst
    have hni := Lin.eq_of_swap hswap hi₀ hi₀n hP'
    obtain rfl : i₀ = 2 := by omega
    exact hPi

end CFSG.Quasithin.H13.L32A.C
