module

public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecQ4C3
public import CFSG.Quasithin.Vol2.Ch10SecFH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem perm_seven_pow_three : ∀ σ : Equiv.Perm (Fin 7), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  intro σ h9
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd] at h9 ⊢
  intro n hn
  have h1 := Equiv.Perm.two_le_of_mem_cycleType hn
  have h2 : n ≤ 7 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin 7))
  have h3 := h9 n hn
  interval_cases n <;> omega

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_nine (J : Subgroup G)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 7)) :
    ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 ↥J with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal (p := 2) (G := ↥J)
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := ↥J)
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hcard : Nat.card ↥J = Nat.card Q * 2520 := by
    rw [← Q.card_mul_index, Subgroup.index, ← hA7]
    exact congrArg _ (Nat.card_congr e.toEquiv)
  have hdvd : 3 ^ 2 ∣ Nat.card ↥J := by
    rw [hcard]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hPQ : P ⊓ Q = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hP, hk]
    exact Nat.Coprime.pow _ _ (by norm_num)
  let π : ↥J →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hπ : ∀ x : ↥J, π x = 1 → x ∈ Q := by
    intro x hx
    have h1 : (QuotientGroup.mk' Q x) = 1 := by
      have := congrArg e.symm hx
      simpa [π] using this
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    have h9 : x ^ 9 = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨x, hx⟩)
      rw [hP] at this
      exact congrArg Subtype.val this
    have hπ9 : ((π x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 9 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, h9, map_one, Subgroup.coe_one]
    have hπ3 : π (x ^ 3) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact perm_seven_pow_three _ hπ9)
    have hmem : x ^ 3 ∈ P ⊓ Q := ⟨P.pow_mem hx 3, hπ _ hπ3⟩
    rw [hPQ] at hmem
    exact hmem
  have hcomm : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP
  refine ⟨P.map J.subtype, Subgroup.map_subtype_le P, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have := congrArg (fun z : ↥P => ((z : ↥J) : G)) (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩
    have := congrArg Subtype.val (hexp a ha)
    simpa using this
  · rw [Subgroup.card_map_of_injective J.subtype_injective, hP]
    norm_num

variable {T L I : Subgroup G}

theorem stmt10_2_2_four (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (hO2 : Obl10_2_1E4A314)
    (hO3 : Obl10_2_2FourS5) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  by_cases hsyl : IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T)
  · obtain ⟨R₀, hR₀, hR₀S, hnorm⟩ := h311 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow _ H (baum T) (inH_normalizer_baum hyp) hH.1
      ⟨_, SecB.isUniqueMaxOver_of_isHStar h331 hyp hH⟩ (SecE.baum_ne_bot hyp) inf_le_left hsyl
      le_rfl
    apply hR₀
    refine le_bot_iff.mp (hbot ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hnorm
      (hyp.fsu.sylow.1.to_le (hR₀S.trans inf_le_left)))
    exact (hR₀S.trans Subgroup.le_normalizer).trans le_sup_left
  · obtain ⟨h2, K, hK, hKs, hKa, X, J, hXs, hT1, hJ, hKJ, hT1J, hm3⟩ :=
      hO3 G T L I hyp h12 H hH hZH hsyl hbot
    rcases (hO2 G T L I hyp h2 K hK hKs hKa X J hXs hT1 hJ hKJ hT1J).2 with
      ⟨⟨e⟩, -⟩ | ⟨-, ⟨z₀, hz₀J, hz₀C, hz₀3⟩, -⟩
    · obtain ⟨E, hEJ, hEab, hE9⟩ := exists_elemAbelian_nine J e
      have := hm3 E hEJ hEab
      omega
    ·
      obtain ⟨E, hEJ, hEab, hE3⟩ :=
        C10E4.exists_elemAbelian_gt_three hKJ.le hKa hz₀J hz₀C hz₀3
      have := hm3 E hEJ hEab
      omega

end CFSG.Quasithin.Vol2.Ch10.SecF
