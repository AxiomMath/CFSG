module

public import CFSG.Quasithin.H13.L32ASk2
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Walter.AStar.Subnormal
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Generic

variable {Q : Type*} [Group Q]

theorem oddCore_eq_pPrimeCore : CFSG.oddCore Q = CFSG.pPrimeCore 2 Q := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

variable [Finite Q]

theorem odd_card_oddCore : Odd (Nat.card (CFSG.oddCore Q)) := by
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem le_oddCore_of_isSubnormal {S : Subgroup Q} (hS : S.IsSubnormal)
    (hodd : Odd (Nat.card S)) : S ≤ CFSG.oddCore Q := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hS
  have htop : CFSG.pPrimeCore 2 S = ⊤ := by
    apply le_antisymm le_top
    apply le_sSup
    exact ⟨Subgroup.normal_top, by rw [Subgroup.card_top]; exact Nat.coprime_two_left.mpr hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  rw [oddCore_eq_pPrimeCore]
  exact h1

end Generic

theorem sl2_exists_ne_one {p : ℕ} [Fact p.Prime] :
    ∃ y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), y ≠ 1 := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp at this

theorem fitting_ne_bot_coprime_six {X : Type} [Group X] [Finite X]
    (h : A36Case3 X ∨ A36Case4 X) :
    CFSG.fittingSubgroup X ≠ ⊥ ∧ Nat.Coprime (Nat.card ↥(CFSG.fittingSubgroup X)) 6 := by
  rcases h with ⟨p, hp, hp3, -, ⟨eF⟩, -⟩ | ⟨hgF, -, ⟨eS⟩, hprimes⟩
  · have hcard : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
      rw [Nat.card_congr (eF.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun hbot => ?_, ?_⟩
    · rw [hbot, Subgroup.card_bot] at hcard
      have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    · rw [hcard]
      refine Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h6 => ?_)
      have := Nat.le_of_dvd (by norm_num) h6
      interval_cases p <;> (revert hp h6; decide)
  · refine ⟨fun hbot => ?_, ?_⟩
    · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      obtain ⟨y, hy⟩ := sl2_exists_ne_one (p := 5)
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (eS.symm y)
      have hC := CFSG.centralizer_generalizedFitting_le X
      rw [hgF, hbot] at hC
      have hx1 : x ∈ (⊥ : Subgroup X) := hC (by
        rw [Subgroup.coe_bot, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg, one_mul, mul_one])
      rw [Subgroup.mem_bot] at hx1
      apply hy
      rw [← eS.apply_symm_apply y, ← hx, hx1, QuotientGroup.mk_one, map_one]
    · have h2 : ¬ 2 ∣ Nat.card ↥(CFSG.fittingSubgroup X) := fun h2 => by
        rcases (hprimes 2 Nat.prime_two h2).1 with h | h | h <;> norm_num at h
      have h3 : ¬ 3 ∣ Nat.card ↥(CFSG.fittingSubgroup X) := fun h3 => by
        rcases (hprimes 3 Nat.prime_three h3).1 with h | h | h <;> norm_num at h
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))

section Ambient

variable {G : Type} [Group G]

theorem subgroupOf_pCoreOf_eq_pCore (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

variable [Finite G]

theorem card_modO2Image_dvd_three {H N : Subgroup G} (hNH : N ≤ H)
    (h3 : (pCoreOf 2 N).relIndex N = 3) (hodd : Odd (Nat.card (modO2Image H N))) :
    Nat.card (modO2Image H N) ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (modO2Image H N) ∣ Nat.card N := by
    have := Subgroup.card_map_dvd (H := N.subgroupOf H) (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at this
  have hle : pCoreOf 2 N ≤ N := Subgroup.map_subtype_le _
  have h2 : Nat.card N = 3 * Nat.card (pCoreOf 2 N) := by
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 N) (K := N)
    rw [inf_eq_left.mpr hle, h3] at this
    exact this.symm
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).exists_card_eq
  rw [h2, hk] at h1
  exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_right h1

variable {T L V H : Subgroup G}

theorem isQuasisimple_cStar (h36 : A36ForSQTK) (h28 : Lemma14_7_28) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hK : K ∈ cComp H) : CFSG.IsQuasisimple (cStar K) := by
  have h := S.hyp
  have hpc : pCoreOf 2 H ≠ ⊥ := S.hz.1.2
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong h.fsu.qtke h.fsu.simple h.fsu.nonabelian
    h36 hpc hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  let e' : cStar K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore K)
  have key : CFSG.IsQuasisimple ↥(modO2Image H K) → CFSG.IsQuasisimple (cStar K) := fun hq =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e'.trans e).symm hq
  have hcase : A36Case3 ↥(modO2Image H K) ∨ A36Case4 ↥(modO2Image H K) → False := by
    intro hc
    obtain ⟨hF0, hF6⟩ := fitting_ne_bot_coprime_six hc
    set Kb := modO2Image H K with hKb
    set F := CFSG.fittingSubgroup ↥Kb with hF
    have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
    have hFn : ((F.map Kb.subtype).subgroupOf Kb).Normal := by
      rw [map_subtype_subgroupOf']
      infer_instance
    have hFs : (F.map Kb.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le F) hKbs hFn
    have hcard : Nat.card (F.map Kb.subtype) = Nat.card F :=
      Subgroup.card_map_of_injective Kb.subtype_injective
    have hodd : Odd (Nat.card (F.map Kb.subtype)) := by
      rw [hcard]
      exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) hF6)
    have hle := le_oddCore_of_isSubnormal hFs hodd
    have hone : Nat.card (F.map Kb.subtype) = 1 := by
      rcases h28 G T L V H S with h0 | h1
      · rw [h0, le_bot_iff] at hle
        rw [hle, Subgroup.card_bot]
      · rw [h1] at hle
        have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
        have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := h1 ▸ odd_card_oddCore
        have hd : Nat.card (F.map Kb.subtype) ∣ 3 :=
          (Subgroup.card_dvd_of_le hle).trans (card_modO2Image_dvd_three hL1H hL3 hoddL)
        rw [hcard] at hd ⊢
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (by norm_num) hF6) hd
    rw [hcard, Subgroup.card_eq_one] at hone
    exact hF0 hone
  rcases hA.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
  · exact key hc.1
  · exact key hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

end Ambient

end CFSG.Quasithin.H13.L32A.C
