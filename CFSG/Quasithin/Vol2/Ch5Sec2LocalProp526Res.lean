module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528STr
public import CFSG.Quasithin.H13.U4ParTorus
public import CFSG.Quasithin.H13.NQCatG2RadTorus
import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclNB
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Orient
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2B
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Snd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Amalgam

variable {G : Type} [Group G] {Y : Type} [Group Y]

theorem isYAmalgamPair_swap {T M₁ M₂ : Subgroup Y} (h : IsYAmalgamPair T M₁ M₂) :
    IsYAmalgamPair T M₂ M₁ :=
  ⟨h.1, h.2.1.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem irred_full_transport {G₁ : Subgroup G} {M : Subgroup Y} (e : ↥G₁ ≃* ↥M)
    (h2 : ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore M) → M ≤ Subgroup.normalizer (W : Set Y) →
        W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M)) :
    ∀ W : Subgroup G, centerOf (pCoreOf 2 (perfectCore G₁)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore G₁) → G₁ ≤ Subgroup.normalizer (W : Set G) →
        W = centerOf (pCoreOf 2 (perfectCore G₁)) ∨ W = pCoreOf 2 (perfectCore G₁) := by
  obtain ⟨K', -, -, hQg, hQf, hZg, hZf⟩ := model_data e
  have hg : Function.Injective G₁.subtype := G₁.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hQ₀ : pCoreOf 2 (perfectCore G₁) ≤ G₁ := by
    rw [hQg]
    exact (Subgroup.map_le_range _ _).trans (le_of_eq (Subgroup.range_subtype G₁))
  have hGtop : (⊤ : Subgroup ↥G₁).map G₁.subtype = G₁ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hMtop : (⊤ : Subgroup ↥G₁).map (M.subtype.comp e.toMonoidHom) = M := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro W hZW hWQ hGW
  obtain ⟨W', rfl⟩ := exists_map_subtype_of_le hQ₀ hWQ
  rw [hZg, Subgroup.map_le_map_iff_of_injective hg] at hZW
  rw [hQg, Subgroup.map_le_map_iff_of_injective hg] at hWQ
  have hGW' : (⊤ : Subgroup ↥G₁).map G₁.subtype ≤
      Subgroup.normalizer ((W'.map G₁.subtype : Subgroup G) : Set G) := by
    rw [hGtop]
    exact hGW
  rw [map_le_normalizer_map_iff _ hg] at hGW'
  have hMW : M ≤ Subgroup.normalizer ((W'.map (M.subtype.comp e.toMonoidHom) : Subgroup Y) :
      Set Y) := by
    have h := (map_le_normalizer_map_iff _ hf _ _).mpr hGW'
    rw [hMtop] at h
    exact h
  rcases h2 (W'.map (M.subtype.comp e.toMonoidHom))
      ((le_of_eq hZf).trans (Subgroup.map_mono hZW))
      ((Subgroup.map_mono hWQ).trans (le_of_eq hQf.symm)) hMW with h | h
  · left
    rw [hZf] at h
    rw [hZg, Subgroup.map_injective hf h]
  · right
    rw [hQf] at h
    rw [hQg, Subgroup.map_injective hf h]

theorem irred_full_of_amalgam_g2
    {G₁ G₂ : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsG2Over f))
    (hsp : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore G₁))) :
    ∀ W : Subgroup G, centerOf (pCoreOf 2 (perfectCore G₁)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore G₁) → G₁ ≤ Subgroup.normalizer (W : Set G) →
        W = centerOf (pCoreOf 2 (perfectCore G₁)) ∨ W = pCoreOf 2 (perfectCore G₁) := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ := h
  have hY' : IsLieOverTwo .G2 0 f Y := by
    rcases hY with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  exact irred_full_transport φ.φ1 (NQCat.G2Rad.parabolic_irred_full hf hY'
    (isSpecialPow_model φ.φ1 hsp) (isYAmalgamPair_swap hpair))

theorem irred_full_of_amalgam_u4 {G₁ G₂ : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G₁ G₂) (IsLieOverTwo .PSU 4 f) ∨
      IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups G₁ G₂))
    (hsp : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore G₁))) :
    ∀ W : Subgroup G, centerOf (pCoreOf 2 (perfectCore G₁)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore G₁) → G₁ ≤ Subgroup.normalizer (W : Set G) →
        W = centerOf (pCoreOf 2 (perfectCore G₁)) ∨ W = pCoreOf 2 (perfectCore G₁) := by
  rcases h with ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ |
      ⟨Y₀, _, Y, _, ι, hY₀, hι, hidx, T, M₁, M₂, hpair, ⟨φ⟩⟩
  · exact irred_full_transport φ.φ1 (U4Par.parabolic_irred_full hf (Or.inl hY)
      (isYAmalgamPair_swap hpair) (isSpecialPow_model φ.φ1 hsp))
  · exact irred_full_transport φ.φ1 (U4Par.parabolic_irred_full hf
      (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩) (isYAmalgamPair_swap hpair)
      (isSpecialPow_model φ.φ1 hsp))

end Amalgam

variable {G : Type} [Group G] [Finite G]

theorem stmt5_2_6_L2K_rank2_res_of
    (h331 : Stmt3_3_1) (hRL : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2)
    (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4) : Stmt5_2_6_L2K_rank2_res := by
  intro G _ _ T M L V H B D L₂ n k hyp hk _ ⟨P, hP, hL₂P⟩ hpsl hcard he hsec
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : L2RankOneSylowFact := NQCat.l2RankOneSylowFact_holds
  set S := sec52S M H with hSdef
  set K := oTwoUpper H with hKdef
  set R₀ := pCoreOf 2 K ⊓ L₂ with hR₀def
  have hL₂P' : L₂ ≤ P :=
    IsSubnormal.rec (motive := fun A B _ => A ≤ B) (fun _ => le_rfl)
      (fun hle _ _ ih => hle.trans ih) hL₂P.2.2.1
  have hL₂K : L₂ ≤ K := hL₂P'.trans hP.1
  have hL₂q : IsL2Quot k (oTwoQuot ↥L₂) :=
    isL2Quot_oTwoQuot_of_lieModel (by omega) (Or.inl ⟨by decide, hpsl⟩)
  obtain ⟨h111', hq', hSn', hns1', hns2'⟩ := hyp.f112_hyps hF11 hbor h524 (Or.inr ⟨rfl, rfl⟩)
  have hlist : F112ListALegacyBare L₂ L S := by
    unfold F112ListALegacyBare
    rcases he with he | he
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
  have hab := stmt5_2_6_second_holds G L₂ L S h111' hq' hSn' hns1' hns2' hlist hsec
  set B' := bigB L₂ L S with hB'
  have h111R := Hyp111R.of_hyp111 hRL h111'
  have hBN : B' ≤ Subgroup.normalizer (L₂ : Set G) := (F1.bigB_le_normalizer_left h111R).1
  have hG1core : perfectCore (L₂ ⊔ B') = L₂ := by
    have hAn : (L₂.subgroupOf (L₂ ⊔ B')).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hBN)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111R))
      (le_perfectCore_of_perfect le_sup_left hL₂P.2.1)
  have hBeq := (hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)).2.2
  have hBK : B' ≤ Subgroup.normalizer (K : Set G) := by
    rw [hB', bigB_swap L L₂ S, hBeq]
    refine sup_le (sup_le hyp.D_le ?_) ?_
    · exact ((pCoreOf_le 2 _).trans inf_le_right).trans (le_normalizer_oTwoUpper H)
    · exact (inf_le_right.trans hL₂K).trans Subgroup.le_normalizer
  have hG1R₀ : L₂ ⊔ B' ≤ Subgroup.normalizer (R₀ : Set G) := by
    have h1 : L₂ ⊔ B' ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      sup_le (hL₂K.trans (le_normalizer_pCoreOf 2 K))
        (hBK.trans (normalizer_le_normalizer_pCoreOf 2 K))
    have h2 : L₂ ⊔ B' ≤ Subgroup.normalizer (L₂ : Set G) := sup_le Subgroup.le_normalizer hBN
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  set Q := pCoreOf 2 L₂ with hQdef
  have hR₀Q : R₀ ≤ Q :=
    le_pCoreOf 2 inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        (le_sup_left.trans hG1R₀))
      ((pCoreOf_isPGroup 2 K).to_le inf_le_left)
  obtain ⟨f, hf, hfk, hsp, hirr⟩ : ∃ f : ℕ, 2 ≤ f ∧ f = k ∧ IsSpecialPow 2 (2 ^ f) 2 ↥Q ∧
      ∀ W : Subgroup G, centerOf Q ≤ W → W ≤ Q →
        L₂ ⊔ B' ≤ Subgroup.normalizer (W : Set G) → W = centerOf Q ∨ W = Q := by
    rcases hab with ⟨-, -, hSL₂, -⟩ | hext
    · rcases he with ⟨f, hf, hA, hq1, -, hsp, -⟩ | ⟨f, hf, hA, hq1, hsp, -⟩
      · rw [sup_eq_left.mpr hSL₂] at hsp
        have hsp' : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore (L₂ ⊔ B'))) := by
          rw [hG1core]
          exact hsp
        have hirr := irred_full_of_amalgam_g2 hf hA hsp'
        rw [hG1core] at hirr
        exact ⟨f, hf, eq_of_isL2Quot (by omega) (by omega) hq1 hL₂q, hsp, hirr⟩
      · have hsp' : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore (L₂ ⊔ B'))) := by
          rw [hG1core]
          exact hsp
        have hirr := irred_full_of_amalgam_u4 hf hA hsp'
        rw [hG1core] at hirr
        exact ⟨f, hf, eq_of_isL2Quot (by omega) (by omega) hq1 hL₂q, hsp, hirr⟩
    · obtain ⟨f, hf, hA, hq1, hsp, -⟩ := hext
      have hsp' : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore (L₂ ⊔ B'))) := by
        rw [hG1core]
        exact hsp
      have hirr := irred_full_of_amalgam_u4 hf (Or.inr hA) hsp'
      rw [hG1core] at hirr
      exact ⟨f, hf, eq_of_isL2Quot (by omega) (by omega) hq1 hL₂q, hsp, hirr⟩
  subst hfk
  have hZQ : centerOf Q ≤ Q := inf_le_left
  have hQZ : L₂ ⊔ B' ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) := fun g hg =>
    NQCat.G2Rad.mem_normalizer_centerOf
      (normalizer_le_normalizer_pCoreOf 2 L₂ ((sup_le Subgroup.le_normalizer hBN) hg))
  have hWN : L₂ ⊔ B' ≤ Subgroup.normalizer ((R₀ ⊔ centerOf Q : Subgroup G) : Set G) :=
    Rk2.le_normalizer_sup hG1R₀ hQZ
  have hcZ : Nat.card ↥(centerOf Q) = 2 ^ f := by rw [card_centerOf_eq, hsp.2.2]
  have hcQ : Nat.card ↥Q = 2 ^ (5 * f) := by
    rw [hsp.2.1, ← pow_mul]
    ring_nf
  have hf3 : f < 3 * f := by omega
  rcases hirr _ le_sup_right (sup_le hR₀Q hZQ) hWN with hW | hW
  ·
    have hle := Subgroup.card_le_of_le (le_sup_left.trans hW.le : R₀ ≤ centerOf Q)
    rw [hcard, hcZ] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  ·
    have hRZ : R₀ ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) := fun g hg =>
      NQCat.G2Rad.mem_normalizer_centerOf (Subgroup.le_normalizer (hR₀Q hg))
    have hprod := Sec526.card_sup_mul_card_inf_of_normalizes hRZ
    rw [hW, hcQ, hcard, hcZ] at hprod
    have hpos : 0 < Nat.card ↥(R₀ ⊓ centerOf Q) := Nat.card_pos
    have hle : 2 ^ (5 * f) ≤ 2 ^ (3 * f) * 2 ^ f := by
      calc 2 ^ (5 * f) ≤ 2 ^ (5 * f) * Nat.card ↥(R₀ ⊓ centerOf Q) :=
            Nat.le_mul_of_pos_right _ hpos
        _ = 2 ^ (3 * f) * 2 ^ f := hprod
    rw [← pow_add] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega

end CFSG.Quasithin.H13
