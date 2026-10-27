module

public import CFSG.Quasithin.EmptyFaithful.S146E1
public import CFSG.Quasithin.Background.F918C0
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

section Interface

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem isQuasisimple_of_perfect_of_isSimpleGroup {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup Q) : CFSG.IsQuasisimple Q := by
  have := hs
  have hnt : Nontrivial Q := hs.toNontrivial
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.2 fun y _ => hcon y x
    have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [_root_.commutator_def] at this
    rw [h1] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (Subgroup.mem_bot.1 (hc ▸ Subgroup.mem_top x))
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩

omit [Finite G] in
theorem conjClosure_sup_le {K T H : Subgroup G} (hK : K ≤ H) (hT : T ≤ H) :
    conjClosure K T ⊔ T ≤ H :=
  sup_le (conjClosure_le fun _ ht _ hz => H.mul_mem (H.mul_mem (hT ht) (hK hz)) (H.inv_mem (hT ht)))
    hT

theorem Setting146.sqtkGroup_of_isHTM (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    SQTKGroup ↥H :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.qtke hH.1.2,
    kGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian hH.1.2⟩

theorem Setting146.isHTM_conjClosure_sup (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting146 G T M) {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) :
    IsHTM T M (conjClosure K T ⊔ T) := by
  have hHT : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hTH : T ≤ mcOf T := hHT.1.1
  have hle : conjClosure K T ⊔ T ≤ mcOf T := conjClosure_sup_le hKH hTH
  refine ⟨⟨le_sup_right, ?_⟩, fun hM => S.not_le_M_of_cComp h37 h38 hHT hK
    (((le_conjClosure K T).trans le_sup_left).trans hM)⟩
  have hsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (conjClosure K T ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((isSylowTwoOf_pCoreOf_le hsyl).trans le_sup_right)
      (hle.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  intro h0
  exact hHT.1.2 (le_bot_iff.mp (h0 ▸ h1))

theorem hypF918_of_setting146 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (S : Setting146 G T M)
    {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) (hs : IsSimpleGroup (KBar K)) :
    HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (conjClosure K T ⊔ T) K := by
  have hHTM := S.isHTM_conjClosure_sup h37 h38 hK
  have hF := S.lemma_14_5_14 (S.isHz_iff.mpr hHTM)
  have hKH : K ≤ conjClosure K T ⊔ T := (le_conjClosure K T).trans le_sup_left
  have hHle : conjClosure K T ⊔ T ≤ mcOf T :=
    conjClosure_sup_le (le_of_mem_cComp hK) (S.isHTM_mcOf).1.1
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
  refine ⟨hF.2, cComp_mem_of_le hK hKH hHle, ?_, ?_, HypF918.K₀T_le_normalizer_K₀ T K⟩
  · exact isQuasisimple_of_perfect_of_isSimpleGroup
      (Group.IsPerfect.ofSurjective (G := K) (G' := KBar K)
        (f := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) (QuotientGroup.mk'_surjective _)) hs
  · exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right (le_inf le_sup_right le_sup_right)))
      (sup_le le_sup_left inf_le_right)

end Interface

end CFSG.Quasithin
