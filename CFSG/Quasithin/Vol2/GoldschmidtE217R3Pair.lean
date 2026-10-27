module

public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

namespace E217R3

variable {G : Type} [Group G] [Finite G]

theorem exists_paired_of_case1_aux (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {H T M V K : Subgroup G} (hyp : E2.Hyp28 H T M V) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (h1 : Case1 H T M K) :
    ∃ t₀ ∈ T.subgroupOf H,
      t₀ ∉ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) ∧
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) =
        barIn M H K ⊔ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom ∧
      (∀ a ∈ barIn M H K, ∀ b ∈ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom,
        a * b = b * a) ∧
      barIn M H K ⊓ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hTH : T ≤ H := hmp.isSylow.1
  set R := CFSG.pCore 2 ↥H with hRdef
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hDdef
  have hRD : R = D := by
    rw [hDdef, kerIn_subgroupOf_top_eq hMH, h1.1,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf]
  set bar := QuotientGroup.mk' R with hbar
  set e : (↥H ⧸ R) ≃* (↥H ⧸ D) := QuotientGroup.quotientMulEquivOfEq hRD with he
  have hebar : e.toMonoidHom.comp bar = QuotientGroup.mk' D := by
    ext x
    rfl
  have hbarsurj : Function.Surjective bar := QuotientGroup.mk'_surjective R
  have hbarker : Group.IsSolvable bar.ker := by
    rw [hbar, QuotientGroup.ker_mk']
    have : Group.IsNilpotent (CFSG.pCore 2 ↥H) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  set K' := K.subgroupOf H with hK'
  have hK'c : K' ∈ cComp (⊤ : Subgroup H) := subgroupOf_mem_cComp hKc
  set Kb := K'.map bar with hKb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ R)) := map_mem_cComp_top bar hbarsurj hbarker hK'c
  have hYcat : CFSG.QuasithinUnique.Vol2Native.SQTKHypCat (↥H ⧸ R) := by
    have h := SQTKHyp.of_sqtkGroup ↥H hyp.sqtk
    exact ⟨h.finite, CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.sqt, h.kgroup, h.o2⟩
  obtain ⟨T', hT'⟩ := exists_sylow_subgroupOf hmp.isSylow
  set Tb := (T.subgroupOf H).map bar with hTb
  have hTb2 : IsPGroup 2 Tb := by
    rw [hTb, ← hT']
    exact T'.isPGroup'.map bar
  have hTbsyl : IsSylowTwoOf Tb ⊤ := by
    refine ⟨le_top, hTb2, ?_⟩
    show ¬ 2 ∣ Tb.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := (T'.mapSurjective hbarsurj).not_dvd_index
    rwa [Sylow.coe_mapSurjective, hT'] at h
  have hKTb : Kb ⊔ Tb = ⊤ := by
    rw [hKb, hTb, ← Subgroup.map_sup, subgroupOf_sup_eq_top hHK,
      Subgroup.map_top_of_surjective _ hbarsurj]
  obtain ⟨-, hA⟩ := h38 _ hYcat Kb hKbc
  rcases hA Tb hTbsyl with ⟨hn, -, -⟩ | ⟨tb, htb, htbN, -, -, hcomm, hdisj, hnorm, hsup⟩
  · exfalso
    obtain ⟨-, t, ht, hKt, -⟩ := h1
    apply hKt
    set t' : H := ⟨t, hTH ht⟩
    have h1 : (K'.map (MulAut.conj t').toMonoidHom).map bar = K'.map bar := by
      rw [map_map_conj_eq, ← hKb]
      exact (CFSG.Quasithin.A38.map_conj_eq_iff).2
        ((Subgroup.normalizer_eq_top_iff.mpr hn).symm ▸ Subgroup.mem_top _)
    have h2 : K'.map (MulAut.conj t').toMonoidHom = K' :=
      map_injOn_cComp_top bar hbarker (CFSG.Quasithin.A38.cComp_conj hK'c) hK'c h1
    have h3 := congrArg (Subgroup.map H.subtype) h2
    rw [map_map_conj_eq, hK', Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hKc)]
      at h3
    exact h3
  · obtain ⟨t₀, ht₀T, rfl⟩ := htb
    set Kb₂ := Kb.map (MulAut.conj (bar t₀)).toMonoidHom with hKb₂
    have hN : (K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom).map bar = Kb ⊔ Kb₂ := by
      rw [Subgroup.map_sup, map_map_conj_eq]
    have hNT : (Kb ⊔ Kb₂) ⊔ Tb = ⊤ := hsup ▸ hKTb
    have hNn : (Kb ⊔ Kb₂).Normal := by
      refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
      rw [← hNT]
      exact sup_le Subgroup.le_normalizer hnorm
    have hperf : ⁅K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom,
        K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom⁆ = K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom := by
      refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le ?_ ?_)
      · calc K' = ⁅K', K'⁆ := (perfect_of_mem_cComp hK'c).symm
          _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc K'.map (MulAut.conj t₀).toMonoidHom
            = ⁅K'.map (MulAut.conj t₀).toMonoidHom, K'.map (MulAut.conj t₀).toMonoidHom⁆ := by
              rw [← Subgroup.map_commutator, perfect_of_mem_cComp hK'c]
          _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right
    have hodd : (oddResidualPreimage H).map bar = Kb ⊔ Kb₂ := by
      rw [← hN]
      refine map_oddResidualPreimage_eq (CFSG.pCore_eq_open _ _).ge hperf (hN ▸ hNn) fun x => ?_
      have := hNn
      obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hTb2 hNT (bar x)
      exact ⟨k, hN ▸ hk⟩
    have hK₁ : Kb.map e.toMonoidHom = barIn M H K := by
      rw [hKb, Subgroup.map_map, hebar]
      rfl
    have hK₂ : Kb₂.map e.toMonoidHom = (barIn M H K).map
        (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom := by
      rw [hKb₂, map_map_conj_eq, hK₁]
      rfl
    refine ⟨t₀, ht₀T, fun ht₀ => htbN ?_, ?_, ?_, ?_⟩
    · rw [← CFSG.Quasithin.A38.map_conj_eq_iff, hKb, ← map_map_conj_eq,
        (CFSG.Quasithin.A38.map_conj_eq_iff).2 ht₀]
    · rw [← hK₂, ← hK₁, ← hebar, ← Subgroup.map_map, hodd, Subgroup.map_sup]
    · rw [← hK₂, ← hK₁]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : b * a = a * b :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha) b hb
      rw [← map_mul, ← map_mul, hab]
    · rw [← hK₂, ← hK₁, ← Subgroup.map_inf _ _ _ e.injective, hdisj, Subgroup.map_bot]

end E217R3

end CFSG.Quasithin
