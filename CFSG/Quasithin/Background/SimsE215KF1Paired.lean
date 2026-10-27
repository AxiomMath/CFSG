module

public import CFSG.Quasithin.Background.SimsE215KF1Defs
public import CFSG.Quasithin.Vol2.E2SevenKG1
public import CFSG.Quasithin.Vol2.E2SevenPair
import CFSG.Quasithin.Background.SimsE215KF1Star
import CFSG.Quasithin.Vol2.Ch3E213MOS12
import CFSG.Quasithin.Vol2.Ch10SecQ3CWrI
import CFSG.Quasithin.Vol2.E2SevenKG1Sz

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

section Paired

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

omit [Finite G] in
theorem star_paired_M_eq {t : G} (hTH : T ≤ H) (hMH : M ≤ H)
    (htH : t ∈ H) (hM : M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) :
    E2.star M H M =
      (E2.star M H M ⊓ E2.star M H K) ⊔
        cjSub (E2P.starMap M H ⟨t, htH⟩) (E2.star M H M ⊓ E2.star M H K) ⊔
          E2.star M H T := by
  have hMKH : M ⊓ K ≤ H := inf_le_left.trans hMH
  have hctH : cjSub t (M ⊓ K) ≤ H :=
    cjSub_le (Subgroup.le_normalizer htH) hMKH
  have hstarMK : E2.star M H (cjSub t (M ⊓ K)) =
      cjSub (E2P.starMap M H ⟨t, htH⟩) (E2.star M H (M ⊓ K)) := by
    simpa only [cjSub, B6.conjSub, MulEquiv.coe_mapSubgroup] using
      (E2.star_conjSub (M := M) (H := H) (X := M ⊓ K) (g := t) htH)
  calc E2.star M H M
      = E2.star M H ((M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) :=
        congrArg (fun X : Subgroup G => E2.star M H X) hM
    _ = E2.star M H ((M ⊓ K) ⊔ cjSub t (M ⊓ K)) ⊔ E2.star M H T := by
        rw [E2.star_sup (sup_le hMKH hctH) hTH]
    _ = (E2.star M H (M ⊓ K) ⊔ E2.star M H (cjSub t (M ⊓ K))) ⊔
          E2.star M H T := by
        rw [E2.star_sup hMKH hctH]
    _ = (E2.star M H M ⊓ E2.star M H K) ⊔
          cjSub (E2P.starMap M H ⟨t, htH⟩) (E2.star M H M ⊓ E2.star M H K) ⊔
            E2.star M H T := by
        rw [E2P.star_inf_M, hstarMK, E2P.star_inf_M]

theorem pairCase_star (hS : Setting H T M V K) {t : G} (htT : t ∈ T)
    (hne : cjSub t K ≠ K) (hs : IsSimpleGroup ↥(E2.star M H K)) :
    E2.PairCase (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H T) (E2.star M H K)
      (E2P.starMap M H ⟨t, hS.hyp.minParabolic.isSylow.1 htT⟩) := by
  classical
  have hfin : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hmp : MinParabolic H T M := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  let X := E2.StarQuot M H
  let Tstar : Subgroup X := E2.star M H T
  let Kstar : Subgroup X := E2.star M H K
  have htH : t ∈ H := hTH htT
  have hY28 : E2.Hyp28 (⊤ : Subgroup X) Tstar (E2.star M H M) (E2.star M H V) :=
    hS.hyp.star (E2.sqtkGroup_top hS.sqtk)
  have hJY : kerIn (E2.star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have htstar : E2P.starMap M H ⟨t, htH⟩ ∈ Tstar := E2.starMap_mem_star htH htT
  have hJsolv : Group.IsSolvable ↥((kerIn M H).subgroupOf H) := by
    have h := E2P.isSolvable_ker_starMap hmp
    rwa [E2P.ker_starMap] at h
  have hKc : Kstar ∈ cComp (⊤ : Subgroup X) :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.mem_cComp_star hJsolv hS.mem_cComp
  have hs' : IsSimpleGroup ↥(E2.star (E2.star M H M) ⊤ Kstar) :=
    (MulEquiv.isSimpleGroup_congr (E2.equivStarOfKerInEqBot hJY le_top)).mp hs
  have hneStar : cjSub (E2P.starMap M H ⟨t, htH⟩) Kstar ≠ Kstar := by
    have hKt : cjSub t K ∈ cComp H := E2.mem_cComp_cjSub hS.mem_cComp htH
    have hneq : E2.star M H (cjSub t K) ≠ E2.star M H K :=
      CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.star_ne hJsolv hKt hS.mem_cComp hne
    have hstar_eq : E2.star M H (cjSub t K) =
        cjSub (E2P.starMap M H ⟨t, htH⟩) Kstar := by
      simpa only [cjSub, B6.conjSub, MulEquiv.coe_mapSubgroup] using
        (E2.star_conjSub (M := M) (H := H) (X := K) (g := t) htH)
    rw [← hstar_eq]
    exact hneq
  have hHK : (⊤ : Subgroup X) = Kstar ⊔ Tstar := by
    rw [← E2P.star_top M H, ← E2.star_sup hKH hTH, ← hS.eq_sup]
  exact E2.pairCase_of hY28 hJY hKc hHK htstar hneStar hs'

theorem star_inf_eq_of_paired (hmp : MinParabolic H T M) (hKs : IsSubnormal K H)
    (hKH : K ≤ H) (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    E2.star M H M ⊓ E2.star M H K =
      E2.star M H K ⊓ Subgroup.normalizer
        ((E2.star M H T ⊓ E2.star M H K : Subgroup (E2.StarQuot M H)) :
          Set (E2.StarQuot M H)) :=
  E2.star_inf_eq_of_isBorelIn' hmp
    (isSylowTwoOf_star_inf_star hmp.isSylow hKH
      (E2P.isSylowTwoOf_inf_of_subnormal hmp.isSylow hKs)) hB

theorem starCentral_of_pairedKG1 (hS : Setting H T M V K) (h1 : Case1 H T M K)
    {n : ℕ} (hn : 2 ≤ n)
    (hKG : (IsPSL 2 2 n ↥(E2.star M H K) ∧ E2.KGBenderInnerTwoL2) ∨
      (IsSz n ↥(E2.star M H K) ∧ E2.KGBenderInnerTwoSz))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    StarCentral H T M V := by
  classical
  have hfin : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hmp : MinParabolic H T M := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  obtain ⟨_, t, htT, hneK, hM⟩ := h1
  have htH : t ∈ H := hTH htT
  have hY28 : E2.Hyp28 (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H T)
      (E2.star M H M) (E2.star M H V) :=
    hS.hyp.star (E2.sqtkGroup_top hS.sqtk)
  have hJY : kerIn (E2.star M H M) (⊤ : Subgroup (E2.StarQuot M H)) = ⊥ :=
    E2P.kerIn_star M H
  have hmpY := E2P.minParabolic_star hmp
  set tq : E2.StarQuot M H := E2P.starMap M H ⟨t, htH⟩ with htqdef
  have htqT : tq ∈ E2.star M H T := E2.starMap_mem_star htH htT
  have hty : IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K) := by
    rcases hKG with ⟨hPSL, -⟩ | ⟨hSz, -⟩
    · exact Or.inl hPSL
    · exact Or.inr hSz
  have hP := pairCase_star hS htT hneK (E2.isSimpleGroup_of_psl_or_sz hty)
  have hHKq : (⊤ : Subgroup (E2.StarQuot M H)) =
      E2.star M H K ⊔ E2.star M H T :=
    (CFSG.Quasithin.Ch3E213M.OS.star_sup_eq_top (M := M) hS.eq_sup).symm
  have hMq : E2.star M H M =
      (E2.star M H M ⊓ E2.star M H K) ⊔
        cjSub tq (E2.star M H M ⊓ E2.star M H K) ⊔ E2.star M H T := by
    have h := star_paired_M_eq hTH hMH htH hM
    rwa [← htqdef] at h
  have hMKq := star_inf_eq_of_paired hmp (subnormal_of_mem_cComp hS.mem_cComp) hKH hB
  rcases hKG with ⟨hPSL, hL2⟩ | ⟨hSz, hSz2⟩
  · have hF₀ : (E2.star M H K ⊔ cjSub tq (E2.star M H K)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hP.norm)
    have hKG1 := hL2 (E2.StarQuot M H) ⊤ (E2.star M H T) (E2.star M H M)
      (E2.star M H K) tq n hmpY hJY htqT le_top hP.ne hP.norm hP.cent hP.inf hP.comm
      hHKq.symm hn hPSL hMq hMKq
    exact starCentral_of_kg1 hY28 hF₀ hKG1
  · have hF₀ : (E2.star M H K ⊔ cjSub tq (E2.star M H K)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hP.norm)
    have hKG1 := hSz2 (E2.StarQuot M H) ⊤ (E2.star M H T) (E2.star M H M)
      (E2.star M H K) tq n hmpY hJY htqT le_top hP.ne hP.norm hP.cent hP.inf hP.comm
      hHKq.symm hn hSz hMq hMKq
    exact starCentral_of_kg1 hY28 hF₀ hKG1

end Paired

theorem pkgL2PairedKF1 : PkgL2PairedKF1 := by
  intro G _ _ H T M V K hS h1 n hn hPSL hB
  exact starCentral_of_pairedKG1 hS h1 hn
    (Or.inl ⟨hPSL, E2.kgBenderInnerTwoL2_holds⟩) hB

theorem pkgSzPairedKF1 : PkgSzPairedKF1 := by
  intro G _ _ H T M V K hS h1 n hn hSz hB
  exact starCentral_of_pairedKG1 hS h1 hn
    (Or.inr ⟨hSz, E2.kgBenderInnerTwoSz_holds⟩) hB

end CFSG.Quasithin.SimsE2.KF1
