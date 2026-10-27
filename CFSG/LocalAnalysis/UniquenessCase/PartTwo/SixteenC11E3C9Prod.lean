module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9ProdA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Nine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case9_prod {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    ∃ x : MulAut (Vtil V₀ V hV), x ∈ barSub V₀ V hV D.T ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom,
        a * b = b * a) ∧
      lBar V₀ V hV L ⊓ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = ⊥ ∧
      (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map (Fstar (Mbar D.M V₀ V hV)).subtype =
        lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
      (∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom, ∀ w ∈ wTil V₀ V hV L,
        b w = w) ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, a w = w) ∧
      wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map x.toMonoidHom = ⊥ ∧
      wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map x.toMonoidHom = ⊤ ∧
      IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := s1611e3_nine_two D h.h1217 hV hc (s1611e3_nine_v1Sub h9) h9
  have h9' := h9
  obtain ⟨⟨e⟩, hL3, hs15, hsum, hsig⟩ := h9
  set A : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hA
  set Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hTb
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMb
  set F : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar (Mbar D.M V₀ V hV) with hF
  set E : Subgroup (MulAut (Vtil V₀ V hV)) := (commutator ↥F).map F.subtype with hE
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
      hc.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTsyl : IsSylowIn 2 Tb Mb :=
    s1611e3_barSub_sylow hMstab (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)
  have huniq : ∀ a ∈ Mb, ∀ b ∈ Mb, A.map (MulAut.conj a).toMonoidHom ≠ A →
      A.map (MulAut.conj b).toMonoidHom ≠ A →
      A.map (MulAut.conj a).toMonoidHom = A.map (MulAut.conj b).toMonoidHom := by
    intro a ha b hb hane hbne
    rcases hg.conj a ha with hh | hh
    · exact absurd hh hane
    · rcases hg.conj b hb with hh' | hh'
      · exact absurd hh' hbne
      · rw [hh, hh']
  have hx_exists : ∃ x ∈ Tb, A.map (MulAut.conj x).toMonoidHom ≠ A := by
    by_contra hcon
    have hstab : Tb ≤ Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
      intro φ hφ
      refine ⟨hTsyl.le hφ, ?_⟩
      exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := φ)).mpr (by
        by_contra hne
        exact hcon ⟨φ, hφ, hne⟩)
    have hidx : ((Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
        Mb).index = 2 :=
      s1611e3_relIndex_stabilizer_eq_two (K := A) (x₁ := g) hg.mem hg.ne huniq
    have hrel : Tb.relIndex (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))) *
        (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).relIndex Mb =
          Tb.relIndex Mb :=
      Subgroup.relIndex_mul_relIndex Tb
        (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))) Mb hstab inf_le_left
    have hdvd : 2 ∣ Tb.relIndex Mb := by
      rw [← hrel]
      have h2 : (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).relIndex Mb = 2 :=
        hidx
      rw [h2]
      exact dvd_mul_left 2 _
    exact hTsyl.not_dvd_relIndex hdvd
  obtain ⟨x, hxTb, hxAne⟩ := hx_exists
  have hxMb : x ∈ Mb := hTsyl.le hxTb
  have hAx : A.map (MulAut.conj x).toMonoidHom = A.map (MulAut.conj g).toMonoidHom := by
    rcases hg.conj x hxMb with hh | hh
    · exact absurd hh hxAne
    · exact hh
  have hAinf : A ⊓ A.map (MulAut.conj x).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hycenter : (⟨y, hy.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro gg
      apply Subtype.ext
      have hgy : y ∈ A.map (MulAut.conj g).toMonoidHom := by rw [← hAx]; exact hy.2
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hg.comm
      have hcy : y * (gg : MulAut (Vtil V₀ V hV)) =
          (gg : MulAut (Vtil V₀ V hV)) * y :=
        Subgroup.mem_centralizer_iff.mp (hle gg.2) y hgy
      simpa using hcy.symm
    rw [center_eq_bot_of_isL3 hL3, Subgroup.mem_bot] at hycenter
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hycenter
  obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hperfA : Group.IsPerfect ↥A :=
    s16c167_isPSL_isPerfect (s16n9b_case9_isPSL_of_isL3 hL3)
  have hAF : A ≤ F := s1611e3_lBar_le_fstar hc h9'
  have hEcard : Nat.card ↥E = 168 * 168 := by
    show Nat.card ↥((commutator ↥F).map F.subtype) = 168 * 168
    rw [Subgroup.card_map_of_injective (f := F.subtype) F.subtype_injective,
      s1611e3_commutator_card (F := ↥F) hperfA e, card_eq_of_isL3 hL3]
  have hEeq : E = ⁅F, F⁆ := Subgroup.map_subtype_commutator F
  have hAperf : ⁅A, A⁆ = A := by
    haveI : Group.IsPerfect ↥A := hperfA
    exact Subgroup.commutator_eq_self
  have hA'perf : ⁅A.map (MulAut.conj x).toMonoidHom, A.map (MulAut.conj x).toMonoidHom⁆ =
      A.map (MulAut.conj x).toMonoidHom := by
    haveI : Group.IsPerfect ↥A := hperfA
    haveI : Group.IsPerfect ↥(A.map (MulAut.conj x).toMonoidHom) :=
      Group.IsPerfect.map (f := (MulAut.conj x).toMonoidHom)
    exact Subgroup.commutator_eq_self
  have hAE : A ≤ E := by
    rw [hEeq]
    calc A = ⁅A, A⁆ := hAperf.symm
      _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hAF hAF
  have hA'F : A.map (MulAut.conj x).toMonoidHom ≤ F := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply] using hFn x hxMb a (hAF ha)
  have hA'E : A.map (MulAut.conj x).toMonoidHom ≤ E := by
    rw [hEeq]
    calc A.map (MulAut.conj x).toMonoidHom
        = ⁅A.map (MulAut.conj x).toMonoidHom, A.map (MulAut.conj x).toMonoidHom⁆ :=
          hA'perf.symm
      _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hA'F hA'F
  have hcomm : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj x).toMonoidHom, a * b = b * a := by
    intro a ha b hb
    rw [hAx] at hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hg.comm
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hAsup_card : Nat.card ↥(A ⊔ A.map (MulAut.conj x).toMonoidHom) = 168 * 168 := by
    rw [CFSG.card_sup_eq_mul_of_commute A (A.map (MulAut.conj x).toMonoidHom)
      (fun a ha b hb => hcomm a ha b hb) hAinf,
      card_eq_of_isL3 hL3,
      Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective,
      card_eq_of_isL3 hL3]
  have hE_eq : E = A ⊔ A.map (MulAut.conj x).toMonoidHom := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAE hA'E) ?_
    rw [hEcard, hAsup_card]
  have hEMb : E ≤ Mb := by
    rw [hEeq]
    exact (Subgroup.commutator_le_self F).trans hFX
  have hEnorm : (E.subgroupOf Mb).Normal :=
    (Subgroup.normal_subgroupOf_iff hEMb).2 fun hh k hhk hk =>
      s1611e3_commutator_conj_mem hFn k hk hh hhk
  have hA'norm : A.map (MulAut.conj x).toMonoidHom ≤
      Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
    have hle : A.map (MulAut.conj x).toMonoidHom ≤
        Subgroup.centralizer (A : Set (MulAut (Vtil V₀ V hV))) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.commutator_comm, hAx]
      exact hg.comm
    exact hle.trans (Subgroup.centralizer_le_normalizer (A : Set (MulAut (Vtil V₀ V hV))))
  have hEnormA : E ≤ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hE_eq]
    exact sup_le Subgroup.le_normalizer hA'norm
  have hAnormE : (A.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEnormA
  have hTEsyl : IsSylowIn 2 (Tb ⊓ E) E := IsSylowIn.inf_normal hTsyl hEMb hEnorm
  have hTEAsyl : IsSylowIn 2 ((Tb ⊓ E) ⊓ A) A := IsSylowIn.inf_normal hTEsyl hAE hAnormE
  have hsyl : IsSylowIn 2 (Tb ⊓ A) A := by
    simpa [inf_assoc, inf_eq_right.mpr hAE] using hTEAsyl
  have hWmap : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom =
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map g.toMonoidHom := by
    rw [← s15_Infra_commSub_top_map_conj A x, ← s15_Infra_commSub_top_map_conj A g, hAx]
  have hfixB : ∀ b ∈ A.map (MulAut.conj x).toMonoidHom, ∀ w ∈ wTil V₀ V hV L,
      b w = w := by
    intro b hb w hw
    rw [hAx] at hb
    have hw' : w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) A := by
      simpa [wTil, hA, lBar] using hw
    exact hg.fixB b hb w hw'
  have hfixA : ∀ a ∈ A, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, a w = w := by
    intro a ha w hw
    have hw1 : w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom := by
      simpa [wTil, hA, lBar] using hw
    have hw' : w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map g.toMonoidHom := by
      rwa [hWmap] at hw1
    exact hg.fixA a ha w hw'
  have hWinf : wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map x.toMonoidHom = ⊥ := by
    show commSub (⊤ : Subgroup (Vtil V₀ V hV)) A ⊓
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom = ⊥
    rw [hWmap]
    exact hg.inf
  have hWsup : wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map x.toMonoidHom = ⊤ := by
    show commSub (⊤ : Subgroup (Vtil V₀ V hV)) A ⊔
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom = ⊤
    rw [hWmap]
    exact hg.sup
  exact ⟨x, hxTb, hcomm, hAinf, hE_eq, hfixB, hfixA, hWinf, hWsup, hsyl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
