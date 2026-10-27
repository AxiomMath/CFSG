module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Orbit
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w4Thm14_1_unique (hKL : KL32PairRank) (hKI : KInvolGen) (hKS : KSimpleGen2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hcomp : IsComponentOf L Y) (hL3 : IsL3 ↥L 1)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV H = ⊥)
    (hm : E3.mParam Y = 4) :
    ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X' := by
  classical
  have hHc : H = ⨆ X ∈ conjSet L Y, X := by rw [hH, iSup_conjSet_eq_biSup_conj]
  obtain ⟨hbi, hLH, hHY, hn, hnormH, hHne⟩ := h_facts hcomp hHc
  have hQ : QuadTrivial H := by
    rw [hbi]
    exact quadTrivial_biSup_conj (s16c1610_commutator_of_isL3 hL3) Y
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO2 hB H hHne hHY hnormH).2 L hcomp hbi).1.1
  have irrBot : ∀ {J : Subgroup W}, J ∈ irrSet H → IsIrrOn H J ⊥ := by
    intro J hJ
    have h := hJ.2
    rwa [hfix, inf_bot_eq] at h
  have isL3_of_mem : ∀ {Z : Subgroup (MulAut W)}, Z ∈ conjSet L Y → IsL3 ↥Z 1 := by
    rintro Z ⟨g, -, rfl⟩
    exact LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hL3
  have klApply : ∀ {J : Subgroup W}, J ∈ irrSet H →
      ∀ {Z Z' : Subgroup (MulAut W)}, Z ∈ conjSet L Y → Z' ∈ conjSet L Y → Z ≠ Z' →
      ¬ commSub J Z ≤ fixV H → ¬ commSub J Z' ≤ fixV H →
      9 ≤ rk ↥J ∧ (rk ↥J ≤ 16 → ∀ s ∈ Z, orderOf s = 2 →
        rk ↥(commSub J (Subgroup.zpowers s)) = 3) := by
    intro J hJ Z Z' hZ hZ' hne hJZ hJZ'
    obtain ⟨hZc, hZH, hZn⟩ := conjSet_facts hcomp hHc hZ
    obtain ⟨hZc', hZH', hZn'⟩ := conjSet_facts hcomp hHc hZ'
    have hJZne : commSub J Z ≠ ⊥ := fun h => hJZ (by rw [h]; exact bot_le)
    have hJZne' : commSub J Z' ≠ ⊥ := fun h => hJZ' (by rw [h]; exact bot_le)
    exact hKL W hW H Z Z' J (irrBot hJ) hZH hZH' hZn hZn'
      (B69.components_mul_comm_of_ne hZc' hZc (Ne.symm hne)) (isL3_of_mem hZ)
      (isL3_of_mem hZ') hJZne hJZne'
  have inf_eq_bot_of_ne : ∀ {I J : Subgroup W}, I ∈ irrSet H → J ∈ irrSet H → I ≠ J →
      I ⊓ J = ⊥ := by
    intro I J hI hJ hIJ
    have hIirr := irrBot hI
    have hJirr := irrBot hJ
    have hstab : StableUnder H (I ⊓ J) := stableUnder_inf hIirr.2.1 hJirr.2.1
    rcases hIirr.2.2.2 (I ⊓ J) hstab bot_le inf_le_left with h | h
    · exact h
    · have hle : I ≤ J := h ▸ inf_le_right
      rcases hJirr.2.2.2 I hIirr.2.1 bot_le hle with h2 | h2
      · exact absurd h2 hIirr.1.ne'
      · exact absurd h2 hIJ
  intro I hI X hX X' hX' hIX hIX'
  by_cases hcase : ∃ U ∈ irrSet H, ∀ Z ∈ conjSet L Y, ∀ Z' ∈ conjSet L Y,
      ¬ commSub U Z ≤ fixV H → ¬ commSub U Z' ≤ fixV H → Z = Z'
  ·
    obtain ⟨U, hU, huniq0⟩ := hcase
    have hsupp : ∃ X₀ ∈ conjSet L Y, ¬ commSub U X₀ ≤ fixV H := by
      by_contra h
      push Not at h
      have hle : H ≤ centSub U := by
        rw [hHc]
        refine iSup₂_le fun Z hZ => ?_
        intro z hz
        rw [mem_centSub]
        intro u hu
        have hZ : commSub U Z = ⊥ := le_bot_iff.mp ((h Z hZ).trans (le_of_eq hfix))
        exact (commSub_eq_bot_iff.mp hZ) hu z hz
      have hUle : U ≤ fixV H := by
        intro u hu z hz
        exact (mem_centSub.mp (hle hz)) u hu
      exact not_le_fixV_of_mem_irrSet hU hUle
    obtain ⟨X₀, hX₀, hUX₀⟩ := hsupp
    have hcomp₀ : IsComponentOf X₀ Y := (conjSet_facts hcomp hHc hX₀).1
    have hH₀ : H = ⨆ Z ∈ conjSet X₀ Y, Z := by rw [conjSet_eq_of_mem hX₀, hHc]
    have huniq : ∀ Z ∈ conjSet X₀ Y, ¬ commSub U Z ≤ fixV H → Z = X₀ := by
      intro Z hZ hUZ
      rw [conjSet_eq_of_mem hX₀] at hZ
      exact huniq0 Z hZ X₀ hX₀ hUZ hUX₀
    have hXc₀ : X ∈ conjSet X₀ Y := by simpa [conjSet_eq_of_mem hX₀] using hX
    have hXc₀' : X' ∈ conjSet X₀ Y := by simpa [conjSet_eq_of_mem hX₀] using hX'
    exact forall_unique_of_unique hW hO2 hB hcomp₀ hH₀ hU huniq I hI X hXc₀ X' hXc₀' hIX hIX'
  ·
    push Not at hcase
    exfalso
    have rank_nine : ∀ {J : Subgroup W}, J ∈ irrSet H → 9 ≤ rk ↥J := by
      intro J hJ
      obtain ⟨Z, hZ, Z', hZ', hJZ, hJZ', hZZ'⟩ := hcase J hJ
      exact (klApply hJ hZ hZ' hZZ' hJZ hJZ').1
    have hEvenY : Even (Nat.card Y) := by
      have hdvd : Nat.card ↥L ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le (hLH.trans hHY)
      rw [card_eq_of_isL3 hL3] at hdvd
      exact even_iff_two_dvd.mpr (dvd_trans ⟨84, by norm_num⟩ hdvd)
    obtain ⟨t, htY, ht2, htm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y hEvenY
    have ht4 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := htm.trans hm
    have hrkt : rk ↥(commV (Subgroup.zpowers t)) = 4 := by
      rw [← rkIdx_fixV_zpowers, ht4]
    have htpow : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    by_cases hcent : ∀ h ∈ H, t * h = h * t
    ·
      have hTstab : StableUnder H (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
        refine stableUnder_commSub ?_ (fun x hx u hu => Subgroup.mem_top u)
        intro h hh x hx
        have hcx : h * x = x * h := by
          have hle : Subgroup.zpowers t ≤ Subgroup.centralizer ({h} : Set (MulAut W)) := by
            rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact (hcent h hh).symm
          exact Subgroup.mem_centralizer_iff.mp (hle hx) h (Set.mem_singleton h)
        rw [hcx]
        simpa using hx
      have hne : commSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) H ≠ ⊥ := by
        intro hbot
        have hle : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ≤ fixV H :=
          commSub_eq_bot_iff.mp hbot
        have hbot2 : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) = ⊥ :=
          le_bot_iff.mp (hle.trans (le_of_eq hfix))
        have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
          rw [← commV_eq_commSub]
          exact hrkt
        rw [hbot2, rk_bot] at h4
        omega
      obtain ⟨I₁, hI₁, hI₁le⟩ := exists_mem_irrSet_le hQ hTstab hne
      have h9 : 9 ≤ rk ↥I₁ := rank_nine hI₁
      have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
        rw [← commV_eq_commSub]
        exact hrkt
      have := rk_mono hI₁le
      omega
    ·
      push Not at hcent
      obtain ⟨h₀, hh₀, hnc₀⟩ := hcent
      have hXB : ∃ Z ∈ conjSet L Y, ∃ z ∈ Z, t * z ≠ z * t := by
        by_contra h
        push Not at h
        apply hnc₀
        have hle : H ≤ Subgroup.centralizer ({t} : Set (MulAut W)) := by
          rw [hHc]
          refine iSup₂_le fun Z hZ => ?_
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact h Z hZ z hz
        exact Subgroup.mem_centralizer_iff.mp (hle hh₀) t (Set.mem_singleton t)
      obtain ⟨Xc, hXc, x, hxXc, htx⟩ := hXB
      obtain ⟨hXccomp, hXcH, hXcn⟩ := conjSet_facts hcomp hHc hXc
      have hXcL3 : IsL3 ↥Xc 1 := isL3_of_mem hXc
      have hXcne : Xc ≠ ⊥ := by
        intro hbot
        have hcard := card_eq_of_isL3 hXcL3
        rw [hbot] at hcard
        have hone : Nat.card ↥(⊥ : Subgroup (MulAut W)) = 1 := by simp
        omega
      have finish : rk ↥(commSub (⊤ : Subgroup W) Xc) ≤ 16 → False := by
        intro hrkX
        have hXceven : Even (Nat.card ↥Xc) := by
          have hc : Nat.card ↥Xc = 168 := card_eq_of_isL3 hXcL3
          rw [hc]
          norm_num
        obtain ⟨s, hsX, hs2, -⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Xc hXceven
        have hsY : s ∈ Y := hHY (hXcH hsX)
        have hVne : commSub (⊤ : Subgroup W) Xc ≠ ⊥ := by
          intro h
          have h1 : (⊤ : Subgroup W) ≤ fixV Xc := commSub_eq_bot_iff.mp h
          apply hXcne
          rw [eq_bot_iff]
          intro z hz
          rw [Subgroup.mem_bot]
          refine MulEquiv.ext fun w => ?_
          simpa using h1 (Subgroup.mem_top w) z hz
        have hdecomp : commSub (⊤ : Subgroup W) Xc = ⨆ J ∈ irrSet H, commSub J Xc := by
          conv_lhs => rw [← htop]
          rw [iSup_subtype', s15_semiBot_commSub_iSup_left, iSup_subtype']
        have hexI : ∃ J ∈ irrSet H, commSub J Xc ≠ ⊥ := by
          by_contra h
          push Not at h
          apply hVne
          rw [hdecomp]
          exact iSup_eq_bot.mpr fun J => iSup_eq_bot.mpr fun hJ => h J hJ
        obtain ⟨I₀, hI₀, hI₀X⟩ := hexI
        have hI₀irr : IsIrrOn H I₀ ⊥ := irrBot hI₀
        have hI₀eq : commSub I₀ Xc = I₀ := by
          have hstab : StableUnder H (commSub I₀ Xc) := stableUnder_commSub hXcn hI₀irr.2.1
          have hle : commSub I₀ Xc ≤ I₀ :=
            commSub_le_of_invariant (fun z hz w hw => hI₀irr.2.1 z (hXcH hz) w hw)
          rcases hI₀irr.2.2.2 (commSub I₀ Xc) hstab bot_le hle with h | h
          · exact absurd h hI₀X
          · exact h
        have hI₀le : I₀ ≤ commSub (⊤ : Subgroup W) Xc := by
          rw [← hI₀eq]
          exact commSub_mono le_top le_rfl
        have hI₀16 : rk ↥I₀ ≤ 16 := le_trans (rk_mono hI₀le) hrkX
        have hI₀Xc : ¬ commSub I₀ Xc ≤ fixV H := by
          intro h
          exact hI₀X (le_bot_iff.mp (h.trans (le_of_eq hfix)))
        obtain ⟨Z₁, hZ₁, Z₂, hZ₂, hI₀Z₁, hI₀Z₂, hZne⟩ := hcase I₀ hI₀
        have hZex : ∃ Z' ∈ conjSet L Y, Z' ≠ Xc ∧ ¬ commSub I₀ Z' ≤ fixV H := by
          by_cases h1 : Z₁ = Xc
          · exact ⟨Z₂, hZ₂, fun h2 => hZne (h1.trans h2.symm), hI₀Z₂⟩
          · exact ⟨Z₁, hZ₁, h1, hI₀Z₁⟩
        obtain ⟨Z', hZ', hZX, hI₀Z'⟩ := hZex
        have hrk3 : rk ↥(commSub I₀ (Subgroup.zpowers s)) = 3 :=
          (klApply hI₀ hXc hZ' (fun h => hZX h.symm) hI₀Xc hI₀Z').2 hI₀16 s hsX hs2
        have hOnly : ∀ J ∈ irrSet H, J ≠ I₀ → commSub J Xc = ⊥ := by
          intro J hJ hJI
          by_contra hJX
          have hJirr : IsIrrOn H J ⊥ := irrBot hJ
          have hstab : StableUnder H (commSub J Xc) := stableUnder_commSub hXcn hJirr.2.1
          have hle : commSub J Xc ≤ J :=
            commSub_le_of_invariant (fun z hz w hw => hJirr.2.1 z (hXcH hz) w hw)
          have hEq : commSub J Xc = J := by
            rcases hJirr.2.2.2 (commSub J Xc) hstab bot_le hle with h | h
            · exact absurd h hJX
            · exact h
          have hJle : J ≤ commSub (⊤ : Subgroup W) Xc := by
            rw [← hEq]
            exact commSub_mono le_top le_rfl
          have hdisj : J ⊓ I₀ = ⊥ := inf_eq_bot_of_ne hJ hI₀ hJI
          have hsum := rk_sup_add_rk_inf J I₀
          rw [hdisj, rk_bot] at hsum
          have h9J : 9 ≤ rk ↥J := rank_nine hJ
          have h9I : 9 ≤ rk ↥I₀ := rank_nine hI₀
          have h16 : rk ↥(J ⊔ I₀) ≤ 16 := le_trans (rk_mono (sup_le hJle hI₀le)) hrkX
          omega
        have htopV : (⊤ : Subgroup W) ≤ I₀ ⊔ fixV Xc := by
          rw [← htop]
          refine iSup₂_le fun J hJ => ?_
          by_cases hJI : J = I₀
          · rw [hJI]
            exact le_sup_left
          · exact (commSub_eq_bot_iff.mp (hOnly J hJ hJI)).trans le_sup_right
        have htopV' : (⊤ : Subgroup W) = I₀ ⊔ fixV Xc := (top_le_iff.mp htopV).symm
        have hVs : commSub (⊤ : Subgroup W) (Subgroup.zpowers s) =
            commSub I₀ (Subgroup.zpowers s) := by
          rw [htopV']
          exact commSub_sup_fixV (H := Subgroup.zpowers s)
            (fun w hw => fun y hy => hw y (Subgroup.zpowers_le.mpr hsX hy))
        have hmle : E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers s)) :=
          CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hsY hs2
        rw [CFSG.Quasithin.rkIdx_fixV_zpowers, commV_eq_commSub, hVs, hrk3, hm] at hmle
        omega
      by_cases hXt : Xc.map (MulAut.conj t).toMonoidHom = Xc
      ·
        have hnormXc : ∀ z ∈ Xc, t * z * t⁻¹ ∈ Xc := by
          intro z hz
          have hmem : (MulAut.conj t) z ∈ Xc.map (MulAut.conj t).toMonoidHom :=
            Subgroup.mem_map_of_mem _ hz
          rw [hXt] at hmem
          simpa [MulAut.conj_apply] using hmem
        obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hle⟩ :=
          hKI (MulAut W) Xc t (Or.inl hXcL3) htpow hnormXc ⟨x, hxXc, htx⟩
        refine finish ?_
        have h := rk_commSub_le_of_le_closure hle
        rw [hrkt] at h
        simpa using h
      ·
        have hXtmem : Xc.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := by
          obtain ⟨g, hg, rfl⟩ := hXc
          exact ⟨t * g, Y.mul_mem htY hg, CFSG.Quasithin.B19.map_conj_map_conj L t g⟩
        have hXtcomp : IsComponentOf (Xc.map (MulAut.conj t).toMonoidHom) Y :=
          (conjSet_facts hcomp hHc hXtmem).1
        have hcommXt : ∀ z ∈ Xc, ∀ z' ∈ Xc.map (MulAut.conj t).toMonoidHom,
            z * z' = z' * z :=
          B69.components_mul_comm_of_ne hXtcomp hXccomp hXt
        obtain ⟨y₁, hy₁, y₂, hy₂, hgen, hnc⟩ := hKS (MulAut W) Xc (Or.inl hXcL3)
        have hle := sup_map_conj_le_closure (isSimpleGroup_of_isL3 hXcL3) hy₁ hy₂ hgen hnc hcommXt
        refine finish ?_
        have h := rk_commSub_le_of_le_closure (le_trans le_sup_left hle)
        rw [hrkt] at h
        simpa using h

theorem w4Thm14_1_two (hKL : KL32PairRank) (hKI : KInvolGen) (hKS : KSimpleGen2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hcomp : IsComponentOf L Y) (hL3 : IsL3 ↥L 1)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV H = ⊥)
    (hm : E3.mParam Y = 4) :
    ∀ g : MulAut W, g ∈ Y → g ∉ normIn Y L →
      commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  intro g hgY hgn
  have hHc : H = ⨆ X ∈ conjSet L Y, X := by rw [hH, iSup_conjSet_eq_biSup_conj]
  have huniq := w4Thm14_1_unique hKL hKI hKS hW hO2 hB hcomp hL3 hH hfix hm
  have hgN : g ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro h
    exact hgn (Subgroup.mem_inf.mpr ⟨hgY, h⟩)
  have hne : L.map (MulAut.conj g).toMonoidHom ≠ L := by
    intro h
    exact hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact commSub_commSub_eq_bot_of_unique hW hO2 hB hcomp hHc hfix huniq
    (self_mem_conjSet L Y) ⟨g, hgY, rfl⟩ (Ne.symm hne)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
