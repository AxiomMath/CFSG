module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseTwoG26

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

@[expose] def Gap_18_4_Mbar_image (D : Data G) (V₀ V L : Subgroup G) : Prop :=
  ∀ (K : Subgroup G) (hK : A5Pair18 D V₀ V L K), V₀ ≠ ⊥ →
    2 ≤ CFSG.Open.pRank 5
      (barSub V₀ V hK.data.hyp.hyp125.isElemAbelian (L ⊔ K ⊔ deltaB D))

theorem barImage_deltaB (D : Data G) :
    barImage D.M (deltaB D) = deltaCyclicR D := by
  show ((deltaB D).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
    deltaCyclicR D
  rw [deltaB_subgroupOf D]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem barSub_LKB_rank {D : Data G} {V₀ V L K : Subgroup G} (hK : A5Pair18 D V₀ V L K)
    (hV₀ : V₀ ≠ ⊥) (h61 : UC6.R6_1 D) (h127 : R127 D) :
    2 ≤ CFSG.Open.pRank 5
      (barSub V₀ V hK.data.hyp.hyp125.isElemAbelian (L ⊔ K ⊔ deltaB D)) := by
  classical
  have hV : IsElemAbelian 2 V := hK.data.hyp.hyp125.isElemAbelian
  have hpF : PairFacts D.M V₀ V := hK.data.hyp.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpF.le_normalizer hpF.le_normalizer₀
  have hLle : L ≤ D.M := s13_le_of_mem_calC hK.data.hyp.hL.1
  have hKle : K ≤ D.M := s13_le_of_mem_calC hK.mem_calC
  have hLKle : L ⊔ K ≤ D.M := sup_le hLle hKle
  have hBle : deltaB D ≤ D.M := deltaB_le_M D
  set X : Subgroup G := L ⊔ K ⊔ deltaB D with hXdef
  have hXM : X ≤ D.M := sup_le hLKle hBle
  have hXS : X ≤ stabTil V₀ V := hXM.trans hMs
  have hcomm : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M K, a * b = b * a :=
    CFSG.Quasithin.modO2Image_commute hK.commutator_le
  have hA5 : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K)) :=
    isA5xA5_barImage_sup_of_calC hK.data.hyp.hL.1 hK.mem_calC hK.ne_L hK.data.alt
      hK.alt_K hcomm
  have hrankA : CFSG.Open.pRank 5 (barImage D.M (L ⊔ K)) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact S17.pRank_eq_two_of_isA5xA5 hA5 (Or.inr rfl)
  have hrankZ : CFSG.Open.pRank 5 (deltaCyclicR D) = 1 :=
    s13_pRank_of_card_prime (deltaCyclicR D) Nat.prime_five (deltaR_card hK.data)
  have hAleQ : barImage D.M (L ⊔ K) ≤ deltaCyclicQ D := by
    rw [s13_barImage_sup hLle hKle]
    exact sup_le (hK.data.barImage_le_pElementSubgroup hK.data.hyp.hL.1)
      (hK.data.barImage_le_pElementSubgroup hK.mem_calC)
  have hcommAZ : ∀ a ∈ barImage D.M (L ⊔ K), ∀ z ∈ deltaCyclicR D, a * z = z * a := by
    intro a ha z hz
    exact Subgroup.mem_centralizer_iff.mp (deltaCyclicR_le_centralizer D hz) a
      (hAleQ ha)
  have hdisjAZ : barImage D.M (L ⊔ K) ⊓ deltaCyclicR D = ⊥ := by
    refine le_bot_iff.mp ?_
    intro z hz
    have hzcent : (⟨z, hz.1⟩ : ↥(barImage D.M (L ⊔ K))) ∈
        Subgroup.center ↥(barImage D.M (L ⊔ K)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcommAZ w w.2 z hz.2)
    rw [S17.center_eq_bot_of_isA5xA5 hA5, Subgroup.mem_bot] at hzcent
    exact Subtype.ext_iff.mp hzcent
  have hrank3 : 3 ≤ CFSG.Open.pRank 5
      (barImage D.M (L ⊔ K) ⊔ deltaCyclicR D) := by
    have h := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_five hcommAZ hdisjAZ
    omega
  have hXeq : barImage D.M X = barImage D.M (L ⊔ K) ⊔ deltaCyclicR D := by
    rw [hXdef, s13_barImage_sup hLKle hBle, s13_barImage_sup hLle hKle, barImage_deltaB]
  have h3X : 3 ≤ CFSG.Open.pRank 5 X := by
    have h := s13_pRank_barImage (p := 5) Nat.prime_five (by norm_num) hXM
    rw [hXeq] at h
    omega
  have hker1 : CFSG.Open.pRank 5 (X ⊓ F11.CTilde D.M V₀ V) ≤ 1 := by
    have h4 : Nat.card V₀ ≤ 4 := by
      have h2 : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hpF.elemAbelian₀).mp hK.data.hyp.small
      omega
    refine (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) inf_le_right).trans ?_
    exact uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 hK.data.hyp.hyp125) h4
      hK.data.hyp.hp
  let ρ : ↥X →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hXS)
  have hker : ρ.ker.map X.subtype = X ⊓ F11.CTilde D.M V₀ V := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      exact (mem_cTilde_iff (M := D.M) (V₀ := V₀) (V := V) hV hpF.le_normalizer).2
        ⟨hXM x.2, hXS x.2, hx⟩
    · rintro ⟨hgX, hgC⟩
      obtain ⟨hgs, hact⟩ :=
        ((mem_cTilde_iff (M := D.M) (V₀ := V₀) (V := V) hV hpF.le_normalizer).1 hgC).2
      refine ⟨⟨g, hgX⟩, ?_, rfl⟩
      show actTil V₀ V hV ⟨g, hXS hgX⟩ = 1
      rwa [show (⟨g, hXS hgX⟩ : stabTil V₀ V) = ⟨g, hgs⟩ from Subtype.ext rfl]
  have hrange : (⊤ : Subgroup ↥X).map ρ = barSub V₀ V hV X := by
    ext φ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, -, rfl⟩
      exact actTil_mem_barSub V₀ V hV x.2 (hXS x.2)
    · intro hφ
      obtain ⟨g, hgX, hgact⟩ := (mem_barSub V₀ V hV X φ).1 hφ
      refine ⟨⟨(g : G), hgX⟩, Subgroup.mem_top _, ?_⟩
      show actTil V₀ V hV ⟨(g : G), hXS hgX⟩ = φ
      rwa [show (⟨(g : G), hXS hgX⟩ : stabTil V₀ V) = g from Subtype.ext rfl]
  have hineq : CFSG.Open.pRank 5 X ≤
      CFSG.Open.pRank 5 (X ⊓ F11.CTilde D.M V₀ V) +
        CFSG.Open.pRank 5 (barSub V₀ V hV X) := by
    have h1 : CFSG.Open.pRank 5 ρ.ker ≤ CFSG.Open.pRank 5 (X ⊓ F11.CTilde D.M V₀ V) := by
      rw [← hker]
      exact CFSG.SectionRank.pRank_le_map (by norm_num) X.subtype X.subtype_injective ρ.ker
    have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
      (p := 5) Nat.prime_five ρ ⊤
    rw [top_inf_eq, hrange, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X] at h
    exact h.trans (Nat.add_le_add_right h1 _)
  omega

theorem gap_18_4_Mbar_image_of (h61 : UC6.R6_1 D) (h127 : R127 D) :
    Gap_18_4_Mbar_image D V₀ V L :=
  fun K hK hV₀ => barSub_LKB_rank hK hV₀ h61 h127

theorem deltaCalMOf_of (h61 : UC6.R6_1 D) (himg : Gap_18_4_Mbar_image D V₀ V L)
    (hV₀ : V₀ ≠ ⊥) {K : Subgroup G} (hK : A5Pair18 D V₀ V L K)
    {Δ : Set (Subgroup G)} (hΔM : ∀ H ∈ Δ, H ≤ D.M)
    (hL : L ≤ ⨆ H ∈ Δ, H) (hKle : K ≤ ⨆ H ∈ Δ, H)
    (hB : deltaB D ≤ ⨆ H ∈ Δ, H) :
    DeltaCalMOf D V₀ V hK.data.hyp.hyp125.isElemAbelian Δ := by
  classical
  intro K' hTK' hK'le hbar
  have hV := hK.data.hyp.hyp125.isElemAbelian
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hK.data.hyp.hyp125.pairFacts.le_normalizer
      hK.data.hyp.hyp125.pairFacts.le_normalizer₀
  have hKM : K' ≤ D.M := hK'le.trans (iSup₂_le hΔM)
  have hLKB : L ⊔ K ⊔ deltaB D ≤ ⨆ H ∈ Δ, H := sup_le (sup_le hL hKle) hB
  have hbarSup : barSub V₀ V hV (⨆ H ∈ Δ, H) =
      ⨆ H ∈ Δ, barSub V₀ V hV H := by
    have h1 : (⨆ H ∈ Δ, H) = ⨆ H : {H : Subgroup G // H ∈ Δ}, H.1 := iSup_subtype'
    have h2 : (⨆ H ∈ Δ, barSub V₀ V hV H) =
        ⨆ H : {H : Subgroup G // H ∈ Δ}, barSub V₀ V hV H.1 := iSup_subtype'
    rw [h1, h2]
    exact barSub_iSup_of_le hV (K := fun H : {H : Subgroup G // H ∈ Δ} => H.1)
      (fun H => (hΔM H.1 H.2).trans hMstab)
  have hcomp : barSub V₀ V hV (L ⊔ K ⊔ deltaB D) ≤ barSub V₀ V hV K' := by
    rw [hbar, ← hbarSup]
    exact barSub_mono V₀ V hV hLKB
  have hrank' : 2 ≤ CFSG.Open.pRank 5 (barSub V₀ V hV K') :=
    (himg K hK hV₀).trans (CFSG.SectionRank.pRank_mono (by norm_num) hcomp)
  have hK'stab : K' ≤ stabTil V₀ V := hKM.trans hMstab
  let ψ : ↥K' →* ↥(barSub V₀ V hV K') :=
    { toFun := fun x =>
        ⟨actTil V₀ V hV ⟨(x : G), hK'stab x.2⟩,
          actTil_mem_barSub V₀ V hV x.2 (hK'stab x.2)⟩
      map_one' := Subtype.ext (by
        change actTil V₀ V hV (⟨((1 : ↥K') : G), hK'stab (one_mem K')⟩ : stabTil V₀ V) = 1
        rw [show (⟨((1 : ↥K') : G), hK'stab (one_mem K')⟩ : stabTil V₀ V) = 1 from
          Subtype.ext (by simp), map_one])
      map_mul' := fun a b => Subtype.ext (by
        change actTil V₀ V hV
            (⟨((a : G) * (b : G)), hK'stab (mul_mem a.2 b.2)⟩ : stabTil V₀ V) =
          actTil V₀ V hV (⟨(a : G), hK'stab a.2⟩ : stabTil V₀ V) *
            actTil V₀ V hV (⟨(b : G), hK'stab b.2⟩ : stabTil V₀ V)
        rw [show (⟨((a : G) * (b : G)), hK'stab (mul_mem a.2 b.2)⟩ : stabTil V₀ V) =
            (⟨(a : G), hK'stab a.2⟩ : stabTil V₀ V) * ⟨(b : G), hK'stab b.2⟩
              from Subtype.ext rfl, map_mul]) }
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hgK, hgy⟩ := (mem_barSub V₀ V hV K' (y : MulAut (Vtil V₀ V hV))).1 y.2
    refine ⟨⟨(g : G), hgK⟩, Subtype.ext ?_⟩
    show actTil V₀ V hV ⟨(g : G), hK'stab hgK⟩ = (y : MulAut (Vtil V₀ V hV))
    rw [show (⟨(g : G), hK'stab hgK⟩ : stabTil V₀ V) = g from Subtype.ext rfl]
    exact hgy
  have hbarRank : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(barSub V₀ V hV K')) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barSub V₀ V hV K')]
    exact hrank'
  have hpK' : 2 ≤ CFSG.Open.pRank 5 K' :=
    @CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective G _ _ K'
      ↥(barSub V₀ V hV K') _ _ ψ hψsurj 5 ⟨Nat.prime_five⟩ (by norm_num) hbarRank
  obtain ⟨A, hAK', hAel, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (by norm_num : 1 < 5) K'
  have hAc : ¬ IsCyclic A := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
    have hgp : g ^ 5 = 1 := Subtype.ext (by simpa using hAel.2 (g : G) g.2)
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hgp
    rw [hg, hAcard] at hdvd
    have h25 : 5 ^ 2 ∣ 5 ^ CFSG.Open.pRank 5 K' := pow_dvd_pow 5 hpK'
    have hle : 5 ^ 2 ≤ 5 := Nat.le_of_dvd (by norm_num) (h25.trans hdvd)
    norm_num at hle
  exact c23_uniqueMax_of_noncyclic D h61 hK.data.hyp.hp
    (CFSG.Open.IsElemAbelian.isPGroup hAel) hAc hAK' hKM

theorem deltaCalMOfCase_of (h61 : UC6.R6_1 D) (himg : Gap_18_4_Mbar_image D V₀ V L)
    (hV₀ : V₀ ≠ ⊥) : DeltaCalMOfCase D V₀ V L := by
  intro K hK
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hBleM : deltaB D ≤ D.M := deltaB_le_M D
  have hXleM : UC22.conjClosure D.M L ≤ D.M := hK.data.hyp.X_le_M
  have hLleM : L ≤ D.M := s13_le_of_mem_calC hK.data.hyp.hL.1
  have hKleM : K ≤ D.M := s13_le_of_mem_calC hK.mem_calC
  constructor
  · intro hX
    refine deltaCalMOf_of h61 himg hV₀ hK
      (Δ := {UC22.conjClosure D.M L ⊔ D.T, deltaB D ⊔ D.T}) ?_ ?_ ?_ ?_
    · intro H hH
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl
      · exact sup_le hXleM hTM
      · exact sup_le hBleM hTM
    · have hLce : L ≤ UC22.conjClosure D.M L := by
        rw [UC22.conjClosure]
        exact le_iSup₂_of_le L ⟨1, D.M.one_mem, by ext; simp⟩ le_rfl
      exact (hLce.trans (le_sup_left : UC22.conjClosure D.M L ≤
          UC22.conjClosure D.M L ⊔ D.T)).trans
        (le_iSup₂_of_le (UC22.conjClosure D.M L ⊔ D.T) (by simp) le_rfl)
    · have hKce : K ≤ UC22.conjClosure D.M L := by rw [hX]; exact le_sup_right
      exact (hKce.trans (le_sup_left : UC22.conjClosure D.M L ≤
          UC22.conjClosure D.M L ⊔ D.T)).trans
        (le_iSup₂_of_le (UC22.conjClosure D.M L ⊔ D.T) (by simp) le_rfl)
    · exact (le_sup_left : deltaB D ≤ deltaB D ⊔ D.T).trans
        (le_iSup₂_of_le (deltaB D ⊔ D.T) (by simp) le_rfl)
  · refine deltaCalMOf_of h61 himg hV₀ hK
      (Δ := {L ⊔ D.T, K ⊔ D.T, deltaB D ⊔ D.T}) ?_ ?_ ?_ ?_
    · intro H hH
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl | rfl
      · exact sup_le hLleM hTM
      · exact sup_le hKleM hTM
      · exact sup_le hBleM hTM
    · exact (le_sup_left : L ≤ L ⊔ D.T).trans
        (le_iSup₂_of_le (L ⊔ D.T) (by simp) le_rfl)
    · exact (le_sup_left : K ≤ K ⊔ D.T).trans
        (le_iSup₂_of_le (K ⊔ D.T) (by simp) le_rfl)
    · exact (le_sup_left : deltaB D ≤ deltaB D ⊔ D.T).trans
        (le_iSup₂_of_le (deltaB D ⊔ D.T) (by simp) le_rfl)



theorem gap_18_4_Delta_of_case
    (c : A5Data18 D V₀ V L) (h61 : UC6.R6_1 D) (h43c : W3Lem45_2Chief)
    (hgen : CFSG.SignalizerFunctorTheorem.McBride.orbitClosure
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) L)
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T) ⊔
      imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T = ⊤)
    (hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T')
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank)
    (h1768 : S17.R17_68At D V₀ V) (h127 : R127 D) :
    Gap_18_4_Delta D V₀ V L c := by
  classical
  intro hV₀
  exact gap_18_4_Delta_of c h61 h43c hgen hcf hKc h1768
    (deltaCalMOfCase_of h61 (gap_18_4_Mbar_image_of h61 h127) hV₀) hV₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
