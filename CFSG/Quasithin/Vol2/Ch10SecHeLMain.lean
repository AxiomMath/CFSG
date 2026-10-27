module

public import CFSG.Quasithin.Vol2.Ch10SecHeLOrd
public import CFSG.Quasithin.Vol2.Ch10SecHeLAut
public import CFSG.Quasithin.Vol2.Ch10SecHeLDefs
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Excl

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank HeL
open scoped IsMulCommutative

namespace HeL

theorem sl2_isSimpleGroup {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* _).isSimpleGroup

variable {G : Type} [Group G]

theorem not_he_of_J4
    {K : Subgroup G} (e : O2Q K ≃* NativeSporadic.Carrier .He)
    (eJ : G ≃* NativeSporadic.J4) : False := by
  have hHe : Nat.card (O2Q K) = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  have hdvd : Nat.card (O2Q K) ∣ Nat.card G :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K)
  have hG : Nat.card G = 86775571046077562880 :=
    (Nat.card_congr eJ.toEquiv).trans CFSG.Sporadic.J4.card_J4
  have h25 : 25 ∣ Nat.card G := (show 25 ∣ 4030387200 by norm_num).trans (hHe ▸ hdvd)
  rw [hG] at h25
  norm_num at h25

theorem not_card_he_of_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ (2 * n)) {H : Type*} [Group H]
    (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) →* H)
    (hπ : Function.Surjective π) (hH : Nat.card H = 4030387200) : False := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (sl2_isSimpleGroup h4)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have hinj : Function.Injective π := by
    rcases hs.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).mp h
    · exfalso
      have h1 : ∀ x : H, x = 1 := fun x => by
        obtain ⟨g, rfl⟩ := hπ x
        exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g)
      have : Subsingleton H := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
      rw [Nat.card_unique] at hH
      norm_num at hH
  have hcard : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) = 4030387200 :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).trans hH
  exact card_SL2_ne hF ((Nat.card_congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv).trans hcard)

end HeL

theorem noHeLStarF_of
    (hfsu : StmtFSUChoice) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h701 : Stmt7_0_1) :
    NoHeLStarF := by
  intro G _ _ T K hs hna hq hT hmax hf hTK ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, hfsu'⟩ := hfsu G T K hs hna hq hT hmax hf (isQuasisimple_O2Q e)
  have hKT : conjClosure K T = K := conjClosure_eq hTK
  have hKK : K = conjClosure K T := hKT.symm
  have hV₀ : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V₀ := by
    have h := hfsu'.irrPlus
    rwa [hKT] at h
  have hR : V₀ ≤ reducedAggregate (K ⊔ T) := hV₀.1
  have hKV₀ : K ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hne₀ : ¬ K ≤ Subgroup.centralizer (V₀ : Set G) := not_le_centralizer_of_isIrrPlusIn hV₀
  have hKV : K ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_K hTK hKV₀
  have hVR : conjClosure V₀ T ≤ reducedAggregate (K ⊔ T) := conjClosure_le_reducedAggregate hR
  have hneV : ¬ K ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := card_autOn_eq e hTK hKV hVR hneV
  obtain ⟨-, -, hcases⟩ := h325 G T K V₀ hfsu' hKK
  have hVeq : V₀ = conjClosure V₀ T := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlist, -⟩
    · exact h1
    · exact h1
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e'⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩ |
        ⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩
      · exact card_SL3_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 6 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
      · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL4_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL5_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 7 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
  have hcard := card_autOn_eq e hTK hKV₀ hR hne₀
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  obtain ⟨k, hk⟩ := L34Orders.exists_card_autOn_sup hKV₀ hTV₀ hTK hT.1
  rw [hcard] at hk
  have hc : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props _).2.1 _ (hR a.2) _ (hR b.2))⟩⟩
  by_cases hFF : IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn K V₀ : Set (MulAut ↥V₀))))
  ·
    obtain ⟨_, hcases⟩ := h328 G T K V₀ hfsu' hKK hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, hl, -⟩ | ⟨⟨m, F, _, _, hF, ⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩⟩ |
      ⟨m, F, _, _, hF, ⟨e'⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e'⟩, -⟩ | ⟨⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩⟩ |
      ⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩ | ⟨-, hZ, ⟨e'⟩, -⟩ | ⟨m, hm, ⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_ne m h1.symm
    · exact card_SL3_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hcard)
    · exact card_SL3_ne (F := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)
        ((Nat.card_congr e'.toEquiv).symm.trans hcard)
    · exact card_statedSp_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hcard)
    · exact card_G2_derived_ne hF ((Nat.card_congr e'.toEquiv).symm.trans hcard)
    · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcard
      rw [L34Orders.card_alt 5 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcard
      rw [L34Orders.card_alt 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcard
      rw [L34Orders.card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := Nat.card_congr e'.toEquiv
      rw [hk, L34Orders.card_alt 7 (by norm_num), show Nat.factorial 7 / 2 = 2520 by decide]
        at h1
      exact mul_two_pow_ne (by norm_num) k h1
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(autOn K V₀))
      rw [hcard, hZ, Nat.card_congr e'.toEquiv, L34Orders.card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · rcases hm with rfl | rfl
      · have h1 := Nat.card_congr e'.toEquiv
        rw [hk, L34Orders.card_SL4_two] at h1
        exact mul_two_pow_ne (by norm_num) k h1
      · have h1 := Nat.card_congr e'.toEquiv
        rw [hk, L34Orders.card_SL5_two] at h1
        exact mul_two_pow_ne (by norm_num) k h1
    · have h1 := (Nat.card_congr e'.toEquiv).symm.trans hcard
      rw [L34Orders.card_SL4_two] at h1
      norm_num at h1
    · have h1 := Nat.card_congr e'.toEquiv
      rw [hk, L34Orders.card_SL5_two] at h1
      exact mul_two_pow_ne (by norm_num) k h1
  ·
    obtain ⟨hcV, -, -, hcases⟩ := h701 G T K V₀ hfsu'
    rcases hcases with ⟨A, hA⟩ | hJ4 | ⟨n, hn, F, _, _, _, hF, π, hπ, -⟩ | hFour
    · exact hFF ((isFFModule_congr hVeq.symm hKT).mp (isFFModule_of_isFFStarOffender hA))
    · obtain ⟨-, -, -, -, -, ⟨eJ⟩⟩ := hJ4
      exact not_he_of_J4 e eJ
    · have hH : Nat.card ↥(autOn (fsuL0 T K) (fsuV T V₀)) = 4030387200 := by
        show Nat.card ↥(autOn (conjClosure K T) (conjClosure V₀ T)) = 4030387200
        rw [hKT]
        exact hcardV
      exact not_card_he_of_sl2 hn hF π hπ hH
    · have h4 : K < conjClosure K T := hFour.1
      rw [hKT] at h4
      exact lt_irrefl K h4

end CFSG.Quasithin.Vol2.Ch10
