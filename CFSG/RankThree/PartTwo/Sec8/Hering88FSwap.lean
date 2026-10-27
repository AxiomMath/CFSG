module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Cases
public import CFSG.RankThree.PartTwo.Sec8.Hering88FModel
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSmall
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem not_isSolvable_inf_barCentralizer_abs {G : Type} [Group G] [Finite G]
    {Y I' T₀ : Subgroup G} {x d : G} (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1) (hIY : I' ≤ Y)
    (hIx : I' ≤ Subgroup.centralizer ({x} : Set G))
    (hdI : d ∈ Subgroup.normalizer (I' : Set G)) (hT₀p : Group.IsPerfect T₀) (hT₀ : T₀ ≠ ⊥)
    (hT₀I : T₀ ≤ I') (hT₀d : T₀ ≤ Subgroup.centralizer ({d} : Set G)) :
    ¬ Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers x) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y) := by
  intro hsolv
  set T := inSubgroup perfectResidual (I' ⊓ Subgroup.centralizer ({d} : Set G)) with hT
  have hTp : Group.IsPerfect T := Item87Proof.isPerfect_residual _
  have hTI : T ≤ I' ⊓ Subgroup.centralizer ({d} : Set G) := Item87Proof.residual_le _
  have hTY : T ≤ Y := hTI.trans (inf_le_left.trans hIY)
  have hT₀T : T₀ ≤ T := KFacts.le_inSubgroup_perfectResidual hT₀p (le_inf hT₀I hT₀d)
  have hT1 : T ≠ ⊥ := fun hbot => hT₀ (le_bot_iff.mp (hbot ▸ hT₀T))
  have hπT : imageModTheta Y T = inSubgroup perfectResidual
      (imageModTheta Y I' ⊓ barCentralizer (Subgroup.zpowers d) Y) :=
    imageModTheta_residual_inf_centralizer_eq hIY hdN hdI hd3
  have hπI : imageModTheta Y I' ≤ barCentralizer (Subgroup.zpowers x) Y := by
    rw [← KFacts.imageModTheta_centralizer_eq hxN ⟨1, by simpa using hx3⟩]
    exact imageModTheta_mono' (le_inf hIY hIx)
  have hPle : imageModTheta Y T ≤
      barCentralizer (Subgroup.zpowers x) Y ⊓ barCentralizer (Subgroup.zpowers d) Y := by
    rw [hπT]
    exact (Item87Proof.residual_le _).trans (inf_le_inf_right _ hπI)
  have hPbot : imageModTheta Y T = ⊥ := by
    by_contra hne
    haveI : Nontrivial (imageModTheta Y T) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect (imageModTheta Y T) := by
      rw [hπT]
      exact Item87Proof.isPerfect_residual _
    haveI := hsolv
    have hs : Group.IsSolvable (imageModTheta Y T) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPle)
    exact Group.IsPerfect.not_isSolvable (imageModTheta Y T) hs
  exact Item87Res2Proof.not_le_theta_of_isPerfect hTp hT1 (M := Y)
    (Hering88D.le_theta_of_imageModTheta_eq_bot hTY hPbot)

theorem classB_core_abs {G : Type} [Group G] [Finite G] {Y I' : Subgroup G} {x d : G} {m : ℕ}
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1) (hIY : I' ≤ Y)
    (hdI : d ∈ Subgroup.normalizer (I' : Set G))
    (hM1 : imageModTheta Y I' = barCentralizer (Subgroup.zpowers x) Y)
    (hTcomm : ∀ P : Subgroup G, P ≤ inSubgroup perfectResidual
      (I' ⊓ Subgroup.centralizer ({d} : Set G)) → IsPGroup 3 P →
        ∀ u ∈ P, ∀ v ∈ P, u * v = v * u)
    (hdich : ClassBDichotomy Y x d m) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  rcases hdich with hL | ⟨z, hz, hz1, hz3, hzc⟩
  · exact hL
  exfalso
  set T := inSubgroup perfectResidual (I' ⊓ Subgroup.centralizer ({d} : Set G)) with hT
  have hTI : T ≤ I' ⊓ Subgroup.centralizer ({d} : Set G) := Item87Proof.residual_le _
  have hTY : T ≤ Y := hTI.trans (inf_le_left.trans hIY)
  have hTeq : imageModTheta Y T = inSubgroup perfectResidual
      (barCentralizer (Subgroup.zpowers x) Y ⊓ barCentralizer (Subgroup.zpowers d) Y) := by
    rw [hT, imageModTheta_residual_inf_centralizer_eq hIY hdN hdI hd3, hM1]
  exact false_of_central_three_of_eq hTY hTcomm hTeq (Item87Proof.isPerfect_residual _) hz hz1 hz3
    hzc

theorem classBDichotomy_of_case1 (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} {x d : G} {A₀ : Subgroup G} {d' : G}
    {m : ℕ} (hxN : x ∈ Subgroup.normalizer (Y : Set G))
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hxd : x * d = d * x) (hx3 : x ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hxout : Sec4.InducesOuterTheta x Y)
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) (hm2 : 2 ≤ m)
    (hodd : Odd m) (hc1 : Case83One Y x A₀ d' m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers x) Y) m) :
    ClassBDichotomy Y x d m := by
  rcases hc1.1 with hD | hG
  · obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    exact classBDichotomy_d4 h47 hxN hdN hxd hx3 hd3 hxout hin hne hm2 hodd hK hσ e hG2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
    exact classBDichotomy_g2 hxN hdN hxd hx3 hd3 hxout hin hne hm2 hodd hK e

theorem exists_T₀ (hF : KF84Field) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hn2 : 2 ≤ n) {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) :
    ∃ T₀ : Subgroup G, Group.IsPerfect T₀ ∧ T₀ ≠ ⊥ ∧
      T₀ ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊓
        Subgroup.centralizer ({a} : Set G) ∧ T₀ ≤ Subgroup.centralizer ({d} : Set G) := by
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hT₀ : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠ ⊥ := by
    refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3 (hF G A c L a b X n h)
    rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, hSU⟩ | hL2
    · exact Or.inl ⟨Item87Res2Proof.odd_of_isGammaTypeRee hRee, hSU⟩
    · exact Or.inr hL2
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdcl).symm
  refine ⟨_, Item87Proof.isPerfect_residual _, hT₀, Item87Proof.residual_le _, ?_⟩
  exact (Item87Proof.residual_le _).trans (inf_le_left.trans hKd)

theorem not_isSolvable_inf_barCentralizer_swap (h45 : Sec4.Item4_5) (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    {Y : Subgroup G} (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbN : b ∈ Subgroup.normalizer (Y : Set G))
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) :
    ¬ Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers b) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y) := by
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu b hbA)) X hX
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X :=
    h.pairRel.2.2.2.1
  obtain ⟨T₀, hT₀p, hT₀, hT₀le, hT₀d⟩ := exists_T₀ hF h hn2 hdcl
  have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
  have hdJ : d ∈ Subgroup.normalizer (sec8J X a : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX hdA, Subgroup.le_normalizer hda⟩)
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hT₀J : T₀ ≤ sec8J X a :=
    KFacts.le_inSubgroup_perfectResidual hT₀p
      (le_inf (hT₀le.trans (inf_le_left.trans hKX)) (hT₀le.trans inf_le_right))
  exact not_isSolvable_inf_barCentralizer_abs hbN hb3 hdN hd3 (le_sup_right.trans hIJ)
    (hJX.trans hXb) hdJ hT₀p hT₀ hT₀J hT₀d

theorem false_of_small_swap (h45 : Sec4.Item4_5) (hF : KF84Field) (hG : G2TwoCentThreeSolvable)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    {Y : Subgroup G} (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbN : b ∈ Subgroup.normalizer (Y : Set G))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hH : IsoGTwoEven (barCentralizer (Subgroup.zpowers b) Y) 1 ∨
      IsoPGUThree (barCentralizer (Subgroup.zpowers b) Y) (2 ^ 1))
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) : False := by
  obtain ⟨hAc, -⟩ := Hering88C.pair_commute_pow_three h
  obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hbd : b * d = d * b := hAc b hbA d hdA
  refine not_isSolvable_inf_barCentralizer_swap h45 hF h hn2 hIJ hbN hdcl hdA hd3 hdN ?_
  rcases hH with hG2 | hP
  · exact isSolvable_inf_barCentralizer_of_isoGTwoEven_one hG hbN hdN hbd hd3 hin hne hZ hG2
  · haveI : Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers b) Y) :=
      isSolvable_of_isoPGUThree_two hP
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left :
        barCentralizer (Subgroup.zpowers b) Y ⊓ barCentralizer (Subgroup.zpowers d) Y ≤
          barCentralizer (Subgroup.zpowers b) Y))

theorem not_card_eq_projSL_statedSU {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ (3 * n)) ^ 2)
    (hcard : Nat.card (projSL 2 (GaloisField 2 (3 * n'))) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * n)) F)) : False := by
  rw [Item87Proof.card_projSL_two_three hn', Item87Proof.card_statedSU_three_two hF] at hcard
  set f := 3 * n with hf
  have ho1 : Odd ((2 ^ (3 * n')) ^ 2 - 1) := Item87Proof.odd_two_pow_sq_sub_one (by omega)
  have ho2 : Odd (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
    (Item87Proof.odd_two_pow_sq_sub_one (by omega)).mul
      (Item87Proof.odd_two_pow_cube_add_one (by omega))
  have heq : 3 * n' = 3 * f := by
    rcases lt_trichotomy (3 * n') (3 * f) with hlt | heq | hgt
    · exfalso
      refine Item87Proof.not_two_pow_dvd_two_pow_mul_odd hlt ho1 ?_
      rw [hcard]
      exact Dvd.intro _ rfl
    · exact heq
    · exfalso
      refine Item87Proof.not_two_pow_dvd_two_pow_mul_odd hgt ho2 ?_
      rw [← hcard]
      exact Dvd.intro _ rfl
  rw [heq] at hcard
  have h2pos : 0 < 2 ^ (3 * f) := by positivity
  have hcancel := Nat.eq_of_mul_eq_mul_left h2pos hcard
  have hq : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  set q := 2 ^ f with hqdef
  have h3 : 2 ^ (3 * f) = q ^ 3 := by rw [hqdef, ← pow_mul, mul_comm]
  rw [h3] at hcancel
  have h1 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2] at hcancel
  nlinarith [pow_pos (show (0 : ℤ) < q by positivity) 5, pow_pos (show (0 : ℤ) < q by positivity) 2,
    show (8 : ℤ) ≤ q by exact_mod_cast hq]

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
