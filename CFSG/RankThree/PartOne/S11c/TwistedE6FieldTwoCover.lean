module

public import CFSG.RankThree.PartOne.S11b.OddF4Cover
public import CFSG.RankThree.PartOne.KP.BLeviMonster
public import CFSG.RankThree.PartOne.S11c.InverterData
public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
public import CFSG.Monster.B.E6.StandardSimple
public import CFSG.RankThree.PartOne.KP.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Fischer CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedProj StatedSU)

theorem central_cover_of_levi_le {Cg : Type*} [Group Cg] (L : Subgroup Cg)
    (e : L ≃* StatedProj (StatedSU 6 (2 ^ 1) F4)) (Y : Type) [Group Y] [Finite Y]
    (f : Y →* Cg) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Y) :
    ∃ V : Subgroup Y, IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ 4 ∧ V ≤ L.comap f := by
  let YL : Subgroup Y := L.comap f
  let φ : YL →* StatedProj (StatedSU 6 (2 ^ 1) F4) :=
    e.toMonoidHom.comp ((f.comp YL.subtype).codRestrict L (fun y => y.2))
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := hf (e.symm x : Cg)
    have hyL : y ∈ YL := by
      show f y ∈ L
      rw [hy]
      exact (e.symm x).2
    refine ⟨⟨y, hyL⟩, ?_⟩
    show e (⟨f y, hyL⟩ : L) = x
    rw [show (⟨f y, hyL⟩ : L) = e.symm x from Subtype.ext hy]
    exact e.apply_symm_apply x
  have hφk : φ.ker ≤ Subgroup.center YL := by
    intro y hy
    have h1 : f y = 1 := by
      rw [MonoidHom.mem_ker] at hy
      have h0 : e (⟨f y, y.2⟩ : L) = 1 := hy
      have h2 : (⟨f y, y.2⟩ : L) = 1 := e.injective (h0.trans (map_one e).symm)
      exact congrArg Subtype.val h2
    have h3 : (y : Y) ∈ Subgroup.center Y := hker ((MonoidHom.mem_ker).2 h1)
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h3 z.1))
  obtain ⟨U, hU, hUc⟩ := stated_psu6_central_cover φ hφ hφk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hU
  exact ⟨U.map YL.subtype, IsElementaryAbelian.map _, by
    rw [Subgroup.card_map_of_injective YL.subtype_injective, hUc], Subgroup.map_subtype_le U⟩

theorem two_eq_zero_stdField : (2 : C2E6Overlap.K) = 0 := by
  have := CharP.cast_eq_zero C2E6Overlap.K 2
  exact_mod_cast this

theorem pinnedX_theta_one_mem_stdGroup :
    pinnedX Tag.E6 C2E6Overlap.K e6HighestRoot 1 ∈ stdGroup := by
  let _ : Algebra (ZMod 2) C2E6Overlap.K := ZMod.algebra C2E6Overlap.K 2
  have hle := thetaRankOneGroup_le_graphFixedRootGroup (k := ZMod 2) (K := C2E6Overlap.K)
    two_eq_zero_stdField (σ := barHom) (fun c => by
      rw [Nat.card_zmod]
      exact CFSG.Monster.B.E6.barHom_eq_pow c)
  refine hle ?_
  refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, ?_⟩)
  simp only [map_one]
  rfl

@[expose] noncomputable def stdTheta : stdGroup :=
  ⟨pinnedX Tag.E6 C2E6Overlap.K e6HighestRoot 1, pinnedX_theta_one_mem_stdGroup⟩

theorem orderOf_stdTheta : orderOf stdTheta = 2 := by
  rw [stdTheta, Subgroup.orderOf_mk]
  exact orderOf_pinnedX_one_charTwo _

theorem commute_stdTheta_of_mem_stdLeviIn {l : stdGroup} (hl : l ∈ stdLeviIn) :
    Commute stdTheta l := by
  have h1 : (l : ModGL Tag.E6 C2E6Overlap.K) ∈ subsystemGroup Tag.E6 C2E6Overlap.K
      (nativeUnion firstJ) := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)).1
  have hA : nativeUnion firstJ = E6GraphLevi.setA := by
    rw [nativeUnion_firstJ]
    ext i
    show i ∈ C2E6Std.setA ↔ i ≠ (1 : Fin 6)
    fin_cases i <;> simp [C2E6Std.setA]
  rw [hA] at h1
  have h2 := subsystemGroup_le_centralizer_thetaSL2 (E := C2E6Overlap.K) two_eq_zero_stdField h1
  have h3 : thetaSL2 C2E6Overlap.K (uSL 1) ∈
      (((thetaSL2 C2E6Overlap.K).range : Subgroup _) : Set (ModGL TwistTag.E6.tag C2E6Overlap.K)) :=
    Set.mem_range_self (uSL 1)
  have h4 := Subgroup.mem_centralizer_iff.mp h2 _ h3
  rw [thetaSL2_uSL two_eq_zero_stdField] at h4
  exact Subtype.ext h4

theorem twisted_E6_field_two_actual_central_cover_local_three_rank_four {X : Type} [Group X]
    [Finite X] (Y : Subgroup X)
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 1) :
    FourRankWitness X Y 3 ∧ 4 ≤ localRank 3 X ∧ 4 ≤ CFSG.twoLocalOddRank X := by
  obtain ⟨-, hm⟩ := hmod
  obtain ⟨L, _, _, hL, σ, hσ, φ, hφ, hker⟩ :=
    CFSG.RankThree.Chevalley.exists_surj_graphFixedRootGroup_of_model Nat.prime_two (le_refl 1) hm
  obtain ⟨e⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_stdGroup_of_card_eq_four
    (by rw [hL]; norm_num) σ (fun c => by simpa using hσ c)
  let φ' : Y →* stdGroup := e.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := e.surjective.comp hφ
  have hker' : φ'.ker ≤ Subgroup.center Y := by
    intro y hy
    rw [← hker]
    have h1 : e (φ y) = 1 := MonoidHom.mem_ker.mp hy
    exact MonoidHom.mem_ker.mpr (e.injective (h1.trans (map_one e).symm))
  obtain ⟨V, hV, hVcard, hVle⟩ := central_cover_of_levi_le stdLeviIn stdLeviEquiv Y φ' hφ' hker'
  have hVe : CFSG.Open.IsElemAbelian 3 V := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian
    3 V).mp hV
  obtain ⟨y0, hy0⟩ := hφ' stdTheta
  have hdvd : 2 ∣ orderOf y0 := by
    rw [← orderOf_stdTheta, ← hy0]
    exact orderOf_map_dvd φ' y0
  have hy00 : orderOf y0 ≠ 0 := (orderOf_pos y0).ne'
  set u : Y := y0 ^ (orderOf y0 / 2) with hudef
  have hu : orderOf u = 2 := orderOf_pow_orderOf_div hy00 hdvd
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hcomm : ∀ x : Y, x ∈ V → u * x = x * u := fun x hx =>
    oddF4_commute_of_involution hker' (Nat.prime_three.odd_of_ne_two (by norm_num)) hu2
      (hVe.2 x hx)
      (by
        have hxL : φ' x ∈ stdLeviIn := hVle hx
        rw [hudef, map_pow, hy0]
        exact ((commute_stdTheta_of_mem_stdLeviIn hxL).pow_left _).eq)
  set A : Subgroup X := V.map Y.subtype with hA
  have hAle : A ≤ Y ⊓ Subgroup.centralizer {(u : X)} := by
    refine le_inf (Subgroup.map_subtype_le V) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm x hx).symm
  have hAab : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hVe _
  have hAcard : Nat.card A = 3 ^ 4 := by
    rw [hA, Subgroup.card_map_of_injective Y.subtype_injective, hVcard]
  have huo : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hrank : 4 ≤ localRank 3 X :=
    CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian Nat.prime_three huo
      (le_inf_iff.1 hAle).2 hAab hAcard
  have hw : FourRankWitness X Y 3 :=
    ⟨u, u.2, huo, A, hAle, hAab, hAcard,
      (le_inf_iff.1 hAle).2.trans (CFSG.RankThree.CentralCover.centralizer_le_normalizer_zpowers _),
      CFSG.RankThree.CentralCover.isTwoLocal_normalizer_zpowers huo, hrank⟩
  exact ⟨hw, hrank, four_le_twoLocalOddRank_of_fourRankWitness Nat.prime_three (by norm_num) hw⟩

end CFSG.RankThree.PartOne
