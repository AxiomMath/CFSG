module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.RankThree.PartTwo.J2Residue.Endgame
import CFSG.RankThree.PartTwo.J2Residue.Lemma17
import CFSG.RankThree.PartTwo.J2Residue.ChiefFactor
import CFSG.RankThree.PartTwo.J2Residue.ChiefRep
import CFSG.RankThree.PartTwo.J2Residue.CentralInvolution
import CFSG.RankThree.PartTwo.J2Residue.Involution
import CFSG.RankThree.PartTwo.J2Residue.StepFour
import CFSG.RankThree.PartTwo.Sec16.Kcd166.FixRank
import CFSG.RankThree.PartTwo.Sec16.Kcd166.BlackburnScalar

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.RankThree CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_centralizer_closure_pair {b d x : G}
    (hb : x ∈ Subgroup.centralizer ({b} : Set G)) (hd : x ∈ Subgroup.centralizer ({d} : Set G)) :
    x ∈ Subgroup.centralizer (Subgroup.closure {b, d} : Set G) := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact Subgroup.mem_centralizer_iff.mp hb h (Set.mem_singleton h)
  · exact Subgroup.mem_centralizer_iff.mp hd h (Set.mem_singleton h)

omit [Finite G] in
private theorem le_centralizer_of_mem_thetaComponentsAt {L : Subgroup G} {b : G}
    (hL : L ∈ thetaComponentsAt 3 b) : L ≤ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨L', -, rfl⟩ := hL
  exact Subgroup.map_subtype_le L'

private theorem alpha_Y_facts {L LB : Subgroup G} {b d : G} (hJ : J2Config L d LB)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) (hbd : Commute b d) :
    LB ≤ Subgroup.centralizer (Subgroup.closure {b, d} : Set G) ⊓
        Subgroup.normalizer (LB : Set G) ∧
      Subgroup.closure {b, d} ≤ Subgroup.centralizer (Subgroup.closure {b, d} : Set G) ⊓
        Subgroup.normalizer (LB : Set G) ∧
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) ≤
        Subgroup.centralizer (Subgroup.closure {b, d} : Set G) ⊓
          Subgroup.normalizer (LB : Set G) := by
  have hLBL : LB ≤ L := hJ.lB_le.trans inf_le_left
  have hLBd : LB ≤ Subgroup.centralizer ({d} : Set G) := hJ.lB_le.trans inf_le_right
  have hCN : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (LB : Set G) :=
    (inf_le_inf_left L (centralizer_le_normalizer_zpowers d)).trans hJ.normalizer_le
  have hbLB : b ∈ Subgroup.centralizer (LB : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hLb (hLBL hx)) b (Set.mem_singleton b)).symm
  have hdLB : d ∈ Subgroup.centralizer (LB : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hLBd hx) d (Set.mem_singleton d)).symm
  refine ⟨le_inf (fun x hx => mem_centralizer_closure_pair (hLb (hLBL hx)) (hLBd hx))
    Subgroup.le_normalizer, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine ⟨mem_centralizer_closure_pair ?_ ?_, Subgroup.centralizer_le_normalizer _ hbLB⟩
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact hbd.symm.eq
    · refine ⟨mem_centralizer_closure_pair ?_ ?_, Subgroup.centralizer_le_normalizer _ hdLB⟩
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact hbd.eq
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  · intro x hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx.1
    exact ⟨mem_centralizer_closure_pair (hLb hxL) hx.2, hCN ⟨hxL, hx.2⟩⟩

theorem false_of_alpha (hfix : KJFix) (hsplit : KJSplit) (hcover : KJCover)
    (hrk : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3)
    {L LB Θ : Subgroup G} {b d e : G} (hJ : J2Config L d LB) (hU : CFSG.Open.pCoreOf 2 LB ≠ ⊥)
    (hLb : L ∈ thetaComponentsAt 3 b) (hb : orderOf b = 3) (hbd : Commute b d)
    (he : e ∈ Subgroup.closure {b, d}) (hed : e ∉ Subgroup.zpowers d)
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hΘ2 : CFSG.Open.pCoreOf 2 Θ = ⊥)
    (hUΘ : CFSG.Open.pCoreOf 2 LB ≤ Θ) (hΘe : Θ ≤ Subgroup.centralizer ({e} : Set G))
    (hYΘ : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (Θ : Set G)) : False := by
  set B : Subgroup G := Subgroup.closure {b, d} with hB
  set Y : Subgroup G := Subgroup.centralizer (B : Set G) ⊓ Subgroup.normalizer (LB : Set G)
    with hY
  obtain ⟨hLBY, hBY, hWY⟩ := alpha_Y_facts hJ (le_centralizer_of_mem_thetaComponentsAt hLb) hbd
  have hYB : Y ≤ Subgroup.centralizer (B : Set G) := inf_le_left
  have hYΘ' : Y ≤ Subgroup.normalizer (Θ : Set G) :=
    (hYB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he))).trans hYΘ
  obtain ⟨hZ1, hZ2, hZU, hZY, hYZ⟩ := omegaZOf_pCoreOf_facts hU hLBY inf_le_right
  set Z₀ := Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) with hZ₀
  obtain ⟨r, hr, hr5, F₁, F₂, hF₁Θ, hch, u, huZ, f, hfF, hfu⟩ :=
    exists_chiefFactor hΘs hΘ3 hΘ2 hZ2 hZ1 (hZU.trans hUΘ) hZY hYΘ'
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, hV1, hV2, hV3, ρ, q, hρ, hq⟩ := exists_chiefRep_of_isChiefFactorUnder hch
  letI := hV1
  letI := hV2
  haveI := hV3
  have hF₁ : IsPGroup r F₁ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup r Θ).to_le hF₁Θ
  have hloc := Sec16.Kcd166.card_le_sq_of_localRank_lt hr (hrk r hr (by omega))
  have h2 : (2 : ZMod r) ≠ 0 := by
    have := natCast_ne_zero_of_lt (r := r) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  have h3 : (3 : ZMod r) ≠ 0 := by
    have := natCast_ne_zero_of_lt (r := r) (n := 3) (by norm_num) (by omega)
    exact_mod_cast this
  have hdB : d ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdY : d ∈ Y := hBY hdB
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥Y, (σ : G) = d := ⟨⟨d, hdY⟩, rfl⟩
  have hσc : σ ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hσ]
    exact (Subgroup.mem_centralizer_iff.mp (hYB g.2) d hdB).symm
  have hd3 : d ^ 3 = 1 := by rw [← hJ.orderOf_d]; exact pow_orderOf_eq_one d
  have hσ3 : σ ^ 3 = 1 := Subtype.ext (by simp only [Subgroup.coe_pow, hσ, hd3]; rfl)
  have hσ1 : ρ σ ≠ 1 := by
    obtain ⟨f', hf', hf'd⟩ := exists_commutator_not_mem_of_alpha hJ hLb hb hbd he hed hΘ3 hΘe
      hLBY hBY hYB hYΘ' hr hr5 hF₁Θ hch
      ⟨u, hZU huZ, f, hfF, hfu⟩
    rw [Ne, hq.rho_eq_one_iff hch, hσ]
    exact fun h => hf'd (h f' hf')
  have hσcomm : ∀ g : ↥Y, ρ σ * ρ g = ρ g * ρ σ := fun g => by
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hσc g).symm]
  have hcube := rho_mul_rho_add_rho_add_one_eq_zero hρ hσcomm hσ3 hσ1
  have hR2 : ∀ t : ↥Y, t * t = 1 → t ≠ 1 →
      Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ 2 := fun t ht ht1 =>
    hq.finrank_ker_le_two Sec16.Kcd166.blackburnScalarAut_holds hr5 hloc hch hF₁ hσc hσ3 hσ1
      (isPGroup_zpowers_of_mul_self ht) ht1
  have hΛ : Group.IsPerfect (LB.subgroupOf Y) :=
    isPerfect_subgroupOf hJ.isPerfect_lB (hLBY.trans le_rfl)
  have hEn : (Z₀.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).mpr hYZ
  have hE2 : ∀ s ∈ Z₀.subgroupOf Y, s * s = 1 := fun s hs =>
    Subtype.ext (by simpa using ((mem_omegaZOf_iff _).mp hs).2.2)
  have hEΛ : Z₀.subgroupOf Y ≤ LB.subgroupOf Y := fun s hs =>
    (hZU.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 LB)) hs
  have hσΛ : σ ∈ LB.subgroupOf Y := Subgroup.mem_subgroupOf.mpr (hσ ▸ hJ.mem_lB)
  obtain ⟨z, hzE, hz1, hρz, -⟩ := exists_neg_one_of_cube h2 h3 hρ hEn hE2
    (subgroupOf_ne_bot hZ1 hZY) hΛ hEΛ hσΛ hσcomm hcube
    (fun s hs hs1 => hR2 s (hE2 s hs) hs1)
  obtain ⟨x, hxW, hx2, hx1, hxz, hxzc⟩ := exists_involution hJ
    (J2Config.four_le_card hfix hsplit hcover hJ hU) (z := (z : G)) hzE
    (fun h => hz1 (Subtype.ext h))
  have hxY : x ∈ Y := (sup_le hLBY hWY) hxW
  have h4 := finrank_le_two_mul_of_neg_one h2 ρ hR2 (x := ⟨x, hxY⟩) hρz (hE2 z hzE)
    (Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hxz (congrArg Subtype.val h)) (Subtype.ext hxzc)
  have htop : ∀ g ∈ LB.subgroupOf Y, ∀ w ∈ (⊤ : Submodule (ZMod r) V),
      ρ g w ∈ (⊤ : Submodule (ZMod r) V) :=
    fun _ _ _ _ => Submodule.mem_top
  have hdiv3 := three_dvd_finrank_of_isPerfect h3 ρ hΛ ⊤ htop hσΛ (fun g _ => hσcomm g)
    (fun w _ => by simpa using congrArg (fun φ => φ w) hcube)
  have heven := even_finrank_of_isPerfect h2 ρ hΛ ⊤ htop (hEΛ hzE)
    (fun w _ => by rw [hρz]; rfl)
  rw [finrank_top] at hdiv3 heven
  have hntV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hσ1 (LinearMap.ext fun v => Subsingleton.elim _ _)
  have hpos : 0 < Module.finrank (ZMod r) V := Module.finrank_pos
  obtain ⟨k, hk⟩ := heven
  omega

end CFSG.RankThree.PartTwo.J2Residue
