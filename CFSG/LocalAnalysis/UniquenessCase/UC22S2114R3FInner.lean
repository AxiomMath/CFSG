module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UBorel
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

private noncomputable def uc22s2114r3f_fixer (L : Subgroup G) (X : Set (BarInf L)) :
    Subgroup G :=
  ((fixingSubgroup (MulAut (BarInf L)) X).comap (inducedBarInfAutHom L)).map
    (normalizer (L : Set G)).subtype

private theorem uc22s2114r3f_mem_fixer {L : Subgroup G} {X : Set (BarInf L)} {g : G}
    (hg : g ∈ normalizer (L : Set G)) :
    g ∈ uc22s2114r3f_fixer L X ↔ ∀ x ∈ X, inducedBarInfAutHom L ⟨g, hg⟩ x = x := by
  constructor
  · rintro ⟨⟨g', hg'⟩, hmem, rfl⟩ x hx
    exact (mem_fixingSubgroup_iff (MulAut (BarInf L))).1 hmem x hx
  · intro h
    exact ⟨⟨g, hg⟩, (mem_fixingSubgroup_iff (MulAut (BarInf L))).2 h, rfl⟩

theorem uc22s2114r3f_fix_zpowers {L : Subgroup G} {X : Set (BarInf L)} {b : G}
    (hbL : b ∈ normalizer (L : Set G)) (hfix : ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) :
    ∀ g (hg : g ∈ zpowers b), ∀ x ∈ X, inducedBarInfAutHom L ⟨g, zpowers_le.2 hbL hg⟩ x = x :=
  fun _ hg => (uc22s2114r3f_mem_fixer (zpowers_le.2 hbL hg)).1
    (zpowers_le.2 ((uc22s2114r3f_mem_fixer hbL).2 hfix) hg)


theorem uc22s2114r3f_false_of_inner (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {m f : ℕ} (hm : m = 6 ∨ m = 7)
    (hX : LieModel (BarInf L) .PSU m 2 f) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (D.T : Set G)) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1)
    (hodd : Odd c.n) (hrf : r ∣ f) (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hf1 : 1 ≤ f := (LieModel.admissible hX).2.1
  have hf7 : 7 ≤ f := hr7.trans (Nat.le_of_dvd (by omega) hrf)
  have hbr' : b ^ r = 1 := hbr ▸ pow_orderOf_eq_one b
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := Subtype.ext (by simpa using hbr')
    rw [this, map_one]
  have hZ := center_barInf_eq_bot hL.2.2
  obtain ⟨U, hU, hαU⟩ := uc22s2114_exists_map_eq (uc22p2214_isSylowOf_inf D.sylowM hL.1) hbL hbT
  obtain ⟨y₀, hy₀, hy₀1, hy₀r⟩ := uc22s2114_exists_of_inner hZ hαU hin hb1 hθr
  have h2f : r ∣ 2 ^ (2 * f) - 1 := by_contra fun hrn' => hy₀1
    (uc22s2114_eq_one_of_pow_mem hU.2.1 hr hr2 hrn' (uc22s2114r3u_pow_mem (by omega) hX hU hy₀)
      hy₀r)
  have hrq : r ∣ 2 ^ f - 1 :=
    (uc22s2114_dvd_two_pow_gcd_sub_one (d := f) (f := 2) hodd ⟨1, rfl⟩ hrn
      (by rwa [mul_comm])).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right c.n f))
  have hcinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    refine (injective_iff_map_eq_one _).2 fun z hz => ?_
    have hc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := DFunLike.congr_fun hz w
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hc
  obtain ⟨x₀, hx₀⟩ := hin
  have hx₀r : orderOf x₀ = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply hcinj
      rw [map_pow, hx₀, hθr, map_one]
    · rintro rfl
      exact hb1 (by rw [← hx₀, map_one])
  obtain ⟨p, hp, hpd, hpprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * f) (by omega) (by omega)
  have hfac : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [show 2 * f = f * 2 by ring, pow_mul, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
  have hpq : p ∣ 2 ^ f + 1 :=
    (hp.dvd_mul.1 (hfac ▸ hpd)).resolve_right (hpprim f (by omega) (by omega))
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpprim 2 (by norm_num) (by omega) (by norm_num)
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε, hXε⟩ : ∃ ε, ε ≤ 1 ∧ LieModel (BarInf L) .PSU (2 * 3 + ε) 2 f := by
    rcases hm with rfl | rfl
    · exact ⟨0, zero_le_one, hX⟩
    · exact ⟨1, le_rfl, hX⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := uc22pwliu_exists_hypPSU hf1 (by omega) hXε
  obtain ⟨A, hAc, hxA, ⟨y, hyA, hyr, hyx⟩, P, hPA, hPp, hPc⟩ :=
    uc22s2114r3f_exists_comm_hypPSU hK hε hr (by omega) hrq hp hp5 hpq (e x₀)
      (by rw [MulEquiv.orderOf_eq, hx₀r])
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨a', ha'⟩)
  have hcommA : ∀ {a : BarInf L}, e a ∈ A → ∀ u ∈ A, a * e.symm u * a⁻¹ = e.symm u := by
    intro a ha u hu
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hAcomm _ ha _ hu,
      mul_inv_cancel_right]
  obtain ⟨yb, hyb⟩ : ∃ yb, e yb = y := ⟨e.symm y, e.apply_symm_apply y⟩
  have hybA : e yb ∈ A := by
    rw [hyb]
    exact hyA
  have hybr : orderOf yb = r := by rw [← MulEquiv.orderOf_eq e, hyb, hyr]
  have hθyb : inducedBarInfAutHom L ⟨b, hbL⟩ yb = yb := by
    rw [← hx₀, MulAut.conj_apply]
    have h := hcommA hxA (e yb) hybA
    rwa [MulEquiv.symm_apply_apply] at h
  have hθP : ∀ z ∈ P.map e.symm.toMonoidHom, inducedBarInfAutHom L ⟨b, hbL⟩ z = z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := mem_map.1 hz
    rw [← hx₀, MulAut.conj_apply]
    exact hcommA hxA u (hPA hu)
  have hybP : ∀ z ∈ P.map e.symm.toMonoidHom, yb * z * yb⁻¹ = z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := mem_map.1 hz
    exact hcommA hybA u (hPA hu)
  have hybx : yb ∉ zpowers x₀ := fun h => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    exact hyx (mem_zpowers_iff.2 ⟨k, by rw [← map_zpow, hk, hyb]⟩)
  have hrK := uc22s2114r3f_not_dvd_card_solvableRadical hGA hL hm hX hr hr7
  have hBL : zpowers b ≤ normalizer (L : Set G) := zpowers_le.2 hbL
  have hbP : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one])
  have hYP : IsPGroup r ↥(zpowers yb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hybr, pow_one])
  have hbFY : b ∈ uc22s2114r3f_fixer L (zpowers yb : Set (BarInf L)) :=
    (uc22s2114r3f_mem_fixer hbL).2 fun x hx => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [map_zpow, hθyb]
  have hfixY : ∀ g (hg : g ∈ zpowers b), ∀ x ∈ zpowers yb,
      inducedBarInfAutHom L ⟨g, hBL hg⟩ x = x := fun g hg x hx =>
    (uc22s2114r3f_mem_fixer (hBL hg)).1 (zpowers_le.2 hbFY hg) x hx
  obtain ⟨y', hy'π, hy'o, hy'c⟩ :=
    uc22s2114r3f_exists_fixed_lift_elem hBL hbP hrK hrK hYP hfixY (mem_zpowers yb)
  have hy'L : (y' : G) ∈ L := y'.2
  have hy'r : orderOf (y' : G) = r := by rw [Subgroup.orderOf_coe, hy'o, hybr]
  have hconj : inducedBarInfAutHom L ⟨y', le_normalizer hy'L⟩ = MulAut.conj yb := by
    rw [uc22s2113_inducedBarInfAutHom_of_mem hy'L, ← hy'π]
    rfl
  have hy'b : (y' : G) ∉ zpowers b := fun h => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have h1 : inducedBarInfAutHom L ⟨y', le_normalizer hy'L⟩ = MulAut.conj (x₀ ^ k) := by
      have : (⟨(y' : G), le_normalizer hy'L⟩ : ↥(normalizer (L : Set G))) = ⟨b, hbL⟩ ^ k :=
        Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
      rw [this, map_zpow, map_zpow, hx₀]
    rw [hconj] at h1
    exact hybx (mem_zpowers_iff.2 ⟨k, (hcinj h1).symm⟩)
  have hcommE : ∀ a ∈ zpowers b, a * (y' : G) = y' * a := fun a ha =>
    mul_inv_eq_iff_eq_mul.1 (hy'c a ha)
  obtain ⟨-, hEcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (by rw [Nat.card_zpowers, hbr]) hy'r hy'b hcommE
  have hEp : IsPGroup r ↥(zpowers b ⊔ zpowers (y' : G)) := IsPGroup.of_card hEcard
  have hEr : 2 ≤ CFSG.Open.pRank r (zpowers b ⊔ zpowers (y' : G)) :=
    CFSG.GroupTheory.two_le_pRank_of_commute (mem_sup_left (mem_zpowers b))
      (mem_sup_right (mem_zpowers _)) hbr hy'r (hcommE b (mem_zpowers b)) hy'b
  have hEM : zpowers b ⊔ zpowers (y' : G) ≤ D.M :=
    sup_le (zpowers_le.2 (c.hBM hbB)) (zpowers_le.2 (hL.1.le hy'L))
  have hEN : zpowers b ⊔ zpowers (y' : G) ≤ normalizer (L : Set G) :=
    sup_le hBL (zpowers_le.2 (le_normalizer hy'L))
  have hbF : b ∈ uc22s2114r3f_fixer L (P.map e.symm.toMonoidHom : Set (BarInf L)) :=
    (uc22s2114r3f_mem_fixer hbL).2 hθP
  have hy'F : (y' : G) ∈ uc22s2114r3f_fixer L (P.map e.symm.toMonoidHom : Set (BarInf L)) :=
    (uc22s2114r3f_mem_fixer (le_normalizer hy'L)).2 fun z hz => by
      rw [hconj, MulAut.conj_apply]
      exact hybP z hz
  have hfixE : ∀ g (hg : g ∈ zpowers b ⊔ zpowers (y' : G)), ∀ x ∈ P.map e.symm.toMonoidHom,
      inducedBarInfAutHom L ⟨g, hEN hg⟩ x = x := fun g hg x hx =>
    (uc22s2114r3f_mem_fixer (hEN hg)).1
      (sup_le (zpowers_le.2 hbF) (zpowers_le.2 hy'F) hg) x hx
  have hPbp : IsPGroup p ↥(P.map e.symm.toMonoidHom) := hPp.of_equiv (e.symm.subgroupMap P)
  have hPbc : ¬ IsCyclic ↥(P.map e.symm.toMonoidHom) := fun h =>
    hPc ((e.symm.subgroupMap P).isCyclic.2 h)
  have hFM : 2 ≤ CFSG.Open.pRank p
      (D.M ⊓ centralizer ((zpowers b ⊔ zpowers (y' : G) : Subgroup G) : Set G)) :=
    (uc22s2114r3f_two_le_pRank_centralizer hEN hEp hrK hp2 hPbp hPbc hfixE).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf_right _ hL.1.le))
  have hpσ : p ∈ D.sig := hSg.four_mem p hp hp2
    ((uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hp hp2 (fun h => absurd h (by omega))
      hpq).trans (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le))
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have hb1' : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  have hN := PartOne.Section7.normalizer_le_of_two_le_pRank_inf_centralizer hsp
    (h76 p hpσ hp2 hsp) hEM hEp hEr hFM (zpowers b) le_sup_left (zpowers_ne_bot.2 hb1')
  exact (uc22s2112r2_normalizer hH c hL.1.le hbB (by rw [hbr]; exact hr)).2.1 hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
