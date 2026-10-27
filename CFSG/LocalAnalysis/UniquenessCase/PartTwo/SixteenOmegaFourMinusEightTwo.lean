module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaFourMinusEightO1a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.B15P4 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s168e3_exists_elemAbelian_nine_of_two_conjugates
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (w : Vtil V₀ V hV) :
    ∃ E : Subgroup (MulAut (Vtil V₀ V hV)),
      E ≤ (lBar V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x)) ⊓
          MulAction.stabilizer (MulAut (Vtil V₀ V hV)) w ∧
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Hx : Subgroup (MulAut W) := barSub V₀ V hV (conjSubgroup L x)
  have hMs : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hxs : x ∈ stabTil V₀ V := hMs hxM
  let τ : MulAut W := actTil V₀ V hV ⟨x, hxs⟩
  have hHxmap : Hx = H.map (MulAut.conj τ⁻¹).toMonoidHom := by
    dsimp only [Hx, H, τ, lBar]
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hxs L]
  have hne : H ≠ Hx := by
    intro hEq
    apply hxn
    rw [s15_Infra_mem_nBar_iff c.setting.hyp151.hyp125 hV hxM]
    simpa only [Hx, H, lBar] using hEq.symm
  have hτA : τ ∈ A := actTil_mem_barSub V₀ V hV hxM hxs
  have hcompHx : IsComponentOf Hx A := by
    rw [hHxmap]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp (A.inv_mem hτA)
  have hcenterH : Subgroup.center ↥H = ⊥ :=
    omegaMinusFourEight_center_eq_bot hrow.2
  obtain ⟨a, haH, haord, hafix⟩ := omegaMinusFourEight_lBar_point_fixer c hrow w
  obtain ⟨b₀, hb₀H, hb₀ord, hb₀fix⟩ :=
    omegaMinusFourEight_lBar_point_fixer c hrow (τ w)
  let b : MulAut W := MulAut.conj τ⁻¹ b₀
  have hbHx : b ∈ Hx := by
    rw [hHxmap]
    exact Subgroup.mem_map.mpr ⟨b₀, hb₀H, rfl⟩
  have hbord : orderOf b = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj τ⁻¹) b₀
    simpa only [b, hb₀ord] using h
  have hbfix : b w = w := by
    calc b w = τ⁻¹ (b₀ (τ w)) := by
          simp only [b, MulAut.conj_apply, MulAut.mul_apply, inv_inv]
      _ = τ⁻¹ (τ w) := by rw [hb₀fix]
      _ = w := by simp
  have hcomm : a * b = b * a :=
    CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp hcompHx hne haH hbHx
  have hinf : ∀ z ∈ Subgroup.zpowers a, z ∈ Subgroup.zpowers b → z = 1 := by
    intro z hza hzb
    have hzH : z ∈ lBar V₀ V hV L := by simpa only [H] using Subgroup.zpowers_le.mpr haH hza
    have hzHx : z ∈ barSub V₀ V hV (conjSubgroup L x) := by
      simpa only [Hx] using Subgroup.zpowers_le.mpr hbHx hzb
    have hzcenter : (⟨z, hzH⟩ : ↥(lBar V₀ V hV L)) ∈
        Subgroup.center ↥(lBar V₀ V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext
        (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne
          (a := z) (b := (h : MulAut (Vtil V₀ V hV)))
          hcompHx hcomp (fun hh => hne hh.symm) hzHx h.2).symm
    rw [show Subgroup.center ↥(lBar V₀ V hV L) = ⊥ from hcenterH] at hzcenter
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hzcenter)
  let Mb : Subgroup (MulAut W) := (H ⊔ Hx) ⊓ MulAction.stabilizer (MulAut W) w
  have haMb : a ∈ Mb :=
    ⟨Subgroup.mem_sup_left haH, MulAction.mem_stabilizer_iff.mpr hafix⟩
  have hbMb : b ∈ Mb :=
    ⟨Subgroup.mem_sup_right hbHx, MulAction.mem_stabilizer_iff.mpr hbfix⟩
  obtain ⟨E, hEMb, hEel, hEcard⟩ :=
    CFSG.Quasithin.exists_elemAbelian_nine_of_commute151b haMb hbMb hcomm haord hbord hinf
  exact ⟨E, hEMb, hEel, hEcard⟩

theorem s168e3_sup_conj_le_barSub_centralizer
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {x : G} (hxM : x ∈ D.M) :
    lBar V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x) ≤
      barSub V₀ V hV (D.M ⊓ centralizer (V₀ : Set G)) := by
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Hx : Subgroup (MulAut W) := barSub V₀ V hV (conjSubgroup L x)
  let τ : MulAut W := actTil V₀ V hV ⟨x, c.m_le_stabTil hxM⟩
  have hHxmap : Hx = H.map (MulAut.conj τ⁻¹).toMonoidHom := by
    dsimp only [Hx, H, τ, lBar]
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (c.m_le_stabTil hxM) L]
  have hτA : τ ∈ A := actTil_mem_barSub V₀ V hV hxM (c.m_le_stabTil hxM)
  have hcompHx : IsComponentOf Hx A := by
    rw [hHxmap]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp (A.inv_mem hτA)
  have h4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D c.setting.hyp16
  have hH : H ≤ barSub V₀ V hV (D.M ⊓ centralizer (V₀ : Set G)) :=
    s16c11_le_barSub_centralizer_of_perfect D hV c.setting.hyp151.hyp125 h4
      (by simpa only [H, A] using hcomp.1) (perfect_of_isComponentOf hcomp)
  have hHx : Hx ≤ barSub V₀ V hV (D.M ⊓ centralizer (V₀ : Set G)) :=
    s16c11_le_barSub_centralizer_of_perfect D hV c.setting.hyp151.hyp125 h4
      (by simpa only [Hx, A] using hcompHx.1) (perfect_of_isComponentOf hcompHx)
  exact sup_le hH hHx

theorem s168e3_isL2_bar2_of_isL2_barSub
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) {K : Subgroup G} (hK : K ∈ calC D.M)
    {n : ℕ} (hn : 3 ≤ n)
    (hB : IsL2 ↥(barSub V₀ V hV K) n) : IsL2 (Bar2 K) n := by
  obtain ⟨hBev, -⟩ := P22fin.isL2Ev_of_isL2 hB
  obtain ⟨F, hFf, hFfin, hFch, hFcard, ⟨e⟩⟩ := P22y.exists_equiv_sl2 hBev
  let : Field F := hFf
  let : Finite F := hFfin
  let : CharP F 2 := hFch
  let π : Bar2 K →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (barSubBar2HomOfHyp125 h125 hK)
  have hπ : Function.Surjective π :=
    e.surjective.comp (barSubBar2HomOfHyp125_surjective h125 hK)
  have : Group.IsPerfect (Bar2 K) := ⟨hK.2.2.1⟩
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (P22y.isSimpleGroup_sl2 (F := F) h4).toNontrivial
  have hker_ne_top : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) F)
    obtain ⟨x, rfl⟩ := hπ y
    exact hy (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x))
  have hker : π.ker = ⊥ :=
    CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2_two_pow
      (m := n) hn hFcard (π := π) hπ
      (CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
        hK.2.2 π.ker hker_ne_top)
  let eK : Bar2 K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hker, hπ⟩
  exact uc22p22d_isL2_of_statedSL (by omega : 2 ≤ n) hFcard
    (eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
