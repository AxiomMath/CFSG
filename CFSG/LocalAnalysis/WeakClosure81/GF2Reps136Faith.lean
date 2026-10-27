module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_wd_stable (L : Subgroup (MulAut W)) : StableUnder L (Wd L) := by
  intro l hl u hu
  change l u ∈ commSub ⊤ L
  have hLmap : L.map (MulAut.conj l).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
  have h := w1369_commSub_top_map_conj L l
  rw [hLmap] at h
  rw [h]
  exact Subgroup.mem_map_of_mem l.toMonoidHom hu

private theorem w1369_cd_stable (L : Subgroup (MulAut W)) : StableUnder L (Cd L) := by
  intro l hl u hu
  obtain ⟨huWd, huFix⟩ := Subgroup.mem_inf.mp hu
  refine Subgroup.mem_inf.mpr ⟨w1369_wd_stable L l hl u huWd, ?_⟩
  rw [mem_fixV] at huFix ⊢
  intro l' hl'
  have hconj : l⁻¹ * l' * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hl') hl
  have hfix := huFix _ hconj
  have h1 : l ((l⁻¹ * l' * l) u) = l' (l u) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact MulEquiv.apply_symm_apply l (l' (l u))
  rw [← h1]
  exact congrArg l hfix

private theorem w1369_le_stabSub_of_stable {A : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder A U) : A ≤ stabSub U := by
  intro a ha
  rw [mem_stabSub]
  intro u
  exact ⟨fun hau => by
    have := h a⁻¹ (A.inv_mem ha) (a u) hau
    simpa using this, h a ha u⟩

private theorem w1369_perfect {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (c : Ctx136 Y t L) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr c.comp.2.2.1)

private theorem w1369_wd_idem {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (c : Ctx136 Y t L) : commSub (Wd L) L = Wd L := by
  refine le_antisymm (commSub_mono le_top le_rfl) ?_
  exact s13_perfect_chain L (w1369_perfect c) (commSub (Wd L) L) (Wd L) ⊤ le_rfl le_rfl

private theorem w1369_fix_Wd (hw2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {a : MulAut W} (ha : a ∈ L) (haWd : ∀ u ∈ Wd L, a u * u⁻¹ ∈ Cd L)
    (hodd : Odd (orderOf a)) : Wd L ≤ fixV (Subgroup.zpowers a) := by
  have hW : ∀ g ∈ Subgroup.zpowers a, ∀ w ∈ Wd L, g w ∈ Wd L :=
    fun g hg => w1369_wd_stable L g (Subgroup.zpowers_le.mpr ha hg)
  have hcomm_le : commSub (Wd L) (Subgroup.zpowers a) ≤ Cd L := by
    rw [commSub_zpowers_eq_map hW]
    rintro _ ⟨u, hu, rfl⟩
    exact haWd u hu
  have hCd_fix : Cd L ≤ fixV (Subgroup.zpowers a) := by
    intro c hc
    rw [mem_fixV]
    intro x hx
    exact (mem_fixV.mp hc.2) x (Subgroup.zpowers_le.mpr ha hx)
  have hodd' : Odd (Nat.card (Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hcop := coprime_decomp (P := Subgroup.zpowers a) hodd' hw2 hW
  have hle_inf : commSub (Wd L) (Subgroup.zpowers a) ≤
      Wd L ⊓ fixV (Subgroup.zpowers a) :=
    le_inf (commSub_le_of_invariant hW) (hcomm_le.trans hCd_fix)
  have hbot : commSub (Wd L) (Subgroup.zpowers a) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ commSub (Wd L) (Subgroup.zpowers a) ⊓
        (Wd L ⊓ fixV (Subgroup.zpowers a)) := ⟨hx, hle_inf hx⟩
    rw [hcop.2] at hx'
    exact hx'
  exact commSub_eq_bot_iff.mp hbot

private theorem w1369_odd_card_ker {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) {K0 : Subgroup ↥L}
    (hK0c : K0 ≤ Subgroup.center ↥L) : Odd (Nat.card K0) := by
  have hpCoreY : pCoreOf 2 Y = ⊥ := by
    have hpc_norm : ((pCoreOf 2 Y).subgroupOf Y).Normal :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 Y Y le_rfl
        (by rw [Subgroup.subgroupOf_self]; infer_instance)
    have hpc_p : IsPGroup 2 (pCoreOf 2 Y) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype
    exact c.std.o2 (pCoreOf 2 Y) (Subgroup.map_subtype_le _) hpc_norm hpc_p
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  let P : Subgroup ↥L := Subgroup.zpowers (z : ↥L)
  have hPle : P ≤ Subgroup.center ↥L := Subgroup.zpowers_le.mpr (hK0c z.2)
  have hPn : P.Normal := Subgroup.normal_of_le_center hPle
  have hPsub : CFSG.Open.IsSubnormal P ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hPn.isSubnormal
  let Pm : Subgroup (MulAut W) := P.map L.subtype
  have htop_map : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hPmL : CFSG.Open.IsSubnormal Pm L := by
    have h := CFSG.Open.IsSubnormal.map L.subtype hPsub
    rwa [htop_map] at h
  have hsub : CFSG.Open.IsSubnormal Pm Y :=
    CFSG.Open.IsSubnormal.trans hPmL c.comp.2.1
  have hcard : Nat.card ↥Pm = 2 := by
    have hP : Nat.card ↥P = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe z, hz]
    rw [← hP]
    exact (Nat.card_congr
      (P.equivMapOfInjective L.subtype L.subtype_injective).toEquiv).symm
  have hP2 : IsPGroup 2 ↥Pm := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hcard]; norm_num⟩
  have hle :=
    CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub hP2
  rw [hpCoreY] at hle
  have hbot : Pm = ⊥ := le_bot_iff.mp hle
  have hzPm : ((z : ↥L) : MulAut W) ∈ Pm :=
    Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_zpowers (z : ↥L))
  have hz1 : ((z : ↥L) : MulAut W) = 1 := by
    rw [hbot] at hzPm
    exact Subgroup.mem_bot.mp hzPm
  have hz2 : orderOf ((z : ↥L) : MulAut W) = 2 := by
    rw [Subgroup.orderOf_coe (z : ↥L), Subgroup.orderOf_coe z]
    exact hz
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

private theorem w1369_eq_one_of_fixes_conjSubs (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hT : Tcl Y L) {a : MulAut W} (ha : a ∈ L)
    (hWd : Wd L ≤ fixV (Subgroup.zpowers a)) : a = 1 := by
  have hfix : ∀ g ∈ Y, ∀ v ∈ (Wd L).map g.toMonoidHom, a v = v := by
    intro g hg v hv
    by_cases hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W))
    · have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      have hWdmap : (Wd L).map g.toMonoidHom = Wd L := by
        have h := w1369_commSub_top_map_conj L g
        rw [hLmap] at h
        exact h.symm
      rw [hWdmap] at hv
      exact mem_fixV_zpowers_iff.mp (hWd hv)
    · obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
      have hTinv : commSub (Wd L) (L.map (MulAut.conj g⁻¹).toMonoidHom) = ⊥ :=
        hT g⁻¹ (Y.inv_mem hg) (fun h => hgN (by simpa using Subgroup.inv_mem _ h))
      have hfixinv : Wd L ≤ fixV (L.map (MulAut.conj g⁻¹).toMonoidHom) :=
        commSub_eq_bot_iff.mp hTinv
      have hmem : (MulAut.conj g⁻¹).toMonoidHom a ∈
          L.map (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ha
      have h1 : ((MulAut.conj g⁻¹).toMonoidHom a) w = w :=
        (mem_fixV.mp (hfixinv hw)) _ hmem
      have h2 : a (g w) = g w := by
        have := congrArg (fun x => g x) h1
        simpa [MulAut.conj_apply, mul_assoc] using this
      exact h2
  have hspan : (⨆ X ∈ conjSubs Y (Wd L), X) = ⊤ :=
    lemmaS c.comp.1 (comm_top_of_component c.std hw2 c.comp)
  have hle : (⨆ X ∈ conjSubs Y (Wd L), X) ≤ fixV (Subgroup.zpowers a) := by
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hg, rfl⟩ := hX
    intro v hv
    rw [mem_fixV_zpowers_iff]
    exact hfix g hg v hv
  rw [hspan] at hle
  exact eq_one_of_fixV_eq_top (top_le_iff.mp hle)

theorem faithful_on_wstar (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hT : Tcl Y L) : FaithOn L (Wd L) (Cd L) := by
  intro a ha haWd
  have hLWd : L ≤ stabSub (Wd L) := w1369_le_stabSub_of_stable (w1369_wd_stable L)
  have hLCd : L ≤ stabSub (Cd L) := w1369_le_stabSub_of_stable (w1369_cd_stable L)
  let ρ : ↥L →* MulAut (Sect (Wd L) (Cd L)) := B5.secHom L hLWd hLCd
  let K0 : Subgroup ↥L := ρ.ker
  have hK0ne : K0 ≠ ⊤ := by
    intro htop
    have htriv : ∀ l ∈ L, ∀ u ∈ Wd L, l u * u⁻¹ ∈ Cd L := by
      intro l hl u hu
      have hmem : (⟨l, hl⟩ : ↥L) ∈ K0 := by rw [htop]; exact Subgroup.mem_top _
      have hc : (⟨l, hl⟩ : ↥L) ∈ (B5.secHom L hLWd hLCd).ker := hmem
      exact (mem_centSec.mp ((B5.mem_ker_secHom L hLWd hLCd ⟨l, hl⟩).mp hc)).2 u hu
    have hle : commSub (Wd L) L ≤ Cd L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, u, hu, rfl⟩
      exact htriv l hl u hu
    have hWdidem : commSub (Wd L) L = Wd L := w1369_wd_idem c
    have hWd_le_fix : Wd L ≤ fixV L := by
      rw [← hWdidem]
      exact hle.trans inf_le_right
    have hWd_bot : Wd L = ⊥ := by
      have h := commSub_eq_bot_iff.mpr hWd_le_fix
      rwa [hWdidem] at h
    have hLbot : L = ⊥ := by
      have hcomm : commSub ⊤ L = ⊥ := hWd_bot
      have hfix : (⊤ : Subgroup W) ≤ fixV L := commSub_eq_bot_iff.mp hcomm
      rw [Subgroup.eq_bot_iff_forall]
      intro l hl
      exact MulEquiv.ext fun w => (mem_fixV.mp (hfix (Subgroup.mem_top w))) l hl
    have hLne : L ≠ ⊥ := by
      haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial c.comp.2.2
      exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
    exact hLne hLbot
  haveI hK0n : K0.Normal := inferInstance
  have hK0c : K0 ≤ Subgroup.center ↥L := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top c.comp.2.2 K0
      with h | h
    · exact h
    · exact absurd h hK0ne
  have hoddK0 : Odd (Nat.card K0) := w1369_odd_card_ker c hK0c
  have haK0 : (⟨a, ha⟩ : ↥L) ∈ K0 := by
    show (⟨a, ha⟩ : ↥L) ∈ (B5.secHom L hLWd hLCd).ker
    rw [B5.mem_ker_secHom]
    exact mem_centSec.mpr ⟨hLWd ha, haWd⟩
  have horder_dvd : orderOf a ∣ Nat.card K0 := by
    have h := orderOf_dvd_natCard (⟨⟨a, ha⟩, haK0⟩ : K0)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h
  have hodd_a : Odd (orderOf a) := Odd.of_dvd_nat hoddK0 horder_dvd
  have hfixWd : Wd L ≤ fixV (Subgroup.zpowers a) := w1369_fix_Wd hw2 ha haWd hodd_a
  exact w1369_eq_one_of_fixes_conjSubs hw2 c hT ha hfixWd

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
