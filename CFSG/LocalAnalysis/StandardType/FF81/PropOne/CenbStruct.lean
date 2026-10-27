module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
import Mathlib.GroupTheory.Transfer
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single_one)

private theorem inf_le_cB {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ≤ cB b z := by
  have hS := h.settingCore
  rw [cB, GGFF.SettingCore.Bt_eq_closure b z, Subgroup.centralizer_closure]
  intro d hd
  rw [Subgroup.mem_inf] at hd
  obtain ⟨hdL, hdb⟩ := hd
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hdb).symm
  · exact (Subgroup.mem_centralizer_iff.mp hdL) _ (GGFF.SettingCore.zs_mem z 0)
  · exact (Subgroup.mem_centralizer_iff.mp hdL) _ (GGFF.SettingCore.zs_mem z 1)
  · exact (Subgroup.mem_centralizer_iff.mp hdL) _ (GGFF.SettingCore.zs_mem z 2)

private theorem comm_vecElt_of_comm_zs {G : Type} [Group G] {L : Subgroup G} {z : Fin 3 → ↥L}
    {d : G} (hd : ∀ i, d * GGFF.zs z i = GGFF.zs z i * d) (v : Fin 3 → ZMod 3) :
    d * vecElt (GGFF.zs z) v = vecElt (GGFF.zs z) v * d := by
  have hgen : d ∈ Subgroup.centralizer ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    exacts [(hd 0).symm, (hd 1).symm, (hd 2).symm]
  have htor : d ∈ Subgroup.centralizer (GGFF.tor (GGFF.zs z)) := by
    rw [GGFF.SettingCore.tor_eq_closure, Subgroup.centralizer_closure]
    exact hgen
  exact ((Subgroup.mem_centralizer_iff.mp htor) _ (GGFF.vecElt_mem_tor _ v)).symm

theorem exists_mul_mem_inf_of_model {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (hA : HypA G n b L) (hM : GGFF.Model ↥L z)
    (hodd : Odd (Nat.card ↥(cB b z))) :
    ∀ x ∈ Subgroup.centralizer ({b} : Set G),
      ∃ d ∈ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G),
        ∃ l ∈ L, x = l * d := by
  have hS := hA.settingCore hM
  intro x hx
  have hn : ∀ k ∈ L, x * k * x⁻¹ ∈ L := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hA.nor hx) k).mp hk
  set α : MulAut ↥L := GGFF.conjAut hn with hαdef
  set E : Subgroup ↥L := (GGFF.tor z).map α.toMonoidHom with hEdef
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    hM.isElemAbelian_tor'.map α.toMonoidHom
  have hEcard : Nat.card E = 27 := by
    rw [hEdef, Subgroup.card_map_of_injective α.injective, hM.card_tor']
  obtain ⟨g, hg⟩ := hM.torus E hEab hEcard
  have hgC : (g : G) ∈ Subgroup.centralizer ({b} : Set G) := hA.le g.2
  set x' : G := (g : G)⁻¹ * x with hx'def
  have hx'C : x' ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [hx'def]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hgC) hx
  have hn' : ∀ k ∈ L, x' * k * x'⁻¹ ∈ L := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hA.nor hx'C) k).mp hk
  have hα' : ∀ v, ∃ w, GGFF.conjAut hn' (vecElt z v) = vecElt z w := by
    intro v
    have hvE : α (vecElt z v) ∈ E := by
      rw [hEdef]
      exact Subgroup.mem_map_of_mem α.toMonoidHom (GGFF.vecElt_mem_tor z v)
    obtain ⟨w, hw⟩ := (hg (α (vecElt z v))).mp hvE
    refine ⟨w, Subtype.ext ?_⟩
    have hwG : x * vecElt (GGFF.zs z) v * x⁻¹ =
        (g : G) * vecElt (GGFF.zs z) w * (g : G)⁻¹ := by
      have := congrArg (Subtype.val) hw
      simpa [hαdef, GGFF.conjAut_apply, ← GGFF.SettingCore.vecElt_zs] using this
    rw [GGFF.conjAut_apply, ← GGFF.SettingCore.vecElt_zs]
    calc x' * vecElt (GGFF.zs z) v * x'⁻¹
        = (g : G)⁻¹ * (x * vecElt (GGFF.zs z) v * x⁻¹) * (g : G) := by
          rw [hx'def]; group
      _ = (g : G)⁻¹ * ((g : G) * vecElt (GGFF.zs z) w * (g : G)⁻¹) * (g : G) := by
          rw [hwG]
      _ = vecElt (GGFF.zs z) w := by group
  obtain ⟨k, hk⟩ := hM.exists_conj_of_aut (GGFF.conjAut hn') hα'
  have hkC : (k : G) ∈ Subgroup.centralizer ({b} : Set G) := hA.le k.2
  set x'' : G := (k : G)⁻¹ * x' with hx''def
  have hx''C : x'' ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [hx''def]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hkC) hx'C
  have hn'' : ∀ y ∈ L, x'' * y * x''⁻¹ ∈ L := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hA.nor hx''C) y).mp hy
  have hkG : ∀ i, x' * GGFF.zs z i * x'⁻¹ = (k : G) * GGFF.zs z i * (k : G)⁻¹ := by
    intro i
    have := congrArg (Subtype.val) (hk i)
    simpa [GGFF.conjAut_apply] using this
  have hx''z : ∀ i, x'' * GGFF.zs z i = GGFF.zs z i * x'' := by
    intro i
    calc x'' * GGFF.zs z i = ((k : G)⁻¹ * x') * GGFF.zs z i := by rw [hx''def]
      _ = (k : G)⁻¹ * (x' * GGFF.zs z i * x'⁻¹) * (k : G) * x'' := by rw [hx''def]; group
      _ = (k : G)⁻¹ * ((k : G) * GGFF.zs z i * (k : G)⁻¹) * (k : G) * x'' := by rw [hkG i]
      _ = GGFF.zs z i * x'' := by group
  have hbx'' : Commute x'' b := Subgroup.mem_centralizer_singleton_iff.mp hx''C
  have hx''B : x'' ∈ cB b z := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨j, v, rfl⟩ := hS.mem_Bt.mp hy
    have hvcomm : x'' * vecElt (GGFF.zs z) v = vecElt (GGFF.zs z) v * x'' :=
      comm_vecElt_of_comm_zs hx''z v
    have hbcomm : b ^ j * x'' = x'' * b ^ j := (hbx''.symm.zpow_left j).eq
    calc (b ^ j * vecElt (GGFF.zs z) v) * x''
        = b ^ j * (vecElt (GGFF.zs z) v * x'') := by group
      _ = b ^ j * (x'' * vecElt (GGFF.zs z) v) := by rw [hvcomm]
      _ = (b ^ j * x'') * vecElt (GGFF.zs z) v := by group
      _ = (x'' * b ^ j) * vecElt (GGFF.zs z) v := by rw [hbcomm]
      _ = x'' * (b ^ j * vecElt (GGFF.zs z) v) := by group
  have hdvd : orderOf x'' ∣ Nat.card ↥(cB b z) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx''B)
  have hodd_ord : Odd (orderOf x'') := hodd.of_dvd_nat hdvd
  have hpow : ∀ m : ℕ, ∀ y : ↥L,
      (((GGFF.conjAut hn'') ^ m) y : G) = x'' ^ m * (y : G) * (x'' ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      have h1 : ((GGFF.conjAut hn'') ^ (m + 1)) y =
          ((GGFF.conjAut hn'') ^ m) ((GGFF.conjAut hn'') y) := by
        rw [pow_succ, MulAut.mul_apply]
      rw [h1, ih ((GGFF.conjAut hn'') y), GGFF.conjAut_apply]
      simp only [pow_succ]
      group
  have hα''m : (GGFF.conjAut hn'') ^ orderOf x'' = 1 := by
    ext y
    rw [hpow (orderOf x'') y, pow_orderOf_eq_one x'']
    simp
  obtain ⟨l, hl⟩ := hM.inner_odd (GGFF.conjAut hn'') (orderOf x'') hodd_ord hα''m
  have hlG : ∀ y ∈ L, x'' * y * x''⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    intro y hy
    have := congrArg (fun f : MulAut ↥L => ((f ⟨y, hy⟩ : ↥L) : G)) hl
    simpa [GGFF.conjAut_apply, MulAut.conj_apply] using this
  refine ⟨(l : G)⁻¹ * x'', ⟨?_, ?_⟩, (g : G) * (k : G) * (l : G), ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    calc y * ((l : G)⁻¹ * x'') = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * x'' := by group
      _ = (l : G)⁻¹ * (x'' * y * x''⁻¹) * x'' := by rw [← hlG y hy]
      _ = ((l : G)⁻¹ * x'') * y := by group
  · exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hA.le l.2)) hx''C
  · exact L.mul_mem (L.mul_mem g.2 k.2) l.2
  · calc x = (g : G) * (k : G) * x'' := by rw [hx''def, hx'def]; group
      _ = (g : G) * (k : G) * ((l : G) * ((l : G)⁻¹ * x'')) := by group
      _ = ((g : G) * (k : G) * (l : G)) * ((l : G)⁻¹ * x'') := by group

private theorem exists_cenL_decomp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∃ O : Subgroup G,
      O ≤ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ∧
      ¬ 3 ∣ Nat.card O ∧
      (∀ d ∈ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G),
        ∃ i : ℕ, ∃ o ∈ O, d = b ^ i * o) := by
  set D : Subgroup G := Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
    with hDdef
  have hD_le_L : D ≤ Subgroup.centralizer (L : Set G) := by rw [hDdef]; exact inf_le_left
  have hD_le_b : D ≤ Subgroup.centralizer ({b} : Set G) := by rw [hDdef]; exact inf_le_right
  have hbD : b ∈ D := by
    rw [hDdef]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun l hl => ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hl)
  have hPsub : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf D) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hbD)).symm
  obtain ⟨Q, hPsubQ⟩ := hPsub.exists_le_sylow
  have hQmap : (Q : Subgroup ↥D).map D.subtype = Subgroup.zpowers b := by
    refine h.facts.syl _ ((Subgroup.map_subtype_le (Q : Subgroup ↥D)).trans hD_le_L)
      ((Subgroup.map_subtype_le (Q : Subgroup ↥D)).trans hD_le_b) (Q.isPGroup'.map D.subtype) ?_
    refine Subgroup.zpowers_le.mpr ?_
    have hb_sub : (⟨b, hbD⟩ : ↥D) ∈ (Subgroup.zpowers b).subgroupOf D := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers b
    exact Subgroup.mem_map_of_mem D.subtype (hPsubQ hb_sub)
  have hQeq : (Q : Subgroup ↥D) = (Subgroup.zpowers b).subgroupOf D := by
    refine le_antisymm ?_ hPsubQ
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    have hq' : ((q : ↥D) : G) ∈ (Q : Subgroup ↥D).map D.subtype :=
      Subgroup.mem_map_of_mem D.subtype hq
    rwa [hQmap] at hq'
  have hcen : Subgroup.normalizer (Q : Set ↥D) ≤ Subgroup.centralizer (Q : Set ↥D) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hq' : (q : ↥D) ∈ (Subgroup.zpowers b).subgroupOf D := by
      rw [← hQeq]; exact hq
    have hqG : (q : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hq'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hqG
    have hzD : (z : G) ∈ Subgroup.centralizer ({b} : Set G) := hD_le_b z.2
    have hzCb : Commute (z : G) b := Subgroup.mem_centralizer_singleton_iff.mp hzD
    exact Subtype.ext (by
      change (q : G) * (z : G) = (z : G) * (q : G)
      rw [← hj]
      exact (hzCb.symm.zpow_left j).eq)
  set φ : ↥D →* ↥Q := MonoidHom.transferSylow Q hcen with hφdef
  set O : Subgroup G := φ.ker.map D.subtype with hOdef
  have hcomp : φ.ker.IsComplement' Q := MonoidHom.ker_transferSylow_isComplement' Q hcen
  have hKnot : ¬ 3 ∣ Nat.card φ.ker := MonoidHom.not_dvd_card_ker_transferSylow Q hcen
  have hOle : O ≤ D := by rw [hOdef]; exact Subgroup.map_subtype_le φ.ker
  have hOnot : ¬ 3 ∣ Nat.card O := by
    rw [hOdef, Subgroup.card_map_of_injective D.subtype_injective]
    exact hKnot
  refine ⟨O, hOle, hOnot, ?_⟩
  intro d hdD
  obtain ⟨⟨k, q⟩, hmul, -⟩ := hcomp.existsUnique ⟨d, hdD⟩
  have hd_q : d = (k : G) * (q : G) := by
    have := congrArg (Subtype.val) hmul
    simpa using this.symm
  have hq' : (q : ↥D) ∈ (Subgroup.zpowers b).subgroupOf D := by
    rw [← hQeq]; exact q.2
  have hqG : (q : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hq'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hqG
  have hkO : (k : G) ∈ O := by
    rw [hOdef]
    exact Subgroup.mem_map_of_mem D.subtype k.2
  have hkD : ((k : ↥D) : G) ∈ Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({b} : Set G) := (k : ↥D).2
  have hkb : Commute (k : G) b :=
    Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.mem_inf.mp hkD).2)
  have hbj : b ^ (j % 3) = b ^ j := by
    have := zpow_mod_orderOf b j
    rwa [h.hypA.ord] at this
  set i : ℕ := (j % 3).toNat with hidef
  have hmod : ((i : ℤ)) = j % 3 := by
    rw [hidef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
  have hbij : b ^ (i : ℤ) = b ^ j := by rw [hmod, hbj]
  refine ⟨i, (k : G), hkO, ?_⟩
  calc d = (k : G) * b ^ j := by rw [hd_q, ← hj]
    _ = b ^ j * (k : G) := (hkb.zpow_right j).eq
    _ = b ^ (i : ℤ) * (k : G) := by rw [← hbij]
    _ = b ^ i * (k : G) := by rw [zpow_natCast]

theorem exists_cen_decomp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (hodd : Odd (Nat.card ↥(cB b z))) :
    ∃ O : Subgroup G, O ≤ Subgroup.centralizer ({b} : Set G) ∧
      O ≤ Subgroup.centralizer (L : Set G) ∧ Odd (Nat.card O) ∧ ¬ 3 ∣ Nat.card O ∧
      ∀ x ∈ Subgroup.centralizer ({b} : Set G), ∃ i : ℕ, ∃ o ∈ O, ∃ l ∈ L,
        x = b ^ i * o * l := by
  obtain ⟨O, hOle, hOnot, hOdec⟩ := exists_cenL_decomp h
  have hO_le_b : O ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp (hOle hx)).2
  have hO_le_L : O ≤ Subgroup.centralizer (L : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp (hOle hx)).1
  refine ⟨O, hO_le_b, hO_le_L, ?_, hOnot, ?_⟩
  · exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (hOle.trans (inf_le_cB h)))
  · intro x hx
    obtain ⟨d, hdD, l, hlL, rfl⟩ := exists_mul_mem_inf_of_model h.hypA h.model hodd x hx
    obtain ⟨i, o, hoO, hd_eq⟩ := hOdec d hdD
    refine ⟨i, o, hoO, l, hlL, ?_⟩
    have hlb : Commute l b := Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hlL)
    have hlo : Commute l o := Subgroup.mem_centralizer_iff.mp (hO_le_L hoO) l hlL
    rw [hd_eq]
    calc l * (b ^ i * o) = (l * b ^ i) * o := by group
      _ = (b ^ i * l) * o := by rw [(hlb.pow_right i).eq]
      _ = b ^ i * (l * o) := by group
      _ = b ^ i * o * l := by rw [hlo.eq]; group

end CFSG.StandardType.FF81.PropOne

end
