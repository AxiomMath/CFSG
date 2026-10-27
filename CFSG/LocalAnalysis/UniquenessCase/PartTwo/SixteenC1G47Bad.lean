module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47V0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47A
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
import CFSG.Quasithin.Vol2.Ch12Sec2Lem22C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1ChoiceDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_le_hConjClosure (z : G) (U : Subgroup G) : U ≤ hConjClosure z U := by
  rw [hConjClosure]
  exact le_iSup_of_le ⟨1, one_mem _⟩ (le_of_eq (conjSubgroup_one U).symm)

theorem s16c1_G47_eTwo_le_cTilde (D : Data G) (hkit : OmegaKit) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (h41 : R16_41 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (ctx : G47Ctx D V₀ V L hV x)
    (hU : 64 ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val))) :
    eTwo D V₀ x.val ≤ F11.CTilde D.M V₀ V := by
  have hS := ctx.sect
  have hC := s16c1_cent_V0_le_pCore D hS ctx.setup ctx.sylow
  have hQM : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D ctx.sylow
  have hQS : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.T ⊓ centralizer ({x.val} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn ctx.sylow
  rw [eTwo, hConjClosure]
  refine iSup_le fun k y hy => ?_
  have hQh : conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) (k : G) =
      pCoreOf 2 (centralizer ({x.val} : Set G)) := s16c1_conjSubgroup_pCoreOf_self _ k.2
  have hQh_inv : conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) (k : G)⁻¹ =
      pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    s16c1_conjSubgroup_pCoreOf_self _ (Subgroup.inv_mem _ k.2)
  set c : G := (k : G) * y * (k : G)⁻¹ with hc_def
  have hc_mem : c ∈ V₀ ⊓ centralizer
      ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) := mem_conjSubgroup_iff.mp hy
  have hcCent : c ∈ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) :=
    hc_mem.2
  have hyQ : y ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    hQh ▸ E3.conjSubgroup_mono_left (k : G) hC hy
  have hyM : y ∈ D.M := hQM hyQ
  have hy_eq : y = (k : G)⁻¹ * c * (k : G) := by rw [hc_def]; group
  have hU1 : ∀ u ∈ uOne V x.val, y * u * y⁻¹ = u := by
    intro u hu
    have huQ : u ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) := hu.2
    have hkuQ : (k : G) * u * (k : G)⁻¹ ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
      rw [← hQh_inv]
      refine mem_conjSubgroup_iff.mpr ?_
      rw [show (k : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = u by group]
      exact huQ
    have hcomm : ((k : G) * u * (k : G)⁻¹) * c = c * ((k : G) * u * (k : G)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hcCent) _ (hQS hkuQ)
    have hc_conj : c * ((k : G) * u * (k : G)⁻¹) * c⁻¹ = (k : G) * u * (k : G)⁻¹ := by
      rw [← hcomm]; group
    calc y * u * y⁻¹ = (k : G)⁻¹ * c * (k : G) * u * ((k : G)⁻¹ * c * (k : G))⁻¹ := by
          rw [hy_eq]
      _ = (k : G)⁻¹ * (c * ((k : G) * u * (k : G)⁻¹) * c⁻¹) * (k : G) := by group
      _ = (k : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) * (k : G) := by rw [hc_conj]
      _ = u := by group
  exact s16c1_G47_cTilde_of_cent_uOne D hkit hkitB hkitC h41 ctx hU hyM hU1

theorem s16c1_G47_a_data (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)))
    (hnle : ¬ V₀ ≤ pCoreOf 2 (centralizer ({x.val} : Set G))) :
    ∃ a ∈ V₀, a ≠ 1 ∧ a ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) ∧
      centralizer ({a} : Set G) ≤ D.M ∧
      ∀ y ∈ V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)), y = 1 ∨ y = a := by
  classical
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hne : V₀ ≠ ⊥ := fun h => hnle (h ▸ bot_le)
  have hV₀M : V₀ ≤ D.M := hP.le.trans hP.le_M
  have hV₀pg : IsPGroup 2 V₀ := hP.elemAbelian₀.isPGroup
  have hV₀T : V₀ ≤ D.T := uc22p22na_le_sylow_of_normal D.sylowM hV₀M hP.le_normalizer₀ hV₀pg
  have hT₀ : D.T ≤ normalizer (V₀ : Set G) := D.sylowM.le.trans hP.le_normalizer₀
  obtain ⟨a, haV₀, ha1, haT⟩ :=
    CFSG.Quasithin.H13.Lem22.exists_ne_one_mem_centralizer D.sylowM.isPGroup hV₀T hT₀ hne
  have haS : a ∈ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (inf_le_left : D.T ⊓ centralizer ({x.val} : Set G) ≤ D.T) haT
  have haQ : a ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    s16c1_cent_V0_le_pCore D hS hx hSyl (Subgroup.mem_inf.2 ⟨haV₀, haS⟩)
  have hCU : centralizer ({a} : Set G) ≤ D.M := by
    rcases hS.setting.hyp151.hyp125.1 with ⟨-, hbot⟩ | ⟨-, hcu, -⟩
    · exact absurd hbot hne
    · exact (hcu a (hV₀T haV₀) (fun t ht => ((Subgroup.mem_centralizer_iff.1 haT) t ht).symm)
        ha1).1
  set W : Subgroup G := V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)) with hW
  have haW : a ∈ W := Subgroup.mem_inf.2 ⟨haV₀, haQ⟩
  have h1 := s16c1_G47_card_V0_le D hS hx hSyl
  have h4 := Sixteen21.card_le_four_of_hyp16 hS.setting.hyp16
  have hWlt : Nat.card ↥W < Nat.card ↥V₀ := by
    have hle : Nat.card ↥W ≤ Nat.card ↥V₀ := Subgroup.card_le_of_le inf_le_left
    by_contra hge
    have heq : W = V₀ := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    apply hnle
    rw [← heq]
    exact inf_le_right
  have hWpg : IsPGroup 2 ↥W := hV₀pg.to_le inf_le_left
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hWpg
  have hWle2 : Nat.card ↥W ≤ 2 := by
    by_contra hgt
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl
      · rw [pow_zero] at hm
        omega
      · rw [pow_one] at hm
        omega
    have h44 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  have hWne : W ≠ ⊥ := by
    intro hb
    rw [hb] at haW
    exact ha1 (Subgroup.mem_bot.1 haW)
  have hWcard : Nat.card ↥W = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot W).2 hWne
    omega
  obtain ⟨c0, -, hc0⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).1 hWcard
  refine ⟨a, haV₀, ha1, haQ, hCU, fun y hy => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    have h1' : (⟨y, hy⟩ : ↥W) = c0 := hc0 _ (fun h => hy1 (congrArg Subtype.val h))
    have h2' : (⟨a, haW⟩ : ↥W) = c0 := hc0 _ (fun h => ha1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1'.trans h2'.symm)

theorem s16c1_G47_stab_mem_M (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {a : G} (haV₀ : a ∈ V₀) (ha1 : a ≠ 1) {h : G}
    (hha : h * a * h⁻¹ = a) : h ∈ D.M := by
  have hne : V₀ ≠ ⊥ := by
    intro hb
    rw [hb] at haV₀
    exact ha1 (Subgroup.mem_bot.1 haV₀)
  have hmem : a ∈ V₀ ⊓ conjSubgroup V₀ h :=
    Subgroup.mem_inf.2 ⟨haV₀, mem_conjSubgroup_iff.2 (by rw [hha]; exact haV₀)⟩
  have hne2 : V₀ ⊓ conjSubgroup V₀ h ≠ ⊥ := fun hb => ha1 (Subgroup.mem_bot.1 (hb ▸ hmem))
  have hconj : conjSubgroup V₀ h = V₀ := s16c1_ti_V₀ hS hne h hne2
  have hnorm : h ∈ normalizer (V₀ : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer (A := V₀) (g := h)).1 hconj
  rwa [normalizer_eq_of_inCalV D (s16c1_inCalV0_of_sect16 hS hne).1] at hnorm

theorem s16c1_G47_alpha (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} {a : G} (haE : a ∈ eTwo D V₀ x.val)
    (hCa : centralizer ({a} : Set G) ≤ D.M) (hch : Chosen1647 D V₀ V x.val) :
    ∃ w ∈ V, ∃ e ∈ eTwo D V₀ x.val, w * e * w⁻¹ ≠ e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg, hzg⟩ := hch
  obtain ⟨hzV, hzVg⟩ := Subgroup.mem_inf.1 hzg
  have hnle : ¬ conjSubgroup V g ≤ D.M := hg.1.1.1
  obtain ⟨K, hKn, hKeq, hQ, ⟨l, hl, hVl⟩, hc1, hc2, hc3⟩ := hg.2
  have hVH : V ≤ centralizer ({x.val} : Set G) := s16c1_G47_le_centralizer hV x.val_mem
  have hVgH : conjSubgroup V g ≤ centralizer ({x.val} : Set G) := by
    intro y hy
    have hgy : g * y * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
    have hgz : g * x.val * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hzVg
    have hcomm := IsElemAbelian.comm hV hgz hgy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff.1 ht]
    have h1 : g * (x.val * y) * g⁻¹ = g * (y * x.val) * g⁻¹ := by
      calc g * (x.val * y) * g⁻¹ = (g * x.val * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x.val * g⁻¹) := hcomm
        _ = g * (y * x.val) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hlH : l ∈ centralizer ({x.val} : Set G) := (sup_le hVH hVgH) hl
  have hEinv : conjSubgroup (eTwo D V₀ x.val) l = eTwo D V₀ x.val := by
    simpa only [eTwo] using s16c1_conjSubgroup_hConjClosure (z := x.val)
      (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G)) hlH
  have hlaE : l * a * l⁻¹ ∈ eTwo D V₀ x.val := by
    have : a ∈ conjSubgroup (eTwo D V₀ x.val) l := by rw [hEinv]; exact haE
    exact mem_conjSubgroup_iff.1 this
  apply hnle
  intro y hy
  rw [hVl] at hy
  have hw : l * y * l⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
  have hwc := hcon _ hw _ hlaE
  have hya : y * a * y⁻¹ = a := by
    calc y * a * y⁻¹ = l⁻¹ * ((l * y * l⁻¹) * (l * a * l⁻¹) * (l * y * l⁻¹)⁻¹) * l := by group
      _ = l⁻¹ * (l * a * l⁻¹) * l := by rw [hwc]
      _ = a := by group
  apply hCa
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff.1 ht]
  exact (mul_inv_eq_iff_eq_mul.1 hya).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
