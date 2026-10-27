module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenMathieuCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.GH74.M12.Hyp (tbl tmul tid tpow tinv wordT tA tB letterP wordP letterP_mem wordP_mem
  tbl_mul tbl_inv tbl_one tbl_getD tbl_m12gA tbl_m12gB G12)
open CFSG.RankThree.PartTwo.Toolkit.M12 (x y P0 basisE basisF basisA basisA' wE tbl_wE eq_iff_tbl
  tblG_mul tblG_one tblG_pow tblG_comm tbl_x tbl_y tbl_z tbl_a tbl_a' Enum)
open CFSG.ComponentClassification.M12Cover (beta beta_m12a beta_m12b exists_conj_or_conj_mul_beta
  m12_center conj_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open scoped commutatorElement

namespace Item434SporGen

theorem eq_bot_of_le_normalizer_of_cent {X : Type*} [Group X] [Finite X] {B Y : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hBY : B ≤ Subgroup.normalizer (Y : Set X))
    (hcent : ∀ v ∈ B, v ≠ 1 → Nat.card (Subgroup.centralizer ({v} : Set X)) = 54)
    (hCB : ∀ t : X, (∀ c ∈ B, t * c = c * t) → t ∈ B) : Y = ⊥ := by
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB (by rw [hB9]; norm_num) hBY
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3) ?_
  intro v hv hv1
  set W := Y ⊓ Subgroup.centralizer ({v} : Set X) with hWdef
  have hW54 : Nat.card W ∣ 54 := by
    rw [← hcent v hv hv1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hW3 : Nat.Coprime (Nat.card W) 27 := by
    have hcop : Nat.Coprime (Nat.card W) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact Nat.Coprime.pow_right 3 hcop
  have hW2 : Nat.card W ∣ 2 :=
    hW3.dvd_of_dvd_mul_right (by rw [show (2 : ℕ) * 27 = 54 by norm_num]; exact hW54)
  by_contra hne
  obtain ⟨t, htW, ht1⟩ : ∃ t ∈ W, t ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne fun x hx => (Subgroup.mem_bot).mpr (hall x hx)
  have hWc : Nat.card W = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hW2 with h1 | h2
    · exfalso
      have hW1 := Subgroup.card_eq_one.mp h1
      rw [hW1] at htW
      exact ht1 (Subgroup.mem_bot.mp htW)
    · exact h2
  have htB : ∀ c ∈ B, t * c = c * t := by
    intro c hc
    have hcv : c * v = v * c := congrArg Subtype.val (hB.1.is_comm.comm ⟨c, hc⟩ ⟨v, hv⟩)
    have htv : t * v = v * t := Subgroup.mem_centralizer_singleton_iff.mp htW.2
    have hctc : c * t * c⁻¹ ∈ W := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hBY hc) t).mp htW.1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hcv' : c⁻¹ * v = v * c⁻¹ := by
        calc c⁻¹ * v = c⁻¹ * (v * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * v) * c⁻¹ := by rw [hcv]
          _ = v * c⁻¹ := by group
      calc c * t * c⁻¹ * v = c * t * (v * c⁻¹) := by rw [mul_assoc (c * t), hcv']
        _ = c * (t * v) * c⁻¹ := by group
        _ = c * (v * t) * c⁻¹ := by rw [htv]
        _ = (c * v) * t * c⁻¹ := by group
        _ = (v * c) * t * c⁻¹ := by rw [hcv]
        _ = v * (c * t * c⁻¹) := by group
    have hne1 : c * t * c⁻¹ ≠ 1 := by
      intro h1
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have heq := Item434SporM11.eq_of_mem_of_card_eq_two hWc hctc htW hne1 ht1
    calc t * c = c * t * c⁻¹ * c := by rw [heq]
      _ = c * t := by group
  have ht3 : t ^ 3 = 1 := hB.2 t (hCB t htB)
  have ht2 : t ^ 2 = 1 := by
    have hdvd : orderOf t ∣ 2 := hWc ▸ Subgroup.orderOf_dvd_natCard W htW
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply ht1
  calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
    _ = 1 := by rw [ht3, ht2, inv_one, mul_one]

theorem mul_conj_mul_inv {X : Type*} [Group X] (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext u
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem noSignalizer_of_inner {X : Type*} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {B : Subgroup X}
    (hin : ∀ W : Subgroup X, ¬ 3 ∣ Nat.card W → B ≤ Subgroup.normalizer (W : Set X) → W = ⊥)
    (hout : ∀ α : MulAut X, (∀ f ∈ B, α f = f) → α ∈ (MulAut.conj : X →* MulAut X).range) :
    NoSignalizer B := by
  intro Y hY3 hBY
  set ι := (MulAut.conj : X →* MulAut X) with hι
  have hinj : Function.Injective ι := Item434Kit.conj_injective_of_center_eq_bot hZ
  set W := Y.comap ι with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    apply hY3
    have h1 : Nat.card (W.map ι) = Nat.card W := Subgroup.card_map_of_injective hinj
    have h2 : W.map ι ≤ Y := Subgroup.map_comap_le _ _
    exact (h1 ▸ h3).trans (Subgroup.card_dvd_of_le h2)
  have hBW : B ≤ Subgroup.normalizer (W : Set X) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hfN : ι f ∈ Subgroup.normalizer (Y : Set (MulAut X)) := hBY ⟨f, hf, rfl⟩
    simp only [hW, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hfN (ι w)
  have hW1 : W = ⊥ := hin W hW3 hBW
  have hYinn : ∀ g : X, ι g ∈ Y → g = 1 := fun g hg => by
    have : g ∈ W := hg
    rw [hW1] at this
    exact Subgroup.mem_bot.mp this
  rw [eq_bot_iff]
  intro α hα
  have hfix : ∀ f ∈ B, α f = f := by
    intro f hf
    have hfN : ι f ∈ Subgroup.normalizer (Y : Set (MulAut X)) := hBY ⟨f, hf, rfl⟩
    have hc : ι f * α * (ι f)⁻¹ * α⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hfN α).mp hα) (Y.inv_mem hα)
    have heq : ι f * α * (ι f)⁻¹ * α⁻¹ = ι (f * (α f)⁻¹) := by
      have h1 : α * (ι f)⁻¹ * α⁻¹ = (ι (α f))⁻¹ := by
        rw [← map_inv ι f, hι, mul_conj_mul_inv, map_inv α, map_inv]
      calc ι f * α * (ι f)⁻¹ * α⁻¹ = ι f * (α * (ι f)⁻¹ * α⁻¹) := by group
        _ = ι (f * (α f)⁻¹) := by rw [h1, map_mul, map_inv]
    rw [heq] at hc
    have h1 := hYinn _ hc
    rw [mul_inv_eq_one] at h1
    exact h1.symm
  obtain ⟨g, rfl⟩ := hout α hfix
  rw [Subgroup.mem_bot, hYinn g hα, map_one]

theorem tbl_m12bp : tbl CFSG.Sporadic.Schreier.m12bp = bpT := by
  decide +kernel

theorem apply_eq_iff_getD (σ : Equiv.Perm (Fin 12)) (i : Fin 12) :
    σ i = i ↔ (tbl σ).getD i.val 0 = i.val := by
  rw [tbl_getD]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

theorem tbl_beta_letter
    (l : ℤ) :
    tbl (beta (⟨letterP l, letterP_mem l⟩ : G12)).1 = letterTB l := by
  have ha : (⟨CFSG.Sporadic.Mathieu.m12gA, CFSG.Sporadic.Mathieu.m12a.2⟩ : G12) =
      CFSG.Sporadic.Mathieu.m12a := rfl
  have hb : (⟨CFSG.Sporadic.Mathieu.m12gB, CFSG.Sporadic.Mathieu.m12b.2⟩ : G12) =
      CFSG.Sporadic.Mathieu.m12b := rfl
  unfold letterTB
  by_cases h1 : l = 1
  · subst h1
    have e : (⟨letterP 1, letterP_mem 1⟩ : G12) = CFSG.Sporadic.Mathieu.m12a :=
      Subtype.ext (by simp [letterP])
    rw [e, beta_m12a, ite_eq_left rfl]
    exact tbl_m12gA
  by_cases h2 : l = -1
  · subst h2
    have e : (⟨letterP (-1), letterP_mem (-1)⟩ : G12) = CFSG.Sporadic.Mathieu.m12a⁻¹ :=
      Subtype.ext (by simp [letterP])
    rw [e, map_inv, beta_m12a, ite_eq_right (by decide), ite_eq_left rfl, Subgroup.coe_inv, tbl_inv]
    rw [show (CFSG.Sporadic.Mathieu.m12a : Equiv.Perm (Fin 12)) = CFSG.Sporadic.Mathieu.m12gA
      from rfl, tbl_m12gA]
  by_cases h3 : l = 2
  · subst h3
    have e : (⟨letterP 2, letterP_mem 2⟩ : G12) = CFSG.Sporadic.Mathieu.m12b :=
      Subtype.ext (by simp [letterP])
    rw [e, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, beta_m12b]
    exact tbl_m12bp
  · have e : (⟨letterP l, letterP_mem l⟩ : G12) = CFSG.Sporadic.Mathieu.m12b⁻¹ :=
      Subtype.ext (by simp [letterP, h1, h2, h3])
    rw [e, map_inv, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, Subgroup.coe_inv, tbl_inv,
      beta_m12b, tbl_m12bp]

theorem tbl_beta_wE
    (w : List ℤ) : tbl (beta (wE w)).1 = wordTB w := by
  induction w with
  | nil =>
    have e : wE [] = 1 := Subtype.ext rfl
    rw [e, map_one]
    exact tbl_one
  | cons l w ih =>
    have e : wE (l :: w) = (⟨letterP l, letterP_mem l⟩ : G12) * wE w := Subtype.ext rfl
    rw [e, map_mul, Subgroup.coe_mul, tbl_mul, tbl_beta_letter, ih]
    rfl

theorem tbl_beta_x :
    tbl (beta x).1 = bxT :=
  tbl_beta_wE CFSG.RankThree.PartTwo.Toolkit.M12.wX

theorem tbl_beta_y :
    tbl (beta y).1 = byT :=
  tbl_beta_wE CFSG.RankThree.PartTwo.Toolkit.M12.wY

theorem tbl_beta_z :
    tbl (beta ⁅x, y⁆).1 = bzT := by
  rw [map_commutatorElement, tblG_comm, tbl_beta_x, tbl_beta_y]
  rfl

theorem common_fix_iff
    {u v g : G12} (hu : g * beta u * g⁻¹ = u) (hv : g * beta v * g⁻¹ = v) :
    (∃ p : Fin 12, u.1 p = p ∧ v.1 p = p) ↔
      ∃ q : Fin 12, (beta u).1 q = q ∧ (beta v).1 q = q := by
  have hu' : (beta u).1 = g.1⁻¹ * u.1 * g.1 := by
    have h1 : beta u = g⁻¹ * u * g := by
      calc beta u = g⁻¹ * (g * beta u * g⁻¹) * g := by group
        _ = g⁻¹ * u * g := by rw [hu]
    rw [h1]
    rfl
  have hv' : (beta v).1 = g.1⁻¹ * v.1 * g.1 := by
    have h1 : beta v = g⁻¹ * v * g := by
      calc beta v = g⁻¹ * (g * beta v * g⁻¹) * g := by group
        _ = g⁻¹ * v * g := by rw [hv]
    rw [h1]
    rfl
  constructor
  · rintro ⟨p, hpu, hpv⟩
    refine ⟨g.1⁻¹ p, ?_, ?_⟩
    · rw [hu']; simp [hpu]
    · rw [hv']; simp [hpv]
  · rintro ⟨q, hqu, hqv⟩
    refine ⟨g.1 q, ?_, ?_⟩
    · rw [hu'] at hqu
      simp only [Equiv.Perm.mul_apply] at hqu
      have := congrArg g.1 hqu
      simpa using this
    · rw [hv'] at hqv
      simp only [Equiv.Perm.mul_apply] at hqv
      have := congrArg g.1 hqv
      simpa using this

theorem m12_fix :
    (⁅x, y⁆ : G12).1 0 = 0 ∧ x.1 0 = 0 ∧
      (∀ i : Fin 12, ¬ ((beta ⁅x, y⁆).1 i = i ∧ (beta x).1 i = i)) ∧
      (beta ⁅x, y⁆).1 2 = 2 ∧ (beta y).1 2 = 2 ∧
      ∀ i : Fin 12, ¬ ((⁅x, y⁆ : G12).1 i = i ∧ y.1 i = i) := by
  have h := m12_fix_check
  simp only [m12FixCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hz0, hx0⟩, hzx⟩, hz2⟩, hy2⟩, hzy⟩ := h
  have hbx : tbl (beta x).1 = bxT := tbl_beta_x
  have hby : tbl (beta y).1 = byT := tbl_beta_y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [apply_eq_iff_getD, tblG_comm, tbl_x, tbl_y]
    exact hz0
  · rw [apply_eq_iff_getD, tbl_x]
    exact hx0
  · intro i ⟨h1, h2⟩
    rw [apply_eq_iff_getD, tbl_beta_z] at h1
    rw [apply_eq_iff_getD, hbx] at h2
    rcases hzx i.val i.2 with h | h
    · exact h h1
    · exact h h2
  · rw [apply_eq_iff_getD, tbl_beta_z]
    exact hz2
  · rw [apply_eq_iff_getD, hby]
    exact hy2
  · intro i ⟨h1, h2⟩
    rw [apply_eq_iff_getD, tblG_comm, tbl_x, tbl_y] at h1
    rw [apply_eq_iff_getD, tbl_y] at h2
    rcases hzy i.val i.2 with h | h
    · exact h h1
    · exact h h2

theorem inner_of_fix_E
    (α : MulAut G12) (hα : ∀ f ∈ basisE.sub, α f = f) :
    α ∈ (MulAut.conj : G12 →* MulAut G12).range := by
  obtain ⟨g, h | h⟩ := exists_conj_or_conj_mul_beta α
  · exact ⟨g, h.symm⟩
  · exfalso
    have hzm : ⁅x, y⁆ ∈ basisE.sub := Subgroup.subset_closure (Set.mem_insert _ _)
    have hxm : x ∈ basisE.sub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hz : g * beta ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ := by
      have := hα _ hzm
      rwa [h, MulAut.mul_apply, MulAut.conj_apply] at this
    have hx : g * beta x * g⁻¹ = x := by
      have := hα _ hxm
      rwa [h, MulAut.mul_apply, MulAut.conj_apply] at this
    obtain ⟨q, hq1, hq2⟩ := (common_fix_iff hz hx).1 ⟨0, m12_fix.1, m12_fix.2.1⟩
    exact m12_fix.2.2.1 q ⟨hq1, hq2⟩

theorem inner_of_fix_F
    (α : MulAut G12) (hα : ∀ f ∈ basisF.sub, α f = f) :
    α ∈ (MulAut.conj : G12 →* MulAut G12).range := by
  obtain ⟨g, h | h⟩ := exists_conj_or_conj_mul_beta α
  · exact ⟨g, h.symm⟩
  · exfalso
    have hzm : ⁅x, y⁆ ∈ basisF.sub := Subgroup.subset_closure (Set.mem_insert _ _)
    have hym : y ∈ basisF.sub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hz : g * beta ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ := by
      have := hα _ hzm
      rwa [h, MulAut.mul_apply, MulAut.conj_apply] at this
    have hy : g * beta y * g⁻¹ = y := by
      have := hα _ hym
      rwa [h, MulAut.mul_apply, MulAut.conj_apply] at this
    obtain ⟨p, hp1, hp2⟩ := (common_fix_iff hz hy).2
      ⟨2, m12_fix.2.2.2.1, m12_fix.2.2.2.2.1⟩
    exact m12_fix.2.2.2.2.2 p ⟨hp1, hp2⟩

theorem card_centralizer_E
    {v : G12} (hv : v ∈ basisE.sub) (hv1 : v ≠ 1) :
    Nat.card (Subgroup.centralizer ({v} : Set G12)) = 54 :=
  m12_cent_check v (List.mem_append_left _
    ((CFSG.RankThree.PartTwo.Toolkit.M12.mem_E_iff v).1 hv)) hv1

theorem card_centralizer_F
    {v : G12} (hv : v ∈ basisF.sub) (hv1 : v ≠ 1) :
    Nat.card (Subgroup.centralizer ({v} : Set G12)) = 54 :=
  m12_cent_check v (List.mem_append_right _
    ((CFSG.RankThree.PartTwo.Toolkit.M12.mem_F_iff v).1 hv)) hv1

theorem mem_of_commute_of_card {B : Subgroup G12} (hBc : Nat.card B = 9)
    (hC : Nat.card (Subgroup.centralizer (B : Set G12)) = 9)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (t : G12) (ht : ∀ c ∈ B, t * c = c * t) :
    t ∈ B := by
  have hle : B ≤ Subgroup.centralizer (B : Set G12) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun c hc => hBab c hc b hb
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hBc])
  have htC : t ∈ Subgroup.centralizer (B : Set G12) :=
    Subgroup.mem_centralizer_iff.mpr fun c hc => (ht c hc).symm
  rwa [← heq] at htC

theorem noSignalizer_E
    (hE : CFSG.Assembly.IsElemAbelian 3 basisE.sub) : NoSignalizer basisE.sub := by
  have hCE : Nat.card (Subgroup.centralizer (basisE.sub : Set G12)) = 9 :=
    CFSG.RankThree.PartTwo.Toolkit.M12.card_centralizer_basisE
  have hab : ∀ a ∈ basisE.sub, ∀ b ∈ basisE.sub, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine noSignalizer_of_inner m12_center (fun W hW3 hEW => ?_) inner_of_fix_E
  exact eq_bot_of_le_normalizer_of_cent hE basisE.card hW3 hEW
    (fun v hv hv1 => card_centralizer_E hv hv1)
    (mem_of_commute_of_card basisE.card hCE hab)

theorem noSignalizer_F
    (hF : CFSG.Assembly.IsElemAbelian 3 basisF.sub) : NoSignalizer basisF.sub := by
  have hCF : Nat.card (Subgroup.centralizer (basisF.sub : Set G12)) = 9 :=
    CFSG.RankThree.PartTwo.Toolkit.M12.card_centralizer_basisF
  have hab : ∀ a ∈ basisF.sub, ∀ b ∈ basisF.sub, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine noSignalizer_of_inner m12_center (fun W hW3 hFW => ?_) inner_of_fix_F
  exact eq_bot_of_le_normalizer_of_cent hF basisF.card hW3 hFW
    (fun v hv hv1 => card_centralizer_F hv hv1)
    (mem_of_commute_of_card basisF.card hCF hab)

@[expose] noncomputable def sigE (ws : List (List ℤ)) (i : ℕ) : G12 := wE (ws.getD i [])

@[expose] noncomputable def evalSig (ws : List (List ℤ)) : List ℕ → G12
  | [] => 1
  | i :: w => sigE ws i * evalSig ws w

theorem tbl_evalSig (ws : List (List ℤ)) (w : List ℕ) :
    tbl (evalSig ws w).1 = evalSigT ws w := by
  induction w with
  | nil => exact tbl_one
  | cons i w ih =>
    rw [evalSig, Subgroup.coe_mul, tbl_mul, ih, sigE, tbl_wE]
    rfl

theorem evalSig_mem (ws : List (List ℤ)) (w : List ℕ) :
    evalSig ws w ∈ Subgroup.closure (Set.range fun i : Fin ws.length => sigE ws i) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    by_cases hi : i < ws.length
    · exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    · have e : sigE ws i = 1 := by
        rw [sigE, List.getD_eq_default _ _ (by omega)]
        exact Subtype.ext rfl
      rw [e]
      exact Subgroup.one_mem _

theorem fixGen_of_m12GenCheck {B : Subgroup G12} {ws : List (List ℤ)} {ps : List (List ℕ)}
    {wa wb : List ℕ} (h : m12GenCheck ws ps wa wb = true) (p : ℕ → G12)
    (hp : ∀ i < ws.length, tbl (p i).1 = ps.getD i tid ∧ p i ∈ B) : FixGen B := by
  simp only [m12GenCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨hσ, ha⟩, hb⟩ := h
  refine ⟨Set.range fun i : Fin ws.length => sigE ws i, ?_, ?_⟩
  · have ha' : CFSG.Sporadic.Mathieu.m12a = evalSig ws wa := by
      rw [eq_iff_tbl, tbl_evalSig, ha]
      exact tbl_m12gA
    have hb' : CFSG.Sporadic.Mathieu.m12b = evalSig ws wb := by
      rw [eq_iff_tbl, tbl_evalSig, hb]
      exact tbl_m12gB
    rw [← CFSG.ComponentClassification.M12Cover.m12_closure_eq_top, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [ha']; exact evalSig_mem ws wa
    · rw [hb']; exact evalSig_mem ws wb
  · rintro _ ⟨i, rfl⟩
    obtain ⟨⟨h2, hc⟩, h1⟩ := hσ i i.2
    obtain ⟨hpt, hpB⟩ := hp i i.2
    have hsig : tbl (sigE ws i).1 = sigT ws i := tbl_wE _
    refine ⟨?_, p i, hpB, ?_, ?_⟩
    · have hsq : sigE ws i ^ 2 = 1 := by
        rw [eq_iff_tbl, tblG_pow, hsig, h2, tblG_one]
      have hd : orderOf (sigE ws i) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      exact Nat.Coprime.coprime_dvd_left hd (by norm_num)
    · intro hp1
      apply h1
      rw [← hpt, hp1, tblG_one]
    · rw [eq_iff_tbl, tblG_mul, tblG_mul, hsig, hpt]
      exact hc.symm

@[expose] noncomputable def pA (i : ℕ) : G12 := if i = 0 then x * y else ⁅x, y⁆

@[expose] noncomputable def pA2 (i : ℕ) : G12 := if i = 3 then x * y ^ 2 else ⁅x, y⁆

theorem fixGen_A : FixGen basisA.sub := by
  refine fixGen_of_m12GenCheck m12_genA_check pA fun i hi => ?_
  have hz : ⁅x, y⁆ ∈ basisA.sub := Subgroup.subset_closure (Set.mem_insert _ _)
  have ha : x * y ∈ basisA.sub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hlen : sigAW.length = 4 := rfl
  rw [hlen] at hi
  interval_cases i
  · exact ⟨by rw [pA, ite_eq_left rfl, tbl_a]; rfl, by rw [pA, ite_eq_left rfl]; exact ha⟩
  · exact ⟨by rw [pA, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA, ite_eq_right (by decide)]; exact hz⟩
  · exact ⟨by rw [pA, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA, ite_eq_right (by decide)]; exact hz⟩
  · exact ⟨by rw [pA, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA, ite_eq_right (by decide)]; exact hz⟩

theorem fixGen_A' : FixGen basisA'.sub := by
  refine fixGen_of_m12GenCheck m12_genA2_check pA2 fun i hi => ?_
  have hz : ⁅x, y⁆ ∈ basisA'.sub := Subgroup.subset_closure (Set.mem_insert _ _)
  have ha : x * y ^ 2 ∈ basisA'.sub := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hlen : sigA2W.length = 4 := rfl
  rw [hlen] at hi
  interval_cases i
  · exact ⟨by rw [pA2, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA2, ite_eq_right (by decide)]; exact hz⟩
  · exact ⟨by rw [pA2, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA2, ite_eq_right (by decide)]; exact hz⟩
  · exact ⟨by rw [pA2, ite_eq_right (by decide), tblG_comm, tbl_x, tbl_y]; rfl,
      by rw [pA2, ite_eq_right (by decide)]; exact hz⟩
  · exact ⟨by rw [pA2, ite_eq_left rfl, tbl_a']; rfl, by rw [pA2, ite_eq_left rfl]; exact ha⟩

theorem kill9_m12
    (P : Subgroup G12) (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hP0 : Nat.card P0 = 3 ^ (Nat.card G12).factorization 3 := by
    rw [CFSG.RankThree.PartTwo.Toolkit.M12.card_P0]
    change 27 = 3 ^ (Nat.card NativeSporadic.M12).factorization 3
    rw [CFSG.Sporadic.Mathieu.card_M12, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hP0 hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hmem : P' ∈ {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} :=
    ⟨Item434AltPerm.map_conj_inv_le hg,
      by rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]⟩
  rw [CFSG.RankThree.PartTwo.Toolkit.M12.nine_eq] at hmem
  have hPeq : P = P'.map (MulAut.conj g).toMonoidHom :=
    (Item434AltPerm.map_conj_map_conj_inv P g).symm
  rcases hmem with h | h | h | h
  · right
    rw [h] at hP'e
    rw [hPeq, h]
    exact (noSignalizer_E hP'e).map_conj g
  · right
    rw [h] at hP'e
    rw [hPeq, h]
    exact (noSignalizer_F hP'e).map_conj g
  · left
    rw [hPeq, h]
    exact fixGen_A.map_conj g
  · left
    rw [Set.mem_singleton_iff] at h
    rw [hPeq, h]
    exact fixGen_A'.map_conj g

end Item434SporGen

section Families


theorem item434Spor_M12_9 :
    Item434Spor_M12_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 b' ?_
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) Item434SporGen.kill9_m12
  rw [CFSG.ComponentClassification.M12Cover.card_outer]
  norm_num

end Families

end CFSG.RankThree.PartTwo.Sec4
