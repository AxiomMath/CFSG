module

public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.RankThree.GF2n.Tim77Prop24Conj
public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.LargeExtraspecial.S9TIX

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem t75_conjSubgroup_eq (T : Subgroup G) (g : G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g T = conjSubgroup T g⁻¹ := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, mem_conjSubgroup_iff]
  simp

private theorem conjSubgroup_inf (g : G) (U V : Subgroup G) :
    conjSubgroup (U ⊓ V) g = conjSubgroup U g ⊓ conjSubgroup V g :=
  Subgroup.map_inf_eq U V (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem card_conjSubgroup' (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup T g) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem inf_conjSubgroup_eq_bot_or_eq {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    (a b : G) :
    conjSubgroup V a ⊓ conjSubgroup V b = ⊥ ∨ conjSubgroup V a = conjSubgroup V b := by
  set A := conjSubgroup V a with hA
  set B := conjSubgroup V b with hB
  have hmap : conjSubgroup (A ⊓ B) a⁻¹ = conjSubgroup A a⁻¹ ⊓ conjSubgroup B a⁻¹ :=
    conjSubgroup_inf a⁻¹ A B
  have hA' : conjSubgroup A a⁻¹ = V := by
    rw [hA, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hB'' : conjSubgroup B a⁻¹ = conjSubgroup V (b * a⁻¹) := by
    rw [hB, conjSubgroup_conjSubgroup]
  have hTI' : V ⊓ conjSubgroup V (b * a⁻¹) = ⊥ ∨ V ⊓ conjSubgroup V (b * a⁻¹) = V := by
    have h := hTI (a * b⁻¹)
    rw [t75_conjSubgroup_eq] at h
    rwa [show (a * b⁻¹)⁻¹ = b * a⁻¹ by group] at h
  rcases hTI' with hbot | heq
  · left
    have hzero : conjSubgroup (A ⊓ B) a⁻¹ = ⊥ := by rw [hmap, hA', hB'', hbot]
    have hcongr := congrArg (fun X => conjSubgroup X a) hzero
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hcongr
    rw [hcongr]
    exact Subgroup.map_bot _
  · right
    have hAeq : A ⊓ B = A := by
      have hcongr : conjSubgroup (A ⊓ B) a⁻¹ = conjSubgroup A a⁻¹ := by rw [hmap, hA', hB'', heq]
      have hcongr2 := congrArg (fun X => conjSubgroup X a) hcongr
      simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using hcongr2
    have hle : A ≤ B := hAeq ▸ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hA, hB, card_conjSubgroup', card_conjSubgroup'])

theorem conjSubgroup_eq_of_isTI {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G}
    (hne : V ⊓ conjSubgroup V g ≠ ⊥) : conjSubgroup V g = V := by
  rcases inf_conjSubgroup_eq_bot_or_eq hTI 1 g with hbot | heq
  · rw [conjSubgroup_one] at hbot
    exact absurd hbot hne
  · rw [conjSubgroup_one] at heq
    exact heq.symm

theorem inf_conjSubgroup_eq_bot_of_isTI {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    {g : G} (hne : conjSubgroup V g ≠ V) : V ⊓ conjSubgroup V g = ⊥ := by
  rcases inf_conjSubgroup_eq_bot_or_eq hTI 1 g with hbot | heq
  · rw [conjSubgroup_one] at hbot
    exact hbot
  · rw [conjSubgroup_one] at heq
    exact absurd heq.symm hne

theorem inf_conj_eq_bot_or_eq_conj {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (g : G) :
    ∀ h : G, conjSubgroup V g ⊓ conjSubgroup (conjSubgroup V g) h = ⊥ ∨
      conjSubgroup (conjSubgroup V g) h = conjSubgroup V g := by
  intro h
  rw [conjSubgroup_conjSubgroup]
  exact (inf_conjSubgroup_eq_bot_or_eq hTI g (g * h)).imp id Eq.symm

theorem centralizer_le_normalizer_of_isTI {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
  intro x hx
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  refine conjSubgroup_eq_of_isTI hTI ?_
  rintro hbot
  have hcomm : v * x = x * v := Subgroup.mem_centralizer_iff.mp hx v (Set.mem_singleton v)
  have hvx : v ∈ conjSubgroup V x := by
    rw [mem_conjSubgroup_iff]
    rw [show x * v * x⁻¹ = v by rw [← hcomm]; group]
    exact hv
  have : v ∈ V ⊓ conjSubgroup V x := ⟨hv, hvx⟩
  rw [hbot, mem_bot] at this
  exact hv1 this

theorem centralizer_le_normalizer_conj {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (g : G) {v : G}
    (hv : v ∈ conjSubgroup V g) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ normalizer (conjSubgroup V g : Set G) := by
  intro x hx
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hcomm : v * x = x * v := Subgroup.mem_centralizer_iff.mp hx v (Set.mem_singleton v)
  have hvx : v ∈ conjSubgroup V (g * x) := by
    rw [← conjSubgroup_conjSubgroup, mem_conjSubgroup_iff]
    rw [show x * v * x⁻¹ = v by rw [← hcomm]; group]
    exact hv
  rcases inf_conjSubgroup_eq_bot_or_eq (V := V) hTI g (g * x) with hbot | heq
  · exfalso
    have : v ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hv, hvx⟩
    exact hv1 (mem_bot.mp this)
  · rw [conjSubgroup_conjSubgroup]
    exact heq.symm

theorem commute_mem_normalizer {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    {W W' : Subgroup G}
    (hW : ∃ a : G, W = conjSubgroup V a) (hW' : ∃ b : G, W' = conjSubgroup V b)
    {w w' : G} (hw : w ∈ W) (hw1 : w ≠ 1) (hw' : w' ∈ W') (hw'1 : w' ≠ 1)
    (hc : w * w' = w' * w) :
    w ∈ normalizer (W' : Set G) ∧ w' ∈ normalizer (W : Set G) := by
  obtain ⟨a, rfl⟩ := hW
  obtain ⟨b, rfl⟩ := hW'
  refine ⟨?_, ?_⟩
  · refine centralizer_le_normalizer_conj (V := V) hTI b hw' hw'1 ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc.symm
  · refine centralizer_le_normalizer_conj (V := V) hTI a hw hw1 ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc

theorem isElemAbelian_conjSubgroup' {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    IsElemAbelian 2 (conjSubgroup V g) := by
  have h := CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup hV g⁻¹
  rw [t75_conjSubgroup_eq] at h
  simpa using h

theorem isTI_conj {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (g : G) :
    CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V g) := by
  have h := CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g⁻¹
  rw [t75_conjSubgroup_eq] at h
  simpa using h

theorem nVSub_inf_bSub_eq_bot {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V) :
    nVSub V g ⊓ bSub V g = ⊥ := by
  have hVW : V ⊓ conjSubgroup V g = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hg
  have hle : nVSub V g ⊓ bSub V g ≤ V ⊓ conjSubgroup V g := by
    rw [nVSub, bSub]
    exact le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_left)
  exact le_bot_iff.mp (hVW ▸ hle)

theorem nVSub_comm_bSub {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V)
    {u b : G} (hu : u ∈ nVSub V g) (hb : b ∈ bSub V g) : u * b = b * u := by
  have hVW : V ⊓ conjSubgroup V g = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hg
  have huV : u ∈ V := (mem_nVSub.mp hu).1
  have huN : u ∈ normalizer (conjSubgroup V g) := (mem_nVSub.mp hu).2
  have hbW : b ∈ conjSubgroup V g := (mem_bSub.mp hb).1
  have hbN : b ∈ normalizer V := (mem_bSub.mp hb).2
  have hmemV : u * b * u⁻¹ * b⁻¹ ∈ V := by
    have h1 : b * u⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hbN u⁻¹).mp (V.inv_mem huV)
    rw [show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
    exact Subgroup.mul_mem V huV h1
  have hmemW : u * b * u⁻¹ * b⁻¹ ∈ conjSubgroup V g := by
    have h1 : u * b * u⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp huN b).mp hbW
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem hbW)
  have hbot : u * b * u⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hVW]
    exact ⟨hmemV, hmemW⟩
  rw [mem_bot] at hbot
  have h : (u * b) * (b * u)⁻¹ = 1 := by simpa [mul_inv_rev, mul_assoc] using hbot
  exact mul_inv_eq_one.mp h

theorem bSub_inf_centralizer_eq_bot {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V)
    {x : G} (hxV : x ∈ V) (hxU : x ∉ nVSub V g) :
    bSub V g ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  have hbW : b ∈ conjSubgroup V g := (mem_bSub.mp hbB).1
  by_cases hb1 : b = 1
  · exact Subgroup.mem_bot.mpr hb1
  · have hxN : x ∈ normalizer (conjSubgroup V g : Set G) :=
      centralizer_le_normalizer_conj hTI g hbW hb1
        (Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (Subgroup.mem_centralizer_iff.mp hbC x (Set.mem_singleton x)).symm)
    exact (hxU (mem_nVSub.mpr ⟨hxV, hxN⟩)).elim

theorem nVSub_inf_centralizer_eq_bot {V : Subgroup G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V)
    {y : G} (hyW : y ∈ conjSubgroup V g) (hyB : y ∉ bSub V g) :
    nVSub V g ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro u hu
  obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
  have huV : u ∈ V := (mem_nVSub.mp huU).1
  by_cases hu1 : u = 1
  · exact Subgroup.mem_bot.mpr hu1
  · have hyN : y ∈ normalizer (V : Set G) :=
      centralizer_le_normalizer_of_isTI hTI huV hu1
        (Subgroup.mem_centralizer_iff.mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact (Subgroup.mem_centralizer_iff.mp huC y (Set.mem_singleton y)).symm)
    exact (hyB (mem_bSub.mpr ⟨hyW, hyN⟩)).elim

private theorem commute_commutator_of_mem_normalizer {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {v b : G} (hv : v ∈ V) (hb2 : b * b = 1)
    (hbN : b ∈ normalizer (V : Set G)) : b * ⁅v, b⁆ = ⁅v, b⁆ * b := by
  have hv2 : v * v = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV hv
  have hcV : ⁅v, b⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbN v).mp hv
    have h2 : b * v⁻¹ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbN v⁻¹).mp (V.inv_mem hv)
    have e : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h2
  have hc2 : ⁅v, b⁆ * ⁅v, b⁆ = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV hcV
  have hcV' : ⁅b, v⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbN v).mp hv
    exact V.mul_mem h1 (V.inv_mem hv)
  have hcc : ⁅b, v⁆ * ⁅b, v⁆ = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV hcV'
  obtain ⟨hbc, -⟩ :=
    CFSG.LargeExtraspecial.S9.TIX.commute_commutator_of_involutions hb2 hv2 rfl hcc
  have hinv : ⁅v, b⁆ = ⁅b, v⁆⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hinv]
  have hbc' : b * ⁅b, v⁆⁻¹ = ⁅b, v⁆⁻¹ * b := by
    have h : (b * ⁅b, v⁆)⁻¹ = (⁅b, v⁆ * b)⁻¹ := congrArg Inv.inv hbc
    rw [show (b * ⁅b, v⁆)⁻¹ = ⁅b, v⁆⁻¹ * b by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2],
        show (⁅b, v⁆ * b)⁻¹ = b * ⁅b, v⁆⁻¹ by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2]] at h
    exact h.symm
  exact hbc'

theorem commutator_mem_nVSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} {v b : G} (hv : v ∈ V)
    (hb : b ∈ bSub V g) : ⁅v, b⁆ ∈ nVSub V g := by
  have hbW : b ∈ conjSubgroup V g := (mem_bSub.mp hb).1
  have hbN : b ∈ normalizer V := (mem_bSub.mp hb).2
  have hb2 : b * b = 1 :=
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_self (isElemAbelian_conjSubgroup' hV g) hbW
  have hcV : ⁅v, b⁆ ∈ V := by
    rw [commutatorElement_def]
    have h2 : b * v⁻¹ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbN v⁻¹).mp (V.inv_mem hv)
    have e : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h2
  refine mem_nVSub.mpr ⟨hcV, ?_⟩
  by_cases hb1 : b = 1
  · subst hb1
    simp [commutatorElement_def]
  · have hcomm : b * ⁅v, b⁆ = ⁅v, b⁆ * b :=
      commute_commutator_of_mem_normalizer hV hv hb2 hbN
    exact centralizer_le_normalizer_conj hTI g hbW hb1
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm)

theorem commutator_mem_bSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} {w u : G}
    (hw : w ∈ conjSubgroup V g) (hu : u ∈ nVSub V g) : ⁅w, u⁆ ∈ bSub V g := by
  have huV : u ∈ V := (mem_nVSub.mp hu).1
  have huN : u ∈ normalizer (conjSubgroup V g) := (mem_nVSub.mp hu).2
  have hu2 : u * u = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV huV
  have hcW : ⁅w, u⁆ ∈ conjSubgroup V g := by
    rw [commutatorElement_def]
    have h1 : u * w⁻¹ * u⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp huN w⁻¹).mp ((conjSubgroup V g).inv_mem hw)
    rw [show w * u * w⁻¹ * u⁻¹ = w * (u * w⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem (conjSubgroup V g) hw h1
  refine mem_bSub.mpr ⟨hcW, ?_⟩
  by_cases hu1 : u = 1
  · subst hu1
    simp [commutatorElement_def]
  · have hcomm : u * ⁅w, u⁆ = ⁅w, u⁆ * u :=
      commute_commutator_of_mem_normalizer (isElemAbelian_conjSubgroup' hV g) hw hu2 huN
    exact centralizer_le_normalizer_of_isTI hTI huV hu1
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm)

theorem exists_mul_of_mem_sup_nVSub_bSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V)
    {x : G} (hx : x ∈ nVSub V g ⊔ bSub V g) :
    ∃ u ∈ nVSub V g, ∃ b ∈ bSub V g, x = u * b := by
  have hnorm : bSub V g ≤ normalizer (nVSub V g : Set G) := by
    intro b hb
    have hfix : ∀ u ∈ nVSub V g, b * u * b⁻¹ = u := by
      intro u hu
      rw [(nVSub_comm_bSub hTI hg hu hb).symm]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hfix u hu]
      exact hu
    · intro hu
      have hb2 : b * b = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
        (isElemAbelian_conjSubgroup' hV g) (mem_bSub.mp hb).1
      have h2 : b * (b * u * b⁻¹) * b⁻¹ = b * u * b⁻¹ := hfix _ hu
      rw [show b * (b * u * b⁻¹) * b⁻¹ = u by
            rw [show b * (b * u * b⁻¹) * b⁻¹ = (b * b) * u * (b⁻¹ * b⁻¹) by group,
              hb2, show b⁻¹ * b⁻¹ = 1 by rw [← mul_inv_rev, hb2, inv_one], one_mul,
              mul_one]] at h2
      rwa [h2]
  have hx' : x ∈ ((nVSub V g : Set G) * (bSub V g : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (nVSub V g) (bSub V g) hnorm]
    exact hx
  obtain ⟨u, hu, b, hb, rfl⟩ := hx'
  exact ⟨u, hu, b, hb, rfl⟩

theorem isElemAbelian_sup_nVSub_bSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V) :
    IsElemAbelian 2 (nVSub V g ⊔ bSub V g) := by
  have hUab : ∀ a ∈ nVSub V g, ∀ b ∈ nVSub V g, a * b = b * a := fun a ha b hb =>
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hV (mem_nVSub.mp ha).1 (mem_nVSub.mp hb).1
  have hBab : ∀ a ∈ bSub V g, ∀ b ∈ bSub V g, a * b = b * a := fun a ha b hb =>
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm (isElemAbelian_conjSubgroup' hV g)
      (mem_bSub.mp ha).1 (mem_bSub.mp hb).1
  have hUB : ∀ u ∈ nVSub V g, ∀ b ∈ bSub V g, u * b = b * u := fun u hu b hb =>
    nVSub_comm_bSub hTI hg hu hb
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu, u', hu', ha⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg a.2
    obtain ⟨v, hv, v', hv', hb⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg b.2
    change (a : G) * (b : G) = (b : G) * (a : G)
    rw [ha, hb]
    calc (u * u') * (v * v')
        = u * (u' * v) * v' := by group
      _ = u * (v * u') * v' := by rw [(hUB v hv u' hu').symm]
      _ = (u * v) * (u' * v') := by group
      _ = (v * u) * (v' * u') := by rw [hUab u hu v hv, hBab u' hu' v' hv']
      _ = v * (u * v') * u' := by group
      _ = v * (v' * u) * u' := by rw [(hUB u hu v' hv').symm]
      _ = (v * v') * (u * u') := by group
  · obtain ⟨u, hu, b, hb, rfl⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg hx
    have hu2 : u * u = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV (mem_nVSub.mp hu).1
    have hb2 : b * b = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
      (isElemAbelian_conjSubgroup' hV g) (mem_bSub.mp hb).1
    have hUBcomm : u * b = b * u := nVSub_comm_bSub hTI hg hu hb
    calc (u * b) ^ 2 = (u * b) * (u * b) := by rw [pow_two]
      _ = u * (b * u) * b := by group
      _ = u * (u * b) * b := by rw [hUBcomm]
      _ = (u * u) * (b * b) := by group
      _ = 1 := by rw [hu2, hb2, mul_one]

theorem sup_le_normalizer_sup_nVSub_bSub {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V) :
    V ⊔ conjSubgroup V g ≤
      normalizer (((nVSub V g ⊔ bSub V g : Subgroup G) : Set G)) := by
  have hfwV : ∀ v ∈ V, ∀ y ∈ nVSub V g ⊔ bSub V g,
      v * y * v⁻¹ ∈ nVSub V g ⊔ bSub V g := by
    intro v hv y hy
    obtain ⟨u, hu, b, hb, rfl⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg hy
    have huv : v * u * v⁻¹ = u := by
      rw [CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hV hv (mem_nVSub.mp hu).1]
      group
    have hc : ⁅v, b⁆ ∈ nVSub V g := commutator_mem_nVSub hV hTI hv hb
    have e : v * (u * b) * v⁻¹ = (u * ⁅v, b⁆) * b := by
      rw [commutatorElement_def]
      rw [show v * (u * b) * v⁻¹ = (v * u * v⁻¹) * (v * b * v⁻¹) by group, huv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_left hc)) (Subgroup.mem_sup_right hb)
  have hfwW : ∀ w ∈ conjSubgroup V g, ∀ y ∈ nVSub V g ⊔ bSub V g,
      w * y * w⁻¹ ∈ nVSub V g ⊔ bSub V g := by
    intro w hw y hy
    obtain ⟨u, hu, b, hb, rfl⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg hy
    have hwb : w * b * w⁻¹ = b := by
      rw [CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm (isElemAbelian_conjSubgroup' hV g) hw
        (mem_bSub.mp hb).1]
      group
    have hc : ⁅w, u⁆ ∈ bSub V g := commutator_mem_bSub hV hTI hw hu
    have e : w * (u * b) * w⁻¹ = ⁅w, u⁆ * (u * b) := by
      rw [commutatorElement_def]
      rw [show w * (u * b) * w⁻¹ = (w * u * w⁻¹) * (w * b * w⁻¹) by group, hwb]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hb))
  refine sup_le ?_ ?_
  · intro v hv
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hfwV v hv y, fun hy => ?_⟩
    have this := hfwV v⁻¹ (V.inv_mem hv) (v * y * v⁻¹) hy
    rw [show v⁻¹ * (v * y * v⁻¹) * v⁻¹⁻¹ = y by group] at this
    exact this
  · intro w hw
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hfwW w hw y, fun hy => ?_⟩
    have this := hfwW w⁻¹ ((conjSubgroup V g).inv_mem hw) (w * y * w⁻¹) hy
    rw [show w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y by group] at this
    exact this

theorem sup_nVSub_bSub_le_pCoreOf {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V) :
    nVSub V g ⊔ bSub V g ≤ pCoreOf 2 (V ⊔ conjSubgroup V g) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (by
      refine sup_le ?_ ?_
      · exact (inf_le_left : nVSub V g ≤ V).trans le_sup_left
      · exact (inf_le_left : bSub V g ≤ conjSubgroup V g).trans le_sup_right)
    (sup_le_normalizer_sup_nVSub_bSub hV hTI hg)
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
      (isElemAbelian_sup_nVSub_bSub hV hTI hg))

theorem prop24Setup {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G}
    (hU : nVSub V g ≠ ⊥) (hne : nVSub V g ≠ V) :
    CFSG.RankThree.GF2n.Tim77.Prop24Setup V (conjSubgroup V g) (nVSub V g) (bSub V g)
      (nVSub V g ⊔ bSub V g) where
  elem := hV
  ti := hTI
  conj := ⟨g⁻¹, by simpa using (t75_conjSubgroup_eq V g⁻¹).symm⟩
  hL := rfl
  hLb := rfl
  hM := rfl
  ne_bot := hU
  ne := hne

theorem odd_orderOf_mul {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hU : nVSub V g ≠ ⊥)
    {v x : G} (hv : v ∈ V) (hvU : v ∉ nVSub V g)
    (hx : x ∈ conjSubgroup V g) (hxB : x ∉ bSub V g) :
    Odd (orderOf (v * x)) := by
  have hne : nVSub V g ≠ V := fun h => hvU (h.symm ▸ hv)
  exact (prop24Setup hV hTI hU hne).odd_orderOf_mul hv hvU hx hxB

private theorem two_conj_eq_or_comm_conj {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {a b : G}
    (hN : conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥) :
    (∀ u ∈ conjSubgroup V a, ∀ v ∈ conjSubgroup V b, u * v = v * u) ∨
      ∃ y ∈ conjSubgroup V a ⊔ conjSubgroup V b,
        conjSubgroup V b = conjSubgroup (conjSubgroup V a) y := by
  let A := conjSubgroup V a
  let B := conjSubgroup V b
  have hAelem : IsElemAbelian 2 A := isElemAbelian_conjSubgroup' hV a
  have hBelem : IsElemAbelian 2 B := isElemAbelian_conjSubgroup' hV b
  have hATI : CFSG.CGT.Timmesfeld75.IsTI A := isTI_conj hTI a
  have hBTI : CFSG.CGT.Timmesfeld75.IsTI B := isTI_conj hTI b
  have hA75 : A = CFSG.CGT.Timmesfeld75.conjSubgroup a⁻¹ V := by
    simpa using (t75_conjSubgroup_eq V a⁻¹).symm
  have hB75 : B = CFSG.CGT.Timmesfeld75.conjSubgroup b⁻¹ V := by
    simpa using (t75_conjSubgroup_eq V b⁻¹).symm
  have hconjAB : ∃ k : G, B = CFSG.CGT.Timmesfeld75.conjSubgroup k A := by
    refine ⟨b⁻¹ * a, ?_⟩
    rw [hA75, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show (b⁻¹ * a) * a⁻¹ = b⁻¹ by group]
    exact hB75
  have hconjBA : ∃ k : G, A = CFSG.CGT.Timmesfeld75.conjSubgroup k B := by
    refine ⟨a⁻¹ * b, ?_⟩
    rw [hB75, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show (a⁻¹ * b) * b⁻¹ = a⁻¹ by group]
    exact hA75
  by_cases hL : A ⊓ normalizer (B : Set G) = A
  · have hAne : A ≠ ⊥ := fun h => hN (by rw [hL, h])
    have hL' : B ⊓ normalizer (A : Set G) ≠ ⊥ := by
      intro hbot
      obtain ⟨u, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
      have huA : (u : G) ∈ A := u.2
      have huN : (u : G) ∈ normalizer (B : Set G) := by
        have : (u : G) ∈ A ⊓ normalizer (B : Set G) := by rw [hL]; exact huA
        exact (Subgroup.mem_inf.mp this).2
      have hu2 : (u : G) * (u : G) = 1 :=
        CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hAelem huA
      have hBne : B ≠ ⊥ := by
        intro h
        apply hAne
        have hcard : Nat.card A = Nat.card B := by
          dsimp only [A, B]
          rw [card_conjSubgroup', card_conjSubgroup']
        have h1 : Nat.card B = 1 := by rw [h, card_bot]
        rw [← hcard] at h1
        exact Subgroup.card_eq_one.mp h1
      have hBsq : ∀ x ∈ B, x * x = 1 := fun x hx =>
        CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hBelem hx
      obtain ⟨x, hxB, hx1, hux⟩ :=
        CFSG.LargeExtraspecial.S9.TIX.exists_ne_one_commute hBsq hBne huN hu2
      have hxN : x ∈ normalizer (A : Set G) :=
        centralizer_le_normalizer_of_isTI hATI huA (fun h => hu1' (Subtype.ext h))
          (Subgroup.mem_centralizer_iff.mpr fun y hy => by
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hux)
      have : x ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hxB, hxN⟩
      exact hx1 (Subgroup.mem_bot.mp this)
    by_cases hL'eq : B ⊓ normalizer (A : Set G) = B
    · by_cases hAB : A = B
      · right
        refine ⟨1, Subgroup.mem_sup_left A.one_mem, ?_⟩
        rw [conjSubgroup_one]
        exact hAB.symm
      · have hABbot : A ⊓ B = ⊥ := by
          rcases inf_conjSubgroup_eq_bot_or_eq hTI a b with h | h
          · exact h
          · exact absurd h hAB
        left
        intro u hu v hv
        have huN : u ∈ normalizer (B : Set G) := by
          have : u ∈ A ⊓ normalizer (B : Set G) := by rw [hL]; exact hu
          exact (Subgroup.mem_inf.mp this).2
        have hvN : v ∈ normalizer (A : Set G) := by
          have : v ∈ B ⊓ normalizer (A : Set G) := by rw [hL'eq]; exact hv
          exact (Subgroup.mem_inf.mp this).2
        have huvB : u * v * u⁻¹ * v⁻¹ ∈ B := by
          have h1 : u * v * u⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp huN v).mp hv
          exact Subgroup.mul_mem B h1 (B.inv_mem hv)
        have huvA : u * v * u⁻¹ * v⁻¹ ∈ A := by
          have h1 : v * u⁻¹ * v⁻¹ ∈ A :=
            (Subgroup.mem_normalizer_iff.mp hvN u⁻¹).mp (A.inv_mem (show u ∈ A from hu))
          rw [show u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) by group]
          exact Subgroup.mul_mem A (show u ∈ A from hu) h1
        have hbot : u * v * u⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hABbot]; exact ⟨huvA, huvB⟩
        rw [Subgroup.mem_bot] at hbot
        have h : (u * v) * (v * u)⁻¹ = 1 := by simpa [mul_inv_rev, mul_assoc] using hbot
        exact mul_inv_eq_one.mp h
    · right
      have hsetB : CFSG.RankThree.GF2n.Tim77.Prop24Setup B A
          (B ⊓ normalizer (A : Set G)) (A ⊓ normalizer (B : Set G))
          ((B ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (B : Set G))) :=
        { elem := hBelem
          ti := hBTI
          conj := hconjBA
          hL := rfl
          hLb := rfl
          hM := rfl
          ne_bot := hL'
          ne := hL'eq }
      obtain ⟨x, hxX, hx⟩ := hsetB.exists_conj_eq
      refine ⟨x, ?_, ?_⟩
      · rwa [sup_comm] at hxX
      · rw [t75_conjSubgroup_eq] at hx
        have hAeq : conjSubgroup V a = conjSubgroup B x⁻¹ := hx
        rw [hAeq, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  · right
    have hsetA : CFSG.RankThree.GF2n.Tim77.Prop24Setup A B
        (A ⊓ normalizer (B : Set G)) (B ⊓ normalizer (A : Set G))
        ((A ⊓ normalizer (B : Set G)) ⊔ (B ⊓ normalizer (A : Set G))) :=
      { elem := hAelem
        ti := hATI
        conj := hconjAB
        hL := rfl
        hLb := rfl
        hM := rfl
        ne_bot := hN
        ne := hL }
    obtain ⟨x, hxX, hx⟩ := hsetA.exists_conj_eq
    refine ⟨x⁻¹, (A ⊔ B).inv_mem hxX, ?_⟩
    rw [t75_conjSubgroup_eq] at hx
    exact hx

theorem two_conj_eq_or_comm {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {W W' : Subgroup G}
    (hW : ∃ a : G, W = conjSubgroup V a) (hW' : ∃ b : G, W' = conjSubgroup V b)
    (hN : W ⊓ normalizer (W' : Set G) ≠ ⊥) :
    (∀ u ∈ W, ∀ v ∈ W', u * v = v * u) ∨
      ∃ y ∈ W ⊔ W', W' = conjSubgroup W y := by
  obtain ⟨a, rfl⟩ := hW
  obtain ⟨b, rfl⟩ := hW'
  exact two_conj_eq_or_comm_conj hV hTI hN

theorem not_isPGroup_sup_of_odd {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G} (hg : conjSubgroup V g ≠ V)
    (hU : nVSub V g ≠ ⊥) {v x : G} (hv : v ∈ V) (hvU : v ∉ nVSub V g)
    (hx : x ∈ conjSubgroup V g) (hxB : x ∉ bSub V g) :
    ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup V g) := by
  intro hX
  have hodd : Odd (orderOf (v * x)) := odd_orderOf_mul hV hTI hU hv hvU hx hxB
  have hxX : v * x ∈ V ⊔ conjSubgroup V g :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hx)
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow
    (G := ↥(V ⊔ conjSubgroup V g)) hX ⟨v * x, hxX⟩
  have hk' : orderOf (v * x) ∣ 2 ^ k := by
    rwa [← orderOf_injective (V ⊔ conjSubgroup V g).subtype
      (V ⊔ conjSubgroup V g).subtype_injective] at hk
  have h1 : orderOf (v * x) = 1 :=
    ((Nat.coprime_two_right.2 hodd).pow_right k).eq_one_of_dvd hk'
  have hvx : v * x = 1 := orderOf_eq_one_iff.mp h1
  have hv2 : v * v = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self hV hv
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
    (isElemAbelian_conjSubgroup' hV g) hx)
  have hvx' : v = x := by
    have h : x = v := by
      have h := eq_inv_of_mul_eq_one_right hvx
      rwa [inv_eq_of_mul_eq_one_right hv2] at h
    exact h.symm
  have hbot : V ⊓ conjSubgroup V g = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hg
  have hvbot : v ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hv, hvx' ▸ hx⟩
  rw [Subgroup.mem_bot] at hvbot
  exact hvU (by rw [hvbot]; exact (nVSub V g).one_mem)

end CFSG.LocalAnalysis.WeakClosure81
