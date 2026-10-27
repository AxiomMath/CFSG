module

public import CFSG.Timmesfeld.ARS.CaseBDict
public import CFSG.Timmesfeld.ARS.CaseBChain

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem conjSub_le_sup_of_mem_M (h : Hyp G R) {X Z : Subgroup G} (hX : X ∈ R)
    (hZ : Z ∈ lambdaSet R X) {w : G} (hw : w ∈ M R X) : conjSub Z w ≤ Z ⊔ X := by
  rintro _ ⟨z, hz, rfl⟩
  have hc : ⁅w, z⁆ ∈ X := by
    rw [← (Q_eq_M h hX).2.2.1]
    exact Subgroup.commutator_mem_commutator hw (QD.le_M hZ hz)
  show w * z * w⁻¹ ∈ Z ⊔ X
  rw [show w * z * w⁻¹ = ⁅w, z⁆ * z by group]
  have hcomm : Commute ⁅w, z⁆ z := (hZ.1.2.2 _ hc z hz)
  rw [hcomm.eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hc)

theorem commute_of_conjSub_eq_of_mem_M (h : Hyp G R) {X Z : Subgroup G} (hX : X ∈ R)
    (hZ : Z ∈ lambdaSet R X) {m : G} (hm : m ∈ M R X) (hmZ : conjSub Z m = Z) {z : G}
    (hz : z ∈ Z) : Commute m z := by
  have := h.finite
  have hc : ⁅m, z⁆ ∈ X ⊓ Z := by
    refine ⟨?_, ?_⟩
    · rw [← (Q_eq_M h hX).2.2.1]
      exact Subgroup.commutator_mem_commutator hm (QD.le_M hZ hz)
    · rw [commutatorElement_def]
      refine Z.mul_mem ?_ (Z.inv_mem hz)
      have := conj_mem_conjSub m hz
      rwa [hmZ] at this
  rw [inf_eq_bot h.root h.noIsolated hX hZ.1.1 hZ.1.2.1.symm, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem exists_conjSub_eq_of_le_sup [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Z Y D : Subgroup G} (hZ : Z ∈ R) (hY : Y ∈ R) (hD : D ∈ R) (hs : Special R Z Y)
    (hle : D ≤ Z ⊔ ⁅Z, Y⁆) (hne : D ≠ ⁅Z, Y⁆) : ∃ y ∈ Y, conjSub Z y = D := by
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD
  have hXZ : ⁅Z, Y⁆ ≤ Subgroup.normalizer ((Z : Set G)) := le_normalizer_of_conjSub_le fun g hg =>
    (conjSub_of_forall_commute fun k hk => (hs.2.1 g hg k hk)).le
  have hd' : d ∈ ((Z : Subgroup G) : Set G) * ((⁅Z, Y⁆ : Subgroup G) : Set G) := by
    rw [sup_comm] at hle
    have hd2 : d ∈ ((⁅Z, Y⁆ ⊔ Z : Subgroup G) : Set G) := hle hd
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXZ] at hd2
    obtain ⟨x, hx, z, hz, hxz⟩ := hd2
    refine ⟨z, hz, x, hx, ?_⟩
    rw [← hxz]
    exact (hs.2.1 x hx z hz).symm.eq
  obtain ⟨z, hz, x, hx, rfl⟩ := hd'
  beta_reduce at hd hd1 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [one_mul] at hd hd1
    have hmem : x ∈ D ⊓ ⁅Z, Y⁆ := ⟨hd, hx⟩
    rw [inf_eq_bot hR hiso hD hs.1 hne, Subgroup.mem_bot] at hmem
    exact hd1 hmem
  obtain ⟨y, hy, hyx⟩ := (bijOn_commutator hR hiso hZ hY hs hz hz1).2.2
    (show x⁻¹ ∈ ((⁅Z, Y⁆ : Subgroup G) : Set G) from Subgroup.inv_mem _ hx)
  refine ⟨y, hy, ?_⟩
  have hmem : z * x ∈ conjSub Z y := by
    refine ⟨z, hz, ?_⟩
    show y * z * y⁻¹ = z * x
    have hyx' : z * y * z⁻¹ * y⁻¹ = x⁻¹ := hyx
    have hcomm : Commute x z := hs.2.1 x hx z hz
    calc y * z * y⁻¹ = (y * z⁻¹ * y⁻¹)⁻¹ := by group
      _ = (z⁻¹ * (z * y * z⁻¹ * y⁻¹))⁻¹ := by group
      _ = (z⁻¹ * x⁻¹)⁻¹ := by rw [hyx']
      _ = x * z := by group
      _ = z * x := hcomm.eq
  by_contra hne'
  have hmem' : z * x ∈ conjSub Z y ⊓ D := ⟨hmem, hd⟩
  rw [inf_eq_bot hR hiso (hR.conjSub_mem hZ y) hD hne', Subgroup.mem_bot] at hmem'
  exact hd1 hmem'

theorem eq_one_of_forall_commute [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {Y Z : Subgroup G} (hY : Y ∈ R) (hZ : Z ∈ R) (hs : Special R Y Z) {y : G} (hy : y ∈ Y)
    (hyZ : ∀ z ∈ Z, Commute y z) : y = 1 := by
  obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZ
  exact eq_one_of_commute_of_special hR hiso hZ hY hs.symm hz hz1 hy (hyZ z hz).symm

abbrev W (R : Set (Subgroup G)) (X Y : Subgroup G) : Subgroup G := M R X ⊓ M R Y

theorem commuting_W (h : Hyp G R) {X Y : Subgroup G} (hX : X ∈ R) (hY : Y ∈ R) (hXY : X ≠ Y) :
    Commuting (W R X Y) (W R X Y) :=
  have := h.finite
  commuting_of_le_M_inf h hX hY (inf_eq_bot h.root h.noIsolated hX hY hXY) inf_le_left
    inf_le_right inf_le_left inf_le_right

theorem exists_decomp (h : Hyp G R) {X Y Z₁ Z₂ Y₁ Y₂ : Subgroup G} (hX : X ∈ R)
    (hZ₁ : Z₁ ∈ lambdaSet R X) (hZ₂ : Z₂ ∈ lambdaSet R X) (hY₁ : Y₁ ∈ R) (hY₂ : Y₂ ∈ R)
    (hs₁ : Special R Z₁ Y₁) (hs₂ : Special R Z₂ Y₂) (hc₁ : ⁅Z₁, Y₁⁆ = X) (hc₂ : ⁅Z₂, Y₂⁆ = X)
    (hY₁W : Y₁ ≤ W R X Y) (hY₂W : Y₂ ≤ W R X Y) (hY₂Z₁ : Commuting Y₂ Z₁) {w : G}
    (hw : w ∈ W R X Y) :
    ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, (y₁ * y₂)⁻¹ * w ∈ W R X Y ∧
      (∀ z ∈ Z₁, Commute ((y₁ * y₂)⁻¹ * w) z) ∧ (∀ z ∈ Z₂, Commute ((y₁ * y₂)⁻¹ * w) z) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hXc : ∀ m ∈ M R X, conjSub X m = X := fun m hm =>
    conjSub_of_forall_commute fun x hx => (QD.commuting_M hR hX x hx m hm).symm
  have step : ∀ {Z Y' : Subgroup G}, Z ∈ lambdaSet R X → Y' ∈ R → Special R Z Y' →
      ⁅Z, Y'⁆ = X → ∀ m ∈ M R X, ∃ y ∈ Y', conjSub Z (y⁻¹ * m) = Z := by
    intro Z Y' hZ hY' hs hc m hm
    have hle := conjSub_le_sup_of_mem_M h hX hZ hm
    have hne : conjSub Z m ≠ X := by
      intro e
      apply hZ.1.2.1
      have := congrArg (fun H => conjSub H m⁻¹) e
      simp only [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
      rw [this, hXc _ (Subgroup.inv_mem _ hm)]
    rw [← hc] at hle hne
    obtain ⟨y, hy, hyZ⟩ := exists_conjSub_eq_of_le_sup hR hiso hZ.1.1 hY' (hR.conjSub_mem hZ.1.1 m)
      hs hle hne
    refine ⟨y, hy, ?_⟩
    rw [conjSub_mul, ← hyZ, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  obtain ⟨y₁, hy₁, h₁⟩ := step hZ₁ hY₁ hs₁ hc₁ w hw.1
  have hw₁ : y₁⁻¹ * w ∈ M R X := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hY₁W hy₁).1) hw.1
  obtain ⟨y₂, hy₂, h₂⟩ := step hZ₂ hY₂ hs₂ hc₂ _ hw₁
  have hmul : (y₁ * y₂)⁻¹ * w = y₂⁻¹ * (y₁⁻¹ * w) := by group
  have hW : (y₁ * y₂)⁻¹ * w ∈ W R X Y := by
    rw [hmul]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hY₂W hy₂))
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hY₁W hy₁)) hw)
  refine ⟨y₁, hy₁, y₂, hy₂, hW, fun z hz => ?_, fun z hz => ?_⟩
  · rw [hmul]
    exact ((hY₂Z₁ _ (Subgroup.inv_mem _ hy₂) z hz).mul_left
      (commute_of_conjSub_eq_of_mem_M h hX hZ₁ hw₁ h₁ hz))
  · rw [← hmul] at h₂
    exact commute_of_conjSub_eq_of_mem_M h hX hZ₂ hW.1 h₂ hz

theorem conjSub_centralizer' (H : Subgroup G) (g : G) :
    conjSub (Subgroup.centralizer (H : Set G)) g =
      Subgroup.centralizer ((conjSub H g : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hy k hk
    change g * k * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * k * g⁻¹)
    rw [show g * k * g⁻¹ * (g * y * g⁻¹) = g * (k * y) * g⁻¹ by group, this]
    group
  · intro hx
    refine ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_iff.2 fun k hk => ?_, by
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group⟩
    have := Subgroup.mem_centralizer_iff.1 hx (g * k * g⁻¹) ⟨k, hk, rfl⟩
    calc k * (g⁻¹ * x * g) = g⁻¹ * (g * k * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * k * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * k := by group

theorem conjSub_inf (H K : Subgroup G) (g : G) : conjSub (H ⊓ K) g = conjSub H g ⊓ conjSub K g :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem conjSub_W (hR : IsRootClass R) (X Y : Subgroup G) (g : G) :
    conjSub (W R X Y) g = W R (conjSub X g) (conjSub Y g) := by
  rw [W, conjSub_inf, Sec5.conjSub_M hR, Sec5.conjSub_M hR]

section Skeleton

variable {F : Type} [Field F] {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (R Ψ) in
@[expose] noncomputable def hidAt (s₁ s₂ t₁ t₂ : Fin 4) : Subgroup G :=
  W R (xg Ψ s₁ t₂) (xg Ψ s₂ t₁) ⊓ (Subgroup.centralizer ((xg Ψ s₁ s₂ : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ((xg Ψ t₁ t₂ : Subgroup G) : Set G))

theorem conjSub_hidAt [CharP F 2] (hR : IsRootClass R) (σ : Equiv.Perm (Fin 4))
    {s₁ s₂ t₁ t₂ : Fin 4} (h12 : s₁ ≠ s₂) (h34 : t₁ ≠ t₂) (h14 : s₁ ≠ t₂) (h23 : s₂ ≠ t₁) :
    conjSub (hidAt R Ψ s₁ s₂ t₁ t₂) (Ψ (pm σ)) = hidAt R Ψ (σ s₁) (σ s₂) (σ t₁) (σ t₂) := by
  rw [hidAt, conjSub_inf, conjSub_W hR, conjSub_inf, conjSub_centralizer', conjSub_centralizer',
    conjSub_xg σ h14, conjSub_xg σ h23, conjSub_xg σ h12, conjSub_xg σ h34, hidAt]

variable (R Ψ) in
noncomputable abbrev hid : Subgroup G := hidAt R Ψ 0 1 2 3

section Basic

variable (h : Hyp G R) (hS : Skel R Ψ)
include h hS

omit h hS in
theorem commuting_hid_01 : Commuting (hid R Ψ) (xg Ψ 0 1) := fun _ hn p hp =>
  ((Subgroup.mem_centralizer_iff.1 hn.2.1 p hp)).symm

omit h hS in
theorem commuting_hid_23 : Commuting (hid R Ψ) (xg Ψ 2 3) := fun _ hn p hp =>
  ((Subgroup.mem_centralizer_iff.1 hn.2.2 p hp)).symm

theorem commuting_hid_03 : Commuting (hid R Ψ) (xg Ψ 0 3) := fun n hn a ha =>
  have := h.finite
  (QD.commuting_M h.root (hS.mem 0 3 (by decide)) a ha n hn.1.1).symm

theorem commuting_hid_12 : Commuting (hid R Ψ) (xg Ψ 1 2) := fun n hn a ha =>
  have := h.finite
  (QD.commuting_M h.root (hS.mem 1 2 (by decide)) a ha n hn.1.2).symm

theorem xg_02_le_W : xg Ψ 0 2 ≤ W R (xg Ψ 0 3) (xg Ψ 1 2) :=
  le_inf (QD.le_M (hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide)))
    (QD.le_M (hS.mem_lambdaSet_col h.root (by decide) (by decide) (by decide)))

theorem xg_13_le_W : xg Ψ 1 3 ≤ W R (xg Ψ 0 3) (xg Ψ 1 2) :=
  le_inf (QD.le_M (hS.mem_lambdaSet_col h.root (by decide) (by decide) (by decide)))
    (QD.le_M (hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide)))

theorem commuting_W₁ : Commuting (W R (xg Ψ 0 3) (xg Ψ 1 2)) (W R (xg Ψ 0 3) (xg Ψ 1 2)) :=
  commuting_W h (hS.mem 0 3 (by decide)) (hS.mem 1 2 (by decide))
    (hS.xg_ne (by decide) (by decide) (by decide))

theorem commuting_hid_02 : Commuting (hid R Ψ) (xg Ψ 0 2) :=
  (commuting_W₁ h hS).mono inf_le_left (xg_02_le_W h hS)

theorem commuting_hid_13 : Commuting (hid R Ψ) (xg Ψ 1 3) :=
  (commuting_W₁ h hS).mono inf_le_left (xg_13_le_W h hS)

theorem commuting_hid_10 : Commuting (hid R Ψ) (xg Ψ 1 0) := by
  have := h.finite
  have hR := h.root
  intro n hn p hp
  have hA₁ : (1 : Fin 4) ≠ 2 := by decide
  have hpM : p ∈ M R (xg Ψ 1 2) :=
    QD.le_M (hS.mem_lambdaSet_row hR (by decide) (by decide) (by decide)) hp
  have hc : ⁅n, p⁆ ∈ xg Ψ 1 2 := by
    rw [← (Q_eq_M h (hS.mem 1 2 hA₁)).2.2.1]
    exact Subgroup.commutator_mem_commutator hn.1.2 hpM
  have hcE : ∀ e ∈ xg Ψ 2 3, Commute ⁅n, p⁆ e := by
    intro e he
    have h1 := (commuting_hid_23 n hn e he)
    have h2 := (commuting_xg (Ψ := Ψ) (by decide : (1 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 3)
      (by decide) (by decide) p hp e he)
    rw [commutatorElement_def]
    exact ((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left
  have := eq_one_of_forall_commute hR h.noIsolated (hS.mem 1 2 hA₁) (hS.mem 2 3 (by decide))
    (hS.special (by decide) (by decide) (by decide)) hc hcE
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem commuting_hid_32 : Commuting (hid R Ψ) (xg Ψ 3 2) := by
  have := h.finite
  have hR := h.root
  intro n hn f hf
  have hA₁ : (1 : Fin 4) ≠ 2 := by decide
  have hfM : f ∈ M R (xg Ψ 1 2) :=
    QD.le_M (hS.mem_lambdaSet_col hR (by decide) (by decide) (by decide)) hf
  have hc : ⁅n, f⁆ ∈ xg Ψ 1 2 := by
    rw [← (Q_eq_M h (hS.mem 1 2 hA₁)).2.2.1]
    exact Subgroup.commutator_mem_commutator hn.1.2 hfM
  have hcP : ∀ p ∈ xg Ψ 0 1, Commute ⁅n, f⁆ p := by
    intro p hp
    have h1 := (commuting_hid_01 n hn p hp)
    have h2 := (commuting_xg (Ψ := Ψ) (by decide : (3 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
      (by decide) (by decide) f hf p hp)
    rw [commutatorElement_def]
    exact ((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left
  have := eq_one_of_forall_commute hR h.noIsolated (hS.mem 1 2 hA₁) (hS.mem 0 1 (by decide))
    (hS.special (by decide) (by decide) (by decide)).symm hc hcP
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem commuting_hid {a b : Fin 4} (hab : a ≠ b) (hc : a.val < 2 ∨ 2 ≤ b.val) :
    Commuting (hid R Ψ) (xg Ψ a b) := by
  fin_cases a <;> fin_cases b <;> simp at hab hc
  exacts [commuting_hid_01, commuting_hid_02 h hS, commuting_hid_03 h hS,
    commuting_hid_10 h hS, commuting_hid_12 h hS, commuting_hid_13 h hS, commuting_hid_23,
    commuting_hid_32 h hS]

theorem conjSub_hid_swap01 [CharP F 2] :
    conjSub (hid R Ψ) (Ψ (pm (Equiv.swap 0 1))) = hid R Ψ := by
  refine conjSub_of_forall_commute fun n hn => ?_
  have hmem := pm_swap_mem_sup (Ψ := Ψ) (by decide : (0 : Fin 4) ≠ 1)
  have hle : xg Ψ 0 1 ⊔ xg Ψ 1 0 ≤ Subgroup.centralizer {n} := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (commuting_hid_01 n hn x hx).symm
    · exact (commuting_hid_10 h hS n hn x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem))

theorem conjSub_hid_swap23 [CharP F 2] :
    conjSub (hid R Ψ) (Ψ (pm (Equiv.swap 2 3))) = hid R Ψ := by
  refine conjSub_of_forall_commute fun n hn => ?_
  have hmem := pm_swap_mem_sup (Ψ := Ψ) (by decide : (2 : Fin 4) ≠ 3)
  have hle : xg Ψ 2 3 ⊔ xg Ψ 3 2 ≤ Subgroup.centralizer {n} := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (commuting_hid_23 n hn x hx).symm
    · exact (commuting_hid_32 h hS n hn x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem))

theorem exists_mul_mem_hid {w : G} (hw : w ∈ W R (xg Ψ 0 3) (xg Ψ 1 2)) :
    ∃ c' ∈ xg Ψ 1 3, ∃ c ∈ xg Ψ 0 2, (c' * c)⁻¹ * w ∈ hid R Ψ := by
  have hR := h.root
  obtain ⟨y₁, hy₁, y₂, hy₂, hW, h1, h2⟩ := exists_decomp h (hS.mem 0 3 (by decide))
    (hS.mem_lambdaSet_row hR (by decide) (by decide) (by decide))
    (hS.mem_lambdaSet_col hR (by decide) (by decide) (by decide))
    (hS.mem 1 3 (by decide)) (hS.mem 0 2 (by decide))
    (hS.special (by decide) (by decide) (by decide))
    (hS.special (by decide : (0 : Fin 4) ≠ 2) (by decide : (2 : Fin 4) ≠ 3) (by decide)).symm
    (commutator_xg (by decide) (by decide) (by decide))
    (by rw [Subgroup.commutator_comm, commutator_xg (by decide) (by decide) (by decide)])
    (xg_13_le_W h hS) (xg_02_le_W h hS) (commuting_xg (by decide) (by decide) (by decide)
      (by decide)) hw
  refine ⟨y₁, hy₁, y₂, hy₂, hW, Subgroup.mem_centralizer_iff.2 fun z hz => (h1 z hz).symm,
    Subgroup.mem_centralizer_iff.2 fun z hz => (h2 z hz).symm⟩

end Basic

section Nontrivial

variable (h : Hyp G R) (hS : Skel R Ψ)
include h hS

omit h in
theorem mem_leviSet_12 : xg Ψ 1 2 ∈ leviSet R (xg Ψ 0 3) (xg Ψ 3 0) :=
  ⟨⟨hS.mem 1 2 (by decide), hS.xg_ne (by decide) (by decide) (by decide),
      commuting_xg (by decide) (by decide) (by decide) (by decide)⟩,
    ⟨hS.mem 1 2 (by decide), hS.xg_ne (by decide) (by decide) (by decide),
      commuting_xg (by decide) (by decide) (by decide) (by decide)⟩⟩

omit h in
theorem mem_leviSet_21 : xg Ψ 2 1 ∈ leviSet R (xg Ψ 0 3) (xg Ψ 3 0) :=
  ⟨⟨hS.mem 2 1 (by decide), hS.xg_ne (by decide) (by decide) (by decide),
      commuting_xg (by decide) (by decide) (by decide) (by decide)⟩,
    ⟨hS.mem 2 1 (by decide), hS.xg_ne (by decide) (by decide) (by decide),
      commuting_xg (by decide) (by decide) (by decide) (by decide)⟩⟩

omit h in
theorem mem_omegaSet_30 : xg Ψ 3 0 ∈ omegaSet R (xg Ψ 0 3) :=
  ⟨hS.mem 3 0 (by decide), hS.opp 0 3 (by decide)⟩

theorem exists_mem_lambdaSet_not_le (hB : HypB G R (xg Ψ 0 3)) :
    ∃ D ∈ lambdaSet R (xg Ψ 0 3), D ∈ lambdaSet R (xg Ψ 1 2) ∧ ¬ D ≤ Ψ.range := by
  have := h.finite
  have hR := h.root
  have hA : xg Ψ 0 3 ∈ R := hS.mem 0 3 (by decide)
  have h8 := hB.sec8
  obtain ⟨Δ, hΔ, hAΔ⟩ := hB.exists_isWeakTI
  have hA₀ := mem_omegaSet_30 hS
  have hMA : ¬ M R (xg Ψ 0 3) ≤ Ψ.range := by
    intro hle
    have htop := gen_lambdaSet_sup_eq_top h hA hA₀
    have hle' : gen (lambdaSet R (xg Ψ 0 3)) ⊔ xg Ψ 3 0 ≤ Ψ.range :=
      sup_le ((gen_le fun C hC => QD.le_M hC).trans hle) (Subgroup.map_le_range _ _)
    rw [htop] at hle'
    exact hS.not_isCoatom_of_surjective hR (MonoidHom.range_eq_top.1 (top_le_iff.1 hle')) hB.max
  obtain ⟨D', hD', hD'r⟩ : ∃ D' ∈ lambdaStar R (xg Ψ 0 3) (xg Ψ 3 0), ¬ D' ≤ Ψ.range := by
    by_contra! hall
    rw [M_eq_gen_lambdaStar h hA hA₀] at hMA
    exact hMA (gen_le hall)
  obtain ⟨B, hB', hD'B⟩ := exists_mem_leviSet_mem_lambdaSet h hA h8 hA₀ hΔ hAΔ hD'
  obtain ⟨v, hv, hvB⟩ := exists_mem_levi_conjSub_eq h hA h8 hA₀ hΔ hAΔ hB' (mem_leviSet_12 hS)
  have hvr : v ∈ Ψ.range := by
    rw [levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ (mem_leviSet_12 hS) (mem_leviSet_21 hS)
      (hS.xg_ne (by decide) (by decide) (by decide))] at hv
    exact (sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)) hv
  have hvA : conjSub (xg Ψ 0 3) v = xg Ψ 0 3 := conjSub_of_forall_commute fun a ha =>
    ((Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left _ _ hv)) a ha).symm
  refine ⟨conjSub D' v, ?_, ?_, ?_⟩
  · have := conjSub_mem_lambdaSet hR hD'.1 v
    rwa [hvA] at this
  · have := conjSub_mem_lambdaSet hR hD'B v
    rwa [hvB] at this
  · intro hle
    apply hD'r
    have hle' := Subgroup.map_mono (f := (MulAut.conj v⁻¹).toMonoidHom) hle
    have e : conjSub (conjSub D' v) v⁻¹ = D' := by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [← conjSub, e] at hle'
    refine hle'.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    change v⁻¹ * x * v⁻¹⁻¹ ∈ Ψ.range
    rw [inv_inv]
    exact Ψ.range.mul_mem (Ψ.range.mul_mem (Ψ.range.inv_mem hvr) hx) hvr

theorem hid_ne_bot (hB : HypB G R (xg Ψ 0 3)) : hid R Ψ ≠ ⊥ := by
  intro hbot
  obtain ⟨D, hDA, hDA₁, hDr⟩ := exists_mem_lambdaSet_not_le h hS hB
  apply hDr
  intro d hd
  have hdW : d ∈ W R (xg Ψ 0 3) (xg Ψ 1 2) := ⟨QD.le_M hDA hd, QD.le_M hDA₁ hd⟩
  obtain ⟨c', hc', c, hc, hn⟩ := exists_mul_mem_hid h hS hdW
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hn
  rw [← hn]
  exact Ψ.range.mul_mem (Subgroup.map_le_range _ _ hc') (Subgroup.map_le_range _ _ hc)

end Nontrivial

end Skeleton

end CaseB

end CFSG.Timmesfeld.ARS
