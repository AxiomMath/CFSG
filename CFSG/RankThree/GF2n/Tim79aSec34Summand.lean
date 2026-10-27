module

public import CFSG.RankThree.GF2n.Tim79a34Pairing

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Sec34LineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H →
    ∃ A₁ : Subgroup G, A₁ ≤ V ⊓ wOf V H ∧ Nat.card ↥A₁ = qBar V H ∧
      ∀ n ∈ xOf V H, conjSubgroup n V = V → conjSubgroup n A₁ = A₁

@[expose] def Sec34BraidStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → ∀ y ∈ xOf V H, y ∉ Ycomm V H →
      ∀ a ∈ V, a ∉ wOf V H → ∃ b ∈ conjSubgroup y V, b ∉ wOf V H ∧ (a * b) ^ 3 ∈ wOf V H

@[expose] def Sec34OppMeetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → ∀ y ∈ xOf V H, y ∉ Ycomm V H →
      ∀ v ∈ conjSubgroup y V, v ∈ Subgroup.normalizer (V : Set G) → v ∈ wOf V H

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
include hc

theorem wOf_mem_normalizer_conj {y : G} (hy : y ∈ H) {w : G} (hw : w ∈ wOf V H) :
    w ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
  hc.pCoreH_le_normalizer_conj hy (wOf_le_pCore V H hw)

theorem commutator_mem_conj_inf_wOf {y : G} (hy : y ∈ H) {v w : G}
    (hv : v ∈ conjSubgroup y V) (hw : w ∈ wOf V H) :
    ⁅v, w⁆ ∈ conjSubgroup y V ⊓ wOf V H := by
  have hvH : v ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hy hv
  refine ⟨?_, ?_⟩
  · have h1 : w * v⁻¹ * w⁻¹ ∈ conjSubgroup y V :=
      ((Subgroup.mem_normalizer_iff.mp (hc.wOf_mem_normalizer_conj hy hw)) v⁻¹).mp
        ((conjSubgroup y V).inv_mem hv)
    have e : ⁅v, w⁆ = v * (w * v⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (conjSubgroup y V).mul_mem hv h1
  · have h1 : v * w * v⁻¹ ∈ wOf V H :=
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hvH)) w).mp hw
    rw [commutatorElement_def]
    exact (wOf V H).mul_mem h1 ((wOf V H).inv_mem hw)

end MinCex

theorem piBar_eq_of_inv_mul_mem {V H : Subgroup G} (x x' : ↥H)
    (h : (x : G)⁻¹ * (x' : G) ∈ wOf V H) : piBar V H x = piBar V H x' := by
  have h1 : piBar V H (x⁻¹ * x') = 1 := (piBar_eq_one_iff _).2 (by simpa using h)
  rw [map_mul, map_inv] at h1
  exact inv_mul_eq_one.mp h1

theorem mem_wOf_iff_conj {V H : Subgroup G} {y : G} (hy : y ∈ H) (x : G) :
    x ∈ wOf V H ↔ y⁻¹ * x * y ∈ wOf V H := by
  have := Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem hy)) x
  simpa only [inv_inv] using this

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem braid_data (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ xOf V H)
    (hyc : y ∉ Ycomm V H) {a b : G} (ha : a ∈ V) (hb : b ∈ conjSubgroup y V)
    (hbW : b ∉ wOf V H) (hbr : (a * b) ^ 3 ∈ wOf V H) :
    a * b * a ∈ xOf V H ∧ (a * b * a) * (a * b * a) = 1 ∧
    y⁻¹ * (a * b * a) ∈ Subgroup.normalizer (V : Set G) ∧
    conjSubgroup (a * b * a) V = conjSubgroup y V ∧
    (∀ u ∈ V ⊓ wOf V H, (a * b * a) * u * (a * b * a)⁻¹ = ⁅b, u⁆ ∧
      ⁅b, u⁆ ∈ conjSubgroup y V ⊓ wOf V H ∧ ⁅a, ⁅b, u⁆⁆ = u) ∧
    (∀ v ∈ conjSubgroup y V ⊓ wOf V H, (a * b * a) * v * (a * b * a)⁻¹ = ⁅a, v⁆) := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  have hWab : ∀ x ∈ wOf V H, ∀ z ∈ wOf V H, x * z = z * x := fun x hx z hz =>
    hc.wOf_isElemAbelian.comm hx hz
  have haX : a ∈ xOf V H := le_xOf (V_mem_omegaOf V H) ha
  have hbX : b ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hyH) hb
  have haH : a ∈ H := hVH ha
  have haa : a * a = 1 := hc.elemAb.mul_self_eq_one ha
  have hbb : b * b = 1 := by
    have h1 := hc.elemAb.mul_self_eq_one (mem_conjSubgroup.mp hb)
    calc b * b = y * ((y⁻¹ * b * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have binv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨t, ht⟩ : ∃ t : G, t = a * b * a := ⟨_, rfl⟩
  have htX : t ∈ xOf V H := by
    rw [ht]; exact (xOf V H).mul_mem ((xOf V H).mul_mem haX hbX) haX
  have htH : t ∈ H := xOf_le_H hVH htX
  have hti : t⁻¹ = a * b * a := by
    have : (a * b * a)⁻¹ = a⁻¹ * b⁻¹ * a⁻¹ := by group
    rw [ht, this, ainv, binv]
  have htt : t * t = 1 := by
    calc t * t = (a * b * a) * (a * b * a) := by rw [ht]
      _ = a * b * (a * a) * b * a := by group
      _ = 1 := by rw [haa, mul_one]; calc a * b * b * a = a * (b * b) * a := by group
                                          _ = 1 := by rw [hbb, mul_one, haa]
  have hta : t * a * t⁻¹ = (a * b) ^ 3 * b := by
    rw [hti, ht]
    calc a * b * a * a * (a * b * a) = a * b * (a * a) * (a * b * a) := by group
      _ = a * b * (a * b * a) := by rw [haa, mul_one]
      _ = (a * b) ^ 3 * b := by
        calc a * b * (a * b * a) = a * b * a * b * a * (b * b) := by rw [hbb, mul_one]; group
          _ = (a * b) ^ 3 * b := by rw [pow_three]; simp only [mul_assoc]
  have hnH : y⁻¹ * t ∈ H := H.mul_mem (H.inv_mem hyH) htH
  have hWy : ∀ x : G, x ∈ wOf V H ↔ y⁻¹ * x * y ∈ wOf V H := mem_wOf_iff_conj hyH
  have hnN : y⁻¹ * t ∈ Subgroup.normalizer (V : Set G) := by
    apply hc.mem_normalizer_of_inf_ne_bot hnH
    have hyb : y⁻¹ * b * y ∈ V := mem_conjSubgroup.mp hb
    have hybH : y⁻¹ * b * y ∈ H := hVH hyb
    have hmemT : (y⁻¹ * t) * a * (y⁻¹ * t)⁻¹ ∈ conjSubgroup (y⁻¹ * t) V := by
      rw [mem_conjSubgroup]
      have e : (y⁻¹ * t)⁻¹ * ((y⁻¹ * t) * a * (y⁻¹ * t)⁻¹) * (y⁻¹ * t) = a := by group
      rw [e]; exact ha
    have hxH : (y⁻¹ * t) * a * (y⁻¹ * t)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hnH haH) (H.inv_mem hnH)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨piBar V H ⟨y⁻¹ * b * y, hybH⟩, ?_⟩, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨mem_barOf_iff.mpr ⟨⟨y⁻¹ * b * y, hybH⟩, hyb, rfl⟩, ?_⟩
      rw [conjSubgroup_piBar_barOf]
      refine mem_barOf_iff.mpr ⟨⟨(y⁻¹ * t) * a * (y⁻¹ * t)⁻¹, hxH⟩, hmemT, ?_⟩
      apply piBar_eq_of_inv_mul_mem
      show ((y⁻¹ * t) * a * (y⁻¹ * t)⁻¹)⁻¹ * (y⁻¹ * b * y) ∈ wOf V H
      have e : ((y⁻¹ * t) * a * (y⁻¹ * t)⁻¹)⁻¹ * (y⁻¹ * b * y) =
          (y⁻¹ * b * y)⁻¹ * (y⁻¹ * (a * b) ^ 3 * y)⁻¹ * (y⁻¹ * b * y) := by
        have : (y⁻¹ * t) * a * (y⁻¹ * t)⁻¹ = y⁻¹ * (t * a * t⁻¹) * y := by group
        rw [this, hta]; group
      rw [e]
      have hw0 : (y⁻¹ * (a * b) ^ 3 * y)⁻¹ ∈ wOf V H := (wOf V H).inv_mem ((hWy _).mp hbr)
      have := (Subgroup.mem_normalizer_iff.mp
        (H_le_normalizer_wOf V H (H.inv_mem hybH)) _).mp hw0
      simpa [mul_assoc] using this
    · intro h1
      have h2 : piBar V H ⟨y⁻¹ * b * y, hybH⟩ = 1 := congrArg Subtype.val h1
      exact hbW ((hWy b).mpr ((piBar_eq_one_iff _).1 h2))
  have htV : conjSubgroup t V = conjSubgroup y V := by
    rw [show t = y * (y⁻¹ * t) by group, ← conjSubgroup_conjSubgroup,
      mem_normalizer_iff_conjSubgroup_eq.mp hnN]
  have hne : conjSubgroup y V ≠ V := by
    intro heq
    apply hyc
    refine ⟨hy, fun u hu w hw => ?_⟩
    rw [heq] at hw
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc.elemAb.comm hu hw)]
    exact (wOf V H).one_mem
  have hbot := inf_conjSubgroup_eq_bot_of_isTI hc.ti hne
  have hmain : ∀ u ∈ V ⊓ wOf V H, t * u * t⁻¹ = ⁅b, u⁆ ∧ ⁅b, u⁆ ∈ conjSubgroup y V ⊓ wOf V H ∧
      ⁅a, ⁅b, u⁆⁆ = u := by
    intro u hu
    have huV : u ∈ V := hu.1
    have huW : u ∈ wOf V H := hu.2
    set α := t * u * t⁻¹ with hα
    have hαV : α ∈ conjSubgroup y V := by
      rw [← htV, mem_conjSubgroup]
      have e : t⁻¹ * α * t = u := by rw [hα]; group
      rw [e]; exact huV
    have hαW : α ∈ wOf V H :=
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H htH)) u).mp huW
    have hau : a * u * a⁻¹ = u := by
      rw [hc.elemAb.comm ha huV, mul_inv_cancel_right]
    have hαe : α = a * b * u * b * a := by
      rw [hα, ht]
      calc a * b * a * u * (a * b * a)⁻¹ = a * b * (a * u * a⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = a * b * u * b * a := by rw [hau, ainv, binv]
    have haα : a * α * a⁻¹ = b * u * b := by
      rw [hαe, ainv]
      calc a * (a * b * u * b * a) * a = (a * a) * b * u * b * (a * a) := by group
        _ = b * u * b := by rw [haa]; group
    have hbub : b * u * b = ⁅b, u⁆ * u := by
      rw [commutatorElement_def, binv]; group
    have hcomm1 : ⁅a, α⁆ = ⁅b, u⁆ * u * α⁻¹ := by
      rw [commutatorElement_def, haα, hbub]
    have hbu : ⁅b, u⁆ ∈ conjSubgroup y V ⊓ wOf V H := hc.commutator_mem_conj_inf_wOf hyH hb huW
    have haαm : ⁅a, α⁆ ∈ V ⊓ wOf V H := by
      have := hc.commutator_mem_conj_inf_wOf (H.one_mem) (v := a) (w := α)
        (by rwa [conjSubgroup_one]) hαW
      rwa [conjSubgroup_one] at this
    have hcc : ⁅a, α⁆ * u⁻¹ = ⁅b, u⁆ * α⁻¹ := by
      have hcom : u * α⁻¹ = α⁻¹ * u := hWab u huW α⁻¹ ((wOf V H).inv_mem hαW)
      calc ⁅a, α⁆ * u⁻¹ = ⁅b, u⁆ * (u * α⁻¹) * u⁻¹ := by rw [hcomm1]; group
        _ = ⁅b, u⁆ * (α⁻¹ * u) * u⁻¹ := by rw [hcom]
        _ = ⁅b, u⁆ * α⁻¹ := by group
    have hmemV : ⁅a, α⁆ * u⁻¹ ∈ V := V.mul_mem haαm.1 (V.inv_mem huV)
    have hmemU : ⁅a, α⁆ * u⁻¹ ∈ conjSubgroup y V := by
      rw [hcc]
      exact (conjSubgroup y V).mul_mem hbu.1 ((conjSubgroup y V).inv_mem hαV)
    have h1 : ⁅a, α⁆ * u⁻¹ ∈ V ⊓ conjSubgroup y V := ⟨hmemV, hmemU⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    have hαb : α = ⁅b, u⁆ := by
      have h2 : ⁅a, α⁆ * α = ⁅b, u⁆ * u := by
        rw [commutatorElement_def, inv_mul_cancel_right, haα, hbub]
      rw [h1] at h2
      have hcom : u * ⁅b, u⁆ = ⁅b, u⁆ * u := hWab u huW _ hbu.2
      have h3 : u * α = u * ⁅b, u⁆ := by rw [h2, hcom]
      exact mul_left_cancel h3
    refine ⟨hαb, hbu, ?_⟩
    rw [← hαb, h1]
  rw [← ht]
  refine ⟨htX, htt, hnN, htV, fun u hu => hmain u hu, ?_⟩
  intro v hv
  have hu : t * v * t⁻¹ ∈ V ⊓ wOf V H := by
    refine ⟨?_, ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H htH)) v).mp hv.2⟩
    have : t * v * t⁻¹ ∈ conjSubgroup t (conjSubgroup y V) := by
      rw [mem_conjSubgroup]
      have e : t⁻¹ * (t * v * t⁻¹) * t = v := by group
      rw [e]; exact hv.1
    rw [← htV, conjSubgroup_conjSubgroup, htt, conjSubgroup_one] at this
    exact this
  have hback : t * (t * v * t⁻¹) * t⁻¹ = v := by
    calc t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t * t)⁻¹ := by group
      _ = v := by rw [htt]; group
  obtain ⟨h1, -, h3⟩ := hmain _ hu
  rw [hback] at h1
  calc t * v * t⁻¹ = ⁅a, ⁅b, t * v * t⁻¹⁆⁆ := h3.symm
    _ = ⁅a, v⁆ := by rw [← h1]

theorem commutator_mem_of_braid (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ xOf V H)
    (hyc : y ∉ Ycomm V H) {A₁ : Subgroup G} (hA₁ : A₁ ≤ V ⊓ wOf V H)
    (hinv : ∀ n ∈ xOf V H, conjSubgroup n V = V → conjSubgroup n A₁ = A₁)
    {a b : G} (ha : a ∈ V) (hb : b ∈ conjSubgroup y V) (hbW : b ∉ wOf V H)
    (hbr : (a * b) ^ 3 ∈ wOf V H) :
    ∀ α ∈ conjSubgroup y A₁, ⁅a, α⁆ ∈ A₁ := by
  obtain ⟨htX, -, hnN, -, hmain, -⟩ := hs.braid_data hy hyc ha hb hbW hbr
  have hnX : y⁻¹ * (a * b * a) ∈ xOf V H := (xOf V H).mul_mem ((xOf V H).inv_mem hy) htX
  have hnA := hinv _ hnX (mem_normalizer_iff_conjSubgroup_eq.mp hnN)
  have htA : conjSubgroup (a * b * a) A₁ = conjSubgroup y A₁ := by
    rw [show a * b * a = y * (y⁻¹ * (a * b * a)) by group, ← conjSubgroup_conjSubgroup, hnA]
  intro α hα
  have hα' : α ∈ conjSubgroup (a * b * a) A₁ := by rw [htA]; exact hα
  obtain ⟨u, hu, hαu⟩ : ∃ u ∈ A₁, α = (a * b * a) * u * (a * b * a)⁻¹ :=
    ⟨(a * b * a)⁻¹ * α * (a * b * a), mem_conjSubgroup.mp hα', by group⟩
  obtain ⟨h1, -, h3⟩ := hmain u (hA₁ hu)
  rw [hαu, h1, h3]
  exact hu

end Sec3Setup

@[expose] def xClosure (V H A₁ : Subgroup G) : Subgroup G :=
  ⨆ y ∈ xOf V H, conjSubgroup y A₁

theorem le_xClosure {V H A₁ : Subgroup G} {y : G} (hy : y ∈ xOf V H) :
    conjSubgroup y A₁ ≤ xClosure V H A₁ :=
  le_iSup₂_of_le y hy le_rfl

theorem xClosure_le {V H A₁ S : Subgroup G} (h : ∀ y ∈ xOf V H, conjSubgroup y A₁ ≤ S) :
    xClosure V H A₁ ≤ S :=
  iSup₂_le h

theorem self_le_xClosure {V H A₁ : Subgroup G} : A₁ ≤ xClosure V H A₁ := by
  have := le_xClosure (V := V) (H := H) (A₁ := A₁) (xOf V H).one_mem
  rwa [conjSubgroup_one] at this

theorem xClosure_le_wOf {V H A₁ : Subgroup G} (hVH : V ≤ H) (hA₁ : A₁ ≤ wOf V H) :
    xClosure V H A₁ ≤ wOf V H := by
  refine xClosure_le fun y hy α hα => ?_
  have hyH : y ∈ H := xOf_le_H hVH hy
  exact (mem_wOf_iff_conj hyH α).mpr (hA₁ (mem_conjSubgroup.mp hα))

theorem conjSubgroup_xClosure_le {V H A₁ : Subgroup G} {x : G} (hx : x ∈ xOf V H) :
    conjSubgroup x (xClosure V H A₁) ≤ xClosure V H A₁ := by
  have h : conjSubgroup x (xClosure V H A₁) =
      ⨆ y ∈ xOf V H, conjSubgroup x (conjSubgroup y A₁) := by
    unfold xClosure conjSubgroup
    simp only [Subgroup.map_iSup]
  rw [h]
  refine iSup₂_le fun y hy => ?_
  rw [conjSubgroup_conjSubgroup]
  exact le_iSup₂_of_le (x * y) ((xOf V H).mul_mem hx hy) le_rfl

theorem conjSubgroup_xClosure {V H A₁ : Subgroup G} [Finite G] {x : G} (hx : x ∈ xOf V H) :
    conjSubgroup x (xClosure V H A₁) = xClosure V H A₁ :=
  conjSubgroup_eq_of_le (conjSubgroup_xClosure_le hx)

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem conjSubgroup_xClosure_of_mem_H (hs : Sec3Setup M V Q P H) {A₁ : Subgroup G}
    (hA₁ : A₁ ≤ wOf V H) : ∀ h ∈ H, conjSubgroup h (xClosure V H A₁) = xClosure V H A₁ := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hW₁ : xClosure V H A₁ ≤ wOf V H := xClosure_le_wOf hc.V_le_H hA₁
  have hle : xOf V H ⊔ cPbar V H P ≤ Subgroup.normalizer (xClosure V H A₁ : Set G) := by
    refine sup_le (fun x hx => ?_) (fun c hc' => ?_)
    · exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_xClosure hx)
    · apply mem_normalizer_of_conjSubgroup_eq
      have hcen := hc.cPbar_centralizes_wOf hc'
      have hfix : ∀ z ∈ wOf V H, c⁻¹ * z * c = z := by
        intro z hz
        calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
          _ = c⁻¹ * (c * z) := by rw [← hcen z hz]
          _ = z := by group
      ext z
      constructor
      · intro hz
        have h1 : c⁻¹ * z * c ∈ xClosure V H A₁ := mem_conjSubgroup.mp hz
        have h2 : c⁻¹ * z * c ∈ wOf V H := hW₁ h1
        have e : c * (c⁻¹ * z * c) = (c⁻¹ * z * c) * c := hcen _ h2
        have h3 : z = c⁻¹ * z * c := by
          calc z = (c * (c⁻¹ * z * c)) * c⁻¹ := by group
            _ = ((c⁻¹ * z * c) * c) * c⁻¹ := by rw [e]
            _ = c⁻¹ * z * c := by group
        rw [h3]; exact h1
      · intro hz
        exact mem_conjSubgroup.mpr (by rw [hfix z (hW₁ hz)]; exact hz)
  intro h hh
  have hh' : h ∈ xOf V H ⊔ cPbar V H P := by rw [hs.concl.2.1]; exact hh
  exact mem_normalizer_iff_conjSubgroup_eq.mp (hle hh')

end Sec3Setup

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
include hc

theorem wOf_comm {x z : G} (hx : x ∈ wOf V H) (hz : z ∈ wOf V H) : x * z = z * x :=
  hc.wOf_isElemAbelian.comm hx hz

theorem commutator_mul_of_mem_wOf {g u u' : G} (hg : g ∈ H) (hu : u ∈ wOf V H)
    (hu' : u' ∈ wOf V H) : ⁅g, u * u'⁆ = ⁅g, u⁆ * ⁅g, u'⁆ := by
  have hq : g * u' * g⁻¹ ∈ wOf V H :=
    ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hg)) u').mp hu'
  have h1 : u'⁻¹ * u⁻¹ = u⁻¹ * u'⁻¹ :=
    hc.wOf_comm ((wOf V H).inv_mem hu') ((wOf V H).inv_mem hu)
  have h2 : (g * u' * g⁻¹) * u⁻¹ = u⁻¹ * (g * u' * g⁻¹) :=
    hc.wOf_comm hq ((wOf V H).inv_mem hu)
  calc ⁅g, u * u'⁆ = (g * u * g⁻¹) * (g * u' * g⁻¹) * (u'⁻¹ * u⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = (g * u * g⁻¹) * (g * u' * g⁻¹) * (u⁻¹ * u'⁻¹) := by rw [h1]
    _ = (g * u * g⁻¹) * ((g * u' * g⁻¹) * u⁻¹) * u'⁻¹ := by group
    _ = (g * u * g⁻¹) * (u⁻¹ * (g * u' * g⁻¹)) * u'⁻¹ := by rw [h2]
    _ = ⁅g, u⁆ * ⁅g, u'⁆ := by simp only [commutatorElement_def]; group

theorem commutator_mem_xClosure {A₁ : Subgroup G} (hA₁ : A₁ ≤ wOf V H) {a : G} (haH : a ∈ H)
    (hR : ∀ y ∈ xOf V H, ∀ α ∈ conjSubgroup y A₁, ⁅a, α⁆ ∈ A₁) :
    ∀ w ∈ xClosure V H A₁, ⁅a, w⁆ ∈ A₁ := by
  let S : Subgroup G :=
    { carrier := {w | w ∈ wOf V H ∧ ⁅a, w⁆ ∈ A₁}
      one_mem' := ⟨(wOf V H).one_mem, by simp [commutatorElement_def]⟩
      mul_mem' := fun {w₁ w₂} h₁ h₂ => by
        refine ⟨(wOf V H).mul_mem h₁.1 h₂.1, ?_⟩
        rw [hc.commutator_mul_of_mem_wOf haH h₁.1 h₂.1]
        exact A₁.mul_mem h₁.2 h₂.2
      inv_mem' := fun {w} h => by
        refine ⟨(wOf V H).inv_mem h.1, ?_⟩
        have h1 : ⁅a, w * w⁻¹⁆ = ⁅a, w⁆ * ⁅a, w⁻¹⁆ :=
          hc.commutator_mul_of_mem_wOf haH h.1 ((wOf V H).inv_mem h.1)
        rw [mul_inv_cancel, commutatorElement_def] at h1
        have h2 : ⁅a, w⁻¹⁆ = ⁅a, w⁆⁻¹ := by
          have : ⁅a, w⁆ * ⁅a, w⁻¹⁆ = 1 := by
            rw [← h1]; simp [commutatorElement_def]
          exact eq_inv_of_mul_eq_one_right this
        rw [h2]
        exact A₁.inv_mem h.2 }
  have hS : xClosure V H A₁ ≤ S := by
    refine xClosure_le fun y hy α hα => ?_
    have hyH : y ∈ H := xOf_le_H hc.V_le_H hy
    exact ⟨(mem_wOf_iff_conj hyH α).mpr (hA₁ (mem_conjSubgroup.mp hα)), hR y hy α hα⟩
  exact fun w hw => (hS hw).2

end MinCex

theorem sec34SummandStatement_of_parts (hLine : Sec34LineStatement)
    (hBraid : Sec34BraidStatement) (hOpp : Sec34OppMeetStatement) :
    Sec34SummandStatement := by
  intro G _ _ M V Q P H hs h3 hcc
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨A₁, hA₁, hcard, hinv⟩ := hLine G M V Q P H hs h3 hcc
  have hA₁W : A₁ ≤ wOf V H := fun x hx => (hA₁ hx).2
  have hR : ∀ y ∈ xOf V H, ∀ a ∈ V, ∀ α ∈ conjSubgroup y A₁, ⁅a, α⁆ ∈ A₁ := by
    intro y hy a ha α hα
    have hyH : y ∈ H := xOf_le_H hVH hy
    have hαW : α ∈ wOf V H := (mem_wOf_iff_conj hyH α).mpr (hA₁W (mem_conjSubgroup.mp hα))
    by_cases hyc : y ∈ Ycomm V H
    · have hαP : α ∈ P := hs.aof_le_P hyc
        (Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mpr (hA₁ (mem_conjSubgroup.mp hα)).1, hαW⟩)
      have : ⁅a, α⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hc.commute_of_mem_P hαP ha)
      rw [this]; exact A₁.one_mem
    · by_cases haW : a ∈ wOf V H
      · have : ⁅a, α⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc.wOf_comm haW hαW)
        rw [this]; exact A₁.one_mem
      · obtain ⟨_, hb, hbW, hbr⟩ := hBraid G M V Q P H hs h3 y hy hyc a ha haW
        exact hs.commutator_mem_of_braid hy hyc hA₁ hinv ha hb hbW hbr α hα
  have hW₁ : xClosure V H A₁ ≤ wOf V H := xClosure_le_wOf hVH hA₁W
  refine ⟨xClosure V H A₁, hW₁, hs.conjSubgroup_xClosure_of_mem_H hA₁W, ?_⟩
  have hcomm : ∀ v ∈ V, ∀ w ∈ xClosure V H A₁, ⁅v, w⁆ ∈ A₁ := fun v hv w hw =>
    hc.commutator_mem_xClosure hA₁W (hVH hv) (fun y hy α hα => hR y hy v hv α hα) w hw
  obtain ⟨g, hgX, u₀, hu₀, w₀, hw₀, hnc⟩ := hc.exists_noncomm_conj hs.setup.data
  have hgH : g ∈ H := xOf_le_H hVH hgX
  have hgc : g ∉ Ycomm V H := fun h => hnc (h.2 u₀ hu₀ w₀ hw₀)
  have hw₀H : w₀ ∈ H := conjSubgroup_le_of_le_of_mem hVH hgH hw₀
  have hw₀W : w₀ ∉ wOf V H := fun h => hnc
    (hc.commutator_mem_conj_inf_wOf H.one_mem (v := u₀) (w := w₀)
      (by rw [conjSubgroup_one]; exact hu₀) h).2
  have hgW₁ : conjSubgroup g (xClosure V H A₁) = xClosure V H A₁ := conjSubgroup_xClosure hgX
  have hginv : ∀ u ∈ xClosure V H A₁, g⁻¹ * u * g ∈ xClosure V H A₁ := by
    intro u hu
    rw [← hgW₁] at hu
    exact mem_conjSubgroup.mp hu
  have hmemc : ∀ u ∈ xClosure V H A₁, ⁅w₀, u⁆ ∈ conjSubgroup g A₁ := by
    intro u hu
    have hv₀ : g⁻¹ * w₀ * g ∈ V := mem_conjSubgroup.mp hw₀
    have h1 := hcomm _ hv₀ _ (hginv u hu)
    rw [mem_conjSubgroup]
    have e : g⁻¹ * ⁅w₀, u⁆ * g = ⁅g⁻¹ * w₀ * g, g⁻¹ * u * g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact h1
  let f : ↥(V ⊓ xClosure V H A₁) → ↥(conjSubgroup g A₁) := fun u => ⟨⁅w₀, u⁆, hmemc u u.2.2⟩
  have hinj : Function.Injective f := by
    intro u u' h
    have hh : ⁅w₀, (u : G)⁆ = ⁅w₀, (u' : G)⁆ := congrArg Subtype.val h
    have huW : (u : G) ∈ wOf V H := hW₁ u.2.2
    have hu'W : (u' : G) ∈ wOf V H := hW₁ u'.2.2
    have hinvc : ⁅w₀, (u' : G)⁻¹⁆ = ⁅w₀, (u' : G)⁆⁻¹ := by
      have h1 := hc.commutator_mul_of_mem_wOf hw₀H hu'W ((wOf V H).inv_mem hu'W)
      have h0 : ⁅w₀, (u' : G) * (u' : G)⁻¹⁆ = 1 := by
        rw [mul_inv_cancel]; simp [commutatorElement_def]
      have : ⁅w₀, (u' : G)⁆ * ⁅w₀, (u' : G)⁻¹⁆ = 1 := by rw [← h1]; exact h0
      exact eq_inv_of_mul_eq_one_right this
    have hd1 : ⁅w₀, (u : G) * (u' : G)⁻¹⁆ = 1 := by
      rw [hc.commutator_mul_of_mem_wOf hw₀H huW ((wOf V H).inv_mem hu'W), hinvc, hh]
      exact mul_inv_cancel _
    have hcm : w₀ * ((u : G) * (u' : G)⁻¹) = ((u : G) * (u' : G)⁻¹) * w₀ :=
      commutatorElement_eq_one_iff_mul_comm.mp hd1
    have hdV : (u : G) * (u' : G)⁻¹ ∈ V := V.mul_mem u.2.1 (V.inv_mem u'.2.1)
    by_contra hne
    have hd : (u : G) * (u' : G)⁻¹ ≠ 1 := fun h' => hne (Subtype.ext (mul_inv_eq_one.mp h'))
    have hM : w₀ ∈ M := hc.mem_M_of_commute hdV hd hcm
    have hN : w₀ ∈ Subgroup.normalizer (V : Set G) := by rw [hc.normalizer_eq]; exact hM
    exact hw₀W (hOpp G M V Q P H hs h3 g hgX hgc w₀ hw₀ hN)
  have hle : Nat.card ↥(V ⊓ xClosure V H A₁) ≤ Nat.card ↥(conjSubgroup g A₁) :=
    Nat.card_le_card_of_injective f hinj
  rw [card_conjSubgroup, hcard] at hle
  have hA₁le : A₁ ≤ V ⊓ xClosure V H A₁ := le_inf (fun x hx => (hA₁ hx).1) self_le_xClosure
  have hge : Nat.card ↥A₁ ≤ Nat.card ↥(V ⊓ xClosure V H A₁) := Subgroup.card_le_of_le hA₁le
  rw [hcard] at hge
  exact le_antisymm hle hge

end CFSG.RankThree.GF2n.Tim79a
