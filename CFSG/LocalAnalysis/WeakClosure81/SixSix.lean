module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem centralizesMod_conj (V₀ V : Subgroup G) (m g : G) :
    CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) (g⁻¹ * m * g) ↔
      CentralizesMod V₀ V m := by
  unfold CentralizesMod
  constructor
  · intro h v hv
    have hw : g⁻¹ * v * g ∈ conjSubgroup V g :=
      mem_conjSubgroup_iff.2 (by rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group]; exact hv)
    have h1 := h (g⁻¹ * v * g) hw
    rw [mem_conjSubgroup_iff] at h1
    convert h1 using 1 <;> group
  · intro h w hw
    rw [mem_conjSubgroup_iff] at hw ⊢
    have h1 := h (g * w * g⁻¹) hw
    convert h1 using 1 <;> group

theorem centralizesMod_conj' (V₀ V : Subgroup G) (m' g : G) :
    CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) m' ↔
      CentralizesMod V₀ V (g * m' * g⁻¹) := by
  have h := centralizesMod_conj V₀ V (g * m' * g⁻¹) g
  rwa [show g⁻¹ * (g * m' * g⁻¹) * g = m' by group] at h

theorem mem_centMod_conj {V₀ V : Subgroup G} {m g x : G} :
    x ∈ centMod (conjSubgroup V₀ g) (conjSubgroup V g) (g⁻¹ * m * g) ↔
      g * x * g⁻¹ ∈ centMod V₀ V m := by
  unfold centMod
  constructor
  · rintro ⟨hxV, hx⟩
    refine ⟨?_, ?_⟩
    · rw [mem_conjSubgroup_iff] at hxV
      convert hxV using 1 <;> group
    · rw [mem_conjSubgroup_iff] at hx
      convert hx using 1 <;> group
  · rintro ⟨hyV, hy⟩
    refine ⟨?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      convert hyV using 1 <;> group
    · rw [mem_conjSubgroup_iff]
      convert hy using 1 <;> group

theorem centMod_conj_card (V₀ V : Subgroup G) (m g : G) :
    Nat.card (centMod (conjSubgroup V₀ g) (conjSubgroup V g) (g⁻¹ * m * g)) =
      Nat.card (centMod V₀ V m) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, (mem_centMod_conj (m := m) (g := g)).1 x.2⟩
      invFun := fun y => ⟨g⁻¹ * (y : G) * g, ?_⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }
  rw [mem_centMod_conj]
  convert y.2 using 1
  group

theorem centMod_conj'_card (V₀ V : Subgroup G) (m' g : G) :
    Nat.card (centMod (conjSubgroup V₀ g) (conjSubgroup V g) m') =
      Nat.card (centMod V₀ V (g * m' * g⁻¹)) := by
  have h := centMod_conj_card V₀ V (g * m' * g⁻¹) g
  rwa [show g⁻¹ * (g * m' * g⁻¹) * g = m' by group] at h

theorem centralizesMod_sq_conj (V₀ V : Subgroup G) (m g : G) :
    CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) ((g⁻¹ * m * g) * (g⁻¹ * m * g)) ↔
      CentralizesMod V₀ V (m * m) := by
  have h := centralizesMod_conj V₀ V (m * m) g
  rwa [show g⁻¹ * (m * m) * g = (g⁻¹ * m * g) * (g⁻¹ * m * g) by group] at h

theorem centralizesMod_sq_conj' (V₀ V : Subgroup G) (m' g : G) :
    CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) (m' * m') ↔
      CentralizesMod V₀ V ((g * m' * g⁻¹) * (g * m' * g⁻¹)) := by
  have h := centralizesMod_conj' V₀ V (m' * m') g
  rwa [show g * (m' * m') * g⁻¹ = (g * m' * g⁻¹) * (g * m' * g⁻¹) by group] at h

theorem mBarGT_conj (M V₀ V : Subgroup G) (g : G) (n : ℕ) :
    MBarGT (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) n ↔ MBarGT M V₀ V n := by
  unfold MBarGT
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun m hm hC hC2 => ?_, fun hodd => ?_⟩
    · have hm' : g⁻¹ * m * g ∈ conjSubgroup M g :=
        mem_conjSubgroup_iff.2 (by rw [show g * (g⁻¹ * m * g) * g⁻¹ = m by group]; exact hm)
      have hC' : ¬ CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) (g⁻¹ * m * g) :=
        fun hh => hC ((centralizesMod_conj V₀ V m g).1 hh)
      have hC2' : CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g)
          ((g⁻¹ * m * g) * (g⁻¹ * m * g)) :=
        (centralizesMod_sq_conj V₀ V m g).2 hC2
      have hh := h1 (g⁻¹ * m * g) hm' hC' hC2'
      rw [← centMod_conj_card V₀ V m g, ← E3.card_conjSubgroup V g]
      exact hh
    · have hodd' : ∀ m' ∈ conjSubgroup M g,
          CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) (m' * m') →
          CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) m' := by
        intro m' hm' hc
        have hm : g * m' * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 hm'
        have hc' : CentralizesMod V₀ V ((g * m' * g⁻¹) * (g * m' * g⁻¹)) :=
          (centralizesMod_sq_conj' V₀ V m' g).1 hc
        exact (centralizesMod_conj' V₀ V m' g).2 (hodd (g * m' * g⁻¹) hm hc')
      have hh := h2 hodd'
      rw [← E3.card_conjSubgroup V₀ g, ← E3.card_conjSubgroup V g]
      exact hh
  · rintro ⟨h1, h2⟩
    refine ⟨fun m' hm' hC hC2 => ?_, fun hodd => ?_⟩
    · have hm : g * m' * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 hm'
      have hC' : ¬ CentralizesMod V₀ V (g * m' * g⁻¹) :=
        fun hh => hC ((centralizesMod_conj' V₀ V m' g).2 hh)
      have hC2' : CentralizesMod V₀ V ((g * m' * g⁻¹) * (g * m' * g⁻¹)) :=
        (centralizesMod_sq_conj' V₀ V m' g).1 hC2
      have hh := h1 (g * m' * g⁻¹) hm hC' hC2'
      rw [centMod_conj'_card V₀ V m' g, E3.card_conjSubgroup V g]
      exact hh
    · have hodd' : ∀ m ∈ M, CentralizesMod V₀ V (m * m) → CentralizesMod V₀ V m := by
        intro m hm hc
        have hm' : g⁻¹ * m * g ∈ conjSubgroup M g :=
          mem_conjSubgroup_iff.2 (by rw [show g * (g⁻¹ * m * g) * g⁻¹ = m by group]; exact hm)
        have hc' : CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g)
            ((g⁻¹ * m * g) * (g⁻¹ * m * g)) :=
          (centralizesMod_sq_conj V₀ V m g).2 hc
        exact (centralizesMod_conj V₀ V m g).1 (hodd (g⁻¹ * m * g) hm' hc')
      have hh := h2 hodd'
      rw [E3.card_conjSubgroup V₀ g, E3.card_conjSubgroup V g]
      exact hh

theorem mBar_conj (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) (g : G) :
    mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g) = mBar M V₀ V hV := by
  set hVg := E3.isElemAbelian_conjSubgroup hV g with hVgdef
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hV₀
  have hMg : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hM).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hM₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  refine le_antisymm ?_ ?_
  · by_contra hle
    rw [not_le] at hle
    set n := mBar M V₀ V hV with hn
    have hb : MBarGT (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) n :=
      (mBarGT_iff_lt_mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg hV₀g
        hMg hM₀g n).2 (by simpa [hn] using hle)
    have ha : MBarGT M V₀ V n := (mBarGT_conj M V₀ V g n).1 hb
    have : n < mBar M V₀ V hV := (mBarGT_iff_lt_mBar M V₀ V hV hV₀ hM hM₀ n).1 ha
    exact lt_irrefl n (by simpa [hn] using this)
  · by_contra hle
    rw [not_le] at hle
    set n := mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg with hn
    have ha : MBarGT M V₀ V n :=
      (mBarGT_iff_lt_mBar M V₀ V hV hV₀ hM hM₀ n).2 (by simpa [hn] using hle)
    have hb : MBarGT (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) n :=
      (mBarGT_conj M V₀ V g n).2 ha
    have : n < mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg :=
      (mBarGT_iff_lt_mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg hV₀g
        hMg hM₀g n).1 hb
    exact lt_irrefl n (by simpa [hn] using this)

theorem oneFirst_of_lt_mBar {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    {n : ℕ} (hn : n < mBar M V₀ V hV) (g : G) (hO : OFirst n M V₀ V g) :
    OneFirst M V₀ V g := by
  intro x hx
  obtain ⟨hxinf, hxC⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxVg, hxM⟩ := Subgroup.mem_inf.1 hxinf
  rw [mem_cTilde_iff hV hM]
  refine ⟨hxM, ?_⟩
  have hxs : x ∈ stabTil V₀ V := ⟨hM hxM, hM₀ hxM⟩
  refine ⟨hxs, (actTil_eq_one_iff V₀ V hV ⟨x, hxs⟩).2 ?_⟩
  by_contra hnot
  have hGT := (mBarGT_iff_lt_mBar M V₀ V hV hV₀ hM hM₀ n).2 hn
  have hx2 : x * x = 1 := by
    have h2 := (E3.isElemAbelian_conjSubgroup hV g).2 x hxVg
    simpa [pow_two] using h2
  have hC2 : CentralizesMod V₀ V (x * x) := by
    rw [hx2]
    intro v _
    simpa using V₀.one_mem
  have hcard := hGT.1 x hxM hnot hC2
  set U := V ⊓ conjSubgroup M g with hU
  have hUleV : U ≤ V := inf_le_left
  have hle_cent : U ≤ centMod V₀ V x := by
    intro u hu
    obtain ⟨huV, huMg⟩ := Subgroup.mem_inf.1 hu
    refine ⟨huV, ?_⟩
    have hcomm : u * x = x * u := hxC u (Subgroup.mem_inf.2 ⟨huV, huMg⟩)
    have hone : x * u * x⁻¹ * u⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [hone]
    exact V₀.one_mem
  have hcardU : Nat.card U ≤ Nat.card (centMod V₀ V x) :=
    Nat.card_le_card_of_injective
      (fun u : U => (⟨(u : G), hle_cent u.2⟩ : ↥(centMod V₀ V x)))
      (fun a b hab => Subtype.ext (by
        have h := congrArg (fun y : ↥(centMod V₀ V x) => (y : G)) hab
        simpa using h))
  have h2 : 2 ^ (n + 1) * Nat.card U ≤ Nat.card V :=
    (Nat.mul_le_mul_left _ hcardU).trans hcard
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hpow := E3.card_eq_two_pow_mul hV2 hUleV
  rw [hpow] at h2
  have hle1 : 2 ^ (n + 1) ≤ 2 ^ (E3.mQuot V U) :=
    Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hle2 : n + 1 ≤ E3.mQuot V U :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle1
  have hUeq : E3.mQuot V U = E3.mQuot V (conjSubgroup M g) := by
    have h1 : U.subgroupOf V = (conjSubgroup M g).subgroupOf V := by
      ext y
      simp only [Subgroup.mem_subgroupOf]
      rw [hU]
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    rw [E3.mQuot_eq_rkIdx, E3.mQuot_eq_rkIdx, h1]
  have hle3 : E3.mQuot V (conjSubgroup M g) ≤ n := hO.2.1
  omega

theorem oneDual_of_lt_mBar {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    {n : ℕ} (hn : n < mBar M V₀ V hV) (g : G) (hg : InCalO n M V₀ V g) :
    OneDual M V₀ V g := by
  have hVg := E3.isElemAbelian_conjSubgroup hV g
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hV₀
  have hMg : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hM).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hM₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hconj : n < mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg := by
    rw [mBar_conj M V₀ V hV hV₀ hM hM₀ g]
    exact hn
  have hfirst := oneFirst_of_lt_mBar hVg hV₀g hMg hM₀g hconj g⁻¹
    ((oFirst_swap n M V₀ V g).2 hg.2)
  exact (oneFirst_swap M V₀ V g).1 hfirst

theorem six_six {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    {n : ℕ} (hn : n < mBar M V₀ V hV) :
    ∀ g : G, InCalO n M V₀ V g ↔ InCalO1 n M V₀ V g :=
  fun g => ⟨fun hg => ⟨hg, oneFirst_of_lt_mBar hV hV₀ hM hM₀ hn g hg.1,
    oneDual_of_lt_mBar hV hV₀ hM hM₀ hn g hg⟩, fun hg => hg.1⟩

end CFSG.LocalAnalysis.WeakClosure81
