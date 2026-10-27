module

public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.B15P4

open CFSG.Open
open scoped commutatorElement

section General

variable {M : Type*} [Group M]

theorem perfect_of_isComponentOf {K X : Subgroup M} (h : IsComponentOf K X) : ⁅K, K⁆ = K := by
  have : Group.IsPerfect K := ⟨h.2.2.1⟩
  exact Subgroup.isPerfect_iff.mp this

theorem ne_bot_of_isComponentOf {K X : Subgroup M} (h : IsComponentOf K X) : K ≠ ⊥ := by
  have hn := CFSG.ComponentClassification.Quasisimple.nontrivial h.2.2
  exact (Subgroup.nontrivial_iff_ne_bot K).mp hn

theorem isSubnormal_inf {L X : Subgroup M} (Y : Subgroup M) (h : IsSubnormal L X) :
    IsSubnormal (L ⊓ Y) (X ⊓ Y) :=
  h.inf Y

theorem isComponentOf_of_le {K X Y : Subgroup M} (h : IsComponentOf K X) (hKY : K ≤ Y)
    (hYX : Y ≤ X) : IsComponentOf K Y := by
  refine ⟨hKY, ?_, h.2.2⟩
  have := isSubnormal_inf Y h.2.1
  rwa [inf_eq_left.mpr hKY, inf_eq_right.mpr hYX] at this

theorem isSubnormal_subgroupOf {L X : Subgroup M} (S : Subgroup M) (h : IsSubnormal L X) :
    IsSubnormal (L.subgroupOf S) (X.subgroupOf S) :=
  h.comap S.subtype

theorem isComponentOf_subgroupOf {K X : Subgroup M} (S : Subgroup M) (h : IsComponentOf K X)
    (hXS : X ≤ S) : IsComponentOf (K.subgroupOf S) (X.subgroupOf S) := by
  have hKS : K ≤ S := h.1.trans hXS
  refine ⟨fun x hx => h.1 hx, isSubnormal_subgroupOf S h.2.1, ?_⟩
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe hKS) h.2.2

theorem isComponentOf_map_hom {N : Type*} [Group N] (f : M →* N) {K X : Subgroup M}
    (h : IsComponentOf K X) (hf : ¬ K ≤ f.ker) : IsComponentOf (K.map f) (X.map f) := by
  refine ⟨Subgroup.map_mono h.1,
    CFSG.ComponentClassification.Components.chain_map f h.2.1, ?_⟩
  have hker : (f.comp K.subtype).ker ≠ ⊤ := by
    intro htop
    apply hf
    intro x hx
    have : (f.comp K.subtype) ⟨x, hx⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [htop]
      exact Subgroup.mem_top _
    exact this
  have hq := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top h.2.2
    (f.comp K.subtype) hker
  have hrange : K.map f = (f.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (MulEquiv.subgroupCongr hrange) hq

theorem isComponentOf_map_equiv {N : Type*} [Group N] (e : M ≃* N) {K X : Subgroup M}
    (h : IsComponentOf K X) : IsComponentOf (K.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  refine isComponentOf_map_hom e.toMonoidHom h fun hle => ne_bot_of_isComponentOf h ?_
  rw [eq_bot_iff]
  intro x hx
  have := hle hx
  rw [MonoidHom.mem_ker] at this
  have hx1 : x = 1 := e.injective (by simpa using this)
  simp [hx1]

theorem commutator_mul_left_of_commute {x y z : M} (h : z * y = y * z) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h' : z * y * z⁻¹ = y := by rw [h, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅x * z, y⁆ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ := by
        rw [h']
        simp only [commutatorElement_def]

theorem commutator_mul_right_of_commute {x y z : M} (h : z * x = x * z) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h' : z * x⁻¹ * z⁻¹ = x⁻¹ := by
    have hc : Commute z x := h
    exact hc.inv_right.mul_inv_cancel
  calc ⁅x, y * z⁆ = x * y * (z * x⁻¹ * z⁻¹) * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ := by
        rw [h']
        simp only [commutatorElement_def]

theorem commutator_mul_central {y₁ y₂ k₁ k₂ : M} (h12 : y₁ * y₂ = y₂ * y₁)
    (h1k₁ : y₁ * k₁ = k₁ * y₁) (h1k₂ : y₁ * k₂ = k₂ * y₁) (h2k₁ : y₂ * k₁ = k₁ * y₂)
    (h2k₂ : y₂ * k₂ = k₂ * y₂) : ⁅y₁ * k₁, y₂ * k₂⁆ = ⁅k₁, k₂⁆ := by
  have h3 : y₁ * (y₂ * k₂) = (y₂ * k₂) * y₁ := by
    rw [← mul_assoc, h12, mul_assoc, h1k₂, ← mul_assoc]
  calc ⁅y₁ * k₁, y₂ * k₂⁆ = ⁅k₁ * y₁, y₂ * k₂⁆ := by rw [h1k₁]
    _ = ⁅k₁, y₂ * k₂⁆ := commutator_mul_left_of_commute h3
    _ = ⁅k₁, k₂ * y₂⁆ := by rw [h2k₂]
    _ = ⁅k₁, k₂⁆ := commutator_mul_right_of_commute h2k₁

end General

section Conj

variable {V : Type*} [CommGroup V]

theorem conjAut_one (K : Subgroup (MulAut V)) : B1.conjAut 1 K = K := by
  ext x
  simp [B1.mem_conjAut]

theorem conjAut_mul (a b : MulAut V) (K : Subgroup (MulAut V)) :
    B1.conjAut (a * b) K = B1.conjAut a (B1.conjAut b K) := by
  ext x
  simp only [B1.mem_conjAut, mul_inv_rev, mul_assoc]

theorem conjAut_eq_self {G : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ G) :
    B1.conjAut a G = G := by
  ext x
  rw [B1.mem_conjAut]
  constructor
  · intro hx
    have := G.mul_mem (G.mul_mem ha hx) (G.inv_mem ha)
    simpa [mul_assoc] using this
  · intro hx
    exact G.mul_mem (G.mul_mem (G.inv_mem ha) hx) ha

theorem conjAut_eq_map (a : MulAut V) (K : Subgroup (MulAut V)) :
    B1.conjAut a K = K.map (MulAut.conj a).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

theorem conjAut_mono {a : MulAut V} {K L : Subgroup (MulAut V)} (h : K ≤ L) :
    B1.conjAut a K ≤ B1.conjAut a L :=
  B1.conjAut_le_iff.mpr h

theorem mem_normalizer_iff_conjAut {K : Subgroup (MulAut V)} {a : MulAut V} :
    a ∈ Subgroup.normalizer (K : Set (MulAut V)) ↔ B1.conjAut a K = K := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [B1.mem_conjAut]
    have := h (a⁻¹ * x * a)
    rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by simp [mul_assoc]] at this
    exact this
  · intro h y
    have h2 : a * y * a⁻¹ ∈ B1.conjAut a K ↔ y ∈ K := by
      rw [B1.mem_conjAut]
      simp [mul_assoc]
    rw [h] at h2
    exact h2.symm

theorem conjAut_inv_eq_self_iff {K : Subgroup (MulAut V)} {a : MulAut V} :
    B1.conjAut a⁻¹ K = K ↔ B1.conjAut a K = K := by
  constructor
  · intro h
    have := B1.conjAut_conjAut_inv a K
    rwa [h] at this
  · intro h
    have := B1.conjAut_inv_conjAut a K
    rwa [h] at this

theorem isComponentOf_conjAut {G K : Subgroup (MulAut V)} (hK : IsComponentOf K G) {a : MulAut V}
    (ha : a ∈ G) : IsComponentOf (B1.conjAut a K) G := by
  have h := isComponentOf_map_equiv (MulAut.conj a) hK
  have hG : G.map (MulAut.conj a).toMonoidHom = G := by
    rw [← conjAut_eq_map]
    exact conjAut_eq_self ha
  rw [hG, ← conjAut_eq_map] at h
  exact h

variable [Finite V]

theorem comp_commute {G K₁ K₂ : Subgroup (MulAut V)} (h₁ : IsComponentOf K₁ G)
    (h₂ : IsComponentOf K₂ G) (hne : K₁ ≠ K₂) : ⁅K₁, K₂⁆ = ⊥ := by
  obtain ⟨hK₁G, c₁⟩ := isComponentOf_iff_subgroupOf.mp h₁
  obtain ⟨hK₂G, c₂⟩ := isComponentOf_iff_subgroupOf.mp h₂
  have hne' : K₁.subgroupOf G ≠ K₂.subgroupOf G := by
    intro h
    apply hne
    have := congrArg (Subgroup.map G.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hK₁G, Subgroup.map_subgroupOf_eq_of_le hK₂G] at this
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ c₁ c₂ hne'
  have := congrArg (Subgroup.map G.subtype) hcomm
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK₁G,
    Subgroup.map_subgroupOf_eq_of_le hK₂G, Subgroup.map_bot] at this

end Conj

section Span

variable {V : Type*} [CommGroup V]

@[expose] def Kspan (A K : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ a ∈ A, B1.conjAut a K

theorem conjAut_le_Kspan {A K : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) :
    B1.conjAut a K ≤ Kspan A K :=
  le_iSup₂ (f := fun (a : MulAut V) (_ : a ∈ A) => B1.conjAut a K) a ha

theorem Kspan_le_iff {A K X : Subgroup (MulAut V)} :
    Kspan A K ≤ X ↔ ∀ a ∈ A, B1.conjAut a K ≤ X :=
  iSup₂_le_iff

theorem le_Kspan (A K : Subgroup (MulAut V)) : K ≤ Kspan A K := by
  have := conjAut_le_Kspan (K := K) (A.one_mem)
  rwa [conjAut_one] at this

theorem conjAut_Kspan_le {A K : Subgroup (MulAut V)} {b : MulAut V} (hb : b ∈ A) :
    B1.conjAut b (Kspan A K) ≤ Kspan A K := by
  rw [conjAut_eq_map, Kspan, Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha => ?_
  rw [← conjAut_eq_map, ← conjAut_mul]
  exact conjAut_le_Kspan (A.mul_mem hb ha)

theorem conjAut_Kspan {A K : Subgroup (MulAut V)} {b : MulAut V} (hb : b ∈ A) :
    B1.conjAut b (Kspan A K) = Kspan A K := by
  refine le_antisymm (conjAut_Kspan_le hb) ?_
  have h := conjAut_mono (a := b) (conjAut_Kspan_le (K := K) (A.inv_mem hb))
  rwa [B1.conjAut_conjAut_inv] at h

theorem Kspan_le {G A K : Subgroup (MulAut V)} (hK : K ≤ G) (hAG : A ≤ G) :
    Kspan A K ≤ G :=
  Kspan_le_iff.mpr fun _ ha => B1.conjAut_le (hAG ha) hK

theorem isComponentOf_conjAut_of_mem {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {a : MulAut V} (ha : a ∈ A) : IsComponentOf (B1.conjAut a K) G :=
  isComponentOf_conjAut hK (hAG ha)

theorem Kspan_perfect {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G) (hAG : A ≤ G) :
    ⁅Kspan A K, Kspan A K⁆ = Kspan A K := by
  refine le_antisymm (Subgroup.commutator_le_self _) (Kspan_le_iff.mpr fun a ha => ?_)
  have hp := perfect_of_isComponentOf (isComponentOf_conjAut_of_mem hK hAG ha)
  calc B1.conjAut a K = ⁅B1.conjAut a K, B1.conjAut a K⁆ := hp.symm
    _ ≤ ⁅Kspan A K, Kspan A K⁆ :=
      Subgroup.commutator_mono (conjAut_le_Kspan ha) (conjAut_le_Kspan ha)

theorem le_normalizer_Kspan (A K : Subgroup (MulAut V)) :
    A ≤ Subgroup.normalizer (Kspan A K : Set (MulAut V)) := fun _ ha =>
  mem_normalizer_iff_conjAut.mpr (conjAut_Kspan ha)

theorem commutator_Kspan_le (A K : Subgroup (MulAut V)) : ⁅Kspan A K, A⁆ ≤ Kspan A K := by
  rw [Subgroup.commutator_le]
  intro e he a ha
  have hn := conjAut_Kspan (K := K) ha
  have h1 : a * e⁻¹ * a⁻¹ ∈ Kspan A K := by
    rw [← hn, B1.mem_conjAut]
    simpa [mul_assoc] using (Kspan A K).inv_mem he
  have : ⁅e, a⁆ = e * (a * e⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact (Kspan A K).mul_mem he h1

variable [Finite V]

theorem Kspan_le_normalizer {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {a : MulAut V} (ha : a ∈ A) :
    Kspan A K ≤ Subgroup.normalizer (B1.conjAut a K : Set (MulAut V)) := by
  refine Kspan_le_iff.mpr fun b hb => ?_
  by_cases h : B1.conjAut b K = B1.conjAut a K
  · rw [h]
    exact Subgroup.le_normalizer
  · have hc := comp_commute (isComponentOf_conjAut_of_mem hK hAG hb)
      (isComponentOf_conjAut_of_mem hK hAG ha) h
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (Subgroup.centralizer_le_normalizer _)

theorem commutator_Kspan_eq {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {a₀ : MulAut V} (ha₀ : a₀ ∈ A)
    (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V))) : ⁅Kspan A K, A⁆ = Kspan A K := by
  refine le_antisymm (commutator_Kspan_le A K) ?_
  have hEnorm : Kspan A K ≤
      Subgroup.normalizer ((⁅Kspan A K, A⁆ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    Subgroup.normalizer_commutator_ge_left _ _
  have hAnorm : A ≤
      Subgroup.normalizer ((⁅Kspan A K, A⁆ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hK₃ : IsComponentOf (B1.conjAut a₀⁻¹ K) G :=
    isComponentOf_conjAut_of_mem hK hAG (A.inv_mem ha₀)
  have hne : K ≠ B1.conjAut a₀⁻¹ K := by
    intro h
    apply hn
    rw [mem_normalizer_iff_conjAut]
    exact conjAut_inv_eq_self_iff.mp h.symm
  have hcomm := comp_commute hK hK₃ hne
  have hKN : K ≤ ⁅Kspan A K, A⁆ := by
    calc K = ⁅K, K⁆ := (perfect_of_isComponentOf hK).symm
      _ ≤ ⁅Kspan A K, A⁆ := by
        rw [Subgroup.commutator_le]
        intro k hk l hl
        have hc : ⁅k, a₀⁻¹⁆ ∈ ⁅Kspan A K, A⁆ :=
          Subgroup.commutator_mem_commutator (le_Kspan A K hk) (A.inv_mem ha₀)
        have hk₃ : a₀⁻¹ * k⁻¹ * a₀ ∈ B1.conjAut a₀⁻¹ K := by
          rw [B1.mem_conjAut]
          simpa [mul_assoc] using K.inv_mem hk
        have hcomm' : (a₀⁻¹ * k⁻¹ * a₀) * l = l * (a₀⁻¹ * k⁻¹ * a₀) := by
          have := Subgroup.commutator_mem_commutator hl hk₃
          rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this.symm
        have h1 : ⁅⁅k, a₀⁻¹⁆, l⁆ = ⁅k, l⁆ := by
          have e1 : ⁅k, a₀⁻¹⁆ = k * (a₀⁻¹ * k⁻¹ * a₀) := by
            simp [commutatorElement_def, mul_assoc]
          rw [e1]
          set k₃ := a₀⁻¹ * k⁻¹ * a₀
          have e2 : k₃ * l * k₃⁻¹ = l := by rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
          calc ⁅k * k₃, l⁆ = k * (k₃ * l * k₃⁻¹) * k⁻¹ * l⁻¹ := by
                simp [commutatorElement_def, mul_assoc]
            _ = ⁅k, l⁆ := by rw [e2]; simp [commutatorElement_def, mul_assoc]
        have h2 : ⁅⁅k, a₀⁻¹⁆, l⁆ ∈ ⁅Kspan A K, A⁆ := by
          have hl' := hEnorm (le_Kspan A K hl)
          rw [Subgroup.mem_normalizer_iff] at hl'
          have h3 : l * (⁅k, a₀⁻¹⁆)⁻¹ * l⁻¹ ∈ ⁅Kspan A K, A⁆ :=
            (hl' _).mp (Subgroup.inv_mem _ hc)
          have e : ⁅⁅k, a₀⁻¹⁆, l⁆ = ⁅k, a₀⁻¹⁆ * (l * (⁅k, a₀⁻¹⁆)⁻¹ * l⁻¹) := by
            simp [commutatorElement_def, mul_assoc]
          rw [e]
          exact Subgroup.mul_mem _ hc h3
        rw [← h1]
        exact h2
  refine Kspan_le_iff.mpr fun b hb y hy => ?_
  rw [B1.mem_conjAut] at hy
  have hb' := hAnorm hb
  rw [Subgroup.mem_normalizer_iff] at hb'
  have hy' := (hb' (b⁻¹ * y * b)).mp (hKN hy)
  simpa [mul_assoc] using hy'

omit [Finite V] in
theorem conj_mem_centSub {W : Subgroup V} {g r : MulAut V} (hg : g ∈ stabSub W)
    (hr : r ∈ centSub W) : g * r * g⁻¹ ∈ centSub W := by
  rw [mem_centSub] at hr ⊢
  intro w hw
  have hw' : g⁻¹ w ∈ W := (mem_stabSub.mp ((stabSub W).inv_mem hg) w).mpr hw
  simp only [MulAut.mul_apply]
  rw [hr _ hw']
  exact MulAut.apply_inv_self _ g w

omit [Finite V] in
theorem not_conjAut_le_centSub {A K : Subgroup (MulAut V)} {W : Subgroup V} (hAW : A ≤ stabSub W)
    (hKW : ¬ K ≤ centSub W) {a : MulAut V} (ha : a ∈ A) : ¬ B1.conjAut a K ≤ centSub W := by
  intro h
  apply hKW
  intro k hk
  have hk' : a * k * a⁻¹ ∈ B1.conjAut a K := by
    rw [B1.mem_conjAut]
    simpa [mul_assoc] using hk
  have h1 := h hk'
  rw [mem_centSub] at h1 ⊢
  intro w hw
  have haw : a w ∈ W := (mem_stabSub.mp (hAW ha) w).mpr hw
  have h2 := h1 (a w) haw
  simp only [MulAut.mul_apply] at h2
  rw [MulAut.inv_apply_self] at h2
  exact a.injective h2

theorem Kspan_centSub_commutator {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) {W : Subgroup V} (hEW : Kspan A K ≤ stabSub W)
    (hKW : ∀ a ∈ A, ¬ B1.conjAut a K ≤ centSub W) :
    ⁅Kspan A K ⊓ centSub W, Kspan A K⁆ = ⊥ := by
  set E := Kspan A K with hE
  set R := E ⊓ centSub W with hR
  have hRn : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := by
    intro e he r hr
    exact ⟨E.mul_mem (E.mul_mem he hr.1) (E.inv_mem he), conj_mem_centSub (hEW he) hr.2⟩
  have hRK : ∀ a ∈ A, ⁅B1.conjAut a K, R⁆ = ⊥ := by
    intro a ha
    set Ki := B1.conjAut a K with hKi
    have hKic : IsComponentOf Ki G := isComponentOf_conjAut_of_mem hK hAG ha
    have hKiE : Ki ≤ E := conjAut_le_Kspan ha
    have hEKi : E ≤ Subgroup.normalizer (Ki : Set (MulAut V)) := Kspan_le_normalizer hK hAG ha
    have h1 : ⁅R, Ki⁆ ≤ R ⊓ Ki := by
      rw [Subgroup.commutator_le]
      intro r hr k hk
      constructor
      · have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact R.mul_mem hr (hRn k (hKiE hk) r⁻¹ (R.inv_mem hr))
      · have hrn := hEKi hr.1
        rw [Subgroup.mem_normalizer_iff] at hrn
        have h3 : r * k * r⁻¹ ∈ Ki := (hrn k).mp hk
        have e : ⁅r, k⁆ = (r * k * r⁻¹) * k⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact Ki.mul_mem h3 (Ki.inv_mem hk)
    have h2 : ⁅R ⊓ Ki, Ki⁆ = ⊥ := by
      have hnormal : ((R ⊓ Ki).subgroupOf Ki).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_right]
        intro h k hh hk
        exact ⟨hRn k (hKiE hk) h hh.1, Ki.mul_mem (Ki.mul_mem hk hh.2) (Ki.inv_mem hk)⟩
      have hproper : (R ⊓ Ki).subgroupOf Ki ≠ ⊤ := by
        intro htop
        apply hKW a ha
        rw [Subgroup.subgroupOf_eq_top] at htop
        exact fun x hx => (htop hx).1.2
      have hcen := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
        hKic.2.2 _ hproper
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro r hr k hk
      have hmem : (⟨r, hr.2⟩ : Ki) ∈ (R ⊓ Ki).subgroupOf Ki := hr
      have h4 := Subgroup.mem_center_iff.mp (hcen hmem) ⟨k, hk⟩
      have h5 : k * r = r * k := congrArg Subtype.val h4
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h5.symm
    have h3 : ⁅⁅R, Ki⁆, Ki⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (h1.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2))
    have h4 : ⁅⁅Ki, R⁆, Ki⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Ki R]
      exact h3
    have h5 := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h3
    rwa [perfect_of_isComponentOf hKic] at h5
  have hEcent : E ≤ Subgroup.centralizer (R : Set (MulAut V)) := by
    refine Kspan_le_iff.mpr fun a ha => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hRK a ha)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcent

theorem oTwoUpper_Kspan {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G) (hAG : A ≤ G) :
    oTwoUpper (Kspan A K) = Kspan A K :=
  B1Red.oTwoUpper_eq_of_perfect (Subgroup.isPerfect_iff.mpr (Kspan_perfect hK hAG))

theorem allTwoChiefFactorsCentral_Kspan {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) : AllTwoChiefFactorsCentral (Kspan A K) := by
  rintro X Y ⟨hYX, hXE, hXn, hYn, -, hX2⟩
  have hKa : ∀ a ∈ A, ⁅X, B1.conjAut a K⁆ ≤ Y := by
    intro a ha
    have hKic : IsComponentOf (B1.conjAut a K) G := isComponentOf_conjAut_of_mem hK hAG ha
    have hKiE : B1.conjAut a K ≤ Kspan A K := conjAut_le_Kspan ha
    have hEKi := Kspan_le_normalizer hK hAG ha
    have hNL : ∀ n ∈ X, ∀ l ∈ B1.conjAut a K, n * l * n⁻¹ ∈ B1.conjAut a K := by
      intro n hn l hl
      have := (Subgroup.mem_normalizer_iff.mp (hEKi (hXE hn)) l).mp hl
      exact this
    have hLN : ∀ l ∈ B1.conjAut a K, ∀ n ∈ X, l * n * l⁻¹ ∈ X := by
      intro l hl n hn
      have := (Subgroup.mem_normalizer_iff.mp (hXn (hKiE hl)) n).mp hn
      exact this
    by_cases hKX : B1.conjAut a K ≤ X
    · have hperf : Group.IsPerfect ↥(B1.conjAut a K) := ⟨hKic.2.2.1⟩
      have h1 : B1.conjAut a K ≤ oTwoUpper X := B1Red.perfect_le_oTwoUpper' hKX hperf
      have h2 : oTwoUpper X ≤ Y := oTwoUpper_le_of_pow_mem hX2
      refine le_trans ?_ (h1.trans h2)
      rw [Subgroup.commutator_le]
      intro n hn l hl
      have e : ⁅n, l⁆ = (n * l * n⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (B1.conjAut a K).mul_mem (hNL n hn l hl) ((B1.conjAut a K).inv_mem hl)
    · have hc := B1Red.commute_of_normal_not_le hKic.2.2 hNL hLN hKX
      rw [Subgroup.commutator_le]
      intro n hn l hl
      have : ⁅n, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc n hn l hl)
      rw [this]
      exact Y.one_mem
  let S : Subgroup (MulAut V) :=
    { carrier := {e | e ∈ Kspan A K ∧ ∀ x ∈ X, ⁅x, e⁆ ∈ Y}
      one_mem' := ⟨(Kspan A K).one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro e e' ⟨he, h1⟩ ⟨he', h2⟩
        refine ⟨(Kspan A K).mul_mem he he', fun x hx => ?_⟩
        have hn := (Subgroup.mem_normalizer_iff.mp (hYn he) (⁅x, e'⁆)).mp (h2 x hx)
        have eq : ⁅x, e * e'⁆ = ⁅x, e⁆ * (e * ⁅x, e'⁆ * e⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [eq]
        exact Y.mul_mem (h1 x hx) hn
      inv_mem' := by
        rintro e ⟨he, h1⟩
        refine ⟨(Kspan A K).inv_mem he, fun x hx => ?_⟩
        have hn := (Subgroup.mem_normalizer_iff.mp (hYn ((Kspan A K).inv_mem he))
          (⁅x, e⁆⁻¹)).mp (Y.inv_mem (h1 x hx))
        have eq : ⁅x, e⁻¹⁆ = e⁻¹ * ⁅x, e⁆⁻¹ * e⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [eq]
        exact hn }
  have hES : Kspan A K ≤ S := Kspan_le_iff.mpr fun a ha k hk =>
    ⟨conjAut_le_Kspan ha hk, fun x hx =>
      hKa a ha (Subgroup.commutator_mem_commutator hx hk)⟩
  rw [Subgroup.commutator_le]
  intro x hx e he
  exact (hES he).2 x hx

end Span

end CFSG.Quasithin.B15P4
