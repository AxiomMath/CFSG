module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def fSub15 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L X : Subgroup G) : Subgroup G :=
  X ⊔ v1Sub M V₀ V hV L

@[expose] noncomputable def ySub15 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L X : Subgroup G) (k : G) : Subgroup G :=
  conjSubgroup (fSub15 M V₀ V hV L X) k ⊓ M

@[expose] def Cond1512 (n : ℕ) (M V : Subgroup G) (k : G) : Prop :=
  ¬ conjSubgroup V k ≤ M ∧ ¬ V ≤ conjSubgroup M k ∧ E3.mQuot V (conjSubgroup M k) ≤ n ∧
    E3.mQuot (conjSubgroup V k) M ≤ n

theorem exists_cond1512 {n : ℕ} {M V₀ V : Subgroup G} (h : (calO n M V₀ V).Nonempty) :
    ∃ k : G, Cond1512 n M V k := by
  obtain ⟨X, g, -, ⟨h1, h2, -⟩, ⟨h3, h4, -⟩⟩ := h
  exact ⟨g, h1, h3, h2, h4⟩

theorem cond1512_inv {n : ℕ} {M V : Subgroup G} {k : G} (h : Cond1512 n M V k) :
    Cond1512 n M V k⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hle
    apply h2
    have := E3.conjSubgroup_mono_left k hle
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
  · intro hle
    apply h1
    have := E3.conjSubgroup_mono_left k hle
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
  · have h' := E3.mQuot_conjSubgroup (conjSubgroup V k) M k⁻¹
    rw [conjSubgroup_conjSubgroup_inv] at h'
    rw [h']
    exact h4
  · have h' := E3.mQuot_conjSubgroup V (conjSubgroup M k) k⁻¹
    rw [conjSubgroup_conjSubgroup_inv] at h'
    rw [h']
    exact h3

private lemma s15_TwelveA_imgTil_mono {V₀ V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAB : A ≤ B) : imgTil V₀ V hV A ≤ imgTil V₀ V hV B := by
  unfold imgTil intSub
  exact Subgroup.map_mono fun x hx => hAB hx

private lemma s15_TwelveA_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

private lemma s15_TwelveA_conjSubgroup_conjSubgroup_of_mem_normalizer {F : Subgroup G}
    {g c : G} (hc : g * c * g⁻¹ ∈ normalizer (F : Set G)) :
    conjSubgroup (conjSubgroup F g) c = conjSubgroup F g := by
  have hb : conjSubgroup F (g * c * g⁻¹) = F :=
    conjSubgroup_eq_iff_mem_normalizer.2 hc
  calc conjSubgroup (conjSubgroup F g) c
      = conjSubgroup F (g * c) := conjSubgroup_conjSubgroup F g c
    _ = conjSubgroup F ((g * c * g⁻¹) * g) := by
          congr 1
          group
    _ = conjSubgroup (conjSubgroup F (g * c * g⁻¹)) g :=
          (conjSubgroup_conjSubgroup F (g * c * g⁻¹) g).symm
    _ = conjSubgroup F g := by rw [hb]

private lemma s15_TwelveA_fSub_conj_inf_V_eq_bot (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {k : G}
    (hVg : ¬ V ≤ conjSubgroup D.M k) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) :
    conjSubgroup (fSub15 D.M V₀ V hV L X) k ⊓ V = ⊥ := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hVg' : ¬ V ≤ conjSubgroup D.M (m * k) := by
    rw [← conjSubgroup_conjSubgroup D.M m k, s15_Tools_conjSubgroup_M D hm]
    exact hVg
  have h1 := s15_Glue_inf_V_eq_bot D h hV (g := m * k) hVg'
  have hV1m : conjSubgroup (v1Sub D.M V₀ V hV L) m = v1Sub D.M V₀ V hV L :=
    s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV hm
  have heq : conjSubgroup (fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m)) k =
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (m * k) := by
    unfold fSub15
    rw [s15_TwelveA_conjSubgroup_sup, s15_TwelveA_conjSubgroup_sup, conjSubgroup_conjSubgroup,
      ← conjSubgroup_conjSubgroup (v1Sub D.M V₀ V hV L) m k, hV1m]
  rw [heq]
  exact h1

private lemma s15_TwelveA_rk_map_le {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (H : Subgroup A) : rk ↥(H.map f) ≤ rk ↥H := by
  unfold rk
  exact padicValNat_two_le_of_dvd (Nat.card_pos (α := ↥H)).ne' (Subgroup.card_map_dvd (H := H) f)

private lemma s15_TwelveA_imgTil_wConj_injOn (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) :
    Set.InjOn (fun X => imgTil (v1Sub D.M V₀ V hV L) V hV X) (wConj D.M V₀ V hV L) := by
  have himgset : (fun X => imgTil (v1Sub D.M V₀ V hV L) V hV X) '' wConj D.M V₀ V hV L =
      wStarConj D.M V₀ V hV L := by
    ext U
    constructor
    · rintro ⟨X, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  refine (Set.ncard_image_iff (Set.toFinite _)).1 ?_
  rw [himgset, ncard_wStarConj D h hV, ncard_wConj D h hV]

private lemma s15_TwelveA_commute_of_mem_normalizer (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {k : G}
    (hVg : ¬ V ≤ conjSubgroup D.M k) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    {y a : G} (hy : y ∈ ySub15 D.M V₀ V hV L X k) (haV : a ∈ V)
    (haM : a ∈ conjSubgroup D.M k)
    (hN : k * a * k⁻¹ ∈ normalizer (fSub15 D.M V₀ V hV L X : Set G)) : y * a = a * y := by
  unfold ySub15 at hy
  obtain ⟨hyF, hyM⟩ := Subgroup.mem_inf.1 hy
  have ha'M : k * a * k⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 haM
  have ha'F' : k * a⁻¹ * k⁻¹ ∈ normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
    have := (normalizer (fSub15 D.M V₀ V hV L X : Set G)).inv_mem hN
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have hFk : conjSubgroup (conjSubgroup (fSub15 D.M V₀ V hV L X) k) a⁻¹ =
      conjSubgroup (fSub15 D.M V₀ V hV L X) k :=
    s15_TwelveA_conjSubgroup_conjSubgroup_of_mem_normalizer ha'F'
  have hay : a * y⁻¹ * a⁻¹ ∈ conjSubgroup (fSub15 D.M V₀ V hV L X) k := by
    rw [← hFk]
    exact (mem_conjSubgroup_iff (A := conjSubgroup (fSub15 D.M V₀ V hV L X) k)
      (g := a⁻¹) (x := a * y⁻¹ * a⁻¹)).2 (by
        rw [show a⁻¹ * (a * y⁻¹ * a⁻¹) * (a⁻¹)⁻¹ = y⁻¹ by group]
        exact (conjSubgroup (fSub15 D.M V₀ V hV L X) k).inv_mem hyF)
  have hcomm_mem : ⁅y, a⁆ ∈ conjSubgroup (fSub15 D.M V₀ V hV L X) k := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      (conjSubgroup (fSub15 D.M V₀ V hV L X) k).mul_mem hyF hay
  have hcomm_V : ⁅y, a⁆ ∈ V := by
    have hyaV : y * a * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (h.hyp151.hyp125.pairFacts.le_normalizer hyM) a).1 haV
    rw [commutatorElement_def]
    simpa only [mul_assoc] using V.mul_mem hyaV (V.inv_mem haV)
  have hbot := s15_TwelveA_fSub_conj_inf_V_eq_bot D h hV hVg hX
  have h1 : ⁅y, a⁆ = 1 := by
    have := Subgroup.mem_inf.2 ⟨hcomm_mem, hcomm_V⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  rw [commutatorElement_def] at h1
  calc y * a = (y * a * y⁻¹ * a⁻¹) * (a * y) := by group
    _ = a * y := by rw [h1, one_mul]

private lemma s15_TwelveA_commute_of_four_le_s (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {n : ℕ} {k : G} (hk : Cond1512 n D.M V k)
    (hs : 4 ≤ s15 D.M V₀ V hV L) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    {y a : G} (hy : y ∈ ySub15 D.M V₀ V hV L X k) (haV : a ∈ V)
    (haM : a ∈ conjSubgroup D.M k) : y * a = a * y := by
  by_contra hne
  have hw1 : ⁅y, a⁆ ≠ 1 := by
    intro hw
    apply hne
    rw [commutatorElement_def] at hw
    calc y * a = (y * a * y⁻¹ * a⁻¹) * (a * y) := by group
      _ = a * y := by rw [hw, one_mul]
  set w : G := ⁅y, a⁆ with hwdef
  set a' : G := k * a * k⁻¹ with ha'def
  have ha'M : a' ∈ D.M := mem_conjSubgroup_iff.1 haM
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hXleV : X ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hX
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hFXleV : fSub15 D.M V₀ V hV L X ≤ V := by
    unfold fSub15
    exact sup_le hXleV hV1V
  set X' : Subgroup G := conjSubgroup X a'⁻¹ with hX'def
  have hX'mem : X' ∈ wConj D.M V₀ V hV L := by
    obtain ⟨m, hm, rfl⟩ := hX
    refine ⟨m * a'⁻¹, D.M.mul_mem hm (D.M.inv_mem ha'M), ?_⟩
    rw [hX'def, conjSubgroup_conjSubgroup]
  have hX'leV : X' ≤ V := by
    obtain ⟨m', hm', hX'eq⟩ := hX'mem
    rw [hX'eq]
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm'
  have hFX'leV : fSub15 D.M V₀ V hV L X' ≤ V := by
    unfold fSub15
    exact sup_le hX'leV hV1V
  have hF' : fSub15 D.M V₀ V hV L X' = conjSubgroup (fSub15 D.M V₀ V hV L X) a'⁻¹ := by
    rw [hX'def]
    unfold fSub15
    rw [s15_TwelveA_conjSubgroup_sup,
      s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV (D.M.inv_mem ha'M)]
  have hFk' : conjSubgroup (conjSubgroup (fSub15 D.M V₀ V hV L X) k) a⁻¹ =
      conjSubgroup (fSub15 D.M V₀ V hV L X') k := by
    have hka : k * a⁻¹ = a'⁻¹ * k := by rw [ha'def]; group
    rw [conjSubgroup_conjSubgroup, hka, ← conjSubgroup_conjSubgroup (fSub15 D.M V₀ V hV L X) a'⁻¹ k,
      hF']
  obtain ⟨hyF, hyM⟩ := Subgroup.mem_inf.1 (by simpa [ySub15] using hy)
  have hay : a * y⁻¹ * a⁻¹ ∈ conjSubgroup (fSub15 D.M V₀ V hV L X') k := by
    rw [← hFk']
    exact (mem_conjSubgroup_iff (A := conjSubgroup (fSub15 D.M V₀ V hV L X) k)
      (g := a⁻¹) (x := a * y⁻¹ * a⁻¹)).2 (by
        rw [show a⁻¹ * (a * y⁻¹ * a⁻¹) * (a⁻¹)⁻¹ = y⁻¹ by group]
        exact (conjSubgroup (fSub15 D.M V₀ V hV L X) k).inv_mem hyF)
  have hwmem : w ∈ conjSubgroup (fSub15 D.M V₀ V hV L X) k ⊔
      conjSubgroup (fSub15 D.M V₀ V hV L X') k := by
    rw [hwdef, commutatorElement_def]
    simpa only [mul_assoc] using Subgroup.mul_mem_sup hyF hay
  have hw'mem : k * w * k⁻¹ ∈ fSub15 D.M V₀ V hV L X ⊔ fSub15 D.M V₀ V hV L X' := by
    have hmem : k * w * k⁻¹ ∈ conjSubgroup (conjSubgroup (fSub15 D.M V₀ V hV L X) k ⊔
        conjSubgroup (fSub15 D.M V₀ V hV L X') k) k⁻¹ :=
      (mem_conjSubgroup_iff (A := conjSubgroup (fSub15 D.M V₀ V hV L X) k ⊔
        conjSubgroup (fSub15 D.M V₀ V hV L X') k) (g := k⁻¹) (x := k * w * k⁻¹)).2 (by
          rw [show k⁻¹ * (k * w * k⁻¹) * (k⁻¹)⁻¹ = w by group]
          exact hwmem)
    rwa [s15_TwelveA_conjSubgroup_sup, E3.conjSubgroup_conj_inv,
      E3.conjSubgroup_conj_inv] at hmem
  have hw'1 : k * w * k⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    calc w = k⁻¹ * (k * w * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have hw'V : k * w * k⁻¹ ∈ V := (sup_le hFXleV hFX'leV) hw'mem
  have hw'2 : ∃ m : ℕ, (k * w * k⁻¹) ^ (2 ^ m) = 1 :=
    ⟨1, by simpa using hV.2 (k * w * k⁻¹) hw'V⟩
  have hTcard : 2 ≤ (wConj D.M V₀ V hV L \ {X, X'}).ncard := by
    have hle := Set.le_ncard_sdiff ({X, X'} : Set (Subgroup G)) (wConj D.M V₀ V hV L)
      (Set.toFinite _)
    have hpair : ({X, X'} : Set (Subgroup G)).ncard ≤ 2 := by
      have := Set.ncard_insert_le X ({X'} : Set (Subgroup G))
      rw [Set.ncard_singleton] at this
      simpa using this
    have hcard := ncard_wConj D h.hyp151 hV
    omega
  obtain ⟨Z1, Z2, hZ1, hZ2, hZ12⟩ :=
    (Set.one_lt_ncard_iff (s := wConj D.M V₀ V hV L \ {X, X'}) (Set.toFinite _)).1 (by omega)
  rw [Set.mem_sdiff] at hZ1 hZ2
  obtain ⟨hZ1W, hZ1not⟩ := hZ1
  obtain ⟨hZ2W, hZ2not⟩ := hZ2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hZ1not hZ2not
  obtain ⟨hz1M, hz1mem, hZ1eq⟩ := hZ1W
  obtain ⟨hz2M, hz2mem, hZ2eq⟩ := hZ2W
  have hz12 : conjSubgroup (wSub V₀ V hV L) hz1M ≠
      conjSubgroup (wSub V₀ V hV L) hz2M := by
    intro heq
    exact hZ12 (hZ1eq.trans (heq.trans hZ2eq.symm))
  have hw'S : k * w * k⁻¹ ∈ v1Sub D.M V₀ V hV L ⊔
      ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz1M ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz2M}, X := by
    have hXS : X ≤ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz1M ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz2M}, X :=
      le_iSup₂_of_le X ⟨hX, fun h => hZ1not.1 (hZ1eq.trans h.symm),
        fun h => hZ2not.1 (hZ2eq.trans h.symm)⟩ le_rfl
    have hX'S : X' ≤ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz1M ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) hz2M}, X :=
      le_iSup₂_of_le X' ⟨hX'mem, fun h => hZ1not.2 (hZ1eq.trans h.symm),
        fun h => hZ2not.2 (hZ2eq.trans h.symm)⟩ le_rfl
    have hFX : fSub15 D.M V₀ V hV L X ≤
        v1Sub D.M V₀ V hV L ⊔ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) hz1M ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) hz2M}, X := by
      unfold fSub15
      exact sup_le (hXS.trans le_sup_right) le_sup_left
    have hFX' : fSub15 D.M V₀ V hV L X' ≤
        v1Sub D.M V₀ V hV L ⊔ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) hz1M ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) hz2M}, X := by
      unfold fSub15
      exact sup_le (hX'S.trans le_sup_right) le_sup_left
    exact (sup_le hFX hFX') hw'mem
  have hgood' := h.unique₂ hz1M hz1mem hz2M hz2mem hz12 (k * w * k⁻¹) hw'S hw'1
  have hcentw' : centralizer ({k * w * k⁻¹} : Set G) ≤ D.M :=
    (centralizer_le_of_uniqueMax D.maxLocal hw'1 hw'2 hgood').1
  have hwV : w ∈ V := by
    rw [hwdef, commutatorElement_def]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1
      (h.hyp151.hyp125.pairFacts.le_normalizer hyM) a).1 haV) (V.inv_mem haV)
  have hVcent : V ≤ centralizer ({w} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (B2F.isElemAbelian_comm hV hv hwV).symm
  have hcent_le : centralizer ({w} : Set G) ≤ conjSubgroup D.M k := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    apply hcentw'
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    have hxw : w * x = x * w := (Subgroup.mem_centralizer_iff.1 hx) w (by simp)
    calc (k * w * k⁻¹) * (k * x * k⁻¹) = k * (w * x) * k⁻¹ := by group
      _ = k * (x * w) * k⁻¹ := by rw [hxw]
      _ = (k * x * k⁻¹) * (k * w * k⁻¹) := by group
  exact hk.2.1 (hVcent.trans hcent_le)

private lemma s15_TwelveA_relIndex_inf_normalizer_le (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {k : G} {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) :
    ((conjSubgroup V k⁻¹ ⊓ D.M) ⊓ normalizer (X : Set G)).relIndex
      (conjSubgroup V k⁻¹ ⊓ D.M) ≤ s15 D.M V₀ V hV L := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hEM : conjSubgroup (conjSubgroup V k⁻¹ ⊓ D.M) m⁻¹ ≤ D.M := by
    calc conjSubgroup (conjSubgroup V k⁻¹ ⊓ D.M) m⁻¹ ≤ conjSubgroup D.M m⁻¹ :=
          E3.conjSubgroup_mono_left m⁻¹ inf_le_right
      _ = D.M := s15_Tools_conjSubgroup_M D (D.M.inv_mem hm)
  have h1 := s15_Glue_relIndex_inf_normalizer_le D h.hyp151 hV
    (E := conjSubgroup (conjSubgroup V k⁻¹ ⊓ D.M) m⁻¹) hEM
  have hNX : conjSubgroup (normalizer (conjSubgroup (wSub V₀ V hV L) m : Set G)) m⁻¹ =
      normalizer (wSub V₀ V hV L : Set G) := by
    rw [E3.conjSubgroup_normalizer]
    congr 1
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hEm : conjSubgroup (conjSubgroup V k⁻¹ ⊓ D.M) m⁻¹ ⊓
      normalizer (wSub V₀ V hV L : Set G) =
      conjSubgroup ((conjSubgroup V k⁻¹ ⊓ D.M) ⊓
        normalizer (conjSubgroup (wSub V₀ V hV L) m : Set G)) m⁻¹ := by
    conv_lhs => rw [E3.conjSubgroup_inf]
    conv_rhs => rw [E3.conjSubgroup_inf, E3.conjSubgroup_inf]
    rw [hNX]
  rw [hEm, E3.relIndex_conjSubgroup] at h1
  exact h1



theorem s15_Twelve_rank_bound (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {n : ℕ} {k : G} (hk : Cond1512 n D.M V k) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) :
    E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) ≤ n + 1 ∧
      ((4 ≤ s15 D.M V₀ V hV L ∨
          conjSubgroup V k⁻¹ ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L X : Set G)) →
        E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) ≤ n) := by
  set Y : Subgroup G := ySub15 D.M V₀ V hV L X k with hYdef
  set P : Subgroup G := V ⊓ conjSubgroup D.M k with hPdef
  have hPleV : P ≤ V := by rw [hPdef]; exact inf_le_left
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hP : E3.mQuot V P ≤ n := by
    have h3 := hk.2.2.1
    rw [hPdef]
    unfold E3.mQuot at h3 ⊢
    rw [Subgroup.inf_relIndex_left]
    exact h3
  have hCeq : E3.mQuot V (centralizer (Y : Set G)) =
      E3.mQuot V (V ⊓ centralizer (Y : Set G)) := by
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left]
  have hgood : (4 ≤ s15 D.M V₀ V hV L ∨ conjSubgroup V k⁻¹ ⊓ D.M ≤
      normalizer (fSub15 D.M V₀ V hV L X : Set G)) →
      E3.mQuot V (centralizer (Y : Set G)) ≤ n := by
    intro hcases
    rw [hCeq]
    have hPC : P ≤ V ⊓ centralizer (Y : Set G) := by
      refine le_inf hPleV ?_
      intro a ha
      rw [hPdef] at ha
      obtain ⟨haV, haM⟩ := Subgroup.mem_inf.1 ha
      have ha'M : k * a * k⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 haM
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hYdef] at hy
      unfold ySub15 at hy
      rcases hcases with h4 | hR
      · exact s15_TwelveA_commute_of_four_le_s D h hV hk h4 hX hy haV haM
      · have ha'R : k * a * k⁻¹ ∈ conjSubgroup V k⁻¹ ⊓ D.M := by
          refine Subgroup.mem_inf.2 ⟨?_, ha'M⟩
          exact mem_conjSubgroup_iff.2 (by
            rw [show k⁻¹ * (k * a * k⁻¹) * (k⁻¹)⁻¹ = a by group]
            exact haV)
        exact s15_TwelveA_commute_of_mem_normalizer D h hV hk.2.1 hX hy haV haM (hR ha'R)
    have := E3.mQuot_mono (V := V) hPC
    exact le_trans this hP
  have hbound : E3.mQuot V (centralizer (Y : Set G)) ≤ n + 1 := by
    by_cases h4 : 4 ≤ s15 D.M V₀ V hV L
    · exact le_trans (hgood (Or.inl h4)) (Nat.le_succ n)
    · rw [hCeq]
      have hle3 : s15 D.M V₀ V hV L ≤ 3 := by omega
      set R : Subgroup G := conjSubgroup V k⁻¹ ⊓ D.M with hR
      set R₀ : Subgroup G := R ⊓ normalizer (X : Set G) with hR₀
      have hR2 : IsPGroup 2 R := by
        rw [hR]
        exact (E3.isElemAbelian_conjSubgroup hV k⁻¹).isPGroup.to_le inf_le_left
      have hidx : R₀.relIndex R ≤ s15 D.M V₀ V hV L := by
        rw [hR₀]
        exact s15_TwelveA_relIndex_inf_normalizer_le D h hV hX
      have hmqR : E3.mQuot R R₀ ≤ 1 := by
        have hpow : 2 ^ E3.mQuot R R₀ ≤ 3 := by
          rw [← E3.relIndex_eq_two_pow hR2 R₀]
          exact le_trans hidx hle3
        by_contra hcon
        have h2 : 2 ≤ E3.mQuot R R₀ := by omega
        have h4' : 4 ≤ 2 ^ E3.mQuot R R₀ := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ E3.mQuot R R₀ := Nat.pow_le_pow_right (by norm_num) h2
        omega
      have hP_eq : P = conjSubgroup R k := by
        rw [hPdef, hR, E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj]
      have hP₀C : conjSubgroup R₀ k ≤ V ⊓ centralizer (Y : Set G) := by
        intro a ha
        obtain ⟨r, hr, harfl⟩ := ha
        have hrR : r ∈ R := (Subgroup.mem_inf.1 hr).1
        have hrN : r ∈ normalizer (X : Set G) := (Subgroup.mem_inf.1 hr).2
        have hrM : r ∈ D.M := (Subgroup.mem_inf.1 hrR).2
        have haV : (MulAut.conj k⁻¹) r ∈ V := by
          have h := mem_conjSubgroup_iff.1 (Subgroup.mem_inf.1 hrR).1
          simpa using h
        have haM : (MulAut.conj k⁻¹) r ∈ conjSubgroup D.M k :=
          Subgroup.mem_map.mpr ⟨r, hrM, rfl⟩
        have hrF : r ∈ normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
          have hXr : conjSubgroup X r = X := conjSubgroup_eq_iff_mem_normalizer.2 hrN
          have hV1r : conjSubgroup (v1Sub D.M V₀ V hV L) r = v1Sub D.M V₀ V hV L :=
            s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV hrM
          refine conjSubgroup_eq_iff_mem_normalizer.1 ?_
          unfold fSub15
          rw [s15_TwelveA_conjSubgroup_sup, hXr, hV1r]
        have hN : k * (MulEquiv.toMonoidHom (MulAut.conj k⁻¹)) r * k⁻¹ ∈
            normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
          change k * (MulAut.conj k⁻¹) r * k⁻¹ ∈
            normalizer (fSub15 D.M V₀ V hV L X : Set G)
          rw [show k * (MulAut.conj k⁻¹) r * k⁻¹ = r by rw [MulAut.conj_apply]; group]
          exact hrF
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rwa [← harfl]
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [hYdef] at hy
          unfold ySub15 at hy
          rw [← harfl]
          exact s15_TwelveA_commute_of_mem_normalizer D h hV hk.2.1 hX hy haV haM hN
      have hR₀P : conjSubgroup R₀ k ≤ P := by
        rw [hP_eq]
        exact E3.conjSubgroup_mono_left k (by rw [hR₀]; exact inf_le_left)
      have hstep : E3.mQuot P (P ⊓ (V ⊓ centralizer (Y : Set G))) ≤ 1 := by
        have hle4 : conjSubgroup R₀ k ≤ P ⊓ (V ⊓ centralizer (Y : Set G)) :=
          le_inf hR₀P hP₀C
        have hmono : E3.mQuot P (P ⊓ (V ⊓ centralizer (Y : Set G))) ≤
            E3.mQuot P (conjSubgroup R₀ k) := E3.mQuot_mono hle4
        have hPeq : E3.mQuot P (conjSubgroup R₀ k) = E3.mQuot R R₀ := by
          rw [hP_eq, E3.mQuot_conjSubgroup]
        rw [hPeq] at hmono
        exact le_trans hmono hmqR
      have hmain := s15_Tools_mQuot_le_add (B := V) (D := P)
        (C := V ⊓ centralizer (Y : Set G)) hPleV
      omega
  exact ⟨hbound, fun hcases => hgood hcases⟩

theorem s15_Twelve_moved_rank (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {y : G}
    (hy : y ∈ D.M) {Z : Subgroup G} (hZ : Z ∈ wConj D.M V₀ V hV L)
    (hmove : conjSubgroup (fSub15 D.M V₀ V hV L Z) y ≠ fSub15 D.M V₀ V hV L Z) :
    gamma15 D.M V₀ V hV L ≤ E3.mQuot V (centralizer ({y} : Set G)) := by
  have hZV : Z ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hZ
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hyN : y ∈ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer hy
  have hV1y : conjSubgroup (v1Sub D.M V₀ V hV L) y = v1Sub D.M V₀ V hV L :=
    s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hy
  obtain ⟨m, hm, hZeq⟩ := hZ
  have hFZeq : fSub15 D.M V₀ V hV L Z =
      conjSubgroup (fSub15 D.M V₀ V hV L (wSub V₀ V hV L)) m := by
    rw [hZeq]
    unfold fSub15
    rw [s15_TwelveA_conjSubgroup_sup, s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hm]
  have hxn : m * y * m⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have hnormW : m * y * m⁻¹ ∈
        normalizer ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) := by
      have hmem' : m * y * m⁻¹ ∈ D.M ⊓
          normalizer ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) := by
        rwa [inf_normalizer_wSub_sup_v1Sub_eq_nBar D h hV]
      exact (Subgroup.mem_inf.1 hmem').2
    apply hmove
    rw [hFZeq]
    refine conjSubgroup_eq_iff_mem_normalizer.2 ?_
    rw [← E3.conjSubgroup_normalizer]
    exact mem_conjSubgroup_iff.2 hnormW
  let c : MulAut (IntMod V hV) := convI hV ⟨y, hyN⟩
  let φ : IntMod V hV →* IntMod V hV :=
    { toFun := fun v => v * c v
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        rw [mul_mul_mul_comm] }
  have hc_val : ∀ v : IntMod V hV, (c v).val = y * v.val * y⁻¹ := by
    intro v
    exact convI_apply_val hV ⟨y, hyN⟩ v
  have hφ_val : ∀ v : IntMod V hV, (φ v).val = v.val * (y * v.val * y⁻¹) := by
    intro v
    show (v * c v).val = _
    rw [IntMod.val_mul, hc_val v]
  have hvalrange : (valHom V hV).range = V := by
    ext g
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.val_mem
    · intro hg
      exact ⟨⟨g, hg⟩, rfl⟩
  have hker_φ : φ.ker = (centralizer ({y} : Set G) ⊓ V).comap (valHom V hV) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_inf]
    constructor
    · intro hv
      have hv1 : v.val * (y * v.val * y⁻¹) = 1 := by
        have := congrArg IntMod.val hv
        rwa [hφ_val v, IntMod.val_one] at this
      have hcomm : y * v.val = v.val * y := by
        have h3 : v.val * y * v.val = y := by
          have h := congrArg (fun t => t * y) hv1
          rw [one_mul] at h
          rwa [show v.val * (y * v.val * y⁻¹) * y = v.val * y * v.val by group] at h
        have hv2 : v.val * v.val = 1 := by
          simpa [pow_two] using hV.2 v.val v.val_mem
        have hA : (v.val * y * v.val) * v.val = y * v.val := by rw [h3]
        have hB : (v.val * y * v.val) * v.val = v.val * y := by
          calc (v.val * y * v.val) * v.val = v.val * y * (v.val * v.val) := by group
            _ = v.val * y := by rw [hv2, mul_one]
        rw [hA] at hB
        exact hB
      refine ⟨?_, v.val_mem⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm
    · rintro ⟨hvcent, -⟩
      apply IntMod.val_injective
      rw [hφ_val, IntMod.val_one]
      have hcomm : y * v.val = v.val * y :=
        (Subgroup.mem_centralizer_iff.1 hvcent) y (by simp)
      calc v.val * (y * v.val * y⁻¹) = v.val * (v.val * y * y⁻¹) := by rw [hcomm]
        _ = v.val * v.val := by group
        _ = 1 := by simpa [pow_two] using hV.2 v.val v.val_mem
  have hmq_φ : E3.mQuot V (centralizer ({y} : Set G)) = rk ↥φ.range := by
    unfold E3.mQuot rk
    have h1 : (centralizer ({y} : Set G)).relIndex V = (φ.ker).index := by
      rw [← Subgroup.inf_relIndex_left (H := V) (K := centralizer ({y} : Set G))]
      have h2 : ((centralizer ({y} : Set G) ⊓ V).comap (valHom V hV)).index =
          (centralizer ({y} : Set G) ⊓ V).relIndex V := by
        rw [Subgroup.index_comap, hvalrange]
      rw [inf_comm, ← h2, ← hker_φ]
    rw [h1, Subgroup.index_ker]
  let incl : ↥Z →* IntMod V hV :=
    { toFun := fun z => ⟨z.1, hZV z.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let ψ : ↥Z →* Vtil (v1Sub D.M V₀ V hV L) V hV :=
    (mkTil (v1Sub D.M V₀ V hV L) V hV).comp (φ.comp incl)
  have hker_ψ : ψ.ker = (Z ⊓ v1Sub D.M V₀ V hV L).subgroupOf Z := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hz
      have hφzV1 : (φ (incl z)).val ∈ v1Sub D.M V₀ V hV L := by
        have hz' : mkTil (v1Sub D.M V₀ V hV L) V hV (φ (incl z)) = 1 := hz
        rw [← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV)] at hz'
        have := (mkTil_eq_iff (v1Sub D.M V₀ V hV L) V hV _ 1).1 hz'
        simpa using this
      have hxM : m * y * m⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hm hy) (D.M.inv_mem hm)
      have hwW : m * z.val * m⁻¹ ∈ wSub V₀ V hV L :=
        mem_conjSubgroup_iff.1 (hZeq ▸ z.2)
      have hwWV : m * z.val * m⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
        Subgroup.mem_sup_left hwW
      have ha2 : z.val * z.val = 1 := by
        simpa [pow_two] using hV.2 z.val (hZV z.2)
      have hcomm_eq : y * z.val * y⁻¹ * z.val⁻¹ = z.val * (y * z.val * y⁻¹) := by
        have hyaV : y * z.val * y⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (h.hyp125.pairFacts.le_normalizer hy) z.val).1 (hZV z.2)
        have hcommab : z.val * (y * z.val * y⁻¹) = (y * z.val * y⁻¹) * z.val :=
          B2F.isElemAbelian_comm hV (hZV z.2) hyaV
        have hinv : z.val⁻¹ = z.val := inv_eq_of_mul_eq_one_left ha2
        rw [hinv, hcommab]
      have hcommV1 : (m * y * m⁻¹) * (m * z.val * m⁻¹) * (m * y * m⁻¹)⁻¹ *
          (m * z.val * m⁻¹)⁻¹ ∈ v1Sub D.M V₀ V hV L := by
        have hconj : (m * y * m⁻¹) * (m * z.val * m⁻¹) * (m * y * m⁻¹)⁻¹ *
            (m * z.val * m⁻¹)⁻¹ = m * (φ (incl z)).val * m⁻¹ := by
          rw [hφ_val (incl z)]
          change (m * y * m⁻¹) * (m * z.val * m⁻¹) * (m * y * m⁻¹)⁻¹ *
              (m * z.val * m⁻¹)⁻¹ = m * (z.val * (y * z.val * y⁻¹)) * m⁻¹
          rw [← hcomm_eq]
          group
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.1 (s15_Infra_le_normalizer_v1Sub h.hyp125 hV hm)
          (φ (incl z)).val).1 hφzV1
      have hwV1 : m * z.val * m⁻¹ ∈ v1Sub D.M V₀ V hV L :=
        mem_v1Sub_of_commutator_mem D h hV hxM hxn hwWV hcommV1
      have hzV1 : z.val ∈ v1Sub D.M V₀ V hV L := by
        have := mem_conjSubgroup_iff.2 hwV1
        rwa [s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hm] at this
      exact ⟨z.2, hzV1⟩
    · rintro ⟨-, hzV1⟩
      change mkTil (v1Sub D.M V₀ V hV L) V hV (φ (incl z)) = 1
      rw [← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV), mkTil_eq_iff]
      have hyaV1 : y * z.val * y⁻¹ ∈ v1Sub D.M V₀ V hV L :=
        (Subgroup.mem_normalizer_iff.1 (s15_Infra_le_normalizer_v1Sub h.hyp125 hV hy) z.val).1
          hzV1
      have hprod : (φ (incl z)).val ∈ v1Sub D.M V₀ V hV L := by
        rw [hφ_val]
        exact (v1Sub D.M V₀ V hV L).mul_mem hzV1 hyaV1
      simpa using hprod
  have hψrk : E3.mQuot Z (Z ⊓ v1Sub D.M V₀ V hV L) = rk ↥ψ.range := by
    unfold E3.mQuot rk
    have h1 : (Z ⊓ v1Sub D.M V₀ V hV L).relIndex Z = (ψ.ker).index := by
      show ((Z ⊓ v1Sub D.M V₀ V hV L).subgroupOf Z).index = (ψ.ker).index
      rw [← hker_ψ]
    rw [h1, Subgroup.index_ker]
  have hZstar : imgTil (v1Sub D.M V₀ V hV L) V hV Z ∈ wStarConj D.M V₀ V hV L := by
    exact ⟨m, hm, by rw [hZeq]⟩
  have hZrk : E3.mQuot Z (Z ⊓ v1Sub D.M V₀ V hV L) = gamma15 D.M V₀ V hV L := by
    have hInf : Z ⊓ v1Sub D.M V₀ V hV L ≤ Z := inf_le_left
    have h1 := E3.mQuot_add (V := Z) (U := ⊥) (U' := Z ⊓ v1Sub D.M V₀ V hV L) bot_le hInf
    have h2 := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V Z hV hZV
    have h3 := s15_FiveTen_mQuot_bot_eq_rk Z
    have h4 := s15_FiveTen_mQuot_bot_eq_rk (Z ⊓ v1Sub D.M V₀ V hV L)
    have h5 := s15_Two_rk_wStarConj h hV hZstar
    rw [h3, h4] at h1
    rw [h5] at h2
    have h2' : rk ↥Z = gamma15 D.M V₀ V hV L + rk ↥(Z ⊓ v1Sub D.M V₀ V hV L) := h2
    omega
  have hψle : rk ↥ψ.range ≤ rk ↥φ.range := by
    have hle : ψ.range ≤ (φ.range).map (mkTil (v1Sub D.M V₀ V hV L) V hV) := by
      rintro _ ⟨z, rfl⟩
      refine Subgroup.mem_map.mpr ⟨φ (incl z), ?_, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨incl z, rfl⟩
    calc rk ↥ψ.range ≤ rk ↥((φ.range).map (mkTil (v1Sub D.M V₀ V hV L) V hV)) :=
          rk_mono hle
      _ ≤ rk ↥φ.range := s15_TwelveA_rk_map_le (mkTil (v1Sub D.M V₀ V hV L) V hV) φ.range
  calc gamma15 D.M V₀ V hV L
      = E3.mQuot Z (Z ⊓ v1Sub D.M V₀ V hV L) := hZrk.symm
    _ = rk ↥ψ.range := hψrk
    _ ≤ rk ↥φ.range := hψle
    _ = E3.mQuot V (centralizer ({y} : Set G)) := hmq_φ.symm

theorem s15_Twelve_fSub_inj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hγ : 0 < gamma15 D.M V₀ V hV L) {X X' : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    (hX' : X' ∈ wConj D.M V₀ V hV L)
    (heq : fSub15 D.M V₀ V hV L X = fSub15 D.M V₀ V hV L X') : X = X' := by
  by_contra hne
  have hXV : X ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hX
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hX'V : X' ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hX'
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hle : X ≤ fSub15 D.M V₀ V hV L X' := by
    rw [← heq]
    exact le_sup_left
  have hsub : imgTil (v1Sub D.M V₀ V hV L) V hV X ≤
      imgTil (v1Sub D.M V₀ V hV L) V hV X' := by
    calc imgTil (v1Sub D.M V₀ V hV L) V hV X
        ≤ imgTil (v1Sub D.M V₀ V hV L) V hV (X' ⊔ v1Sub D.M V₀ V hV L) :=
          s15_TwelveA_imgTil_mono hV hle
      _ = imgTil (v1Sub D.M V₀ V hV L) V hV X' :=
          s15_Infra_imgTil_sup_left hV hX'V hV1V
  have hinj := s15_TwelveA_imgTil_wConj_injOn D h1217 h hV hL
  have hne_img : imgTil (v1Sub D.M V₀ V hV L) V hV X ≠
      imgTil (v1Sub D.M V₀ V hV L) V hV X' :=
    fun hh => hne (hinj hX hX' hh)
  have hXstar : imgTil (v1Sub D.M V₀ V hV L) V hV X ∈ wStarConj D.M V₀ V hV L := by
    obtain ⟨m, hm, rfl⟩ := hX
    exact ⟨m, hm, rfl⟩
  have hX'star : imgTil (v1Sub D.M V₀ V hV L) V hV X' ∈ wStarConj D.M V₀ V hV L := by
    obtain ⟨m, hm, rfl⟩ := hX'
    exact ⟨m, hm, rfl⟩
  have hind := (fifteen_two_directSum D h1217 h hV hL).1
  have hbot : imgTil (v1Sub D.M V₀ V hV L) V hV X = ⊥ := by
    have hd : Disjoint (imgTil (v1Sub D.M V₀ V hV L) V hV X)
        (imgTil (v1Sub D.M V₀ V hV L) V hV X') :=
      hind.pairwiseDisjoint hXstar hX'star hne_img
    rw [disjoint_iff] at hd
    rwa [inf_eq_left.2 hsub] at hd
  have hrk := s15_Two_rk_wStarConj h hV hXstar
  rw [hbot, rk_bot] at hrk
  omega

theorem s15_Twelve_fixes (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    {Y : Subgroup G} (hY : Y ≤ D.M)
    (hc : E3.mQuot V (centralizer (Y : Set G)) < gamma15 D.M V₀ V hV L)
    {Z : Subgroup G} (hZ : Z ∈ wConj D.M V₀ V hV L) :
    Y ≤ normalizer (fSub15 D.M V₀ V hV L Z : Set G) ∧ Y ≤ normalizer (Z : Set G) := by
  have hγ : 0 < gamma15 D.M V₀ V hV L := lt_of_le_of_lt (Nat.zero_le _) hc
  have hstep : ∀ y ∈ Y, conjSubgroup (fSub15 D.M V₀ V hV L Z) y = fSub15 D.M V₀ V hV L Z ∧
      conjSubgroup Z y = Z := by
    intro y hy
    have hcy : E3.mQuot V (centralizer ({y} : Set G)) < gamma15 D.M V₀ V hV L :=
      lt_of_le_of_lt (E3.mQuot_mono (V := V) (U := centralizer (Y : Set G))
        (U' := centralizer ({y} : Set G))
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy))) hc
    have hFy : conjSubgroup (fSub15 D.M V₀ V hV L Z) y = fSub15 D.M V₀ V hV L Z := by
      by_contra hne
      exact absurd (s15_Twelve_moved_rank D h1217 h hV hL (hY hy) hZ hne) (not_le.2 hcy)
    have hZy : conjSubgroup Z y ∈ wConj D.M V₀ V hV L := by
      obtain ⟨m, hm, rfl⟩ := hZ
      refine ⟨m * y, D.M.mul_mem hm (hY hy), ?_⟩
      rw [conjSubgroup_conjSubgroup]
    have heq : fSub15 D.M V₀ V hV L (conjSubgroup Z y) = fSub15 D.M V₀ V hV L Z := by
      rw [← hFy]
      unfold fSub15
      rw [s15_TwelveA_conjSubgroup_sup, s15_Infra_conjSubgroup_v1Sub h.hyp125 hV (hY hy)]
    exact ⟨hFy, s15_Twelve_fSub_inj D h1217 h hV hL hγ hZy hZ heq⟩
  refine ⟨fun y hy => conjSubgroup_eq_iff_mem_normalizer.1 (hstep y hy).1, ?_⟩
  exact fun y hy => conjSubgroup_eq_iff_mem_normalizer.1 (hstep y hy).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
