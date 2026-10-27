module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FixedPointsTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Glue3_good_of_mem_wConj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) {x : G}
    (hx : x ∈ X) (hx1 : x ≠ 1) : UniqueMax D.M (D.M ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨m, hm, rfl⟩ := hX
  refine s15_Tools_good_of_mem_conj D h hV hm ?_ hx1
  exact E3.conjSubgroup_mono_left m (le_sup_left : wSub V₀ V hV L ≤ _) hx

theorem s15_Glue3_centralizer_le_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) (g : G) {a : G}
    (ha : a ∈ conjSubgroup X g) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) ≤ conjSubgroup D.M g := by
  have hXV : X ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hX
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hu := uniqueMax_conjSubgroup_of_mem (g := g) (X := X) (M := D.M)
    (fun w hw hw1 => s15_Glue3_good_of_mem_wConj D h hV hX hw hw1) ha ha1
  have hK : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have ha2 : ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have := (E3.isElemAbelian_conjSubgroup hV g).2 a (E3.conjSubgroup_mono_left g hXV ha)
    simpa using this
  exact (centralizer_le_of_uniqueMax hK ha1 ha2 hu).1

theorem s15_Glue3_inf_V_eq_bot_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hVg : ¬ V ≤ conjSubgroup D.M g) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) : conjSubgroup X g ⊓ V = ⊥ := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hMg : conjSubgroup D.M (m * g) = conjSubgroup D.M g := by
    rw [← conjSubgroup_conjSubgroup, s15_Tools_conjSubgroup_M D hm]
  have h1 := s15_Glue_inf_V_eq_bot D h hV (g := m * g) (hMg ▸ hVg)
  rw [eq_bot_iff, ← h1, ← conjSubgroup_conjSubgroup]
  exact inf_le_inf_right _ (E3.conjSubgroup_mono_left g
    (E3.conjSubgroup_mono_left m (le_sup_left : wSub V₀ V hV L ≤ _)))

theorem s15_Glue3_rk_conjSubgroup (X : Subgroup G) (g : G) :
    rk ↥(conjSubgroup X g) = rk ↥X := by
  rw [← s15_FiveTen_mQuot_bot_eq_rk, ← s15_FiveTen_mQuot_bot_eq_rk, ← E3.mQuot_conjSubgroup X ⊥ g,
    (conjSubgroup_eq_bot_iff (A := (⊥ : Subgroup G)) (g := g)).2 rfl]

theorem s15_Glue3_rk_wConj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hV1 : v1Sub D.M V₀ V hV L = ⊥) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) : rk ↥X = gamma15 D.M V₀ V hV L := by
  obtain ⟨m, hm, rfl⟩ := hX
  have h2 := mSub_wSub D h.hyp125 hV (L := L)
  have h3 : delta15 D.M V₀ V hV L = 0 := by
    unfold delta15
    rw [hV1, bot_inf_eq]
    exact rk_bot
  rw [s15_Glue3_rk_conjSubgroup]
  change mSub (wSub V₀ V hV L) = _ at h2
  rw [h3] at h2
  exact h2

theorem s15_Glue3_indep (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hV1 : v1Sub D.M V₀ V hV L = ⊥) : sSupIndep (wConj D.M V₀ V hV L) := by
  classical
  set V₁ := v1Sub D.M V₀ V hV L with hV₁
  set 𝒲 := wConj D.M V₀ V hV L with h𝒲
  have hXV : ∀ X ∈ 𝒲, X ≤ V := by
    rintro X ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have himgset : (fun X => imgTil V₁ V hV X) '' 𝒲 = wStarConj D.M V₀ V hV L := by
    ext U
    constructor
    · rintro ⟨X, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hinj : Set.InjOn (fun X => imgTil V₁ V hV X) 𝒲 := by
    refine (Set.ncard_image_iff (Set.toFinite _)).1 ?_
    rw [himgset, ncard_wStarConj D h hV, ncard_wConj D h hV]
  have hind := sSupIndep_wStarConj D h hV hL
  intro X hX
  have hXst : imgTil V₁ V hV X ∈ wStarConj D.M V₀ V hV L := by
    rw [← himgset]
    exact ⟨X, hX, rfl⟩
  have hdiff : wStarConj D.M V₀ V hV L \ {imgTil V₁ V hV X} =
      (fun Y => imgTil V₁ V hV Y) '' (𝒲 \ {X}) := by
    ext Z
    constructor
    · rintro ⟨hZ, hZX⟩
      have hZ' : Z ∈ (fun Y => imgTil V₁ V hV Y) '' 𝒲 := by
        rw [himgset]
        exact hZ
      obtain ⟨Y, hY, rfl⟩ := hZ'
      refine ⟨Y, ⟨hY, ?_⟩, rfl⟩
      rintro rfl
      exact hZX rfl
    · rintro ⟨Y, ⟨hY, hYX⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← himgset]
        exact ⟨Y, hY, rfl⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hYX (hinj hY hX h)
  have hsup : imgTil V₁ V hV (sSup (𝒲 \ {X})) =
      sSup (wStarConj D.M V₀ V hV L \ {imgTil V₁ V hV X}) := by
    rw [sSup_eq_iSup']
    rw [s15_Core_imgTil_iSup V₁ V hV (fun Y : ↥(𝒲 \ {X}) => (Y : Subgroup G))
      (fun Y => hXV Y.1 Y.2.1)]
    rw [hdiff, sSup_image']
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxX, hxS⟩
  have hxV : x ∈ V := hXV X hX hxX
  have hq : mkTil V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
      imgTil V₁ V hV X ⊓ sSup (wStarConj D.M V₀ V hV L \ {imgTil V₁ V hV X}) := by
    refine ⟨?_, ?_⟩
    · exact (mem_imgTil V₁ V hV X _).2 ⟨IntMod.mk hV ⟨x, hxV⟩, hxX, rfl⟩
    · rw [← hsup]
      exact (mem_imgTil V₁ V hV (sSup (𝒲 \ {X})) _).2
        ⟨IntMod.mk hV ⟨x, hxV⟩, hxS, rfl⟩
  have hbot := (hind hXst).le_bot hq
  rw [Subgroup.mem_bot, ← map_one (mkTil V₁ V hV), mkTil_eq_iff] at hbot
  have hxV1 : x ∈ V₁ := by
    rw [show (IntMod.mk hV ⟨x, hxV⟩).val = x from rfl, IntMod.val_one, inv_one, mul_one] at hbot
    exact hbot
  rw [hV1] at hxV1
  exact Subgroup.mem_bot.2 (Subgroup.mem_bot.1 hxV1)

@[expose] def wConjG (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) (g : G) :
    Set (Subgroup G) :=
  (fun X => conjSubgroup X g) '' wConj M V₀ V hV L

theorem mem_wConjG {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G} {g : G}
    {Y : Subgroup G} : Y ∈ wConjG M V₀ V hV L g ↔ ∃ X ∈ wConj M V₀ V hV L, Y = conjSubgroup X g :=
  ⟨fun ⟨X, hX, hY⟩ => ⟨X, hX, hY.symm⟩, fun ⟨X, hX, hY⟩ => ⟨X, hX, hY.symm⟩⟩

theorem s15_Glue3_wConjG_indep (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (g : G) : sSupIndep (wConjG D.M V₀ V hV L g) := by
  classical
  set 𝒲 := wConj D.M V₀ V hV L with h𝒲
  have hinj : Function.Injective (fun Z : Subgroup G => conjSubgroup Z g) := fun A B hab => by
    have := congrArg (fun Z => conjSubgroup Z g⁻¹) hab
    simpa only [conjSubgroup_conjSubgroup_inv] using this
  have hind := s15_Glue3_indep D h hV hL hV1
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := mem_wConjG.1 hY
  have hset : wConjG D.M V₀ V hV L g \ {conjSubgroup X g} =
      (fun Z => conjSubgroup Z g) '' (𝒲 \ {X}) := by
    ext Z
    constructor
    · rintro ⟨hZ, hZX⟩
      obtain ⟨Z₀, hZ₀, rfl⟩ := mem_wConjG.1 hZ
      refine ⟨Z₀, ⟨hZ₀, ?_⟩, rfl⟩
      rintro rfl
      exact hZX rfl
    · rintro ⟨Z₀, ⟨hZ₀, hZ₀X⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_wConjG]
        exact ⟨Z₀, hZ₀, rfl⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hZ₀X (hinj h)
  have hsup : sSup (wConjG D.M V₀ V hV L g \ {conjSubgroup X g}) =
      conjSubgroup (sSup (𝒲 \ {X})) g := by
    rw [hset, sSup_image']
    unfold conjSubgroup
    rw [sSup_eq_iSup', Subgroup.map_iSup]
  have hd : Disjoint X (sSup (𝒲 \ {X})) := hind hX
  rw [disjoint_iff] at hd ⊢
  rw [hsup, ← E3.conjSubgroup_inf, hd, E3.conjSubgroup_bot]

theorem s15_Glue3_wConjG_sSup (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (g : G) :
    sSup (wConjG D.M V₀ V hV L g) = conjSubgroup V g := by
  have h1 := iSup_wConj_eq D h1217 h hV hL
  have h2 : sSup (wConjG D.M V₀ V hV L g) =
      conjSubgroup (⨆ X ∈ wConj D.M V₀ V hV L, X) g := by
    unfold wConjG conjSubgroup
    rw [sSup_image]
    simp only [Subgroup.map_iSup]
  rw [h2, h1]

theorem s15_Glue3_wConjG_rk (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hV1 : v1Sub D.M V₀ V hV L = ⊥) (g : G) {Y : Subgroup G}
    (hY : Y ∈ wConjG D.M V₀ V hV L g) : rk ↥Y = gamma15 D.M V₀ V hV L := by
  obtain ⟨X, hX, rfl⟩ := mem_wConjG.1 hY
  rw [s15_Glue3_rk_conjSubgroup]
  exact s15_Glue3_rk_wConj D h hV hV1 hX

theorem s15_Glue3_wConjG_ncard (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (g : G) :
    (wConjG D.M V₀ V hV L g).ncard = s15 D.M V₀ V hV L := by
  unfold wConjG
  have hinj : Function.Injective (fun X : Subgroup G => conjSubgroup X g) := fun X Y hXY => by
    have := congrArg (fun Z => conjSubgroup Z g⁻¹) hXY
    simpa only [conjSubgroup_conjSubgroup_inv] using this
  rw [Set.ncard_image_of_injective _ hinj]
  exact ncard_wConj D h hV

theorem s15_Glue3_wConjG_perm (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    {g y : G} (hy : y ∈ conjSubgroup D.M g) {Y : Subgroup G}
    (hY : Y ∈ wConjG D.M V₀ V hV L g) : conjSubgroup Y y ∈ wConjG D.M V₀ V hV L g := by
  obtain ⟨X, ⟨m, hm, rfl⟩, rfl⟩ := hY
  have hy' : g * y * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hy
  refine ⟨conjSubgroup (wSub V₀ V hV L) (m * (g * y * g⁻¹)),
    ⟨_, D.M.mul_mem hm hy', rfl⟩, ?_⟩
  simp only [conjSubgroup_conjSubgroup]
  congr 1
  group

theorem s15_Glue3_normalizes_of_fixes (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) {f : G} (hf : f ∈ D.M) {x : G} (hx : x ∈ X)
    (hx1 : x ≠ 1) (hfix : f * x * f⁻¹ = x) : f ∈ normalizer (X : Set G) := by
  have hind := (s15_Glue3_indep D h hV hL hV1).pairwiseDisjoint
  obtain ⟨m, hm, rfl⟩ := hX
  have hX' : conjSubgroup (conjSubgroup (wSub V₀ V hV L) m) f ∈ wConj D.M V₀ V hV L := by
    refine ⟨m * f, D.M.mul_mem hm hf, ?_⟩
    rw [conjSubgroup_conjSubgroup]
  by_contra hnot
  have hne : conjSubgroup (conjSubgroup (wSub V₀ V hV L) m) f ≠
      conjSubgroup (wSub V₀ V hV L) m := fun heq =>
    hnot (conjSubgroup_eq_iff_mem_normalizer.1 heq)
  have hdis := hind ⟨m, hm, rfl⟩ hX' hne.symm
  have hxX' : x ∈ conjSubgroup (conjSubgroup (wSub V₀ V hV L) m) f := by
    rw [mem_conjSubgroup_iff, hfix]
    exact hx
  have := hdis.le_bot ⟨hx, hxX'⟩
  exact hx1 (Subgroup.mem_bot.1 this)

private lemma s15_Glue3_eq_conj_of_mem {A : Subgroup G} {g x : G}
    (h : x ∈ conjSubgroup A g) : ∃ a ∈ A, x = g⁻¹ * a * g := by
  rw [conjSubgroup, Subgroup.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, by simp⟩

theorem s15_Glue3_seven_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {A E X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) (hAM : A ≤ D.M) (hA2 : IsPGroup 2 A) (hEA : E ≤ A)
    (hEN : A ⊓ normalizer (X : Set G) ≤ E) (hne : E ≠ A) :
    ∃ v ∈ V, (∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L) ∧
      (∃ a ∈ A, a * v * a⁻¹ * v⁻¹ ∉ v1Sub D.M V₀ V hV L) ∧
      (E ≤ normalizer (X : Set G) → v ∈ X) := by
  classical
  set V₁ := v1Sub D.M V₀ V hV L with hV₁
  set W := wSub V₀ V hV L with hW
  obtain ⟨m, hm, rfl⟩ := hX
  have hinv : (m⁻¹)⁻¹ = m := inv_inv m
  have hinj : Function.Injective (fun Z : Subgroup G => conjSubgroup Z m⁻¹) := fun P Q h => by
    have := congrArg (fun Z => conjSubgroup Z m) h
    simpa only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] using this
  have hB2 : IsPGroup 2 (conjSubgroup A m⁻¹) := E3.isPGroup_conjSubgroup hA2 m⁻¹
  have hBM : conjSubgroup A m⁻¹ ≤ D.M := by
    rw [← s15_Tools_conjSubgroup_M D (D.M.inv_mem hm)]
    exact E3.conjSubgroup_mono_left m⁻¹ hAM
  have hE'B : conjSubgroup E m⁻¹ ≤ conjSubgroup A m⁻¹ :=
    E3.conjSubgroup_mono_left m⁻¹ hEA
  have hne' : conjSubgroup E m⁻¹ ≠ conjSubgroup A m⁻¹ := fun heq => hne (hinj heq)
  have hEN' : conjSubgroup A m⁻¹ ⊓ normalizer (W : Set G) ≤ conjSubgroup E m⁻¹ := by
    rintro b ⟨hbB, hbN⟩
    obtain ⟨a, haA, hbaeq⟩ := s15_Glue3_eq_conj_of_mem (A := A) (g := m⁻¹) hbB
    have hba : b = (m⁻¹)⁻¹ * a * m⁻¹ := hbaeq
    have hma : m * a * m⁻¹ = b := by rw [hba]; group
    have haN : a ∈ normalizer (conjSubgroup W m : Set G) := by
      rw [← E3.conjSubgroup_normalizer W m]
      exact (mem_conjSubgroup_iff (A := normalizer (W : Set G)) (g := m) (x := a)).2
        (by rw [hma]; exact hbN)
    have haE : a ∈ E := hEN ⟨haA, haN⟩
    refine (mem_conjSubgroup_iff (A := E) (g := m⁻¹) (x := b)).2 ?_
    have h1 : m⁻¹ * b * (m⁻¹)⁻¹ = a := by rw [hba]; group
    rw [h1]
    exact haE
  obtain ⟨v', hv'V, hv'E', hv'A', hv'W'⟩ :=
    fifteen_seven_G D h hV hL hBM hB2 hE'B hEN' hne'
  have hV1m : conjSubgroup V₁ m = V₁ := s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hm
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  refine ⟨m⁻¹ * v' * m, ?_, ?_, ?_, ?_⟩
  · have h1 := ((Subgroup.mem_normalizer_iff.1 (hM (D.M.inv_mem hm))) v').1 hv'V
    simpa [inv_inv] using h1
  · intro e he
    have he' : m * e * m⁻¹ ∈ conjSubgroup E m⁻¹ := by
      refine (mem_conjSubgroup_iff (A := E) (g := m⁻¹) (x := m * e * m⁻¹)).2 ?_
      have h1 : m⁻¹ * (m * e * m⁻¹) * (m⁻¹)⁻¹ = e := by group
      rw [h1]
      exact he
    have hmem := hv'E' _ he'
    have hmem' : m * (e * (m⁻¹ * v' * m) * e⁻¹ * (m⁻¹ * v' * m)⁻¹) * m⁻¹ ∈ V₁ := by
      rw [show m * (e * (m⁻¹ * v' * m) * e⁻¹ * (m⁻¹ * v' * m)⁻¹) * m⁻¹ =
        (m * e * m⁻¹) * v' * (m * e * m⁻¹)⁻¹ * v'⁻¹ from by group]
      exact hmem
    have hmem'' : e * (m⁻¹ * v' * m) * e⁻¹ * (m⁻¹ * v' * m)⁻¹ ∈ conjSubgroup V₁ m :=
      (mem_conjSubgroup_iff (A := V₁) (g := m) (x := _)).2 hmem'
    rwa [hV1m] at hmem''
  · obtain ⟨b, hbB, hb⟩ := hv'A'
    obtain ⟨a, haA, hbaeq⟩ := s15_Glue3_eq_conj_of_mem (A := A) (g := m⁻¹) hbB
    have hba : b = (m⁻¹)⁻¹ * a * m⁻¹ := hbaeq
    refine ⟨a, haA, ?_⟩
    intro hcontr
    apply hb
    have hb' : b = m * a * m⁻¹ := by rw [hba]; group
    have hW : a * (m⁻¹ * v' * m) * a⁻¹ * (m⁻¹ * v' * m)⁻¹ ∈ conjSubgroup V₁ m := by
      rwa [hV1m]
    have hmem' : m * (a * (m⁻¹ * v' * m) * a⁻¹ * (m⁻¹ * v' * m)⁻¹) * m⁻¹ ∈ V₁ :=
      (mem_conjSubgroup_iff (A := V₁) (g := m) (x := _)).1 hW
    rw [hb', show m * a * m⁻¹ * v' * (m * a * m⁻¹)⁻¹ * v'⁻¹ =
      m * (a * (m⁻¹ * v' * m) * a⁻¹ * (m⁻¹ * v' * m)⁻¹) * m⁻¹ from by group]
    exact hmem'
  · intro hE
    have hE'N : conjSubgroup E m⁻¹ ≤ normalizer (W : Set G) := by
      have hmono := E3.conjSubgroup_mono_left m⁻¹ hE
      rw [← E3.conjSubgroup_normalizer W m] at hmono
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hmono
    have hv'W : v' ∈ W := hv'W' hE'N
    refine (mem_conjSubgroup_iff (A := W) (g := m) (x := m⁻¹ * v' * m)).2 ?_
    have h1 : m * (m⁻¹ * v' * m) * m⁻¹ = v' := by group
    rw [h1]
    exact hv'W

theorem s15_Glue3_even_of_no_fixed (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPM : P ≤ D.M)
    (hP : ∀ X ∈ wConj D.M V₀ V hV L, ¬ P ≤ normalizer (X : Set G)) :
    Even (s15 D.M V₀ V hV L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set 𝒲 := wConj D.M V₀ V hV L with h𝒲
  haveI : Finite ↥𝒲 := Set.toFinite _
  letI : MulAction ↥P ↥𝒲 :=
    { smul := fun p X => ⟨conjSubgroup (X : Subgroup G) ((p : G)⁻¹), by
        obtain ⟨m, hm, hXm⟩ := X.2
        exact ⟨m * ((p : G)⁻¹), D.M.mul_mem hm (D.M.inv_mem (hPM p.2)), by
          rw [hXm, conjSubgroup_conjSubgroup]⟩⟩
      one_smul := fun X => Subtype.ext (by
        show conjSubgroup (X : Subgroup G) (((1 : ↥P) : G)⁻¹) = (X : Subgroup G)
        rw [show ((1 : ↥P) : G) = 1 from rfl, inv_one, conjSubgroup_one])
      mul_smul := fun p q X => Subtype.ext (by
        show conjSubgroup (X : Subgroup G) (((p * q : ↥P) : G)⁻¹) =
          conjSubgroup (conjSubgroup (X : Subgroup G) ((q : G)⁻¹)) ((p : G)⁻¹)
        rw [conjSubgroup_conjSubgroup]
        congr 1
        simp only [Subgroup.coe_mul, mul_inv_rev]) }
  have hfix : MulAction.fixedPoints ↥P ↥𝒲 = ∅ := by
    ext X
    constructor
    · intro hX
      rw [Set.mem_empty_iff_false]
      apply hP X X.2
      intro p hp
      have hfixp := (MulAction.mem_fixedPoints.1 hX) (⟨p, hp⟩ : ↥P)
      have hval : conjSubgroup (X : Subgroup G) (p⁻¹) = (X : Subgroup G) := by
        have h := congrArg Subtype.val hfixp
        exact h
      have hp' : p⁻¹ ∈ normalizer (X : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.1 hval
      simpa using (Subgroup.normalizer (X : Set G)).inv_mem hp'
    · intro hX
      rw [Set.mem_empty_iff_false] at hX
      exact hX.elim
  have hfix0 : Nat.card (MulAction.fixedPoints ↥P ↥𝒲) = 0 := by
    rw [hfix]
    simp
  have hmod := hP2.card_modEq_card_fixedPoints (α := ↥𝒲)
  rw [hfix0, h𝒲, Nat.card_coe_set_eq, ncard_wConj D h hV] at hmod
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.1 hmod)

theorem s15_Glue3_normalizer_eq_of_s_two (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) :
    D.M ⊓ normalizer (X : Set G) = D.M ⊓ normalizer (wSub V₀ V hV L : Set G) := by
  classical
  set N0 := D.M ⊓ normalizer (wSub V₀ V hV L : Set G) with hN0
  have hrel := s15_Glue_relIndex_inf_normalizer_le D h hV (E := D.M) le_rfl
  rw [hs] at hrel
  have hidx : (N0.subgroupOf D.M).index ≤ 2 := hrel
  have hne : (N0.subgroupOf D.M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : (N0.subgroupOf D.M).index = 1 ∨ (N0.subgroupOf D.M).index = 2 := by
    have h1 : 1 ≤ (N0.subgroupOf D.M).index := Nat.one_le_iff_ne_zero.mpr hne
    omega
  have hnormal : (N0.subgroupOf D.M).Normal := by
    rcases hcases with hc | hc
    · rw [Subgroup.index_eq_one.1 hc]
      exact Subgroup.normal_top
    · exact Subgroup.normal_of_index_eq_two hc
  have hNM : D.M ≤ normalizer (N0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).1 hnormal
  obtain ⟨m, hm, rfl⟩ := hX
  have hconj : conjSubgroup N0 m = N0 :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hNM hm)
  have hXeq : D.M ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) m : Set G) = N0 := by
    have h1 : conjSubgroup N0 m =
        D.M ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) m : Set G) := by
      rw [hN0, E3.conjSubgroup_inf, E3.conjSubgroup_normalizer,
        s15_Tools_conjSubgroup_M D hm]
    rw [← h1]
    exact hconj
  rw [hXeq, hN0]

theorem s15_Glue3_exists_fixed {P U : Subgroup G} (hP : IsPGroup 2 P) (hU : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) (hPU : P ≤ normalizer (U : Set G)) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ x ∈ P, x * u = u * x :=
  CFSG.AGLEmbeddingD2.McLaughlin.exists_ne_one_mem_centralizer_of_normalizes hP hU hU1 hPU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
