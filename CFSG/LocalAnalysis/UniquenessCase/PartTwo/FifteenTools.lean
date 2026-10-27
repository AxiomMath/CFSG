module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Tools_mQuot_le_add {B D C : Subgroup G} (hDB : D ≤ B) :
    E3.mQuot B C ≤ E3.mQuot B D + E3.mQuot D (D ⊓ C) := by
  have h1 := E3.mQuot_add (V := B) (U := D ⊓ C) (U' := D) inf_le_left hDB
  have h2 := E3.mQuot_mono (V := B) (U := D ⊓ C) (U' := C) inf_le_right
  omega

theorem s15_Tools_mQuot_inf_centralizer_le_add {B D F : Subgroup G} {v : G} (hB : IsPGroup 2 B)
    (hDB : D ≤ B) (hF : IsPGroup 2 F) (h : ∀ e ∈ D, v⁻¹ * (e⁻¹ * v * e) ∈ F) :
    E3.mQuot B (B ⊓ centralizer ({v} : Set G)) ≤ E3.mQuot B D + E3.mQuot F ⊥ := by
  have hD2 : IsPGroup 2 D := hB.to_le hDB
  have h1 := s15_Tools_mQuot_le_add (B := B) (D := D) (C := B ⊓ centralizer ({v} : Set G)) hDB
  have h2 := s15_FiveTen_mQuot_inf_centralizer_le hD2 hF h
  have h3 : D ⊓ (B ⊓ centralizer ({v} : Set G)) = D ⊓ centralizer ({v} : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hDB]
  rw [h3] at h1
  omega

theorem s15_Tools_mSub_le_mQuot {V U A : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hAV : A ≤ V) (hUA : U ⊓ A = ⊥) : mSub A ≤ E3.mQuot V U := by
  have hA2 : IsPGroup 2 A := hV.to_le hAV
  have h1 : U.relIndex A ≤ U.relIndex V :=
    Subgroup.relIndex_le_of_le_right hAV (E3.relIndex_ne_zero' V U)
  have h2 : U.relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_right U A, hUA, Subgroup.relIndex_bot_left]
  rw [h2, E3.relIndex_eq_two_pow hV U, card_eq_two_pow_mSub hA2] at h1
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 h1

theorem s15_Tools_conjSubgroup_M (D : Data G) {m : G} (hm : m ∈ D.M) :
    conjSubgroup D.M m = D.M := by
  have hK : IsMaxTwoLocalSubgroup D.M := D.maxLocal
  exact conjSubgroup_eq_iff_mem_normalizer.mpr
    (by rw [UC6.normalizer_eq_of_isMaxTwoLocal hK]; exact hm)

theorem s15_Tools_good_of_mem_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {m w : G} (hm : m ∈ D.M)
    (hw : w ∈ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m) (hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have := uniqueMax_conjSubgroup_of_mem (M := D.M) (g := m) (a := w)
    (X := wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (fun w hw hw1 => h.unique₁ w hw hw1) hw hw1
  rwa [s15_Tools_conjSubgroup_M D hm] at this

theorem s15_Tools_good_of_mem_sup_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : 4 ≤ s15 D.M V₀ V hV L) {x y w : G} (hx : x ∈ D.M)
    (hy : y ∈ D.M)
    (hw : w ∈ conjSubgroup (wSub V₀ V hV L) x ⊔ conjSubgroup (wSub V₀ V hV L) y) (hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hcard := ncard_wConj D h.hyp151 hV
  have hfin : (wConj D.M V₀ V hV L).Finite := Set.toFinite _
  have hX : conjSubgroup (wSub V₀ V hV L) x ∈ wConj D.M V₀ V hV L := ⟨x, hx, rfl⟩
  have hY : conjSubgroup (wSub V₀ V hV L) y ∈ wConj D.M V₀ V hV L := ⟨y, hy, rfl⟩
  have h1 := Set.ncard_le_ncard_sdiff_add_ncard (wConj D.M V₀ V hV L)
    ({conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} : Set (Subgroup G))
  have h2 : ({conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
      Set (Subgroup G)).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have h3 : 1 < (wConj D.M V₀ V hV L \ {conjSubgroup (wSub V₀ V hV L) x,
      conjSubgroup (wSub V₀ V hV L) y}).ncard := by omega
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := (Set.one_lt_ncard_iff (hfin.diff)).1 h3
  obtain ⟨⟨a, ha, rfl⟩, hPXY⟩ := hP
  obtain ⟨⟨b, hb, rfl⟩, hQXY⟩ := hQ
  have hPX : conjSubgroup (wSub V₀ V hV L) a ≠ conjSubgroup (wSub V₀ V hV L) x :=
    fun e => hPXY (Or.inl e)
  have hPY : conjSubgroup (wSub V₀ V hV L) a ≠ conjSubgroup (wSub V₀ V hV L) y :=
    fun e => hPXY (Or.inr e)
  have hQX : conjSubgroup (wSub V₀ V hV L) b ≠ conjSubgroup (wSub V₀ V hV L) x :=
    fun e => hQXY (Or.inl e)
  have hQY : conjSubgroup (wSub V₀ V hV L) b ≠ conjSubgroup (wSub V₀ V hV L) y :=
    fun e => hQXY (Or.inr e)
  refine h.unique₂ a ha b hb hPQ w ?_ hw1
  refine Subgroup.mem_sup_right ?_
  have hle : conjSubgroup (wSub V₀ V hV L) x ⊔ conjSubgroup (wSub V₀ V hV L) y ≤
      ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧ X ≠ conjSubgroup (wSub V₀ V hV L) a ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) b}, X := by
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (conjSubgroup (wSub V₀ V hV L) x)
        ⟨hX, fun e => hPX e.symm, fun e => hQX e.symm⟩ le_rfl
    · exact le_iSup₂_of_le (conjSubgroup (wSub V₀ V hV L) y)
        ⟨hY, fun e => hPY e.symm, fun e => hQY e.symm⟩ le_rfl
  exact hle hw

theorem s15_Tools_inf_conj_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) {m : G} (hm : m ∈ D.M) :
    U ⊓ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  by_contra hu1
  obtain ⟨huU, hum⟩ := Subgroup.mem_inf.1 hu
  have hgood := s15_Tools_good_of_mem_conj D h hV hm hum hu1
  have hu2 : ∃ n : ℕ, u ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 u (hUV huU)⟩
  have hc := (centralizer_le_of_uniqueMax D.maxLocal hu1 hu2 hgood).1
  exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)).trans hc)

theorem s15_Tools_inf_S_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) {x y : G} (hx : x ∈ D.M) (hy : y ∈ D.M)
    (hxy : conjSubgroup (wSub V₀ V hV L) x ≠ conjSubgroup (wSub V₀ V hV L) y) :
    U ⊓ (v1Sub D.M V₀ V hV L ⊔ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
      X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y}, X) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  by_contra hu1
  obtain ⟨huU, huS⟩ := Subgroup.mem_inf.1 hu
  have hgood := h.unique₂ x hx y hy hxy u huS hu1
  have hu2 : ∃ n : ℕ, u ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 u (hUV huU)⟩
  have hc := (centralizer_le_of_uniqueMax D.maxLocal hu1 hu2 hgood).1
  exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)).trans hc)

theorem s15_Tools_conj_wSub_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {m : G} (hm : m ∈ D.M) :
    conjSubgroup (wSub V₀ V hV L) m ≤ V := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)]
  exact preTil_le V₀ V hV _

theorem s15_Tools_mSub_S (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {x y : G}
    (hx : x ∈ D.M) (hy : y ∈ D.M)
    (hxy : conjSubgroup (wSub V₀ V hV L) x ≠ conjSubgroup (wSub V₀ V hV L) y) :
    mSub (v1Sub D.M V₀ V hV L ⊔ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
      X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y}, X) =
      (s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) := by
  set V₁ := v1Sub D.M V₀ V hV L with hV₁def
  set 𝒲 := wConj D.M V₀ V hV L with h𝒲def
  set W₁ := conjSubgroup (wSub V₀ V hV L) x with hW₁def
  set W₂ := conjSubgroup (wSub V₀ V hV L) y with hW₂def
  set 𝒲' : Set (Subgroup G) := {X | X ∈ 𝒲 ∧ X ≠ W₁ ∧ X ≠ W₂} with h𝒲'def
  have hV₁V : V₁ ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hXV : ∀ X ∈ 𝒲, X ≤ V := by
    rintro X ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hTV : (⨆ X ∈ 𝒲', X) ≤ V := iSup₂_le fun X hX => hXV X hX.1
  have hSV : V₁ ⊔ (⨆ X ∈ 𝒲', X) ≤ V := sup_le hV₁V hTV
  have himg : imgTil V₁ V hV (V₁ ⊔ ⨆ X ∈ 𝒲', X) = sSup ((fun X => imgTil V₁ V hV X) '' 𝒲') := by
    rw [s15_Core_imgTil_sup hV hV₁V hTV, s15_Core_imgTil_eq_bot_of_le hV le_rfl, bot_sup_eq,
      s15_Core_imgTil_iSup V₁ V hV _ (fun X => iSup_le fun hX => hXV X hX.1), sSup_image]
    refine iSup_congr fun X => ?_
    rw [s15_Core_imgTil_iSup V₁ V hV (fun _ : X ∈ 𝒲' => X) (fun hX => hXV X hX.1)]
  have hsub : (fun X => imgTil V₁ V hV X) '' 𝒲' ⊆ wStarConj D.M V₀ V hV L := by
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hX.1
    exact ⟨m, hm, rfl⟩
  have hind : sSupIndep ((fun X => imgTil V₁ V hV X) '' 𝒲') :=
    (sSupIndep_wStarConj D h hV hL).mono hsub
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
  have hW₁ : W₁ ∈ 𝒲 := ⟨x, hx, rfl⟩
  have hW₂ : W₂ ∈ 𝒲 := ⟨y, hy, rfl⟩
  have hncard : 𝒲'.ncard = s15 D.M V₀ V hV L - 2 := by
    have h1 : 𝒲' = 𝒲 \ {W₁, W₂} := by
      ext X
      simp only [h𝒲'def, Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
    have h2 : ({W₁, W₂} : Set (Subgroup G)) ⊆ 𝒲 := by
      intro X hX
      rcases hX with rfl | rfl
      exacts [hW₁, hW₂]
    rw [h1, Set.ncard_sdiff' h2 (Set.toFinite _), ncard_wConj D h hV, Set.ncard_pair hxy]
  have hrk : rk ↥(imgTil V₁ V hV (V₁ ⊔ ⨆ X ∈ 𝒲', X)) =
      (s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L := by
    rw [himg, s15_Lin_rk_sSup_eq_finsum hind,
      s15_Two_finsum_mem_eq_ncard_mul _ (fun U : Subgroup (vStar D.M V₀ V hV L) => rk ↥U)
        (gamma15 D.M V₀ V hV L) (Set.toFinite _)
        (fun U hU => ?_), (hinj.mono fun X hX => hX.1).ncard_image, hncard]
    exact s15_Two_rk_wStarConj h hV (hsub hU)
  have hfin := s15_Infra_mSub_eq_rk_imgTil_add V₁ V (V₁ ⊔ ⨆ X ∈ 𝒲', X) hV hSV
  rw [inf_eq_right.2 (le_sup_left : V₁ ≤ V₁ ⊔ ⨆ X ∈ 𝒲', X), hrk] at hfin
  exact hfin

theorem s15_Tools_le_mQuot (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    max (gamma15 D.M V₀ V hV L) ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) +
        mSub (v1Sub D.M V₀ V hV L) ≤ E3.mQuot V U := by
  have h151 := h.hyp151
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h151.hyp125 hV
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V := sup_le (preTil_le V₀ V hV _) hV1V
  have hA : gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) ≤ E3.mQuot V U := by
    have h1 := s15_Tools_inf_conj_eq_bot D h hV hUV hU D.M.one_mem
    rw [conjSubgroup_one] at h1
    have h2 := s15_Tools_mSub_le_mQuot hV2 hUV hWV h1
    rwa [mSub_wSub_sup_v1Sub D h151.hyp125 hV] at h2
  have hB : (s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) ≤
      E3.mQuot V U := by
    by_cases hs : s15 D.M V₀ V hV L ≤ 1
    · have h0 : s15 D.M V₀ V hV L - 2 = 0 := by omega
      rw [h0, zero_mul, zero_add]
      omega
    · have hcard := ncard_wConj D h151 hV
      have h2 : 1 < (wConj D.M V₀ V hV L).ncard := by omega
      obtain ⟨P, Q, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hPQ⟩ :=
        (Set.one_lt_ncard_iff (Set.toFinite _)).1 h2
      have hS := s15_Tools_mSub_S D h151 hV hL hx hy hPQ
      have hSV : v1Sub D.M V₀ V hV L ⊔ ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y}, X ≤ V := by
        refine sup_le hV1V (iSup₂_le fun X hX => ?_)
        obtain ⟨m, hm, rfl⟩ := hX.1
        exact s15_Tools_conj_wSub_le D h151.hyp125 hV hm
      have h3 := s15_Tools_mSub_le_mQuot hV2 hUV hSV
        (s15_Tools_inf_S_eq_bot D h hV hUV hU hx hy hPQ)
      rwa [hS] at h3
  rw [← Nat.add_max_add_right]
  exact max_le hA hB

theorem s15_Tools_le_rMV (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    ((max (gamma15 D.M V₀ V hV L) ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) +
        mSub (v1Sub D.M V₀ V hV L) : ℕ) : ℕ∞) ≤ rMV D.M V := by
  unfold rMV
  refine le_iInf₂ fun U hU => ?_
  exact_mod_cast s15_Tools_le_mQuot D h hV hL hU.1 hU.2

theorem s15_Tools_inf_centralizer_eq_bot (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} {B : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) {w : G}
    (hwg : w ∉ conjSubgroup D.M g) :
    B ⊓ centralizer ({w} : Set G) = ⊥ := by
  subst hB
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  by_contra hb1
  obtain ⟨hbA, hbC⟩ := Subgroup.mem_inf.1 hb
  have hu := uniqueMax_conjSubgroup_of_mem (g := g) h.unique₁ hbA hb1
  have hK : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hb2 : ∃ n : ℕ, b ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have := (E3.isElemAbelian_conjSubgroup hV g).2 b (E3.conjSubgroup_mono_left g hWV hbA)
    simpa using this
  have hwb : w ∈ centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbC).symm
  exact hwg ((centralizer_le_of_uniqueMax hK hb1 hb2 hu).1 hwb)

theorem s15_Tools_orbit_mem (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {e w : G} (he : e⁻¹ ∈ normalizer (wSub V₀ V hV L : Set G))
    (hw : w ∈ wSub V₀ V hV L) (hc : e⁻¹ * w * e * w⁻¹ ∈ v1Sub D.M V₀ V hV L) :
    w⁻¹ * (e⁻¹ * w * e) ∈ v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L := by
  have hc2 : e⁻¹ * w * e ∈ wSub V₀ V hV L := by
    have := (Subgroup.mem_normalizer_iff.1 he w).1 hw
    simpa using this
  have hc3 : e⁻¹ * w * e * w⁻¹ ∈ wSub V₀ V hV L :=
    (wSub V₀ V hV L).mul_mem hc2 ((wSub V₀ V hV L).inv_mem hw)
  have hcV : e⁻¹ * w * e * w⁻¹ ∈ V := preTil_le V₀ V hV _ hc3
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  have hcomm := B2F.isElemAbelian_comm hV hcV hwV
  have key : w⁻¹ * (e⁻¹ * w * e) = e⁻¹ * w * e * w⁻¹ := by
    calc w⁻¹ * (e⁻¹ * w * e) = w⁻¹ * ((e⁻¹ * w * e * w⁻¹) * w) := by group
      _ = w⁻¹ * (w * (e⁻¹ * w * e * w⁻¹)) := by rw [hcomm]
      _ = e⁻¹ * w * e * w⁻¹ := by group
  rw [key]
  exact Subgroup.mem_inf.2 ⟨hc, hc3⟩

theorem s15_Tools_mSub_le_delta (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} {B E : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) (hEB : E ≤ B)
    (hEN : E ≤ normalizer (wSub V₀ V hV L : Set G))
    (hE : ∀ e ∈ E, ∀ w ∈ wSub V₀ V hV L, e * w * e⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L)
    (hW : ¬ wSub V₀ V hV L ≤ conjSubgroup D.M g) : mSub E ≤ delta15 D.M V₀ V hV L := by
  obtain ⟨w, hwW, hwg⟩ := SetLike.not_le_iff_exists.1 hW
  have hcb := s15_Tools_inf_centralizer_eq_bot D h hV hB hwg
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hBV : B ≤ conjSubgroup V g := hB ▸ E3.conjSubgroup_mono_left g hWV
  have hE2 : IsPGroup 2 E :=
    ((E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV).to_le hEB
  have hF2 : IsPGroup 2 ↥(v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) :=
    hV.isPGroup.to_le (inf_le_left.trans (s15_Infra_v1Sub_le h.hyp151.hyp125 hV))
  have horbit : ∀ e ∈ E, w⁻¹ * (e⁻¹ * w * e) ∈ v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L := by
    intro e he
    have hc1 := hE e⁻¹ (E.inv_mem he) w hwW
    rw [inv_inv] at hc1
    exact s15_Tools_orbit_mem D h.hyp151.hyp125 hV (hEN (E.inv_mem he)) hwW hc1
  have hmq := s15_FiveTen_mQuot_inf_centralizer_le hE2 hF2 horbit
  have h1 : E ⊓ centralizer ({w} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' := Subgroup.mem_inf.1 hx
    have h2 : x ∈ B ⊓ centralizer ({w} : Set G) := Subgroup.mem_inf.2 ⟨hEB hx'.1, hx'.2⟩
    rw [hcb] at h2
    exact h2
  rw [h1, s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at hmq
  exact hmq

theorem s15_Tools_mem_conj_of_mQuot_lt (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} {B Dd : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hBN : B ≤ normalizer (wSub V₀ V hV L : Set G)) (hDB : Dd ≤ B)
    (hm : E3.mQuot B Dd < gamma15 D.M V₀ V hV L) {w : G} (hw : w ∈ wSub V₀ V hV L)
    (hfix : ∀ d ∈ Dd, d * w * d⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L) : w ∈ conjSubgroup D.M g := by
  by_contra hwg
  have hcb := s15_Tools_inf_centralizer_eq_bot D h hV hB hwg
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hBV : B ≤ conjSubgroup V g := hB ▸ E3.conjSubgroup_mono_left g hWV
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hF2 : IsPGroup 2 ↥(v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) :=
    hV.isPGroup.to_le (inf_le_left.trans (s15_Infra_v1Sub_le h.hyp151.hyp125 hV))
  have horbit : ∀ e ∈ Dd, w⁻¹ * (e⁻¹ * w * e) ∈ v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L := by
    intro e he
    have hc1 := hfix e⁻¹ (Dd.inv_mem he)
    rw [inv_inv] at hc1
    exact s15_Tools_orbit_mem D h.hyp151.hyp125 hV (hBN (hDB (Dd.inv_mem he))) hw hc1
  have hmq := s15_Tools_mQuot_inf_centralizer_le_add hB2 hDB hF2 horbit
  rw [hcb] at hmq
  have h1 := s15_FiveTen_mQuot_conj_bot D h.hyp151.hyp125 hV (L := L) g
  rw [← hB] at h1
  have h2 := E3.mQuot_add (V := v1Sub D.M V₀ V hV L) (U := ⊥)
    (U' := v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) bot_le inf_le_left
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
