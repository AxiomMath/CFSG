module

public import CFSG.Quasithin.H13.A5S1327zc
public import CFSG.Quasithin.H13.A5S1328Sym3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c126_of_minParabolic {C₁ C₂ : Subgroup G → Subgroup G} (h126 : C126Statement C₁ C₂)
    {X T X₀ : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hmp : MinParabolic X T X₀) :
    X ≤ Subgroup.centralizer (C₁ T : Set G) ∨ X ≤ Subgroup.normalizer (C₂ T : Set G) ∨
      ∃ B : Subgroup G, IsChi0Block X B := by
  obtain ⟨hmin, hT, -⟩ := minParabolic_iff.mp hmp
  rcases h126 X T hSQ hT hX hmin with h1 | h2 | ⟨r, B, hr, hB, -⟩
  · left
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (h1 hc).2 x hx).symm
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨B ⟨0, hr⟩, (hB _).1⟩)

omit [Finite G] in
theorem eq_of_isBlock2 {X K B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hX2 : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K)
    (hKres : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal →
      (∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = K)
    (hsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hB : IsBlock2 X B) : B = K := by
  classical
  obtain ⟨hBs, hBX, hBsn⟩ := hB
  have hres := hBs.1
  have hB1 : B ≠ ⊥ := by
    rintro rfl
    have h := hBs.2.2.2.2.1
    have hU : blockU (⊥ : Subgroup G) = ⊥ := by
      unfold blockU
      exact Subgroup.commutator_bot_right _
    rw [hU] at h
    exact not_lt_bot h
  have hBK : B ≤ K := by
    set N : Subgroup ↥B := K.subgroupOf B with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      show ((g : G) * n * (g : G)⁻¹) ∈ K
      exact (Subgroup.mem_normalizer_iff.mp (hXN (hBX g.2)) n).mp hn
    have hp : IsPGroup 2 (↥B ⧸ N) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨k, hk⟩ := hX2 b (hBX b.2)
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hk
    have htop := hres N hp
    intro b hb
    have : (⟨b, hb⟩ : ↥B) ∈ N := htop ▸ Subgroup.mem_top _
    exact this
  have hBsnK : (B.subgroupOf K).IsSubnormal := by
    have h := hBsn.comap (Subgroup.inclusion hKX)
    have e : (B.subgroupOf X).comap (Subgroup.inclusion hKX) = B.subgroupOf K := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [e] at h
  rcases hBsnK.lt_normal with htop | ⟨N, hNn, hBN, hNlt⟩
  · refine le_antisymm hBK fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ B.subgroupOf K := htop ▸ Subgroup.mem_top _
    exact this
  · exfalso
    set Q := CFSG.pCore 2 ↥K with hQ
    have hNQ : (N.map (QuotientGroup.mk' Q)).Normal := hNn.map _ (QuotientGroup.mk'_surjective Q)
    rcases hNQ.eq_bot_or_eq_top with hbot | htop
    ·
      have hNle : N ≤ Q := by
        intro n hn
        have : QuotientGroup.mk' Q n ∈ N.map (QuotientGroup.mk' Q) := Subgroup.mem_map_of_mem _ hn
        rw [hbot, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff n).mp this
      have hB2 : IsPGroup 2 ↥B := by
        intro b
        have hbQ : (⟨b, hBK b.2⟩ : ↥K) ∈ Q := hNle (hBN b.2)
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hbQ⟩
        refine ⟨k, Subtype.ext ?_⟩
        have := congrArg (fun x : ↥Q => ((x : ↥K) : G)) hk
        simpa using this
      have hbot' := hres ⊥ (by
        intro q
        induction q using QuotientGroup.induction_on with
        | H b =>
          obtain ⟨k, hk⟩ := hB2 b
          exact ⟨k, by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]⟩)
      apply hB1
      rw [eq_bot_iff]
      intro b hb
      have : (⟨b, hb⟩ : ↥B) ∈ (⊥ : Subgroup ↥B) := hbot'.symm ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    ·
      have hNK : N.map K.subtype = K := by
        refine hKres _ (Subgroup.map_subtype_le N) ?_ fun x hx => ?_
        · have e : (N.map K.subtype).subgroupOf K = N :=
            Subgroup.comap_map_eq_self_of_injective K.subtype_injective N
          rw [e]
          exact hNn
        · have hxm : QuotientGroup.mk' Q (⟨x, hx⟩ : ↥K) ∈ N.map (QuotientGroup.mk' Q) := by
            rw [htop]; exact Subgroup.mem_top _
          obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxm
          have hq : n⁻¹ * ⟨x, hx⟩ ∈ Q := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
            have : (QuotientGroup.mk n : ↥K ⧸ Q) = QuotientGroup.mk ⟨x, hx⟩ := hnx
            rw [this, inv_mul_cancel]
          obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hq⟩
          have hk' : (n⁻¹ * ⟨x, hx⟩ : ↥K) ^ 2 ^ k = 1 := by
            have := congrArg Subtype.val hk
            simpa using this
          have hN1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ N) ^ 2 ^ k = 1 := by
            have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ N) =
                QuotientGroup.mk (n⁻¹ * ⟨x, hx⟩) := by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
                (QuotientGroup.eq_one_iff n).mpr hn, inv_one, one_mul]
            rw [h1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hN1
          exact ⟨k, ⟨_, hN1, rfl⟩⟩
      apply hNlt.ne
      rw [eq_top_iff]
      intro k _
      have hk : (k : G) ∈ N.map K.subtype := hNK.symm ▸ k.2
      obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp hk
      have : n = k := Subtype.ext hnk
      exact this ▸ hn

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem le_borel_sup_of_lt {Y : Subgroup G} (hTY : T ≤ Y) (hY : Y < L ⊔ T) :
    Y ≤ borelOf L T ⊔ T := by
  have hR := S.rankOneAt_L
  have hYL : Y ⊓ L ≠ L := by
    intro h
    apply hY.ne
    refine le_antisymm hY.le (sup_le ?_ hTY)
    rw [← h]
    exact inf_le_left
  have hle : Y ⊓ L ≤ borelOf L T :=
    le_inf inf_le_right (hR.unique_max (Y ⊓ L) (le_inf (inf_le_left.trans hTY) inf_le_right)
      inf_le_right hYL)
  intro y hy
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL
  have hy' : y ∈ (L : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hY.le hy
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hy'
  have hlY : l ∈ Y := by
    have e : l = (l * t) * t⁻¹ := by group
    rw [e]
    exact Y.mul_mem hy (Y.inv_mem (hTY ht))
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hle ⟨hlY, hl⟩)) (Subgroup.mem_sup_right ht)

theorem T_le_normalizer_borelOf : T ≤ Subgroup.normalizer (borelOf L T : Set G) := by
  intro t ht
  have htL : t ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL ht
  have htTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htL x).mp hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL x).mpr hxL⟩
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
  have htN : t ∈ Subgroup.normalizer
      (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) : Set G) := Subgroup.le_normalizer htTL
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxN⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp htL x).mp hxL,
      (Subgroup.mem_normalizer_iff.mp htN x).mp hxN⟩
  · rintro ⟨hxL, hxN⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp htL x).mpr hxL,
      (Subgroup.mem_normalizer_iff.mp htN x).mpr hxN⟩

theorem borel_sup_lt : borelOf L T ⊔ T < L ⊔ T := by
  refine lt_of_le_of_ne (sup_le_sup inf_le_left le_rfl) fun h => ?_
  apply S.rankOneAt_L.borel_ne
  refine le_antisymm inf_le_left fun l hl => ?_
  have hlBT : l ∈ ((borelOf L T ⊔ T : Subgroup G) : Set G) := by
    rw [h]
    exact Subgroup.mem_sup_left hl
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ T S.T_le_normalizer_borelOf] at hlBT
  obtain ⟨b, hb, t, ht, rfl⟩ := Set.mem_mul.mp hlBT
  have htL : t ∈ L := by
    have e : t = b⁻¹ * (b * t) := by group
    rw [e]
    exact L.mul_mem (L.inv_mem hb.1) hl
  have htN : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        L.mul_mem (L.mul_mem htL hxL) (L.inv_mem htL)⟩
    · rintro ⟨hxT, hxL⟩
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e]
      exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht,
        L.mul_mem (L.mul_mem (L.inv_mem htL) hxL) htL⟩
  have htB : t ∈ borelOf L T := ⟨htL, htN⟩
  exact (borelOf L T).mul_mem hb htB

theorem minParabolic_LT : MinParabolic (L ⊔ T) T (borelOf L T ⊔ T) := by
  refine ⟨S.sylow_LT, fun h => ?_, ?_⟩
  ·
    obtain ⟨g, hgT, hg⟩ := S.frame.K4_T A5Model.pa (Or.inr (Or.inl rfl))
    have hTP : T ≤ pCoreOf 2 (L ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right h S.isPGroup_T
    have hgC : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
      have := hTP hgT
      rw [← S.cLT] at this
      exact this.2
    have h1 := S.frame.rho_eq_one_of_mem g hgC
    rw [hg] at h1
    exact absurd h1 (by decide)
  · rw [isUniqueMaxOver_iff]
    have hmax : IsMaxSubgroupIn (L ⊔ T) (borelOf L T ⊔ T) := by
      refine ⟨S.borel_sup_lt, fun K' hK' hK'X => ?_⟩
      by_contra hne
      exact absurd (S.le_borel_sup_of_lt (le_sup_right.trans hK'.le)
        (lt_of_le_of_ne hK'X hne)) (not_le_of_gt hK')
    refine ⟨hmax, le_sup_right, fun N hN hTN => ?_⟩
    have hNle := S.le_borel_sup_of_lt hTN hN.1
    by_contra hne
    exact S.borel_sup_lt.ne (hN.2 _ (lt_of_le_of_ne hNle hne) S.borel_sup_lt.le)

theorem eq_L_of_isBlock2 {B : Subgroup G} (hB : IsBlock2 (L ⊔ T) B) : B = L := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff L _).1 S.a5
  exact eq_of_isBlock2 le_sup_left (sup_le Subgroup.le_normalizer S.T_le_NL)
    (fun _ hx => C1.exists_pow_mem_of_mem_sup S.isPGroup_T S.T_le_NL hx) S.h13.faithful.2.1
    e.isSimpleGroup hB

theorem isA5Block_of_isChi0Block {B : Subgroup G} (hB : IsChi0Block (L ⊔ T) B) :
    IsBlock2 (L ⊔ T) L ∧ IsAltType L 5 := by
  obtain ⟨hblk, htype⟩ := hB
  have hBL := S.eq_L_of_isBlock2 hblk
  subst hBL
  rcases htype with ⟨n, -, hlin⟩ | h3 | h5
  · exact (S.not_isLin2Type hblk.1 hlin).elim
  · exact absurd (S.eq_five_of_isAltType le_rfl h3) (by norm_num)
  · exact ⟨hblk, h5⟩

theorem c126_LT {C₁ C₂ : Subgroup G → Subgroup G} (h126 : C126Statement C₁ C₂) :
    L ⊔ T ≤ Subgroup.centralizer (C₁ T : Set G) ∨
      L ⊔ T ≤ Subgroup.normalizer (C₂ T : Set G) ∨ (IsBlock2 (L ⊔ T) L ∧ IsAltType L 5) := by
  have hLTH : InH T (L ⊔ T) := ⟨le_sup_right, S.maximal.1.2.2.2⟩
  rcases c126_of_minParabolic h126 (S.charTwo_of_inH hLTH)
      (isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hLTH) S.minParabolic_LT with
    h1 | h2 | ⟨B, hB⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (S.isA5Block_of_isChi0Block hB))

end Setting

end CFSG.Quasithin.H13.A5
