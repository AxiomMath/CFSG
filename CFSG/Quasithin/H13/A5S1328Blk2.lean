module

public import CFSG.Quasithin.H13.A5S1328Blk1
public import CFSG.Quasithin.H13.A5S1327zd
public import CFSG.Quasithin.Background.C118NoOuter
public import CFSG.Quasithin.Background.C1CampbellConnect
public import CFSG.Quasithin.H13.A5S1328Sym1

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (h : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (Y : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  set N := T ⊓ Subgroup.centralizer (Y : Set G) with hNdef
  have hNT : N ≤ T := inf_le_left
  have hn : (N.subgroupOf T).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr fun t ht => ?_
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · refine ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), ?_⟩
      exact conj_mem_centralizer_of_mem_normalizer (hTY ht) hx.2
    · refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
      have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ (hTY ht)) hx.2
      rwa [inv_inv] at this
  by_contra hne
  have hne' : N.subgroupOf T ≠ ⊥ := by
    intro h'
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNT hx⟩ : ↥T) ∈ N.subgroupOf T := hx
    rw [h', Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N.subgroupOf T) hne'
  have hWp : IsPGroup 2 ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) := hT.to_subgroup _
  obtain ⟨w, hw2⟩ : ∃ w : ↥(N.subgroupOf T ⊓ Subgroup.center ↥T), orderOf w = 2 := by
    have h1 : 1 < Nat.card ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hW
    obtain ⟨k, hk⟩ := hWp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, pow_zero] at h1
      exact lt_irrefl _ h1
    exact exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hw1 : ((w : ↥T) : G) ≠ 1 := by
    intro h'
    have : w = 1 := Subtype.ext (Subtype.ext h')
    rw [this, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hwsq : ((w : ↥T) : G) ^ 2 = 1 := by
    have h1 : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
    have h2 := congrArg (fun x : ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) => ((x : ↥T) : G)) h1
    simpa using h2
  have hwN : ((w : ↥T) : G) ∈ N := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp w.2).1
  have hwZ : ((w : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    refine mem_quasithinOmegaOneCenter_iff.mpr ⟨(w : ↥T).2, ?_, hwsq⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp w.2).2 ⟨t, ht⟩)
  have hmem : ((w : ↥T) : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (Y : Set G) :=
    ⟨hwZ, hwN.2⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hw1 hmem

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

omit S in
theorem mem_V1_of (h512 : Stmt5_1_2) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) {y : G}
    (hy : y ∈ quasithinOmegaOneCenter T) : y = 1 ∨ y = S'.z := by
  obtain ⟨v, hv, c, hc, rfl⟩ := S'.Z_decomp h512 hJK hy
  have hvZ : v ∈ quasithinOmegaOneCenter T := by
    rcases S'.mem_V1.1 hv with rfl | rfl
    · exact Subgroup.one_mem _
    · exact S'.z_mem_omegaOneCenter
  have hcZ : c ∈ quasithinOmegaOneCenter T := by
    have e : c = v⁻¹ * (v * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvZ) hy
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hc
  have hc1 : c = 1 := by
    have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) := ⟨hcZ, hcK⟩
    rwa [hZK, Subgroup.mem_bot] at this
  rw [hc1, mul_one]
  exact S'.mem_V1.1 hv

theorem z_eq_of (h512 : Stmt5_1_2) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) : S.z = S'.z :=
  (mem_V1_of h512 S' hJK hZK S.z_mem_omegaOneCenter).resolve_left S.z_ne_one

theorem mem_omegaOneCenter_of (h512 : Stmt5_1_2) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) {x : G}
    (hx : x ∈ quasithinOmegaOneCenter T) : x = 1 ∨ x = S.z := by
  rw [S.z_eq_of h512 S' hJK hZK]
  exact mem_V1_of h512 S' hJK hZK hx

theorem isA5Block_or_isA5Block (h331 : Stmt3_3_1) (h512 : Stmt5_1_2)
    (h5172 : Stmt5_1_7_two) (h126 : TheoremC126) {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hHK : H = K ⊔ T)
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    (IsBlock2 (K ⊔ T) K ∧ IsAltType K 5) ∨ (IsBlock2 (L ⊔ T) L ∧ IsAltType L 5) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  have hT0 : T ≠ ⊥ := by
    intro h
    exact S.z_ne_one (Subgroup.mem_bot.mp (h.le (S.V_le_T S.z_mem_V)))
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, -, -⟩ := hC.pair T S.isPGroup_T hT0
  have hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ (by rw [Setting.UH, hHK]; exact hJ)
  have hZz : ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = S.z :=
    fun x hx => S.mem_omegaOneCenter_of h512 S' hJK hZK hx
  have hzC₁ : S.z ∈ C₁ T := by
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := C₁ T)).1 h1ne
    rcases hZz c (h1Z c.2) with h | h
    · exact absurd (Subtype.ext h) hc1
    · rw [← h]; exact c.2
  have hC₂2 : IsPGroup 2 ↥(C₂ T) := S.isPGroup_T.to_le (h2B.trans (C1GN.baum_le T))
  have hHH : InH T H := hH.1
  have hmpH : MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) :=
    (S.hyp501.minParabolic_of_isHStar h331 hH).1
  have hH1 : (H ≤ Subgroup.normalizer (C₂ T : Set G)) ∨ (IsBlock2 (K ⊔ T) K ∧ IsAltType K 5) := by
    rcases c126_of_minParabolic (h126 G C₁ C₂ hC) (S.charTwo_of_inH hHH)
        (isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hHH) hmpH with
      h1 | h2 | ⟨B, hB⟩
    · exfalso
      apply hHZ
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hZz x hx with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_iff.mp (h1 hh) _ hzC₁)
    · exact Or.inl h2
    · right
      rw [hHK] at hB
      obtain ⟨hblk, htype⟩ := hB
      have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨e⟩ := (quasithinO2QuotientIso_iff K _).1 S'.a5
      have hBK : B = K := eq_of_isBlock2 le_sup_left (sup_le Subgroup.le_normalizer S'.T_le_NL)
        (fun _ hx => C1.exists_pow_mem_of_mem_sup S.isPGroup_T S'.T_le_NL hx)
        S'.h13.faithful.2.1 e.isSimpleGroup hblk
      subst hBK
      rcases htype with ⟨n, -, hlin⟩ | h3 | h5
      · exact (S'.not_isLin2Type hblk.1 hlin).elim
      · exact absurd (S'.eq_five_of_isAltType le_rfl h3) (by norm_num)
      · exact ⟨hblk, h5⟩
  have hL1 : (L ⊔ T ≤ Subgroup.normalizer (C₂ T : Set G)) ∨
      (IsBlock2 (L ⊔ T) L ∧ IsAltType L 5) := by
    rcases S.c126_LT (h126 G C₁ C₂ hC) with h1 | h2 | h3
    · exfalso
      have hzC : S.z ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_sup_left hl)) _ hzC₁).symm
      have hzL : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hzC⟩
      rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzL
      exact S.z_ne_one hzL
    · exact Or.inl h2
    · exact Or.inr h3
  rcases hH1 with hHN | hK
  · rcases hL1 with hLN | hLb
    · exfalso
      have hloc : IsTwoLocal (Subgroup.normalizer (C₂ T : Set G)) := ⟨C₂ T, h2ne, hC₂2, rfl⟩
      obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
      have hM'eq : M' = Subgroup.normalizer (L : Set G) := S.uniqueM.2 M' ⟨hM', hLN.trans hle⟩
      exact hH.2.1 (hM'eq ▸ hHN.trans hle)
    · exact Or.inr hLb
  · exact Or.inl hK

theorem pCoreOf_KT_eq (h331 : Stmt3_3_1) (h512 : Stmt5_1_2)
    (h5172 : Stmt5_1_7_two) (h126 : TheoremC126) {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hHK : H = K ⊔ T)
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    pCoreOf 2 (K ⊔ T) = VH := by
  have hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ (by rw [Setting.UH, hHK]; exact hJ)
  have hZz : ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = S.z :=
    fun x hx => S.mem_omegaOneCenter_of h512 S' hJK hZK hx
  rcases S.isA5Block_or_isA5Block h331 h512 h5172 h126 S' hH hHZ hHK hZK with
    ⟨hblk, h5⟩ | ⟨hblk, h5⟩
  ·
    have hCTK := inf_centralizer_eq_bot_of S.isPGroup_T S'.T_le_NL hZK
    exact le_antisymm (S'.pCoreOf_LT_le_V hblk h5 hCTK) S'.V_le_pCoreOf_LT
  ·
    have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxZ, hxL⟩
      rw [Subgroup.mem_bot]
      rcases hZz x hxZ with h | rfl
      · exact h
      · have hzb : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hxL⟩
        rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzb
        exact hzb
    have hCTL := inf_centralizer_eq_bot_of S.isPGroup_T S.T_le_NL hZL
    have hO : pCoreOf 2 (L ⊔ T) = V :=
      le_antisymm (S.pCoreOf_LT_le_V hblk h5 hCTL) S.V_le_pCoreOf_LT
    obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
      S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
    have hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1 :=
      ⟨j, thompsonJ_le_self T hjJ, by
        rw [show (⟨j, S.frame.T_le (thompsonJ_le_self T hjJ)⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = ⟨j, hjN⟩ from rfl, hj]
        decide⟩
    have hcardT : Nat.card ↥T = 128 := by
      rw [S.card_T_eq hodd, hO, S.card_V]
    have hUV : S.UH H ≤ VH := by
      unfold Setting.UH
      rw [hHK]
      refine conjClosure_le fun h hh x hx => ?_
      have hxV : x ∈ VH := by
        rcases hZz x hx with rfl | rfl
        · exact Subgroup.one_mem _
        · rw [S.z_eq_of h512 S' hJK hZK]
          exact S'.z_mem_V
      have hhN : h ∈ Subgroup.normalizer (VH : Set G) :=
        (sup_le S'.frame.L_le S'.frame.T_le) hh
      exact (Subgroup.mem_normalizer_iff.mp hhN x).mp hxV
    have hJVH : ¬ thompsonJ T ≤ Subgroup.centralizer (VH : Set G) := fun hJ =>
      S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ
        (hJ.trans (Subgroup.centralizer_le hUV))
    obtain ⟨⟨j', hjJ', hjN', hj'⟩, -⟩ := S'.lemma_13_2_4_two_b hJVH
    have hodd' : ∃ (t : G) (ht : t ∈ T), (S'.frame.ρ ⟨t, S'.frame.T_le ht⟩).sign ≠ 1 :=
      ⟨j', thompsonJ_le_self T hjJ', by
        rw [show (⟨j', S'.frame.T_le (thompsonJ_le_self T hjJ')⟩ :
          ↥(Subgroup.normalizer (VH : Set G))) = ⟨j', hjN'⟩ from rfl, hj']
        decide⟩
    have hcard : Nat.card ↥(pCoreOf 2 (K ⊔ T)) = 16 := by
      have := S'.card_T_eq hodd'
      omega
    exact (Subgroup.eq_of_le_of_card_ge S'.V_le_pCoreOf_LT (by rw [hcard, S'.card_V])).symm

end Setting

end CFSG.Quasithin.H13.A5
