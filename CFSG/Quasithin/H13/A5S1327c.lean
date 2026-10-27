module

public import CFSG.Quasithin.H13.A5S1327b
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517
public import CFSG.Quasithin.Background.B69Comp

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem card_mul_card_le_card_sup {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (h : A ⊓ B = ⊥) : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : X) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have e : (a : X) * b = a' * b' := congrArg Subtype.val hab
  have h1 : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
    calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
      _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [e]
      _ = b' * (b : X)⁻¹ := by group
  have hmem : (a' : X)⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [h, Subgroup.mem_bot] at hmem
  have ha : (a : X) = a' := by
    calc (a : X) = a' * ((a' : X)⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one]
  have hb : (b : X) = b' := by
    have := e
    rw [ha] at this
    exact mul_left_cancel this
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem card_W2 : Nat.card ↥W2 = 4 := by
  have : Fintype.card {x : W5 // InW2 x} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem card_V2 : Nat.card ↥S.V2 = 4 := by
  rw [V2, S.card_pre, card_W2]

theorem inf_centralizer_eq_bot_of_center {H : Subgroup G} (hTH : T ≤ H)
    (hZH : centerOf H = ⊥) : T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
  set N := T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hN
  have hNT : N ≤ T := inf_le_left
  have hTO : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hn : (N.subgroupOf T).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr fun t ht => ?_
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · refine ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), ?_⟩
      exact conj_mem_centralizer_of_mem_normalizer (hTO ht) hx.2
    · refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
      have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ (hTO ht)) hx.2
      rwa [inv_inv] at this
  by_contra hne
  have hne' : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNT hx⟩ : ↥T) ∈ N.subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent ↥T := S.isPGroup_T.isNilpotent
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N.subgroupOf T) hne'
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
  have hwN : ((w : ↥T) : G) ∈ N := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp w.2).1
  have hwT : ((w : ↥T) : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp w.2).2 ⟨t, ht⟩)
  have hwC : ((w : ↥T) : G) ∈ centerOf H := by
    refine ⟨hTH (w : ↥T).2, ?_⟩
    have hle : oTwoUpper H ⊔ T ≤
        Subgroup.centralizer ((Subgroup.zpowers ((w : ↥T) : G) : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hwN).2)
      · exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hwT)
    have h1 := Subgroup.le_centralizer_iff.mp hle (Subgroup.mem_zpowers ((w : ↥T) : G))
    rwa [← eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hTH)] at h1
  rw [hZH, Subgroup.mem_bot] at hwC
  exact hw1 (Subtype.ext (Subtype.ext hwC))

theorem o2H0One (h331 : Stmt3_3_1) (h5172 : Stmt5_1_7_two)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    pCoreOf 2 (S.H0 H) ≠ ⊥ := by
  classical
  intro hO2
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hV := S.isCh5Module
  have hTH : T ≤ H := hH.1.1
  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨-, hLHJ, hiii⟩ := h5172 G T M L V H 2 h501 hV hH hZH'
  have hZH : centerOf H = ⊥ := (hiii.resolve_left fun h => h hO2).2.2
  have hN := S.inf_centralizer_eq_bot_of_center hTH hZH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  have hZU : quasithinOmegaOneCenter T ≤ S.UH H := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (S.UH H : Set G) := by
    intro hJ
    have h1 := (hMP.le_pCoreOf_iff_le_centralizer hUred hHU (thompsonJ T)).mpr
      (le_inf (thompsonJ_le_self T) hJ)
    have h2 := (hMP.commutator_lt_iff_le_pCoreOf (thompsonJ_le_self T)
      (B2F.R_le_normalizer_thompsonJ T)).mpr h1
    rw [twoResidual_eq_oTwoUpper', ← hLHJ] at h2
    exact lt_irrefl _ h2
  obtain ⟨-, I, hIcard, hJH, -, hind, -, hnat, hsup, -, -⟩ :=
    E2_3_one_of_isSolvable hUel hMP hsolv hSQT hUred hJ
  obtain ⟨-, -, -, hE, -⟩ := E2_3_two_of_isSolvable hUel hMP hsolv hSQT hUred hJ
  rw [twoResidual_eq_oTwoUpper'] at hE hsup
  have hEle : omegaOneCenterOf (thompsonJ T) ≤ T :=
    (A4.omegaOneCenterOf_le _).trans (thompsonJ_le_self T)
  have hEC : omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ :=
    le_bot_iff.mp (hN ▸ inf_le_inf_right _ hEle)
  rw [hEC, sup_bot_eq] at hE
  have hfix : fixV (autI hUel (oTwoUpper H)) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have huT : u.val ∈ T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨(hUO.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))) u.val_mem, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (S.UH H : Set G) :=
        hUred.2.1 (oTwoUpper_le H hx)
      have h1 := hu (convI hUel ⟨x, hxN⟩) (convI_mem_autI hUel hx hxN)
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      calc x * u.val = x * u.val * x⁻¹ * x := by group
        _ = u.val * x := by rw [h2]
    rw [hN, Subgroup.mem_bot] at huT
    exact Subgroup.mem_bot.mpr (IntMod.val_injective huT)
  rw [hfix, bot_sup_eq] at hsup
  obtain ⟨eS3⟩ := hS3
  have hcardH0 : Nat.card ↥(S.HStar H) = 6 := by
    rw [Nat.card_congr eS3.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hcardH : Nat.card ↥(autI hUel H) = 6 := hcardH0
  have hJHle : autI hUel (thompsonJ H) ≤ autI hUel H := autI_mono hUel (thompsonJ_le_self H)
  have hcardL : ∀ L' ∈ I, Nat.card ↥L' = 6 := by
    intro L' hL'
    obtain ⟨e, -, -⟩ := hnat L' hL'
    rw [Nat.card_congr e.toEquiv, B69.card_sl2]
  have hI1 : I.card = 1 := by
    rcases hIcard with h1 | h2
    · exact h1
    · exfalso
      obtain ⟨A, B, hAB, hIAB⟩ := Finset.card_eq_two.mp h2
      have hA : A ∈ I := by rw [hIAB]; exact Finset.mem_insert_self A {B}
      have hB : B ∈ I := by rw [hIAB]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self B)
      have hBA : B ≤ ⨆ L' ∈ I, ⨆ (_ : L' ≠ A), L' :=
        le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => ⨆ (_ : L' ≠ A), L') B hB
          (le_iSup_of_le (Ne.symm hAB) le_rfl)
      have hAB' : A ⊓ B = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_left _ hBA).trans (hind A hA).le)
      have hAI : A ≤ ⨆ L' ∈ I, L' := le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') A hA le_rfl
      have hBI : B ≤ ⨆ L' ∈ I, L' := le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') B hB le_rfl
      have hle : A ⊔ B ≤ autI hUel H := (sup_le hAI hBI).trans (hJH.symm.le.trans hJHle)
      have h36 := card_mul_card_le_card_sup hAB'
      rw [hcardL A hA, hcardL B hB] at h36
      have := Subgroup.card_le_of_le hle
      omega
  obtain ⟨L₀, hIL⟩ := Finset.card_eq_one.mp hI1
  have hL₀ : L₀ ∈ I := by rw [hIL]; exact Finset.mem_singleton_self L₀
  have hsup' : commV L₀ = ⊤ := by
    rw [hIL, Finset.iSup_singleton] at hsup
    exact hsup
  have hcardU : Nat.card ↥(S.UH H) = 4 := by
    obtain ⟨-, φ, -⟩ := hnat L₀ hL₀
    have h1 : Nat.card ↥(commV L₀) = 4 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    rw [hsup'] at h1
    have h2 : Nat.card ↥(⊤ : Subgroup (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel)) =
        Nat.card (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
      Subgroup.card_top
    rw [h1] at h2
    exact h2.symm
  have hlt : S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G) < S.UH H := by
    refine lt_of_le_of_ne inf_le_left fun heq => hJ ?_
    exact Subgroup.le_centralizer_iff.mp (heq ▸ inf_le_right)
  have hdvd : Nat.card ↥(S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ∣ 4 := by
    rw [← hcardU]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne4 : Nat.card ↥(S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ≠ 4 := by
    intro h4
    rw [← hcardU] at h4
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge inf_le_left h4.ge)
  have hE2 : Nat.card ↥(omegaOneCenterOf (thompsonJ T)) ≤ 2 := by
    rw [hE]
    show Nat.card ↥(S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ≤ 2
    have hmem : Nat.card ↥(S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ∈
        Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have := Subgroup.card_le_of_le S.V2_le_omegaOneCenter_J
  rw [S.card_V2] at this
  omega

end Setting

theorem o2H0One1327_of (h331 : Stmt3_3_1) (h5172 : Stmt5_1_7_two) :
    O2H0One1327 := fun _ _ _ _ _ _ S _ hH hHZ hsolv hS3 => S.o2H0One h331 h5172 hH hHZ hsolv hS3

end CFSG.Quasithin.H13.A5
