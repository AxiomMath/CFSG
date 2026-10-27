module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

namespace Sec1219Odd

variable {G : Type} [Group G] [Finite G]

theorem exists_isHStar_le {S M X : Subgroup G} (hX : InH S X) (hXM : ¬ X ≤ M) :
    ∃ H : Subgroup G, IsHStar S M H ∧ H ≤ X := by
  obtain ⟨H, ⟨hH1, hH2, hHX⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH S H ∧ ¬ H ≤ M ∧ H ≤ X} ⟨X, hX, hXM, le_rfl⟩
  refine ⟨H, ⟨hH1, hH2, fun Y hY hYH hYM => ?_⟩, hHX⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM, hYH.trans hHX⟩ (lt_of_le_of_ne hYH hne)

theorem minParabolic_of_isHStar {S M H : Subgroup G} (hH : IsHStar S M H)
    (hS : IsSylowTwoOf S H) (hSM : S ≤ M) (hNS : Subgroup.normalizer (S : Set G) ≤ M) :
    MinParabolic H S (H ⊓ M) := by
  have hSH : S ≤ H := hH.1.1
  have hlt : H ⊓ M < H := lt_of_le_of_ne inf_le_left fun h => hH.2.1 (h ▸ inf_le_right)
  have hinH : ∀ Y : Subgroup G, S ≤ Y → Y ≤ H → InH S Y := by
    intro Y hSY hYH
    refine ⟨hSY, fun h => hH.1.2 (le_bot_iff.mp ?_)⟩
    rw [← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hS).trans hSY)
      (hYH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have key : ∀ Y : Subgroup G, S ≤ Y → Y < H → Y ≤ H ⊓ M := by
    intro Y hSY hYH
    refine le_inf hYH.le ?_
    by_contra hYM
    exact hYH.ne (hH.2.2 Y (hinH Y hSY hYH.le) hYH.le hYM)
  refine ⟨hS, fun h => hH.2.1 (h.trans hNS), ?_⟩
  have hmax : IsMaxSubgroupIn H (H ⊓ M) := by
    refine ⟨hlt, fun K hK hKH => ?_⟩
    by_contra hne
    exact (lt_irrefl _) (lt_of_lt_of_le hK
      (key K ((le_inf hSH hSM).trans hK.le) (lt_of_le_of_ne hKH hne)))
  rw [isUniqueMaxOver_iff]
  refine ⟨hmax, le_inf hSH hSM, fun N hN hSN => ?_⟩
  have hNle : N ≤ H ⊓ M := key N hSN hN.1
  by_contra hne
  exact hlt.ne (hN.2 (H ⊓ M) (lt_of_le_of_ne hNle hne) inf_le_left)

theorem exists_of_sylow (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1)
    (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hE : E2.E22StatementC) {T L V V₁ V₂ : Subgroup G} {n : ℕ} (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {U : Subgroup G} (hUV : U ≤ V) (hU1 : U ≠ ⊥)
    (hUM : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hTU : IsSylowTwoOf (T ⊓ Subgroup.centralizer (U : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G))) :
    ∃ X : Subgroup G,
      X ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ∧ X ≠ ⊥ ∧
        Odd (Nat.card X) ∧
          ¬ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  set TU := T ⊓ Subgroup.centralizer (U : Set G) with hTUdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hVT := Sec1215.le_of_hyp121 hyp hTL
  have huniqQ : IsUniqueM (Subgroup.normalizer (Q : Set G)) M :=
    Sec1215.isUniqueM_of_hyp121 h331 hyp hTL
  have hT : IsSylowIn 2 T ⊤ :=
    ⟨le_top, hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hyp.sylow.2⟩
  have hQTU : Q ≤ TU := inf_le_inf_left T (Subgroup.centralizer_le hUV)
  have hTU2 : IsPGroup 2 TU := hyp.sylow.1.to_le inf_le_left
  have hQ2 : IsPGroup 2 Q := hyp.sylow.1.to_le inf_le_left
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ n hyp hTL).2
  have hs : sParam hVe = 2 :=
    ((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ n β hyp hβ).2 hVe |>.2.1
  have hrk : 2 ≤ rk ↥V := hs ▸ sParam_le_rk hVe
  have hWQ : ∀ i, i ≤ 1 → wClos V i TU ≤ Q ∧ wClos V i TU ≠ ⊥ := by
    intro i hi
    have hWT : wClos V i T ≤ Q := by
      interval_cases i
      · exact h1217 G T L V V₁ V₂ n hyp
      · exact h1218 G T L V V₁ V₂ n hyp
    have heq := e3_15 hT le_top hTU2 (hWT.trans hQTU)
    rw [← heq]
    exact ⟨hWT, wClos_ne_bot hVe hVT (by omega)⟩
  have hTUs : IsSylowIn 2 TU TU := ⟨le_rfl, hTU2, by rw [Subgroup.relIndex_self]; norm_num⟩
  have hN0 : Subgroup.normalizer (wClos V 0 TU : Set G) ≤ M :=
    (e3_16_one hTUs hQTU hQ2 (hWQ 0 (by norm_num)).1 (hWQ 0 (by norm_num)).2 huniqQ).2
  have hC : ∀ i, i ≤ 1 → Subgroup.centralizer (cClos V i TU : Set G) ≤ M := fun i hi =>
    e3_16_three hTUs hQTU hQ2 (hWQ i hi).1 (hWQ i hi).2 huniqQ
  have hNTU : Subgroup.normalizer (TU : Set G) ≤ M :=
    (normalizer_le_normalizer_wClos TU).trans hN0
  have hTUGU : IsSylowTwoOf TU (Subgroup.centralizer (U : Set G)) :=
    Sec1215.isSylowTwoOf_of_normalizer_le inf_le_right hNTU (by rw [inf_comm]; exact hTU)
  have hUQ : U ≤ pCoreOf 2 (Subgroup.centralizer (U : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
      (Subgroup.centralizer_le_normalizer _) (hyp.sylow.1.to_le (hUV.trans hVT))
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    exact congrArg Subtype.val (hVe.1.1.comm ⟨u', hUV hu'⟩ ⟨u, hUV hu⟩)
  have hGU : InH TU (Subgroup.centralizer (U : Set G)) :=
    ⟨inf_le_right, fun h => hU1 (le_bot_iff.mp (h ▸ hUQ))⟩
  obtain ⟨H, hH, hHGU⟩ := exists_isHStar_le hGU hUM
  have hTUH : IsSylowTwoOf TU H := Sec1215.isSylowTwoOf_of_le_of_le hTUGU hH.1.1 hHGU
  have hmin := minParabolic_of_isHStar hH hTUH (inf_le_left.trans hTL) hNTU
  have hn1 : 1 < E1.nParam H := by
    by_contra hle
    push Not at hle
    obtain ⟨j, hj⟩ : ∃ j : ℕ, E1.nParam H = j :=
      ⟨(E1.nParam H).toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hle)).symm⟩
    have hj1 : j ≤ 1 := by
      rw [hj] at hle
      exact_mod_cast hle
    have hgen := e3_19 hVe hTUH (i := 0) hj (by omega)
    apply hH.2.1
    rw [← hgen, zero_add]
    exact sup_le (inf_le_right.trans (hC j hj1)) (inf_le_right.trans hN0)
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH.1.2
  obtain ⟨m, hm, -, hB⟩ :=
    E2.e22BorelLift hE (E2.e22TorusCover_of_facts e22TorusFacts_holds) hmin hSQ hn1
  obtain ⟨-, R, -, -, -, ⟨C, hCM, hCodd, hCidx⟩, hall⟩ := hB
  obtain ⟨-, -, -, Y, hYC, -, hYcard, hYN⟩ := hall C hCM hCodd hCidx
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hY1 : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    omega
  refine ⟨Y, le_inf ((hYC.trans hCM).trans inf_le_right)
    ((hYC.trans hCM).trans (inf_le_left.trans hHGU)), hY1, ?_, fun hNY => ?_⟩
  · rw [hYcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  · exact hYN Y le_rfl hY1 fun h hh => ⟨hh.1, hNY hh.2⟩

omit [Finite G] in
theorem normalizer_cjSub (g : G) (X : Subgroup G) :
    Subgroup.normalizer (cjSub g X : Set G) = cjSub g (Subgroup.normalizer (X : Set G)) :=
  (Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)).symm

end Sec1219Odd

open Sec1219Odd

theorem lem1219OddLocal_of (h1001 : Stmt10_0_1)
    (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hE : E2.E22StatementC) : Lem1219OddLocal := by
  intro G _ _ T L V V₁ V₂ n hyp hTL U hUV hU1 hUM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
    obtain ⟨hn, -⟩ := hyp.reduced
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hyp.le).mp hn
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTL
  obtain ⟨P, hP⟩ := exists_isSylowTwoOf (M ⊓ Subgroup.centralizer (U : Set G))
  obtain ⟨h, hhM, hhP⟩ := exists_conj_le_of_isSylowTwoOf hTM (hP.1.trans inf_le_left) hP.2.1
  have hMh : ∀ g ∈ M, cjSub g M = M := fun g hg =>
    B2F.cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hCU : cjSub h (Subgroup.centralizer (U : Set G)) =
      Subgroup.centralizer (cjSub h U : Set G) := B2F.cjSub_centralizer h U
  have hU'V : cjSub h U ≤ V := cjSub_le (hMV hhM) hUV
  have hU'1 : cjSub h U ≠ ⊥ := by
    intro h1
    apply hU1
    rw [← cjSub_inv_cjSub h U, h1]
    exact Subgroup.map_bot _
  have hU'M : ¬ Subgroup.centralizer (cjSub h U : Set G) ≤ M := by
    intro hle
    apply hUM
    have h1 := cjSub_mono (g := h⁻¹) hle
    rwa [← hCU, cjSub_inv_cjSub, hMh h⁻¹ (M.inv_mem hhM)] at h1
  have hSyl' : IsSylowTwoOf (cjSub h P) (M ⊓ Subgroup.centralizer (cjSub h U : Set G)) := by
    have h1 := B2F.isSylowTwoOf_cjSub h hP
    rwa [B2F.cjSub_inf, hMh h hhM, hCU] at h1
  have hTU' : IsSylowTwoOf (T ⊓ Subgroup.centralizer (cjSub h U : Set G))
      (M ⊓ Subgroup.centralizer (cjSub h U : Set G)) := by
    have hle : cjSub h P ≤ T ⊓ Subgroup.centralizer (cjSub h U : Set G) :=
      le_inf hhP (hSyl'.1.trans inf_le_right)
    have h2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (cjSub h U : Set G)) :=
      hyp.sylow.1.to_le inf_le_left
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp hSyl').2.2 _
      (inf_le_inf_right _ hTL) h2 hle
    rwa [le_antisymm hmax hle]
  obtain ⟨X', hX'MU, hX'1, hX'odd, hX'N⟩ :=
    exists_of_sylow h1001 h331 h1211 hH91 h1217 h1218 hE hyp hTL hU'V hU'1 hU'M hTU'
  refine ⟨cjSub h⁻¹ X', ?_, ?_, ?_, fun hN => hX'N ?_⟩
  · have h1 := cjSub_mono (g := h⁻¹) hX'MU
    rwa [B2F.cjSub_inf, ← hCU, cjSub_inv_cjSub, hMh h⁻¹ (M.inv_mem hhM)] at h1
  · intro h1
    apply hX'1
    rw [← cjSub_cjSub_inv h X', h1]
    exact Subgroup.map_bot _
  · rw [card_cjSub]
    exact hX'odd
  · have h1 := cjSub_mono (g := h) hN
    rwa [← normalizer_cjSub, cjSub_cjSub_inv, hMh h hhM] at h1

end CFSG.Quasithin.H13
