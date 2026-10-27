module

public import CFSG.Quasithin.Vol2.Ch12Sec6L22
public import CFSG.Quasithin.Background.E3Nlow
public import CFSG.Quasithin.Vol2.Ch12Sec6L20e

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

namespace S126L23a

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem basics (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ IsElemAbelian 2 V ∧ V ≠ ⊥ ∧
      (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, hMV, -⟩ := hall V hyp.irrPlus
  have hVe : IsElemAbelian 2 V := S126L1b.isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  have hV1 : V ≠ ⊥ := by
    intro h
    have h1 := S126L20.card_V F
    have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
    rw [h, Subgroup.card_bot] at h1
    omega
  exact ⟨hVT, hTV, hVe, hV1, hMV⟩

theorem centralizer_Z_le (h1222 : Stmt12_2_2) (h1229 : Stmt12_2_9) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  obtain ⟨hVT, -, hVe, -, -⟩ := basics h1222 F hH
  obtain ⟨-, heq⟩ := S126L1c.part2 h1222 hH hZ
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hzT : (z : G) ∈ V ⊓ Subgroup.centralizer (T : Set G) := heq ▸ z.2
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨z, Subgroup.subset_closure ⟨⟨hVT hzT.1, hzT.2⟩, hVe.2 _ hzT.1⟩, z.2.2⟩, ?_⟩
    intro h
    apply hz1
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  exact (h1229 G T L V hH.hyp).1 hZL

omit [IsMulCommutative ↥V] in
theorem stmt331 (h331 : Stmt3_3_1) (hH : Hyp126 G T L V) :
    (quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G)) ∧
        L ⊔ T ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
          M' = Subgroup.normalizer (L : Set G)) ∧
      (∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H) ∧
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
        IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
  have hyp := hH.hyp
  have h := (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal
    hyp.quasisimple
  rw [hyp.conjClosure_eq] at h
  obtain ⟨hM, -, hex, -, hmax⟩ := h
  exact ⟨hM, hex, fun H hH' => (hmax H hH').1⟩

theorem isUniqueM_Q (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  have hyp := hH.hyp
  obtain ⟨hVT, hTV, hVe, hV1, -⟩ := basics h1222 F hH
  obtain ⟨⟨hM, -, huniq⟩, -, -⟩ := stmt331 h331 hH
  have hVcl : conjClosure V T = V :=
    le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (hTV ht) _).mp hz)
      (le_conjClosure V T)
  obtain ⟨-, -, hO⟩ := h3228 G T L V hyp.fsu
  rw [hyp.conjClosure_eq, hVcl] at hO
  have hLT : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hO]
    exact LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hVQ : V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf hVT fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    ⟨T ⊓ Subgroup.centralizer (V : Set G), fun hb => hV1 (le_bot_iff.1 (hb ▸ hVQ)),
      hyp.sylow.1.to_le inf_le_left, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := huniq M' hM' (hLT.trans hle)
  exact ⟨⟨hM, hM'eq ▸ hle⟩, fun M'' hM'' => huniq M'' hM''.1 (hLT.trans hM''.2)⟩

omit [IsMulCommutative ↥V] in
theorem isSylowIn_top (hH : Hyp126 G T L V) : IsSylowIn 2 T ⊤ :=
  ⟨le_top, hH.hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hH.hyp.sylow.2⟩

omit [IsMulCommutative ↥V] in
theorem isSylowIn_of_le (hH : Hyp126 G T L V) {H : Subgroup G} (hTH : T ≤ H) :
    IsSylowIn 2 T H :=
  ⟨hTH, hH.hyp.sylow.1, fun h2 => hH.hyp.sylow.2 (h2.trans
    (by simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem not_solvable (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (hS8 : FactS8ElemAbE8) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) : ¬ Group.IsSolvable ↥H := by
  intro hsol
  obtain ⟨hVT, hTV, hVe, hV1, -⟩ := basics h1222 F hH
  have hw := (lemma12_6_22_of h331 h1222 h1262 h1219 hS8 G T L V F hH hZ).2.2
  have hr := (lemma12_6_20_of h331 h1222 h1262 h1219 G T L V F hH).2.2 hZ
  have h1 : 1 < min (E3.wParam T V) (E3.rParam V) :=
    lt_min hw (lt_of_lt_of_le (by norm_num) hr)
  have hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S126L20c.normalizer_V_le h331 h1222 F hH))
  exact hHs.2.1 (E3.e3_35_one_solvable hVe hV1 ⟨isSylowIn_top hH, hVT, hTV⟩
    (isUniqueM_Q h331 h3228 h1222 F hH) (isSylowIn_of_le hH hHs.1.1) hCH inf_le_left hsol h1)

theorem exists_A (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2)
    (h1227 : Stmt12_2_7) (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (hS8 : FactS8ElemAbE8)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    ∃ g : G, conjSubgroup V g ≤ T ∧ ¬ conjSubgroup V g ≤ Subgroup.centralizer (VZ T H : Set G) ∧
      conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hVT, hTV, hVe, hV1, -⟩ := basics h1222 F hH
  have hV2 : IsPGroup 2 V := hH.hyp.sylow.1.to_le hVT
  have hW0 := (lemma12_6_22_of h331 h1222 h1262 h1219 hS8 G T L V F hH hZ).1
  have hw := (lemma12_6_22_of h331 h1222 h1262 h1219 hS8 G T L V F hH hZ).2.2
  obtain ⟨⟨-, hCT, -, -⟩, -⟩ := h1227 G T L V H hH.hyp hCZ hHs
  have hgam : ∀ A ∈ E3.gammaSet V 0 T, ∃ g : G, A = conjSubgroup V g ∧ conjSubgroup V g ≤ T := by
    rintro A ⟨hAT, g, hAg, hm⟩
    have hp : IsPGroup 2 (conjSubgroup V g) := S126L22.isPGroup_conj h1222 F hH hZ g
    have hAe : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hp hAg).1 hm
    exact ⟨g, hAe, hAe ▸ hAT⟩
  have hWO : E3.wClos V 0 T ≤ pCoreOf 2 H := by
    rw [← hCT]
    refine iSup₂_le fun A hA => ?_
    obtain ⟨g, rfl, hgT⟩ := hgam A hA
    have hAW : conjSubgroup V g ≤ E3.wClos V 0 T := le_iSup₂_of_le (conjSubgroup V g) hA le_rfl
    refine le_inf hgT ?_
    by_contra hc
    exact hcon g hgT hc (hAW.trans hW0)
  have hOT : pCoreOf 2 H ≤ T := by
    rw [← hCT]
    exact inf_le_left
  have hON : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have key : ∀ h ∈ H, ∀ x ∈ E3.wClos V 0 T, h * x * h⁻¹ ∈ E3.wClos V 0 T := by
    intro h hh x hx
    have hle : E3.wClos V 0 T ≤ (E3.wClos V 0 T).comap (MulAut.conj h).toMonoidHom := by
      refine iSup₂_le fun A hA => ?_
      obtain ⟨g, rfl, hgT⟩ := hgam A hA
      have hAW : conjSubgroup V g ≤ E3.wClos V 0 T :=
        le_iSup₂_of_le (conjSubgroup V g) hA le_rfl
      have hmem : conjSubgroup V (g * h⁻¹) ∈ E3.gammaSet V 0 T := by
        refine ⟨fun y hy => ?_, g * h⁻¹, le_rfl, E3.mQuot_self _⟩
        rw [mem_conjSubgroup_iff] at hy
        have hy' : h⁻¹ * y * h ∈ conjSubgroup V g := by
          rw [mem_conjSubgroup_iff]
          have e : g * (h⁻¹ * y * h) * g⁻¹ = g * h⁻¹ * y * (g * h⁻¹)⁻¹ := by group
          rw [e]
          exact hy
        have h1 : h⁻¹ * y * h ∈ pCoreOf 2 H := hWO (hAW hy')
        have h2 := (Subgroup.mem_normalizer_iff.1 (hON hh) _).1 h1
        rw [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h2
        exact hOT h2
      have hAW' : conjSubgroup V (g * h⁻¹) ≤ E3.wClos V 0 T := le_iSup₂_of_le _ hmem le_rfl
      intro y hy
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine hAW' ?_
      rw [mem_conjSubgroup_iff]
      rw [mem_conjSubgroup_iff] at hy
      have e : g * h⁻¹ * (h * y * h⁻¹) * (g * h⁻¹)⁻¹ = g * y * g⁻¹ := by group
      rw [e]
      exact hy
    have := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hHN : H ≤ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  have hi : 0 < rk ↥V := by
    have hVcard : 1 < Nat.card V := by
      rcases Nat.lt_or_ge 1 (Nat.card V) with h | h
      · exact h
      · exfalso
        exact hV1 (Subgroup.eq_bot_of_card_le V h)
    unfold rk
    obtain ⟨n, hn⟩ := hV2.exists_card_eq
    rw [hn, padicValNat.prime_pow]
    rcases n with _ | n
    · rw [hn] at hVcard
      norm_num at hVcard
    · omega
  have hNW := (E3.e3_34_two hVe ⟨isSylowIn_top hH, hVT, hTV⟩
    (isUniqueM_Q h331 h3228 h1222 F hH) hi (lt_trans (by norm_num) hw)).1
  exact hHs.2.1 (hHN.trans hNW)

end S126L23a

end CFSG.Quasithin.H13
