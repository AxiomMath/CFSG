module

public import CFSG.RankThree.GF2n.Stroth80.Sec10RootFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec101Tt
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec103Three

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem conjSubgroup_inf_eq_bot {P Y : Subgroup G} {c : G} (hcP : c ∈ P) (hYP : Y ⊓ P = ⊥) :
    conjSubgroup c Y ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy, hyP⟩
  have h : c⁻¹ * y * c ∈ Y ⊓ P :=
    ⟨mem_conjSubgroup.mp hy, P.mul_mem (P.mul_mem (P.inv_mem hcP) hyP) hcP⟩
  rw [hYP, Subgroup.mem_bot] at h
  rw [Subgroup.mem_bot]
  calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    _ = 1 := by rw [h]; group

omit [Finite G] in
private theorem ne_of_le_of_inf_eq_bot {X W P : Subgroup G} (hXP : X ≤ P) {x : G} (hx : x ∈ X)
    (hx1 : x ≠ 1) (hW : W ⊓ P = ⊥) : X ≠ W := by
  rintro rfl
  have h : x ∈ X ⊓ P := ⟨hx, hXP hx⟩
  rw [hW, Subgroup.mem_bot] at h
  exact hx1 h

theorem Sec10Hyp.Rt_ne_LB_of_mem_QB_of_ne (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (htM : t ∈ M) {D P : Subgroup G} (hD : Ctx M Q Z D) (hBP : B ≤ P) (hDP : D ≤ P)
    (hPQ : P ≤ Q) (hPZ : P ⊓ Z = ⊥) (hne : B ≠ D) (htD : t ∈ QB D) :
    Rt M (LB M Q B) t ≠ LB M Q B := by
  obtain ⟨μ, hμ, rfl⟩ := H.rootTrans h34 hspread D hD
  exact H.Rt_ne_LB_of_mem_QB h34 hμ
    (hc.hyp.sup_inf_sup_eq hc.conj hD.conj hne hBP hDP hPQ hPZ) htM htD

theorem Good101.mem_normalizer_conj (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) : t ∈ Subgroup.normalizer (conjSubgroup c Y : Set G) := by
  obtain ⟨g, hg⟩ := hs.conj
  have hY' : conjSubgroup c Y = conjSubgroup (c * g) Z := by rw [hg, conjSubgroup_conjSubgroup]
  have hmem : c * t * c⁻¹ ∈ conjSubgroup c Y := mem_conjSubgroup.mpr (by
    rw [show c⁻¹ * (c * t * c⁻¹) * c = t by group]; exact hs.mem)
  have hne : c * t * c⁻¹ ≠ 1 := fun h1 => hs.ne_one (by
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group)
  exact IsZConjugate.mem_normalizer_of_commute hs.hyp ⟨c * g, hY'⟩ hne hmem
    (ht.conj_comm_self h34 H hs hcQ).symm

theorem Good101.not_mem_QB_conj (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hB : ¬ CaseA Q Z t) {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) : t ∉ QB (conjSubgroup c Y) := by
  intro htY
  have hcW' : c⁻¹ ∉ Wt Q (Vt M (LB M Q B) B Z t) := fun h => hcW (by
    simpa using (Wt Q (Vt M (LB M Q B) B Z t)).inv_mem h)
  apply ht.comm_not_mem_Tt h34 H (Q.inv_mem hcQ) hcW'
  apply ht.Vt_le_Tt h34 H
  have hxQ : ⁅t, c⁻¹⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.comm_mem_Q ht.2.1 (Q.inv_mem hcQ))
  have hxU : ⁅t, c⁻¹⁆ ∈ Ut Q Z t := by
    rw [← commutatorElement_inv]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut (Q.inv_mem hcQ))
  have hxY : ⁅t, c⁻¹⁆ ∈ QB Y := by
    rw [QB_conj, mem_conjSubgroup] at htY
    have htY' : t ∈ QB Y := IsZConjugate.le_QB_self hs.hyp hs.conj hs.mem
    have e : ⁅t, c⁻¹⁆ = t * (c⁻¹ * t * c)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (QB Y).mul_mem htY' ((QB Y).inv_mem htY)
  exact ht.inf_QB_inf_Ut_le_Vt_of_not_caseA h34 hspread H hs hB ⟨⟨hxQ, hxY⟩, hxU⟩

private theorem ctx_conj_frame {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q)
    (hc' : Ctx (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
      (conjSubgroup c Y) B) {D : Subgroup G} (hD : Ctx M Q Z D) (hDY : D ≤ QB Y)
    (hDc : D ≤ Subgroup.centralizer ({c} : Set G)) :
    Ctx (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
      (conjSubgroup c Y) D := by
  obtain ⟨g, hg⟩ := hs.conj
  obtain ⟨gD, hgD⟩ := hD.conj
  obtain ⟨d, hd, hd1⟩ := hD.exists_ne_one
  refine ⟨hc'.hyp, ⟨gD * (c * g)⁻¹, ?_⟩, fun x hx => mem_QB_conj_of_mem_centralizer (hDY hx)
    (hDc hx), ne_of_le_of_inf_eq_bot hD.le hd hd1 (conjSubgroup_inf_eq_bot hcQ hs.X_inf_Q)⟩
  rw [hg, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
    show gD * (c * g)⁻¹ * c * g = gD by group, hgD]

theorem Good101.exists_conj_frame (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hB : ¬ CaseA Q Z t) {c : G} (hcQ : c ∈ Q)
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    {D : Subgroup G} (hD : Ctx M Q Z D) (hDY : D ≤ QB Y) (hYD : Y ≤ QB D)
    (hDc : D ≤ Subgroup.centralizer ({c} : Set G)) (hDB : ¬ D ≤ B) :
    ∃ hc' : Ctx (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
      (conjSubgroup c Y) B, Sec10Hyp hc' n ∧
      Good101 (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
        (conjSubgroup c Y) B t ∧
      Sit (Subgroup.normalizer (conjSubgroup c Y : Set G)) (QB (conjSubgroup c Y))
        (conjSubgroup c Y) Y t ∧
      ∃ μ ∈ Subgroup.normalizer (conjSubgroup c Y : Set G), conjSubgroup μ B = D := by
  obtain ⟨g, hg⟩ := hs.conj
  have hY' : conjSubgroup c Y = conjSubgroup (c * g) Z := by rw [hg, conjSubgroup_conjSubgroup]
  have hY'Q := conjSubgroup_inf_eq_bot hcQ hs.X_inf_Q
  have hBY : B ≤ QB Y := hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hBY' : B ≤ QB (conjSubgroup c Y) := fun b hb => mem_QB_conj_of_mem_centralizer (hBY hb)
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcB b hb))
  obtain ⟨b, hb, hb1⟩ := hc.exists_ne_one
  obtain ⟨hc', H'⟩ := H.exists_frame h34 hspread ⟨c * g, hY'⟩ hBY'
    (ne_of_le_of_inf_eq_bot hc.le hb hb1 hY'Q)
  have htN := ht.mem_normalizer_conj h34 H hs hcQ
  have htQ' := ht.not_mem_QB_conj h34 hspread H hs hB hcQ hcW
  have hD' := ctx_conj_frame hs hcQ hc' hD hDY hDc
  have hPZ : Q ⊓ QB (conjSubgroup c Y) ⊓ conjSubgroup c Y = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h : a ∈ conjSubgroup c Y ⊓ Q := ⟨ha.2, ha.1.1⟩
    rwa [hY'Q] at h
  have hRt := H'.Rt_ne_LB_of_mem_QB_of_ne h34 hspread htN hD' (le_inf hc.le hBY')
    (le_inf hD.le hD'.le) inf_le_right hPZ (fun h => hDB (le_of_eq h.symm)) (hYD hs.mem)
  refine ⟨hc', H', ⟨(isRoot_conj_iff hY').mpr ht.1, htN, htQ', ht.2.2.2.1, hRt⟩,
    ⟨hc'.hyp, ⟨c⁻¹, ?_⟩, hs.mem, hs.ne_one, htN, htQ'⟩, H'.rootTrans h34 hspread D hD'⟩
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

end CFSG.RankThree.GF2n.Stroth80
