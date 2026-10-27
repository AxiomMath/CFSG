module

public import CFSG.Timmesfeld.Transvection.FrameExists
public import CFSG.Timmesfeld.Transvection.PlaneGroup
public import CFSG.Timmesfeld.Transvection.RankThreeComm
public import CFSG.Timmesfeld.Transvection.CoprimeSplit
public import CFSG.Timmesfeld.Transvection.Sp4Root

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

namespace RankThree

theorem mem_of_commute_of_forall_eq_mul {M L : Subgroup G} {h : G}
    (hM : ∀ x ∈ M, ∀ y ∈ M, Commute x y) (hhM : ∀ x ∈ M, h * x * h⁻¹ ∈ M)
    (h2 : ∀ x ∈ M, x * x = 1) (hodd : Odd (orderOf h)) (hL : ∀ l ∈ L, Commute l h)
    (hgen : ∀ x ∈ M, ∃ l ∈ L, ∃ m ∈ M, x = l * (m * h * m⁻¹ * h⁻¹))
    {g : G} (hg : g ∈ M) (hgh : Commute g h) : g ∈ L := by
  obtain ⟨l, hl, m, hm, rfl⟩ := hgen g hg
  have hc : Commute (m * h * m⁻¹ * h⁻¹) h := by
    have h1 : m * h * m⁻¹ * h⁻¹ = l⁻¹ * (l * (m * h * m⁻¹ * h⁻¹)) := by group
    rw [h1]
    exact ((hL l hl).inv_left).mul_left hgh
  have hmem : (commMap hM hhM ⟨m, hm⟩ : M) ∈ (commMap hM hhM).ker ⊓ (commMap hM hhM).range :=
    ⟨(mem_ker_commMap_iff hM hhM _).2 hc, ⟨⟨m, hm⟩, rfl⟩⟩
  rw [inf_ker_range_commMap hM hhM h2 hodd, Subgroup.mem_bot] at hmem
  have h1 : m * h * m⁻¹ * h⁻¹ = 1 := by
    have := congrArg Subtype.val hmem
    simpa using this
  rw [h1, mul_one]
  exact hl

@[expose] def mulCommSub {M : Subgroup G} (L : Subgroup G) {h : G}
    (hM : ∀ x ∈ M, ∀ y ∈ M, Commute x y) (hhM : ∀ x ∈ M, h * x * h⁻¹ ∈ M) (hLM : L ≤ M) :
    Subgroup G where
  carrier := {x | ∃ l ∈ L, ∃ m ∈ M, x = l * (m * h * m⁻¹ * h⁻¹)}
  mul_mem' := by
    rintro _ _ ⟨l, hl, m, hm, rfl⟩ ⟨l', hl', m', hm', rfl⟩
    refine ⟨l * l', L.mul_mem hl hl', m * m', M.mul_mem hm hm', ?_⟩
    have hc := (commMap hM hhM).map_mul ⟨m, hm⟩ ⟨m', hm'⟩
    have hc' := congrArg Subtype.val hc
    simp only [coe_commMap, Subgroup.coe_mul] at hc'
    have hcm : (commMap hM hhM ⟨m, hm⟩ : G) ∈ M := (commMap hM hhM ⟨m, hm⟩).2
    simp only [coe_commMap] at hcm
    rw [hc', show l * (m * h * m⁻¹ * h⁻¹) * (l' * (m' * h * m'⁻¹ * h⁻¹)) =
      l * ((m * h * m⁻¹ * h⁻¹) * l') * (m' * h * m'⁻¹ * h⁻¹) by group,
      (hM _ hcm _ (hLM hl')).eq]
    group
  one_mem' := ⟨1, L.one_mem, 1, M.one_mem, by group⟩
  inv_mem' := by
    rintro _ ⟨l, hl, m, hm, rfl⟩
    refine ⟨l⁻¹, L.inv_mem hl, m⁻¹, M.inv_mem hm, ?_⟩
    have hc := (commMap hM hhM).map_inv ⟨m, hm⟩
    have hc' := congrArg Subtype.val hc
    simp only [coe_commMap, InvMemClass.coe_inv] at hc'
    have hcm : (commMap hM hhM ⟨m, hm⟩ : G) ∈ M := (commMap hM hhM ⟨m, hm⟩).2
    simp only [coe_commMap] at hcm
    rw [mul_inv_rev, hc', (hM _ (M.inv_mem hcm) _ (M.inv_mem (hLM hl))).eq]

theorem mem_shortRootGroup {P Q P' Q' : Subgroup G} {x : G} :
    x ∈ shortRootGroup Δ P Q P' Q' ↔
      (x ∈ lineGroup Δ P P' ∧ x ∈ lineStab Δ Q P') ∧ x ∈ lineStab Δ P Q' := by
  simp only [shortRootGroup, Subgroup.mem_inf]

theorem commutatorElement_mul_right' (x m n : G) :
    ⁅x, m * n⁆ = ⁅x, m⁆ * (m * ⁅x, n⁆ * m⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_left' (u v y : G) :
    ⁅u * v, y⁆ = u * ⁅v, y⁆ * u⁻¹ * ⁅u, y⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_commutatorElement (h a b : G) :
    h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

end RankThree

open RankThree

namespace IsFrame

variable [Finite G] (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) {i j k : Fin r}
include hF hΔ

omit [Finite G] hΔ in
private theorem commuting_aux (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Commuting (Q i) (P j) ∧ Commuting (Q i) (P k) ∧ Commuting (P j) (P k) ∧
      Commuting (Q i) (Q j) ∧ Commuting (Q j) (P k) :=
  ⟨hF.commuting_QP hij, hF.commuting_QP hik, hF.commuting_PP hjk, hF.commuting_QQ hij,
    hF.commuting_QP hjk⟩

theorem commutator_mem_planeGroup (hik : i ≠ k) (hjk : j ≠ k) {x y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) :
    ⁅x, y⁆ ∈ planeGroup Δ (Q i) (P j) (P k) := by
  obtain ⟨⟨hxL, -⟩, -⟩ := mem_shortRootGroup.1 hx
  obtain ⟨⟨hyL, hyS⟩, -⟩ := mem_shortRootGroup.1 hy
  have hQi : Q i ∈ planeOf Δ (Q i) (P j) (P k) := left_mem_planeOf (hF.memQ i)
  have hPj : P j ∈ planeOf Δ (Q i) (P j) (P k) := mid_mem_planeOf (hF.memP j)
  have hPk : P k ∈ planeOf Δ (Q i) (P j) (P k) := right_mem_planeOf (hF.memP k)
  have hxπ : x ∈ planeGroup Δ (Q i) (P j) (P k) := lineGroup_le_planeGroup hQi hPj hxL
  have h1 : conjSub (Q i) y = Q i := conjSub_of_forall_commute fun q hq =>
    ((hF.commuting_framePt_lineGroup hΔ.root (a := Sum.inr i) (c := Sum.inr j) (d := Sum.inl k)
      (by simp) (by simpa using hik.symm)) q hq y hyL).symm
  have h2 : conjSub (P k) y = P k := conjSub_of_forall_commute fun p hp =>
    ((hF.commuting_framePt_lineGroup hΔ.root (a := Sum.inl k) (c := Sum.inr j) (d := Sum.inl k)
      (by simpa using hjk) (by simp)) p hp y hyL).symm
  have h3 : conjSub (P j) y ∈ planeOf Δ (Q i) (P j) (P k) :=
    lineOf_subset_planeOf hPj hPk ((mem_lineStab_iff.1 hyS (P j)).2 (left_mem_lineOf (hF.memP j)))
  have hn := conjSub_planeGroup_eq_of_fix hΔ.root (hF.memQ i) (hF.memP k) h1 h2 h3
  have hmem : y * x⁻¹ * y⁻¹ ∈ planeGroup Δ (Q i) (P j) (P k) := by
    rw [← hn]
    exact conj_mem_conjSub y (Subgroup.inv_mem _ hxπ)
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact Subgroup.mul_mem _ hxπ hmem

theorem commutator_mem_planeGroup' (hij : i ≠ j) (hik : i ≠ k) {x y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) :
    ⁅x, y⁆ ∈ planeGroup Δ (Q i) (Q j) (P k) := by
  obtain ⟨⟨hxL, -⟩, hxS⟩ := mem_shortRootGroup.1 hx
  obtain ⟨⟨hyL, -⟩, -⟩ := mem_shortRootGroup.1 hy
  have hQi : Q i ∈ planeOf Δ (Q i) (Q j) (P k) := left_mem_planeOf (hF.memQ i)
  have hQj : Q j ∈ planeOf Δ (Q i) (Q j) (P k) := mid_mem_planeOf (hF.memQ j)
  have hPk : P k ∈ planeOf Δ (Q i) (Q j) (P k) := right_mem_planeOf (hF.memP k)
  have hyπ : y ∈ planeGroup Δ (Q i) (Q j) (P k) := lineGroup_le_planeGroup hQj hPk hyL
  have h1 : conjSub (Q i) x = Q i := conjSub_of_forall_commute fun q hq =>
    ((hF.commuting_framePt_lineGroup hΔ.root (a := Sum.inr i) (c := Sum.inr i) (d := Sum.inl j)
      (by simp) (by simpa using hij.symm)) q hq x hxL).symm
  have h2 : conjSub (P k) x = P k := conjSub_of_forall_commute fun p hp =>
    ((hF.commuting_framePt_lineGroup hΔ.root (a := Sum.inl k) (c := Sum.inr i) (d := Sum.inl j)
      (by simpa using hik) (by simp)) p hp x hxL).symm
  have h3 : conjSub (Q j) x ∈ planeOf Δ (Q i) (Q j) (P k) :=
    lineOf_subset_planeOf hQi hQj ((mem_lineStab_iff.1 hxS (Q j)).2 (right_mem_lineOf (hF.memQ j)))
  have hn := conjSub_planeGroup_eq_of_fix hΔ.root (hF.memQ i) (hF.memP k) h1 h2 h3
  have hmem : x * y * x⁻¹ ∈ planeGroup Δ (Q i) (Q j) (P k) := by
    rw [← hn]
    exact conj_mem_conjSub x hyπ
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hyπ)

theorem commute_commutator_of_mem_sup (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) {z : G} (hz : z ∈ P j ⊔ Q j) :
    Commute ⁅x, y⁆ z := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := commuting_aux hF hij hik hjk
  have hP : P j ≤ Subgroup.centralizer {⁅x, y⁆} := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_planeGroup hΔ.root (hF.memQ i) (hF.memP j) (hF.memP k) c1 c2 c3
      (commutator_mem_planeGroup hF hΔ hik hjk hx hy)
      (le_planeGroup (mid_mem_planeOf (hF.memP j)) hp)).symm.eq
  have hQ : Q j ≤ Subgroup.centralizer {⁅x, y⁆} := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_planeGroup hΔ.root (hF.memQ i) (hF.memQ j) (hF.memP k) c4 c2 c5
      (commutator_mem_planeGroup' hF hΔ hij hik hx hy)
      (le_planeGroup (mid_mem_planeOf (hF.memQ j)) hp)).symm.eq
  have := sup_le hP hQ hz
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

end IsFrame

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) {i j k : Fin r}
include hfr hΔ hpts hml

theorem commutator_mem_lineGroup (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {h : G}
    (hhX : h ∈ P j ⊔ Q j) (hhP : conjSub (P j) h = P j) (hodd : Odd (orderOf h))
    (hcent : ∀ D' ∈ lineOf Δ (Q i) (P k), ∀ u ∈ lineGroup Δ (P j) D', Commute u h → u ∈ D')
    {x y : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) :
    ⁅x, y⁆ ∈ lineGroup Δ (Q i) (P k) := by
  have hF := hfr.toIsFrame
  have c1 := hF.commuting_QP hij
  have c2 := hF.commuting_QP hik
  have c3 := hF.commuting_PP hjk
  have hQiπ : Q i ∈ planeOf Δ (Q i) (P j) (P k) := left_mem_planeOf (hF.memQ i)
  have hPjπ : P j ∈ planeOf Δ (Q i) (P j) (P k) := mid_mem_planeOf (hF.memP j)
  have hPkπ : P k ∈ planeOf Δ (Q i) (P j) (P k) := right_mem_planeOf (hF.memP k)
  have hMc : ∀ a ∈ planeGroup Δ (Q i) (P j) (P k), ∀ b ∈ planeGroup Δ (Q i) (P j) (P k),
      Commute a b := fun a ha b hb =>
    commute_of_mem_planeGroup hΔ.root (hF.memQ i) (hF.memP j) (hF.memP k) c1 c2 c3 ha hb
  have hhL : ∀ l ∈ lineGroup Δ (Q i) (P k), Commute l h := fun l hl =>
    ((hF.commuting_sup_lineGroup hΔ.root (i := j) (a := Sum.inr i) (b := Sum.inl k)
      (by simpa using hij) (by simpa using hjk.symm)) h hhX l hl).symm
  have hQh : conjSub (Q i) h = Q i := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := j) (a := Sum.inr i) (by simpa using hij)) h hhX q hq
  have hPh : conjSub (P k) h = P k := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := j) (a := Sum.inl k) (by simpa using hjk.symm))
      h hhX q hq
  have hMn := conjSub_planeGroup_eq_of_fix hΔ.root (hF.memQ i) (hF.memP k) hQh hPh
    (by rw [hhP]; exact hPjπ)
  have hhM : ∀ a ∈ planeGroup Δ (Q i) (P j) (P k), h * a * h⁻¹ ∈ planeGroup Δ (Q i) (P j) (P k) :=
    fun a ha => hMn ▸ conj_mem_conjSub h ha
  have h2M : ∀ a ∈ planeGroup Δ (Q i) (P j) (P k), a * a = 1 := fun a ha =>
    mul_self_of_mem_planeGroup hΔ.root (hF.memQ i) (hF.memP j) (hF.memP k) c1 c2 c3 ha
  have hLM : lineGroup Δ (Q i) (P k) ≤ planeGroup Δ (Q i) (P j) (P k) :=
    lineGroup_le_planeGroup hQiπ hPkπ
  have hpt : ∀ D ∈ planeOf Δ (Q i) (P j) (P k),
      ∃ D' ∈ lineOf Δ (Q i) (P k), D ≤ lineGroup Δ (P j) D' := by
    intro D hD
    by_cases hDj : D = P j
    · refine ⟨P k, right_mem_lineOf (hF.memP k), ?_⟩
      rw [hDj]
      exact le_lineGroup (left_mem_lineOf (hF.memP j))
    have hjD : Commuting (P j) D :=
      commuting_of_mem_planeOf hΔ.root (hF.memQ i) (hF.memP j) (hF.memP k) c1 c2 c3 hPjπ hD
    obtain ⟨D', hD'l, hQD'⟩ := hml (P j) (hF.memP j) D hD.1 (Ne.symm hDj) hjD (Q j) (hF.memQ j)
    have hD'π := lineOf_subset_planeOf hPjπ hD hD'l
    have hD'j : D' ≠ P j := by
      rintro rfl
      exact ModelRank.not_commuting_of_opposite (hF.opposite j) hQD'.symm
    have hlD := lineOf_eq_of_mem_of_ne hΔ hpts (hF.memP j) hD.1 (Ne.symm hDj) hjD hD'l hD'j
    refine ⟨D', hfr.toIsFrame.mem_lineOf_of_mem_planeOf hfr.maximal hΔ hpts hml hij hik hjk
      hD'π hQD'.symm,
      le_lineGroup ?_⟩
    rw [hlD]
    exact right_mem_lineOf hD.1
  have hle : planeGroup Δ (Q i) (P j) (P k) ≤ mulCommSub (lineGroup Δ (Q i) (P k)) hMc hhM hLM := by
    refine iSup₂_le fun D hD d hd => ?_
    obtain ⟨D', hD'l, hDle⟩ := hpt D hD
    have hjD' : Commuting (P j) D' := hD'l.2 (P j) (hF.memP j) c1.symm c3
    have hD'π := lineOf_subset_planeOf hQiπ hPkπ hD'l
    have hUc : ∀ a ∈ lineGroup Δ (P j) D', ∀ b ∈ lineGroup Δ (P j) D', Commute a b :=
      fun a ha b hb => commute_of_mem_lineGroup hΔ (hF.memP j) hD'l.1 hjD' ha hb
    have hUn : conjSub (lineGroup Δ (P j) D') h = lineGroup Δ (P j) D' := by
      rw [← lineGroup_conjSub hΔ.root, hhP,
        conjSub_of_forall_commute fun e he => (hhL e (le_lineGroup hD'l he)).symm]
    have hhU : ∀ u ∈ lineGroup Δ (P j) D', h * u * h⁻¹ ∈ lineGroup Δ (P j) D' :=
      fun u hu => hUn ▸ conj_mem_conjSub h hu
    obtain ⟨c, hch, m, hcm⟩ := exists_eq_mul_commMap hUc hhU
      (fun u hu => mul_self_of_mem_lineGroup hΔ (hF.memP j) hD'l.1 hjD' hu) hodd ⟨d, hDle hd⟩
    refine ⟨c, le_lineGroup hD'l (hcent D' hD'l c c.2 hch), m,
      lineGroup_le_planeGroup hPjπ hD'π m.2, ?_⟩
    have := congrArg Subtype.val hcm
    simpa [coe_commMap] using this
  exact mem_of_commute_of_forall_eq_mul hMc hhM h2M hodd hhL (fun a ha => hle ha)
    (IsFrame.commutator_mem_planeGroup hF hΔ hik hjk hx hy)
    (IsFrame.commute_commutator_of_mem_sup hF hΔ hij hik hjk hx hy hhX)

end IsMaxFrame

namespace IsFrame

variable [Finite G] (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) {i j k : Fin r}
include hF hΔ

omit [Finite G] in
theorem commute_left_of_mem_lineGroup (hij : i ≠ j) (hik : i ≠ k) {x l : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j)) (hl : l ∈ lineGroup Δ (Q i) (P k)) :
    Commute x l :=
  (hF.commuting_lineGroup_lineGroup hΔ.root (a := Sum.inr i) (b := Sum.inl j)
    (c := Sum.inr i) (d := Sum.inl k) (by simp) (by simpa using hij) (by simpa using hik.symm)
    (by simp)) x ((mem_shortRootGroup.1 hx).1.1) l hl

omit [Finite G] in
theorem commute_right_of_mem_lineGroup (hik : i ≠ k) (hjk : j ≠ k) {y l : G}
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) (hl : l ∈ lineGroup Δ (Q i) (P k)) :
    Commute y l :=
  (hF.commuting_lineGroup_lineGroup hΔ.root (a := Sum.inr j) (b := Sum.inl k)
    (c := Sum.inr i) (d := Sum.inl k) (by simp) (by simpa using hik) (by simpa using hjk.symm)
    (by simp)) y ((mem_shortRootGroup.1 hy).1.1) l hl

omit [Finite G] in
theorem commutator_mul_left (hij : i ≠ j) (hik : i ≠ k) {x x' y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hxy : ⁅x, y⁆ ∈ lineGroup Δ (Q i) (P k)) (hx'y : ⁅x', y⁆ ∈ lineGroup Δ (Q i) (P k)) :
    ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  rw [commutatorElement_mul_left', (hF.commute_left_of_mem_lineGroup hΔ hij hik hx hx'y).eq,
    mul_inv_cancel_right]
  exact (commute_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP k) (hF.commuting_QP hik) hx'y hxy).eq

omit [Finite G] in
theorem commutator_mul_right (hik : i ≠ k) (hjk : j ≠ k) {x y y' : G}
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k))
    (hxy' : ⁅x, y'⁆ ∈ lineGroup Δ (Q i) (P k)) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  rw [commutatorElement_mul_right', (hF.commute_right_of_mem_lineGroup hΔ hik hjk hy hxy').eq,
    mul_inv_cancel_right]

theorem commutator_mem_commSub_right (hik : i ≠ k) (hjk : j ≠ k) {hk : G}
    (hkX : hk ∈ P k ⊔ Q k) (hkP : conjSub (P k) hk = P k) (hkQ : conjSub (Q k) hk = Q k)
    (hkodd : Odd (orderOf hk))
    (hkfpf : ∀ y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), Commute y hk → y = 1) {x y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k))
    (hall : ∀ y' ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), ⁅x, y'⁆ ∈ lineGroup Δ (Q i) (P k)) :
    ⁅x, y⁆ ∈ commSub (lineGroup Δ (Q i) (P k)) hk := by
  have hYL := shortRootGroup_le_lineGroup (Δ := Δ) (Q j) (P j) (P k) (Q k)
  have hjk' : Commuting (Q j) (P k) := hF.commuting_QP hjk
  have hYc : ∀ a ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k),
      ∀ b ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), Commute a b := fun a ha b hb =>
    commute_of_mem_lineGroup hΔ (hF.memQ j) (hF.memP k) hjk' (hYL ha) (hYL hb)
  have hQj : conjSub (Q j) hk = Q j := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := k) (a := Sum.inr j) (by simpa using hjk)) hk hkX q hq
  have hPj : conjSub (P j) hk = P j := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := k) (a := Sum.inl j) (by simpa using hjk)) hk hkX q hq
  have hYn : conjSub (shortRootGroup Δ (Q j) (P j) (P k) (Q k)) hk =
      shortRootGroup Δ (Q j) (P j) (P k) (Q k) := by
    rw [← shortRootGroup_conjSub hΔ.root, hQj, hPj, hkP, hkQ]
  have hhY : ∀ a ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k),
      hk * a * hk⁻¹ ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k) := fun a ha =>
    hYn ▸ conj_mem_conjSub hk ha
  have h2Y : ∀ a ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), a * a = 1 := fun a ha =>
    mul_self_of_mem_lineGroup hΔ (hF.memQ j) (hF.memP k) hjk' (hYL ha)
  obtain ⟨c, hch, m, hcm⟩ := exists_eq_mul_commMap hYc hhY h2Y hkodd ⟨y, hy⟩
  have hc1 : (c : G) = 1 := hkfpf c c.2 hch
  have hym : y = m * hk * (m : G)⁻¹ * hk⁻¹ := by
    have := congrArg Subtype.val hcm
    simpa [coe_commMap, hc1] using this
  have hminv : (m : G)⁻¹ = m := inv_eq_of_mul_eq_one_right (h2Y m m.2)
  have hkx : hk * x * hk⁻¹ = x := by
    rw [((hF.commuting_sup_lineGroup hΔ.root (i := k) (a := Sum.inr i) (b := Sum.inl j)
      (by simpa using hik) (by simpa using hjk)) hk hkX x ((mem_shortRootGroup.1 hx).1.1)).eq,
      mul_inv_cancel_right]
  have hm' : hk * (m : G)⁻¹ * hk⁻¹ ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k) :=
    hhY _ (Subgroup.inv_mem _ m.2)
  set a := ⁅x, (m : G)⁆ with ha_def
  have ha : a ∈ lineGroup Δ (Q i) (P k) := hall m m.2
  have hainv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP k)
      (hF.commuting_QP hik) ha)
  have hxy : ⁅x, y⁆ = a * hk * a⁻¹ * hk⁻¹ := by
    calc ⁅x, y⁆ = ⁅x, (m : G) * (hk * (m : G)⁻¹ * hk⁻¹)⁆ := by rw [hym]; group
      _ = a * ((m : G) * ⁅x, hk * (m : G)⁻¹ * hk⁻¹⁆ * (m : G)⁻¹) :=
          commutatorElement_mul_right' _ _ _
      _ = a * ⁅x, hk * (m : G)⁻¹ * hk⁻¹⁆ := by
          rw [(hF.commute_right_of_mem_lineGroup hΔ hik hjk m.2 (hall _ hm')).eq,
            mul_inv_cancel_right]
      _ = a * (hk * a * hk⁻¹) := by
          rw [conj_commutatorElement, hkx, hminv]
      _ = a * hk * a⁻¹ * hk⁻¹ := by rw [hainv]; group
  rw [hxy]
  exact Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem commutator_mem_commSub_left (hij : i ≠ j) (hik : i ≠ k) {hi : G}
    (hiX : hi ∈ P i ⊔ Q i) (hiP : conjSub (P i) hi = P i) (hiQ : conjSub (Q i) hi = Q i)
    (hiodd : Odd (orderOf hi))
    (hifpf : ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), Commute x hi → x = 1) {x y : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k))
    (hall : ∀ x' ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), ⁅x', y⁆ ∈ lineGroup Δ (Q i) (P k)) :
    ⁅x, y⁆ ∈ commSub (lineGroup Δ (Q i) (P k)) hi := by
  have hXL := shortRootGroup_le_lineGroup (Δ := Δ) (Q i) (P i) (P j) (Q j)
  have hij' : Commuting (Q i) (P j) := hF.commuting_QP hij
  have hXc : ∀ a ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
      ∀ b ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), Commute a b := fun a ha b hb =>
    commute_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP j) hij' (hXL ha) (hXL hb)
  have hQj : conjSub (Q j) hi = Q j := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := i) (a := Sum.inr j) (by simpa using hij.symm))
      hi hiX q hq
  have hPj : conjSub (P j) hi = P j := conjSub_of_forall_commute fun q hq =>
    (hF.commuting_sup_framePt hΔ.root (i := i) (a := Sum.inl j) (by simpa using hij.symm))
      hi hiX q hq
  have hXn : conjSub (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) hi =
      shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
    rw [← shortRootGroup_conjSub hΔ.root, hQj, hPj, hiP, hiQ]
  have hhX : ∀ a ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
      hi * a * hi⁻¹ ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) := fun a ha =>
    hXn ▸ conj_mem_conjSub hi ha
  have h2X : ∀ a ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), a * a = 1 := fun a ha =>
    mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP j) hij' (hXL ha)
  obtain ⟨c, hch, m, hcm⟩ := exists_eq_mul_commMap hXc hhX h2X hiodd ⟨x, hx⟩
  have hc1 : (c : G) = 1 := hifpf c c.2 hch
  have hxm : x = m * hi * (m : G)⁻¹ * hi⁻¹ := by
    have := congrArg Subtype.val hcm
    simpa [coe_commMap, hc1] using this
  have hminv : (m : G)⁻¹ = m := inv_eq_of_mul_eq_one_right (h2X m m.2)
  have hiy : hi * y * hi⁻¹ = y := by
    rw [((hF.commuting_sup_lineGroup hΔ.root (i := i) (a := Sum.inr j) (b := Sum.inl k)
      (by simpa using hij.symm) (by simpa using hik.symm)) hi hiX y
      ((mem_shortRootGroup.1 hy).1.1)).eq, mul_inv_cancel_right]
  have hm' : hi * (m : G)⁻¹ * hi⁻¹ ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) :=
    hhX _ (Subgroup.inv_mem _ m.2)
  set b := ⁅(m : G), y⁆ with hb_def
  have hb : b ∈ lineGroup Δ (Q i) (P k) := hall m m.2
  have hbinv : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_right (mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP k)
      (hF.commuting_QP hik) hb)
  have hxy : ⁅x, y⁆ = (b * hi * b⁻¹ * hi⁻¹)⁻¹ := by
    calc ⁅x, y⁆ = ⁅(m : G) * (hi * (m : G)⁻¹ * hi⁻¹), y⁆ := by rw [hxm]; group
      _ = (m : G) * ⁅hi * (m : G)⁻¹ * hi⁻¹, y⁆ * (m : G)⁻¹ * b :=
          commutatorElement_mul_left' _ _ _
      _ = ⁅hi * (m : G)⁻¹ * hi⁻¹, y⁆ * b := by
          rw [(hF.commute_left_of_mem_lineGroup hΔ hij hik m.2 (hall _ hm')).eq,
            mul_inv_cancel_right]
      _ = hi * b * hi⁻¹ * b := by
          rw [conj_commutatorElement, hiy, hminv]
      _ = (b * hi * b⁻¹ * hi⁻¹)⁻¹ := by
          rw [show (b * hi * b⁻¹ * hi⁻¹)⁻¹ = hi * b * hi⁻¹ * b⁻¹ by group, hbinv]
  rw [hxy]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨b, hb, rfl⟩)

end IsFrame

namespace IsFrame

variable [Finite G] (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
  {i j k : Fin r}
include hF hΔ hpts

theorem eq_one_of_commutator_eq_one (hij : i ≠ j) (hik : i ≠ k)
    (hxreg : ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = P i → x = 1)
    (hyreg : ∀ y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), conjSub (P j) y = P j → y = 1)
    {x y : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) (hy1 : y ≠ 1) (hxy : ⁅x, y⁆ = 1) :
    x = 1 := by
  by_contra hx1
  obtain ⟨⟨-, hxS⟩, -⟩ := mem_shortRootGroup.1 hx
  obtain ⟨⟨hyL, hyS⟩, -⟩ := mem_shortRootGroup.1 hy
  have hC : conjSub (P i) x ∈ lineOf Δ (P i) (P j) :=
    (mem_lineStab_iff.1 hxS (P i)).2 (left_mem_lineOf (hF.memP i))
  have hCi : conjSub (P i) x ≠ P i := fun e => hx1 (hxreg x hx e)
  have hyPi : conjSub (P i) y = P i := conjSub_of_forall_commute fun p hp =>
    ((hF.commuting_framePt_lineGroup hΔ.root (a := Sum.inl i) (c := Sum.inr j) (d := Sum.inl k)
      (by simpa using hij.symm) (by simp)) p hp y hyL).symm
  have hcomm : Commute x y := commutatorElement_eq_one_iff_commute.1 hxy
  have hCy : conjSub (conjSub (P i) x) y = conjSub (P i) x := by
    rw [← conjSub_mul, ← hcomm.eq, conjSub_mul, hyPi]
  have hPjy : conjSub (P j) y ∈ lineOf Δ (P j) (P k) :=
    (mem_lineStab_iff.1 hyS (P j)).2 (left_mem_lineOf (hF.memP j))
  have hPjy1 : conjSub (P j) y ≠ P j := fun e => hy1 (hyreg y hy e)
  have hC' : conjSub (P i) x ∈ lineOf Δ (P i) (conjSub (P j) y) := by
    have := conjSub_mem_lineOf_conjSub hΔ.root hC y
    rwa [hCy, hyPi] at this
  have hQPjy : Commuting (Q i) (conjSub (P j) y) :=
    hPjy.2 (Q i) (hF.memQ i) (hF.commuting_QP hij) (hF.commuting_QP hik)
  have hPjyi : conjSub (P j) y ≠ P i := by
    intro e
    rw [e] at hQPjy
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) hQPjy.symm
  have hcij : Commuting (P i) (conjSub (P j) y) := by
    have := (hF.commuting_PP hij).conjSub y
    rwa [hyPi] at this
  have hPjyΔ : conjSub (P j) y ∈ Δ := hΔ.root.conjSub_mem (hF.memP j) y
  have h1 := lineOf_eq_of_mem_of_ne hΔ hpts (hF.memP i) (hF.memP j) (hF.P_ne hij)
    (hF.commuting_PP hij) hC hCi
  have h2 := lineOf_eq_of_mem_of_ne hΔ hpts (hF.memP i) hPjyΔ (Ne.symm hPjyi) hcij hC' hCi
  have hmem : conjSub (P j) y ∈ lineOf Δ (P i) (P j) := by
    rw [← h1, h2]
    exact right_mem_lineOf hPjyΔ
  exact ModelRank.not_commuting_of_opposite (hF.opposite_of_mem_lineOf hΔ hpts hij hmem hPjy1)
    hQPjy

end IsFrame

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) {i j k : Fin r}
include hfr hΔ hpts hml

theorem commutator_mem_shortRootGroup (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {hi hj hk : G}
    (hiX : hi ∈ P i ⊔ Q i) (hiP : conjSub (P i) hi = P i) (hiQ : conjSub (Q i) hi = Q i)
    (hiodd : Odd (orderOf hi))
    (hifpf : ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), Commute x hi → x = 1)
    (hjX : hj ∈ P j ⊔ Q j) (hjP : conjSub (P j) hj = P j) (hjodd : Odd (orderOf hj))
    (hjcent : ∀ D' ∈ lineOf Δ (Q i) (P k), ∀ u ∈ lineGroup Δ (P j) D', Commute u hj → u ∈ D')
    (hkX : hk ∈ P k ⊔ Q k) (hkP : conjSub (P k) hk = P k) (hkQ : conjSub (Q k) hk = Q k)
    (hkodd : Odd (orderOf hk))
    (hkfpf : ∀ y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k), Commute y hk → y = 1)
    (hX : commSub (lineGroup Δ (Q i) (P k)) hi ⊓ commSub (lineGroup Δ (Q i) (P k)) hk ≤
      shortRootGroup Δ (Q i) (P i) (P k) (Q k))
    {x y : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) :
    ⁅x, y⁆ ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) := by
  have hF := hfr.toIsFrame
  have hline := fun {x' y' : G} (hx' : x' ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy' : y' ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) =>
    hfr.commutator_mem_lineGroup hΔ hpts hml hij hik hjk hjX hjP hjodd hjcent hx' hy'
  exact hX ⟨hF.commutator_mem_commSub_left hΔ hij hik hiX hiP hiQ hiodd hifpf hx hy
      fun _ hx' => hline hx' hy,
    hF.commutator_mem_commSub_right hΔ hik hjk hkX hkP hkQ hkodd hkfpf hx hy
      fun _ hy' => hline hx hy'⟩

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
