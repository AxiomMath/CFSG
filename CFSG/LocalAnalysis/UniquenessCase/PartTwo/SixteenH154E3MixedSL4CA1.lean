module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3PermLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]

private theorem s16h_map_subgroupOf_map_inclusion {A B Y : Subgroup G}
    (hYA : Y ≤ A) (hAB : A ≤ B) :
    (Y.subgroupOf A).map (Subgroup.inclusion hAB) = Y.subgroupOf B := by
  ext k
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hk
    exact ⟨⟨(k : G), hYA hk⟩, hk, Subtype.ext rfl⟩

theorem s16h_sl4_engine_b_exists_permuting_three
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 9 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧ Permutes Y D.T ∧
      barSub ⊥ V h.hyp151.isElemAbelian Y ≤ lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  classical
  have hV := h.hyp151.isElemAbelian
  have hMn : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMn h.hyp151.hyp125.pairFacts.le_normalizer₀
  let T' : Subgroup ↥D.M := D.T.subgroupOf D.M
  let φ : ↥D.M →* MulAut (Vtil ⊥ V hV) := barHom ⊥ V hV hMs
  obtain ⟨hT2, hTsyl⟩ := isPGroup_two_subgroupOf_sylow D
  obtain ⟨J, hJM, hTJ, hJL, ⟨a, hJcard⟩, hJexp⟩ :=
    s16h_sl4_engine_b_bar_two_three D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 hxM hxn hZ0
  have h3C := s16h_sl4_engine_b_three_not_dvd_kernel D S hσ hJP h hs2 ht ht2 ht1 htr hW
    hcomp hthin hZ hbad hrow hZ4 hxM hxn hZ0
  have hrange : J ≤ φ.range := by
    rw [range_barHom]
    exact hJM
  have hTmap : T'.map φ = barSub ⊥ V hV D.T := by
    show (D.T.subgroupOf D.M).map ((actTil ⊥ V hV).comp (Subgroup.inclusion hMs)) =
      barSub ⊥ V hV D.T
    rw [← Subgroup.map_map, s16h_map_subgroupOf_map_inclusion D.sylowM.le hMs]
    rfl
  have hTJ' : T'.map φ ≤ J := hTmap ▸ hTJ
  have hJcard' : Nat.card ↥J = 2 ^ a * 3 ^ 2 := by
    rw [hJcard]
    norm_num
  have hK3 : ¬ 3 ∣ Nat.card ↥φ.ker := by
    have hker_eq : φ.ker = (F11.CTilde D.M ⊥ V).subgroupOf D.M :=
      ker_barHom ⊥ V hV hMn hMs
    have hle : F11.CTilde D.M ⊥ V ≤ D.M := by
      rw [cTilde_eq_preBarSub_bot hV hMn]
      exact inf_le_left
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact h3C
  obtain ⟨Y', hY'3, hY'card, hY'perm, hY'le⟩ :=
    s16h_exists_permuting_three_of_ker φ hT2 hTsyl hrange hTJ' hJcard' hK3
  have hY'9 : Nat.card ↥Y' = 9 := by
    rw [hY'card]
    norm_num
  have hY'inf : Y' ⊓ φ.ker = ⊥ := by
    have hdivY' : Nat.card ↥(Y' ⊓ φ.ker) ∣ Nat.card ↥Y' :=
      Subgroup.card_dvd_of_le inf_le_left
    have hdivK : Nat.card ↥(Y' ⊓ φ.ker) ∣ Nat.card ↥φ.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : ¬ 3 ∣ Nat.card ↥(Y' ⊓ φ.ker) := fun h3d => hK3 (h3d.trans hdivK)
    have hdvd9 : Nat.card ↥(Y' ⊓ φ.ker) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hY'9 ▸ hdivY'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).1 hdvd9
    have hk0 : k = 0 := by
      by_contra hk0
      exact hcop (hk ▸ dvd_pow_self 3 hk0)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  have hY'exp : ∀ z ∈ Y', z ^ 3 = 1 := by
    intro z hz
    have hz9 : z ^ 9 = 1 := by
      have hdvd : orderOf z ∣ 9 :=
        hY'9 ▸ Subgroup.orderOf_dvd_natCard (Y' : Subgroup ↥D.M) hz
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    have hmemJ : φ z ∈ J := Subgroup.mem_comap.1 (hY'le hz)
    have hphi9 : (φ z) ^ 9 = 1 := by rw [← map_pow, hz9, map_one]
    have hphi3 : (φ z) ^ 3 = 1 := hJexp (φ z) hmemJ hphi9
    have hz3ker : z ^ 3 ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      simp [map_pow, hphi3]
    have hz3inf : z ^ 3 ∈ Y' ⊓ φ.ker := Subgroup.mem_inf.2 ⟨Y'.pow_mem hz 3, hz3ker⟩
    rw [hY'inf] at hz3inf
    exact Subgroup.mem_bot.1 hz3inf
  let Y : Subgroup G := Y'.map D.M.subtype
  have hYM : Y ≤ D.M := Subgroup.map_subtype_le Y'
  have hY3 : IsPGroup 3 ↥Y := hY'3.map D.M.subtype
  have hYcard : Nat.card ↥Y = 9 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective, hY'9]
  have hexp : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← map_pow, hY'exp z hz, map_one]
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      exact hexp (g : G) g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    rw [hg, hYcard] at hdvd
    have hle : 9 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = D.M.subtype '' (Y' : Set ↥D.M) := by
      change (Y'.map D.M.subtype : Set G) = D.M.subtype '' (Y' : Set ↥D.M)
      rw [Subgroup.coe_map]
    have hTmapSub : T'.map D.M.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le D.sylowM.le
    have hTcoe : (D.T : Set G) = D.M.subtype '' (T' : Set ↥D.M) := by
      rw [← hTmapSub, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  have hYL : barSub ⊥ V hV Y ≤ lBar ⊥ V hV L ⊔ lBar ⊥ V hV (conjSubgroup L x) := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV _ e).1 he
    obtain ⟨z, hz, hzg⟩ := hg
    have hzJ : φ z ∈ J := Subgroup.mem_comap.1 (hY'le hz)
    have hφz : φ z = actTil ⊥ V hV g := by
      have hzg' : (⟨(z : G), hMs z.2⟩ : ↥(stabTil ⊥ V)) = g := Subtype.ext hzg
      rw [← hzg']
      rfl
    rw [← hφz]
    refine s16h_threeElem_mem_of_two_normalizes (s16h_sl4_barSub_T_isPGroup D hV)
      (s16h_sl4_barSub_T_normalizes_sup D h hs2 hxM hxn) ?_ (hJL hzJ)
    rw [← map_pow, hY'exp z hz, map_one]
  exact ⟨Y, hYM, hY3, hYcard, hexp, hYnc, hperm, hYL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
