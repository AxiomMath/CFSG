module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3PermLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_map_subgroupOf_map_inclusion {A B Y : Subgroup G}
    (hYA : Y ≤ A) (hAB : A ≤ B) :
    (Y.subgroupOf A).map (Subgroup.inclusion hAB) = Y.subgroupOf B := by
  ext k
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hk
    exact ⟨⟨(k : G), hYA hk⟩, hk, Subtype.ext rfl⟩

theorem s16h_e3_mBarGT_of_rank (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ}
    (hn : ∀ τ ∈ Mbar D.M V₀ V h.isElemAbelian, τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (n + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
        (Subgroup.zpowers τ)))
    (hex : ∃ τ ∈ Mbar D.M V₀ V h.isElemAbelian, τ ^ 2 = 1 ∧ τ ≠ 1) :
    MBarGT D.M V₀ V n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  have hpow : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  rw [Hyp125.mBarGT_iff_lt_mBar h n]
  unfold mBar E3.mParam
  have hev : Even (Nat.card ↥(Mbar D.M V₀ V hV)) := by
    obtain ⟨τ, hτ, hτ2, hτ1⟩ := hex
    have ho : orderOf τ = 2 := orderOf_eq_prime_iff.2 ⟨hτ2, hτ1⟩
    rw [even_iff_two_dvd]
    exact ho ▸ Subgroup.orderOf_dvd_natCard (Mbar D.M V₀ V hV) hτ
  rw [if_pos hev]
  have hmem : sInf {k : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
      k = rkIdx (fixV (Subgroup.zpowers t))} ∈
      {k : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))} := by
    obtain ⟨τ, hτ, hτ2, hτ1⟩ := hex
    exact Nat.sInf_mem ⟨_, τ, hτ, orderOf_eq_prime_iff.2 ⟨hτ2, hτ1⟩, rfl⟩
  obtain ⟨t, ht, hto, hkeq⟩ := hmem
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.1 hto).1
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 hto).2
  have hcard := hn t ht ht2 ht1
  have hcard2 : Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
      (Subgroup.zpowers t)) = 2 ^ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
        (Subgroup.zpowers t)) :=
    card_eq_two_pow hpow _
  have hrk : n + 1 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) := by
    rw [hcard2] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  have hrkidx : n < rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    omega
  rw [hkeq]
  exact hrkidx

theorem s16h_e3_good_vector_lift (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥) (h3 : 3 ∈ D.sig)
    {w : Vtil V₀ V h.hyp151.isElemAbelian} (hw : w ≠ 1)
    (hwT : ∀ τ ∈ barSub V₀ V h.hyp151.isElemAbelian D.T, τ w = w)
    {E : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    (hE : E ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian) (hEab : IsElemAbelian 3 E)
    (hEcard : 9 ≤ Nat.card ↥E) (hEw : ∀ e ∈ E, e w = w) :
    ∃ v : G, v ∈ V ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  subst hV₀
  have hV := h.hyp151.isElemAbelian
  have hMn : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hMn h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hxw⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
  let v : G := IntMod.val x
  have hvV : v ∈ V := IntMod.val_mem x
  have hx1 : x ≠ 1 := by
    intro hx
    apply hw
    rw [← hxw, hx, map_one]
  have hv1 : v ≠ 1 := by
    intro hv
    exact hx1 (IntMod.val_injective (by simpa [v] using hv))
  have hTv : ∀ t ∈ D.T, t * v = v * t := by
    intro t ht
    have htM : t ∈ D.M := D.sylowM.le ht
    have hst : t ∈ stabTil (⊥ : Subgroup G) V := hMs htM
    have hτmem : actTil (⊥ : Subgroup G) V hV ⟨t, hst⟩ ∈ barSub (⊥ : Subgroup G) V hV D.T :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV ht hst
    have hfix := hwT _ hτmem
    rw [← hxw, actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    have h1 : t * v * t⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hfix
    have h2 : t * v * t⁻¹ = v := mul_inv_eq_one.1 h1
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [h2]
  have hE3 : IsPGroup 3 ↥E := hEab.isPGroup
  have hEcard' : 3 ^ 2 ≤ Nat.card ↥E := by simpa using hEcard
  have hEnc : ¬ IsCyclic ↥E :=
    s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab hEcard'
  obtain ⟨P, hPp, hPnc, hPfix⟩ :=
    exists_noncyclic_pGroup_map_le (barHom (⊥ : Subgroup G) V hV hMs) Nat.prime_three
      (by rw [range_barHom]; exact hE) hE3 hEnc
  have hPle : P.map D.M.subtype ≤ F11.CElt D.M (⊥ : Subgroup G) v := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hg
    have hfix : (barHom (⊥ : Subgroup G) V hV hMs) y (mkTil (⊥ : Subgroup G) V hV x)
        = mkTil (⊥ : Subgroup G) V hV x := by
      have h := hEw _ (hPfix y hy)
      rwa [← hxw] at h
    change (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hMs y))
      (mkTil (⊥ : Subgroup G) V hV x) = mkTil (⊥ : Subgroup G) V hV x at hfix
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    change D.M.subtype y * v * (D.M.subtype y)⁻¹ * v⁻¹ ∈ ⊥ at hfix
    have hcomm : D.M.subtype y * v * (D.M.subtype y)⁻¹ * v⁻¹ = 1 :=
      Subgroup.mem_bot.1 hfix
    refine ⟨y.2, ?_, ?_⟩
    · change (y : G) ∈ normalizer ((⊥ : Subgroup G) : Set G)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    · rw [hcomm]
      exact Subgroup.one_mem _
  have hPpG : IsPGroup 3 ↥(P.map D.M.subtype) := hPp.map D.M.subtype
  have hPncG : ¬ IsCyclic ↥(P.map D.M.subtype) := by
    intro hc
    exact hPnc ((Subgroup.equivMapOfInjective P D.M.subtype
      D.M.subtype_injective).isCyclic.mpr hc)
  have hu := s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 h3 hPpG hPncG hvV
    (by simp [hv1]) hPle
  refine ⟨v, hvV, hTv, ?_⟩
  have hw2 : ∃ n : ℕ, v ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 v hvV⟩
  exact (centralizer_le_of_uniqueMax D.maxLocal hv1 hw2 hu).1

theorem s16h_e3_permuting_lift (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    {J : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))} {a : ℕ}
    (hJ : J ≤ Mbar D.M V₀ V h.isElemAbelian) (hTJ : barSub V₀ V h.isElemAbelian D.T ≤ J)
    (hJcard : Nat.card ↥J = 2 ^ a * 9) (hJexp : ∀ x ∈ J, x ^ 9 = 1 → x ^ 3 = 1) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 9 ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
      ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  classical
  have hV := h.isElemAbelian
  have hMn : D.M ≤ normalizer (V : Set G) := h.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hMn h.pairFacts.le_normalizer₀
  let T' : Subgroup ↥D.M := D.T.subgroupOf D.M
  let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs
  obtain ⟨hT2, hTsyl⟩ := isPGroup_two_subgroupOf_sylow D
  have hrange : J ≤ φ.range := by
    rw [range_barHom]
    exact hJ
  have hTmap : T'.map φ = barSub V₀ V hV D.T := by
    show (D.T.subgroupOf D.M).map ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)) =
      barSub V₀ V hV D.T
    rw [← Subgroup.map_map, s16h_e3_map_subgroupOf_map_inclusion D.sylowM.le hMs]
    rfl
  have hTJ' : T'.map φ ≤ J := hTmap ▸ hTJ
  have hJcard' : Nat.card ↥J = 2 ^ a * 3 ^ 2 := by
    rw [hJcard]
    norm_num
  have hK3 : ¬ 3 ∣ Nat.card ↥φ.ker := by
    have hker_eq : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf D.M :=
      ker_barHom V₀ V hV hMn hMs
    rw [hker_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (WeakClosure81.cTilde_le_M D.M V₀ V)).toEquiv]
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
  exact ⟨Y, hYM, hY3, hYcard, hexp, hYnc, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
