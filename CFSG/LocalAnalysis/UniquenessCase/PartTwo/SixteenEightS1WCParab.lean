module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCLift
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16w_isPGroup_of_sup_of_normal {A : Type*} [Group A] {p : ℕ}
    {N P H : Subgroup A} [N.Normal] (hsup : N ⊔ P = ⊤)
    (hN : IsPGroup p ↥(N ⊓ H)) (hP : IsPGroup p ↥P) : IsPGroup p ↥H := by
  intro x
  have hxsup : (x : A) ∈ N ⊔ P := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨n, hn, q, hq, hx⟩ := (Subgroup.mem_sup_of_normal_left (s := N) (t := P)).1 hxsup
  obtain ⟨k, hk⟩ := hP ⟨q, hq⟩
  have hqk : q ^ p ^ k = 1 := congrArg Subtype.val hk
  have hxN : (x : A) ^ p ^ k ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' N) ((x : A) ^ p ^ k) = 1
    have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_pow, ← hx, map_mul, hn1, one_mul, ← map_pow, hqk, map_one]
  obtain ⟨m, hm⟩ := hN ⟨(x : A) ^ p ^ k, hxN, pow_mem x.2 _⟩
  refine ⟨k + m, ?_⟩
  have hm' : ((x : A) ^ p ^ k) ^ p ^ m = 1 := congrArg Subtype.val hm
  apply Subtype.ext
  show (x : A) ^ p ^ (k + m) = 1
  rw [pow_add p k m, pow_mul]
  exact hm'

private theorem s16w_barSub_sup {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {X Y : Subgroup G}
    (hX : X ≤ stabTil V₀ V) (hY : Y ≤ stabTil V₀ V) :
    barSub V₀ V hV (X ⊔ Y) = barSub V₀ V hV X ⊔ barSub V₀ V hV Y := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

private theorem s16w_map_subgroupOf_map_inclusion {A B Y : Subgroup G}
    (hYA : Y ≤ A) (hAB : A ≤ B) :
    (Y.subgroupOf A).map (Subgroup.inclusion hAB) = Y.subgroupOf B := by
  ext k
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hk
    exact ⟨⟨(k : G), hYA hk⟩, hk, Subtype.ext rfl⟩

theorem S16gRowCtx.exists_permuting_of_parabolic (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {J : Subgroup (MulAut (Vtil V₀ V hV))} {a : ℕ} (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ lBar V₀ V hV L ⊔ barSub V₀ V hV D.T)
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) (ha : 2 ≤ a) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ a ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov : ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧
      IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := h.cover_lBar hsimple hmult
  obtain ⟨Yc, hYcM, hYcN, hYcbar, hYc2⟩ := hcov
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  let S : Subgroup G := Yc ⊔ D.T
  have hYcS : Yc ≤ S := le_sup_left
  have hDTS : D.T ≤ S := le_sup_right
  have hSM : S ≤ D.M := sup_le hYcM D.sylowM.le
  have hSs : S ≤ stabTil V₀ V := hSM.trans hMst
  have hYcNs : (Yc.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYcS]
    exact hSM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYcM).1 hYcN)
  haveI := hYcNs
  let φ : ↥S →* MulAut (Vtil V₀ V hV) :=
    (barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)
  let T' : Subgroup ↥S := D.T.subgroupOf S
  have hT'2 : IsPGroup 2 ↥T' := D.sylowM.isPGroup.comap_subtype
  have hT'syl : ¬ 2 ∣ T'.index := by
    have hdvd : D.T.relIndex S ∣ D.T.index := Subgroup.relIndex_dvd_index_of_le hDTS
    have hodd : ¬ 2 ∣ D.T.index := by
      have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowG).2.2
      rwa [Subgroup.relIndex_top_right] at h2
    intro hdiv
    exact hodd (hdiv.trans hdvd)
  have hNH : IsPGroup 2 ↥(Yc.subgroupOf S ⊓ (F11.CTilde D.M V₀ V).subgroupOf S) := by
    have hEq : (Yc ⊓ F11.CTilde D.M V₀ V).subgroupOf S =
        Yc.subgroupOf S ⊓ (F11.CTilde D.M V₀ V).subgroupOf S :=
      Subgroup.comap_inf Yc (F11.CTilde D.M V₀ V) S.subtype
    rw [← hEq]
    exact hYc2.comap_subtype
  have hsup : Yc.subgroupOf S ⊔ D.T.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYcS hDTS]
    exact Subgroup.subgroupOf_self S
  have hker2' : IsPGroup 2 ↥((F11.CTilde D.M V₀ V).subgroupOf S) :=
    s16w_isPGroup_of_sup_of_normal (p := 2) (N := Yc.subgroupOf S)
      (P := D.T.subgroupOf S) (H := (F11.CTilde D.M V₀ V).subgroupOf S) hsup hNH hT'2
  have hφker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf S := by
    show ((barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)).ker = _
    rw [← MonoidHom.comap_ker, ker_barHom V₀ V hV hMn hMst,
      Subgroup.comap_inclusion_subgroupOf hSM]
  have hker2 : IsPGroup 2 ↥φ.ker := by
    rw [hφker]
    exact hker2'
  have hφeq : φ = (actTil V₀ V hV).comp (Subgroup.inclusion hSs) := by
    ext x
    rfl
  have hφrange : φ.range = barSub V₀ V hV S := by
    rw [hφeq, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hrange : φ.range = lBar V₀ V hV L ⊔ barSub V₀ V hV D.T := by
    rw [hφrange]
    show barSub V₀ V hV (Yc ⊔ D.T) = lBar V₀ V hV L ⊔ barSub V₀ V hV D.T
    rw [s16w_barSub_sup (hYcM.trans hMst) (D.sylowM.le.trans hMst), hYcbar]
  have hJrange : J ≤ φ.range := by rw [hrange]; exact hJL
  have hT'map : T'.map φ = barSub V₀ V hV D.T := by
    show (D.T.subgroupOf S).map ((barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)) = _
    rw [← Subgroup.map_map]
    rw [s16w_map_subgroupOf_map_inclusion hDTS hSM]
    rw [barHom]
    rw [← Subgroup.map_map]
    rw [s16w_map_subgroupOf_map_inclusion D.sylowM.le hMst]
    rfl
  have hTJ' : T'.map φ ≤ J := by rw [hT'map]; exact hTJ
  have hJcard' : Nat.card ↥J = 3 ^ a * Nat.card ↥(T'.map φ) := by
    rw [hT'map]; exact hJcard
  obtain ⟨Y', hY'3, hY'card, hY'perm, hY'map, hY'inj⟩ :=
    s16w_exists_permuting_three_subgroup φ hT'2 hT'syl hker2 hTJ' hJrange hJcard'
  have hY'exp : ∀ z ∈ Y', z ^ 3 = 1 := by
    intro z hz
    have hz3 : (⟨z, hz⟩ : ↥Y') ^ 3 = 1 := by
      apply hY'inj
      change φ (Y'.subtype ((⟨z, hz⟩ : ↥Y') ^ 3)) = φ (Y'.subtype 1)
      rw [map_pow Y'.subtype, map_pow φ, map_one Y'.subtype, map_one φ]
      obtain ⟨n, hn⟩ := hY'3 (⟨z, hz⟩ : ↥Y')
      have hzn : z ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hpow : (φ z) ^ 3 ^ n = 1 := by rw [← map_pow, hzn, map_one]
      exact hJexp (φ z) (hY'map (Subgroup.mem_map_of_mem φ hz)) n hpow
    simpa using congrArg Subtype.val hz3
  let Y : Subgroup G := Y'.map S.subtype
  have hYM : Y ≤ D.M := (Subgroup.map_subtype_le Y').trans hSM
  have hY3 : IsPGroup 3 ↥Y := hY'3.map S.subtype
  have hYcard : Nat.card ↥Y = 3 ^ a := by
    show Nat.card ↥(Y'.map S.subtype) = 3 ^ a
    rw [Subgroup.card_map_of_injective S.subtype_injective, hY'card]
  have hexp : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← map_pow, hY'exp z hz, map_one]
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      show (g : G) ^ 3 = 1
      exact hexp (g : G) g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    have hdvd' : 3 ^ a ∣ 3 := by rw [hg, hYcard] at hdvd; exact hdvd
    have hle : 3 ^ a ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd'
    have h9 : 9 ≤ 3 ^ a := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = S.subtype '' (Y' : Set ↥S) := by
      change (Y'.map S.subtype : Set G) = S.subtype '' (Y' : Set ↥S)
      rw [Subgroup.coe_map]
    have hTmapS : T'.map S.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le hDTS
    have hTcoe : (D.T : Set G) = S.subtype '' (T' : Set ↥S) := by
      rw [← hTmapS, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  exact ⟨Y, hYM, hY3, hYcard, hexp, hYnc, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
