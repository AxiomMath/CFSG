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

private theorem s16t3_isPGroup_of_sup_of_normal {A : Type*} [Group A] {p : ℕ}
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

private theorem s16t3_isPGroup_sup_subgroupOf {p : ℕ} {M H K : Subgroup G}
    (hHM : H ≤ M) (hKM : K ≤ M) (hHN : (H.subgroupOf M).Normal)
    (hKN : (K.subgroupOf M).Normal) (hH : IsPGroup p ↥H) (hK : IsPGroup p ↥K) :
    IsPGroup p ↥(H ⊔ K) := by
  haveI := hHN
  haveI := hKN
  have hsup : (H.subgroupOf M) ⊔ (K.subgroupOf M) = (H ⊔ K).subgroupOf M :=
    (Subgroup.subgroupOf_sup hHM hKM).symm
  have h' : IsPGroup p ↥((H.subgroupOf M) ⊔ (K.subgroupOf M)) :=
    (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHM).symm).to_sup_of_normal_left
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKM).symm)
  rw [hsup] at h'
  exact h'.of_equiv (Subgroup.subgroupOfEquivOfLe (sup_le hHM hKM))

private theorem s16t3_barSub_sup {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {X Y : Subgroup G}
    (hX : X ≤ stabTil V₀ V) (hY : Y ≤ stabTil V₀ V) :
    barSub V₀ V hV (X ⊔ Y) = barSub V₀ V hV X ⊔ barSub V₀ V hV Y := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

private theorem s16t3_map_subgroupOf_map_inclusion {A B Y : Subgroup G}
    (hYA : Y ≤ A) (hAB : A ≤ B) :
    (Y.subgroupOf A).map (Subgroup.inclusion hAB) = Y.subgroupOf B := by
  ext k
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hk
    exact ⟨⟨(k : G), hYA hk⟩, hk, Subtype.ext rfl⟩

theorem s16t3_exists_permuting_of_parabolic_two (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb)
    (hKmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥Kb) = 2 ^ k)
    (hLK : lBar V₀ V hV L ⊓ Kb = ⊥)
    {J : Subgroup (MulAut (Vtil V₀ V hV))} {a : ℕ} (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ lBar V₀ V hV L ⊔ Kb ⊔ barSub V₀ V hV D.T)
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) (ha : 2 ≤ a) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ a ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcovL : ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧
      IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := h.cover_lBar hsimple hmult
  obtain ⟨YL, hYLM, hYLN, hYLbar, hYL2⟩ := hcovL
  have hcovK : ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = Kb ∧
      IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := h.cover_of_simple hKM hKN hKs hKnc hKmult
  obtain ⟨YK, hYKM, hYKN, hYKbar, hYK2⟩ := hcovK
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  let S0 : Subgroup G := YL ⊔ YK
  let S : Subgroup G := S0 ⊔ D.T
  have hYLS0 : YL ≤ S0 := le_sup_left
  have hYKS0 : YK ≤ S0 := le_sup_right
  have hS0S : S0 ≤ S := le_sup_left
  have hDTS : D.T ≤ S := le_sup_right
  have hS0M : S0 ≤ D.M := sup_le hYLM hYKM
  have hSM : S ≤ D.M := sup_le hS0M D.sylowM.le
  have hSs : S ≤ stabTil V₀ V := hSM.trans hMst
  have hS0NDM : (S0.subgroupOf D.M).Normal := by
    haveI : (YL.subgroupOf D.M).Normal := hYLN
    haveI : (YK.subgroupOf D.M).Normal := hYKN
    rw [show S0 = YL ⊔ YK from rfl, Subgroup.subgroupOf_sup hYLM hYKM]
    infer_instance
  have hS0NS : (S0.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hS0S]
    exact hSM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hS0M).1 hS0NDM)
  have hCTN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMst
  have hS0CT : IsPGroup 2 ↥(S0 ⊓ F11.CTilde D.M V₀ V) := by
    have heq : S0 ⊓ F11.CTilde D.M V₀ V =
        (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V) :=
      sup_inf_cTilde_eq_of_disjoint_barSub hMst hYLM hYKM hYKN hYLbar hYKbar hLK
    rw [heq]
    refine s16t3_isPGroup_sup_subgroupOf (M := D.M)
      (inf_le_left.trans hYLM) (inf_le_left.trans hYKM) ?_ ?_ hYL2 hYK2
    · haveI : (YL.subgroupOf D.M).Normal := hYLN
      haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := hCTN
      have h : (YL ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M =
          YL.subgroupOf D.M ⊓ (F11.CTilde D.M V₀ V).subgroupOf D.M :=
        Subgroup.comap_inf YL (F11.CTilde D.M V₀ V) D.M.subtype
      rw [h]
      infer_instance
    · haveI : (YK.subgroupOf D.M).Normal := hYKN
      haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := hCTN
      have h : (YK ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M =
          YK.subgroupOf D.M ⊓ (F11.CTilde D.M V₀ V).subgroupOf D.M :=
        Subgroup.comap_inf YK (F11.CTilde D.M V₀ V) D.M.subtype
      rw [h]
      infer_instance
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
  haveI : (S0.subgroupOf S).Normal := hS0NS
  have hsup : S0.subgroupOf S ⊔ D.T.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hS0S hDTS]
    exact Subgroup.subgroupOf_self S
  have hN2 : IsPGroup 2 ↥(S0.subgroupOf S ⊓ (F11.CTilde D.M V₀ V).subgroupOf S) := by
    have hEq : (S0 ⊓ F11.CTilde D.M V₀ V).subgroupOf S =
        S0.subgroupOf S ⊓ (F11.CTilde D.M V₀ V).subgroupOf S :=
      Subgroup.comap_inf S0 (F11.CTilde D.M V₀ V) S.subtype
    rw [← hEq]
    exact hS0CT.comap_subtype
  have hker2' : IsPGroup 2 ↥((F11.CTilde D.M V₀ V).subgroupOf S) :=
    s16t3_isPGroup_of_sup_of_normal (p := 2) (N := S0.subgroupOf S)
      (P := D.T.subgroupOf S) (H := (F11.CTilde D.M V₀ V).subgroupOf S) hsup hN2 hT'2
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
  have hrange : φ.range = lBar V₀ V hV L ⊔ Kb ⊔ barSub V₀ V hV D.T := by
    rw [hφrange]
    show barSub V₀ V hV (S0 ⊔ D.T) = lBar V₀ V hV L ⊔ Kb ⊔ barSub V₀ V hV D.T
    rw [s16t3_barSub_sup (hS0M.trans hMst) (D.sylowM.le.trans hMst)]
    rw [show S0 = YL ⊔ YK from rfl,
      s16t3_barSub_sup (hYLM.trans hMst) (hYKM.trans hMst), hYLbar, hYKbar]
  have hJrange : J ≤ φ.range := by rw [hrange]; exact hJL
  have hT'map : T'.map φ = barSub V₀ V hV D.T := by
    show (D.T.subgroupOf S).map ((barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)) = _
    rw [← Subgroup.map_map]
    rw [s16t3_map_subgroupOf_map_inclusion hDTS hSM]
    rw [barHom]
    rw [← Subgroup.map_map]
    rw [s16t3_map_subgroupOf_map_inclusion D.sylowM.le hMst]
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
