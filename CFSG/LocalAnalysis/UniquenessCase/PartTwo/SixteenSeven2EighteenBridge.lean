module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_mem_stabTil_bot {V : Subgroup G} {m : G} (hm : m ∈ normalizer (V : Set G)) :
    m ∈ stabTil (⊥ : Subgroup G) V := by
  rw [stabTil, Subgroup.mem_inf]
  refine ⟨hm, ?_⟩
  show m ∈ normalizer ((⊥ : Subgroup G) : Set G)
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top m

theorem s16c167_rk_imgTil {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V) :
    rk ↥(imgTil ⊥ V hV U) = rk ↥U := by
  unfold rk
  rw [s16c167_card_imgTil_bot hV hU]

private theorem s16c167_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil ⊥ V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

theorem s16c167_mQuot_imgTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {I C : Subgroup G}
    (hI : I ≤ V) (hC : C ≤ I) :
    E3.mQuot (imgTil ⊥ V hV I) (imgTil ⊥ V hV C) = E3.mQuot I C := by
  have hCV : C ≤ V := hC.trans hI
  have hmono : imgTil ⊥ V hV C ≤ imgTil ⊥ V hV I :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono V hC)
  have h1 := Subgroup.relIndex_mul_card (H := imgTil ⊥ V hV C) (K := imgTil ⊥ V hV I)
  rw [inf_eq_left.2 hmono, s16c167_card_imgTil_bot hV hCV,
    s16c167_card_imgTil_bot hV hI] at h1
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := I)
  rw [inf_eq_left.2 hC] at h2
  unfold E3.mQuot
  rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)]

theorem s16c167_fixV_actTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil (⊥ : Subgroup G) V) :
    fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨m, hm⟩)) =
      imgTil ⊥ V hV (V ⊓ centralizer ({m} : Set G)) := by
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [mem_fixV_zpowers, actTil_mk, mem_imgTil]
  constructor
  · intro h
    rw [mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at h
    refine ⟨x, ⟨x.val_mem, ?_⟩, rfl⟩
    have h2 : m * x.val * m⁻¹ = x.val := mul_inv_eq_one.1 h
    have h4 : m * x.val = x.val * m := mul_inv_eq_iff_eq_mul.1 h2
    show ∀ h' ∈ ({m} : Set G), h' * x.val = x.val * h'
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact h4
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := s16c167_mkTil_bot_injective hV hyx
    rw [hyx'] at hy
    have hyC : x.val ∈ centralizer ({m} : Set G) := (Subgroup.mem_inf.1 hy).2
    rw [mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    have h4 : m * x.val = x.val * m := (Subgroup.mem_centralizer_iff.1 hyC) m (by simp)
    have h5 : m * x.val * m⁻¹ = x.val := mul_inv_eq_iff_eq_mul.2 h4
    rw [h5, mul_inv_cancel]

theorem s16c167_rkIdx_fixV_actTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil (⊥ : Subgroup G) V) :
    rkIdx (fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨m, hm⟩))) =
      E3.mQuot V (V ⊓ centralizer ({m} : Set G)) := by
  rw [s16c167_fixV_actTil hV hm]
  have htop : imgTil ⊥ V hV V = ⊤ := by
    rw [← imgTil_preTil ⊥ V hV ⊤, preTil_top]
  have hmq := s16c167_mQuot_imgTil hV (I := V) (C := V ⊓ centralizer ({m} : Set G))
    le_rfl inf_le_left
  rw [← hmq, htop]
  unfold E3.mQuot rkIdx
  rw [Subgroup.relIndex_top_right]

theorem s16c167_imgTil_conjSubgroup {V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil (⊥ : Subgroup G) V) (hm2 : m ^ 2 = 1) (I : Subgroup G) :
    imgTil ⊥ V hV (conjSubgroup I m) =
      (imgTil ⊥ V hV I).map (actTil ⊥ V hV ⟨m, hm⟩).toMonoidHom := by
  have hmul : m * m = 1 := by rw [← pow_two]; exact hm2
  have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmul
  have key : ∀ z : G, m * (m * z * m⁻¹) * m⁻¹ = z := by
    intro z
    rw [hminv, show m * (m * z * m) * m = (m * m) * z * (m * m) by group, hmul]
    simp
  have hmV : m ∈ normalizer (V : Set G) := stabTil_le_normalizer ⊥ V hm
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [mem_imgTil, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := s16c167_mkTil_bot_injective hV hyx
    rw [hyx'] at hy
    have hxI : m * x.val * m⁻¹ ∈ I := (mem_conjSubgroup_iff).1 hy
    have hxV : m * x.val * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hmV x.val).1 x.val_mem
    refine ⟨mkTil ⊥ V hV (IntMod.mk hV ⟨m * x.val * m⁻¹, hxV⟩), ?_, ?_⟩
    · rw [mem_imgTil]
      exact ⟨IntMod.mk hV ⟨m * x.val * m⁻¹, hxV⟩, hxI, rfl⟩
    · change actTil ⊥ V hV ⟨m, hm⟩
        (mkTil ⊥ V hV (IntMod.mk hV ⟨m * x.val * m⁻¹, hxV⟩)) = mkTil ⊥ V hV x
      rw [actTil_mk]
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      exact key x.val
  · rintro ⟨z, hz, hzq⟩
    obtain ⟨y, hyI, rfl⟩ := (mem_imgTil ⊥ V hV I z).1 hz
    change actTil ⊥ V hV ⟨m, hm⟩ (mkTil ⊥ V hV y) = mkTil ⊥ V hV x at hzq
    rw [actTil_mk] at hzq
    have hzy : actStab ⊥ V hV ⟨m, hm⟩ y = x := s16c167_mkTil_bot_injective hV hzq
    have hval : m * y.val * m⁻¹ = x.val := by
      have h := congrArg IntMod.val hzy
      rwa [actStab_apply_val] at h
    refine ⟨x, ?_, rfl⟩
    rw [mem_conjSubgroup_iff, ← hval, key y.val]
    exact hyI

theorem s16c167_mBar_le_mQuot {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) {t : G} (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hne : ¬ V ≤ centralizer ({t} : Set G)) :
    mBar M ⊥ V hV ≤ E3.mQuot V (V ⊓ centralizer ({t} : Set G)) := by
  have hm : t ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot (hM htM)
  have htbar_mem : actTil ⊥ V hV ⟨t, hm⟩ ∈ Mbar M ⊥ V hV := actTil_mem_barSub ⊥ V hV htM hm
  have hA : Subgroup.zpowers (actTil ⊥ V hV ⟨t, hm⟩) ≤ Mbar M ⊥ V hV :=
    Subgroup.zpowers_le.2 htbar_mem
  have htbar2 : (actTil ⊥ V hV ⟨t, hm⟩) ^ 2 = 1 := by
    have h2 : (⟨t, hm⟩ : stabTil (⊥ : Subgroup G) V) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using ht2
    rw [← map_pow, h2, map_one]
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers (actTil ⊥ V hV ⟨t, hm⟩)) := by
    obtain h | h := (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_iff_pow_eq_one.2 htbar2)
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hAne : Subgroup.zpowers (actTil ⊥ V hV ⟨t, hm⟩) ≠ ⊥ := by
    intro hbot
    have ht1 : actTil ⊥ V hV ⟨t, hm⟩ = 1 := by
      have hmem : actTil ⊥ V hV ⟨t, hm⟩ ∈ Subgroup.zpowers (actTil ⊥ V hV ⟨t, hm⟩) :=
        Subgroup.mem_zpowers _
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    apply hne
    intro v hv
    have h1 := (actTil_eq_one_iff ⊥ V hV ⟨t, hm⟩).1 ht1 v hv
    rw [Subgroup.mem_bot] at h1
    have h2 : t * v * t⁻¹ = v := mul_inv_eq_one.1 h1
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hle := E3.mParam_le_rkIdx_fixV hA hA2 hAne
  rw [s16c167_rkIdx_fixV_actTil hV hm] at hle
  simpa [mBar] using hle

theorem s16c167_imgTil_decomp {V : Subgroup G} (hV : IsElemAbelian 2 V) {Δ : Set (Subgroup G)}
    (hn : Δ.ncard = 2) (hle : ∀ I ∈ Δ, I ≤ V) (hi : sSupIndep Δ) (hs : sSup Δ = V) :
    (imgTil ⊥ V hV '' Δ).ncard = 2 ∧ sSupIndep (imgTil ⊥ V hV '' Δ) ∧
      sSup (imgTil ⊥ V hV '' Δ) = ⊤ := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 hn
  have ha_le : a ≤ V := hle a (by simp)
  have hb_le : b ≤ V := hle b (by simp)
  have hdisab : a ⊓ b = ⊥ := disjoint_iff.1 ((sSupIndep_pair hab).1 hi)
  have hsup : a ⊔ b = V := by rw [sSup_pair] at hs; exact hs
  have hmap : imgTil ⊥ V hV (a ⊔ b) = imgTil ⊥ V hV a ⊔ imgTil ⊥ V hV b := by
    have hsub : intSub V hV (a ⊔ b) = intSub V hV a ⊔ intSub V hV b :=
      Subgroup.subgroupOf_sup (A := a) (A' := b) (B := V) ha_le hb_le
    have h2 := congrArg (Subgroup.map (mkTil ⊥ V hV)) hsub
    rw [Subgroup.map_sup] at h2
    exact h2
  have hbot : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
    have hsub : intSub V hV (⊥ : Subgroup G) = ⊥ := Subgroup.bot_subgroupOf V
    have h2 := congrArg (Subgroup.map (mkTil ⊥ V hV)) hsub
    rw [Subgroup.map_bot] at h2
    exact h2
  have htop : imgTil ⊥ V hV V = ⊤ := by
    rw [← imgTil_preTil ⊥ V hV ⊤, preTil_top]
  have himg_inj : imgTil ⊥ V hV a ≠ imgTil ⊥ V hV b := by
    intro h
    apply hab
    have h1 : a.subgroupOf V = b.subgroupOf V :=
      Subgroup.map_injective (s16c167_mkTil_bot_injective hV) (show
        (intSub V hV a).map (mkTil ⊥ V hV) = (intSub V hV b).map (mkTil ⊥ V hV) from h)
    rw [Subgroup.subgroupOf_inj] at h1
    rwa [inf_eq_left.2 ha_le, inf_eq_left.2 hb_le] at h1
  have hdisj : Disjoint (imgTil ⊥ V hV a) (imgTil ⊥ V hV b) := by
    rw [disjoint_iff, ← s16c167_imgTil_inf_bot (U := a) (U' := b) hV, hdisab, hbot]
  rw [Set.image_pair]
  exact ⟨Set.ncard_pair himg_inj, (sSupIndep_pair himg_inj).2 hdisj, by
    rw [sSup_pair, ← hmap, hsup, htop]⟩

theorem s16c167_imgTil_wConj {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (L : Subgroup G) :
    imgTil ⊥ V hV '' wConj M ⊥ V hV L =
      {X | ∃ φ ∈ Mbar M ⊥ V hV, X = (wTil ⊥ V hV L).map φ.toMonoidHom} := by
  ext X
  constructor
  · rintro ⟨Y, ⟨m, hmM, rfl⟩, rfl⟩
    have hm : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot (hM hmM)
    refine ⟨actTil ⊥ V hV ⟨m⁻¹, (stabTil ⊥ V).inv_mem hm⟩, ?_, ?_⟩
    · exact actTil_mem_barSub ⊥ V hV (M.inv_mem hmM) ((stabTil ⊥ V).inv_mem hm)
    · unfold wSub
      rw [s16c167_conjSubgroup_preTil hV hm (wTil ⊥ V hV L), imgTil_preTil]
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub ⊥ V hV M φ).1 hφ
    refine ⟨conjSubgroup (wSub ⊥ V hV L) (g : G)⁻¹, ⟨(g : G)⁻¹, M.inv_mem hgM, rfl⟩, ?_⟩
    have hinv : (g : G)⁻¹ ∈ stabTil (⊥ : Subgroup G) V := (stabTil ⊥ V).inv_mem g.2
    unfold wSub
    rw [s16c167_conjSubgroup_preTil hV hinv (wTil ⊥ V hV L), imgTil_preTil]
    have h1 : actTil ⊥ V hV
        ⟨((g : G)⁻¹)⁻¹, (stabTil (⊥ : Subgroup G) V).inv_mem
          ((stabTil (⊥ : Subgroup G) V).inv_mem g.2)⟩ = φ := by
      have hg' : (⟨((g : G)⁻¹)⁻¹, (stabTil (⊥ : Subgroup G) V).inv_mem
          ((stabTil (⊥ : Subgroup G) V).inv_mem g.2)⟩ :
          stabTil (⊥ : Subgroup G) V) = g := by
        apply Subtype.ext
        exact inv_inv (g : G)
      rw [hg']
      exact hgφ
    rw [h1]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
