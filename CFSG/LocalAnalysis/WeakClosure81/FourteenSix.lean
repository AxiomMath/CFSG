module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.RankThree.GF2n.Tim77Prop24Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def ConjGenerated (M V₀ V : Subgroup G) : Prop :=
  ∀ v ∈ V, v ∉ V₀ → V = Subgroup.closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹}

theorem eq_of_normalizer_of_not_le_of_conjGenerated {M V₀ V W : Subgroup G}
    (hgen : ConjGenerated M V₀ V) (hW : W ≤ V)
    (hMW : M ≤ Subgroup.normalizer (W : Set G)) (hnot : ¬ W ≤ V₀) : W = V := by
  have hnot' : ∃ w, w ∈ W ∧ w ∉ V₀ := by
    by_contra h
    apply hnot
    intro x hxW
    by_contra hxV₀
    exact h ⟨x, hxW, hxV₀⟩
  obtain ⟨w, hwW, hw0⟩ := hnot'
  refine le_antisymm hW ?_
  rw [hgen w (hW hwW) hw0]
  refine (Subgroup.closure_le W).2 ?_
  rintro y ⟨m, hmM, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hMW hmM) w).1 hwW

theorem le_of_normalizer_of_ne_of_conjGenerated {M V₀ V W : Subgroup G}
    (hgen : ConjGenerated M V₀ V) (hW : W ≤ V)
    (hMW : M ≤ Subgroup.normalizer (W : Set G)) (hne : W ≠ V) : W ≤ V₀ := by
  by_contra hnot
  exact hne (eq_of_normalizer_of_not_le_of_conjGenerated hgen hW hMW hnot)

private theorem timmesfeld_conjSubgroup_eq (T : Subgroup G) (g : G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g T = conjSubgroup T g⁻¹ := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, mem_conjSubgroup_iff, inv_inv]

private theorem conjSubgroup_zpowers (x g : G) :
    conjSubgroup (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  rw [conjSubgroup, MonoidHom.map_zpowers]
  congr 1
  show MulAut.conj g⁻¹ x = g⁻¹ * x * g
  rw [MulAut.conj_apply, inv_inv]

theorem conjSubgroup_inf_self_eq_bot {M V₀ : Subgroup G}
    (hN : Subgroup.normalizer (V₀ : Set G) = M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) {g : G} (hg : g ∉ M) :
    conjSubgroup V₀ g ⊓ V₀ = ⊥ := by
  have hbridge : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ = conjSubgroup V₀ g := by
    rw [timmesfeld_conjSubgroup_eq, inv_inv]
  have h := hTI g⁻¹
  rw [hbridge] at h
  rcases h with hbot | heq
  · simpa [inf_comm] using hbot
  · exfalso
    have hle : V₀ ≤ conjSubgroup V₀ g := by
      calc V₀ = V₀ ⊓ conjSubgroup V₀ g := heq.symm
        _ ≤ conjSubgroup V₀ g := inf_le_right
    have heqC : conjSubgroup V₀ g = V₀ := by
      have hEq : V₀ = conjSubgroup V₀ g :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (E3.card_conjSubgroup V₀ g))
      exact hEq.symm
    exact hg ((le_of_eq hN) (conjSubgroup_eq_iff_mem_normalizer.mp heqC))

private theorem mQuot_inf_le_of_le {V D Cc : Subgroup G} (hV : IsPGroup 2 V) (hD : D ≤ V)
    (hC : Cc ≤ V) : E3.mQuot D (D ⊓ Cc) ≤ E3.mQuot V Cc := by
  have hDp : IsPGroup 2 D := hV.to_le hD
  have hle : (D ⊓ Cc).relIndex D ≤ Cc.relIndex V := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right hD (E3.relIndex_ne_zero' V Cc)
  have h1 : (D ⊓ Cc).relIndex D = 2 ^ E3.mQuot D (D ⊓ Cc) := E3.relIndex_eq_two_pow hDp _
  have h2 : Cc.relIndex V = 2 ^ E3.mQuot V Cc := E3.relIndex_eq_two_pow hV Cc
  rw [h1, h2] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle

private theorem mQuot_conjSubgroup_left {V A : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    E3.mQuot V (conjSubgroup A m) = E3.mQuot V A := by
  have hV : conjSubgroup V m = V := conjSubgroup_eq_iff_mem_normalizer.2 hm
  have h := E3.mQuot_conjSubgroup V A m
  rwa [hV] at h

private theorem le_preTil_fixV_actTil {V₀ V C : Subgroup G} (hV : IsElemAbelian 2 V)
    {t : G} (hts : t ∈ stabTil V₀ V) (hCV : C ≤ V)
    (hCt : C ≤ Subgroup.centralizer ({t} : Set G)) :
    C ≤ preTil V₀ V hV (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) := by
  intro c hc
  rw [mem_preTil_iff_of_mem V₀ V hV _ (hCV hc)]
  rw [mem_fixV_zpowers, actTil_mk, mkTil_eq_iff, actStab_apply_val]
  change t * c * t⁻¹ * c⁻¹ ∈ V₀
  have hcomm : t * c = c * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hCt hc)).symm
  have h1 : t * c * t⁻¹ * c⁻¹ = 1 := by rw [hcomm]; group
  rw [h1]
  exact V₀.one_mem

theorem mQuot_preTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) :
    E3.mQuot V (preTil V₀ V hV S) = rkIdx S := by
  change rkIdx (intSub V hV (preTil V₀ V hV S)) = rkIdx S
  have h : intSub V hV (preTil V₀ V hV S) = S.comap (mkTil V₀ V hV) := by
    ext x
    rw [mem_intSub, mem_preTil]
    constructor
    · rintro ⟨y, hy, hyS⟩
      have : y = x := IntMod.val_injective hy
      rwa [this] at hyS
    · intro hx
      exact ⟨x, rfl, hx⟩
  rw [h]
  unfold rkIdx
  rw [Subgroup.index_comap_of_surjective S (mkTil_surjective V₀ V hV)]

private theorem cTilde_conj_mem {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) {x m : G}
    (hx : x ∈ F11.CTilde M V₀ V) (hm : m ∈ M) :
    m * x * m⁻¹ ∈ F11.CTilde M V₀ V := by
  obtain ⟨hxM, hxs, hx1⟩ := (mem_cTilde_iff hV hM).1 hx
  have hms : m ∈ stabTil V₀ V := le_inf hM hM₀ hm
  have hmxM : m * x * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
  have hmxs : m * x * m⁻¹ ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hms hxs) ((stabTil V₀ V).inv_mem hms)
  refine (mem_cTilde_iff hV hM).2 ⟨hmxM, hmxs, ?_⟩
  have hprod : (⟨m * x * m⁻¹, hmxs⟩ : stabTil V₀ V) =
      ⟨m, hms⟩ * ⟨x, hxs⟩ * ⟨m, hms⟩⁻¹ := by
    ext
    simp [mul_assoc]
  rw [hprod, map_mul, map_mul, map_inv, hx1]
  simp

theorem mem_cTilde_of_mQuot_lt {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) {t : G} (ht : t ∈ M)
    (ht2 : ∃ k : ℕ, orderOf t = 2 ^ k) {C : Subgroup G} (hCV : C ≤ V)
    (hCt : C ≤ Subgroup.centralizer ({t} : Set G))
    (hlt : (E3.mQuot V C : ℕ∞) < (mBar M V₀ V hV : ℕ∞)) :
    t ∈ F11.CTilde M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMs : M ≤ stabTil V₀ V := le_inf hM hM₀
  have hts : t ∈ stabTil V₀ V := hMs ht
  by_contra hmem
  have hφ1 : actTil V₀ V hV ⟨t, hts⟩ ≠ 1 := by
    intro h1
    exact hmem ((mem_cTilde_iff hV hM).2 ⟨ht, hts, h1⟩)
  obtain ⟨k, hk⟩ := ht2
  have hgorder : orderOf (⟨t, hts⟩ : stabTil V₀ V) = 2 ^ k := by
    rw [← Subgroup.orderOf_coe (⟨t, hts⟩ : stabTil V₀ V), hk]
  have horder : orderOf (actTil V₀ V hV ⟨t, hts⟩) ∣ 2 ^ k := by
    rw [← hgorder]
    exact orderOf_map_dvd (actTil V₀ V hV) ⟨t, hts⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 horder
  have hAp : IsPGroup 2 (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩)) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hφmem : actTil V₀ V hV ⟨t, hts⟩ ∈ Mbar M V₀ V hV :=
    actTil_mem_barSub V₀ V hV ht hts
  have hAle : Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩) ≤ Mbar M V₀ V hV :=
    Subgroup.zpowers_le.2 hφmem
  have hA1 : Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩) ≠ ⊥ := by
    intro hbot
    have : actTil V₀ V hV ⟨t, hts⟩ ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
      rw [← hbot]; exact Subgroup.mem_zpowers _
    exact hφ1 (Subgroup.mem_bot.1 this)
  have h1 : mBar M V₀ V hV ≤ rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) :=
    E3.mParam_le_rkIdx_fixV hAle hAp hA1
  have h2 : rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) ≤ E3.mQuot V C := by
    rw [← mQuot_preTil V₀ V hV (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩)))]
    exact E3.mQuot_mono (le_preTil_fixV_actTil hV hts hCV hCt)
  have hbar : (mBar M V₀ V hV : ℕ∞) ≤ (E3.mQuot V C : ℕ∞) := by
    exact_mod_cast (h1.trans h2)
  exact absurd (lt_of_lt_of_le hlt hbar) (lt_irrefl _)

private theorem centralizer_zpowers_eq_singleton (x : G) :
    Subgroup.centralizer (Subgroup.zpowers x : Set G) = Subgroup.centralizer ({x} : Set G) := by
  refine le_antisymm (Subgroup.centralizer_le ?_) ?_
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_zpowers x
  · intro z hz
    have hxz : x * z = z * x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hz).symm
    have hcomm : Commute x z := hxz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hcomm.zpow_left n

private theorem centralizer_singleton_of_mem_cTilde_of_mQuot_lt {M V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hN₀ : Subgroup.normalizer (V₀ : Set G) = M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) {g : G} (hg : g ∉ M) {x : G}
    (hx : x ∈ F11.CTilde M V₀ V)
    (hlt : (E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℕ∞)
      < (rk ↥(conjSubgroup V₀ g ⊓ V) : ℕ∞)) :
    conjSubgroup V₀ g ⊓ V ≤ Subgroup.centralizer ({x} : Set G) := by
  set Cc : Subgroup G := conjSubgroup V₀ g with hC
  set D : Subgroup G := Cc ⊓ V with hD
  obtain ⟨hxM, hxs, hxact⟩ := (mem_cTilde_iff hV hM).1 hx
  have hxV₀ : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀ :=
    (actTil_eq_one_iff V₀ V hV ⟨x, hxs⟩).1 hxact
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hM hxM
  have hDV₀ : D ⊓ V₀ = ⊥ := by
    rw [hD, hC, inf_assoc, inf_eq_right.2 hV₀]
    exact conjSubgroup_inf_self_eq_bot hN₀ hTI hg
  have hVp : IsPGroup 2 V := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV
  have hDleV : D ≤ V := by rw [hD]; exact inf_le_right
  have hCxV : V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) ≤ V := inf_le_left
  have hDne : D ⊓ (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) ≠ ⊥ := by
    intro hbot
    have hle : rk D ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
      have h := mQuot_inf_le_of_le hVp hDleV hCxV
      rw [hbot] at h
      have hbot' : E3.mQuot D ⊥ = rk D := by
        rw [E3.mQuot, rk, Subgroup.relIndex_bot_left]
      rwa [hbot'] at h
    have hle' : (rk D : ℕ∞) ≤
        (E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℕ∞) := by
      exact_mod_cast hle
    exact absurd (lt_of_lt_of_le hlt hle') (lt_irrefl _)
  obtain ⟨w, hwD, hwCx, hw1⟩ : ∃ w, w ∈ D ∧ w ∈ V ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G) ∧ w ≠ 1 := by
    haveI : Nontrivial ↥(D ⊓ (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥(D ⊓ (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))))
    exact ⟨w, (Subgroup.mem_inf.1 w.2).1, (Subgroup.mem_inf.1 w.2).2,
      fun h => hw (Subtype.ext (by simpa using h))⟩
  have hwCc : w ∈ Cc := by rw [hD] at hwD; exact (Subgroup.mem_inf.1 hwD).1
  have hwx : x * w = w * x :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hwCx).2) x (Subgroup.mem_zpowers x)
  have hCTI : CFSG.CGT.Timmesfeld75.IsTI Cc := by
    have h := CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g⁻¹
    rwa [timmesfeld_conjSubgroup_eq V₀ g⁻¹, inv_inv] at h
  have hwx' : x * w * x⁻¹ = w := by rw [hwx]; group
  have hwCc' : w ∈ conjSubgroup Cc x := by
    rw [mem_conjSubgroup_iff, hwx']
    exact hwCc
  have hxNc : x ∈ Subgroup.normalizer (Cc : Set G) :=
    CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI hCTI hwCc hw1 hwx
  intro d hd
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hD] at hd
  have hdCc : d ∈ Cc := (Subgroup.mem_inf.1 hd).1
  have hdV : d ∈ V := (Subgroup.mem_inf.1 hd).2
  have hxdx : x * d * x⁻¹ ∈ Cc := (Subgroup.mem_normalizer_iff.1 hxNc d).1 hdCc
  have hxdxV : x * d * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxN d).1 hdV
  have hcommC : x * d * x⁻¹ * d⁻¹ ∈ Cc := Cc.mul_mem hxdx (Cc.inv_mem hdCc)
  have hcommV : x * d * x⁻¹ * d⁻¹ ∈ V := V.mul_mem hxdxV (V.inv_mem hdV)
  have hcommV₀ : x * d * x⁻¹ * d⁻¹ ∈ V₀ := hxV₀ d hdV
  have hcommbot : x * d * x⁻¹ * d⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hDV₀]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcommC, hcommV⟩, hcommV₀⟩
  rw [Subgroup.mem_bot] at hcommbot
  have hxd : x * d = d * x := by
    have h1 : (x * d) * (d * x)⁻¹ = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hcommbot
    exact mul_inv_eq_one.1 h1
  exact hxd.symm

theorem mQuot_centralizer_ge_rk_conjSubgroup_inf {M V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hN₀ : Subgroup.normalizer (V₀ : Set G) = M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) (hgen : ConjGenerated M V₀ V)
    {g : G} (hg : g ∉ M) {x : G} (hx : x ∈ F11.CTilde M V₀ V)
    (hxV : ¬ V ≤ Subgroup.centralizer ({x} : Set G)) :
    rk ↥(conjSubgroup V₀ g ⊓ V) ≤
      E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := le_of_eq hN₀.symm
  have hxV' : ¬ V ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rwa [centralizer_zpowers_eq_singleton x]
  rw [← centralizer_zpowers_eq_singleton x]
  by_contra hcon
  have hlt : (E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℕ∞)
      < (rk ↥(conjSubgroup V₀ g ⊓ V) : ℕ∞) := by
    exact_mod_cast (not_le.1 hcon)
  have hDx : conjSubgroup V₀ g ⊓ V ≤ Subgroup.centralizer ({x} : Set G) :=
    centralizer_singleton_of_mem_cTilde_of_mQuot_lt hV hV₀ hM hN₀ hTI hg hx hlt
  set D : Subgroup G := conjSubgroup V₀ g ⊓ V with hD
  have hDleV : D ≤ V := by rw [hD]; exact inf_le_right
  have hDV₀ : D ⊓ V₀ = ⊥ := by
    rw [hD, inf_assoc, inf_eq_right.2 hV₀]
    exact conjSubgroup_inf_self_eq_bot hN₀ hTI hg
  have hDne : D ≠ ⊥ := by
    intro hb
    have hlt0 : (E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℕ∞)
        < (0 : ℕ∞) := by
      have hltD : (E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℕ∞)
          < (rk D : ℕ∞) := by rwa [hD] at hlt
      rw [hb, rk_bot] at hltD
      simpa using hltD
    exact absurd hlt0 (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ _))
  obtain ⟨v₀, hv₀D, hv₀1⟩ : ∃ v₀, v₀ ∈ D ∧ v₀ ≠ 1 := by
    haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥D)
    exact ⟨w, w.2, fun h => hw (Subtype.ext (by simpa using h))⟩
  have hv₀V : v₀ ∈ V := hDleV hv₀D
  have hv₀0 : v₀ ∉ V₀ := by
    intro hv
    have : v₀ ∈ D ⊓ V₀ := Subgroup.mem_inf.2 ⟨hv₀D, hv⟩
    rw [hDV₀, Subgroup.mem_bot] at this
    exact hv₀1 this
  have hgen' := hgen v₀ hv₀V hv₀0
  have hVle : V ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [hgen']
    refine (Subgroup.closure_le _).2 ?_
    rintro z ⟨m, hmM, rfl⟩
    have hmN : m ∈ Subgroup.normalizer (V : Set G) := hM hmM
    have hmx : m⁻¹ * x * m ∈ F11.CTilde M V₀ V := by
      simpa [inv_inv] using cTilde_conj_mem hV hM hM₀ hx (M.inv_mem hmM)
    have hquot : E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers (m⁻¹ * x * m) : Set G))
        = E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
      have hconj : V ⊓ Subgroup.centralizer (Subgroup.zpowers (m⁻¹ * x * m) : Set G) =
          conjSubgroup (V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) m := by
        rw [E3.conjSubgroup_inf, conjSubgroup_eq_iff_mem_normalizer.2 hmN,
          E3.conjSubgroup_centralizer, conjSubgroup_zpowers]
      rw [hconj, mQuot_conjSubgroup_left hmN]
    have hlt' : (E3.mQuot V
        (V ⊓ Subgroup.centralizer (Subgroup.zpowers (m⁻¹ * x * m) : Set G)) : ℕ∞)
        < (rk D : ℕ∞) := by
      rw [hquot]
      exact hlt
    have hDm : D ≤ Subgroup.centralizer ({m⁻¹ * x * m} : Set G) :=
      centralizer_singleton_of_mem_cTilde_of_mQuot_lt hV hV₀ hM hN₀ hTI hg hmx hlt'
    have hDmz : D ≤ Subgroup.centralizer (Subgroup.zpowers (m⁻¹ * x * m) : Set G) := by
      rwa [centralizer_zpowers_eq_singleton]
    have hDm' : conjSubgroup D m⁻¹ ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      have hcm : conjSubgroup (Subgroup.centralizer (Subgroup.zpowers (m⁻¹ * x * m) : Set G)) m⁻¹ =
          Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
        rw [E3.conjSubgroup_centralizer, conjSubgroup_zpowers]
        congr 1
        group
      exact (E3.conjSubgroup_mono_left m⁻¹ hDmz).trans (le_of_eq hcm)
    have hv₀conj : m * v₀ * m⁻¹ ∈ conjSubgroup D m⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have he : m⁻¹ * (m * v₀ * m⁻¹) * (m⁻¹)⁻¹ = v₀ := by group
      rw [he]
      exact hv₀D
    exact hDm' hv₀conj
  exact hxV' hVle

theorem commutator_le_inf_of_mQuot_add_lt {M V₀ V A B E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (hA : A ≤ V) {i : ℕ}
    (hi : E3.mQuot V A = i) (hB : B ≤ A)
    (hEA : A ≤ Subgroup.normalizer (E : Set G)) (hEp : IsPGroup 2 E)
    (hlt : (E3.mQuot A B : ℕ∞) + (i : ℕ∞) < min (rMV M V) (mBar M V₀ V hV : ℕ∞)) :
    ⁅E ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤ E ⊓ V₀ := by
  refine Subgroup.commutator_le.2 ?_
  intro e he a ha
  rw [Subgroup.mem_inf] at he
  obtain ⟨heE, heCB⟩ := he
  set Cc : Subgroup G := A ⊓ Subgroup.centralizer ({e} : Set G) with hCc
  have hCA : Cc ≤ A := by rw [hCc]; exact inf_le_left
  have hCV : Cc ≤ V := hCA.trans hA
  have hBC : B ≤ Cc := le_inf hB (by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact heCB b hb)
  have hmC : (E3.mQuot V Cc : ℕ∞) < min (rMV M V) (mBar M V₀ V hV : ℕ∞) := by
    have hadd : E3.mQuot V Cc = E3.mQuot A Cc + E3.mQuot V A := E3.mQuot_add hCA hA
    have hle : E3.mQuot A Cc ≤ E3.mQuot A B := E3.mQuot_mono hBC
    have : (E3.mQuot V Cc : ℕ∞) ≤ (E3.mQuot A B : ℕ∞) + (i : ℕ∞) := by
      rw [hadd, hi, Nat.cast_add]
      exact add_le_add (by exact_mod_cast hle) le_rfl
    exact this.trans_lt hlt
  have hmem : e ∈ M := by
    have hr : (E3.mQuot V Cc : ℕ∞) < rMV M V := lt_of_lt_of_le hmC (min_le_left _ _)
    refine centralizer_le_of_mQuot_lt_rMV hCV hr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [hCc] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hc).2
  obtain ⟨k, hk⟩ : ∃ k, orderOf e = 2 ^ k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hEp) (⟨e, heE⟩ : E)
    exact ⟨k, (Subgroup.orderOf_coe (⟨e, heE⟩ : E)).trans hk⟩
  have heCt : e ∈ F11.CTilde M V₀ V := by
    refine mem_cTilde_of_mQuot_lt hV hV₀ hM hM₀ hmem ⟨k, hk⟩ inf_le_left inf_le_right ?_
    have hle : E3.mQuot V (V ⊓ Subgroup.centralizer ({e} : Set G)) ≤ E3.mQuot V Cc :=
      E3.mQuot_mono (le_inf hCV inf_le_right)
    have : (E3.mQuot V (V ⊓ Subgroup.centralizer ({e} : Set G)) : ℕ∞) ≤ (E3.mQuot V Cc : ℕ∞) := by
      exact_mod_cast hle
    exact this.trans_lt (lt_of_lt_of_le hmC (min_le_right _ _))
  obtain ⟨-, hes, heact⟩ := (mem_cTilde_iff hV hM).1 heCt
  have heV₀ : ∀ v ∈ V, e * v * e⁻¹ * v⁻¹ ∈ V₀ := (actTil_eq_one_iff V₀ V hV ⟨e, hes⟩).1 heact
  have hcommV : ⁅e, a⁆ ∈ V₀ := by
    simpa only [commutatorElement_def] using heV₀ a (hA ha)
  have hcommE : ⁅e, a⁆ ∈ E := by
    have haE : a ∈ Subgroup.normalizer (E : Set G) := hEA ha
    have h1 : a * e⁻¹ * a⁻¹ ∈ E := by
      have h2 : a * e * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 haE e).1 heE
      simpa [mul_assoc] using E.inv_mem h2
    have h3 : e * (a * e⁻¹ * a⁻¹) ∈ E := E.mul_mem heE h1
    simpa only [commutatorElement_def, mul_assoc] using h3
  exact Subgroup.mem_inf.2 ⟨hcommE, hcommV⟩

end CFSG.LocalAnalysis.WeakClosure81
