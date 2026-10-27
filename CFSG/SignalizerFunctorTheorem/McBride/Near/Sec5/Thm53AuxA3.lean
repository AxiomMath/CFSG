module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA0
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxSmear
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Subdirect
public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KHat

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] [Finite Γ]

section Crd

variable {S : Set (Subgroup Γ)} {K : Subgroup Γ}

open Classical in
noncomputable def crd (hdp : IsDirectProduct S K) (J : Subgroup Γ) (u : Γ) : Γ :=
  if h : J ∈ S ∧ u ∈ K then ((hdp.coord h.1 ⟨u, h.2⟩ : J) : Γ) else 1

theorem crd_eq (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {u : Γ} (hu : u ∈ K) :
    crd hdp J u = ((hdp.coord hJ ⟨u, hu⟩ : J) : Γ) := by
  unfold crd
  simp [hJ, hu]

theorem crd_mem (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {u : Γ} (hu : u ∈ K) :
    crd hdp J u ∈ J := by
  rw [crd_eq hdp hJ hu]
  exact (hdp.coord hJ ⟨u, hu⟩).2

theorem crd_mul (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {u v : Γ}
    (hu : u ∈ K) (hv : v ∈ K) : crd hdp J (u * v) = crd hdp J u * crd hdp J v := by
  rw [crd_eq hdp hJ (mul_mem hu hv), crd_eq hdp hJ hu, crd_eq hdp hJ hv]
  exact congrArg Subtype.val (map_mul (hdp.coord hJ) ⟨u, hu⟩ ⟨v, hv⟩)

theorem crd_inv (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {u : Γ}
    (hu : u ∈ K) : crd hdp J u⁻¹ = (crd hdp J u)⁻¹ := by
  rw [crd_eq hdp hJ (inv_mem hu), crd_eq hdp hJ hu]
  exact congrArg Subtype.val (map_inv (hdp.coord hJ) ⟨u, hu⟩)

theorem crd_of_mem (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {x : Γ}
    (hx : x ∈ J) : crd hdp J x = x := by
  rw [crd_eq hdp hJ (hdp.le hJ hx)]
  exact hdp.coord_of_mem hJ hx

theorem crd_of_mem_ne (hdp : IsDirectProduct S K) {J J' : Subgroup Γ} (hJ : J ∈ S)
    (hJ' : J' ∈ S) (hne : J' ≠ J) {x : Γ} (hx : x ∈ J') : crd hdp J x = 1 := by
  rw [crd_eq hdp hJ (hdp.le hJ' hx)]
  exact congrArg Subtype.val (hdp.coord_of_mem_ne hJ hJ' hne hx)

theorem crd_eq_one_iff (hdp : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {u : Γ}
    (hu : u ∈ K) : crd hdp J u = 1 ↔ u ∈ sSup (S \ {J}) := by
  rw [crd_eq hdp hJ hu]
  constructor
  · intro h
    exact (hdp.coord_eq_one_iff hJ ⟨u, hu⟩).mp (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val ((hdp.coord_eq_one_iff hJ ⟨u, hu⟩).mpr h)

theorem crd_conj (hdp : IsDirectProduct S K) {a : Γ}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup Γ} (hJ : J ∈ S) {u : Γ}
    (hu : u ∈ K) :
    crd hdp (J.map (MulAut.conj a).toMonoidHom) (a * u * a⁻¹) = a * crd hdp J u * a⁻¹ := by
  rw [crd_eq hdp (ha J hJ) (hdp.conj_mem ha hu), crd_eq hdp hJ hu]
  exact hdp.coord_conj ha hJ hu

end Crd

section Diag

variable {p : ℕ} {X : Subgroup Γ}

theorem exists_smear_elem (hp : p.Prime) (hsol : sol X = ⊥) {b : Γ}
    (hbX : b ∈ Subgroup.normalizer (X : Set Γ)) (hbp : b ^ p = 1) {J : Subgroup Γ}
    (hJ : J ∈ lcal X) (hbJ : b ∉ Subgroup.normalizer (J : Set Γ)) {x : Γ} (hx : x ∈ J) :
    ∃ u ∈ perfRes (cenIn (kOf X) {b}),
      crd (isDirectProduct_lcal_kOf hsol) J u = x ∧
      (∀ a ∈ Subgroup.zpowers b, crd (isDirectProduct_lcal_kOf hsol)
        (J.map (MulAut.conj a).toMonoidHom) u = a * x * a⁻¹) ∧
      (∀ J'' ∈ lcal X, (∀ a ∈ Subgroup.zpowers b, J'' ≠ J.map (MulAut.conj a).toMonoidHom) →
        crd (isDirectProduct_lcal_kOf hsol) J'' u = 1) := by
  set A := Subgroup.zpowers b with hA
  set hdp := isDirectProduct_lcal_kOf hsol with hhdp
  have hAX : A ≤ Subgroup.normalizer (X : Set Γ) := Subgroup.zpowers_le.mpr hbX
  have hperm : ∀ a ∈ A, ∀ J' ∈ lcal X, J'.map (MulAut.conj a).toMonoidHom ∈ lcal X :=
    fun a ha J' hJ' => map_conj_mem_lcal hJ' (hAX ha)
  let S' : Set (Subgroup Γ) := {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}
  have hL : IsDirectProduct S' (orbitClosure J A) := isDirectProduct_orbit hAX hJ
  have hAS : ∀ a ∈ A, ∀ K ∈ S', K.map (MulAut.conj a).toMonoidHom ∈ S' := by
    rintro a ha _ ⟨a', ha', rfl⟩
    refine ⟨a * a', mul_mem ha ha', ?_⟩
    rw [Thm52Aux.map_conj_map_conj]
  have hJS : J ∈ S' := ⟨1, one_mem A, by ext x; simp⟩
  have hN : A ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ :=
    Thm52Aux.zpowers_inf_normalizer_eq_bot hp hbp hbJ
  have hS'lc : ∀ K ∈ S', K ∈ lcal X := by
    rintro _ ⟨a, ha, rfl⟩
    exact hperm a ha J hJ
  have hΔperf : Group.IsPerfect ↥(smear J A) := by
    obtain ⟨e⟩ := Thm52Aux.nonempty_mulEquiv_smear hp hbX hbp hJ hbJ
    obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
    have hJperf : Group.IsPerfect ↥J :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hΔle : smear J A ≤ cenIn (kOf X) {b} := by
    refine le_inf ((smear_le_orbitClosure J A).trans (Thm52Aux.orbitClosure_le_kOf hsol hAX hJ)) ?_
    rw [← Thm52Aux.centralizer_zpowers_eq]
    exact smear_le_centralizer J A
  have hxproj : x ∈ projIn S' J (orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ)) := by
    rw [projIn_centralizer_eq hL hAS hJS, hN]
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh]
    simp
  obtain ⟨y, hy, hyx⟩ := (hL.mem_projIn_iff hJS).mp hxproj
  have hyΔ : (y : Γ) ∈ smear J A := hy
  have hyK : (y : Γ) ∈ kOf X := (hΔle hyΔ).1
  have hyC : ∀ a ∈ A, a * (y : Γ) * a⁻¹ = y := by
    intro a ha
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 a ha
    rw [this]
    group
  have hcrdJ : crd hdp J (y : Γ) = x := by
    have hyJ : (y : Γ) ∈ J ⊔ sSup (S' \ {J}) := by
      rw [(hL.isDirectPair hJS).sup_eq]
      exact y.2
    obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_of_commute (hL.commute_sSup_diff hJS)).mp hyJ
    have h1 := hL.coord_mul hJS hj hl
    have hy' : (⟨j * l, mul_mem (hL.le hJS hj) (hL.sSup_diff_le _ Set.sdiff_subset hl)⟩ :
        orbitClosure J A) = y := Subtype.ext hjl
    rw [hy'] at h1
    have hjx : j = x := by rw [← hyx, h1]
    have hsub : S' \ {J} ⊆ lcal X \ {J} := fun K hK => ⟨hS'lc K hK.1, hK.2⟩
    have hl' : l ∈ sSup (lcal X \ {J}) := sSup_le_sSup hsub hl
    have hlK : l ∈ kOf X := hdp.sSup_diff_le _ Set.sdiff_subset hl'
    have hjK : j ∈ kOf X := hdp.le hJ hj
    rw [← hjl, crd_mul hdp hJ hjK hlK, crd_of_mem hdp hJ hj, (crd_eq_one_iff hdp hJ hlK).mpr hl',
      mul_one, hjx]
  refine ⟨y, le_perfRes_of_isPerfect hΔperf hΔle hyΔ, hcrdJ, ?_, ?_⟩
  · intro a ha
    have h1 := crd_conj hdp (a := a) (hperm a ha) hJ hyK
    rw [hyC a ha, hcrdJ] at h1
    exact h1
  · intro J'' hJ'' hne
    refine (crd_eq_one_iff hdp hJ'' hyK).mpr ?_
    have : orbitClosure J A ≤ sSup (lcal X \ {J''}) := by
      refine orbitClosure_le fun a ha => ?_
      exact le_sSup ⟨hperm a ha J hJ, fun h => hne a ha h.symm⟩
    exact this y.2

end Diag

section Tie

variable {X : Subgroup Γ}

theorem exists_tie (hsol : sol X = ⊥) {H : Subgroup Γ} (hHK : H ≤ kOf X)
    (hH : ∀ J ∈ lcal X, projIn (lcal X) J H = J) {J : Subgroup Γ} (hJ : J ∈ lcal X)
    (hne : H ⊓ J = ⊥) :
    ∃ J' ∈ lcal X, J' ≠ J ∧ ∀ u ∈ H, ∀ u' ∈ H,
      (crd (isDirectProduct_lcal_kOf hsol) J u = crd (isDirectProduct_lcal_kOf hsol) J u' →
        crd (isDirectProduct_lcal_kOf hsol) J' u = crd (isDirectProduct_lcal_kOf hsol) J' u') ∧
      (crd (isDirectProduct_lcal_kOf hsol) J u ≠ 1 →
        crd (isDirectProduct_lcal_kOf hsol) J' u ≠ 1) := by
  classical
  set hdp := isDirectProduct_lcal_kOf hsol with hhdp
  have hsemi : IsSemisimple (kOf X) := isSemisimple_kOf hsol
  have hlc : lcal (kOf X) = lcal X := by
    rw [hsemi.lcal_eq, simpleComponents_kOf hsol]
  obtain ⟨P, -, hPU, hPd, hPdp, hPdiag⟩ :=
    exists_partition_isDiagonal hsemi hHK (by rw [hlc]; exact hH)
  rw [hlc] at hPU
  obtain ⟨T, hT, hJT⟩ : ∃ T ∈ P, J ∈ T := by
    have : J ∈ ⋃₀ P := by rw [hPU]; exact hJ
    exact Set.mem_sUnion.mp this
  have hTsub : T ⊆ lcal X := fun K hK => by
    rw [← hPU]
    exact Set.mem_sUnion.mpr ⟨T, hT, hK⟩
  obtain ⟨hDle, hdiag⟩ := hPdiag T hT
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
    rintro rfl
    exact hnc inferInstance
  have hTne : ∃ J' ∈ T, J' ≠ J := by
    by_contra hcon
    push Not at hcon
    have hTeq : T = {J} := Set.eq_singleton_iff_unique_mem.mpr ⟨hJT, hcon⟩
    have h1 := (hdiag J hJT).2
    rw [hTeq, sSup_singleton] at h1
    have h2 : projIn ({J} : Set (Subgroup Γ)) J (H ⊓ J) ≤ H ⊓ J := by
      unfold projIn proj
      refine (Subgroup.closure_le _).mpr ?_
      rintro j ⟨hjJ, l, hl, hjl⟩
      rw [Set.sdiff_self, sSup_empty, Subgroup.mem_bot] at hl
      rw [hl, mul_one] at hjl
      exact hjl
    rw [h1, hne] at h2
    exact hJ0 (le_bot_iff.mp h2)
  obtain ⟨J', hJ'T, hJ'ne⟩ := hTne
  have hdecomp : ∀ u ∈ H, ∃ d ∈ H ⊓ sSup T, ∀ J'' ∈ T, crd hdp J'' u = crd hdp J'' d := by
    intro u hu
    have hDF : H ⊓ sSup T ∈ (fun T' => H ⊓ sSup T') '' P := ⟨T, hT, rfl⟩
    have hpair := hPdp.isDirectPair hDF
    have huH : u ∈ (H ⊓ sSup T) ⊔ sSup (((fun T' => H ⊓ sSup T') '' P) \ {H ⊓ sSup T}) := by
      rw [hpair.sup_eq]
      exact hu
    obtain ⟨d, hd, r, hr, hdr⟩ := (mem_sup_iff_of_commute hpair.commute).mp huH
    refine ⟨d, hd, fun J'' hJ'' => ?_⟩
    have hrH : r ∈ H := hPdp.sSup_diff_le _ Set.sdiff_subset hr
    have hrK : r ∈ kOf X := hHK hrH
    have hdK : d ∈ kOf X := hHK (Subgroup.mem_inf.mp hd).1
    have hr1 : crd hdp J'' r = 1 := by
      refine (crd_eq_one_iff hdp (hTsub hJ'') hrK).mpr ?_
      have hle : sSup (((fun T' => H ⊓ sSup T') '' P) \ {H ⊓ sSup T}) ≤
          sSup (lcal X \ {J''}) := by
        refine sSup_le fun E hE => ?_
        obtain ⟨⟨T', hT', rfl⟩, hEne⟩ := hE
        have hT'T : T' ≠ T := by
          rintro rfl
          exact hEne rfl
        have hdisj : Disjoint T' T := hPd hT' hT hT'T
        have hT'sub : T' ⊆ lcal X := fun K hK => by
          rw [← hPU]
          exact Set.mem_sUnion.mpr ⟨T', hT', hK⟩
        refine inf_le_right.trans (sSup_le_sSup fun K hK => ⟨hT'sub hK, fun h => ?_⟩)
        exact Set.disjoint_left.mp hdisj hK (by rw [Set.mem_singleton_iff] at h; rw [h]; exact hJ'')
      exact hle hr
    rw [← hdr, crd_mul hdp (hTsub hJ'') hdK hrK, hr1, mul_one]
  have hinj : ∀ J₀ ∈ T, ∀ d ∈ H ⊓ sSup T, crd hdp J₀ d = 1 → d = 1 := by
    intro J₀ hJ₀ d hd h1
    have hdK : d ∈ kOf X := hHK (Subgroup.mem_inf.mp hd).1
    have hdT : d ∈ sSup T := (Subgroup.mem_inf.mp hd).2
    have hTins : insert J₀ (T \ {J₀}) = T := by
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hJ₀]
    have hsupT : sSup T = J₀ ⊔ sSup (T \ {J₀}) := by
      conv_lhs => rw [← hTins]
      rw [sSup_insert]
    have hsubT : T \ {J₀} ⊆ lcal X \ {J₀} := Set.sdiff_subset_sdiff_left hTsub
    rw [hsupT] at hdT
    obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      hdp.commute_sSup_diff (hTsub hJ₀) x hx y (sSup_le_sSup hsubT hy)).mp hdT
    have hlK : l ∈ kOf X := hdp.sSup_diff_le _ Set.sdiff_subset (sSup_le_sSup hsubT hl)
    have hjK : j ∈ kOf X := hdp.le (hTsub hJ₀) hj
    have hl1 : crd hdp J₀ l = 1 := (crd_eq_one_iff hdp (hTsub hJ₀) hlK).mpr (sSup_le_sSup hsubT hl)
    have hj1 : j = 1 := by
      rw [← hjl, crd_mul hdp (hTsub hJ₀) hjK hlK, hl1, mul_one, crd_of_mem hdp (hTsub hJ₀) hj]
        at h1
      exact h1
    have hdl : d = l := by rw [← hjl, hj1, one_mul]
    have : d ∈ (H ⊓ sSup T) ⊓ sSup (T \ {J₀}) := Subgroup.mem_inf.mpr ⟨hd, hdl ▸ hl⟩
    rw [(hdiag J₀ hJ₀).1, Subgroup.mem_bot] at this
    exact this
  refine ⟨J', hTsub hJ'T, hJ'ne, fun u hu u' hu' => ⟨fun heq => ?_, fun hne1 => ?_⟩⟩
  · obtain ⟨d, hd, hdu⟩ := hdecomp u hu
    obtain ⟨d', hd', hdu'⟩ := hdecomp u' hu'
    have hdK : d ∈ kOf X := hHK (Subgroup.mem_inf.mp hd).1
    have hdK' : d' ∈ kOf X := hHK (Subgroup.mem_inf.mp hd').1
    have h1 : crd hdp J d = crd hdp J d' := by
      rw [← hdu J hJT, ← hdu' J hJT]
      exact heq
    have h2 : d = d' := by
      have h3 : crd hdp J (d⁻¹ * d') = 1 := by
        rw [crd_mul hdp (hTsub hJT) (inv_mem hdK) hdK', crd_inv hdp (hTsub hJT) hdK, h1,
          inv_mul_cancel]
      exact inv_mul_eq_one.mp (hinj J hJT (d⁻¹ * d') (mul_mem (inv_mem hd) hd') h3)
    rw [hdu J' hJ'T, hdu' J' hJ'T, h2]
  · obtain ⟨d, hd, hdu⟩ := hdecomp u hu
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hne1
      rw [hdu J hJT, crd_of_mem hdp (hTsub hJT) (one_mem J)]
    rw [hdu J' hJ'T]
    exact fun h => hd1 (hinj J' hJ'T d hd h)

end Tie

section Generation

variable {p : ℕ} {X : Subgroup Γ}

omit [Finite Γ] in
theorem exists_ne_one_le_centralizer (hp : p.Prime) {B J : Subgroup Γ} (hB : IsElemAbelian p B)
    (hcard : Nat.card B = p ^ 2) (hBJ : B ≤ Subgroup.normalizer (J : Set Γ))
    (hAut : ∀ P : Subgroup (MulAut ↥J), IsPGroup p ↥P → Nat.card P ∣ p) :
    ∃ b ∈ B, b ≠ 1 ∧ J ≤ Subgroup.centralizer {b} := by
  by_contra hcon
  push Not at hcon
  let f : ↥B →* MulAut ↥J := (J.normalizerMonoidHom).comp (Subgroup.inclusion hBJ)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro b hb
    by_contra hb1
    have hb1' : (b : Γ) ≠ 1 := fun h => hb1 (Subtype.ext h)
    refine hcon b b.2 hb1' (fun t ht => ?_)
    have h1 : ((f b ⟨t, ht⟩ : ↥J) : Γ) = (b : Γ) * t * (b : Γ)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨b, hBJ b.2⟩ ⟨t, ht⟩
    rw [hb] at h1
    have h2 : t = (b : Γ) * t * (b : Γ)⁻¹ := by simpa using h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (b : Γ) = ((b : Γ) * t * (b : Γ)⁻¹) * b := by rw [← h2]
      _ = (b : Γ) * t := by group
  have hP : IsPGroup p ↥f.range :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B hB).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
  have h1 := hAut f.range hP
  have h2 : Nat.card ↥f.range = Nat.card ↥B :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h2, hcard] at h1
  have := Nat.le_of_dvd hp.pos h1
  nlinarith [hp.two_le]

theorem exists_mem_not_mem_zpowers (hp : p.Prime) {B : Subgroup Γ} (hB : IsElemAbelian p B)
    (hcard : Nat.card B = p ^ 2) {b : Γ} (hb : b ∈ B) :
    ∃ b' ∈ B, b' ∉ Subgroup.zpowers b := by
  by_contra h
  push Not at h
  have hle : B ≤ Subgroup.zpowers b := h
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers] at h1
  have h2 : orderOf b ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 b hb))
  nlinarith [hp.two_le]

theorem kOf_le_iSup_perfRes_cenIn (hp : p.Prime) (hsol : sol X = ⊥) {B : Subgroup Γ}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set Γ))
    (hcard : Nat.card B = p ^ 2)
    (hAut : ∀ J ∈ lcal X, ∀ P : Subgroup (MulAut ↥J), IsPGroup p ↥P → Nat.card P ∣ p) :
    kOf X ≤ ⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf X) {b}) := by
  set U := ⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf X) {b}) with hU
  set hdp := isDirectProduct_lcal_kOf hsol with hhdp
  have hsemi : IsSemisimple (kOf X) := isSemisimple_kOf hsol
  have hlc : lcal (kOf X) = lcal X := by
    rw [hsemi.lcal_eq, simpleComponents_kOf hsol]
  have hgen : ∀ b ∈ B, b ≠ 1 → perfRes (cenIn (kOf X) {b}) ≤ U := fun b hb hb1 =>
    le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)
  have hUK : U ≤ kOf X :=
    iSup₂_le fun b _ => iSup_le fun _ => (perfRes_le _).trans inf_le_left
  have hBp : ∀ b ∈ B, b ^ p = 1 := hB.2
  have hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have := hB.1
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨c, hc⟩)
  have hJinfo : ∀ J ∈ lcal X, J ≠ ⊥ ∧ Group.IsPerfect ↥J ∧ J ≤ kOf X := by
    intro J hJ
    obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
    refine ⟨?_, TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc,
      Thm52Aux.le_kOf_of_mem_lcal hJ⟩
    rintro rfl
    exact hnc inferInstance
  have hcaseA : ∀ J ∈ lcal X, ∀ b ∈ B, b ≠ 1 → J ≤ Subgroup.centralizer {b} → J ≤ U := by
    intro J hJ b hb hb1 hJb
    obtain ⟨-, hperf, hJK⟩ := hJinfo J hJ
    exact (le_perfRes_of_isPerfect hperf (le_inf hJK hJb)).trans (hgen b hb hb1)
  have houtside : ∀ J ∈ lcal X, (¬ ∃ b ∈ B, b ≠ 1 ∧ J ≤ Subgroup.centralizer {b}) →
      ∃ b ∈ B, b ≠ 1 ∧ b ∉ Subgroup.normalizer (J : Set Γ) := by
    intro J hJ hnc
    by_contra hcon
    push Not at hcon
    refine hnc (exists_ne_one_le_centralizer hp hB hcard (fun b hb => ?_) (hAut J hJ))
    by_cases hb1 : b = 1
    · rw [hb1]
      exact one_mem _
    · exact hcon b hb hb1
  have hproj : ∀ J ∈ lcal X, projIn (lcal X) J U = J := by
    intro J hJ
    refine le_antisymm (projIn_le J U) fun x hx => ?_
    rw [hdp.mem_projIn_iff hJ]
    by_cases hc : ∃ b ∈ B, b ≠ 1 ∧ J ≤ Subgroup.centralizer {b}
    · obtain ⟨b, hb, hb1, hJb⟩ := hc
      have hxU : x ∈ U := hcaseA J hJ b hb hb1 hJb hx
      exact ⟨⟨x, hUK hxU⟩, hxU, hdp.coord_of_mem hJ hx⟩
    · obtain ⟨b, hb, hb1, hbJ⟩ := houtside J hJ hc
      obtain ⟨u, hu, hcrd, -, -⟩ := exists_smear_elem hp hsol (hBX hb) (hBp b hb) hJ hbJ hx
      have huU : u ∈ U := hgen b hb hb1 hu
      refine ⟨⟨u, hUK huU⟩, huU, ?_⟩
      rw [← crd_eq hdp hJ (hUK huU)]
      exact hcrd
  have hint : ∀ J ∈ lcal X, U ⊓ J ≠ ⊥ := by
    intro J hJ hbot
    obtain ⟨hJ0, -, -⟩ := hJinfo J hJ
    by_cases hc : ∃ b ∈ B, b ≠ 1 ∧ J ≤ Subgroup.centralizer {b}
    · obtain ⟨b, hb, hb1, hJb⟩ := hc
      rw [inf_eq_right.mpr (hcaseA J hJ b hb hb1 hJb)] at hbot
      exact hJ0 hbot
    · obtain ⟨b, hb, hb1, hbJ⟩ := houtside J hJ hc
      obtain ⟨J', hJ'lc, hJ'ne, htie⟩ := exists_tie hsol hUK hproj hJ hbot
      obtain ⟨x₀, hx₀J, hx₀1⟩ : ∃ x ∈ J, x ≠ 1 := by
        obtain ⟨⟨x, hxJ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJ0
        exact ⟨x, hxJ, fun h => hx1 (Subtype.ext h)⟩
      have hconj1 : J.map (MulAut.conj (1 : Γ)).toMonoidHom = J := by
        ext y
        simp
      by_cases hN : ∃ b₀ ∈ B, b₀ ≠ 1 ∧ b₀ ∈ Subgroup.normalizer (J : Set Γ)
      ·
        obtain ⟨b₀, hb₀, hb₀1, hb₀N⟩ := hN
        obtain ⟨x, hxJ, hxnc⟩ : ∃ x ∈ J, ¬ (x * b₀ = b₀ * x) := by
          by_contra hcon
          push Not at hcon
          exact hc ⟨b₀, hb₀, hb₀1, fun x hx =>
            Subgroup.mem_centralizer_singleton_iff.mpr (hcon x hx)⟩
        have hx1 : x ≠ 1 := fun h => hxnc (by rw [h]; simp)
        have hbb₀ : b * b₀ ∈ B := mul_mem hb hb₀
        have hbb₀N : b * b₀ ∉ Subgroup.normalizer (J : Set Γ) := fun h => hbJ (by
          have := mul_mem h (inv_mem hb₀N)
          simpa using this)
        have hbb₀1 : b * b₀ ≠ 1 := fun h => hbb₀N (h ▸ one_mem _)
        obtain ⟨u, hu, hcrdu, hconju, hsuppu⟩ :=
          exists_smear_elem hp hsol (hBX hb) (hBp b hb) hJ hbJ hxJ
        obtain ⟨u', hu', hcrdu', hconju', -⟩ :=
          exists_smear_elem hp hsol (hBX hbb₀) (hBp _ hbb₀) hJ hbb₀N hxJ
        have huU : u ∈ U := hgen b hb hb1 hu
        have hu'U : u' ∈ U := hgen _ hbb₀ hbb₀1 hu'
        obtain ⟨hi, hii⟩ := htie u huU u' hu'U
        have h1 := hi (by rw [hcrdu, hcrdu'])
        have h2 : crd hdp J' u ≠ 1 := hii (by rw [hcrdu]; exact hx1)
        obtain ⟨a, haA, hJ'a⟩ : ∃ a ∈ Subgroup.zpowers b,
            J' = J.map (MulAut.conj a).toMonoidHom := by
          by_contra hcon
          push Not at hcon
          exact h2 (hsuppu J' hJ'lc hcon)
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp haA
        have hbk : b ^ k ≠ 1 := by
          intro h
          exact hJ'ne (by rw [hJ'a, h, hconj1])
        have hcomm' : Commute b b₀ := hcomm b hb b₀ hb₀
        have ha' : (b * b₀) ^ k ∈ Subgroup.zpowers (b * b₀) := Subgroup.zpow_mem_zpowers _ _
        have hbn : J.map (MulAut.conj (b₀ ^ k)).toMonoidHom = J :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem hb₀N k)
        have hJ'a' : J.map (MulAut.conj ((b * b₀) ^ k)).toMonoidHom = J' := by
          rw [hcomm'.mul_zpow, ← Thm52Aux.map_conj_map_conj, hbn]
          exact hJ'a.symm
        have hu1 := hconju (b ^ k) haA
        have hu2 := hconju' ((b * b₀) ^ k) ha'
        rw [← hJ'a] at hu1
        rw [hJ'a'] at hu2
        rw [hu1, hu2, hcomm'.mul_zpow] at h1
        have h3 : b₀ ^ k * x * (b₀ ^ k)⁻¹ = x := by
          calc b₀ ^ k * x * (b₀ ^ k)⁻¹
              = (b ^ k)⁻¹ * (b ^ k * b₀ ^ k * x * (b ^ k * b₀ ^ k)⁻¹) * b ^ k := by group
            _ = (b ^ k)⁻¹ * (b ^ k * x * (b ^ k)⁻¹) * b ^ k := by rw [h1]
            _ = x := by group
        by_cases hb₀k : b₀ ^ k = 1
        · have : Fact p.Prime := ⟨hp⟩
          have hb_ord : orderOf b = p := orderOf_eq_prime (hBp b hb) hb1
          have hb₀_ord : orderOf b₀ = p := orderOf_eq_prime (hBp b₀ hb₀) hb₀1
          have hdvd : (orderOf b₀ : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hb₀k
          rw [hb₀_ord, ← hb_ord] at hdvd
          exact hbk (orderOf_dvd_iff_zpow_eq_one.mp hdvd)
        · have hmem : b₀ ^ k ∈ Subgroup.zpowers b₀ := Subgroup.zpow_mem_zpowers _ _
          have heq := Thm52Aux.zpowers_eq_of_mem_zpowers hp (hBp b₀ hb₀) hb₀1 hmem hb₀k
          have hb₀mem : b₀ ∈ Subgroup.zpowers (b₀ ^ k) := by
            rw [heq]
            exact Subgroup.mem_zpowers b₀
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb₀mem
          have hcx : Commute x (b₀ ^ k) := by
            show x * b₀ ^ k = b₀ ^ k * x
            calc x * b₀ ^ k = (b₀ ^ k * x * (b₀ ^ k)⁻¹) * b₀ ^ k := by rw [h3]
              _ = b₀ ^ k * x := by group
          have := hcx.zpow_right m
          rw [hm] at this
          exact hxnc this.eq
      · push Not at hN
        obtain ⟨b', hb'B, hb'not⟩ := exists_mem_not_mem_zpowers hp hB hcard hb
        have hb'1 : b' ≠ 1 := fun h => hb'not (h ▸ one_mem _)
        have hb'J : b' ∉ Subgroup.normalizer (J : Set Γ) := hN b' hb'B hb'1
        obtain ⟨u, hu, hcrdu, hconju, hsuppu⟩ :=
          exists_smear_elem hp hsol (hBX hb) (hBp b hb) hJ hbJ hx₀J
        obtain ⟨u', hu', hcrdu', hconju', hsuppu'⟩ :=
          exists_smear_elem hp hsol (hBX hb'B) (hBp b' hb'B) hJ hb'J hx₀J
        have huU : u ∈ U := hgen b hb hb1 hu
        have hu'U : u' ∈ U := hgen b' hb'B hb'1 hu'
        have h2 : crd hdp J' u ≠ 1 := (htie u huU u huU).2 (by rw [hcrdu]; exact hx₀1)
        have h2' : crd hdp J' u' ≠ 1 := (htie u' hu'U u' hu'U).2 (by rw [hcrdu']; exact hx₀1)
        obtain ⟨a, haA, hJ'a⟩ : ∃ a ∈ Subgroup.zpowers b,
            J' = J.map (MulAut.conj a).toMonoidHom := by
          by_contra hcon
          push Not at hcon
          exact h2 (hsuppu J' hJ'lc hcon)
        obtain ⟨a', ha'A, hJ'a'⟩ : ∃ a' ∈ Subgroup.zpowers b',
            J' = J.map (MulAut.conj a').toMonoidHom := by
          by_contra hcon
          push Not at hcon
          exact h2' (hsuppu' J' hJ'lc hcon)
        have haB : a ∈ B := Subgroup.zpowers_le.mpr hb haA
        have ha'B : a' ∈ B := Subgroup.zpowers_le.mpr hb'B ha'A
        have hN2 : a'⁻¹ * a ∈ Subgroup.normalizer (J : Set Γ) := by
          have hmap : J.map (MulAut.conj (a'⁻¹ * a)).toMonoidHom = J := by
            rw [← Thm52Aux.map_conj_map_conj, ← hJ'a, hJ'a', Thm52Aux.map_conj_map_conj,
              inv_mul_cancel, hconj1]
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
        have hdiff : a'⁻¹ * a = 1 := by
          by_contra hne
          exact hN _ (mul_mem (inv_mem ha'B) haB) hne hN2
        have haa' : a = a' := by
          have := inv_mul_eq_one.mp hdiff
          exact this.symm
        by_cases ha1 : a = 1
        · exact hJ'ne (by rw [hJ'a, ha1, hconj1])
        · have e1 := Thm52Aux.zpowers_eq_of_mem_zpowers hp (hBp b hb) hb1 haA ha1
          have e2 := Thm52Aux.zpowers_eq_of_mem_zpowers hp (hBp b' hb'B) hb'1
            (haa' ▸ ha'A : a ∈ Subgroup.zpowers b') ha1
          refine hb'not ?_
          rw [← e1, e2]
          exact Subgroup.mem_zpowers b'
  have hUeq : U = kOf X :=
    eq_of_projIn_eq_of_inf_ne_bot hsemi hUK (by rw [hlc]; exact hproj) (by rw [hlc]; exact hint)
  exact hUeq.ge

end Generation

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
