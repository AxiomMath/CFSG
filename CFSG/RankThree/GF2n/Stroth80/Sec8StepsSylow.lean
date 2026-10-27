module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsClose81
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec78FixedMod
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec8_exists_mem_normalizer_not_mem {H : Type} [Group H] [Finite H] (T P : Subgroup H)
    (hT : IsPGroup 2 T) (hPT : P < T) :
    ∃ g : H, g ∈ T ∧ g ∈ Subgroup.normalizer (P : Set H) ∧ g ∉ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent
  have htop : P.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    exact lt_irrefl P (lt_of_lt_of_le hPT (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨g, hgN, hgP⟩ := SetLike.exists_of_lt (hnc _ htop)
  have hgN' : g ∈ (Subgroup.normalizer (P : Set H)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hPT.le]
    exact hgN
  have hgP' : (g : H) ∉ P := fun h => hgP (Subgroup.mem_subgroupOf.mpr h)
  exact ⟨(g : H), g.2, Subgroup.mem_subgroupOf.mp hgN', hgP'⟩

theorem sec8_exists_sylow_of_normalizer_le {H : Type} [Group H] [Finite H] (N P : Subgroup H)
    (hP : IsPGroup 2 P) (hPN : P ≤ N)
    (hmax : ∀ S : Subgroup H, IsPGroup 2 S → S ≤ N → P ≤ S → S = P)
    (hnorm : ∀ g ∈ Subgroup.normalizer (P : Set H), g ∈ N) :
    ∃ S : Sylow 2 H, S.toSubgroup = P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hPT : P < S.toSubgroup := lt_of_le_of_ne hPS (Ne.symm hne)
  obtain ⟨g, hgT, hgN, hgP⟩ := sec8_exists_mem_normalizer_not_mem S.toSubgroup P S.isPGroup' hPT
  have hgN' : g ∈ N := hnorm g hgN
  have hS₁T : P ⊔ Subgroup.zpowers g ≤ S.toSubgroup :=
    sup_le hPT.le (Subgroup.zpowers_le.mpr hgT)
  have hS₁N : P ⊔ Subgroup.zpowers g ≤ N := sup_le hPN (Subgroup.zpowers_le.mpr hgN')
  have hS₁2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers g) := S.isPGroup'.to_le hS₁T
  have heq : P ⊔ Subgroup.zpowers g = P := hmax _ hS₁2 hS₁N le_sup_left
  have hmem : g ∈ P ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rw [heq] at hmem
  exact hgP hmem

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8SylowCore (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h53 : Stroth53Statement) (hTI : Sec8TIStatement) (hZV : Sec8ZVStatement)
    (hpt : Sec8PointTIStatement) (hD : Sec8LemmaDStatement) (hD' : Sec8DPrimeStatement)
    (hH : Sec8LemmaHStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) (hna : ¬ Conc81a hc t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZL : Z0 ≤ LB M Q B) {T : Subgroup G}
    (hT2 : IsPGroup 2 ↥T) (hTM : T ≤ M) (hLT : LB M Q B ≤ T)
    (hTN : T ≤ Subgroup.normalizer (Z0 : Set G)) {g : G} (hg : g ∈ M)
    (hgT : conjSubgroup g T = T) : g ∈ Subgroup.normalizer (Z0 : Set G) := by
  by_contra hgZ
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t h5 (Or.inl hs.spNat)).1
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hLp : IsPGroup 2 ↥(LB M Q B) := Ctx.isPGroup_LB h34 hc h5.width h5.n_gt h5.noA2 h5.gen
  have hQ2 : IsPGroup 2 ↥Q := hLp.to_le sec39_Q_le_LB
  have hNV : ∀ s ∈ M, s ∈ Subgroup.normalizer (Z0 : Set G) →
      s ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    intro s hsM hsZ
    have hst : s * t * s⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hsZ t).mp htZ0
    have hstQ : s * t * s⁻¹ ∉ Q := by
      intro h
      apply h5.notQ
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hsM)) _).mp h
      have e : s⁻¹ * (s * t * s⁻¹) * s⁻¹⁻¹ = t := by group
      rwa [e] at h1
    have h1 := hZV G M Q Z B hc n t hs Z0 hZ0 (s * t * s⁻¹) hst hstQ
    have h2 := Ut_conj_of_normalizes (hc.conj_Q_eq hsM) (hc.conj_Z_eq hsM) t
    refine conjSubgroup_eq_self_iff.mp ?_
    calc conjSubgroup s (Vt M (LB M Q B) B Z t) = conjSubgroup s (Ut Q Z t) := by rw [← hV]
      _ = Ut Q Z (s * t * s⁻¹) := h2.symm
      _ = Vt M (LB M Q B) B Z t := h1
  have hTVg : ∀ s ∈ T, s ∈ Subgroup.normalizer
      ((conjSubgroup g (Vt M (LB M Q B) B Z t) : Subgroup G) : Set G) := by
    intro s hsT
    have h1 : g⁻¹ * s * g ∈ T := by
      rw [← hgT] at hsT
      exact mem_conjSubgroup.mp hsT
    have h2 := hNV _ (M.mul_mem (M.mul_mem (M.inv_mem hg) (hTM hsT)) hg) (hTN h1)
    refine conjSubgroup_eq_self_iff.mp ?_
    have e : s * g = g * (g⁻¹ * s * g) := by group
    rw [← conjSubgroup_mul, e, conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr h2]
  have hZ0g_le : conjSubgroup g Z0 ≤ T := by
    have h1 : conjSubgroup g Z0 ≤ conjSubgroup g T := Subgroup.map_mono (hZL.trans hLT)
    rwa [hgT] at h1
  have hZ0_norm : ∀ z ∈ Z0, z ∈ Subgroup.normalizer ((conjSubgroup g Z0 : Subgroup G) : Set G) := by
    intro z hz
    have hzT : z ∈ T := hLT (hZL hz)
    have h1 : g⁻¹ * z * g ∈ T := by
      rw [← hgT] at hzT
      exact mem_conjSubgroup.mp hzT
    have h2 : conjSubgroup (g⁻¹ * z * g) Z0 = Z0 := conjSubgroup_eq_self_iff.mpr (hTN h1)
    refine conjSubgroup_eq_self_iff.mp ?_
    have e : z * g = g * (g⁻¹ * z * g) := by group
    rw [← conjSubgroup_mul, e, conjSubgroup_mul, h2]
  have hinter : ∀ u ∈ Z0, u ∈ conjSubgroup g Z0 → u ∈ Q := by
    intro u hu hug
    by_contra huQ
    have hs' : g⁻¹ * u * g ∈ Z0 := mem_conjSubgroup.mp hug
    have hsQ : g⁻¹ * u * g ∉ Q := by
      intro h
      apply huQ
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) _).mp h
      have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rwa [e] at h1
    have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    exact hgZ (hTI G M Q Z B hc n t hs Z0 hZ0 g hg _ hs' hsQ (by rw [e]; exact hu))
  have hcomm : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q := by
    intro z hz y hy
    have hyN : y ∈ Subgroup.normalizer (Z0 : Set G) := hTN (hZ0g_le hy)
    apply hinter
    · have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Z0.mul_mem hz ((Subgroup.mem_normalizer_iff.mp hyN z⁻¹).mp (Z0.inv_mem hz))
    · have e : ⁅z, y⁆ = (z * y * z⁻¹) * y⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact (conjSubgroup g Z0).mul_mem ((Subgroup.mem_normalizer_iff.mp (hZ0_norm z hz) y).mp hy)
        ((conjSubgroup g Z0).inv_mem hy)
  have hVg_Q : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q := by
    have h1 : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ conjSubgroup g Q := Subgroup.map_mono hVQ
    rwa [hc.conj_Q_eq hg] at h1
  have hZVg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    have h1 : conjSubgroup g Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono sec39_Z_le_Vt
    rwa [hc.conj_Z_eq hg] at h1
  have hZltVg : Z < conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine lt_of_le_of_ne hZVg fun heq => ?_
    have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
    have h1 : conjSubgroup g B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := Subgroup.map_mono hBV
    rw [← heq] at h1
    obtain ⟨g', hg'⟩ := hc.conj
    have hcard : Nat.card ↥Z ≤ Nat.card ↥(conjSubgroup g B) := by
      rw [card_conjSubgroup, hg', card_conjSubgroup]
    have h2 : conjSubgroup g B = Z := Subgroup.eq_of_le_of_card_ge h1 hcard
    apply hc.ne
    have h3 : conjSubgroup g⁻¹ (conjSubgroup g B) = conjSubgroup g⁻¹ Z := by rw [h2]
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, hc.conj_Z_eq (M.inv_mem hg)] at h3
  obtain ⟨d, hdVg, hdZ, hdfix⟩ := sec7ctr_exists_fixed_mod (T := T)
    (D := conjSubgroup g (Vt M (LB M Q B) B Z t)) (V := Z) hT2
    ((hQ2.to_le hVg_Q)) hZltVg
    (fun x hx y hy => hc.hyp.toHyp79.comm_mem_V (hVg_Q hx) (hVg_Q hy))
    (fun x hx => hc.hyp.toHyp79.sq_mem_V (hVg_Q hx))
    (fun s hsT x hx => (Subgroup.mem_normalizer_iff.mp (hTVg s hsT) x).mp hx)
    (fun s hsT x hx =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hTM hsT)) x).mp hx)
  have hCQ : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    hc.CQt_eq_of_3_4 h5.width h5.n_gt h5.noA2
      (h34 G M Q Z B hc n h5.width h5.n_gt h5.noA2 h5.gen)
  have hdB : d ∈ (B ⊔ Z : Subgroup G) := by
    have hd : d ∈ CQt Q Z (LB M Q B) := ⟨hVg_Q hdVg, fun l hl => hdfix l (hLT hl)⟩
    rw [hCQ] at hd
    exact hd
  have hc' : Ctx M Q Z (conjSubgroup g B) := hc.conj_of_mem hg
  have hno' : NoA2 Q Z (LB M Q (conjSubgroup g B)) := hc.noA2_conj h5.noA2 hg
  have hCQ' : CQt Q Z (LB M Q (conjSubgroup g B)) = ((conjSubgroup g B ⊔ Z : Subgroup G) : Set G) :=
    hc'.CQt_eq_of_3_4 h5.width h5.n_gt hno'
      (h34 G M Q Z (conjSubgroup g B) hc' n h5.width h5.n_gt hno' (h5.gen.conj_of_mem hg))
  have hdBg : d ∈ (conjSubgroup g B ⊔ Z : Subgroup G) := by
    have hd : d ∈ CQt Q Z (LB M Q (conjSubgroup g B)) := by
      refine ⟨hVg_Q hdVg, fun l hl => hdfix l ?_⟩
      rw [hc.LB_conj hg] at hl
      have h1 : l ∈ conjSubgroup g T := Subgroup.map_mono hLT hl
      rwa [hgT] at h1
    rw [hCQ'] at hd
    exact hd
  have hBZV : (B ⊔ Z : Subgroup G) ≤ Vt M (LB M Q B) B Z t :=
    sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt
  have hZVV : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_inf sec39_Z_le_Vt hZVg
  have hlt : Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine lt_of_le_of_ne hZVV fun heq => hdZ ?_
    rw [heq]
    exact ⟨hBZV hdB, hdVg⟩
  have hBgZ : conjSubgroup g B ⊔ Z = B ⊔ Z := hpt G M Q Z B hc g hg ⟨d, hdB, hdBg, hdZ⟩
  obtain ⟨h, hh, hsub⟩ := hD' G M Q Z B hc n t hs hna Z0 hZ0 g hg hlt
  have hx₀Z0 : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [e]
    exact htZ0
  have hx₀N : g * t * g⁻¹ ∈ hc.CN t := (hsub hx₀Z0).2
  have hb := (h53.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl).2
  have hd5 := (h53.2.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl).1
  have hW : ∀ w ∈ Sec8W1 M Q Z B t r, ⁅g * t * g⁻¹, w⁆ ∈ Sec8V1 M Q Z B t r :=
    fun w hw => hb _ hx₀N w hw
  obtain ⟨m, -, hmsp⟩ := hs.sp
  have hcount := (hD G M Q Z B hc n t hs r hr m hmsp g hg hW).2
  have hx₀H : g * t * g⁻¹ ∈ H0 M Z := sec8_conj_mem_H0 hc hg (hc.LB_le_H0 ht)
  have hUtW : Ut Q Z (g * t * g⁻¹) ≤ Wt Q (Sec8V1 M Q Z B t r) :=
    Ut_le_Wt_of_vanish hc hV1Q hx₀H (fun v hv => hd5 _ hx₀N v hv)
  have hVgW : ∀ v ∈ Vt M (LB M Q B) B Z t, g * v * g⁻¹ ∈ Sec8W1 M Q Z B t r := by
    intro v hv
    have h1 : g * v * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rw [e]
      exact hv
    rw [sec8_conj_V_eq_Ut hc hV hg] at h1
    exact hUtW h1
  have hgBZ : g ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [conjSubgroup_sup', hc.conj_Z_eq hg, hBgZ]
  have hgL : g ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (hc.mem_normalizer_LB_iff' h5.width h5.n_gt h5.noA2 hg).mpr hgBZ
  have hgR := hH G M Q Z B hc n t hs r hr m hmsp g hg hgL hVgW hcount
  exact hgZ (sec8NormR_le_normZ0 hc hZ0 hg hgR)

section Wrapper

variable [(Q.subgroupOf M).Normal]

theorem sec8_mk_mem_normalizer_bar {S : Subgroup G} (hQS : Q ≤ S) (y : M)
    (hy : (y : G) ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈ Subgroup.normalizer (bar M Q S : Set (Mbar M Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) n
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQS, mk_mem_bar_iff_sec4 hQS]
  exact Subgroup.mem_normalizer_iff.mp hy (z : G)

theorem sec8_mem_normalizer_of_mk_mem_normalizer_bar {L : Subgroup G} (hQL : Q ≤ L) (hLM : L ≤ M)
    (y : M) (hN : QuotientGroup.mk' (Q.subgroupOf M) y ∈
      Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    (y : G) ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hLM hz⟩ : M) ∈ bar M Q L :=
    (mk_mem_bar_iff_sec4 hQL _).mpr hz
  have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  exact (mk_mem_bar_iff_sec4 hQL _).mp h2

@[expose] def sec8_preBar (M Q : Subgroup G) [(Q.subgroupOf M).Normal] (C : Subgroup (Mbar M Q)) :
    Subgroup G :=
  (C.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

theorem sec8_mem_preBar {C : Subgroup (Mbar M Q)} (y : M) :
    (y : G) ∈ sec8_preBar M Q C ↔ QuotientGroup.mk' (Q.subgroupOf M) y ∈ C := by
  unfold sec8_preBar
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).trans Subgroup.mem_comap

theorem sec8_preBar_le (C : Subgroup (Mbar M Q)) : sec8_preBar M Q C ≤ M := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

theorem sec8_Q_le_preBar (C : Subgroup (Mbar M Q)) (hQM : Q ≤ M) : Q ≤ sec8_preBar M Q C := by
  intro x hx
  have h := (sec8_mem_preBar (C := C) ⟨x, hQM hx⟩).mpr
  refine h ?_
  have : QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hQM hx⟩ : M) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  rw [this]
  exact C.one_mem

theorem sec8_bar_preBar (C : Subgroup (Mbar M Q)) : bar M Q (sec8_preBar M Q C) = C := by
  unfold bar
  have hsub : (sec8_preBar M Q C).subgroupOf M = C.comap (QuotientGroup.mk' (Q.subgroupOf M)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, sec8_mem_preBar, Subgroup.mem_comap]
  rw [hsub, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (Q.subgroupOf M)) C]

theorem sec8Sylow_of (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h53 : Stroth53Statement) (hA : Sec8AExistsStatement)
    (hTI : Sec8TIStatement) (hZV : Sec8ZVStatement) (hpt : Sec8PointTIStatement)
    (hD : Sec8LemmaDStatement) (hD' : Sec8DPrimeStatement) (hH : Sec8LemmaHStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r)
    (hna : ¬ Conc81a hc t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer (bar M Q Z0 : Set (Mbar M Q)) := by
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZL' : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hQ2 : IsPGroup 2 ↥Q :=
    (Ctx.isPGroup_LB h34 hc h5.width h5.n_gt h5.noA2 h5.gen).to_le hQL
  set Zb : Subgroup (Mbar M Q) := bar M Q Z0 with hZb
  set NZ : Subgroup (Mbar M Q) := Subgroup.normalizer (Zb : Set (Mbar M Q)) with hNZ
  set Lb : Subgroup (Mbar M Q) := bar M Q (LB M Q B) with hLb
  have hLp : IsPGroup 2 Lb := CFSG.Open.IsElemAbelian.isPGroup (Ctx.isElemAbelian_bar_LB hc)
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hLNZ : Lb ≤ NZ := by
    intro l hl
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) l
    have hyL : (y : G) ∈ LB M Q B := (mk_mem_bar_iff_sec4 hQL y).mp hl
    exact sec8_mk_mem_normalizer_bar hQZ0 y
      (hZ0.mem_normalizer hnormQ (le_Rt (M := M) (LB M Q B) ht hyL))
  have hLpNZ : IsPGroup 2 (Lb.subgroupOf NZ) :=
    hLp.comap_of_injective NZ.subtype Subtype.val_injective
  obtain ⟨S, hLS⟩ := hLpNZ.exists_le_sylow
  set S' : Subgroup (Mbar M Q) := S.toSubgroup.map NZ.subtype with hS'
  have hS'p : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'NZ : S' ≤ NZ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hLbS' : Lb ≤ S' := by
    intro l hl
    exact ⟨⟨l, hLNZ hl⟩, hLS (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  have hmax : ∀ S₂ : Subgroup (Mbar M Q), IsPGroup 2 S₂ → S₂ ≤ NZ → S' ≤ S₂ → S₂ = S' := by
    intro S₂ hS₂ hS₂N hS'S₂
    have hp : IsPGroup 2 (S₂.subgroupOf NZ) :=
      hS₂.comap_of_injective NZ.subtype Subtype.val_injective
    have hle : S.toSubgroup ≤ S₂.subgroupOf NZ := by
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr (hS'S₂ ⟨y, hy, rfl⟩)
    have heq := S.is_maximal' hp hle
    refine le_antisymm (fun x hx => ?_) hS'S₂
    have hxs : (⟨x, hS₂N hx⟩ : NZ) ∈ S₂.subgroupOf NZ := Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at hxs
    exact ⟨_, hxs, rfl⟩
  set T : Subgroup G := sec8_preBar M Q S' with hT
  have hQT : Q ≤ T := sec8_Q_le_preBar S' hQM
  have hTM : T ≤ M := sec8_preBar_le S'
  have hbarT : bar M Q T = S' := sec8_bar_preBar S'
  have hT2 : IsPGroup 2 ↥T := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hS'p
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hQ2
    have hcard := bar_card_mul_card_of_le (M := M) hQT hTM
    rw [hbarT, ha, hb] at hcard
    exact IsPGroup.of_card (n := a + b) (by rw [← hcard, pow_add])
  have hLT : LB M Q B ≤ T := by
    intro l hl
    have hlM : l ∈ M := hLM hl
    have : QuotientGroup.mk' (Q.subgroupOf M) (⟨l, hlM⟩ : M) ∈ S' :=
      hLbS' ((mk_mem_bar_iff_sec4 hQL ⟨l, hlM⟩).mpr hl)
    exact (sec8_mem_preBar ⟨l, hlM⟩).mpr this
  have hTN : T ≤ Subgroup.normalizer (Z0 : Set G) := by
    intro y hy
    have hyM : y ∈ M := hTM hy
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hyM⟩ : M) ∈ S' :=
      (sec8_mem_preBar ⟨y, hyM⟩).mp hy
    exact sec8_mem_normalizer_of_mk_mem_normalizer_bar hQZ0 hZ0M ⟨y, hyM⟩ (hS'NZ h1)
  refine ?_
  obtain ⟨P, hP⟩ := sec8_exists_sylow_of_normalizer_le NZ S' hS'p hS'NZ hmax (by
    intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) gb
    have hgT : (g : G) ∈ Subgroup.normalizer (T : Set G) := by
      refine sec8_mem_normalizer_of_mk_mem_normalizer_bar hQT hTM g ?_
      rw [hbarT]
      exact hgb
    have hgZ := sec8SylowCore h34 h310chi h53 hTI hZV hpt hD hD' hH hs hr hna hZ0 hZL' hT2 hTM
      hLT hTN g.2 (conjSubgroup_eq_self_iff.mpr hgT)
    exact sec8_mk_mem_normalizer_bar hQZ0 g hgZ)
  exact ⟨P, by rw [hP]; exact hS'NZ⟩

end Wrapper

theorem close81Sylow_of (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h53 : Stroth53Statement) (hA : Sec8AExistsStatement)
    (hTI : Sec8TIStatement) (hZV : Sec8ZVStatement) (hpt : Sec8PointTIStatement)
    (hD : Sec8LemmaDStatement) (hD' : Sec8DPrimeStatement) (hH : Sec8LemmaHStatement) :
    Close81SylowStatement := by
  intro G _ _ M Q Z B _ hc n t r h Z0 hZ0
  obtain ⟨hs, hr, hna, -⟩ := h
  exact sec8Sylow_of h34 h310chi h51 h53 hA hTI hZV hpt hD hD' hH hs hr hna hZ0

end CFSG.RankThree.GF2n.Stroth80
