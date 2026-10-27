module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM2Max
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3Orb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadC15
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocInter

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc

@[expose] def BV : Set (J ⧸ Hj) :=
  {w | w ≠ basePt ∧ ∃ g : J, ((g : J) : J ⧸ Hj) = w ∧ ∀ x ∈ V0, g⁻¹ * x * g ∈ Eg uJ 11}

theorem smul_mk (k g : J) : k • ((g : J) : J ⧸ Hj) = ((k * g : J) : J ⧸ Hj) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]

theorem mk_eq_basePt_iff {g : J} : ((g : J) : J ⧸ Hj) = basePt ↔ g ∈ Hj := by
  rw [← smul_basePt_eq_mk, smul_basePt_eq_self_iff]

theorem Ig_mul_Hj (hM : MatFacts) (G h : J) (hh : h ∈ Hj) :
    Ig (G * h) = Ig G := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have := Hj_normalizes_Eg hM h hh _ hx'
    have e : h * ((G * h)⁻¹ * x * (G * h)) * h⁻¹ = G⁻¹ * x * G := by group
    rwa [e] at this
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have := Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) _ hx'
    have e : h⁻¹ * (G⁻¹ * x * G) * h⁻¹⁻¹ = (G * h)⁻¹ * x * (G * h) := by group
    rwa [e] at this

theorem conjSub_V0_subset_Ig (hM : MatFacts) {k g : J}
    (hk : k ∈ Hj) (hg : ∀ x ∈ V0, g⁻¹ * x * g ∈ Eg uJ 11) :
    ((conjSub k V0 : Subgroup J) : Set J) ⊆ Ig (k * g) := by
  intro x hx
  have hv : k⁻¹ * x * k ∈ V0 := mem_conjSub.mp hx
  refine ⟨?_, ?_⟩
  · have := Hj_normalizes_Eg hM k hk _ (V0_le_Eg' hM hv)
    have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    rwa [e] at this
  · have := hg _ hv
    have e : g⁻¹ * (k⁻¹ * x * k) * g = (k * g)⁻¹ * x * (k * g) := by group
    rwa [e] at this

section Count

theorem toFinset_eq_of_maskSub_eq
    (hM : MatFacts) {A B : List ℕ} (hA : A ∈ trioL) (hB : B ∈ trioL)
    (h : maskSub A = maskSub B) : A.toFinset = B.toFinset := by
  have key : ∀ {A B : List ℕ}, A ∈ trioL → B ∈ trioL → maskSub A = maskSub B →
      ∀ a ∈ A, a ∈ B := by
    intro A B hA hB h a ha
    have h1 : eta uJ 11 a ∈ maskSub A :=
      (mem_maskSub_iff hM (trio_xor A hA).1 (trio_xor A hA).2).2 ⟨a, ha, rfl⟩
    rw [h] at h1
    obtain ⟨c, hc, e⟩ := (mem_maskSub_iff hM (trio_xor B hB).1 (trio_xor B hB).2).1 h1
    have := eta_inj' hM ((trio_prop.2 A hA).2.1 a ha) ((trio_prop.2 B hB).2.1 c hc) e
    rw [this]
    exact hc
  ext a
  simp only [List.mem_toFinset]
  exact ⟨key hA hB h a, key hB hA h.symm a⟩

theorem ncard_BV_le
    (hF : J4Facts) :
    BV.ncard ≤ 5 := by
  have hM := hF.mat
  obtain ⟨f, hW, hfinj⟩ := w15_enum
  have hz0 : z0 ∈ Zl := z0_mem_Zl
  have hz0E : z0 ∈ Eg uJ 11 := mem_Eg_of_mem_Zl hz0
  have hk : ∀ j : Fin 15, ∃ k ∈ Hj, maskSub (f j) = conjSub k V0 := fun j =>
    trio_orbit hM _ (w15_subset_trio _ (hW j))
  choose k hkH hkW using hk
  have hmem : ∀ j : Fin 15, ∀ w ∈ BV, k j • w ∈ Opt z0 ∧ k j • w ≠ basePt := by
    intro j w hw
    obtain ⟨hwb, g, rfl, hg⟩ := hw
    refine ⟨⟨k j * g, (smul_mk _ _).symm, ?_⟩, ?_⟩
    · have h1131 : 1131 ∈ f j := one_mem_of_mem_w15 (hW j)
      have hx := w15_subset_trio _ (hW j)
      have hz : z0 ∈ maskSub (f j) :=
        (mem_maskSub_iff hM (trio_xor _ hx).1 (trio_xor _ hx).2).2 ⟨1131, h1131, rfl⟩
      rw [hkW j] at hz
      have hv : (k j)⁻¹ * z0 * k j ∈ V0 := mem_conjSub.mp hz
      have := hg _ hv
      have e : g⁻¹ * ((k j)⁻¹ * z0 * k j) * g = (k j * g)⁻¹ * z0 * (k j * g) := by group
      rwa [e] at this
    · intro h
      apply hwb
      rw [smul_mk] at h
      have : k j * g ∈ Hj := mk_eq_basePt_iff.mp h
      have hg' : g ∈ Hj := by
        have := Hj.mul_mem (Hj.inv_mem (hkH j)) this
        simpa using this
      rw [mk_eq_basePt_iff]
      exact hg'
  let F : ↥BV × Fin 15 → ↥(Opt z0 \ {basePt}) := fun p =>
    ⟨k p.2 • (p.1 : J ⧸ Hj), (hmem p.2 p.1 p.1.2).1, (hmem p.2 p.1 p.1.2).2⟩
  have hinj : Function.Injective F := by
    rintro ⟨⟨w, hw⟩, j⟩ ⟨⟨w', hw'⟩, j'⟩ hF'
    have h1 : k j • w = k j' • w' := congrArg Subtype.val hF'
    obtain ⟨hwb, g, rfl, hg⟩ := hw
    obtain ⟨hwb', g', rfl, hg'⟩ := hw'
    rw [smul_mk, smul_mk] at h1
    have h2 : (k j * g)⁻¹ * (k j' * g') ∈ Hj := QuotientGroup.eq.mp h1
    have hG' : k j' * g' = (k j * g) * ((k j * g)⁻¹ * (k j' * g')) := by group
    have hIg : Ig (k j' * g') = Ig (k j * g) := by
      rw [hG']
      exact Ig_mul_Hj hM _ _ h2
    have hgH : g ∉ Hj := fun h => hwb (mk_eq_basePt_iff.mpr h)
    have hGnH : k j * g ∉ Hj := fun h => hgH (by
      have := Hj.mul_mem (Hj.inv_mem (hkH j)) h
      simpa using this)
    have hsub1 := conjSub_V0_subset_Ig hM (hkH j) hg
    have hsub2 := conjSub_V0_subset_Ig hM (hkH j') hg'
    rw [hIg] at hsub2
    have hc8 : (Ig (k j * g)).ncard ≤ 8 := card_inter_le hF hGnH
    have hn : ∀ j : Fin 15, ((conjSub (k j) V0 : Subgroup J) : Set J).ncard = 8 := fun j => by
      rw [ncard_conjSub, ← Nat.card_coe_set_eq]
      exact card_V0 hM
    have eq1 := Set.eq_of_subset_of_ncard_le hsub1 (by rw [hn j]; exact hc8) (Set.toFinite _)
    have eq2 := Set.eq_of_subset_of_ncard_le hsub2 (by rw [hn j']; exact hc8) (Set.toFinite _)
    have hset : ((conjSub (k j) V0 : Subgroup J) : Set J) = conjSub (k j') V0 := eq1.trans eq2.symm
    have hgrp : maskSub (f j) = maskSub (f j') := by
      rw [hkW j, hkW j']
      exact SetLike.coe_injective hset
    have hjj : j = j' := hfinj j j' (toFinset_eq_of_maskSub_eq hM (w15_subset_trio _ (hW j))
      (w15_subset_trio _ (hW j')) hgrp)
    subst hjj
    have hww : ((g : J) : J ⧸ Hj) = ((g' : J) : J ⧸ Hj) := by
      have := h1
      exact smul_left_cancel (k j) (by rw [smul_mk, smul_mk]; exact this)
    exact Prod.ext (Subtype.ext hww) rfl
  have hcard := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin, Nat.card_coe_set_eq] at hcard
  have hbase : basePt ∈ Opt z0 := ⟨1, rfl, by simpa using hz0E⟩
  have h77 := ncard_Opt_le hF hz0
  have hdiff : (Opt z0 \ {basePt}).ncard = (Opt z0).ncard - 1 :=
    Set.ncard_sdiff_singleton_of_mem hbase
  omega

theorem not_nine_dvd_card_centralizer_V0
    (hF : J4Facts) :
    ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer (V0 : Set J)) := by
  have hM := hF.mat
  set D := Subgroup.centralizer (V0 : Set J) with hD
  have hED : Eg uJ 11 ≤ D := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Eg_comm (elem_uJ hM) (V0_le_Eg' hM hv) hx
  have hmod := orbit_ncard_mod_four_J hF D hED
  have hsub : {w : J ⧸ Hj | ∃ d ∈ D, d • basePt = w} ⊆ insert basePt BV := by
    rintro _ ⟨d, hd, rfl⟩
    by_cases hdH : d ∈ Hj
    · exact Or.inl (smul_basePt_eq_self_iff.mpr hdH)
    · right
      refine ⟨?_, d, (smul_basePt_eq_mk d).symm, ?_⟩
      · rw [smul_basePt_eq_mk]
        intro h
        exact hdH (mk_eq_basePt_iff.mp h)
      · intro x hx
        have hxd := Subgroup.mem_centralizer_iff.mp hd x hx
        have e : d⁻¹ * x * d = x := by rw [mul_assoc, hxd, inv_mul_cancel_left]
        rw [e]
        exact V0_le_Eg' hM hx
  have hS6 : {w : J ⧸ Hj | ∃ d ∈ D, d • basePt = w}.ncard ≤ 6 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by have := ncard_BV_le hF; omega))
  have hfix : ∀ g : J, g • basePt = basePt ↔ g ∈ Hj := fun g => smul_basePt_eq_self_iff
  have hcardD := CFSG.Sporadic.J4.QT2.card_eq_orbit_mul_inf D Hj basePt hfix
  have hDH : D ⊓ Hj = CV := inf_comm _ _
  have hS : MulAction.orbit ↥D basePt = {w : J ⧸ Hj | ∃ d ∈ D, d • basePt = w} := by
    ext w
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  rw [hDH, hS, Nat.card_coe_set_eq, card_CV hF] at hcardD
  rw [hcardD]
  generalize {w : J ⧸ Hj | ∃ d ∈ D, d • basePt = w}.ncard = s at hmod hS6 ⊢
  have hs : s = 1 ∨ s = 5 := by omega
  rcases hs with rfl | rfl <;> norm_num

end Count

end CFSG.Quasithin.J4Rad
