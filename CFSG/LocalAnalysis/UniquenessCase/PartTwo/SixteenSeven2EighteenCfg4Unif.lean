module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Index
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Triple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_cfg4_natCard_multiplicative (α : Type*) :
    Nat.card (Multiplicative α) = Nat.card α :=
  Nat.card_congr Multiplicative.ofAdd.symm

private theorem s16c167_cfg4_card_of_isElemAbelianOfRank {p n : ℕ} {X : Type} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, s16c167_cfg4_natCard_multiplicative, Nat.card_fun,
    Nat.card_fin, Nat.card_zmod]

private theorem s16c167_cfg4_mul_three_eq_one {X : Type} [Group X]
    (h : IsElemAbelianOfRank 3 3 X) (x : X) : x * x * x = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_mul, map_mul, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_mul, toAdd_one]
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  set a : ZMod 3 := Multiplicative.toAdd (e x) i
  have h3 : (3 : ZMod 3) = 0 := by decide
  have : a + a + a = (3 : ZMod 3) * a := by ring
  rw [this, h3, zero_mul]

private theorem s16c167_cfg4_map_eq_of_mem_stabSub {Y : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub Y) : Y.map g.toMonoidHom = Y := by
  have hginv : ∀ u : W, g (g⁻¹ u) = u := by
    intro u
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_stabSub.mp hg v).mpr hv
  · intro hu
    exact ⟨g⁻¹ u, (mem_stabSub.mp hg (g⁻¹ u)).mp (by rw [hginv u]; exact hu), hginv u⟩

private theorem s16c167_cfg4_inf_ne_bot_of_nine_le {G : Type*} [Group G]
    {A B E : Subgroup G} (hBA : B ≤ A) (hEA : E ≤ A)
    (hA : Nat.card A = 27) (hB : 9 ≤ Nat.card B) (hE : 9 ≤ Nat.card E) : B ⊓ E ≠ ⊥ := by
  intro hbot
  have h1 := Subgroup.relIndex_inf_le (H := B) (K := E) (L := A)
  rw [hbot, Subgroup.relIndex_bot_left, hA] at h1
  have hB' := Subgroup.relIndex_mul_card B A
  have hE' := Subgroup.relIndex_mul_card E A
  rw [inf_of_le_left hBA, hA] at hB'
  rw [inf_of_le_left hEA, hA] at hE'
  have hBi : B.relIndex A ≤ 3 := by nlinarith
  have hEi : E.relIndex A ≤ 3 := by nlinarith
  nlinarith

theorem s16c167_cfg4_block (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup W} (hY : rk ↥Y = 2)
    {r t : MulAut W} (hr3 : r * r * r = 1) (hrY : Y.map r.toMonoidHom = Y)
    (hrne : ¬ Y ≤ fixV (Subgroup.zpowers r)) (ht : t * t = 1) (htY : Y.map t.toMonoidHom = Y)
    (hcomm : t * r = r * t) : Y ≤ fixV (Subgroup.zpowers t) := by
  have hrmem : ∀ y ∈ Y, r y ∈ Y := by
    intro y hy
    have : r y ∈ Y.map r.toMonoidHom := ⟨y, hy, rfl⟩
    rwa [hrY] at this
  have htmem : ∀ y ∈ Y, t y ∈ Y := by
    intro y hy
    have : t y ∈ Y.map t.toMonoidHom := ⟨y, hy, rfl⟩
    rwa [htY] at this
  have hYcard : Nat.card ↥Y = 4 := by
    rw [card_eq_two_pow hW Y, hY]
    norm_num
  haveI : IsKleinFour ↥Y := by
    refine ⟨hYcard, ?_⟩
    have hdvd : Monoid.exponent ↥Y ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
        apply Subtype.ext
        exact hW (g : W)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have hsub : Subsingleton ↥Y := Monoid.exp_eq_one_iff.mp h
      have : Nat.card ↥Y = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      omega
    · exact h
  have hCr : Y ⊓ fixV (Subgroup.zpowers r) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    by_contra hc1
    have hcY : c ∈ Y := hc.1
    have hrc : r c = c := (mem_fixV_zpowers r c).mp hc.2
    obtain ⟨y, hyY, hyr⟩ := Set.not_subset.mp hrne
    have hry : r y ≠ y := fun h => hyr ((mem_fixV_zpowers r y).mpr h)
    let cY : ↥Y := ⟨c, hcY⟩
    let yY : ↥Y := ⟨y, hyY⟩
    let ryY : ↥Y := ⟨r y, hrmem y hyY⟩
    have hcY1 : cY ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hyY1 : yY ≠ 1 := by
      intro h
      have hy1 : y = 1 := congrArg Subtype.val h
      exact hry (by rw [hy1, map_one])
    have hryY1 : ryY ≠ 1 := by
      intro h
      have hry1 : r y = 1 := congrArg Subtype.val h
      apply hry
      have hy1 : y = 1 := r.injective (by rw [hry1, map_one])
      rw [hy1, map_one]
    have hcYcy : cY ≠ yY := by
      intro h
      have hcy : c = y := congrArg Subtype.val h
      apply hry
      rw [← hcy, hrc]
    have hryYcy : ryY ≠ cY := by
      intro h
      apply hcYcy
      apply Subtype.ext
      have hryc : r y = c := congrArg Subtype.val h
      have : r y = r c := by rw [hryc, hrc]
      exact (r.injective this).symm
    have hryYyY : ryY ≠ yY := fun h => hry (congrArg Subtype.val h)
    have hry_eq : ryY = cY * yY :=
      IsKleinFour.eq_mul_of_ne_all hcY1 hyY1 hcYcy hryY1 hryYcy hryYyY
    have hry_val : r y = c * y := congrArg Subtype.val hry_eq
    have hr2y : r (r y) = y := by
      rw [hry_val, map_mul, hrc, hry_val, ← mul_assoc, ← pow_two, hW c, one_mul]
    have hcontra : y = r y := by
      have h1 : r (r (r y)) = r y := congrArg r hr2y
      have h2 : r (r (r y)) = y := by
        have := congrArg (fun (f : MulAut W) => f y) hr3
        simpa using this
      rw [h2] at h1
      exact h1
    exact hry hcontra.symm
  by_cases hCt : Y ⊓ fixV (Subgroup.zpowers t) = ⊥
  · intro y hy
    rw [mem_fixV_zpowers]
    have hz : y * t y ∈ Y ⊓ fixV (Subgroup.zpowers t) := by
      refine ⟨Y.mul_mem hy (htmem y hy), ?_⟩
      change y * t y ∈ fixV (Subgroup.zpowers t)
      rw [mem_fixV_zpowers, map_mul]
      have htt : t (t y) = y := by
        have := congrArg (fun (f : MulAut W) => f y) ht
        simpa using this
      rw [htt, mul_comm (t y) y]
    rw [hCt] at hz
    have hz1 : y * t y = 1 := by simpa using hz
    have : t y = y := by
      have h := congrArg (fun z => y * z) hz1
      rw [mul_one, ← mul_assoc, ← pow_two, hW y, one_mul] at h
      exact h
    exact this
  · have hex : ∃ x : W, x ∈ Y ⊓ fixV (Subgroup.zpowers t) ∧ x ≠ 1 := by
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCt
      exact ⟨(x : W), x.2, fun h => hx (Subtype.ext h)⟩
    obtain ⟨c, hcCt, hc1⟩ := hex
    have hcY : c ∈ Y := hcCt.1
    have hrcCt : r c ∈ Y ⊓ fixV (Subgroup.zpowers t) := by
      refine ⟨hrmem c hcY, ?_⟩
      change r c ∈ fixV (Subgroup.zpowers t)
      rw [mem_fixV_zpowers]
      have h1 : (t * r) c = (r * t) c := by rw [hcomm]
      simpa [(mem_fixV_zpowers t c).mp hcCt.2] using h1
    have hrcY : r c ∈ Y := hrcCt.1
    let cY : ↥Y := ⟨c, hcY⟩
    let rcY : ↥Y := ⟨r c, hrcY⟩
    have hcY1 : cY ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hrcY1 : rcY ≠ 1 := by
      intro h
      have hrc1 : r c = 1 := congrArg Subtype.val h
      apply hc1
      exact r.injective (by rw [hrc1, map_one])
    have hcYrcY : cY ≠ rcY := by
      intro h
      have hcr : c = r c := congrArg Subtype.val h
      have hmem : c ∈ Y ⊓ fixV (Subgroup.zpowers r) :=
        ⟨hcY, (mem_fixV_zpowers r c).mpr hcr.symm⟩
      rw [hCr] at hmem
      exact hc1 (by simpa using hmem)
    have hYleCt : Y ≤ Y ⊓ fixV (Subgroup.zpowers t) := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact ⟨Y.one_mem, (fixV _).one_mem⟩
      by_cases hyc : y = c
      · rw [hyc]
        exact hcCt
      by_cases hyrc : y = r c
      · rw [hyrc]
        exact hrcCt
      · have hz1 : (⟨y, hy⟩ : ↥Y) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
        have hzc : (⟨y, hy⟩ : ↥Y) ≠ cY := fun h => hyc (congrArg Subtype.val h)
        have hzrc : (⟨y, hy⟩ : ↥Y) ≠ rcY := fun h => hyrc (congrArg Subtype.val h)
        have hmul : (⟨y, hy⟩ : ↥Y) = cY * rcY :=
          IsKleinFour.eq_mul_of_ne_all hcY1 hrcY1 hcYrcY hz1 hzc hzrc
        have hy_eq : y = c * r c := by
          have := congrArg Subtype.val hmul
          simpa using this
        rw [hy_eq]
        exact (Y ⊓ fixV (Subgroup.zpowers t)).mul_mem hcCt hrcCt
    intro y hy
    exact (hYleCt hy).2

theorem s16c167_cfg4_unif {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z)
    {t : MulAut W} (htX : t ∈ X) (ht : t * t = 1) {Y₁ Y₂ : Subgroup W}
    (h₁ : Y₁ ∈ conjSubs X Z) (h₂ : Y₂ ∈ conjSubs X Z) (hne : Y₁ ≠ Y₂)
    (ht₁ : Y₁.map t.toMonoidHom = Y₁) (ht₂ : Y₂.map t.toMonoidHom = Y₂) :
    Y₁ ≤ fixV (Subgroup.zpowers t) ↔ Y₂ ≤ fixV (Subgroup.zpowers t) := by
  have key : ∀ Ya Yb : Subgroup W, Ya ∈ conjSubs X Z → Yb ∈ conjSubs X Z → Ya ≠ Yb →
      Ya.map t.toMonoidHom = Ya → Yb.map t.toMonoidHom = Yb →
      Ya ≤ fixV (Subgroup.zpowers t) → Yb ≤ fixV (Subgroup.zpowers t) := by
    intro Ya Yb ha hb hne' hta htb hYa
    have hpair_sub : ({Ya, Yb} : Set (Subgroup W)) ⊆ conjSubs X Z := by
      intro z hz
      rcases (by simpa using hz : z = Ya ∨ z = Yb) with rfl | rfl
      · exact ha
      · exact hb
    have hTcard : ((conjSubs X Z) \ {Ya, Yb}).ncard = 2 := by
      rw [Set.ncard_sdiff hpair_sub, F.ncard_eq, Set.ncard_pair hne']
    obtain ⟨Yc, Yd, hcd, hT⟩ := Set.ncard_eq_two.mp hTcard
    have hcT : Yc ∈ (conjSubs X Z) \ {Ya, Yb} := by rw [hT]; simp
    have hdT : Yd ∈ (conjSubs X Z) \ {Ya, Yb} := by rw [hT]; simp
    have hcS : Yc ∈ conjSubs X Z := hcT.1
    have hdS : Yd ∈ conjSubs X Z := hdT.1
    have hca : Yc ≠ Ya := fun h => hcT.2 (by simp [h])
    have hcb : Yc ≠ Yb := fun h => hcT.2 (by simp [h])
    have hda : Yd ≠ Ya := fun h => hdT.2 (by simp [h])
    have hdb : Yd ≠ Yb := fun h => hdT.2 (by simp [h])
    have hmapinj : ∀ H₁ H₂ : Subgroup W,
        H₁.map t.toMonoidHom = H₂.map t.toMonoidHom → H₁ = H₂ := by
      intro H₁ H₂ hh
      have hc : ∀ H : Subgroup W, (H.map t.toMonoidHom).comap t.toMonoidHom = H := by
        intro H
        ext x
        rw [Subgroup.mem_comap, Subgroup.mem_map_iff_mem t.injective]
      have := congrArg (Subgroup.comap t.toMonoidHom) hh
      rwa [hc H₁, hc H₂] at this
    have htperm : ∀ Y ∈ (conjSubs X Z) \ {Ya, Yb},
        Y.map t.toMonoidHom ∈ ({Yc, Yd} : Set (Subgroup W)) := by
      intro Y hY
      have htS : Y.map t.toMonoidHom ∈ conjSubs X Z := s16c167_cfg4_map_mem htX hY.1
      have hn1 : Y.map t.toMonoidHom ≠ Ya := by
        intro h
        exact hY.2 (by simp [hmapinj Y Ya (by rw [h, hta])])
      have hn2 : Y.map t.toMonoidHom ≠ Yb := by
        intro h
        exact hY.2 (by simp [hmapinj Y Yb (by rw [h, htb])])
      have hnot : Y.map t.toMonoidHom ∉ ({Ya, Yb} : Set (Subgroup W)) := by
        intro hmem
        rcases (by simpa using hmem : Y.map t.toMonoidHom = Ya ∨
            Y.map t.toMonoidHom = Yb) with h | h
        · exact hn1 h
        · exact hn2 h
      have : Y.map t.toMonoidHom ∈ (conjSubs X Z) \ {Ya, Yb} := ⟨htS, hnot⟩
      rwa [hT] at this
    have hYc_mem : Yc.map t.toMonoidHom ∈ ({Yc, Yd} : Set (Subgroup W)) := htperm Yc hcT
    have hYd_mem : Yd.map t.toMonoidHom ∈ ({Yc, Yd} : Set (Subgroup W)) := htperm Yd hdT
    have hYc_cases : Yc.map t.toMonoidHom = Yc ∨ Yc.map t.toMonoidHom = Yd := by
      simpa using hYc_mem
    have hYd_cases : Yd.map t.toMonoidHom = Yc ∨ Yd.map t.toMonoidHom = Yd := by
      simpa using hYd_mem
    have hK : ∀ Y : Subgroup W, (L ⊓ centSub Y).map (MulAut.conj t).toMonoidHom =
        L ⊓ centSub (Y.map t.toMonoidHom) := by
      intro Y
      rw [Subgroup.map_inf L (centSub Y) (MulAut.conj t).toMonoidHom (MulAut.conj t).injective,
        F.norm t htX, s16c167_cfg4_centSub_conj t Y]
    have hRstab : (L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd)).map (MulAut.conj t).toMonoidHom =
        L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd) := by
      rw [Subgroup.map_inf (L ⊓ centSub Yc) (L ⊓ centSub Yd) (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective, hK Yc, hK Yd]
      rcases hYc_cases with h | h
      · have hYd : Yd.map t.toMonoidHom = Yd := by
          have hne_d : Yd.map t.toMonoidHom ≠ Yc :=
            fun hh => hcd (hmapinj Yd Yc (by rw [hh, h])).symm
          rcases hYd_cases with hh | hh
          · exact absurd hh hne_d
          · exact hh
        rw [h, hYd]
      · have hYd : Yd.map t.toMonoidHom = Yc := by
          have hne_d : Yd.map t.toMonoidHom ≠ Yd :=
            fun hh => hcd (hmapinj Yd Yc (by rw [hh]; exact h.symm)).symm
          rcases hYd_cases with hh | hh
          · exact hh
          · exact absurd hh hne_d
        rw [h, hYd, inf_comm]
    have hRcardL : Nat.card ↥L = 27 := by
      rw [s16c167_cfg4_card_of_isElemAbelianOfRank F.elem]
      norm_num
    have hR_ne : L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd) ≠ ⊥ :=
      s16c167_cfg4_inf_ne_bot_of_nine_le
        (A := L) (B := L ⊓ centSub Yc) (E := L ⊓ centSub Yd)
        inf_le_left inf_le_left hRcardL
        (s16c167_cfg4_index F hcS) (s16c167_cfg4_index F hdS)
    have hexr : ∃ x : MulAut W, x ∈ L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd) ∧ x ≠ 1 := by
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
      exact ⟨(x : MulAut W), x.2, fun h => hx (Subtype.ext h)⟩
    obtain ⟨r, hrR, hr1⟩ := hexr
    have hrL : r ∈ L := hrR.1.1
    have hrC : r ∈ centSub Yc := hrR.1.2
    have hrD : r ∈ centSub Yd := hrR.2.2
    have hr3 : r * r * r = 1 := by
      have h := s16c167_cfg4_mul_three_eq_one F.elem (⟨r, hrL⟩ : ↥L)
      simpa using congrArg Subtype.val h
    have hrYb : Yb.map r.toMonoidHom = Yb :=
      s16c167_cfg4_map_eq_of_mem_stabSub (s16c167_cfg4_stab F hb hrL)
    have hrne : ¬ Yb ≤ fixV (Subgroup.zpowers r) := by
      intro hle
      have hr_cent : r ∈ centSub Yb := by
        rw [mem_centSub]
        intro y hy
        exact (mem_fixV_zpowers r y).mp (hle hy)
      have hmem : r ∈ L ⊓ centSub Yb ⊓ centSub Yc ⊓ centSub Yd :=
        ⟨⟨⟨hrL, hr_cent⟩, hrC⟩, hrD⟩
      have hbot := s16c167_cfg4_triple F hb hcS hdS hcb.symm hdb.symm hcd
      rw [hbot] at hmem
      exact hr1 (by simpa using hmem)
    have htconjR : MulAut.conj t r ∈ L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd) := by
      rw [← hRstab]
      exact ⟨r, hrR, rfl⟩
    let s : MulAut W := (t * r * t⁻¹) * r⁻¹
    have hsR : s ∈ L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd) := by
      have := (L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd)).mul_mem htconjR
        ((L ⊓ centSub Yc ⊓ (L ⊓ centSub Yd)).inv_mem hrR)
      simpa [s, MulAut.conj_apply] using this
    have hsL : s ∈ L := hsR.1.1
    have hsC : s ∈ centSub Yc := hsR.1.2
    have hsD : s ∈ centSub Yd := hsR.2.2
    have hta_fix : ∀ y ∈ Ya, t y = y := fun y hy => (mem_fixV_zpowers t y).mp (hYa hy)
    have htia_fix : ∀ y ∈ Ya, t⁻¹ y = y := by
      intro y hy
      have h1 : t⁻¹ (t y) = y := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rwa [hta_fix y hy] at h1
    have hr_stabYa : r ∈ stabSub Ya := s16c167_cfg4_stab F ha hrL
    have hria_mem : ∀ y ∈ Ya, r⁻¹ y ∈ Ya := by
      intro y hy
      refine (mem_stabSub.mp hr_stabYa (r⁻¹ y)).mp ?_
      have : r (r⁻¹ y) = y := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rwa [this]
    have hs_centYa : s ∈ centSub Ya := by
      rw [mem_centSub]
      intro y hy
      show ((t * r * t⁻¹) * r⁻¹) y = y
      simp only [MulAut.mul_apply]
      rw [htia_fix (r⁻¹ y) (hria_mem y hy)]
      have hry : r (r⁻¹ y) = y := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [hry, hta_fix y hy]
    have hs_bot : s ∈ (⊥ : Subgroup (MulAut W)) := by
      have hmem : s ∈ L ⊓ centSub Ya ⊓ centSub Yc ⊓ centSub Yd :=
        ⟨⟨⟨hsL, hs_centYa⟩, hsC⟩, hsD⟩
      have hbot := s16c167_cfg4_triple F ha hcS hdS hca.symm hda.symm hcd
      rwa [hbot] at hmem
    have hs1 : s = 1 := by simpa using hs_bot
    have hcomm' : t * r = r * t := by
      have h2 : (t * r * t⁻¹) * r⁻¹ = 1 := by simpa [s] using hs1
      have h3 : t * r * t⁻¹ = r := by
        calc t * r * t⁻¹ = ((t * r * t⁻¹) * r⁻¹) * r := by group
          _ = r := by rw [h2, one_mul]
      calc t * r = (t * r * t⁻¹) * t := by group
        _ = r * t := by rw [h3]
    refine s16c167_cfg4_block F.sq ?_ hr3 hrYb hrne ht htb hcomm'
    rw [s16c167_cfg4_rk_mem hb, F.rk_eq]
  exact ⟨fun h => key Y₁ Y₂ h₁ h₂ hne ht₁ ht₂ h,
    fun h => key Y₂ Y₁ h₂ h₁ hne.symm ht₂ ht₁ h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
