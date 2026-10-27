module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3F

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_subgroupOf_closure {G : Type*} [Group G] {K : Subgroup G} {Y : Set G}
    (hY : Y ⊆ K) : (closure Y).subgroupOf K = closure (K.subtype ⁻¹' Y) := by
  have hclK : closure Y ≤ K := (Subgroup.closure_le K).mpr hY
  have ha : ((closure Y).subgroupOf K).map K.subtype = closure Y := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hclK]
  have hb : (closure (K.subtype ⁻¹' Y)).map K.subtype = closure Y := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hy
      exact ⟨⟨y, hY hy⟩, hy, rfl⟩
  apply (Subgroup.map_subtype_inj (H := K)).mp
  rw [ha, hb]

theorem s16h_exists_order_three_of_torus_res {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W} (hU : rk ↥U = 6) {L : Subgroup (MulAut W)}
    (hL : Nat.card ↥L = 3) (hLU : L ≤ stabSub U) (hfix : U ⊓ fixV L = ⊥)
    {D J : Subgroup (MulAut W)} (hD : IsElemAbelian 3 D) (hDU : D ≤ stabSub U)
    (hD27 : 27 * Nat.card ↥(D ⊓ centSub U) ≤ Nat.card ↥D)
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d) (hJU : J ≤ stabSub U)
    (hJL : ∀ y ∈ J, ∀ l ∈ L, y * l = l * y) (hJc : J ⊓ centSub U = ⊥)
    (hDJ : D ≤ normalizer (J : Set (MulAut W)))
    (hJgen : ∃ Y : Set (MulAut W), (∀ g ∈ Y, g ^ 2 = 1) ∧ J = closure Y) (hJ2 : ¬ IsPGroup 2 J) :
    ∃ y ∈ J, y ^ 3 = 1 ∧ y ∉ L := by
  have hUcard : Nat.card ↥U = 64 := by
    rw [card_eq_two_pow hW U, hU]
    norm_num
  haveI hLnt : Nontrivial ↥L :=
    (Finite.one_lt_card_iff_nontrivial (α := ↥L)).mp (by rw [hL]; norm_num)
  obtain ⟨l₀, hl₀ne⟩ := exists_ne (1 : ↥L)
  let l : MulAut W := (l₀ : MulAut W)
  have hl_mem : l ∈ L := l₀.2
  have hl3 : l ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := l₀)
    rw [hL] at h
    have h' : ((l₀ : MulAut W)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, h]
      rfl
    simpa [l] using h'
  have hl_ne : l ≠ 1 := by
    intro h
    exact hl₀ne (Subtype.ext h)
  have hLgen : Subgroup.zpowers l = L := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le_of_mem hl_mem
    · simp [Nat.card_zpowers, orderOf_eq_prime hl3 hl_ne, hL]
  let lS : stabSub U := ⟨l, hLU hl_mem⟩
  let l' : MulAut ↥U := resHom U lS
  have hlS3 : lS ^ 3 = 1 := Subtype.ext (by simpa using hl3)
  have hl'3 : l' ^ 3 = 1 := by
    change (resHom U lS) ^ 3 = 1
    rw [← map_pow, hlS3, map_one]
  have hl'_ne : l' ≠ 1 := by
    intro h
    have h' : resHom U lS = 1 := h
    have hker : lS ∈ (resHom U).ker := MonoidHom.mem_ker.mpr h'
    rw [ker_resHom, Subgroup.mem_subgroupOf] at hker
    have hfixU : U ≤ fixV L := by
      intro u hu
      rw [← hLgen]
      exact mem_fixV_zpowers_iff_apply.mpr (hker u hu)
    have hUbot : U = ⊥ := by
      have : U ≤ U ⊓ fixV L := le_inf le_rfl hfixU
      exact le_bot_iff.mp (hfix ▸ this)
    have h0 : rk ↥U = 0 := by
      rw [hUbot]
      exact rk_bot
    omega
  have hl' : orderOf l' = 3 := orderOf_eq_prime hl'3 hl'_ne
  have hfpf : ∀ u : ↥U, l' u = u → u = 1 := by
    intro u hu
    have hmem : (u : W) ∈ fixV L := by
      rw [← hLgen]
      refine mem_fixV_zpowers_iff_apply.mpr ?_
      have hw : ((resHom U lS u : ↥U) : W) = (u : W) :=
        congrArg (fun w : ↥U => (w : W)) hu
      rw [resHom_apply] at hw
      exact hw
    have hbot : (u : W) ∈ (⊥ : Subgroup W) := by
      rw [← hfix]
      exact ⟨u.2, hmem⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hD'ea : IsElemAbelian 3 (autSub D U) :=
    (hD.subgroupOf (stabSub U)).map (resHom U)
  have hD'27 : 27 ≤ Nat.card ↥(autSub D U) := by
    have hcard := card_autSub_mul (V := W) (A := D) (U := U) hDU
    have hpos : 0 < Nat.card ↥(D ⊓ centSub U) := Nat.card_pos
    have h27' : 27 * Nat.card ↥(D ⊓ centSub U)
        ≤ Nat.card ↥(autSub D U) * Nat.card ↥(D ⊓ centSub U) := by
      rw [hcard]
      exact hD27
    exact Nat.le_of_mul_le_mul_right h27' hpos
  have hD'l : autSub D U ≤ Subgroup.centralizer ({l'} : Set (MulAut ↥U)) := by
    intro d' hd'
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨dQ, hdSD, hdSrfl⟩ := mem_autSub.mp hd'
    have hcomm : lS * dQ = dQ * lS := by
      apply Subtype.ext
      change (l : MulAut W) * (dQ : MulAut W) = (dQ : MulAut W) * l
      exact (hDL (dQ : MulAut W) hdSD l hl_mem).symm
    rw [← hdSrfl]
    change resHom U lS * resHom U dQ = resHom U dQ * resHom U lS
    rw [← map_mul, ← map_mul, hcomm]
  have hJ'l : autSub J U ≤ Subgroup.centralizer ({l'} : Set (MulAut ↥U)) := by
    intro y' hy'
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨yS, hySJ, hySrfl⟩ := mem_autSub.mp hy'
    have hcomm : lS * yS = yS * lS := by
      apply Subtype.ext
      change (l : MulAut W) * (yS : MulAut W) = (yS : MulAut W) * l
      exact (hJL (yS : MulAut W) hySJ l hl_mem).symm
    rw [← hySrfl]
    change resHom U lS * resHom U yS = resHom U yS * resHom U lS
    rw [← map_mul, ← map_mul, hcomm]
  have hD'J' : autSub D U ≤ Subgroup.normalizer (autSub J U : Set (MulAut ↥U)) := by
    intro d' hd'
    rw [Subgroup.mem_set_normalizer_iff]
    intro j'
    constructor
    · intro hj'
      obtain ⟨jS, hjSJ, hjSrfl⟩ := mem_autSub.mp hj'
      obtain ⟨dQ, hdSD, hdSrfl⟩ := mem_autSub.mp hd'
      have hker : ((dQ * jS * dQ⁻¹ : stabSub U) : MulAut W) ∈ J := by
        have h := (Subgroup.mem_set_normalizer_iff.mp (hDJ hdSD)) (jS : MulAut W)
        simpa using h.mp hjSJ
      have hres : resHom U (dQ * jS * dQ⁻¹) = d' * j' * d'⁻¹ := by
        rw [map_mul, map_mul, map_inv, hdSrfl, hjSrfl]
      rw [← hres]
      exact mem_autSub.mpr ⟨dQ * jS * dQ⁻¹, hker, rfl⟩
    · intro hconj
      obtain ⟨g, hgJ, hgres⟩ := mem_autSub.mp hconj
      obtain ⟨dQ, hdSD, hdSrfl⟩ := mem_autSub.mp hd'
      have hkinv : ((dQ⁻¹ * g * dQ : stabSub U) : MulAut W) ∈ J := by
        have hdSinvD : ((dQ⁻¹ : stabSub U) : MulAut W) ∈ D := D.inv_mem hdSD
        have h := (Subgroup.mem_set_normalizer_iff.mp (hDJ hdSinvD)) (g : MulAut W)
        simpa using h.mp hgJ
      have hres2 : resHom U (dQ⁻¹ * g * dQ) = j' := by
        rw [map_mul, map_mul, map_inv, hdSrfl, hgres]
        group
      rw [← hres2]
      exact mem_autSub.mpr ⟨dQ⁻¹ * g * dQ, hkinv, rfl⟩
  obtain ⟨Y, hYsq, hJeq⟩ := hJgen
  have hYle : Y ⊆ stabSub U :=
    fun g hg => hJU (hJeq.symm ▸ Subgroup.subset_closure hg)
  have hJ'gen : ∃ Y' : Set (MulAut ↥U),
      (∀ g ∈ Y', g ^ 2 = 1) ∧ autSub J U = closure Y' := by
    let Y' : Set (MulAut ↥U) := (resHom U) '' {g : stabSub U | (g : MulAut W) ∈ Y}
    refine ⟨Y', ?_, ?_⟩
    · rintro φ ⟨g, hgY, rfl⟩
      have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hYsq (g : MulAut W) hgY)
      rw [← map_pow, hg2, map_one]
    · change (J.subgroupOf (stabSub U)).map (resHom U) = closure Y'
      rw [hJeq, s16h_subgroupOf_closure hYle, MonoidHom.map_closure]
      rfl
  have hJ'2 : ¬ IsPGroup 2 (autSub J U) := by
    intro hJ'pg
    have hψ_inj : Function.Injective ((resHom U).comp (Subgroup.inclusion hJU)) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      ext j
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_bot]
      constructor
      · intro hj
        have hjker : Subgroup.inclusion hJU j ∈ (resHom U).ker := MonoidHom.mem_ker.mpr hj
        rw [ker_resHom, Subgroup.mem_subgroupOf] at hjker
        have hcent : (j : MulAut W) ∈ centSub U := by simpa using hjker
        have : (j : MulAut W) ∈ J ⊓ centSub U := ⟨j.2, hcent⟩
        rw [hJc, Subgroup.mem_bot] at this
        exact Subtype.ext this
      · intro hj
        rw [hj]
        simp
    have hψ_range :
        MonoidHom.range ((resHom U).comp (Subgroup.inclusion hJU)) = autSub J U := by
      ext φ
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        exact mem_autSub.mpr ⟨Subgroup.inclusion hJU j, j.2, rfl⟩
      · intro hφ
        obtain ⟨g, hgJ, hgres⟩ := mem_autSub.mp hφ
        refine ⟨⟨(g : MulAut W), hgJ⟩, ?_⟩
        change resHom U (Subgroup.inclusion hJU ⟨(g : MulAut W), hgJ⟩) = φ
        rw [show Subgroup.inclusion hJU ⟨(g : MulAut W), hgJ⟩ = g from Subtype.ext rfl,
          hgres]
    have h' : IsPGroup 2 (MonoidHom.range ((resHom U).comp (Subgroup.inclusion hJU))) := by
      rwa [hψ_range]
    exact hJ2 (h'.of_equiv (MonoidHom.ofInjective hψ_inj).symm)
  obtain ⟨y', hy'J, hy'3, hy'not⟩ :=
    s16h_exists_order_three_of_torus hUcard hl' hfpf hD'ea hD'27 hD'l hJ'l hD'J' hJ'gen hJ'2
  obtain ⟨yS, hySJ, hySrfl⟩ := mem_autSub.mp hy'J
  let y : MulAut W := (yS : MulAut W)
  have hy3 : y ^ 3 = 1 := by
    have h1 : yS ^ 3 ∈ (resHom U).ker := by
      rw [MonoidHom.mem_ker, map_pow, hySrfl, hy'3]
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
    have hcent : y ^ 3 ∈ centSub U := by simpa [y] using h1
    have hJmem : y ^ 3 ∈ J := by simpa [y] using J.pow_mem hySJ 3
    have : y ^ 3 ∈ J ⊓ centSub U := ⟨hJmem, hcent⟩
    rw [hJc, Subgroup.mem_bot] at this
    exact this
  refine ⟨y, ?_, hy3, ?_⟩
  · simpa [y] using hySJ
  · intro hyL
    apply hy'not
    have hyL' : y ∈ Subgroup.zpowers l := by
      rw [hLgen]
      exact hyL
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyL'
    have hylS : yS = lS ^ k := by
      apply Subtype.ext
      simpa [lS, y] using hk.symm
    have himg : resHom U yS = l' ^ k := by
      simpa [l', hylS] using map_zpow (resHom U) lS k
    rw [hySrfl] at himg
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, himg.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
