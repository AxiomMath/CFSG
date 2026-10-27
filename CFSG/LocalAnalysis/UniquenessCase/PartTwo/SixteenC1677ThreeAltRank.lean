module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAltCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAltCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_four_le_pRank_of_cover {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) {n : ℕ} (hn9 : 9 ≤ n)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hcov : ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧ IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V))
    (hK3 : 3 ∣ Nat.card ↥(kBar D.M V₀ V hV L)) :
    4 ≤ CFSG.Open.pRank 3 D.M := by
  obtain ⟨Y, hYM, hYN, hYbar, hY2⟩ := hcov
  have hMs : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMn : D.M ≤ Subgroup.normalizer (V : Set G) :=
    hMs.trans (stabTil_le_normalizer V₀ V)
  have hYs : Y ≤ stabTil V₀ V := hYM.trans hMs
  have hYnorm : D.M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN
  let φ0 : ↥Y →* ↥(barSub V₀ V hV Y) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYs))
      (barSub V₀ V hV Y) (fun g => actTil_mem_barSub V₀ V hV g.2 (hYs g.2))
  have hφ0 : Function.Surjective φ0 := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hker0 : φ0.ker = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff hV hMn]
    have hgY : (g : G) ∈ Y := g.2
    constructor
    · intro h1
      exact ⟨hgY, hYM hgY, hYs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  obtain ⟨e⟩ := hA
  let φ : ↥Y →* alternatingGroup (Fin n) :=
    (e.toMonoidHom.comp (MulEquiv.subgroupCongr hYbar).toMonoidHom).comp φ0
  have hφ : Function.Surjective φ :=
    e.surjective.comp ((MulEquiv.subgroupCongr hYbar).surjective.comp hφ0)
  have hker : φ.ker = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y :=
    (MonoidHom.ker_comp_of_injective φ0
      (e.toMonoidHom.comp (MulEquiv.subgroupCongr hYbar).toMonoidHom)
      (e.injective.comp (MulEquiv.subgroupCongr hYbar).injective)).trans hker0
  obtain ⟨z, hz3⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥(kBar D.M V₀ V hV L)) hK3
  have hKM : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV := inf_le_left
  have hKc : kBar D.M V₀ V hV L ≤
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := inf_le_right
  have hzM : (z : MulAut (Vtil V₀ V hV)) ∈ Mbar D.M V₀ V hV := hKM z.2
  have hzc : (z : MulAut (Vtil V₀ V hV)) ∈
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := hKc z.2
  obtain ⟨g, hgM, hgz⟩ := (mem_barSub V₀ V hV D.M (z : MulAut (Vtil V₀ V hV))).1 hzM
  have hz3' : orderOf (z : MulAut (Vtil V₀ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe]; exact hz3
  have hzorder : orderOf (actTil V₀ V hV g) = 3 := by rw [hgz]; exact hz3'
  have h3dvd' : 3 ∣ orderOf g := hzorder ▸ orderOf_map_dvd (actTil V₀ V hV) g
  have h3dvd : 3 ∣ orderOf (g : G) := by
    simpa only [Subgroup.orderOf_coe g] using h3dvd'
  let k : ℕ := orderOf (g : G) / 3
  let y : G := (g : G) ^ k
  have hy3 : orderOf y = 3 := by
    dsimp only [y, k]
    exact orderOf_pow_orderOf_div (orderOf_pos (g : G)).ne' h3dvd
  have hyM : y ∈ D.M := by
    dsimp only [y]
    exact D.M.pow_mem hgM k
  have hys : y ∈ stabTil V₀ V := hMs hyM
  have hy_eq : (⟨y, hys⟩ : ↥(stabTil V₀ V)) = g ^ k := by
    apply Subtype.ext
    rfl
  have hacty : actTil V₀ V hV ⟨y, hys⟩ = (z : MulAut (Vtil V₀ V hV)) ^ k := by
    rw [hy_eq, map_pow, hgz]
  have hzy_mem : actTil V₀ V hV ⟨y, hys⟩ ∈ kBar D.M V₀ V hV L := by
    rw [hacty]
    exact (kBar D.M V₀ V hV L).pow_mem z.2 k
  have hzy_cen : actTil V₀ V hV ⟨y, hys⟩ ∈
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := hKc hzy_mem
  have hcenter_bot : Subgroup.center ↥(lBar V₀ V hV L) = ⊥ := by
    rw [eq_bot_iff]
    intro zbar hzbar
    have hez : e zbar ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzbar w']
    rw [alternatingGroup.center_eq_bot
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
      Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hez
    exact Subgroup.mem_bot.2 hez
  have hyY : y ∉ Y := by
    intro hyYmem
    have hmem_lbar : actTil V₀ V hV ⟨y, hys⟩ ∈ lBar V₀ V hV L := by
      rw [← hYbar]
      exact actTil_mem_barSub V₀ V hV hyYmem hys
    have hcen : (⟨actTil V₀ V hV ⟨y, hys⟩, hmem_lbar⟩ : ↥(lBar V₀ V hV L)) ∈
        Subgroup.center ↥(lBar V₀ V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.1 hzy_cen (w : MulAut (Vtil V₀ V hV)) w.2)
    rw [hcenter_bot, Subgroup.mem_bot] at hcen
    have hact_one : actTil V₀ V hV ⟨y, hys⟩ = 1 := by
      simpa using congrArg Subtype.val hcen
    have hyC : y ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hMn]
      exact ⟨hyM, hys, hact_one⟩
    have hyZ : y ∈ Y ⊓ F11.CTilde D.M V₀ V := ⟨hyYmem, hyC⟩
    obtain ⟨j, hj⟩ := hY2.exists_orderOf_eq_pow (⟨y, hyZ⟩ : ↥(Y ⊓ F11.CTilde D.M V₀ V))
    have h1 : orderOf (⟨y, hyZ⟩ : ↥(Y ⊓ F11.CTilde D.M V₀ V)) = 3 := by
      rw [Subgroup.orderOf_mk]; exact hy3
    have h32 : ¬ (3 : ℕ) ∣ 2 ^ j := by
      intro h
      exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    exact h32 (h1.symm.trans hj ▸ dvd_rfl)
  have hcomm : ∀ u ∈ Y, y * u * y⁻¹ * u⁻¹ ∈ Y ⊓ F11.CTilde D.M V₀ V := by
    intro u hu
    have huM : u ∈ D.M := hYM hu
    have hus : u ∈ stabTil V₀ V := hYs hu
    have hconj : y * u * y⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.1 (hYnorm hyM) u).1 hu
    have hcommY : y * u * y⁻¹ * u⁻¹ ∈ Y := Y.mul_mem hconj (Y.inv_mem hu)
    have hcommM : y * u * y⁻¹ * u⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hyM huM) (D.M.inv_mem hyM))
        (D.M.inv_mem huM)
    have hcommS : y * u * y⁻¹ * u⁻¹ ∈ stabTil V₀ V := hMs hcommM
    have hmem_lbar_u : actTil V₀ V hV ⟨u, hus⟩ ∈ lBar V₀ V hV L := by
      rw [← hYbar]
      exact actTil_mem_barSub V₀ V hV hu hus
    have hcomm_zy_u : actTil V₀ V hV ⟨y, hys⟩ * actTil V₀ V hV ⟨u, hus⟩ =
        actTil V₀ V hV ⟨u, hus⟩ * actTil V₀ V hV ⟨y, hys⟩ :=
      (Subgroup.mem_centralizer_iff.1 hzy_cen
        (actTil V₀ V hV ⟨u, hus⟩) hmem_lbar_u).symm
    have hact_comm : actTil V₀ V hV ⟨y * u * y⁻¹ * u⁻¹, hcommS⟩ = 1 := by
      have h1 : (⟨y * u * y⁻¹ * u⁻¹, hcommS⟩ : ↥(stabTil V₀ V)) =
          ⟨y, hys⟩ * ⟨u, hus⟩ * ⟨y, hys⟩⁻¹ * ⟨u, hus⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [h1]
      simp only [map_mul, map_inv]
      rw [hcomm_zy_u]
      group
    have hcommC : y * u * y⁻¹ * u⁻¹ ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hMn]
      exact ⟨hcommM, hcommS, hact_comm⟩
    exact ⟨hcommY, hcommC⟩
  exact s168e3_four_le_pRank_of_alt_cover hn9 hYM hYN inf_le_left φ hφ hker hY2
    hyM hy3 hyY hcomm

theorem s168e3_false_of_alt_three_centralizer {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn9 : 9 ≤ n)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hK3 : 3 ∣ Nat.card ↥(kBar D.M V₀ V hV L)) : False := by
  have h4 := s168e3_four_le_pRank_of_cover c hn9 hA
    (s168e3_cover_alt c hSchur hs (by omega) hA) hK3
  have h3 : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three (by norm_num)
      D.M D.maxLocal.1
  have h3' := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
