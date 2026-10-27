module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DL
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem mem_autI_oTwoUpper_ch615 (c : Cx615B G T M L V H n)
    {b : MulAut (IntMod (Cx615.UH T H) c.hU)} (hb : b ∈ autI c.hU (thompsonJ H))
    (hb3 : b ^ 3 = 1) : b ∈ autI c.hU (oTwoUpper H) := by
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨x, hx, e, hxe⟩ := c.exists_lift_ch615 hb
  have hxK : c.cvH x ∈ autI c.hU (oTwoUpper H) := by
    rw [autI_eq_map_convHom c.hU hHN (oTwoUpper_le H)]
    exact ⟨x, hx, rfl⟩
  have hmod : 4 ^ e % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h4 : b ^ (4 ^ e) = b := by
    rw [← Nat.div_add_mod (4 ^ e) 3, hmod, pow_add, pow_mul, hb3, one_pow, one_mul, pow_one]
  have h44 : 2 ^ e * 2 ^ e = 4 ^ e := by rw [← mul_pow]; norm_num
  have h22 : (b ^ 2 ^ e) ^ 2 ^ e = b := by rw [← pow_mul, h44, h4]
  rw [← h22, ← hxe]
  exact Subgroup.pow_mem _ hxK _

theorem coords_mod_ch615 (c : Cx615B G T M L V H n) :
    (∃ ψ₁ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU), Function.Injective ψ₁ ∧
        ψ₁.range = autI c.hU (thompsonJ H) ∧
        Nat.card (commV (Subgroup.zpowers (ψ₁ g3_615))) ≤ 4) ∨
     (∃ ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU), Function.Injective ψ ∧
        ψ.range = autI c.hU (thompsonJ H) ∧ (∃ t : ↥H, (t : G) ∈ T ∧
        (∀ u : SL22, ∃ v : SL22, c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹ = ψ (1, v)) ∧
        (∀ v : SL22, ∃ u : SL22, ψ (1, v) = c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹)) ∧
        Nat.card (commV (Subgroup.zpowers (ψ (g3_615, 1)))) ≤ 4 ∧
        Nat.card (commV (Subgroup.zpowers (ψ (1, g3_615)))) ≤ 4) := by
  classical
  obtain ⟨-, I, hcard, hJeq, hcomm, hind, htrans, htype, -, -, -, -⟩ := c.e23
  have hnat := c.s3 I hcard hJeq htype
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hTH : T ≤ H := c.hH.1.1
  have hW : ∀ w : IntMod (Cx615.UH T H) c.hU, w ^ 2 = 1 := IntMod.sq_eq_one
  have hbound : ∀ L₁ ∈ I, ∀ σ ∈ L₁, σ ^ 3 = 1 →
      Nat.card (commV (Subgroup.zpowers σ)) ≤ 4 := by
    intro L₁ hL₁ σ hσ hσ3
    have hσJ : σ ∈ autI c.hU (thompsonJ H) := by
      rw [hJeq]
      exact (le_iSup₂_of_le L₁ hL₁ le_rfl : L₁ ≤ ⨆ K ∈ I, K) hσ
    have hσK : σ ∈ autI c.hU (twoResidual H) := by
      rw [twoResidual_eq_oTwoUpper']
      exact c.mem_autI_oTwoUpper_ch615 hσJ hσ3
    exact card_commV_le_ch615 hW (hnat L₁ hL₁) hσ hσ3 fun w hw x hx =>
      hw x ((Subgroup.zpowers_le.mpr hσK) hx)
  have hg3 : ∀ φ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU), φ g3_615 ^ 3 = 1 := fun φ => by
    rw [← map_pow, g3_615_pow_three, map_one]
  rcases hcard with h1 | h2'
  · obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
    have hBL : autI c.hU (thompsonJ H) = L₁ := by rw [hJeq]; simp
    obtain ⟨ψ₁, hψ₁, hr₁⟩ :=
      exists_hom_of_isL2Natural_ch615 (hnat L₁ (Finset.mem_singleton_self _))
    refine Or.inl ⟨ψ₁, hψ₁, hr₁.trans hBL.symm, ?_⟩
    exact hbound L₁ (Finset.mem_singleton_self _) _ (by rw [← hr₁]; exact ⟨g3_615, rfl⟩)
      (hg3 ψ₁)
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2'
    have hm₁ : L₁ ∈ ({L₁, L₂} : Finset _) := Finset.mem_insert_self _ _
    have hm₂ : L₂ ∈ ({L₁, L₂} : Finset _) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hBL : autI c.hU (thompsonJ H) = L₁ ⊔ L₂ := by
      rw [hJeq, Finset.iSup_insert, Finset.iSup_singleton]
    have hdisj : L₁ ⊓ L₂ = ⊥ := by
      refine le_bot_iff.mp (le_trans (inf_le_inf_left _ ?_) (hind L₁ hm₁).le)
      exact le_iSup₂_of_le (f := fun L' _ => ⨆ (_ : L' ≠ L₁), L') L₂ hm₂
        (le_iSup_of_le hne.symm le_rfl)
    obtain ⟨ψ₁, hψ₁, hr₁⟩ := exists_hom_of_isL2Natural_ch615 (hnat L₁ hm₁)
    obtain ⟨ψ₂, hψ₂, hr₂⟩ := exists_hom_of_isL2Natural_ch615 (hnat L₂ hm₂)
    obtain ⟨ψ, hψ, hr, hψl, hψr⟩ := exists_hom_two_ch615 hψ₁ hψ₂ hr₁ hr₂
      (hcomm L₁ hm₁ L₂ hm₂ hne) hdisj
    obtain ⟨tc, htc, htL⟩ := htrans L₁ hm₁ L₂ hm₂
    rw [autI_eq_map_convHom c.hU hHN hTH] at htc
    obtain ⟨t, ht, htt⟩ := htc
    have htt' : c.cvH t = tc := htt
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    refine Or.inr ⟨ψ, hψ, hr.trans hBL.symm, ⟨t, ht, fun u => ?_, fun v => ?_⟩, ?_, ?_⟩
    · have hmem : tc * ψ (u, 1) * tc⁻¹ ∈ L₂ := by
        rw [← htL, B1.mem_conjAut, hψl, ← hr₁]
        exact ⟨u, by group⟩
      rw [← hr₂] at hmem
      obtain ⟨v, hv⟩ := hmem
      exact ⟨v, by rw [htt', hψr, hv]⟩
    · have hmem : ψ (1, v) ∈ B1.conjAut tc L₁ := by
        rw [htL, hψr, ← hr₂]; exact ⟨v, rfl⟩
      rw [B1.mem_conjAut, ← hr₁] at hmem
      obtain ⟨u, hu⟩ := hmem
      refine ⟨u, ?_⟩
      rw [htt', hψl, hu]
      group
    · rw [hψl]
      exact hbound L₁ hm₁ _ (by rw [← hr₁]; exact ⟨g3_615, rfl⟩) (hg3 ψ₁)
    · rw [hψr]
      exact hbound L₂ hm₂ _ (by rw [← hr₂]; exact ⟨g3_615, rfl⟩) (hg3 ψ₂)

theorem one_coords_ch615 (c : Cx615B G T M L V H n)
    {ψ₁ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ₁ : Function.Injective ψ₁)
    (hr₁ : ψ₁.range = autI c.hU (thompsonJ H)) :
    ∃ r : SL22, r ≠ 1 ∧ r ^ 2 = 1 ∧ ψ₁ r ∈ autI c.hU (thompsonJ T) ∧
      ∀ β ∈ autI c.hU (thompsonJ T), β = 1 ∨ β = ψ₁ r := by
  classical
  obtain ⟨-, -, hsyl, -, -⟩ := c.coords_ch615
  set S := autI c.hU (thompsonJ T) with hS
  rw [← hr₁] at hsyl
  have hBcard : Nat.card ψ₁.range = 6 := by
    rw [← card_sl22]
    exact Nat.card_congr (MonoidHom.ofInjective hψ₁).symm.toEquiv
  have hScard : Nat.card S = 2 := by
    obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
    have hmul : S.relIndex ψ₁.range * Nat.card S = 6 := by
      have h1 := Subgroup.relIndex_mul_card S ψ₁.range
      rwa [inf_eq_left.mpr hsyl.1, hBcard] at h1
    rw [hk] at hmul ⊢
    have hodd : ¬ 2 ∣ S.relIndex ψ₁.range := hsyl.2.2
    have hk2 : k < 2 := by
      by_contra hk2
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h6 : 2 ^ k ∣ 6 := Dvd.intro_left _ hmul
      have := h4.trans h6
      omega
    interval_cases k
    · exfalso
      apply hodd
      rw [pow_zero, mul_one] at hmul
      rw [hmul]
      norm_num
    · rfl
  obtain ⟨p, hp1, hpu⟩ := (Nat.card_eq_two_iff' (1 : ↥S)).mp hScard
  have hpS : (p : MulAut _) ∈ ψ₁.range := hsyl.1 p.2
  obtain ⟨r, hr⟩ := hpS
  have hp1' : (p : MulAut (IntMod (Cx615.UH T H) c.hU)) ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hr1 : r ≠ 1 := fun h => hp1' (by rw [← hr, h, map_one])
  have hall : ∀ β ∈ S, β = 1 ∨ β = ψ₁ r := by
    intro β hβ
    by_cases hβ1 : (⟨β, hβ⟩ : ↥S) = 1
    · exact Or.inl (congrArg Subtype.val hβ1)
    · right
      rw [hr]
      exact congrArg Subtype.val (hpu ⟨β, hβ⟩ hβ1)
  have hr2 : r ^ 2 = 1 := by
    have hp2 : (p : MulAut _) ^ 2 ∈ S := S.pow_mem p.2 2
    rcases hall _ hp2 with h | h
    · rw [← hr, ← map_pow] at h
      exact hψ₁ (h.trans (map_one ψ₁).symm)
    · exfalso
      rw [← hr, ← map_pow] at h
      have h' := hψ₁ h
      apply hr1
      rw [pow_two] at h'
      exact mul_left_cancel (h'.trans (mul_one r).symm)
  exact ⟨r, hr1, hr2, hr ▸ p.2, hall⟩

end Cx615B


namespace Cx615B

theorem cvH_oTwoUpper_one_ch615 (c : Cx615B G T M L V H n)
    {ψ₁ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ₁ : Function.Injective ψ₁)
    (hr₁ : ψ₁.range = autI c.hU (thompsonJ H)) {k : G} (hkH : k ∈ H) (hkK : k ∈ oTwoUpper H) :
    ∃ u : SL22, u ^ 3 = 1 ∧ c.cvH ⟨k, hkH⟩ = ψ₁ u := by
  obtain ⟨hOJ, -⟩ := c.coords_ch615
  set A := Subgroup.zpowers g3_615
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, g3_615_pow_three,
      one_zpow]
  have hAof : ∀ u : SL22, u ^ 3 = 1 → u ∈ A := by
    intro u hu
    rcases eq_of_pow_three_sl22 u g3_615 hu g3_615_pow_three g3_615_ne_one with h | h | h
    · rw [h]; exact A.one_mem
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact A.inv_mem (Subgroup.mem_zpowers _)
  have hX := c.cvH_mem_of_odd_ch615 hOJ (X := A.map ψ₁) (fun x hx hodd => by
    rw [← hr₁] at hx
    obtain ⟨s, rfl⟩ := hx
    have hs : Odd (orderOf s) := by rwa [orderOf_injective ψ₁ hψ₁] at hodd
    have hs3 : s ^ 3 = 1 := by
      rcases sq_or_cube_sl22 s with h2 | h3
      · have hd := orderOf_dvd_of_pow_eq_one h2
        rw [orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hs) hd),
          one_pow]
      · exact h3
    exact ⟨s, hAof s hs3, rfl⟩) ⟨k, hkH⟩ (Subgroup.mem_subgroupOf.mpr hkK)
  obtain ⟨u, hu, huk⟩ := hX
  exact ⟨u, hA3 u hu, huk.symm⟩

theorem existsUnique_mod_ch615 (c : Cx615B G T M L V H n) :
    ∃! w : IntMod (Cx615.UH T H) c.hU, w ∈ commV (autI c.hU (oTwoUpper H)) ∧
      w ∈ fixV (autI c.hU (thompsonJ T)) ∧ w ≠ 1 ∧
      ∀ τ ∈ autI c.hU (oTwoUpper H), τ w = w →
        ∀ w' ∈ commV (autI c.hU (oTwoUpper H)), τ w' = w' := by
  have hW : ∀ w : IntMod (Cx615.UH T H) c.hU, w ^ 2 = 1 := IntMod.sq_eq_one
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hJH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans c.hH.1.1
  rcases c.coords_mod_ch615 with ⟨ψ₁, hψ₁, hr₁, hcard⟩ |
    ⟨ψ, hψ, hr, ⟨t, htT, ht₁, -⟩, hcard₁, hcard₂⟩
  · obtain ⟨r, hr1, hr2, hrB, hB⟩ := c.one_coords_ch615 hψ₁ hr₁
    refine existsUnique_one_ch615 hW hψ₁ (fun τ hτ => ?_) ?_ hr1 hr2 hB hrB hcard
    · rw [autI_eq_map_convHom c.hU hHN hKH] at hτ
      obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hτ
      exact c.cvH_oTwoUpper_one_ch615 hψ₁ hr₁ hkH (Subgroup.mem_subgroupOf.mp hk)
    · exact c.mem_autI_oTwoUpper_ch615 (by rw [← hr₁]; exact ⟨_, rfl⟩)
        (by rw [← map_pow, g3_615_pow_three, map_one])
  · obtain ⟨a, b, r₁, r₂, haJ, hbJ, hr₁1, hr₁2, hr₂1, hr₂2, ha, hb, hJ⟩ :=
      c.two_coords_ch615 hψ hr htT ht₁
    have hg₁ : ((g3_615, (1 : SL22)) : SL22 × SL22) ^ 3 = 1 :=
      Prod.ext g3_615_pow_three (one_pow 3)
    have hg₂ : (((1 : SL22), g3_615) : SL22 × SL22) ^ 3 = 1 :=
      Prod.ext (one_pow 3) g3_615_pow_three
    refine existsUnique_two_ch615 hW hψ (fun τ hτ => ?_) ?_ ?_ hr₁1 hr₁2 hr₂1 hr₂2
      (fun β hβ => ?_) ?_ ?_ hcard₁ hcard₂
    · rw [autI_eq_map_convHom c.hU hHN hKH] at hτ
      obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hτ
      exact c.cvH_oTwoUpper_ch615 hψ hr hkH (Subgroup.mem_subgroupOf.mp hk)
    · exact c.mem_autI_oTwoUpper_ch615 (by rw [← hr]; exact ⟨_, rfl⟩)
        (by rw [← map_pow, hg₁, map_one])
    · exact c.mem_autI_oTwoUpper_ch615 (by rw [← hr]; exact ⟨_, rfl⟩)
        (by rw [← map_pow, hg₂, map_one])
    · rw [autI_eq_map_convHom c.hU hHN hJH] at hβ
      obtain ⟨j, hj, rfl⟩ := hβ
      exact hJ j hj
    · rw [← ha, autI_eq_map_convHom c.hU hHN hJH]
      exact ⟨a, Subgroup.mem_subgroupOf.mpr haJ, rfl⟩
    · rw [← hb, autI_eq_map_convHom c.hU hHN hJH]
      exact ⟨b, Subgroup.mem_subgroupOf.mpr hbJ, rfl⟩

end Cx615B

end CFSG.Quasithin.H13
