module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentA
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Ctx

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

noncomputable abbrev Cx615B.cvH (c : Cx615B G T M L V H n) :
    ↥H →* MulAut (IntMod (Cx615.UH T H) c.hU) :=
  convHom c.hU H (le_normalizer_conjClosure _ _)

omit [Finite G] in
theorem mem_oTwoUpper_subgroupOf_ch615 {H : Subgroup G} {x : ↥H} (hx : Odd (orderOf x)) :
    x ∈ (oTwoUpper H).subgroupOf H := by
  rw [Subgroup.mem_subgroupOf]
  exact mem_oTwoUpper_of_odd x.2 (by rwa [Subgroup.orderOf_coe])

theorem Cx615B.cvH_mem_of_odd_ch615 (c : Cx615B G T M L V H n)
    (hOJ : oTwoUpper H ≤ thompsonJ H) {X : Subgroup (MulAut (IntMod (Cx615.UH T H) c.hU))}
    (hX : ∀ b ∈ autI c.hU (thompsonJ H), Odd (orderOf b) → b ∈ X) :
    ∀ k ∈ (oTwoUpper H).subgroupOf H, c.cvH k ∈ X := by
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hB : autI c.hU (thompsonJ H) = ((thompsonJ H).subgroupOf H).map c.cvH :=
    autI_eq_map_convHom c.hU hHN hJH
  rintro ⟨k, hkH⟩ hk
  rw [Subgroup.mem_subgroupOf] at hk
  refine Subgroup.closure_induction (p := fun g _ => ∀ hg : g ∈ H, c.cvH ⟨g, hg⟩ ∈ X)
    ?_ ?_ ?_ ?_ hk hkH
  · intro g hg hgH
    refine hX _ ?_ ?_
    · rw [hB]
      exact ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr (hOJ (mem_oTwoUpper_of_odd hg.1 hg.2)), rfl⟩
    · refine Odd.of_dvd_nat hg.2 ((orderOf_map_dvd c.cvH _).trans ?_)
      rw [Subgroup.orderOf_mk]
  · intro h1
    have e : (⟨1, h1⟩ : ↥H) = 1 := rfl
    rw [e, map_one]
    exact X.one_mem
  · intro a b ha hb iha ihb hab
    have e : (⟨a * b, hab⟩ : ↥H) =
        ⟨a, oTwoUpper_le H ha⟩ * ⟨b, oTwoUpper_le H hb⟩ := rfl
    rw [e, map_mul]
    exact X.mul_mem (iha _) (ihb _)
  · intro a ha iha hai
    have e : (⟨a⁻¹, hai⟩ : ↥H) = (⟨a, oTwoUpper_le H ha⟩ : ↥H)⁻¹ := rfl
    rw [e, map_inv]
    exact X.inv_mem (iha _)

theorem Cx615B.exists_lift_ch615 (c : Cx615B G T M L V H n)
    {b : MulAut (IntMod (Cx615.UH T H) c.hU)} (hb : b ∈ autI c.hU (thompsonJ H)) :
    ∃ x ∈ (oTwoUpper H).subgroupOf H, ∃ e : ℕ, c.cvH x = b ^ 2 ^ e := by
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hB : autI c.hU (thompsonJ H) = ((thompsonJ H).subgroupOf H).map c.cvH :=
    autI_eq_map_convHom c.hU hHN (thompsonJ_le_self H)
  rw [hB] at hb
  obtain ⟨x₀, -, hx₀⟩ := hb
  obtain ⟨e, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  refine ⟨x₀ ^ 2 ^ e, mem_oTwoUpper_subgroupOf_ch615 ?_, e, by rw [map_pow, hx₀]⟩
  rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hm, Nat.gcd_mul_right_left,
    Nat.mul_div_cancel_left _ (pow_pos two_pos e)]
  exact hr

theorem g3_pow_two_pow_ch615 (e : ℕ) : g3_615 ^ 2 ^ e ≠ 1 ∧ (g3_615 ^ 2 ^ e) ^ 3 = 1 := by
  refine ⟨fun h1 => ?_, by rw [← pow_mul, mul_comm, pow_mul, g3_615_pow_three, one_pow]⟩
  have h3 : orderOf g3_615 = 3 := orderOf_eq_prime g3_615_pow_three g3_615_ne_one
  have hd : 3 ∣ 2 ^ e := h3 ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
  omega

theorem Cx615B.blocks_ch615 (c : Cx615B G T M L V H n) :
    Group.IsSolvable ↥(autI c.hU (thompsonJ H)) ∧
    ((∃ x ∈ (oTwoUpper H).subgroupOf H, ∀ k ∈ (oTwoUpper H).subgroupOf H,
        c.cvH k ∈ Subgroup.zpowers (c.cvH x)) ∨
     (∃ x ∈ (oTwoUpper H).subgroupOf H, ∃ y ∈ (oTwoUpper H).subgroupOf H,
       ∃ a ∈ (thompsonJ T).subgroupOf H, ∃ s ∈ T.subgroupOf H,
        c.cvH x ≠ 1 ∧ c.cvH x ^ 3 = 1 ∧ c.cvH (a * x * a⁻¹ * x) = 1 ∧
        c.cvH (y⁻¹ * (a * y * a⁻¹)) = 1 ∧ c.cvH (y⁻¹ * (s * x * s⁻¹)) = 1 ∧
        c.cvH (x⁻¹ * (s * y * s⁻¹)) = 1 ∧
        ∀ k ∈ (oTwoUpper H).subgroupOf H, c.cvH k ∈ Subgroup.closure {c.cvH x, c.cvH y})) := by
  classical
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, -⟩ := c.e23
  have hnat := c.s3 I hcard hJeq htype
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hTH : T ≤ H := c.hH.1.1
  have hOJ : oTwoUpper H ≤ thompsonJ H := by rw [← twoResidual_eq_oTwoUpper']; exact hKJ
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hB : autI c.hU (thompsonJ H) = ((thompsonJ H).subgroupOf H).map c.cvH :=
    autI_eq_map_convHom c.hU hHN hJH
  rcases hcard with h1 | h2'
  ·
    obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
    have hBL : autI c.hU (thompsonJ H) = L₁ := by rw [hJeq]; simp
    obtain ⟨ψ₁, hψ₁, hr₁⟩ :=
      exists_hom_of_isL2Natural_ch615 (hnat L₁ (Finset.mem_singleton_self _))
    refine ⟨?_, Or.inl ?_⟩
    · rw [hBL, ← hr₁]
      have := isSolvable_sl22
      exact Group.isSolvable_of_surjective ψ₁.rangeRestrict_surjective
    · have hg : ψ₁ g3_615 ∈ autI c.hU (thompsonJ H) := by rw [hBL, ← hr₁]; exact ⟨_, rfl⟩
      obtain ⟨x, hx, e, hxe⟩ := c.exists_lift_ch615 hg
      obtain ⟨hg1, hg3⟩ := g3_pow_two_pow_ch615 e
      refine ⟨x, hx, fun k hk => ?_⟩
      rw [hxe, ← map_pow]
      refine c.cvH_mem_of_odd_ch615 hOJ (fun b hb hodd => ?_) k hk
      rw [hBL, ← hr₁] at hb
      exact one_data_ch615 hψ₁ hg1 hg3 b hb hodd
  ·
    obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2'
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
    have hBψ : autI c.hU (thompsonJ H) = ψ.range := by rw [hBL, hr]
    refine ⟨?_, Or.inr ?_⟩
    · rw [hBψ]
      have := isSolvable_sl22
      exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
    obtain ⟨tc, htc, htL⟩ := htrans L₁ hm₁ L₂ hm₂
    rw [autI_eq_map_convHom c.hU hHN hTH] at htc
    obtain ⟨t, ht, htt⟩ := htc
    have htt' : c.cvH t = tc := htt
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    have htB : ∀ b ∈ ψ.range, tc * b * tc⁻¹ ∈ ψ.range := by
      intro b hb
      rw [← hBψ, hB] at hb ⊢
      obtain ⟨j, hj, rfl⟩ := hb
      refine ⟨t * j * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv, htt']⟩
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hj ⊢
      exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_thompsonJ H)) (hTH ht)) _).mp hj
    have ht₁ : ∀ u : SL22, ∃ v : SL22, tc * ψ (u, 1) * tc⁻¹ = ψ (1, v) := by
      intro u
      have hmem : tc * ψ (u, 1) * tc⁻¹ ∈ L₂ := by
        rw [← htL, B1.mem_conjAut, hψl, ← hr₁]
        exact ⟨u, by group⟩
      rw [← hr₂] at hmem
      obtain ⟨v, hv⟩ := hmem
      exact ⟨v, by rw [hψr, hv]⟩
    have ht₂ : ∀ v : SL22, ∃ u : SL22, ψ (1, v) = tc * ψ (u, 1) * tc⁻¹ := by
      intro v
      have hmem : ψ (1, v) ∈ B1.conjAut tc L₁ := by
        rw [htL, hψr, ← hr₂]; exact ⟨v, rfl⟩
      rw [B1.mem_conjAut, ← hr₁] at hmem
      obtain ⟨u, hu⟩ := hmem
      refine ⟨u, ?_⟩
      rw [hψl, hu]
      group
    obtain ⟨-, hsyl, -, -⟩ := h2 fun L hL => ⟨1, hnat L hL⟩
    rw [hBψ] at hsyl
    have hg : ψ (g3_615, 1) ∈ autI c.hU (thompsonJ H) := by rw [hBψ]; exact ⟨_, rfl⟩
    obtain ⟨x, hx, e, hxe⟩ := c.exists_lift_ch615 hg
    obtain ⟨hg1, hg3⟩ := g3_pow_two_pow_ch615 e
    have hxe' : c.cvH x = ψ (g3_615 ^ 2 ^ e, 1) := by
      rw [hxe, ← map_pow, Prod.pow_mk, one_pow]
    obtain ⟨ac, hac, hax, hay, hty, hodd⟩ := two_data_ch615 hψ hsyl htB ht₁ ht₂ hg1 hg3
    rw [autI_eq_map_convHom c.hU hHN ((thompsonJ_le_self T).trans hTH)] at hac
    obtain ⟨a, ha, haa⟩ := hac
    have haa' : c.cvH a = ac := haa
    rw [SetLike.mem_coe] at ha
    rw [← hxe', ← haa'] at hax
    rw [← hxe', ← htt', ← haa'] at hay
    rw [← hxe', ← htt'] at hty hodd
    have hyK : t * x * t⁻¹ ∈ (oTwoUpper H).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH ht)) _).mp hx
    have hy : c.cvH (t * x * t⁻¹) = c.cvH t * c.cvH x * (c.cvH t)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hx1 : c.cvH x ≠ 1 := by
      rw [hxe']
      exact fun h => hg1 (by
        have := hψ (h.trans (map_one ψ).symm); simpa using congrArg Prod.fst this)
    have hx3 : c.cvH x ^ 3 = 1 := by
      rw [hxe', ← map_pow, Prod.pow_mk, hg3, one_pow]; exact map_one ψ
    have hKcl : ∀ k ∈ (oTwoUpper H).subgroupOf H,
        c.cvH k ∈ Subgroup.closure {c.cvH x, c.cvH (t * x * t⁻¹)} := by
      rw [hy]
      refine c.cvH_mem_of_odd_ch615 hOJ fun b hb hb2 => ?_
      rw [hBψ] at hb
      exact hodd b hb hb2
    have hTa : a ∈ T.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf] at ha ⊢; exact thompsonJ_le_self T ha
    have ht' : t ∈ T.subgroupOf H := Subgroup.mem_subgroupOf.mpr ht
    have R1 : c.cvH (a * x * a⁻¹ * x) = 1 := by
      have e : c.cvH (a * x * a⁻¹ * x) = (c.cvH a * c.cvH x * (c.cvH a)⁻¹) * c.cvH x := by
        simp only [map_mul, map_inv]
      rw [e, hax, inv_mul_cancel]
    rcases hty with hty | hty
    · refine ⟨x, hx, t * x * t⁻¹, hyK, a, ha, t, ht', hx1, hx3, R1, ?_, ?_, ?_, hKcl⟩
      · have e : c.cvH ((t * x * t⁻¹)⁻¹ * (a * (t * x * t⁻¹) * a⁻¹)) =
            (c.cvH t * c.cvH x * (c.cvH t)⁻¹)⁻¹ *
              (c.cvH a * (c.cvH t * c.cvH x * (c.cvH t)⁻¹) * (c.cvH a)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [e, hay, inv_mul_cancel]
      · rw [inv_mul_cancel, map_one]
      · have e : c.cvH (x⁻¹ * (t * (t * x * t⁻¹) * t⁻¹)) =
            (c.cvH x)⁻¹ * (c.cvH t * (c.cvH t * c.cvH x * (c.cvH t)⁻¹) * (c.cvH t)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [e, hty, inv_mul_cancel]
    · refine ⟨x, hx, (t * x * t⁻¹)⁻¹, Subgroup.inv_mem _ hyK, a, ha, t * a,
        Subgroup.mul_mem _ ht' hTa, hx1, hx3, R1, ?_, ?_, ?_, ?_⟩
      · have e : c.cvH ((t * x * t⁻¹)⁻¹⁻¹ * (a * (t * x * t⁻¹)⁻¹ * a⁻¹)) =
            (c.cvH t * c.cvH x * (c.cvH t)⁻¹) *
              (c.cvH a * (c.cvH t * c.cvH x * (c.cvH t)⁻¹) * (c.cvH a)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv, inv_inv]
          group
        rw [e, hay, mul_inv_cancel]
      · have e : c.cvH ((t * x * t⁻¹)⁻¹⁻¹ * (t * a * x * (t * a)⁻¹)) =
            (c.cvH t * c.cvH x * (c.cvH t)⁻¹) *
              (c.cvH t * (c.cvH a * c.cvH x * (c.cvH a)⁻¹) * (c.cvH t)⁻¹) := by
          simp only [map_mul, map_inv, inv_inv]
          group
        rw [e, hax]
        group
      · have e : c.cvH (x⁻¹ * (t * a * (t * x * t⁻¹)⁻¹ * (t * a)⁻¹)) =
            (c.cvH x)⁻¹ * (c.cvH t * (c.cvH a * (c.cvH t * c.cvH x * (c.cvH t)⁻¹) *
              (c.cvH a)⁻¹) * (c.cvH t)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
          group
        rw [e, hay, hty, inv_inv, inv_mul_cancel]
      · intro k hk
        refine (Subgroup.closure_le _).mpr ?_ (hKcl k hk)
        rintro _ (rfl | rfl)
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · have := Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl) :
            c.cvH (t * x * t⁻¹)⁻¹ ∈
              Subgroup.closure {c.cvH x, c.cvH (t * x * t⁻¹)⁻¹})
          rwa [map_inv, inv_inv, ← map_inv] at this

end Ctx

end CFSG.Quasithin.H13
