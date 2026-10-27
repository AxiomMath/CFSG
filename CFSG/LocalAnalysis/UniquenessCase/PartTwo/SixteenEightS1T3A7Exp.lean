module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7K2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ExpA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ExpB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16t3_exp_three_alt (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168)
    {m : ℕ} (hm : m = 6 ∨ m = 7) (e : ↥(lBar V₀ V hV L) ≃* alternatingGroup (Fin m))
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK)
    {J : Subgroup (MulAut (Vtil V₀ V hV))}
    (hJ : ∀ g ∈ J, IsPGroup 3 (Subgroup.zpowers g) →
      ∃ (n : ↥(lBar V₀ V hV L)) (k : MulAut (Vtil V₀ V hV)),
        (n : MulAut (Vtil V₀ V hV)) * k = g ∧
          k ∈ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ∧
          (((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = 0 ∨
            ((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3} ∨
            ((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3, 3}))
    {Y : Subgroup G} (hY3 : IsPGroup 3 ↥Y) (hYS : Y ≤ YL ⊔ YK ⊔ D.T)
    (hYJ : barSub V₀ V hV Y ≤ J) : ∀ y ∈ Y, y ^ 3 = 1 := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMnorm : D.M ≤ normalizer (V : Set G) :=
    hset.hyp16.hyp125.pairFacts.le_normalizer
  have hYLle : YL ≤ D.M := hYL.1
  have hYKle : YK ≤ D.M := hYK.1
  have hYLn : (YL.subgroupOf D.M).Normal := hYL.2.1
  have hYKn : (YK.subgroupOf D.M).Normal := hYK.2.1
  have hYLbar : barSub V₀ V hV YL = lBar V₀ V hV L := hYL.2.2.1
  have hYKbar : barSub V₀ V hV YK =
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hYK.2.2.1
  obtain ⟨hS, -, hR2, -⟩ := s16t3_join_inf_cTilde hset hT h7 hYL hYK
  haveI : (YL.subgroupOf D.M).Normal := hYLn
  haveI : (YK.subgroupOf D.M).Normal := hYKn
  have hYLYKnorm : ((YL ⊔ YK).subgroupOf D.M).Normal := by
    rw [Subgroup.subgroupOf_sup hYLle hYKle]; infer_instance
  have hDTnorm : D.T ≤ normalizer ((YL ⊔ YK : Subgroup G) : Set G) :=
    D.sylowM.le.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hYLle hYKle)).1 hYLYKnorm)
  have hYle : Y ≤ YL ⊔ YK :=
    s16t3_le_of_isPGroup_three hDTnorm D.sylowM.isPGroup hY3 hYS
  have hAB : YL ≤ normalizer (YK : Set G) :=
    hYLle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYKle).1 hYKn)
  have hBA : YK ≤ normalizer (YL : Set G) :=
    hYKle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYLle).1 hYLn)
  have hLbKb : lBar V₀ V hV L ⊓
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥ := by
    obtain ⟨N, -, hLleN, -, -, hNKbot, -, -⟩ := hT.structure_of_seven h7
    exact le_bot_iff.1 (le_trans (inf_le_inf_right _ hLleN) (le_of_eq hNKbot))
  intro y hy
  obtain ⟨n, hn⟩ := hY3 (⟨y, hy⟩ : ↥Y)
  have hyn : y ^ 3 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  obtain ⟨u, hu, v, hv, hu3n, hv3n, hr⟩ :=
    s16t3_exists_three_parts hAB hBA hR2 (hYle hy) hyn
  have hyM : y ∈ D.M := hS (hYS hy)
  have huM : u ∈ D.M := hYLle hu
  have hvM : v ∈ D.M := hYKle hv
  have hrC : y * (u * v)⁻¹ ∈ F11.CTilde D.M V₀ V :=
    s16t3_inf_le_cTilde hset hm e hYL hYK hR2 hr
  obtain ⟨hrM, hrstab, hract⟩ := (mem_cTilde_iff hV hMnorm).1 hrC
  have hbarr1 :
      barHom V₀ V hV (s16g_le_stabTil hset) ⟨y * (u * v)⁻¹, hrM⟩ = 1 := by
    show actTil V₀ V hV ⟨y * (u * v)⁻¹, hMs hrM⟩ = 1
    rw [show (⟨y * (u * v)⁻¹, hMs hrM⟩ : stabTil V₀ V) =
      ⟨y * (u * v)⁻¹, hrstab⟩ from Subtype.ext rfl]
    exact hract
  have hbary_eq : barHom V₀ V hV (s16g_le_stabTil hset) ⟨y, hyM⟩ =
      barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩ *
        barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ := by
    have h1 : (⟨y, hyM⟩ : ↥D.M) = ⟨y * (u * v)⁻¹, hrM⟩ *
        (⟨u, huM⟩ * ⟨v, hvM⟩) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    rw [h1, map_mul, map_mul, hbarr1, one_mul]
  have hbar_u_mem : barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩ ∈
      lBar V₀ V hV L := by
    have hmem := actTil_mem_barSub V₀ V hV (X := YL) hu (hMs huM)
    rw [hYLbar] at hmem
    exact hmem
  have hbar_v_mem : barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ ∈
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := by
    have hmem := actTil_mem_barSub V₀ V hV (X := YK) hv (hMs hvM)
    rw [hYKbar] at hmem
    exact hmem
  have hbar_y_mem_J : barHom V₀ V hV (s16g_le_stabTil hset) ⟨y, hyM⟩ ∈ J := by
    apply hYJ
    exact actTil_mem_barSub V₀ V hV (X := Y) hy (hMs hyM)
  have hbary_3pow :
      (barHom V₀ V hV (s16g_le_stabTil hset) ⟨y, hyM⟩) ^ 3 ^ n = 1 := by
    have hsub : (⟨y, hyM⟩ : ↥D.M) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hyn)
    rw [← map_pow, hsub, map_one]
  have hP : IsPGroup 3
      ↥(Subgroup.zpowers (barHom V₀ V hV (s16g_le_stabTil hset) ⟨y, hyM⟩)) := by
    refine IsPGroup.of_card_dvd_pow (n := n) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.2 hbary_3pow
  obtain ⟨n', k, hnk, hkK, hcyc⟩ := hJ _ hbar_y_mem_J hP
  let bar_u_elem : ↥(lBar V₀ V hV L) :=
    ⟨barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩, hbar_u_mem⟩
  have hleft : ((bar_u_elem : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))⁻¹ *
      (n' : MulAut (Vtil V₀ V hV)) =
        barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ * k⁻¹ := by
    have hrel : (n' : MulAut (Vtil V₀ V hV)) * k =
        barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩ *
          barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ := by
      rw [hnk, hbary_eq]
    calc ((bar_u_elem : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))⁻¹ *
          (n' : MulAut (Vtil V₀ V hV))
        = (barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩)⁻¹ *
          (n' : MulAut (Vtil V₀ V hV)) := rfl
      _ = (barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩)⁻¹ *
          ((n' : MulAut (Vtil V₀ V hV)) * k) * k⁻¹ := by group
      _ = (barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩)⁻¹ *
          (barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, huM⟩ *
            barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩) * k⁻¹ := by
          rw [hrel]
      _ = barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ * k⁻¹ := by group
  have hleft_mem : ((bar_u_elem : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))⁻¹ *
      (n' : MulAut (Vtil V₀ V hV)) ∈ lBar V₀ V hV L :=
    (bar_u_elem⁻¹ * n').2
  have hright_mem : barHom V₀ V hV (s16g_le_stabTil hset) ⟨v, hvM⟩ * k⁻¹ ∈
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
    (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).mul_mem hbar_v_mem
      ((s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).inv_mem hkK)
  have hbot : ((bar_u_elem : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))⁻¹ *
      (n' : MulAut (Vtil V₀ V hV)) ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
    rw [← hLbKb]
    exact ⟨hleft_mem, by rw [hleft]; exact hright_mem⟩
  have h_eq_one : ((bar_u_elem : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))⁻¹ *
      (n' : MulAut (Vtil V₀ V hV)) = 1 := Subgroup.mem_bot.1 hbot
  have h_uniqueness : bar_u_elem = n' := by
    have h1 : bar_u_elem⁻¹ * n' = 1 := Subtype.ext (by simpa using h_eq_one)
    rw [inv_mul_eq_one] at h1
    exact h1
  rw [← h_uniqueness] at hcyc
  have hu3 : u ^ 3 = 1 :=
    s16t3_cube_of_cover_alt hset hm e hYL hu hu3n (n := bar_u_elem) rfl hcyc
  have hv3 : v ^ 3 = 1 := s16t3_cube_of_cover_K hset hK hYK hv hv3n
  have hy3_inf : y ^ 3 ∈ YL ⊓ YK :=
    s16t3_cube_mem_inf_of_normalizing hAB hBA hu hv hr hu3 hv3
  obtain ⟨s, hs⟩ := hR2 ⟨y ^ 3, hy3_inf⟩
  have hx2 : (y ^ 3) ^ 2 ^ s = 1 := by
    simpa using congrArg Subtype.val hs
  have hx3 : (y ^ 3) ^ 3 ^ n = 1 := by
    have h : (y ^ 3) ^ 3 ^ n = (y ^ 3 ^ n) ^ 3 := by
      rw [← pow_mul y 3 (3 ^ n), Nat.mul_comm 3 (3 ^ n), pow_mul y (3 ^ n) 3]
    rw [h, hyn, one_pow]
  have horder : orderOf (y ^ 3) = 1 := by
    have hg : orderOf (y ^ 3) ∣ Nat.gcd (2 ^ s) (3 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.2 hx2) (orderOf_dvd_iff_pow_eq_one.2 hx3)
    have hcop : Nat.gcd (2 ^ s) (3 ^ n) = 1 :=
      Nat.Coprime.pow s n
        ((Nat.coprime_primes Nat.prime_two Nat.prime_three).2 (by norm_num))
    rw [hcop] at hg
    exact Nat.dvd_one.1 hg
  exact orderOf_eq_one_iff.1 horder

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
