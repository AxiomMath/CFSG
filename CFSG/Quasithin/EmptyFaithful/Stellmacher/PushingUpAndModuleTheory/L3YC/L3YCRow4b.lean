module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCHeisExtra
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassIIRows
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod CFSG.Open
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7

namespace Stellmacher.PU.L3YC

variable {Y : Type} [Group Y] [Finite Y]

theorem l5_config_middle_or_other {K P P₀ : Subgroup Y} (hK5 : IsPSL 5 2 1 ↥K)
    (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
    (hPN : P ≤ Subgroup.normalizer (P₀ : Set Y)) (hperf : ⁅P₀, P₀⁆ = P₀)
    (hpsl : IsPSL 3 2 1 (ModO2 P₀)) :
    (CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 ↥P₀) ∧ Nat.card ↥(CFSG.pCore 2 ↥P₀) = 2 ^ 7) ∨
    ∃ (ψ : ↥K ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
      (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (a : ℕ) (hamn : a + 3 ≤ 5)
      (α : ↥P₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)),
      (a = 0 ∨ a = 2) ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥P₀ ∧
      (∀ x : ↥P₀,
        blkAt a 3 hamn ((g⁻¹ * ψ ⟨x, hP₀P.trans hpar.1 x.2⟩ * g :
          SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
            ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
        BlockForm a 3 ((g⁻¹ * ψ ⟨x, hP₀P.trans hpar.1 x.2⟩ * g :
          SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) ∧
      (∀ (k l : Fin 5) (hc : IsCross a 3 k l), ∃ p : ↥P₀, p ∈ CFSG.pCore 2 ↥P₀ ∧
        g⁻¹ * ψ ⟨p, hP₀P.trans hpar.1 p.2⟩ * g =
          SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) := by
  classical
  obtain ⟨ψ⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hK5
  have hP₀K : P₀ ≤ K := hP₀P.trans hpar.1
  obtain ⟨g, a, hamn, α, hprop, hαs, hker, hblk, hcross⟩ :=
    exists_config (K := K) (P := P) (P₀ := P₀) (n := 5) (m := 3) (by norm_num) (by norm_num)
      ψ.toMonoidHom ψ.surjective
      (fun k hk => by
        have h1 : k = 1 := ψ.injective (by simpa using hk)
        rw [h1]
        exact (pCoreOf 2 K).one_mem)
      hpar hPK hP₀P hPN hperf (Or.inl rfl) hpsl
  by_cases ha1 : a = 1
  · subst ha1
    left
    let θ : ↥P₀ →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
      (MulAut.conj g⁻¹).toMonoidHom.comp (ψ.toMonoidHom.comp (Subgroup.inclusion hP₀K))
    have hθ : ∀ x : ↥P₀, θ x = g⁻¹ * ψ ⟨x, hP₀K x.2⟩ * g := fun x => by
      simp [θ, Subgroup.inclusion]
    refine pCore_extraspecial_of_config θ ?_ α hker (fun x => ?_) (fun k l hc => ?_)
    · intro x y hxy
      have h1 : g⁻¹ * ψ ⟨x, hP₀K x.2⟩ * g = g⁻¹ * ψ ⟨y, hP₀K y.2⟩ * g := by
        rw [← hθ, ← hθ]; exact hxy
      have h2 : ψ ⟨x, hP₀K x.2⟩ = ψ ⟨y, hP₀K y.2⟩ := by
        have := mul_right_cancel h1
        exact mul_left_cancel this
      have h3 := ψ.injective h2
      have h4 := congrArg Subtype.val h3
      exact Subtype.ext h4
    · rw [hθ]
      exact hblk x
    · obtain ⟨p, hp, hpe⟩ := hcross k l hc
      exact ⟨p, hp, by rw [hθ]; exact hpe⟩
  · right
    refine ⟨ψ, g, a, hamn, α, ?_, hαs, hker, hblk, hcross⟩
    omega

theorem ne_of_L5 {K P B : Subgroup Y} (hK5 : IsPSL 5 2 1 ↥K) (hBP : B = perfectCore P)
    (hB3 : IsPSL 3 2 1 (ModO2 B)) : P ≠ K := by
  intro hPK
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hK5
  have hperf : Group.IsPerfect ↥K := by
    have : Group.IsPerfect (SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 5)
        (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hperf
  have hBK : B = K := by rw [hBP, hPK]; exact perfectCore_eq_self_of_perfect hKK
  have hcardK : Nat.card ↥K = 9999360 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 5, ZMod.card]
    simp [Fin.prod_univ_succ]
  have h1 : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥B) (p := 2)))
  rw [card_L32 hB3, ha, hBK, hcardK] at h1
  have h5 : 5 ∣ 2 ^ a := by
    have : 2 ^ a = 59520 := by omega
    rw [this]; norm_num
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
  omega

section Bar

variable {G : Type} [Group G] [Finite G]

theorem row4_L5_not_middle
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) {K P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hK5 : IsPSL 5 2 1 ↥K) (hpar : IsParabolic2 K P) (hBP : modO2Image H L = perfectCore P) :
    ∃ (ψ : ↥K ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
      (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (a : ℕ) (hamn : a + 3 ≤ 5)
      (α : ↥(modO2Image H L) →* SpecialLinearGroup (Fin 3) (ZMod 2)),
      (a = 0 ∨ a = 2) ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(modO2Image H L) ∧
      (∀ x : ↥(modO2Image H L),
        blkAt a 3 hamn ((g⁻¹ * ψ ⟨x, (hBP ▸ perfectCore_le P : modO2Image H L ≤ P).trans
            hpar.1 x.2⟩ * g : SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) =
            ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
        BlockForm a 3 ((g⁻¹ * ψ ⟨x, (hBP ▸ perfectCore_le P : modO2Image H L ≤ P).trans
            hpar.1 x.2⟩ * g : SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2))) ∧
      (∀ (k l : Fin 5) (hc : IsCross a 3 k l), ∃ p : ↥(modO2Image H L),
        p ∈ CFSG.pCore 2 ↥(modO2Image H L) ∧
        g⁻¹ * ψ ⟨p, (hBP ▸ perfectCore_le P : modO2Image H L ≤ P).trans hpar.1 p.2⟩ * g =
          SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) := by
  have hB3 : IsPSL 3 2 1 (ModO2 (modO2Image H L)) :=
    Stellmacher.CD.L3YC.isPSL_modO2_modO2Image hLH hq
  have hPK : P ≠ K := ne_of_L5 hK5 hBP hB3
  have hP₀P : modO2Image H L ≤ P := hBP ▸ perfectCore_le P
  have hPN : P ≤ Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [hBP]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le P)).1
      (perfectCore_normal P)
  have hperfB : ⁅modO2Image H L, modO2Image H L⁆ = modO2Image H L := by
    rw [hBP]
    exact perfectCore_perfect P
  rcases l5_config_middle_or_other hK5 hpar hPK hP₀P hPN hperfB hB3 with ⟨hV, hV7⟩ | hcfg
  · exact (classII_false hLG hGL hq hperf h (toModO2Image hLH) (toModO2Image_surjective hLH)
      (isPGroup_ker_toModO2Image hLH) hV hV7).elim
  · exact hcfg

end Bar

end Stellmacher.PU.L3YC

end CFSG.Quasithin
