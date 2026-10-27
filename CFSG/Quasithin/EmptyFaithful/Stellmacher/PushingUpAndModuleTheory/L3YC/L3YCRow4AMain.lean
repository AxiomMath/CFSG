module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4A
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

theorem transfer4 {K B : Subgroup Y} (hBK : B ≤ K)
    (Θ : ↥K ≃* SpecialLinearGroup (Fin 4) (ZMod 2))
    (B₀ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hB₀ : (⊤ : Subgroup ↥B).map (Θ.toMonoidHom.comp (Subgroup.inclusion hBK)) = B₀)
    (hcard : Nat.card B₀ = 1344)
    (hdouble : ∀ g h : SpecialLinearGroup (Fin 4) (ZMod 2), g ∉ B₀ →
      h ∈ B₀ ∨ ∃ a ∈ B₀, ∃ b ∈ B₀, h = a * g * b) :
    Nat.card ↥B = 1344 ∧ (∀ X : Subgroup Y, B ≤ X → X ≤ K → X = B ∨ X = K) ∧
      (∀ g ∈ K, g ∉ B → ∀ h ∈ K, h ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, h = a * g * b) := by
  classical
  set θ : ↥B →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    Θ.toMonoidHom.comp (Subgroup.inclusion hBK) with hθ
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have h1 : Θ ⟨x, hBK x.2⟩ = Θ ⟨y, hBK y.2⟩ := hxy
    have h2 := Θ.injective h1
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hmem : ∀ k : ↥K, Θ k ∈ B₀ ↔ (k : Y) ∈ B := by
    intro k
    constructor
    · intro hk
      rw [← hB₀] at hk
      obtain ⟨x, -, hx⟩ := hk
      have h1 : Θ ⟨x, hBK x.2⟩ = Θ k := hx
      have h2 := Θ.injective h1
      have h3 := congrArg Subtype.val h2
      rw [← h3]
      exact x.2
    · intro hk
      rw [← hB₀]
      exact ⟨⟨k, hk⟩, Subgroup.mem_top _, rfl⟩
  have hdouble' : ∀ g ∈ K, g ∉ B → ∀ h ∈ K, h ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, h = a * g * b := by
    intro g hgK hgB h hhK
    have hgB₀ : Θ ⟨g, hgK⟩ ∉ B₀ := fun hc => hgB ((hmem ⟨g, hgK⟩).1 hc)
    rcases hdouble (Θ ⟨g, hgK⟩) (Θ ⟨h, hhK⟩) hgB₀ with hh | ⟨a₀, ha₀, b₀, hb₀, hab⟩
    · exact Or.inl ((hmem ⟨h, hhK⟩).1 hh)
    · right
      have ha : ((Θ.symm a₀ : ↥K) : Y) ∈ B := by
        apply (hmem (Θ.symm a₀)).1
        simpa using ha₀
      have hb : ((Θ.symm b₀ : ↥K) : Y) ∈ B := by
        apply (hmem (Θ.symm b₀)).1
        simpa using hb₀
      refine ⟨(Θ.symm a₀ : ↥K), ha, (Θ.symm b₀ : ↥K), hb, ?_⟩
      have h1 : (⟨h, hhK⟩ : ↥K) = Θ.symm a₀ * ⟨g, hgK⟩ * Θ.symm b₀ := by
        apply Θ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact hab
      have h2 := congrArg Subtype.val h1
      simpa using h2
  refine ⟨?_, ?_, hdouble'⟩
  · have h1 : Nat.card ((⊤ : Subgroup ↥B).map θ) = Nat.card (⊤ : Subgroup ↥B) :=
      Subgroup.card_map_of_injective hθinj
    rw [hB₀, hcard, Subgroup.card_top] at h1
    exact h1.symm
  · intro X hBX hXK
    by_cases hXB : X ≤ B
    · exact Or.inl (le_antisymm hXB hBX)
    · right
      obtain ⟨x, hxX, hxB⟩ := SetLike.not_le_iff_exists.mp hXB
      refine le_antisymm hXK fun h hhK => ?_
      rcases hdouble' x (hXK hxX) hxB h hhK with hh | ⟨a, ha, b, hb, rfl⟩
      · exact hBX hh
      · exact X.mul_mem (X.mul_mem (hBX ha) hxX) (hBX hb)

theorem ne_of_L4 {K P B : Subgroup Y} (hK4 : IsPSL 4 2 1 ↥K) (hBP : B = perfectCore P)
    (hB3 : IsPSL 3 2 1 (ModO2 B)) : P ≠ K := by
  intro hPK
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hK4
  have hperf : Group.IsPerfect ↥K := by
    have : Group.IsPerfect (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 4)
        (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hperf
  have hBK : B = K := by rw [hBP, hPK]; exact perfectCore_eq_self_of_perfect hKK
  have hcardK : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 4, ZMod.card]
    simp [Fin.prod_univ_succ]
  have h1 : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥B) (p := 2)))
  rw [card_L32 hB3, ha, hBK, hcardK] at h1
  have h5 : 5 ∣ 2 ^ a := by
    have : 2 ^ a = 120 := by omega
    rw [this]; norm_num
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
  omega

theorem l4_parabolic_data {K P B : Subgroup Y} (hK4 : IsPSL 4 2 1 ↥K) (hpar : IsParabolic2 K P)
    (hBP : B = perfectCore P) (hB3 : IsPSL 3 2 1 (ModO2 B)) :
    Nat.card ↥B = 1344 ∧ (∀ X : Subgroup Y, B ≤ X → X ≤ K → X = B ∨ X = K) ∧
      (∀ g ∈ K, g ∉ B → ∀ h ∈ K, h ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, h = a * g * b) := by
  classical
  obtain ⟨ψ⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hK4
  have hPK : P ≠ K := ne_of_L4 hK4 hBP hB3
  have hBP' : B ≤ P := hBP ▸ perfectCore_le P
  have hBK : B ≤ K := hBP'.trans hpar.1
  have hPN : P ≤ Subgroup.normalizer (B : Set Y) := by
    rw [hBP]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le P)).1
      (perfectCore_normal P)
  have hperf : ⁅B, B⁆ = B := by rw [hBP]; exact perfectCore_perfect P
  obtain ⟨g, a, hamn, α, hprop, hαs, hker, hblk, hcross⟩ :=
    exists_config (K := K) (P := P) (P₀ := B) (n := 4) (m := 3) (by norm_num) (by norm_num)
      ψ.toMonoidHom ψ.surjective
      (fun k hk => by
        have h1 : k = 1 := ψ.injective (by simpa using hk)
        rw [h1]
        exact (pCoreOf 2 K).one_mem)
      hpar hPK hBP' hPN hperf (Or.inl rfl) hB3
  let Θ : ↥K ≃* SpecialLinearGroup (Fin 4) (ZMod 2) := ψ.trans (MulAut.conj g⁻¹)
  let θ : ↥B →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    Θ.toMonoidHom.comp (Subgroup.inclusion hBK)
  have hθ : ∀ x : ↥B, θ x = g⁻¹ * ψ ⟨x, hBK x.2⟩ * g := fun x => by
    simp [θ, Θ, Subgroup.inclusion]
  have hcross' : ∀ (k l : Fin 4) (hc : IsCross a 3 k l), ∃ p ∈ CFSG.pCore 2 ↥B,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) := by
    intro k l hc
    obtain ⟨p, hp, hpe⟩ := hcross k l hc
    exact ⟨p, hp, by rw [hθ]; exact hpe⟩
  have ha01 : a = 0 ∨ a = 1 := by omega
  rcases ha01 with rfl | rfl
  · have hblk' : ∀ x : ↥B, blkAt 0 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
        BlockForm 0 3 ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun x => by
      rw [hθ]; exact hblk x
    have hV : ∀ z : Fin 3 → ZMod 2, ∃ n : ↥B,
        ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          blk4' 1 z := fun z => by
      obtain ⟨n, -, hn⟩ := generate_V4hyp θ (CFSG.pCore 2 ↥B) hcross' z
      exact ⟨n, hn⟩
    exact transfer4 hBK Θ hypStab (theta_eq_hyp θ α hαs hblk' hV) card_hypStab
      (fun g h hg => hypStab_double g h hg)
  · have hblk' : ∀ x : ↥B, blkAt 1 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
        BlockForm 1 3 ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun x => by
      rw [hθ]; exact hblk x
    have hV : ∀ z : Fin 3 → ZMod 2, ∃ n : ↥B,
        ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          blk4 z 1 := fun z => by
      obtain ⟨n, -, hn⟩ := generate_V4pt θ (CFSG.pCore 2 ↥B) hcross' z
      exact ⟨n, hn⟩
    exact transfer4 hBK Θ ptStab (theta_eq_pt θ α hαs hblk' hV) card_ptStab
      (fun g h hg => ptStab_double g h hg)

end Stellmacher.PU.L3YC

end CFSG.Quasithin
