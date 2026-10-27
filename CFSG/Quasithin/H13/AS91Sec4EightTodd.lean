module

public import CFSG.Quasithin.H13.AS91Sec4EightSimple
public import CFSG.Quasithin.Background.SmithB45MatIrr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeIdentCode
public import CFSG.Quasithin.H13.AS91Sec4EightM24

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b ∈ zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.emod_add_mul_ediv k 2, hk, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Fix

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)
  (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem eq_one_or_zE_of_fix_T {x : ↥D.E} (hx : ∀ t ∈ D.T, t * (x : G) * t⁻¹ = x) :
    x = 1 ∨ x = D.zE := by
  have hxT : (x : G) ∈ D.T := D.E_le_T hOut hTw x.2
  have hxZ : (x : G) ∈ (center D.T).map D.T.subtype := by
    refine ⟨⟨x, hxT⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    have h1 := hx g g.2
    change (g : G) * x = x * g
    calc (g : G) * x = ((g : G) * x * (g : G)⁻¹) * g := by group
      _ = x * g := by rw [h1]
  rw [D.center_T] at hxZ
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self (D.E_sq hHat hOut hTw D.z_mem_E) hxZ with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem zE_mem_of_odd {S : Set ↥D.E} (hS : ∀ φ : ↥D.Mb, ∀ s ∈ S, (φ : MulAut ↥D.E) s ∈ S)
    (hodd : Odd S.ncard) (h1 : (1 : ↥D.E) ∉ S) : D.zE ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : D.T ≤ normalizer (D.E : Set G) := D.T_le_G13.trans (D.G13_le_normalizer hOut hTw)
  letI : MulAction ↥D.Mb ↥S :=
    { smul := fun φ s => ⟨(φ : MulAut ↥D.E) s, hS φ s s.2⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  letI : MulAction ↥D.T ↥S := MulAction.compHom ↥S (D.toMb.comp (Subgroup.inclusion hTN))
  have h2 : ¬ 2 ∣ Nat.card ↥S := by
    rw [Nat.card_coe_set_eq]
    exact fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  obtain ⟨s, hs⟩ := (D.isPGroup_T hOut hTw).nonempty_fixed_point_of_prime_not_dvd_card ↥S h2
  have hfix : ∀ t ∈ D.T, t * ((s : ↥D.E) : G) * t⁻¹ = (s : ↥D.E) := by
    intro t ht
    have h3 := congrArg (fun y : ↥S => ((y : ↥D.E) : G)) (hs ⟨t, ht⟩)
    exact h3
  rcases D.eq_one_or_zE_of_fix_T hOut hTw hHat hfix with h3 | h3
  · exact absurd (h3 ▸ s.2) h1
  · exact h3 ▸ s.2

end Fix

section Orbit

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)
  (hM : CFSG.CGT.T75P.M24SylowInput)

include hOut hTw hHat hM

theorem card_Mb : Nat.card ↥D.Mb = 244823040 := by
  haveI := D.isSimpleGroup_Mb hOut hTw hHat
  obtain ⟨e⟩ := D.nonempty_mulEquiv_m24 hOut hTw hHat hM
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]

omit hM in
theorem stabilizer_zE : MulAction.stabilizer ↥D.Mb D.zE = D.Mz := by
  ext φ
  rfl

theorem card_orbit_zE : Nat.card ↥(MulAction.orbit ↥D.Mb D.zE) = 1771 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥D.Mb D.zE)
  rw [MulAction.index_stabilizer, D.stabilizer_zE hOut hTw hHat, D.card_Mz hOut hTw hHat,
    D.card_Mb hOut hTw hHat hM] at h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 138240)
    (h1.trans (by norm_num : (244823040 : ℕ) = 138240 * 1771))

theorem irreducible_E (U : Subgroup ↥D.E) (hU : ∀ φ ∈ D.Mb, ∀ u ∈ U, φ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  have hcU : Nat.card U = (U : Set ↥D.E).ncard := (Nat.card_coe_set_eq _).symm.trans rfl
  have hdvd : Nat.card U ∣ 2 ^ 11 := by
    rw [← D.card_E hOut hTw]
    exact Subgroup.card_subgroup_dvd_card U
  obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k ≠ 0 := by
    intro h0
    apply hbot
    rw [h0, pow_zero] at hUk
    exact Subgroup.card_eq_one.mp hUk
  set S : Set ↥D.E := (U : Set ↥D.E) \ {1} with hSdef
  have hSinv : ∀ φ : ↥D.Mb, ∀ s ∈ S, (φ : MulAut ↥D.E) s ∈ S := by
    rintro φ s ⟨hsU, hs1⟩
    refine ⟨hU φ φ.2 s hsU, fun hφs => hs1 ?_⟩
    have hφs' : (φ : MulAut ↥D.E) s = (φ : MulAut ↥D.E) 1 := by
      rw [map_one]
      exact hφs
    exact (φ : MulAut ↥D.E).injective hφs'
  have hSodd : Odd S.ncard := by
    rw [hSdef, Set.ncard_sdiff_singleton_of_mem (one_mem U), ← hcU, hUk]
    obtain ⟨m, hm⟩ : ∃ m, m = 2 ^ k := ⟨_, rfl⟩
    have hev : Even m := hm ▸ (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    have hpos : 0 < m := hm ▸ by positivity
    rw [← hm]
    obtain ⟨r, hr⟩ := hev
    exact Nat.odd_iff.mpr (by omega)
  have hz := D.zE_mem_of_odd hOut hTw hHat hSinv hSodd (fun h1 => h1.2 rfl)
  have horb : MulAction.orbit ↥D.Mb D.zE ⊆ (U : Set ↥D.E) := by
    rintro _ ⟨φ, rfl⟩
    exact hU φ φ.2 _ hz.1
  have hle : 1771 ≤ Nat.card U := by
    rw [hcU, ← D.card_orbit_zE hOut hTw hHat hM, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard horb (Set.toFinite _)
  rw [hUk] at hle
  have hk11 : k = 11 := by
    interval_cases k <;> first | rfl | (norm_num at hle)
  refine Subgroup.eq_top_of_card_eq U ?_
  rw [hUk, hk11, D.card_E hOut hTw]

theorem not_mathieuCode24 :
    ¬ @MathieuCode24 ↥D.E (commGroupOfElem (D.isElemAbelian_E hHat hOut hTw)) D.Mb ⊤ ⊥ := by
  intro hc
  have key : ∃ x : ↥D.E, x ≠ 1 ∧ Nat.card ↥(MulAction.orbit ↥D.Mb x) ∣ 759 := by
    letI : CommGroup ↥D.E := commGroupOfElem (D.isElemAbelian_E hHat hOut hTw)
    exact CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.exists_ne_one_card_orbit_dvd_of_mathieuCode24
      hc
  obtain ⟨x, hx1', hdvd'⟩ := key
  have hodd : Odd (MulAction.orbit ↥D.Mb x).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Odd.of_dvd_nat (by decide) hdvd'
  have h1 : (1 : ↥D.E) ∉ MulAction.orbit ↥D.Mb x := by
    rintro ⟨φ, hφ⟩
    apply hx1'
    have hφ' : (φ : MulAut ↥D.E) x = (φ : MulAut ↥D.E) 1 := by
      rw [map_one]
      exact hφ
    exact (φ : MulAut ↥D.E).injective hφ'
  have hinv : ∀ φ : ↥D.Mb, ∀ s ∈ MulAction.orbit ↥D.Mb x,
      (φ : MulAut ↥D.E) s ∈ MulAction.orbit ↥D.Mb x := by
    rintro φ _ ⟨ψ, rfl⟩
    exact ⟨φ * ψ, mul_smul φ ψ x⟩
  have hz := D.zE_mem_of_odd hOut hTw hHat hinv hodd h1
  have heq : MulAction.orbit ↥D.Mb D.zE = MulAction.orbit ↥D.Mb x := MulAction.orbit_eq_iff.mpr hz
  have h1771 := D.card_orbit_zE hOut hTw hHat hM
  rw [heq] at h1771
  rw [h1771] at hdvd'
  norm_num at hdvd'

theorem mathieuCocode24_E (hJ : MathieuSmallIrr24) :
    @MathieuCocode24 ↥D.E (commGroupOfElem (D.isElemAbelian_E hHat hOut hTw))
      (conjNormalizer D.E).range ⊤ ⊥ := by
  haveI := D.isSimpleGroup_Mb hOut hTw hHat
  have hiso := D.nonempty_mulEquiv_m24 hOut hTw hHat hM
  have hW2 : ∀ w : ↥D.E, w * w = 1 := fun w => Subtype.ext (D.E_sq hHat hOut hTw w.2)
  rcases @hJ ↥D.E (commGroupOfElem (D.isElemAbelian_E hHat hOut hTw)) inferInstance hW2 D.Mb hiso
      (D.irreducible_E hOut hTw hHat hM) (by rw [D.card_E hOut hTw]; norm_num) with hc | hc
  · exact absurd hc (D.not_mathieuCode24 hOut hTw hHat hM)
  · exact hc

end Orbit

end Data41

end CFSG.Quasithin.H13.AS91
