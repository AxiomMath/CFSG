module

public import CFSG.Sporadic.Co2Smith.GlC0Marking
public import CFSG.Sporadic.Co2Smith.SmithCo2
public import CFSG.RankThree.Co2.Three

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.RankThree.Co2

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem exists_sylow_two_z0' :
    ∃ S : Sylow 2 K, z0 ∈ (S : Subgroup K) ∧
    ∀ s ∈ (S : Subgroup K), z0 * s = s * z0 := by
  obtain ⟨S, hS, hc⟩ := exists_sylow_two_z0
  exact ⟨S, hS, fun s hs => (hc s hs).symm⟩

section Hyp

@[expose] noncomputable def hypK : Co2CentHyp K :=
  @Co2CentHyp.ofTwoCentral K _ _
    CFSG.Sporadic.Co2.isSimpleGroup_Co2 z0 orderOf_z0 z0 z0_ne_one exists_sylow_two_z0'
    (MulEquiv.refl _)

@[expose] noncomputable def hypG {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz) : Co2CentHyp G :=
  Co2CentHyp.ofTwoCentral z hz z0 z0_ne_one exists_sylow_two_z0' φ

theorem hypK_z : hypK.z = z0 := rfl

@[expose] noncomputable def toHK (d : Cz) : hypK.H :=
  ⟨d, by
    show (d : K) ∈ Subgroup.centralizer ({hypK.z} : Set K)
    rw [hypK_z]
    exact d.2⟩

theorem toHK_mul (d d' : Cz) : toHK (d * d') = toHK d * toHK d' := rfl

theorem toHK_one : toHK 1 = 1 := rfl

theorem toHK_injective {d d' : Cz} (h : toHK d = toHK d') : d = d' :=
  Subtype.ext (congrArg Subtype.val h)

theorem coe_toHK (d : Cz) : ((toHK d : hypK.H) : K) = d := rfl

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

theorem hypG_φ (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz)
    (x : centralizer ({z} : Set G)) : (hypG hz φ).φ x = hypK.φ (toHK (φ x)) := rfl

theorem φ_zH (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz) : φ (zH z) = z0C := by
  apply toHK_injective
  apply hypK.φ.injective
  rw [← hypG_φ hz φ]
  exact ((hypG hz φ).φ_zG).trans hypK.φ_zG.symm

end Hyp

section Fus

variable
  {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

theorem isConj_K_of_isConj_G (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz)
    {d d' : Cz} (hd2 : d * d = 1) (hd1 : d ≠ 1) (hd2' : d' * d' = 1) (hd1' : d' ≠ 1)
    (h : IsConj (φ.symm d : G) (φ.symm d' : G)) : IsConj (d : K) (d' : K) := by
  have := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  set hG := hypG hz φ
  have hinv : ∀ x : Cz, x * x = 1 → x ≠ 1 →
      hypK.φ (toHK x) * hypK.φ (toHK x) = 1 ∧ hypK.φ (toHK x) ≠ 1 :=
    fun x h2 h1 => ⟨by rw [← map_mul, ← toHK_mul, h2, toHK_one, map_one], fun e =>
      h1 (toHK_injective (hypK.φ.injective (e.trans (map_one _).symm)))⟩
  obtain ⟨c, hc, hcd⟩ := exists_isConj_rep (hypK.φ (toHK d)) (hinv d hd2 hd1).1
    (hinv d hd2 hd1).2
  obtain ⟨c', hc', hcd'⟩ := exists_isConj_rep (hypK.φ (toHK d')) (hinv d' hd2' hd1').1
    (hinv d' hd2' hd1').2
  have hGd := hG.isConj_iff_of_class (t := φ.symm d) hc (by
    rw [hypG_φ, MulEquiv.apply_symm_apply]; exact hcd.symm)
  have hGd' := hG.isConj_iff_of_class (t := φ.symm d') hc' (by
    rw [hypG_φ, MulEquiv.apply_symm_apply]; exact hcd'.symm)
  have hKd := hypK.isConj_iff_of_class (t := toHK d) hc hcd.symm
  have hKd' := hypK.isConj_iff_of_class (t := toHK d') hc' hcd'.symm
  rw [coe_toHK] at hKd hKd'
  have key : ∀ a : G, IsConj a (φ.symm d : G) ↔ IsConj a (φ.symm d' : G) :=
    fun a => ⟨fun e => e.trans h, fun e => e.trans h.symm⟩
  have hd2K : (d : K) * d = 1 := congrArg Subtype.val hd2
  have hd1K : (d : K) ≠ 1 := fun e => hd1 (Subtype.ext e)
  rcases hypK.three_classes hd2K hd1K with e | e | e
  · have hA := hKd.1.1 e
    rw [← hGd.1, key, hGd'.1] at hA
    exact e.symm.trans (hKd'.1.2 hA)
  · have hB := hKd.2.1.1 e
    rw [← hGd.2.1, key, hGd'.2.1] at hB
    exact e.symm.trans (hKd'.2.1.2 hB)
  · have hC := hKd.2.2.1 e
    rw [← hGd.2.2, key, hGd'.2.2] at hC
    exact e.symm.trans (hKd'.2.2.2 hC)

theorem fixFusion (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Cz) : FixFusion φ :=
  fun _ _ hd2 hd1 hd2' hd1' h =>
    fixK_eq_of_isConj (isConj_K_of_isConj_G hz φ hd2 hd1 hd2' hd1' h)

end Fus

end CFSG.Sporadic.Co2Smith
