module

public import CFSG.Sporadic.MI301Three.Co1Cent
public import CFSG.Sporadic.SuzI301.RowBasic

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

section Abstract

variable {G : Type} [Group G] {t : G}

private theorem not_three_dvd_card_ker (L : CFSG.Monster.GMS.LeechSystem t)
    (hQ : Nat.card ↥(CFSG.Monster.GMS.leechQ t) = 2 ^ 25) : ¬ 3 ∣ Nat.card L.φ.ker := by
  intro h3
  have hle : L.φ.ker.map (Subgroup.centralizer ({t} : Set G)).subtype ≤
      CFSG.Monster.GMS.leechQ t := by
    rintro _ ⟨c, hc, rfl⟩
    exact (L.φ_ker c).1 hc
  have hd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hQ] at hd
  have h32 := Nat.prime_three.dvd_of_dvd_pow (h3.trans hd)
  norm_num at h32

private theorem isTypeWithCenter_of_equiv [Finite G] {K : Subgroup G} {H : Type} [Group H]
    {J : Subgroup H} (f : PQuot 3 K ≃* ↥J)
    (eJ : (↥J ⧸ Subgroup.center ↥J) ≃* CFSG.LieType.Multipliers.U43.X₀)
    (hZ : Nat.card ↥(Subgroup.center ↥J) = 9) :
    CFSG.LocalAnalysis.GLTheoremA.S8.IsTypeWithCenter 3 K
      (CFSG.LocalAnalysis.GLTheoremA.S8.isU4of 3) 9 :=
  ⟨CFSG.Sporadic.SuzI301.catalogIs_isU4of_three
    ((QuotientGroup.congr _ _ f (Subgroup.map_center_eq f)).trans eJ),
    by rw [Nat.card_congr (Subgroup.centerCongr f).toEquiv, hZ]⟩

end Abstract

section Layer


theorem isTypeWithCenter_rowK_leech {G : Type} [Group G] [Finite G] {t : G}
    (L : CFSG.Monster.GMS.LeechSystem t)
    (hQ : Nat.card ↥(CFSG.Monster.GMS.leechQ t) = 2 ^ 25) {ζ : G}
    (hζ : ζ ∈ Subgroup.centralizer ({t} : Set G)) (hζ3 : orderOf ζ = 3)
    (hy : IsConj CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.c0 (L.φ ⟨ζ, hζ⟩)) :
    CFSG.LocalAnalysis.GLTheoremA.S8.IsTypeWithCenter 3
      (CFSG.Open.GLAPLayer 3 (Subgroup.centralizer ({ζ} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G))) (CFSG.LocalAnalysis.GLTheoremA.S8.isU4of 3) 9 := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co1 := CFSG.Sporadic.Co1.Module.finite_co1
  set T := Subgroup.centralizer ({t} : Set G)
  set X : Subgroup ↥T := Subgroup.centralizer ({(⟨ζ, hζ⟩ : ↥T)} : Set ↥T)
  have hN := not_three_dvd_card_ker L hQ
  have hp : IsPGroup 3 (Subgroup.zpowers (⟨ζ, hζ⟩ : ↥T)) := by
    have ho : orderOf (⟨ζ, hζ⟩ : ↥T) = 3 := by rw [Subgroup.orderOf_mk, hζ3]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  have hX : X.map L.φ =
      Subgroup.centralizer ({L.φ ⟨ζ, hζ⟩} : Set CFSG.Blueprint.NativeSporadic.Co1) := by
    have h := map_inf_centralizer_of_ker_le Nat.prime_three hN (K := ⊤) le_top hp
    rw [Subgroup.map_top_of_surjective _ L.φ_surj, top_inf_eq, top_inf_eq] at h
    exact h.symm
  have hXG : X.map T.subtype = Subgroup.centralizer ({ζ} : Set G) ⊓ T :=
    CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' T ⟨ζ, hζ⟩
  obtain ⟨J, -, hZ9, ⟨eJ⟩, ⟨eL⟩⟩ := exists_layer_centralizer_of_isConj_c0 hy
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map Nat.prime_three (ψ := T.subtype)
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (GLAPLayer 3 X)
  rw [glaPLayer_map_eq_of_injective Nat.prime_three T.subtype T.subtype_injective, hXG] at e₁
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_map Nat.prime_three hN (GLAPLayer 3 X)
  rw [S267.map_glaPLayer Nat.prime_three L.φ hN, hX] at e₂
  obtain ⟨e₃⟩ := CFSG.LocalAnalysis.GLTheoremA.H301.nonempty_pQuot_glaPLayer_subtype
    Nat.prime_three
    (Subgroup.centralizer ({L.φ ⟨ζ, hζ⟩} : Set CFSG.Blueprint.NativeSporadic.Co1))
  exact isTypeWithCenter_of_equiv (e₁.symm.trans (e₂.trans (e₃.trans eL))) eJ hZ9

end Layer

end CFSG.Sporadic.MI301Three
