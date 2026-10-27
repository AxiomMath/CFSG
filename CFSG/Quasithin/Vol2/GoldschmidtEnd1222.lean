module

public import CFSG.Quasithin.Vol2.GoldschmidtOut1222
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Prime
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Alt
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222G2
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Wedge
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

namespace End1222

section Setting

variable {G : Type} [Group G] {L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem irr_of_irreducibleUnder (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (h : IsIrreducibleUnder L V) :
    ∀ J : Subgroup ↥V, (∀ g ∈ autOn L V, ∀ w ∈ J, (g : MulAut ↥V) w ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  rcases h.2 (J.map V.subtype) (Subgroup.map_subtype_le J)
    (le_normalizer_map_of_invariant hLV hJ) with h1 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have hw' : (w : G) ∈ J.map V.subtype := ⟨w, hw, rfl⟩
    rw [h1, Subgroup.mem_bot] at hw'
    exact Subgroup.mem_bot.2 (Subtype.ext hw')
  · right
    rw [eq_top_iff]
    intro w _
    have hw' : (w : G) ∈ J.map V.subtype := by rw [h1]; exact w.2
    obtain ⟨w', hw', hww'⟩ := hw'
    rw [← Subtype.ext hww']
    exact hw'

end Setting

theorem card_sl_three_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [← VolI.card_GL_zmod_two_eq 3, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

end End1222

section Main

open End1222

theorem end1222Fact_holds :
    End1222Fact := by
  intro G _ _ L V _ hV2 hLV hc hirr hO2 hmod c hcomm
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hV2 w w.2)
  by_cases hne : L ≤ Subgroup.centralizer (V : Set G)
  ·
    have hVbot : V = ⊥ := by
      have h1 : ⁅V, L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.2 hne)
      rw [← hc, h1]
    have hsub : Subsingleton ↥V := ⟨fun a b => Subtype.ext (by
      have ha : (a : G) ∈ (⊥ : Subgroup G) := by rw [← hVbot]; exact a.2
      have hb : (b : G) ∈ (⊥ : Subgroup G) := by rw [← hVbot]; exact b.2
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb])⟩
    have h1 : c = 1 := MulEquiv.ext fun v => Subsingleton.elim _ _
    rw [h1]
    exact Subgroup.one_mem _
  · let Γ : Subgroup (MulAut ↥V) := autOn L V
    have hcommΓ : ∀ g ∈ Γ, c * g = g * c := hcomm
    have hcomm' : commV Γ = ⊤ := commV_autOn_eq_top hLV hc
    have hZ : fixV (autOn L V) = (Subgroup.centralizer (L : Set G)).subgroupOf V :=
      fixV_autOn_eq hLV
    have hirrW : ∀ J : Subgroup ↥V, fixV Γ ≤ J → (∀ g ∈ Γ, ∀ w ∈ J, g w ∈ J) →
        J = fixV Γ ∨ J = ⊤ := by
      rw [hZ]
      exact InternalSec.irr_autOn hLV hirr
    have finish : (∃ v : ↥V, v ∉ fixV Γ ∧ c v * v⁻¹ ∈ fixV Γ) → c ∈ Γ := fun h => by
      rw [eq_one_of_exists hcomm' hirrW hcommΓ h]
      exact Γ.one_mem
    rcases hmod with ⟨n, hn, ⟨e⟩, hBN⟩ | ⟨⟨e⟩, hcard, -⟩ | ⟨⟨e⟩, hcard, hirrU⟩ |
      ⟨n, h5, h8, -, hAN⟩ | ⟨hcard, φ, hφs, hφk⟩ | ⟨-, hG2⟩ |
      ⟨hq, hcen, ⟨eA⟩, hCV, hcard, hirrU⟩
    ·
      rw [G64.BinaryNaturalSL.eq_top hBN]
      trivial
    ·
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
        isSimpleGroup_sl_zmodTwo le_rfl
      obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
      have hΓcard : Nat.card Γ = 168 := by
        rw [Nat.card_congr e'.toEquiv, card_sl_three_two]
      exact finish (exists_move_of_card_sixteen (by rw [hcard]; norm_num)
        (by rw [hΓcard]; norm_num) (by rw [hΓcard]; norm_num) hcommΓ)
    ·
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
        isSimpleGroup_sl_zmodTwo (by norm_num)
      obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
      have hirr0 := irr_of_irreducibleUnder hLV hirrU
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hirrU.1
      have hZbot : fixV Γ = ⊥ := fixV_eq_bot_of_irr hcomm' hirr0 ⟨a, ha⟩
      obtain ⟨v, hv1, hcv⟩ := exists_fixed_of_wedge hW2 hcard e' hirr0 hcommΓ
      refine finish ⟨v, ?_, ?_⟩
      · rw [hZbot]
        exact fun h => hv1 (Subgroup.mem_bot.1 h)
      · rw [hcv, mul_inv_cancel]
        exact (fixV Γ).one_mem
    ·
      have := AltDn.exists_move_of_altDn (n := n) (by omega) hAN hZ hcommΓ
      rw [← hZ] at this
      exact finish this
    ·
      obtain ⟨e'⟩ := Out1222.nonempty_autOn_mulEquiv_of_surjective hLV φ hφs hφk
      have hΓcard : Nat.card Γ = 2520 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup]
        simp [Nat.card_eq_fintype_card, Nat.factorial]
      exact finish (exists_move_of_card_sixteen (by rw [hcard]; norm_num)
        (by rw [hΓcard]; norm_num) (by rw [hΓcard]; norm_num) hcommΓ)
    ·
      obtain ⟨K, _, _, hK, hR⟩ := hG2
      have := G2.exists_move_of_zornQ (by simpa using hK) hR hZ hcommΓ
      rw [← hZ] at this
      exact finish this
    ·
      obtain ⟨e'⟩ := Out1222.nonempty_autOn_mulEquiv_quotient hLV hCV
      have hirr0 := irr_of_irreducibleUnder hLV hirrU
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hirrU.1
      have hZbot : fixV Γ = ⊥ := fixV_eq_bot_of_irr hcomm' hirr0 ⟨a, ha⟩
      have hfix : ∀ b ∈ Subgroup.centralizer (Γ : Set (MulAut ↥V)), ∀ v : ↥V, v ≠ 1 →
          b v = v → b = 1 := by
        intro b hb v hv1 hbv
        refine eq_one_of_exists hcomm' hirrW
          (fun g hg => (Subgroup.mem_centralizer_iff.1 hb g hg).symm) ⟨v, ?_, ?_⟩
        · rw [hZbot]
          exact fun h => hv1 (Subgroup.mem_bot.1 h)
        · rw [hbv, mul_inv_cancel]
          exact (fixV Γ).one_mem
      have hfin : Finite ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
        Nat.finite_of_card_ne_zero (by omega)
      have hnt : Nontrivial ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
        Finite.one_lt_card_iff_nontrivial.1 (by omega)
      obtain ⟨z₀, hz₀⟩ := exists_ne (1 : ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      have hzbar1 : (z₀ : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := fun h => hz₀ (Subtype.ext h)
      have hzbar3 : (z₀ : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
        have h := pow_card_eq_one' (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) (x := z₀)
        rw [hcen] at h
        exact congrArg Subtype.val h
      have hzbarc : ∀ y : ↥L ⧸ CFSG.pCore 2 ↥L,
          y * (z₀ : ↥L ⧸ CFSG.pCore 2 ↥L) = (z₀ : ↥L ⧸ CFSG.pCore 2 ↥L) * y :=
        fun y => Subgroup.mem_center_iff.1 z₀.2 y
      let z : ↥(autOn L V) := e'.symm (z₀ : ↥L ⧸ CFSG.pCore 2 ↥L)
      have hzΓ : (z : MulAut ↥V) ∈ Γ := z.2
      have hz1 : (z : MulAut ↥V) ≠ 1 := fun h => hzbar1 (by
        have h1 : z = 1 := Subtype.ext h
        have h2 := congrArg e' h1
        rwa [MulEquiv.apply_symm_apply, map_one] at h2)
      have hz3 : (z : MulAut ↥V) ^ 3 = 1 := by
        have h1 : z ^ 3 = 1 := by
          apply e'.injective
          rw [map_pow, MulEquiv.apply_symm_apply, hzbar3, map_one]
        exact congrArg Subtype.val h1
      have hzC : (z : MulAut ↥V) ∈ Subgroup.centralizer (Γ : Set (MulAut ↥V)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h1 : (⟨g, hg⟩ : ↥(autOn L V)) * z = z * ⟨g, hg⟩ := by
          apply e'.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact hzbarc _
        exact congrArg Subtype.val h1
      have hΓcard : Nat.card Γ = 1080 := by
        rw [Nat.card_congr e'.toEquiv, Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)), hcen, Nat.card_congr eA.toEquiv,
          nat_card_alternatingGroup]
        simp [Nat.card_eq_fintype_card, Nat.factorial]
      exact mem_of_card_sixtyfour (by rw [hcard]; norm_num) hfix (by rw [hΓcard]; norm_num)
        hzΓ hz1 hz3 hzC (Subgroup.mem_centralizer_iff.2 fun g hg => (hcommΓ g hg).symm)

end Main

end CFSG.Quasithin.H13
