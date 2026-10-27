module

public import CFSG.RankThree.GF2n.Tim81.Sec4.HBarData
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Factor
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRepLattice
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixed
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzCor23
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.GroupTheory
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}
variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]

namespace RootHyp

theorem card_inf_W0_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) :
    Nat.card ↥(Pc M V ⊓ W₀) ≤
      Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀) := by
  have h1 := card_Pc_inf_W0_mul_card_V_le h hPH hVH (W₀ := W₀) hW₀
  have h2 := card_Pc_inf_kOf_le_of_isL2OrSz h hPH hVH hH hnM hK hab hL
  have h3 : Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V ≤
      Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀) * Nat.card V := by
    calc Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V
        ≤ Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) := h1
      _ ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card V) * Nat.card ↥(V ⊓ W₀) :=
          Nat.mul_le_mul_right _ h2
      _ = Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀) * Nat.card V := by ring
  exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos

theorem card_W0_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card W₀ ≤ Nat.card (imgK V H (Pc M V)) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := by
  calc Nat.card W₀ ≤ Nat.card ↥(Pc M V ⊓ W₀) ^ 2 :=
        card_W0_le_sq h hPH hVH hH hnM hW₀ hN hW₀ne hmin
    _ ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀)) ^ 2 :=
        Nat.pow_le_pow_left (card_inf_W0_le h hPH hVH hH hnM hK hab hL hW₀) 2
    _ = Nat.card (imgK V H (Pc M V)) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := by ring


theorem not_isNaturalModule_subRepW (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    ¬ IsNaturalModule (subRepW hW ψ hW₀ hN) := by
  intro hρ
  classical
  have hS : conjSubgroup h₀ (Pc M V) ≤ H := by
    rw [hH]
    exact le_sup_right
  obtain ⟨-, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  set X₀ : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) := subW hW W₀
  set ρ : Representation (ZMod 2) SL(2, F) X₀ := subRepW hW ψ hW₀ hN
  have hρdef : ρ = subRepW hW ψ hW₀ hN := rfl
  have htop : fixedSub ρ (conjSubgroup a (utri F)) ⊔
      fixedSub ρ (conjSubgroup b (utri F)) = ⊤ :=
    Sec2.sup_fixedSub_conj_utri_eq_top ρ hρ hne
  rw [← ha, ← hb] at htop
  have hmap := congrArg (Submodule.map X₀.subtype) htop
  rw [Submodule.map_sup, Submodule.map_top, Submodule.range_subtype] at hmap
  simp only [hρdef, MulEquiv.toMonoidHom_eq_coe] at hmap
  rw [fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
    fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := conjSubgroup h₀ (Pc M V)) hS] at hmap
  have hE : W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) ≤ Tim79a.xOf V H :=
    inf_le_left.trans hW₀
  have hE' : W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) ≤
      Tim79a.xOf V H := inf_le_left.trans hW₀
  rw [← subW_sup (hW := hW) hE hE'] at hmap
  have heq : W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) ⊔
      (W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G)) = W₀ :=
    (subW_inj (hW := hW) (sup_le hE hE') hW₀).mp hmap
  have heq' : (V ⊓ W₀) ⊔ (conjSubgroup h₀ V ⊓ W₀) = W₀ := by
    calc (V ⊓ W₀) ⊔ (conjSubgroup h₀ V ⊓ W₀)
        = (W₀ ⊓ Subgroup.centralizer (Pc M V : Set G)) ⊔
            (W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G)) := by
          rw [inf_centralizer_Pc_eq_inf (h := h), inf_centralizer_conj_Pc_eq_inf (h := h)]
      _ = W₀ := heq
  exact sup_inf_V_W0_ne_of_ne_bot h hPH hVH hH hnM hW₀ hN hW₀ne heq'

theorem not_isSzNatural_subRepW
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    ¬ IsSzNatural (subRepW hW ψ hW₀ hN) := by
  intro hρ
  classical
  have hS : conjSubgroup h₀ (Pc M V) ≤ H := by
    rw [hH]
    exact le_sup_right
  obtain ⟨-, x, y, hx, hy, hne⟩ := imgK_map_sz h hPH hVH hH hnM hF ψ
  set X₀ : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) := subW hW W₀
  set ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a F) X₀ :=
    subRepW hW ψ hW₀ hN
  have hρdef : ρ = subRepW hW ψ hW₀ hN := rfl
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]
    exact hF
  have htop : fixedSub ρ (conjSubgroup x (Sec2.szZ a F)) ⊔
      fixedSub ρ (conjSubgroup y (Sec2.szZ a F)) = ⊤ :=
    Sec2.sup_fixedSub_conj_szZ_eq_top hK ρ hρ hne
  rw [← hx, ← hy] at htop
  have hmap := congrArg (Submodule.map X₀.subtype) htop
  rw [Submodule.map_sup, Submodule.map_top, Submodule.range_subtype] at hmap
  simp only [hρdef, MulEquiv.toMonoidHom_eq_coe] at hmap
  rw [fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
    fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := conjSubgroup h₀ (Pc M V)) hS] at hmap
  have hE : W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) ≤ Tim79a.xOf V H :=
    inf_le_left.trans hW₀
  have hE' : W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) ≤
      Tim79a.xOf V H := inf_le_left.trans hW₀
  rw [← subW_sup (hW := hW) hE hE'] at hmap
  have heq : W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) ⊔
      (W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G)) = W₀ :=
    (subW_inj (hW := hW) (sup_le hE hE') hW₀).mp hmap
  have heq' : (V ⊓ W₀) ⊔ (conjSubgroup h₀ V ⊓ W₀) = W₀ := by
    calc (V ⊓ W₀) ⊔ (conjSubgroup h₀ V ⊓ W₀)
        = (W₀ ⊓ Subgroup.centralizer (Pc M V : Set G)) ⊔
            (W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G)) := by
          rw [inf_centralizer_Pc_eq_inf (h := h), inf_centralizer_conj_Pc_eq_inf (h := h)]
      _ = W₀ := heq
  exact sup_inf_V_W0_ne_of_ne_bot h hPH hVH hH hnM hW₀ hN hW₀ne heq'

theorem exists_apply_subRepW_ne_one {X : Type} [Group X] (h : RootHyp M V)
    (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (ψ : HBar V H ≃* X) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    ∃ g : X, subRepW hW ψ hW₀ hN g ≠ 1 := by
  classical
  by_contra htriv
  push Not at htriv
  have hS : conjSubgroup h₀ (Pc M V) ≤ H := by
    rw [hH]
    exact le_sup_right
  have htopP : fixedSub (subRepW hW ψ hW₀ hN)
      ((imgK V H (Pc M V)).map ψ.toMonoidHom) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_fixedSub]
    intro g _
    rw [htriv g]
    rfl
  have htopPh : fixedSub (subRepW hW ψ hW₀ hN)
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_fixedSub]
    intro g _
    rw [htriv g]
    rfl
  have hmapP := congrArg (Submodule.map (subW hW W₀).subtype) htopP
  rw [Submodule.map_top, Submodule.range_subtype, MulEquiv.toMonoidHom_eq_coe ψ,
    fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH] at hmapP
  have hmapPh := congrArg (Submodule.map (subW hW W₀).subtype) htopPh
  rw [Submodule.map_top, Submodule.range_subtype, MulEquiv.toMonoidHom_eq_coe ψ,
    fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := conjSubgroup h₀ (Pc M V)) hS] at hmapPh
  have hE : W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) ≤ Tim79a.xOf V H :=
    inf_le_left.trans hW₀
  have hE' : W₀ ⊓ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) ≤
      Tim79a.xOf V H := inf_le_left.trans hW₀
  have hleP : W₀ ≤ W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) :=
    (subW_le_subW_iff (hW := hW) (F := W₀ ⊓
      Subgroup.centralizer (Pc M V : Set G)) hW₀).mp (by rw [hmapP])
  have hlePh : W₀ ≤ W₀ ⊓
      Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) :=
    (subW_le_subW_iff (hW := hW) (F := W₀ ⊓
      Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G)) hW₀).mp (by rw [hmapPh])
  have hWleP : W₀ ≤ Subgroup.centralizer (Pc M V : Set G) := hleP.trans inf_le_right
  have hWlePh : W₀ ≤ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) :=
    hlePh.trans inf_le_right
  have hWleV : W₀ ≤ V := by
    have h : W₀ = V ⊓ W₀ := by
      rw [← inf_centralizer_Pc_eq_inf (h := h)]
      exact (inf_eq_left.mpr hWleP).symm
    rw [h]
    exact inf_le_left
  have hWleVh : W₀ ≤ conjSubgroup h₀ V := by
    have h : W₀ = conjSubgroup h₀ V ⊓ W₀ := by
      rw [← inf_centralizer_conj_Pc_eq_inf (h := h)]
      exact (inf_eq_left.mpr hWlePh).symm
    rw [h]
    exact inf_le_left
  have hVVh : V ⊓ conjSubgroup h₀ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ V ⊓ conjSubgroup h₀ (Pc M V) :=
      ⟨hx.1, (Subgroup.map_mono (f := (MulAut.conj h₀).toMonoidHom)
        h.toHyp.le_Pc) hx.2⟩
    rwa [inf_conj_Pc_eq_bot h hH hnM] at hx'
  exact hW₀ne (le_bot_iff.mp (le_inf hWleV hWleVh |>.trans (le_of_eq hVVh)))

theorem false_of_card_lt_fixedSub
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hlt : Nat.card W₀ < Nat.card ↥(V ⊓ W₀) ^ 4) : False := by
  classical
  rcases hL with ⟨F, hField, hFintype, hCharP, h4, ⟨ψ⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, ha, hF, ⟨ψ⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
    haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
    have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
    obtain ⟨n, -, hFn⟩ := FiniteField.card F 2
    have hn : 1 ≤ (n : ℕ) :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hFn]; omega)
    obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
    have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (n : ℕ) := by
      rw [hAcard, hFn]
    have hfix : Nat.card (fixedSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)) =
        Nat.card ↥(V ⊓ W₀) := by
      rw [MulEquiv.toMonoidHom_eq_coe ψ,
        natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
        inf_centralizer_Pc_eq_inf (h := h)]
    have hnat : IsNaturalModule ρ := by
      refine Sec2.isNaturalModule_of_card_lt hn hFn ρ hnt
        ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard' ?_
      have h1 : Nat.card ↥(subW hW W₀) = Nat.card W₀ := natCard_subW hW hW₀
      have hlt' : Nat.card ↥(subW hW W₀) < Nat.card ↥(V ⊓ W₀) ^ 4 := h1.symm ▸ hlt
      simpa only [hfix] using hlt'
    exact not_isNaturalModule_subRepW h hPH hVH hH hnM ψ hW₀ hN hW₀ne hnat
  · letI := hField
    letI := hFintype
    letI := hCharP
    set ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a F) (subW hW W₀) :=
      subRepW hW ψ hW₀ hN
    haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
    have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
    have hK : Nat.card F = 2 ^ (2 * a + 1) := by
      rw [Nat.card_eq_fintype_card]
      exact hF
    obtain ⟨-, x, y, hx, -, -⟩ := imgK_map_sz h hPH hVH hH hnM hF ψ
    have hfix : Nat.card (fixedSub ρ (conjSubgroup x (Sec2.szZ a F))) =
        Nat.card ↥(V ⊓ W₀) := by
      rw [← hx, MulEquiv.toMonoidHom_eq_coe ψ,
        natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
        inf_centralizer_Pc_eq_inf (h := h)]
    have hnat : IsSzNatural ρ := by
      refine Sec2.isSzNatural_of_card_lt_fixedSub_conj hK ρ hnt x ?_
      have h1 : Nat.card ↥(subW hW W₀) = Nat.card W₀ := natCard_subW hW hW₀
      have hlt' : Nat.card ↥(subW hW W₀) < Nat.card ↥(V ⊓ W₀) ^ 4 := h1.symm ▸ hlt
      simpa only [hfix] using hlt'
    exact not_isSzNatural_subRepW h hPH hVH hH hnM hF ψ hW₀ hN hW₀ne hnat

theorem card_inf_V_W0_le
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card ↥(V ⊓ W₀) ≤ Nat.card (imgK V H (Pc M V)) := by
  by_contra hcon
  have hltP : Nat.card (imgK V H (Pc M V)) < Nat.card ↥(V ⊓ W₀) :=
    Nat.lt_of_not_le hcon
  have hW0 := card_W0_le h hPH hVH hH hnM hK hab hL hW₀ hN hW₀ne hmin
  have hlt : Nat.card W₀ < Nat.card ↥(V ⊓ W₀) ^ 4 := by
    calc Nat.card W₀
        ≤ Nat.card (imgK V H (Pc M V)) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := hW0
      _ < Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 :=
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hltP (by norm_num))
            (Nat.pow_pos (Nat.card_pos (α := ↥(V ⊓ W₀))))
      _ = Nat.card ↥(V ⊓ W₀) ^ 4 := by ring
  exact false_of_card_lt_fixedSub (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin hlt


private theorem card_inf_centralizer_le_of_swap {X : Type} [Group X] [Finite X]
    {A B W : Subgroup X} {t : X} (hW : W = A ⊔ B) (hinf : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (htA : conjSubgroup t A = B) (htB : conjSubgroup t B = A) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({t} : Set X)) ≤ Nat.card A := by
  classical
  have hdec : ∀ x ∈ W ⊓ Subgroup.centralizer ({t} : Set X),
      ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    exact exists_mul_of_mem_sup_of_commute hcomm (by rw [← hW]; exact hx.1)
  let f : ↥(W ⊓ Subgroup.centralizer ({t} : Set X)) → ↥A := fun x =>
    ⟨Classical.choose (hdec x.1 x.2), (Classical.choose_spec (hdec x.1 x.2)).1⟩
  have hcomp : ∀ x : ↥(W ⊓ Subgroup.centralizer ({t} : Set X)),
      (x : X) = (f x : X) * (t * (f x : X) * t⁻¹) := by
    intro x
    obtain ⟨haA, b, hbB, hab⟩ := Classical.choose_spec (hdec x.1 x.2)
    set a : X := Classical.choose (hdec x.1 x.2) with ha
    have haA' : a ∈ A := haA
    have hab' : a * b = (x : X) := hab
    have hfix : t * (x : X) * t⁻¹ = (x : X) := by
      have hc := (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    have hd : t * a * t⁻¹ ∈ B :=
      htA ▸ Subgroup.mem_map.mpr ⟨a, haA', rfl⟩
    have hc : t * b * t⁻¹ ∈ A :=
      htB ▸ Subgroup.mem_map.mpr ⟨b, hbB, rfl⟩
    have hEq : a * b = (t * b * t⁻¹) * (t * a * t⁻¹) := by
      calc a * b = (x : X) := hab'
        _ = t * (x : X) * t⁻¹ := hfix.symm
        _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by rw [← hab']; group
        _ = (t * b * t⁻¹) * (t * a * t⁻¹) := (hcomm _ hc _ hd).symm
    have h2 : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
      calc a⁻¹ * (t * b * t⁻¹)
          = a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * b) * (t * a * t⁻¹)⁻¹ := by rw [← hEq]
        _ = b * (t * a * t⁻¹)⁻¹ := by group
    have h1 : a⁻¹ * (t * b * t⁻¹) = 1 := by
      have hmemB : b * (t * a * t⁻¹)⁻¹ ∈ B :=
        B.mul_mem hbB (B.inv_mem hd)
      have hmem : a⁻¹ * (t * b * t⁻¹) ∈ A ⊓ B :=
        Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem haA') hc, h2.symm ▸ hmemB⟩
      rwa [hinf] at hmem
    have hac : a = t * b * t⁻¹ := inv_mul_eq_one.mp h1
    have hbd : b = t * a * t⁻¹ := by
      apply mul_left_cancel (a := a)
      calc a * b = (t * b * t⁻¹) * (t * a * t⁻¹) := hEq
        _ = a * (t * a * t⁻¹) := by rw [← hac]
    calc (x : X) = a * b := hab'.symm
      _ = a * (t * a * t⁻¹) := by rw [hbd]
  refine Nat.card_le_card_of_injective f ?_
  intro x y hxy
  have hx := hcomp x
  have hy := hcomp y
  rw [hxy] at hx
  exact Subtype.ext (hx.trans hy.symm)

private theorem inf_centralizer_mul_kOf_eq {W₀ : Subgroup G} {x y k : G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hk : k ∈ kOf V H) (hx : x = y * k) :
    W₀ ⊓ Subgroup.centralizer ({x} : Set G) =
      W₀ ⊓ Subgroup.centralizer ({y} : Set G) := by
  have hkw : ∀ w ∈ W₀, k * w = w * k := by
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 w (hW₀ hw)).symm
  ext w
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hw, hwx⟩
    have h1 : w * (y * k) = (y * k) * w := by rwa [← hx]
    have h2 : w * (y * k) = (w * y) * k := by group
    have h3 : (y * k) * w = (y * w) * k := by
      calc (y * k) * w = y * (k * w) := by group
        _ = y * (w * k) := by rw [hkw w hw]
        _ = (y * w) * k := by group
    rw [h2, h3] at h1
    exact ⟨hw, mul_right_cancel h1⟩
  · rintro ⟨hw, hwy⟩
    have h1 : w * (y * k) = (y * k) * w := by
      have h2 : w * (y * k) = (w * y) * k := by group
      have h3 : (y * k) * w = (y * w) * k := by
        calc (y * k) * w = y * (k * w) := by group
          _ = y * (w * k) := by rw [hkw w hw]
          _ = (y * w) * k := by group
      rw [h2, h3, hwy]
    exact ⟨hw, by rwa [hx]⟩

private theorem inf_centralizer_conj_eq_conj {W₀ : Subgroup G} {g t : G}
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hg : g ∈ H) :
    W₀ ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) =
      conjSubgroup g (W₀ ⊓ Subgroup.centralizer ({t} : Set G)) := by
  rw [centralizer_conj_singleton, CFSG.RankThree.GF2n.conjSubgroup_inf,
    conjSubgroup_eq_self_iff.mpr (hN hg)]

private theorem commute_of_le_xOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {u v : G} (hu : u ∈ W₀) (hv : v ∈ W₀) : u * v = v * u :=
  congrArg Subtype.val ((isElemAbelian_xOf h hPH hVH).1.is_comm.comm
    ⟨u, hW₀ hu⟩ ⟨v, hW₀ hv⟩)

@[expose] noncomputable def twistMap {W₀ : Subgroup G} (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (x : G) (hxN : x ∈ Subgroup.normalizer (W₀ : Set G)) : ↥W₀ →* ↥W₀ where
  toFun w := ⟨(w : G) * (x * (w : G) * x⁻¹),
    W₀.mul_mem w.2 ((Subgroup.mem_normalizer_iff.mp hxN (w : G)).mp w.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    have ha : x * (a : G) * x⁻¹ ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp hxN (a : G)).mp a.2
    have hb : x * (b : G) * x⁻¹ ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp hxN (b : G)).mp b.2
    have hba : (b : G) * (x * (a : G) * x⁻¹) = (x * (a : G) * x⁻¹) * (b : G) :=
      hWcomm b b.2 _ ha
    refine Subtype.ext ?_
    show ((a : G) * (b : G)) * (x * ((a : G) * (b : G)) * x⁻¹) =
      ((a : G) * (x * (a : G) * x⁻¹)) * ((b : G) * (x * (b : G) * x⁻¹))
    calc ((a : G) * (b : G)) * (x * ((a : G) * (b : G)) * x⁻¹)
        = (a : G) * (b : G) * ((x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹)) := by
          rw [show x * ((a : G) * (b : G)) * x⁻¹ =
            (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) from by group]
      _ = (a : G) * ((b : G) * (x * (a : G) * x⁻¹)) * (x * (b : G) * x⁻¹) := by group
      _ = (a : G) * ((x * (a : G) * x⁻¹) * (b : G)) * (x * (b : G) * x⁻¹) := by rw [hba]
      _ = ((a : G) * (x * (a : G) * x⁻¹)) * ((b : G) * (x * (b : G) * x⁻¹)) := by group

private theorem twistMap_ker {W₀ : Subgroup G} (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (hWsq : ∀ u ∈ W₀, u * u = 1) {x : G}
    (hxN : x ∈ Subgroup.normalizer (W₀ : Set G)) :
    (twistMap hWcomm x hxN).ker = (W₀ ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf W₀ := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hw
    have h1 : (w : G) * (x * (w : G) * x⁻¹) = 1 := congrArg Subtype.val hw
    have h2 : (w : G) * x * (w : G) = x := by
      have := congrArg (fun z => z * x) h1
      simpa [mul_assoc] using this
    have h3 : (w : G) * x = x * (w : G) := by
      have := congrArg (fun z => z * (w : G)) h2
      simpa [mul_assoc, hWsq w w.2] using this
    exact ⟨w.2, h3⟩
  · rintro ⟨-, hwx⟩
    apply Subtype.ext
    have hfix : x * (w : G) * x⁻¹ = (w : G) := by
      rw [← hwx]
      group
    show (w : G) * (x * (w : G) * x⁻¹) = 1
    rw [hfix]
    exact hWsq w w.2

private theorem twistMap_range_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {A : Subgroup G}
    (hA : A = Pc M V ⊓ W₀) {x : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V)
    (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (hWsq : ∀ u ∈ W₀, u * u = 1)
    (hcard : Nat.card W₀ = Nat.card A ^ 2)
    (hker : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card A) :
    (twistMap hWcomm x (hN hxH)).range = A.subgroupOf W₀ := by
  classical
  have hxN : x ∈ Subgroup.normalizer (W₀ : Set G) := hN hxH
  let φ : ↥W₀ →* ↥W₀ := twistMap hWcomm x hxN
  have hkerEq : Nat.card ↥φ.ker =
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [twistMap_ker hWcomm hWsq hxN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrank := Subgroup.card_ker_mul_card_range φ
  have hcardRange : Nat.card A ≤ Nat.card ↥φ.range := by
    have hle : Nat.card A * Nat.card A ≤ Nat.card A * Nat.card ↥φ.range := by
      calc Nat.card A * Nat.card A = Nat.card W₀ := by rw [hcard]; ring
        _ = Nat.card ↥φ.ker * Nat.card ↥φ.range := hrank.symm
        _ ≤ Nat.card A * Nat.card ↥φ.range := by
            refine Nat.mul_le_mul_right _ ?_
            rw [hkerEq]
            exact hker
    exact Nat.le_of_mul_le_mul_left hle Nat.card_pos
  have hrange_le_A : φ.range ≤ A.subgroupOf W₀ := by
    rintro y ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hval : ((φ w : ↥W₀) : G) = ⁅(w : G), x⁆ := by
      show (w : G) * (x * (w : G) * x⁻¹) = ⁅(w : G), x⁆
      rw [commutatorElement_def]
      rw [inv_eq_of_mul_eq_one_right (hWsq w w.2)]
      group
    rw [hval]
    have hmem := Subgroup.commutator_mem_commutator w.2 hxP
    have hsub := commutator_W0_Pc_le h hPH hVH hW₀ hN hmem
    rw [hA]
    exact hsub
  have hA_le_W₀ : A ≤ W₀ := by
    rw [hA]
    exact inf_le_right
  have hcardA : Nat.card ↥(A.subgroupOf W₀) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_W₀).toEquiv
  exact Subgroup.eq_of_le_of_card_ge (H := φ.range) (K := A.subgroupOf W₀) hrange_le_A
    (by rw [hcardA]; exact hcardRange)

private theorem twistMap_range_le_centralizer
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) {A : Subgroup G}
    (hA : A = Pc M V ⊓ W₀) {x : G}
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hxH : x ∈ H)
    (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (hx2 : x * x ∈ kOf V H)
    (hrange : (twistMap hWcomm x (hN hxH)).range = A.subgroupOf W₀) :
    A ≤ W₀ ⊓ Subgroup.centralizer ({x} : Set G) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (W₀ : Set G) := hN hxH
  let φ : ↥W₀ →* ↥W₀ := twistMap hWcomm x hxN
  have hrange_le_C : φ.range ≤
      (W₀ ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf W₀ := by
    rintro y ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hφval : ((φ w : ↥W₀) : G) = (w : G) * (x * (w : G) * x⁻¹) := rfl
    have hxw : x * (w : G) * x⁻¹ ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp hxN (w : G)).mp w.2
    have hx2c : ∀ z ∈ W₀, (x * x) * z = z * (x * x) := by
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hx2).2 z (hW₀ hz)).symm
    have hfix : x * ((φ w : ↥W₀) : G) * x⁻¹ = ((φ w : ↥W₀) : G) := by
      rw [hφval]
      calc x * ((w : G) * (x * (w : G) * x⁻¹)) * x⁻¹
          = (x * (w : G) * x⁻¹) * (x * (x * (w : G) * x⁻¹) * x⁻¹) := by group
        _ = (x * (w : G) * x⁻¹) * (w : G) := by
            congr 1
            calc x * (x * (w : G) * x⁻¹) * x⁻¹ = (x * x) * (w : G) * (x * x)⁻¹ := by group
              _ = (w : G) := by rw [hx2c (w : G) w.2]; group
        _ = (w : G) * (x * (w : G) * x⁻¹) := (hWcomm (w : G) w.2 _ hxw).symm
    refine Subgroup.mem_inf.mpr ⟨(φ w).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := congrArg (fun z => z * x) hfix
    simpa [mul_assoc] using h.symm
  have hA_le_W₀ : A ≤ W₀ := by
    rw [hA]
    exact inf_le_right
  intro a ha
  have hmemA : (⟨a, hA_le_W₀ ha⟩ : ↥W₀) ∈ A.subgroupOf W₀ :=
    Subgroup.mem_subgroupOf.mpr ha
  rw [← hrange] at hmemA
  obtain ⟨w, hwval⟩ := hmemA
  refine Subgroup.mem_inf.mpr ⟨hA_le_W₀ ha, ?_⟩
  have hC := hrange_le_C ⟨w, rfl⟩
  have hcent := Subgroup.mem_subgroupOf.mp hC
  have hval : ((φ w : ↥W₀) : G) = a := congrArg Subtype.val hwval
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hcent.2
  simpa only [hval] using hcomm

private theorem le_inf_centralizer_of_twistMap (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {A : Subgroup G}
    (hA : A = Pc M V ⊓ W₀) {x : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V)
    (hx2 : x * x ∈ kOf V H)
    (hcard : Nat.card W₀ = Nat.card A ^ 2)
    (hker : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card A) :
    A ≤ W₀ ⊓ Subgroup.centralizer ({x} : Set G) := by
  classical
  have hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u :=
    fun u hu v hv => commute_of_le_xOf h hPH hVH hW₀ hu hv
  have hWsq : ∀ u ∈ W₀, u * u = 1 := by
    intro u hu
    have h2 := (isElemAbelian_xOf h hPH hVH).2 u (hW₀ hu)
    rwa [pow_two] at h2
  have hrange := twistMap_range_eq h hPH hVH hW₀ hN hA hxH hxP hWcomm hWsq hcard hker
  exact twistMap_range_le_centralizer hW₀ hA hN hxH hWcomm hx2 hrange

private theorem card_inf_centralizer_le_of_mem_Pc_not_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {A : Subgroup G}
    {t : G} (htH : t ∈ H) (htK : t ∉ kOf V H) (ht2 : t * t ∈ kOf V H)
    (hcardCt : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card A)
    {x : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card A := by
  classical
  have hLbar : IsL2OrSzGroup (HBar V H) := hL
  have hxbar_mem : piK V H ⟨x, hxH⟩ ∈ imgK V H (Pc M V) :=
    (mem_imgK_iff).mpr ⟨⟨x, hxH⟩, hxP, rfl⟩
  have hxbar_sq : piK V H ⟨x, hxH⟩ * piK V H ⟨x, hxH⟩ = 1 := by
    have h := (isElemAbelian_imgK h hPH hVH).2 (piK V H ⟨x, hxH⟩) hxbar_mem
    simpa [pow_two] using h
  have htbar_sq : piK V H ⟨t, htH⟩ * piK V H ⟨t, htH⟩ = 1 := by
    have h1 : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = ⟨t * t, H.mul_mem htH htH⟩ := Subtype.ext rfl
    rw [← map_mul, h1]
    exact (piK_eq_one_iff _).mpr ht2
  have hxbar_ne : piK V H ⟨x, hxH⟩ ≠ 1 := fun h1 =>
    hxK ((piK_eq_one_iff (V := V) (H := H) ⟨x, hxH⟩).mp h1)
  have htbar_ne : piK V H ⟨t, htH⟩ ≠ 1 := fun h1 =>
    htK ((piK_eq_one_iff (V := V) (H := H) ⟨t, htH⟩).mp h1)
  obtain ⟨c, hc⟩ := IsL2OrSzGroup.isConj_of_sq_eq_one hLbar hxbar_sq hxbar_ne
    htbar_sq htbar_ne
  obtain ⟨gH, hgpi⟩ := piK_surjective V H c
  set g : G := (gH : G) with hg
  have hgH : g ∈ H := gH.2
  have hgInvH : g⁻¹ ∈ H := H.inv_mem hgH
  have hgpi' : piK V H ⟨g, hgH⟩ = (↑c : HBar V H) := hgpi
  have hginv_pi : piK V H ⟨g⁻¹, hgInvH⟩ = (↑c : HBar V H)⁻¹ := by
    have h1 : (⟨g⁻¹, hgInvH⟩ : ↥H) = (⟨g, hgH⟩ : ↥H)⁻¹ := Subtype.ext rfl
    rw [h1, map_inv, hgpi']
  set y : G := g⁻¹ * t * g with hy
  have hyH : y ∈ H := H.mul_mem (H.mul_mem hgInvH htH) hgH
  have hypi : piK V H ⟨y, hyH⟩ = piK V H ⟨x, hxH⟩ := by
    have h1 : (⟨y, hyH⟩ : ↥H) = ⟨g⁻¹, hgInvH⟩ * ⟨t, htH⟩ * ⟨g, hgH⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, hginv_pi, hgpi']
    have hc' : (↑c : HBar V H) * piK V H ⟨x, hxH⟩ * (↑c)⁻¹ =
        piK V H ⟨t, htH⟩ := by
      rw [hc]
      group
    calc (↑c)⁻¹ * piK V H ⟨t, htH⟩ * ↑c
        = (↑c)⁻¹ * ((↑c) * piK V H ⟨x, hxH⟩ * (↑c)⁻¹) * ↑c := by rw [hc']
      _ = piK V H ⟨x, hxH⟩ := by simp [mul_assoc]
  have hk : y⁻¹ * x ∈ kOf V H := by
    refine (piK_eq_one_iff (V := V) (H := H)
      ⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩).mp ?_
    have h1 : (⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩ : ↥H) =
        (⟨y, hyH⟩ : ↥H)⁻¹ * ⟨x, hxH⟩ := Subtype.ext rfl
    rw [h1, map_mul, map_inv, hypi]
    simp
  have hxy : x = y * (y⁻¹ * x) := by group
  have hcardCx : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [inf_centralizer_mul_kOf_eq (hW₀ := hW₀) hk hxy]
  have hconj := inf_centralizer_conj_eq_conj (W₀ := W₀) hN (g := g⁻¹) (t := t) hgInvH
  have hcardY : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have h1 : g⁻¹ * t * (g⁻¹)⁻¹ = y := by rw [inv_inv]
    rw [h1] at hconj
    rw [hconj]
    exact card_conjSubgroup g⁻¹ (W₀ ⊓ Subgroup.centralizer ({t} : Set G))
  rw [hcardCx, hcardY]
  exact hcardCt


private theorem sq_mem_kOf_of_mem_Pc (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {x : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V) :
    x * x ∈ kOf V H := by
  have hmem : piK V H ⟨x, hxH⟩ ∈ imgK V H (Pc M V) :=
    (mem_imgK_iff).mpr ⟨⟨x, hxH⟩, hxP, rfl⟩
  have hsq : piK V H ⟨x, hxH⟩ * piK V H ⟨x, hxH⟩ = 1 := by
    have h := (isElemAbelian_imgK h hPH hVH).2 (piK V H ⟨x, hxH⟩) hmem
    simpa [pow_two] using h
  refine (piK_eq_one_iff (V := V) (H := H) ⟨x * x, H.mul_mem hxH hxH⟩).mp ?_
  have h1 : (⟨x * x, H.mul_mem hxH hxH⟩ : ↥H) = ⟨x, hxH⟩ * ⟨x, hxH⟩ := Subtype.ext rfl
  rw [h1, map_mul]
  exact hsq

private theorem inf_Pc_conj_Pc_inf_W0_setup
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hbot : Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ = ⊥) :
    ∃ A : Subgroup G, ∃ t : G,
      A = Pc M V ⊓ W₀ ∧ Nat.card W₀ = Nat.card A ^ 2 ∧
      t ∈ H ∧ t ∉ kOf V H ∧ t * t ∈ kOf V H ∧
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card A := by
  classical
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  set B : Subgroup G := conjSubgroup h₀ (Pc M V) ⊓ W₀ with hB
  have hAB : A ⊓ B = ⊥ := by
    rw [hA, hB]
    rw [show Pc M V ⊓ W₀ ⊓ (conjSubgroup h₀ (Pc M V) ⊓ W₀) =
        Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ from by ac_rfl]
    exact hbot
  have hWsup : W₀ = A ⊔ B := by
    rw [hA, hB]
    exact eq_sup_inf_of_minimal h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact commute_of_le_xOf h hPH hVH hW₀ (hWsup ▸ (le_sup_left : A ≤ A ⊔ B) ha)
      (hWsup ▸ (le_sup_right : B ≤ A ⊔ B) hb)
  have hcardW : Nat.card W₀ = Nat.card A ^ 2 := by
    have hprod := card_W0_mul_card_Pc_inf_conj_inf_W0 h hPH hVH hH hnM hW₀ hN hW₀ne hmin
    have hAB' : Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ = A ⊓ B := by
      rw [hA, hB]
      ac_rfl
    rw [hAB', hAB, Subgroup.card_bot, mul_one] at hprod
    exact hprod
  obtain ⟨t, htH, htK, ht2, htP, htP'⟩ := exists_swap_of_isL2OrSz h hPH hVH hH hnM hL
  have htA : conjSubgroup t A = B := by
    rw [hA, hB, CFSG.RankThree.GF2n.conjSubgroup_inf, htP,
      conjSubgroup_eq_self_iff.mpr (hN htH)]
  have htB : conjSubgroup t B = A := by
    rw [hA, hB, CFSG.RankThree.GF2n.conjSubgroup_inf, htP',
      conjSubgroup_eq_self_iff.mpr (hN htH)]
  have hcardCt : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card A :=
    card_inf_centralizer_le_of_swap (X := G) hWsup hAB hcomm htA htB
  exact ⟨A, t, hA, hcardW, htH, htK, ht2, hcardCt⟩

private theorem inf_Pc_conj_Pc_inf_W0_false
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {A : Subgroup G} {t : G} (hA : A = Pc M V ⊓ W₀)
    (hcardW : Nat.card W₀ = Nat.card A ^ 2)
    (htH : t ∈ H) (htK : t ∉ kOf V H) (ht2 : t * t ∈ kOf V H)
    (hcardCt : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card A) :
    False := by
  classical
  have hA_le_W₀ : A ≤ W₀ := by
    rw [hA]
    exact inf_le_right
  have hA_le_C : ∀ x ∈ Pc M V, A ≤ W₀ ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro x hxP
    by_cases hxK : x ∈ kOf V H
    · have hWle : W₀ ≤ Subgroup.centralizer ({x} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hxK).2 w (hW₀ hw)
      exact le_inf hA_le_W₀ (hA_le_W₀.trans hWle)
    · have hxH : x ∈ H := hPH hxP
      have hx2 : x * x ∈ kOf V H := sq_mem_kOf_of_mem_Pc h hPH hVH hxH hxP
      have hker := card_inf_centralizer_le_of_mem_Pc_not_kOf h hPH hVH hL hW₀ hN
        htH htK ht2 hcardCt hxH hxP hxK
      exact le_inf_centralizer_of_twistMap h hPH hVH hW₀ hN hA hxH hxP hx2 hcardW hker
  have hA_le_CP : A ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := (hA_le_C x hx).trans inf_le_right
    exact Subgroup.mem_centralizer_singleton_iff.mp (h ha)
  have hA_eq_V : A = V ⊓ W₀ := by
    rw [hA]
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : x ∈ W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) :=
        ⟨hx.2, hA_le_CP (hA.symm ▸ hx)⟩
      rwa [inf_centralizer_Pc_eq_inf (h := h)] at hx'
    · exact le_inf (inf_le_left.trans h.toHyp.le_Pc) inf_le_right
  have hA_ne : A ≠ ⊥ := by
    intro hAz
    apply hW₀ne
    have h1 : Nat.card W₀ = 1 := by rw [hcardW, hAz]; simp
    exact Subgroup.card_eq_one.mp h1
  have hA_gt1 : 1 < Nat.card ↥(V ⊓ W₀) := by
    rw [← hA_eq_V]
    by_contra hcon
    have h1 : Nat.card A = 1 := by
      have := Nat.card_pos (α := ↥A)
      omega
    exact hA_ne (Subgroup.card_eq_one.mp h1)
  have hlt : Nat.card W₀ < Nat.card ↥(V ⊓ W₀) ^ 4 := by
    rw [hcardW, hA_eq_V]
    exact Nat.pow_lt_pow_right hA_gt1 (by norm_num)
  exact false_of_card_lt_fixedSub (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin hlt

theorem inf_Pc_conj_Pc_inf_W0_ne_bot
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ ≠ ⊥ := by
  classical
  intro hbot
  obtain ⟨A, t, hA, hcardW, htH, htK, ht2, hcardCt⟩ :=
    inf_Pc_conj_Pc_inf_W0_setup h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin hbot
  exact inf_Pc_conj_Pc_inf_W0_false h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin hA hcardW
    htH htK ht2 hcardCt

theorem card_W0_lt_card_Pc_sq
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card W₀ < Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := by
  have hne := inf_Pc_conj_Pc_inf_W0_ne_bot (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin
  have hgt : 1 < Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
    by_contra hcon
    have hpos := Nat.card_pos (α := ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    have h1 : Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) = 1 := by omega
    exact hne (Subgroup.card_eq_one.mp h1)
  have hprod := card_W0_mul_card_Pc_inf_conj_inf_W0 h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  calc Nat.card W₀ < Nat.card W₀ *
        Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) :=
        lt_mul_of_one_lt_right (Nat.card_pos (α := ↥W₀)) hgt
    _ = Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := hprod

theorem card_W0_lt_card_imgK_pow_four
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card W₀ < Nat.card (imgK V H (Pc M V)) ^ 4 := by
  have h1 := card_W0_lt_card_Pc_sq (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin
  have h2 := card_inf_W0_le h hPH hVH hH hnM hK hab hL hW₀
  have h3 := card_inf_V_W0_le (hW := hW) h hPH hVH hH hnM hK hab hL hW₀ hN hW₀ne hmin
  calc Nat.card W₀ < Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := h1
    _ ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀)) ^ 2 :=
        Nat.pow_le_pow_left h2 2
    _ ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card (imgK V H (Pc M V))) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h3) 2
    _ = Nat.card (imgK V H (Pc M V)) ^ 4 := by ring


theorem isEmpty_hBar_equiv_suzuki
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (a : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ (2 * a + 1)) :
    IsEmpty (HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) := by
  refine ⟨fun ψ => ?_⟩
  set ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a F) (subW hW W₀) :=
    subRepW hW ψ hW₀ hN
  haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
  have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
  have hK' : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  rcases Sec2.isSzNatural_or_le_card hK' ρ hnt with hnat | hbig
  · exact not_isSzNatural_subRepW h hPH hVH hH hnM hcard ψ hW₀ hN hW₀ne hnat
  · have hlt := card_W0_lt_card_imgK_pow_four (hW := hW) h hPH hVH hH hnM hK hab hL
      hW₀ hN hW₀ne hmin
    have hPbar0 := (imgK_map_sz h hPH hVH hH hnM hcard ψ).1
    have hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * a + 1) := by
      rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hPbar0]
    have hlt' : Nat.card W₀ < 2 ^ (4 * (2 * a + 1)) := by
      rw [hPbar] at hlt
      rwa [show (2 ^ (2 * a + 1)) ^ 4 = 2 ^ (4 * (2 * a + 1)) by
        rw [← pow_mul]; congr 1; ring] at hlt
    have hexp : 4 * (2 * a + 1) < 16 * (2 * a + 1) := by nlinarith
    have hpow : 2 ^ (4 * (2 * a + 1)) < 2 ^ (16 * (2 * a + 1)) :=
      Nat.pow_lt_pow_right (by norm_num) hexp
    have hbig' : 2 ^ (16 * (2 * a + 1)) ≤ Nat.card ↥(subW hW W₀) := by
      simpa only [natCard_subW hW hW₀] using hbig
    have hlt'' : Nat.card ↥(subW hW W₀) < 2 ^ (4 * (2 * a + 1)) := by
      simpa only [natCard_subW hW hW₀] using hlt'
    exact (lt_asymm hpow) (lt_of_le_of_lt hbig' hlt'')


theorem exists_isOrthModule_subRepW
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    ∃ (l : ℕ) (hl : Fintype.card F = 2 ^ (2 * l)),
      Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN) := by
  classical
  set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
  haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
  have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
  obtain ⟨n, -, hFn⟩ := FiniteField.card F 2
  have hn : 1 ≤ (n : ℕ) := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hFn]; omega)
  obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (n : ℕ) := by
    rw [hAcard, hFn]
  have hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (n : ℕ) := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hAcard, hFn]
  have hlt := card_W0_lt_card_imgK_pow_four (hW := hW) h hPH hVH hH hnM hK hab hL
    hW₀ hN hW₀ne hmin
  have hlt' : Nat.card ↥(subW hW W₀) < 2 ^ (4 * (n : ℕ)) := by
    rw [hPbar] at hlt
    have h1 : Nat.card ↥(subW hW W₀) = Nat.card W₀ := natCard_subW hW hW₀
    rw [h1]
    rwa [show (2 ^ (n : ℕ)) ^ 4 = 2 ^ (4 * (n : ℕ)) by rw [← pow_mul]; ring] at hlt
  rcases Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt hn hFn ρ hnt
    ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard' hlt' with hnat | horth | hthird
  · exact absurd hnat (not_isNaturalModule_subRepW h hPH hVH hH hnM ψ hW₀ hN hW₀ne)
  · obtain ⟨l, hl, -, hρ⟩ := horth
    exact ⟨l, hl, hρ⟩
  · obtain ⟨l, hn3, hWcard, hfixcard⟩ := hthird
    have hfixeq : Nat.card (fixedSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)) =
        Nat.card ↥(V ⊓ W₀) := by
      rw [MulEquiv.toMonoidHom_eq_coe ψ,
        natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
        inf_centralizer_Pc_eq_inf (h := h)]
    have hVcard : Nat.card ↥(V ⊓ W₀) = 2 ^ l := hfixeq.symm.trans hfixcard
    have hstrict : Nat.card W₀ <
        Nat.card (imgK V H (Pc M V)) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := by
      calc Nat.card W₀ < Nat.card ↥(Pc M V ⊓ W₀) ^ 2 :=
            card_W0_lt_card_Pc_sq (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin
        _ ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card ↥(V ⊓ W₀)) ^ 2 :=
            Nat.pow_le_pow_left (card_inf_W0_le h hPH hVH hH hnM hK hab hL hW₀) 2
        _ = Nat.card (imgK V H (Pc M V)) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := by ring
    have hstrict' : Nat.card W₀ < 2 ^ (8 * l) := by
      rw [hPbar, hn3, hVcard] at hstrict
      rwa [show (2 ^ (3 * l)) ^ 2 * (2 ^ l) ^ 2 = 2 ^ (8 * l) by
        rw [← pow_mul, ← pow_mul]; ring_nf] at hstrict
    have hWcard' : Nat.card W₀ = 2 ^ (8 * l) := by
      simpa only [natCard_subW hW hW₀] using hWcard
    rw [hWcard'] at hstrict'
    exact absurd hstrict' (not_lt.mpr (le_refl _))


theorem exists_field_orth_of_kOf_abelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (l : ℕ),
      1 ≤ l ∧ ∃ hl : Fintype.card F = 2 ^ (2 * l), ∃ ψ : HBar V H ≃* SL(2, F),
        Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN) := by
  classical
  have hL' := hL
  rcases hL with ⟨F, hField, hFintype, hCharP, h4, ⟨ψ⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, ha, hcard, ⟨ψ⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    obtain ⟨l, hl, horth⟩ := exists_isOrthModule_subRepW (hW := hW) h hPH hVH hH hnM
      hK hab hL' ψ hW₀ hN hW₀ne hmin
    have hl1 : 1 ≤ l := by
      have h2 : 2 ^ 1 ≤ 2 ^ (2 * l) := by rw [← hl]; omega
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
      omega
    exact ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, horth⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    exact (isEmpty_hBar_equiv_suzuki (hW := hW) h hPH hVH hH hnM hK hab hL' hW₀ hN hW₀ne
      hmin a F hcard).elim ψ

end RootHyp

end CFSG.RankThree.GF2n.Tim81
