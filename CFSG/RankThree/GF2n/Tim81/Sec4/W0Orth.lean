module

public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Bound
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelAbstract

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Quasithin.B45L2 CFSG.Quasithin.JonesParshall
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.GroupTheory
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}
variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]

theorem card_W0_eq_pow_of_isOrthModule {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Nat.card W₀ = 2 ^ (4 * l) := by
  obtain ⟨j, β, -⟩ := horth
  have h1 : Nat.card ↥(subW hW W₀) = Nat.card ↥W₀ := natCard_subW hW hW₀
  calc Nat.card W₀ = Nat.card ↥(subW hW W₀) := h1.symm
    _ = Nat.card ↥(hermA l F) := Nat.card_congr β.toEquiv
    _ = 2 ^ (4 * l) := card_hermA (one_le_of_card hl) hl

namespace RootHyp

theorem card_inf_V_W0_eq_pow_of_isOrthModule (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Nat.card ↥(V ⊓ W₀) = 2 ^ l := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * l) := by
    rw [hAcard, hl]
  set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
  have hfix := IsOrthModule.card_fixedSub (hF := hl) horth
    ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard'
  have hfixeq : Nat.card (fixedSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)) =
      Nat.card ↥(V ⊓ W₀) := by
    rw [MulEquiv.toMonoidHom_eq_coe ψ,
      natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
      inf_centralizer_Pc_eq_inf (h := h)]
  exact hfixeq.symm.trans hfix

theorem card_commutator_W0_Pc_eq_pow_of_isOrthModule (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Nat.card ↥⁅W₀, Pc M V⁆ = 2 ^ (3 * l) := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * l) := by
    rw [hAcard, hl]
  set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
  have hcomm := IsOrthModule.card_commSub (hF := hl) horth
    ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard'
  have hEW : ⁅W₀, Pc M V⁆ ≤ Tim79a.xOf V H :=
    (commutator_W0_Pc_le h hPH hVH hW₀ hN).trans (inf_le_right.trans hW₀)
  have hmap : (commSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)).map
      (subW hW W₀).subtype = subW hW ⁅W₀, Pc M V⁆ := by
    rw [MulEquiv.toMonoidHom_eq_coe ψ]
    exact commSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH
  have hcard : Nat.card (commSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)) =
      Nat.card ↥(subW hW ⁅W₀, Pc M V⁆) := by
    rw [Nat.card_congr (Submodule.equivMapOfInjective (subW hW W₀).subtype
      (Submodule.subtype_injective (subW hW W₀))
      (commSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom))).toEquiv, hmap]
  exact (natCard_subW hW hEW).symm.trans (hcard.symm.trans hcomm)

theorem card_imgK_eq_two_pow (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * l) := by
  obtain ⟨-, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hAcard, hl]

theorem inf_Pc_W0_eq_commutator_of_isOrthModule (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Pc M V ⊓ W₀ = ⁅W₀, Pc M V⁆ := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hS : conjSubgroup h₀ (Pc M V) ≤ H := by
    rw [hH]
    exact le_sup_right
  have hWcard := card_W0_eq_pow_of_isOrthModule (hW := hW) ψ hl hW₀ hN horth
  have hcommcard := card_commutator_W0_Pc_eq_pow_of_isOrthModule (hW := hW)
    h hPH hVH hH hnM ψ hl hW₀ hN horth
  have hVcard := card_inf_V_W0_eq_pow_of_isOrthModule (hW := hW)
    h hPH hVH hH hnM ψ hl hW₀ hN horth
  obtain ⟨-, -, a, b, -, hb, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hA2h : ∀ x ∈ (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom,
      x * x = 1 := by
    intro x hx
    rw [hb] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have huu : u * u = 1 := by
      simpa [pow_two] using (isElemAbelian_utri (F := F)).2 u hu
    calc (MulAut.conj b) u * (MulAut.conj b) u = MulAut.conj b (u * u) := (map_mul _ _ _).symm
      _ = MulAut.conj b 1 := by rw [huu]
      _ = 1 := map_one _
  have hAcardh : Nat.card ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom) =
      2 ^ (2 * l) := by
    rw [hb, card_conjSubgroup, card_utri, Nat.card_eq_fintype_card, hl]
  set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
  have hfixh := IsOrthModule.card_fixedSub (hF := hl) horth
    ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom) hA2h hAcardh
  have hfixeqh : Nat.card (fixedSub ρ
      ((imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom)) =
      Nat.card ↥(conjSubgroup h₀ V ⊓ W₀) := by
    rw [MulEquiv.toMonoidHom_eq_coe ψ,
      natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN
        (S := conjSubgroup h₀ (Pc M V)) hS,
      inf_centralizer_conj_Pc_eq_inf (h := h)]
  have hVhcard : Nat.card ↥(conjSubgroup h₀ V ⊓ W₀) = 2 ^ l :=
    hfixeqh.symm.trans hfixh
  have hAinfVh : (Pc M V ⊓ W₀) ⊓ (conjSubgroup h₀ V ⊓ W₀) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxPVh : x ∈ Pc M V ⊓ conjSubgroup h₀ V := ⟨hx.1.1, hx.2.1⟩
    rw [inf_comm, conjSubgroup_inf_Pc_eq_bot h hH hnM] at hxPVh
    exact hxPVh
  have hprod : Nat.card ↥(Pc M V ⊓ W₀) * Nat.card ↥(conjSubgroup h₀ V ⊓ W₀) ≤
      Nat.card W₀ :=
    card_mul_card_le_of_inf_eq_bot (A := W₀) inf_le_right inf_le_right hAinfVh
  have hcardA_le : Nat.card ↥(Pc M V ⊓ W₀) ≤ 2 ^ (3 * l) := by
    rw [hVhcard, hWcard] at hprod
    rw [show 2 ^ (4 * l) = 2 ^ (3 * l) * 2 ^ l by rw [← pow_add]; ring_nf] at hprod
    exact Nat.le_of_mul_le_mul_right hprod (pow_pos (by norm_num) l)
  have hle : ⁅W₀, Pc M V⁆ ≤ Pc M V ⊓ W₀ :=
    commutator_W0_Pc_le h hPH hVH hW₀ hN
  exact (Subgroup.eq_of_le_of_card_ge (H := ⁅W₀, Pc M V⁆) (K := Pc M V ⊓ W₀) hle
    (by rw [hcommcard]; exact hcardA_le)).symm

theorem card_inf_Pc_W0_eq_pow_of_isOrthModule (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Nat.card ↥(Pc M V ⊓ W₀) = 2 ^ (3 * l) := by
  rw [inf_Pc_W0_eq_commutator_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth]
  exact card_commutator_W0_Pc_eq_pow_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth

theorem inf_Pc_kOf_eq_sup_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Pc M V ⊓ kOf V H = (Pc M V ⊓ W₀) ⊔ V := by
  have hPbar := card_imgK_eq_two_pow h hPH hVH hH hnM ψ hl
  have hAcard : Nat.card ↥(Pc M V ⊓ W₀) = 2 ^ (3 * l) :=
    card_inf_Pc_W0_eq_pow_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth
  have hVcard := card_inf_V_W0_eq_pow_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth
  have hgen := card_Pc_inf_W0_mul_card_V_le h hPH hVH hW₀
  have hbound := card_Pc_inf_kOf_le_of_isL2OrSz h hPH hVH hH hnM hK hab hL
  have hle : Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) ≤
      Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V := by
    calc Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀)
        ≤ (Nat.card (imgK V H (Pc M V)) * Nat.card V) * Nat.card ↥(V ⊓ W₀) :=
          Nat.mul_le_mul_right _ hbound
      _ = 2 ^ (2 * l) * 2 ^ l * Nat.card V := by rw [hPbar, hVcard]; ring
      _ = 2 ^ (3 * l) * Nat.card V := by
          rw [← pow_add, show 2 * l + l = 3 * l by ring]
      _ = Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V := by rw [hAcard]
  exact (card_Pc_inf_W0_mul_card_V_eq_iff h hPH hVH hW₀).mp (le_antisymm hgen hle)

theorem conj_Pc_inf_kOf_eq_sup_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    conjSubgroup h₀ (Pc M V) ⊓ kOf V H =
      (conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊔ conjSubgroup h₀ V := by
  have hmain := inf_Pc_kOf_eq_sup_of_isOrthModule h hPH hVH hH hnM hK hab hL
    ψ hl hW₀ hN horth
  obtain ⟨y, hyH, hPy, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hKconj : conjSubgroup y (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hyH)
  have hWconj : conjSubgroup y W₀ = W₀ :=
    conjSubgroup_eq_self_iff.mpr (hN hyH)
  have hconj := congrArg (conjSubgroup y) hmain
  have h1 : conjSubgroup y (Pc M V ⊓ kOf V H) =
      conjSubgroup y (Pc M V) ⊓ kOf V H := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_inf y (Pc M V) (kOf V H), hKconj]
  have h2 : conjSubgroup y ((Pc M V ⊓ W₀) ⊔ V) =
      (conjSubgroup y (Pc M V) ⊓ W₀) ⊔ conjSubgroup y V := by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_sup y (Pc M V ⊓ W₀) V,
      CFSG.RankThree.GF2n.conjSubgroup_inf y (Pc M V) W₀, hWconj]
  rw [h1, h2, ← hPy, ← hVy] at hconj
  exact hconj

theorem kOf_eq_sup_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    kOf V H = W₀ ⊔ V ⊔ conjSubgroup h₀ V := by
  have hPQK := inf_Pc_kOf_eq_sup_of_isOrthModule h hPH hVH hH hnM hK hab hL
    ψ hl hW₀ hN horth
  have hPhQK := conj_Pc_inf_kOf_eq_sup_of_isOrthModule h hPH hVH hH hnM hK hab hL
    ψ hl hW₀ hN horth
  have hWsup := eq_sup_inf_of_minimal h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  calc kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := hK
    _ = ((Pc M V ⊓ W₀) ⊔ V) ⊔ ((conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊔ conjSubgroup h₀ V) := by
        rw [hPQK, hPhQK]
    _ = ((Pc M V ⊓ W₀) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ W₀)) ⊔ V ⊔ conjSubgroup h₀ V := by
        ac_rfl
    _ = W₀ ⊔ V ⊔ conjSubgroup h₀ V := by rw [← hWsup]

theorem exists_orth_of_kOf_abelian
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
        Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN) ∧
        Nat.card W₀ = 2 ^ (4 * l) ∧
        Nat.card ↥(V ⊓ W₀) = 2 ^ l ∧
        Pc M V ⊓ W₀ = ⁅W₀, Pc M V⁆ ∧
        Pc M V ⊓ kOf V H = (Pc M V ⊓ W₀) ⊔ V ∧
        kOf V H = W₀ ⊔ V ⊔ conjSubgroup h₀ V := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, horth⟩ :=
    exists_field_orth_of_kOf_abelian (hW := hW) h hPH hVH hH hnM hK hab hL
      hW₀ hN hW₀ne hmin
  letI := hField
  letI := hFintype
  letI := hCharP
  exact ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, horth,
    card_W0_eq_pow_of_isOrthModule (hW := hW) ψ hl hW₀ hN horth,
    card_inf_V_W0_eq_pow_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth,
    inf_Pc_W0_eq_commutator_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth,
    inf_Pc_kOf_eq_sup_of_isOrthModule h hPH hVH hH hnM hK hab hL ψ hl hW₀ hN horth,
    kOf_eq_sup_of_isOrthModule h hPH hVH hH hnM hK hab hL ψ hl hW₀ hN hW₀ne hmin horth⟩

end RootHyp

end CFSG.RankThree.GF2n.Tim81
