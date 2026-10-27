module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbGamma
public import CFSG.RankThree.GF2n.Tim81.Sec2.Transfer
public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Facts
public import CFSG.GroupTheory.CommutatorMemSubgroup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.RankThree.GF2n.Tim81.Sec4
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.C5
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem inf_centralizer_eq_bot (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxW : x ∈ Tim79a.xOf V H := hx.1
  have hxCH : x ∈ Subgroup.centralizer (H : Set G) := hx.2
  have hxP : x ∈ Subgroup.centralizer (Pc M V : Set G) :=
    Subgroup.centralizer_le (show Pc M V ≤ H from hPH) hxCH
  have hxPh : x ∈ Subgroup.centralizer (conjSubgroup h₀ (Pc M V) : Set G) :=
    Subgroup.centralizer_le (show conjSubgroup h₀ (Pc M V) ≤ H from by
      rw [hH]; exact le_sup_right) hxCH
  have hxV : x ∈ V := by
    rw [← RootHyp.xOf_inf_centralizer_Pc_eq_V h]
    exact Subgroup.mem_inf.mpr ⟨hxW, hxP⟩
  have hxVh : x ∈ conjSubgroup h₀ V := by
    rw [← Hyp.centralizer_conj_Pc h.toHyp h₀]
    exact hxPh
  have hxbot : x ∈ conjSubgroup h₀ V ⊓ Pc M V :=
    Subgroup.mem_inf.mpr ⟨hxVh, h.toHyp.le_Pc hxV⟩
  rw [RootHyp.conjSubgroup_inf_Pc_eq_bot h hH hnM] at hxbot
  exact hxbot

private theorem inf_sup_eq_left_of_le_of_comm {A B C : Subgroup G}
    (hA : A ≤ C) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hbot : B ⊓ C = ⊥) :
    C ⊓ (A ⊔ B) = A := by
  refine le_antisymm ?_ (le_inf hA le_sup_left)
  intro x hx
  obtain ⟨a, ha, b, hb, hxab⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx.2
  have hbC : b ∈ C := by
    have h1 : a⁻¹ * x ∈ C := C.mul_mem (C.inv_mem (hA ha)) hx.1
    have h2 : a⁻¹ * x = b := by rw [← hxab, ← mul_assoc, inv_mul_cancel, one_mul]
    rwa [h2] at h1
  have hb_bot : b ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hb, hbC⟩
  have hb1 : b = 1 := Subgroup.mem_bot.mp hb_bot
  rw [← hxab, hb1, mul_one]
  exact ha

private theorem commutator_H_W0_of_mem_inf_conj
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hKy : KFactorization M V H y)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {d : G} (hd : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V)) :
    ∀ g ∈ H, ⁅g, d⁆ ∈ W₀ := by
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hC6 : ⁅D, Pc M V⁆ ≤ V ⊓ W₀ :=
    RootHyp.commutator_inf_conj_Pc_le h hPH hVH hHy hnM hKy hnab hL hW₀ hN hW₀ne
  have hC6' : ⁅D, conjSubgroup y (Pc M V)⁆ ≤ conjSubgroup y V ⊓ W₀ :=
    RootHyp.commutator_inf_conj_Pc_conj_le h hPH hVH hHy hnM hKy hnab hL hW₀ hN hW₀ne
  have hP_le : Pc M V ≤ CFSG.GroupTheory.commMemSubgroup H W₀ hN d := by
    intro p hp
    refine (CFSG.GroupTheory.mem_commMemSubgroup hN d p).mpr ⟨hPH hp, ?_⟩
    have hcomm : ⁅d, p⁆ ∈ V ⊓ W₀ := hC6 (Subgroup.commutator_mem_commutator hd hp)
    have hinv : ⁅p, d⁆ = ⁅d, p⁆⁻¹ := (commutatorElement_inv d p).symm
    rw [hinv]
    exact W₀.inv_mem hcomm.2
  have hPy_le : conjSubgroup y (Pc M V) ≤ CFSG.GroupTheory.commMemSubgroup H W₀ hN d := by
    intro p hp
    refine (CFSG.GroupTheory.mem_commMemSubgroup hN d p).mpr
      ⟨conjSubgroup_le_of_le_of_mem hPH hyH hp, ?_⟩
    have hcomm : ⁅d, p⁆ ∈ conjSubgroup y V ⊓ W₀ :=
      hC6' (Subgroup.commutator_mem_commutator hd hp)
    have hinv : ⁅p, d⁆ = ⁅d, p⁆⁻¹ := (commutatorElement_inv d p).symm
    rw [hinv]
    exact W₀.inv_mem hcomm.2
  have hH_le : H ≤ CFSG.GroupTheory.commMemSubgroup H W₀ hN d := by
    conv_lhs => rw [hHy]
    exact sup_le hP_le hPy_le
  have hgd : ∀ g ∈ H, ⁅g, d⁆ ∈ W₀ := fun g hg =>
    ((CFSG.GroupTheory.mem_commMemSubgroup hN d g).mp (hH_le hg)).2
  exact hgd

private theorem normalizes_sup_zpowers_W0
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {d : G}
    (hdW : d ∈ Tim79a.xOf V H)
    (hgd : ∀ g ∈ H, ⁅g, d⁆ ∈ W₀) :
    H ≤ Subgroup.normalizer (W₀ ⊔ Subgroup.zpowers d : Subgroup G) ∧
      ∀ g ∈ H, ∀ n ∈ (W₀ ⊔ Subgroup.zpowers d : Subgroup G), ⁅g, n⁆ ∈ W₀ := by
  set N : Subgroup G := W₀ ⊔ Subgroup.zpowers d with hNdef
  have hN_le_W : N ≤ Tim79a.xOf V H := sup_le hW₀ (Subgroup.zpowers_le.mpr hdW)
  have hW_cent_W₀ : Tim79a.xOf V H ≤ Subgroup.centralizer (W₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((isElemAbelian_xOf h hPH hVH).comm hx (hW₀ hz)).symm
  have hW_norm_W₀ : Tim79a.xOf V H ≤ Subgroup.normalizer (W₀ : Set G) :=
    hW_cent_W₀.trans (Subgroup.centralizer_le_normalizer _)
  have hNH : H ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hle : conjSubgroup g N ≤ N := by
      rw [hNdef, conjSubgroup_sup_eq_sup, conjSubgroup_eq_self_iff.mpr (hN hg)]
      refine sup_le le_sup_left ?_
      have hcyc : conjSubgroup g (Subgroup.zpowers d) = Subgroup.zpowers (g * d * g⁻¹) := by
        rw [conjSubgroup]
        exact MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom d
      have hgd_eq : g * d * g⁻¹ = ⁅g, d⁆ * d := by
        rw [commutatorElement_def]
        group
      rw [hcyc, hgd_eq]
      exact Subgroup.zpowers_le.mpr
        (N.mul_mem (Subgroup.mem_sup_left (hgd g hg))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  have hcommNH : ∀ g ∈ H, ∀ n ∈ N, ⁅g, n⁆ ∈ W₀ := by
    intro g hg n hn
    have hN_le_comm : N ≤ CFSG.GroupTheory.commMemSubgroup (Tim79a.xOf V H) W₀ hW_norm_W₀ g := by
      refine sup_le ?_ ?_
      · intro z hz
        refine (CFSG.GroupTheory.mem_commMemSubgroup hW_norm_W₀ g z).mpr ⟨hW₀ hz, ?_⟩
        have hgz : g * z * g⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.mp (hN hg) z).mp hz
        have h1 : ⁅z, g⁆ = z * (g * z * g⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [h1]
        exact W₀.mul_mem hz (W₀.inv_mem hgz)
      · refine Subgroup.zpowers_le.mpr
          ((CFSG.GroupTheory.mem_commMemSubgroup hW_norm_W₀ g d).mpr ⟨hdW, ?_⟩)
        have hgd' : ⁅g, d⁆ ∈ W₀ := hgd g hg
        have hinv : ⁅d, g⁆ = ⁅g, d⁆⁻¹ := (commutatorElement_inv g d).symm
        rw [hinv]
        exact W₀.inv_mem hgd'
    have hng : ⁅n, g⁆ ∈ W₀ :=
      ((CFSG.GroupTheory.mem_commMemSubgroup hW_norm_W₀ g n).mp (hN_le_comm hn)).2
    have hinv : ⁅g, n⁆ = ⁅n, g⁆⁻¹ := (commutatorElement_inv n g).symm
    rw [hinv]
    exact W₀.inv_mem hng
  exact ⟨hNH, hcommNH⟩

private theorem fixedSub_top_subRepW_eq_bot
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {N : Subgroup G}
    (hNW : N ≤ Tim79a.xOf V H)
    (hNH : H ≤ Subgroup.normalizer (N : Set G))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    fixedSub (subRepW hW ψ hNW hNH) ⊤ = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : Representation (ZMod 2) SL(2, F) (subW hW N) := subRepW hW ψ hNW hNH
  have hmap := fixedSub_subRepW hW ψ hNW hNH (S := H) le_rfl
  rw [imgK_self] at hmap
  rw [Subgroup.map_top_of_surjective (ψ : HBar V H →* SL(2, F)) ψ.surjective] at hmap
  have hCW : N ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ Tim79a.xOf V H := hNW hx.1
    have hmem : x ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (H : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxW, hx.2⟩
    rw [RootHyp.inf_centralizer_eq_bot h hPH hH hnM] at hmem
    exact hmem
  rw [hCW, subW_bot] at hmap
  rw [eq_bot_iff]
  intro x hx
  have hmem : (subW hW N).subtype x ∈
      (⊥ : Submodule (ZMod 2)
        (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))) := by
    have h1 : (subW hW N).subtype x ∈ (fixedSub ρ ⊤).map (subW hW N).subtype :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [hmap] at h1
  exact Submodule.subtype_injective (subW hW N) (by simpa using hmem)
private theorem mem_W0_of_mem_sup_zpowers
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hHy : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ N : Subgroup G}
    (hNW : N ≤ Tim79a.xOf V H)
    (hNH : H ≤ Subgroup.normalizer (N : Set G))
    (hcommNH : ∀ g ∈ H, ∀ n ∈ N, ⁅g, n⁆ ∈ W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {v : G} (hv : v ∈ V) (hvN : v ∈ N) :
    v ∈ W₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := Pc M V with hPdef
  set S : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ with hSdef
  have hSodd : Odd S.index := by
    obtain ⟨-, -, a, -, ha, -, -⟩ := imgK_map_sl2 h hPH hVH hHy hnM ψ
    have hS' : S = conjSubgroup a (utri F) := by
      rw [hSdef]
      simpa using ha
    rw [hS']
    exact odd_index_conjSubgroup_utri a
  let ρ : Representation (ZMod 2) SL(2, F) (subW hW N) := subRepW hW ψ hNW hNH
  let N₀ : Submodule (ZMod 2) (subW hW N) := (subW hW W₀).comap (subW hW N).subtype
  have htriv : ∀ g n, ρ g n - n ∈ N₀ := by
    intro g n
    obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm g)
    have hgz : ψ (piK V H z) = g := by rw [hz, ψ.apply_symm_apply]
    have hnW : ((toW hW (n : Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) :
        ↥(Tim79a.xOf V H)) : G) ∈ N := n.2
    have hcomm : ⁅(z : G), ((toW hW (n : Additive
        (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) : ↥(Tim79a.xOf V H)) : G)⁆ ∈ W₀ :=
      hcommNH (z : G) z.2 ((toW hW (n : Additive
        (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) : ↥(Tim79a.xOf V H)) : G) hnW
    have hval : ((ρ g n - n : subW hW N) :
        Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) =
        ofW hW ⟨⁅(z : G), ((toW hW (n : Additive
          (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) : ↥(Tim79a.xOf V H)) : G)⁆,
          mem_commutator_xOf (z := z) (w := toW hW (n : Additive
            (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)))⟩ := by
      rw [← hgz]
      change repW hW ψ (ψ (piK V H z)) (ofW hW (toW hW (n : subW hW N))) -
        ofW hW (toW hW (n : subW hW N)) = _
      rw [repW_apply_piK_sub]
    change ((ρ g n - n : subW hW N) :
      Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) ∈ subW hW W₀
    rw [hval]
    exact (mem_subW_iff hW).mpr hcomm
  have hfix := fixedSub_top_subRepW_eq_bot h hPH hHy hnM hNW hNH ψ
  have hv_cent : v ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp hp.2 v hv).symm
  let vN : subW hW N := ⟨ofW hW ⟨v, hNW hvN⟩, (mem_subW_iff hW).mpr hvN⟩
  have hv_fixed : vN ∈ fixedSub ρ S := by
    have hmap := fixedSub_subRepW hW ψ hNW hNH (S := Pc M V) hPH
    have hmem : (subW hW N).subtype vN ∈ (fixedSub ρ S).map (subW hW N).subtype := by
      rw [hmap]
      exact (mem_subW_iff hW).mpr (Subgroup.mem_inf.mpr ⟨hvN, hv_cent⟩)
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hmem
    have hwv' : w = vN := Submodule.subtype_injective (subW hW N) hwv
    rwa [hwv'] at hw
  have hN₀mem : vN ∈ N₀ :=
    mem_of_odd_index_of_fixedSub_top_eq_bot ρ N₀ htriv hSodd hfix hv_fixed
  have hmem : (subW hW N).subtype vN ∈ subW hW W₀ := hN₀mem
  exact (mem_subW_iff hW).mp hmem



theorem mem_of_mul_mem_W0_of_mem_inf_conj
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hKy : KFactorization M V H y)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {v d : G} (hv : v ∈ V) (hd : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V))
    (hvd : v * d ∈ W₀) :
    v ∈ W₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvW : v ∈ Tim79a.xOf V H := le_xOf_self V H hv
  have hdW : d ∈ Tim79a.xOf V H := by
    have h1 : v⁻¹ * (v * d) ∈ Tim79a.xOf V H :=
      (Tim79a.xOf V H).mul_mem ((Tim79a.xOf V H).inv_mem hvW) (hW₀ hvd)
    simpa [mul_assoc] using h1
  have hgd := commutator_H_W0_of_mem_inf_conj h hPH hVH hyH hHy hnM hKy hnab hL
    hW₀ hN hW₀ne hd
  obtain ⟨hNH, hcommNH⟩ := normalizes_sup_zpowers_W0 h hPH hVH
    hW₀ hN hdW hgd
  have hNW : W₀ ⊔ Subgroup.zpowers d ≤ Tim79a.xOf V H :=
    sup_le hW₀ (Subgroup.zpowers_le.mpr hdW)
  have hvN : v ∈ W₀ ⊔ Subgroup.zpowers d := by
    have h1 : v * d ∈ W₀ ⊔ Subgroup.zpowers d := Subgroup.mem_sup_left hvd
    have hdN : d ∈ W₀ ⊔ Subgroup.zpowers d :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    rw [show v = (v * d) * d⁻¹ by group]
    exact (W₀ ⊔ Subgroup.zpowers d).mul_mem h1 ((W₀ ⊔ Subgroup.zpowers d).inv_mem hdN)
  exact mem_W0_of_mem_sup_zpowers h hPH hVH hHy hnM hNW hNH hcommNH ψ hv hvN

theorem inf_sup_Pc_W0_eq
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    (V ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V))) ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hKy : KFactorization M V H y := by
    rw [KFactorization] at hK ⊢
    rw [← hPy]
    exact hK
  rw [hPy]
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxW : x ∈ W₀ := hx.2
    have hxVD : x ∈ V ⊔ D := hx.1
    have hcomm : ∀ a ∈ V, ∀ b ∈ D, a * b = b * a := by
      intro a ha b hb
      have hbD : b ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by simpa [hD] using hb
      have hbC : b ∈ Subgroup.centralizer (V : Set G) :=
        (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hbD.1
      exact Subgroup.mem_centralizer_iff.mp hbC a ha
    obtain ⟨v, hv, d, hd, hvd⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hxVD
    have hvW₀ : v ∈ W₀ :=
      mem_of_mul_mem_W0_of_mem_inf_conj h hPH hVH hyH hHy hnM hKy hnab hL hW₀ hN hW₀ne ψ
        hv (by simpa [hD] using hd) (hvd ▸ hxW)
    have hdW₀ : d ∈ W₀ := by
      have hd_eq : d = v⁻¹ * x := by rw [← hvd]; group
      rw [hd_eq]
      exact W₀.mul_mem (W₀.inv_mem hvW₀) hxW
    rw [← hvd]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hv, hvW₀⟩)
      (Subgroup.mem_inf.mpr ⟨hd, hdW₀⟩)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

private theorem commute_sup_V_D
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    {D : Subgroup G} (hD : D = Pc M V ⊓ conjSubgroup y (Pc M V)) :
    ∀ a ∈ V ⊔ D, ∀ b ∈ conjSubgroup y V, a * b = b * a := by
  have hV_comm : ∀ v ∈ V, ∀ b ∈ conjSubgroup y V, v * b = b * v := by
    intro v hv b hb
    exact (isElemAbelian_xOf h hPH hVH).comm (le_xOf_self V H hv)
      (conjSubgroup_le_xOf_of_mem hyH hb)
  have hD_comm : ∀ d ∈ D, ∀ b ∈ conjSubgroup y V, d * b = b * d := by
    intro d hd b hb
    have hdD : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by
      rw [hD] at hd
      exact hd
    obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.mp hdD.2
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have hd'C : d' ∈ Subgroup.centralizer (V : Set G) :=
      (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hd'
    have hdb : d' * b' = b' * d' := (Subgroup.mem_centralizer_iff.mp hd'C b' hb').symm
    change y * d' * y⁻¹ * (y * b' * y⁻¹) = y * b' * y⁻¹ * (y * d' * y⁻¹)
    calc y * d' * y⁻¹ * (y * b' * y⁻¹) = y * (d' * b') * y⁻¹ := by group
      _ = y * (b' * d') * y⁻¹ := by rw [hdb]
      _ = y * b' * y⁻¹ * (y * d' * y⁻¹) := by group
  have hvd_comm : ∀ v ∈ V, ∀ d ∈ D, v * d = d * v := by
    intro v hv d hd
    have hdD : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by
      rw [hD] at hd
      exact hd
    have hdC : d ∈ Subgroup.centralizer (V : Set G) :=
      (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hdD.1
    exact Subgroup.mem_centralizer_iff.mp hdC v hv
  intro a ha b hb
  obtain ⟨v, hv, d, hd, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hvd_comm ha
  calc v * d * b = v * (d * b) := by group
    _ = v * (b * d) := by rw [hD_comm d hd b hb]
    _ = (v * b) * d := by group
    _ = (b * v) * d := by rw [hV_comm v hv b hb]
    _ = b * (v * d) := by group

private theorem commute_sup_conj_V_D
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    {D : Subgroup G} (hD : D = Pc M V ⊓ conjSubgroup y (Pc M V)) :
    ∀ a ∈ conjSubgroup y V ⊔ D, ∀ b ∈ V, a * b = b * a := by
  have hV_comm : ∀ v ∈ conjSubgroup y V, ∀ b ∈ V, v * b = b * v := by
    intro v hv b hb
    exact (isElemAbelian_xOf h hPH hVH).comm (conjSubgroup_le_xOf_of_mem hyH hv)
      (le_xOf_self V H hb)
  have hD_comm : ∀ d ∈ D, ∀ b ∈ V, d * b = b * d := by
    intro d hd b hb
    have hdD : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by
      rw [hD] at hd
      exact hd
    have hdC : d ∈ Subgroup.centralizer (V : Set G) :=
      (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hdD.1
    exact (Subgroup.mem_centralizer_iff.mp hdC b hb).symm
  have hV_D_comm : ∀ v ∈ conjSubgroup y V, ∀ d ∈ D, v * d = d * v := by
    intro v hv d hd
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    have hdD : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by
      rw [hD] at hd
      exact hd
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hdD.2
    have hpC : p ∈ Subgroup.centralizer (V : Set G) :=
      (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hp
    have hpv : p * v' = v' * p :=
      (Subgroup.mem_centralizer_iff.mp hpC v' hv').symm
    change y * v' * y⁻¹ * (y * p * y⁻¹) = y * p * y⁻¹ * (y * v' * y⁻¹)
    calc y * v' * y⁻¹ * (y * p * y⁻¹) = y * (v' * p) * y⁻¹ := by group
      _ = y * (p * v') * y⁻¹ := by rw [hpv]
      _ = y * p * y⁻¹ * (y * v' * y⁻¹) := by group
  intro a ha b hb
  obtain ⟨v, hv, d, hd, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hV_D_comm ha
  calc v * d * b = v * (d * b) := by group
    _ = v * (b * d) := by rw [hD_comm d hd b hb]
    _ = (v * b) * d := by group
    _ = (b * v) * d := by rw [hV_comm v hv b hb]
    _ = b * (v * d) := by group

theorem inf_Pc_W0_eq_sup
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hW₀K' : W₀ ≤ ⁅kOf V H, kOf V H⁆)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hKy : KFactorization M V H y := by
    rw [KFactorization] at hK ⊢
    rw [← hPy]
    exact hK
  rw [hPy]
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  refine le_antisymm ?_ ?_
  · intro p hp
    have hpP : p ∈ Pc M V := hp.1
    have hpW : p ∈ W₀ := hp.2
    have hpK' : p ∈ ⁅kOf V H, kOf V H⁆ := hW₀K' hpW
    have hK'_le_R : ⁅kOf V H, kOf V H⁆ ≤ V ⊔ D ⊔ conjSubgroup y V :=
      RootHyp.commutator_kOf_le_sup h hPH hHy hnM hKy
    have hpR : p ∈ V ⊔ D ⊔ conjSubgroup y V := hK'_le_R hpK'
    have hcommVD := commute_sup_V_D (hW := hW) h hPH hVH hyH hD
    have hPR : Pc M V ⊓ (V ⊔ D ⊔ conjSubgroup y V) = V ⊔ D :=
      inf_sup_eq_left_of_le_of_comm (A := V ⊔ D) (B := conjSubgroup y V) (C := Pc M V)
        (sup_le h.toHyp.le_Pc inf_le_left) hcommVD
        (RootHyp.conjSubgroup_inf_Pc_eq_bot h hHy hnM)
    have hpVD : p ∈ V ⊔ D := by
      have h : p ∈ Pc M V ⊓ (V ⊔ D ⊔ conjSubgroup y V) :=
        Subgroup.mem_inf.mpr ⟨hpP, hpR⟩
      rwa [hPR] at h
    have ha := inf_sup_Pc_W0_eq h hPH hVH hHy hnM hKy hnab hL hW₀ hN hW₀ne ψ
    rw [← ha]
    exact Subgroup.mem_inf.mpr ⟨hpVD, hpW⟩
  · exact sup_le (le_inf (inf_le_left.trans h.toHyp.le_Pc) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)


private theorem sup_conj_inv_eq_of_eq_sup {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    H = Pc M V ⊔ conjSubgroup y⁻¹ (Pc M V) := by
  have h := congrArg (conjSubgroup y⁻¹) hHy
  rw [conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (H.inv_mem hyH)),
    conjSubgroup_sup_eq_sup, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
  exact h.trans (sup_comm _ _)

private theorem KFactorization_inv {y : G} (hyH : y ∈ H)
    (hKy : KFactorization M V H y) : KFactorization M V H y⁻¹ := by
  have h := congrArg (conjSubgroup y⁻¹) hKy
  have h1 : conjSubgroup y⁻¹ (conjSubgroup y (Pc M V) ⊓ kOf V H) =
      Pc M V ⊓ conjSubgroup y⁻¹ (kOf V H) := by
    rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  rw [conjSubgroup_sup_eq_sup] at h
  rw [h1] at h
  rw [conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hyH))] at h
  rw [conjSubgroup_inf] at h
  rw [conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hyH))] at h
  exact h.trans (sup_comm _ _)

theorem mem_of_mul_mem_W0_of_mem_conj
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hKy : KFactorization M V H y)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {v d : G} (hv : v ∈ conjSubgroup y V)
    (hd : d ∈ Pc M V ⊓ conjSubgroup y (Pc M V)) (hvd : v * d ∈ W₀) :
    v ∈ W₀ := by
  have hyinv : y⁻¹ ∈ H := H.inv_mem hyH
  have hHyinv : H = Pc M V ⊔ conjSubgroup y⁻¹ (Pc M V) :=
    sup_conj_inv_eq_of_eq_sup hyH hHy
  have hKyinv : KFactorization M V H y⁻¹ := KFactorization_inv hyH hKy
  have hv' : MulAut.conj y⁻¹ v ∈ V := by
    have hmem : MulAut.conj y⁻¹ v ∈ conjSubgroup y⁻¹ (conjSubgroup y V) :=
      Subgroup.mem_map_of_mem _ hv
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hmem
  have hd' : MulAut.conj y⁻¹ d ∈ Pc M V ⊓ conjSubgroup y⁻¹ (Pc M V) := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_map_of_mem _ hd.1⟩
    have hmem : MulAut.conj y⁻¹ d ∈ conjSubgroup y⁻¹ (conjSubgroup y (Pc M V)) :=
      Subgroup.mem_map_of_mem _ hd.2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hmem
  have hvd' : MulAut.conj y⁻¹ v * MulAut.conj y⁻¹ d ∈ W₀ := by
    have hmem : MulAut.conj y⁻¹ (v * d) ∈ conjSubgroup y⁻¹ W₀ :=
      Subgroup.mem_map_of_mem _ hvd
    rw [conjSubgroup_eq_self_iff.mpr (hN hyinv)] at hmem
    simpa [map_mul] using hmem
  have hkey' := mem_of_mul_mem_W0_of_mem_inf_conj h hPH hVH hyinv hHyinv hnM hKyinv hnab hL
    hW₀ hN hW₀ne ψ hv' hd' hvd'
  have hmem : MulAut.conj y (MulAut.conj y⁻¹ v) ∈ conjSubgroup y W₀ :=
    Subgroup.mem_map_of_mem _ hkey'
  rw [conjSubgroup_eq_self_iff.mpr (hN hyH)] at hmem
  have hback : y * (y⁻¹ * v * y) * y⁻¹ = v := by group
  simpa [MulAut.conj_apply, hback] using hmem

private theorem inf_sup_conj_V_W0_eq
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hKy : KFactorization M V H y)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    (conjSubgroup y V ⊔ (Pc M V ⊓ conjSubgroup y (Pc M V))) ⊓ W₀ =
      (conjSubgroup y V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup y (Pc M V) ⊓ W₀) := by
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxW : x ∈ W₀ := hx.2
    have hxVD : x ∈ conjSubgroup y V ⊔ D := hx.1
    have hcomm : ∀ a ∈ conjSubgroup y V, ∀ b ∈ D, a * b = b * a := by
      intro a ha b hb
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ha
      have hbD : b ∈ Pc M V ⊓ conjSubgroup y (Pc M V) := by simpa [hD] using hb
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hbD.2
      have hpC : p ∈ Subgroup.centralizer (V : Set G) :=
        (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hp
      have hpv : p * v = v * p :=
        (Subgroup.mem_centralizer_iff.mp hpC v hv).symm
      change y * v * y⁻¹ * (y * p * y⁻¹) = y * p * y⁻¹ * (y * v * y⁻¹)
      calc y * v * y⁻¹ * (y * p * y⁻¹) = y * (v * p) * y⁻¹ := by group
        _ = y * (p * v) * y⁻¹ := by rw [hpv]
        _ = y * p * y⁻¹ * (y * v * y⁻¹) := by group
    obtain ⟨v, hv, d, hd, hvd⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hxVD
    have hvW₀ : v ∈ W₀ :=
      mem_of_mul_mem_W0_of_mem_conj h hPH hVH hyH hHy hnM hKy hnab hL hW₀ hN hW₀ne ψ
        hv (by simpa [hD] using hd) (hvd ▸ hxW)
    have hdW₀ : d ∈ W₀ := by
      have hd_eq : d = v⁻¹ * x := by rw [← hvd]; group
      rw [hd_eq]
      exact W₀.mul_mem (W₀.inv_mem hvW₀) hxW
    rw [← hvd]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hv, hvW₀⟩)
      (Subgroup.mem_inf.mpr ⟨hd, hdW₀⟩)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)


theorem inf_conj_Pc_W0_eq_sup
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hW₀K' : W₀ ≤ ⁅kOf V H, kOf V H⁆)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    conjSubgroup h₀ (Pc M V) ⊓ W₀ =
      (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊔
        (conjSubgroup h₀ V ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hKy : KFactorization M V H y := by
    rw [KFactorization] at hK ⊢
    rw [← hPy]
    exact hK
  rw [hPy, hVy]
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hVP : V ≤ Pc M V := h.toHyp.le_Pc
  have hDPy : D ≤ conjSubgroup y (Pc M V) := by rw [hD]; exact inf_le_right
  have hVPy : conjSubgroup y V ≤ conjSubgroup y (Pc M V) := Subgroup.map_mono hVP
  have ha := inf_sup_conj_V_W0_eq h hPH hVH hyH hHy hnM hKy hnab hL hW₀ hN hW₀ne ψ
  refine le_antisymm ?_ ?_
  · intro p hp
    have hpPy : p ∈ conjSubgroup y (Pc M V) := hp.1
    have hpW : p ∈ W₀ := hp.2
    have hpK' : p ∈ ⁅kOf V H, kOf V H⁆ := hW₀K' hpW
    have hK'_le_R : ⁅kOf V H, kOf V H⁆ ≤ V ⊔ D ⊔ conjSubgroup y V :=
      RootHyp.commutator_kOf_le_sup h hPH hHy hnM hKy
    have hpR : p ∈ V ⊔ D ⊔ conjSubgroup y V := hK'_le_R hpK'
    have hcomm := commute_sup_conj_V_D (hW := hW) h hPH hVH hyH hD
    have hR : V ⊔ D ⊔ conjSubgroup y V = (conjSubgroup y V ⊔ D) ⊔ V := by ac_rfl
    have hPR : conjSubgroup y (Pc M V) ⊓ (V ⊔ D ⊔ conjSubgroup y V) =
        conjSubgroup y V ⊔ D := by
      rw [hR]
      exact inf_sup_eq_left_of_le_of_comm (A := conjSubgroup y V ⊔ D) (B := V)
        (C := conjSubgroup y (Pc M V)) (sup_le hVPy hDPy) hcomm
        (RootHyp.inf_conj_Pc_eq_bot h hHy hnM)
    have hpVD : p ∈ conjSubgroup y V ⊔ D := by
      have h : p ∈ conjSubgroup y (Pc M V) ⊓ (V ⊔ D ⊔ conjSubgroup y V) :=
        Subgroup.mem_inf.mpr ⟨hpPy, hpR⟩
      simpa [hPR] using h
    rw [sup_comm]
    exact ha.symm ▸ Subgroup.mem_inf.mpr ⟨hpVD, hpW⟩
  · exact sup_le (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (inf_le_left.trans hVPy) inf_le_right)

theorem eq_sup_sup_of_nonabelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hW₀K' : W₀ ≤ ⁅kOf V H, kOf V H⁆)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    W₀ = (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊔
      (conjSubgroup h₀ V ⊓ W₀) := by
  have hA5 := RootHyp.eq_sup_inf_of_minimal h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  conv_lhs => rw [hA5]
  rw [inf_Pc_W0_eq_sup h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne hW₀K' ψ,
    inf_conj_Pc_W0_eq_sup h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne hW₀K' ψ]
  rw [← sup_assoc, sup_eq_left.mpr le_sup_right]

private theorem disjoint_A_P0_B {W₀ : Subgroup G} {A P₀ B : Subgroup G} {h₀ : G}
    (hA : A = V ⊓ W₀) (hP₀ : P₀ = Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)
    (hB : B = conjSubgroup h₀ V ⊓ W₀)
    (h : RootHyp M V) (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hA_le_P : A ≤ Pc M V) (hP₀_le_P : P₀ ≤ Pc M V) :
    A ⊓ P₀ = ⊥ ∧ (A ⊔ P₀) ⊓ B = ⊥ := by
  constructor
  · rw [eq_bot_iff]
    intro x hx
    have hxA : x ∈ V := by
      have hx' : x ∈ V ⊓ W₀ := by rw [hA] at hx; exact hx.1
      exact hx'.1
    have hxP₀ : x ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) := by
      have hx' : x ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ := by
        rw [hP₀] at hx; exact hx.2
      exact hx'.1
    have hmem : x ∈ V ⊓ conjSubgroup h₀ (Pc M V) := Subgroup.mem_inf.mpr ⟨hxA, hxP₀.2⟩
    rw [RootHyp.inf_conj_Pc_eq_bot h hH hnM] at hmem
    exact hmem
  · rw [eq_bot_iff]
    intro x hx
    have hxP : x ∈ Pc M V := (sup_le hA_le_P hP₀_le_P) hx.1
    have hxB : x ∈ conjSubgroup h₀ V := by
      have hx' : x ∈ conjSubgroup h₀ V ⊓ W₀ := by rw [hB] at hx; exact hx.2
      exact hx'.1
    have hmem : x ∈ conjSubgroup h₀ V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hxB, hxP⟩
    rw [RootHyp.conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem
    exact hmem

private theorem card_eq_sup_sup_of_disjoint {W₀ A P₀ B : Subgroup G}
    (hW0 : W₀ = A ⊔ P₀ ⊔ B)
    (hAcent : A ≤ Subgroup.centralizer (P₀ : Set G))
    (hAP₀cent : A ⊔ P₀ ≤ Subgroup.centralizer (B : Set G))
    (hAbot : A ⊓ P₀ = ⊥) (hAP₀bot : (A ⊔ P₀) ⊓ B = ⊥)
    (hcardA : Nat.card ↥A = Nat.card ↥B) :
    Nat.card ↥W₀ = Nat.card ↥A ^ 2 * Nat.card ↥P₀ := by
  have h1 : Nat.card ↥(A ⊔ P₀) = Nat.card ↥A * Nat.card ↥P₀ := by
    have hprod := card_sup_mul_card_inf_of_le_normalizer (G := G) (A := A) (B := P₀)
      (hAcent.trans (Subgroup.centralizer_le_normalizer _))
    rw [hAbot] at hprod
    simpa using hprod
  have h2 : Nat.card ↥W₀ = Nat.card ↥(A ⊔ P₀) * Nat.card ↥B := by
    rw [hW0]
    have hprod := card_sup_mul_card_inf_of_le_normalizer (G := G) (A := A ⊔ P₀) (B := B)
      (hAP₀cent.trans (Subgroup.centralizer_le_normalizer _))
    rw [hAP₀bot] at hprod
    simpa using hprod
  rw [h2, h1, hcardA]
  ring

theorem card_eq_of_nonabelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hW₀K' : W₀ ≤ ⁅kOf V H, kOf V H⁆)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  set A : Subgroup G := V ⊓ W₀ with hA
  set P₀ : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP₀
  set B : Subgroup G := conjSubgroup h₀ V ⊓ W₀ with hB
  have hW0 : W₀ = A ⊔ P₀ ⊔ B := by
    rw [hA, hP₀, hB]
    exact eq_sup_sup_of_nonabelian h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne hW₀K' hmin ψ
  have hA_le_P : A ≤ Pc M V := by
    rw [hA]; exact inf_le_left.trans h.toHyp.le_Pc
  have hP₀_le_P : P₀ ≤ Pc M V := by
    rw [hP₀]; exact inf_le_left.trans inf_le_left
  have hA_cent_P₀ : A ≤ Subgroup.centralizer (P₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have haW : a ∈ W₀ := (by simpa [hA] using ha : a ∈ V ⊓ W₀).2
    have hbW : b ∈ W₀ :=
      (by simpa [hP₀] using hb : b ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀).2
    exact ((isElemAbelian_xOf h hPH hVH).comm (hW₀ haW) (hW₀ hbW)).symm
  obtain ⟨hA_bot, hAP₀_bot⟩ := disjoint_A_P0_B hA hP₀ hB h hH hnM hA_le_P hP₀_le_P
  have hAP₀_cent_B : A ⊔ P₀ ≤ Subgroup.centralizer (B : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have haW : a ∈ W₀ := (by simpa [hA] using ha : a ∈ V ⊓ W₀).2
      have hbW : b ∈ W₀ := (by simpa [hB] using hb : b ∈ conjSubgroup h₀ V ⊓ W₀).2
      exact ((isElemAbelian_xOf h hPH hVH).comm (hW₀ haW) (hW₀ hbW)).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have haW : a ∈ W₀ :=
        (by simpa [hP₀] using ha : a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀).2
      have hbW : b ∈ W₀ := (by simpa [hB] using hb : b ∈ conjSubgroup h₀ V ⊓ W₀).2
      exact ((isElemAbelian_xOf h hPH hVH).comm (hW₀ haW) (hW₀ hbW)).symm
  have hcardA : Nat.card A = Nat.card B := by
    rw [hA, hB, hVy]
    have hconj : conjSubgroup y (V ⊓ W₀) = conjSubgroup y V ⊓ W₀ := by
      rw [conjSubgroup_inf, conjSubgroup_eq_self_iff.mpr (hN hyH)]
    rw [← hconj]
    exact (card_conjSubgroup y (V ⊓ W₀)).symm
  exact card_eq_sup_sup_of_disjoint hW0 hA_cent_P₀ hAP₀_cent_B hA_bot hAP₀_bot hcardA

end RootHyp

end CFSG.RankThree.GF2n.Tim81
