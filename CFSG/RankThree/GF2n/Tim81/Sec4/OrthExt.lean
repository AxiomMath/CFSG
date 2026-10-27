module

public import CFSG.GroupTheory.CommutatorMemSubgroup
public import CFSG.RankThree.GF2n.Tim81.Sec4.HBarData
public import CFSG.RankThree.GF2n.Tim81.Sec4.KNonabelian
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthH1
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelBasic
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRep

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem imgK_conj_inf_normalizer_eq_bot_of_sl2 (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    imgK V H (conjSubgroup h₀ (Pc M V)) ⊓
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) = ⊥ := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hHinv : H = Pc M V ⊔ conjSubgroup y⁻¹ (Pc M V) := by
    have h1 : conjSubgroup y⁻¹ H = H :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (H.inv_mem hyH))
    have h2 : conjSubgroup y⁻¹ H =
        conjSubgroup y⁻¹ (Pc M V) ⊔ conjSubgroup y⁻¹ (conjSubgroup y (Pc M V)) := by
      rw [hHy, CFSG.CGT.Timmesfeld75.conjSubgroup_sup]
    rw [h1, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h2
    rw [h2, sup_comm]
  have hmain := inf_imgK_normalizer_eq_bot_of_sl2 h hPH hHinv hnM ψ
  set g : HBar V H := piK V H ⟨y, hyH⟩ with hg
  have hconj : conjSubgroup g (imgK V H (Pc M V)) ⊓
      conjSubgroup g (Subgroup.normalizer
        (imgK V H (conjSubgroup y⁻¹ (Pc M V)) : Set (HBar V H))) = ⊥ := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_inf g (imgK V H (Pc M V))
      (Subgroup.normalizer (imgK V H (conjSubgroup y⁻¹ (Pc M V)) : Set (HBar V H)))]
    rw [hmain]
    exact Subgroup.map_bot _
  rw [← normalizer_conjSubgroup] at hconj
  have hPy' : conjSubgroup g (imgK V H (conjSubgroup y⁻¹ (Pc M V))) =
      imgK V H (Pc M V) := by
    rw [hg]
    have hstep : imgK V H (conjSubgroup y⁻¹ (Pc M V)) =
        conjSubgroup (piK V H ⟨y⁻¹, H.inv_mem hyH⟩) (imgK V H (Pc M V)) :=
      imgK_conjSubgroup (H.inv_mem hyH) hPH
    rw [hstep, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    have h1 : piK V H ⟨y, hyH⟩ * piK V H ⟨y⁻¹, H.inv_mem hyH⟩ = 1 := by
      have hsub : (⟨y, hyH⟩ : ↥H) * ⟨y⁻¹, H.inv_mem hyH⟩ = 1 := by
        ext
        simp
      rw [← map_mul, hsub, map_one]
    rw [h1, conjSubgroup_one]
  have hPy : conjSubgroup g (imgK V H (Pc M V)) =
      imgK V H (conjSubgroup h₀ (Pc M V)) := by
    rw [hg]
    have hstep : imgK V H (conjSubgroup y (Pc M V)) =
        conjSubgroup (piK V H ⟨y, hyH⟩) (imgK V H (Pc M V)) :=
      imgK_conjSubgroup hyH hPH
    rw [← hstep, hPy]
  rwa [hPy', hPy] at hconj

theorem sup_imgK_conj_eq_top_of_sl2
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {y : HBar V H} (hy : y ∈ imgK V H (conjSubgroup h₀ (Pc M V))) (hy1 : y ≠ 1) :
    imgK V H (Pc M V) ⊔ conjSubgroup y (imgK V H (Pc M V)) = ⊤ := by
  classical
  set A : Subgroup (HBar V H) := imgK V H (Pc M V) with hA
  set A' : Subgroup (HBar V H) := imgK V H (conjSubgroup h₀ (Pc M V)) with hA'
  have hbot := imgK_conj_inf_normalizer_eq_bot_of_sl2 h hPH hH hnM ψ
  have hyN : y ∉ Subgroup.normalizer (A : Set (HBar V H)) := by
    intro hyN
    have : y ∈ A' ⊓ Subgroup.normalizer (A : Set (HBar V H)) :=
      Subgroup.mem_inf.mpr ⟨hy, hyN⟩
    rw [hbot] at this
    exact hy1 (Subgroup.mem_bot.mp this)
  obtain ⟨-, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hmapN : (A.map ψ.toMonoidHom) = conjSubgroup a (utri F) := ha
  have hψN : ψ y ∉ Subgroup.normalizer (A.map ψ.toMonoidHom : Set (SL(2, F))) := by
    intro hmem
    apply hyN
    have hmap := Subgroup.map_normalizer_eq_of_bijective A
      (f := ψ.toMonoidHom) ψ.bijective
    have : ψ y ∈ (Subgroup.normalizer (A : Set (HBar V H))).map ψ.toMonoidHom := by
      rw [hmap]
      exact hmem
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp this
    exact (ψ.injective hzy) ▸ hz
  have hne' : conjSubgroup a (utri F) ≠ conjSubgroup (ψ y * a) (utri F) := by
    intro heq
    apply hψN
    rw [← conjSubgroup_eq_self_iff]
    rw [hmapN, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact heq.symm
  have hsup : (A.map ψ.toMonoidHom) ⊔ conjSubgroup (ψ y) (A.map ψ.toMonoidHom) = ⊤ := by
    rw [hmapN, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact sup_conjSubgroup_utri_eq_top hne'
  have hmap_sup : (A ⊔ conjSubgroup y A).map ψ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, map_conjSubgroup]
    exact hsup
  have htop : (⊤ : Subgroup (HBar V H)).map ψ.toMonoidHom = ⊤ := by simp
  rw [← htop] at hmap_sup
  exact Subgroup.map_injective ψ.injective hmap_sup


private theorem subRepW_sub_eq_ofW {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {E : Subgroup G}
    (hE : E ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (E : Set G))
    (h : ↥H) (z : subW hW E) :
    (subRepW hW ψ hE hN (ψ (piK V H h)) z - z :
      Additive (IntMod (Tim79a.xOf V H) hW)) =
      ofW hW ⟨⁅(h : G), ((toW hW (z : Additive (IntMod (Tim79a.xOf V H) hW)) :
        ↥(Tim79a.xOf V H)) : G)⁆,
        mem_commutator_xOf (z := h) (w := toW hW (z : Additive (IntMod (Tim79a.xOf V H) hW)))⟩ := by
  rw [show subRepW hW ψ hE hN = CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW E)
      ((normalizer_subW_iff hW ψ hE).mp hN) from rfl]
  rw [CFSG.Quasithin.B45U33.subRep_apply]
  simpa [ofW_toW] using
    repW_apply_piK_sub (hW := hW) ψ h
      (toW hW (z : Additive (IntMod (Tim79a.xOf V H) hW)))

private theorem exists_cocycle_of_commutator_mem
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    {v : G} (hvK : ∀ k ∈ kOf V H, k * v = v * k)
    (hvH : ∀ g ∈ H, ⁅g, v⁆ ∈ E) :
    ∃ c : ↥H → subW hW E,
      (∀ a : ↥H, (c a : Additive (IntMod (Tim79a.xOf V H) hW)) =
        ofW hW ⟨⁅(a : G), v⁆, hE (hvH a a.2)⟩) ∧
      (∀ a b : ↥H, c (a * b) =
        c a + subRepW hW ψ hE hN (ψ (piK V H a)) (c b)) ∧
      (∀ a : ↥H, ψ (piK V H a) = 1 → c a = 0) := by
  classical
  let c : ↥H → subW hW E := fun g =>
    ⟨ofW hW ⟨⁅(g : G), v⁆, hE (hvH g g.2)⟩, by
      rw [mem_subW_iff hW]
      exact hvH g g.2⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a b
    apply Subtype.ext
    show ofW hW ⟨⁅((a : G) * (b : G)), v⁆, hE (hvH (a * b) (a * b).2)⟩ =
      ofW hW ⟨⁅(a : G), v⁆, hE (hvH a a.2)⟩ +
        (subRepW hW ψ hE hN (ψ (piK V H a)) (c b) :
          Additive (IntMod (Tim79a.xOf V H) hW))
    rw [show (subRepW hW ψ hE hN (ψ (piK V H a)) (c b) :
        Additive (IntMod (Tim79a.xOf V H) hW)) =
        ofW hW (conjH V H a ⟨⁅(b : G), v⁆, hE (hvH b b.2)⟩) by
      show ((subRepW hW ψ hE hN (ψ (piK V H a)) (c b) : subW hW E) :
        Additive (IntMod (Tim79a.xOf V H) hW)) = _
      rw [show subRepW hW ψ hE hN = CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW E)
          ((normalizer_subW_iff hW ψ hE).mp hN) from rfl]
      rw [CFSG.Quasithin.B45U33.subRep_apply]
      rw [show (c b : Additive (IntMod (Tim79a.xOf V H) hW)) =
          ofW hW ⟨⁅(b : G), v⁆, hE (hvH b b.2)⟩ from rfl]
      rw [repW_apply_piK, toW_ofW]]
    rw [add_comm]
    rw [← ofW_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, conjH_apply_coe, commutatorElement_def]
    group
  · intro a ha
    have hpi : piK V H a = 1 := by
      apply ψ.injective
      simpa using ha
    have hK : (a : G) ∈ kOf V H := (piK_eq_one_iff a).mp hpi
    have hcomm : (a : G) * v = v * (a : G) := hvK (a : G) hK
    apply Subtype.ext
    show ofW hW ⟨⁅(a : G), v⁆, hE (hvH a a.2)⟩ =
      (0 : Additive (IntMod (Tim79a.xOf V H) hW))
    have h1 : ⁅(a : G), v⁆ = 1 := by
      rw [commutatorElement_def]
      rw [show (a : G) * v = v * (a : G) from hcomm]
      group
    apply toW_injective hW
    rw [toW_ofW, toW_zero]
    exact Subtype.ext h1

private theorem commutator_eq_and_commutes_of_subRepW
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    {v : G} (hvH : ∀ g ∈ H, ⁅g, v⁆ ∈ E)
    {c : ↥H → subW hW E} {w : subW hW E}
    (hc : ∀ a : ↥H, (c a : Additive (IntMod (Tim79a.xOf V H) hW)) =
      ofW hW ⟨⁅(a : G), v⁆, hE (hvH a a.2)⟩)
    (hw : ∀ a : ↥H, c a = subRepW hW ψ hE hN (ψ (piK V H a)) w - w) :
    (∀ a : ↥H, ⁅(a : G), v⁆ =
      (a : G) * toW hW w * (a : G)⁻¹ * (toW hW w)⁻¹) ∧
    (∀ g : ↥H, (g : G) * (toW hW w)⁻¹ * v =
      (toW hW w)⁻¹ * v * (g : G)) := by
  classical
  let w' : G := toW hW w
  have hgrp : ∀ a : ↥H, ⁅(a : G), v⁆ = (a : G) * w' * (a : G)⁻¹ * w'⁻¹ := by
    intro a
    have h1 : c a = subRepW hW ψ hE hN (ψ (piK V H a)) w - w := hw a
    have h2 : (subRepW hW ψ hE hN (ψ (piK V H a)) w - w : subW hW E) =
        ofW hW ⟨⁅(a : G), ((toW hW (w : Additive (IntMod (Tim79a.xOf V H) hW)) :
          ↥(Tim79a.xOf V H)) : G)⁆,
          mem_commutator_xOf (z := a) (w := toW hW (w : Additive (IntMod (Tim79a.xOf V H) hW)))⟩ :=
      subRepW_sub_eq_ofW (hW := hW) ψ hE hN a w
    have h1amb : (c a : Additive (IntMod (Tim79a.xOf V H) hW)) =
        (subRepW hW ψ hE hN (ψ (piK V H a)) w - w :
          Additive (IntMod (Tim79a.xOf V H) hW)) :=
      congrArg Subtype.val h1
    rw [hc a] at h1amb
    have h3 := congrArg (toW hW) (h1amb.trans h2)
    have h4 := congrArg Subtype.val h3
    have hneg : (toW hW (-(w : Additive (IntMod (Tim79a.xOf V H) hW))) :
        ↥(Tim79a.xOf V H)) =
        (toW hW (w : Additive (IntMod (Tim79a.xOf V H) hW)))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← toW_add, add_neg_cancel, toW_zero]
    simpa [w', hneg, conjH_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def] using h4
  refine ⟨hgrp, ?_⟩
  intro g
  let u : G := w'⁻¹ * v
  conv_lhs => rw [mul_assoc]
  change (g : G) * u = u * (g : G)
  have hg := hgrp g
  have h1 : (g : G) * w' * (g : G)⁻¹ = ⁅(g : G), v⁆ * w' := by
    calc (g : G) * w' * (g : G)⁻¹ =
        ((g : G) * w' * (g : G)⁻¹ * w'⁻¹) * w' := by group
      _ = ⁅(g : G), v⁆ * w' := by rw [← hg]
  have h2 : (g : G) * v * (g : G)⁻¹ = ⁅(g : G), v⁆ * v := by
    rw [commutatorElement_def]
    group
  calc (g : G) * u =
      ((g : G) * w' * (g : G)⁻¹)⁻¹ * ((g : G) * v * (g : G)⁻¹) * (g : G) := by
        simp [u]
        group
    _ = (⁅(g : G), v⁆ * w')⁻¹ * (⁅(g : G), v⁆ * v) * (g : G) := by rw [h1, h2]
    _ = w'⁻¹ * v * (g : G) := by group
    _ = u * (g : G) := by simp [u]

private theorem eq_one_of_commutes_with_H
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {u : G} (hu_comm : ∀ g : ↥H, (g : G) * u = u * (g : G)) :
    u = 1 := by
  classical
  obtain ⟨y₀, -, -, hVy₀, hH₀⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have huC_P : u ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact hu_comm ⟨p, hPH hp⟩
  have huC_Py : u ∈ Subgroup.centralizer (conjSubgroup y₀ (Pc M V) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact hu_comm ⟨p, by rw [hH₀]; exact Subgroup.mem_sup_right hp⟩
  have huV : u ∈ V := by
    rw [← Hyp.centralizer_Pc h.toHyp]
    exact huC_P
  have huVy : u ∈ conjSubgroup y₀ V := by
    rw [← Hyp.centralizer_conj_Pc h.toHyp y₀]
    exact huC_Py
  have hVy_ne : conjSubgroup y₀ V ≠ V := by
    rw [← hVy₀]
    exact conjSubgroup_ne_self h hH hnM
  have hinf : V ⊓ conjSubgroup y₀ V = ⊥ :=
    CFSG.RankThree.GF2n.inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hVy_ne
  have hu1 : u = 1 := by
    have hubot : u ∈ V ⊓ conjSubgroup y₀ V := Subgroup.mem_inf.mpr ⟨huV, huVy⟩
    rw [hinf] at hubot
    exact Subgroup.mem_bot.mp hubot
  exact hu1

theorem mem_of_isOrthModule_of_commutator_mem
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hE hN))
    {v : G} (hvK : ∀ k ∈ kOf V H, k * v = v * k)
    (hvH : ∀ g ∈ H, ⁅g, v⁆ ∈ E) :
    v ∈ E := by
  classical
  let π : ↥H →* SL(2, F) := ψ.toMonoidHom.comp (piK V H)
  have hπ : Function.Surjective π := ψ.surjective.comp (piK_surjective V H)
  let ρ : Representation (ZMod 2) SL(2, F) (subW hW E) := subRepW hW ψ hE hN
  obtain ⟨c, hc_canon, hc, hker⟩ :=
    exists_cocycle_of_commutator_mem (hW := hW) ψ hE hN hvK hvH
  have hl0 : 0 < l := by
    have := Sec2.one_le_of_card hl
    omega
  obtain ⟨w, hw⟩ := horth.exists_eq_sub_of_cocycle_comp hl hl0 π hπ hc hker
  let w' : G := toW hW w
  have hw'E : w' ∈ E := (mem_subW_iff hW).mp (by simpa [w'] using w.2)
  have hcomm :=
    commutator_eq_and_commutes_of_subRepW (hW := hW) ψ hE hN hvH hc_canon hw
  let u : G := w'⁻¹ * v
  have hu_comm : ∀ g : ↥H, (g : G) * u = u * (g : G) := by
    intro g
    simpa [u, w', mul_assoc] using hcomm.2 g
  have hu1 : u = 1 := eq_one_of_commutes_with_H h hPH hH hnM hu_comm
  have hvE : v ∈ E := by
    have hv_eq : v = w' := by
      calc v = w' * (w'⁻¹ * v) := by group
        _ = w' * 1 := by rw [show w'⁻¹ * v = 1 from hu1]
        _ = w' := mul_one w'
    rw [hv_eq]
    exact hw'E
  exact hvE

theorem mem_of_isOrthModule_of_commutator_mem_beta
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hE hN))
    {v : G} (hvK : ∀ k ∈ kOf V H, k * v = v * k)
    (hvP : ∀ p ∈ Pc M V, ⁅p, v⁆ ∈ E)
    {y : G} (hy : y ∈ conjSubgroup h₀ (Pc M V)) (hyK : y ∉ kOf V H)
    (hvy : ⁅y, v⁆ ∈ E) :
    v ∈ E := by
  classical
  have hyH : y ∈ H := by
    have hle : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
    exact hle hy
  let H₁ : Subgroup G := CFSG.GroupTheory.commMemSubgroup H E hN v
  have hH₁le : H₁ ≤ H := fun g hg => hg.1
  have hP_le : Pc M V ≤ H₁ := by
    intro p hp
    exact ⟨hPH hp, hvP p hp⟩
  have hK_le : kOf V H ≤ H₁ := by
    intro k hk
    refine ⟨kOf_le V H hk, ?_⟩
    have hcomm : k * v = v * k := hvK k hk
    have h1 : ⁅k, v⁆ = 1 := by
      rw [commutatorElement_def]
      rw [show k * v = v * k from hcomm]
      group
    rw [h1]
    exact E.one_mem
  have hy_mem : y ∈ H₁ := ⟨hyH, hvy⟩
  have himg_top : imgK V H H₁ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← sup_imgK_conj_eq_top_of_sl2 h hPH hVH hH hnM ψ
      (y := piK V H ⟨y, hyH⟩) ?_ ?_]
    · refine sup_le (imgK_mono hP_le) ?_
      have hPy_le : conjSubgroup y (Pc M V) ≤ H₁ := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
        exact H₁.mul_mem (H₁.mul_mem hy_mem (hP_le hp)) (H₁.inv_mem hy_mem)
      rw [← imgK_conjSubgroup hyH hPH]
      exact imgK_mono hPy_le
    · exact (mem_imgK_iff).mpr ⟨⟨y, hyH⟩, hy, rfl⟩
    · intro h1
      exact hyK ((piK_eq_one_iff _).mp h1)
  have hH₁_eq : H₁ = H := by
    have h1 := (imgK_eq_iff_sup_kOf_eq (V := V) (H := H)
      hH₁le (le_refl H)).mp ?_
    · rwa [sup_eq_left.mpr hK_le, sup_eq_left.mpr (kOf_le V H)] at h1
    · rw [himg_top, imgK_self]
  have hvH : ∀ g ∈ H, ⁅g, v⁆ ∈ E := by
    intro g hg
    exact (hH₁_eq.symm ▸ hg : g ∈ H₁).2
  exact mem_of_isOrthModule_of_commutator_mem h hPH hH hnM ψ hl hE hN horth hvK hvH

theorem mem_of_isOrthModule_of_forall_commutator_mem
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (E : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hE hN))
    {v : G} (hvK : ∀ k ∈ kOf V H, k * v = v * k)
    (hvP : ∀ p ∈ Pc M V, ⁅p, v⁆ ∈ E)
    (hvP' : ∀ p ∈ conjSubgroup h₀ (Pc M V), ⁅p, v⁆ ∈ E) :
    v ∈ E := by
  classical
  have hex : ∃ y ∈ conjSubgroup h₀ (Pc M V), y ∉ kOf V H := by
    by_contra hcon
    push Not at hcon
    have hle : conjSubgroup h₀ (Pc M V) ≤ kOf V H := fun y hy => hcon y hy
    have hcent : conjSubgroup h₀ (Pc M V) ≤ Subgroup.centralizer (V : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (mem_kOf_iff.mp (hle hk)).2 w (le_xOf_self V H hw)
    have hVle : V ≤ conjSubgroup h₀ V := by
      rw [← Hyp.centralizer_conj_Pc h.toHyp h₀]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (Subgroup.mem_centralizer_iff.mp (hcent hp) w hw).symm
    have heqV : V = conjSubgroup h₀ V :=
      Subgroup.eq_of_le_of_card_ge hVle (by rw [card_conjSubgroup])
    exact conjSubgroup_ne_self h hH hnM heqV.symm
  obtain ⟨y, hy, hyK⟩ := hex
  exact mem_of_isOrthModule_of_commutator_mem_beta h hPH hVH hH hnM ψ hl hE hN horth
    hvK hvP hy hyK (hvP' y hy)

end RootHyp

end CFSG.RankThree.GF2n.Tim81

end
