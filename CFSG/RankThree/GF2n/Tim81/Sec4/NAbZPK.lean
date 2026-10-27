
module

public import CFSG.GroupTheory.ConjInfCount
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelPlane
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbAlpha
public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthW
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Orth

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Quasithin.B45L2 CFSG.Quasithin.JonesParshall
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}
variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]

namespace RootHyp

private theorem isL2OrSz_of_sl2 {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l)) : IsL2OrSz V H := by
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · rw [h0, show 2 * 0 = 0 from rfl, pow_zero] at hl
      have := Fintype.one_lt_card (α := F)
      omega
    · exact hpos
  refine Or.inl ⟨F, inferInstance, inferInstance, inferInstance, ?_, ⟨ψ⟩⟩
  rw [hl]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem inf_centralizer_inf_xOf_eq_inf_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    Pc M V ⊓ Subgroup.centralizer ((Pc M V ⊓ Tim79a.xOf V H : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V H := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hA2₀, hAcard₀, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hA2 : ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1 := hA2₀
  have hAcard : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F := hAcard₀
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * l) := by
    rw [hAcard, hl]
  have horth' : Sec2.IsOrthModule hl (repW hW ψ) :=
    IsOrthModule.repW_of_subRepW (hW := hW) ψ hl horth
  refine le_antisymm ?_ ?_
  · intro p hp
    obtain ⟨hpP, hpC⟩ := Subgroup.mem_inf.mp hp
    have hpk : p ∈ kOf V H := by
      have ha : ψ (piK V H ⟨p, hPH hpP⟩) ∈ (imgK V H (Pc M V)).map ψ :=
        Subgroup.mem_map_of_mem _ (mem_imgK_iff.mpr ⟨⟨p, hPH hpP⟩, hpP, rfl⟩)
      have hfix : ∀ v ∈ commSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ),
          repW hW ψ (ψ (piK V H ⟨p, hPH hpP⟩)) v = v := by
        intro v hv
        rw [commSub_repW hW ψ hPH] at hv
        have hv' : ofW hW (toW hW v) ∈ subW hW ⁅Tim79a.xOf V H, Pc M V⁆ := by
          rwa [ofW_toW]
        have hxmem : (toW hW v : G) ∈ ⁅Tim79a.xOf V H, Pc M V⁆ :=
          (mem_subW_iff hW).mp hv'
        have hxPW : (toW hW v : G) ∈ Pc M V ⊓ Tim79a.xOf V H :=
          commutator_W0_Pc_le h hPH hVH (le_refl (Tim79a.xOf V H))
            (Tim79a.H_le_normalizer_xOf V H) hxmem
        have hcomm := Subgroup.mem_centralizer_iff.mp hpC (toW hW v : G) hxPW
        rw [← ofW_toW hW v, repW_apply_piK_ofMul]
        congr 1
        refine Subtype.ext ?_
        rw [conjH_apply_coe]
        calc p * (toW hW v : G) * p⁻¹ = ((toW hW v : G) * p) * p⁻¹ := by rw [hcomm]
          _ = (toW hW v : G) := by group
      have h1 := Sec2.IsOrthModule.eq_one_of_forall_commSub_fixed (hF := hl) horth'
        ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard' ha hfix
      have h2 : piK V H ⟨p, hPH hpP⟩ = 1 := ψ.injective (by rw [h1, map_one])
      exact (piK_eq_one_iff _).mp h2
    exact Subgroup.mem_inf.mpr ⟨hpP, hpk⟩
  · intro p hp
    obtain ⟨hpP, hpk⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨hpP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hpW : p ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := (mem_kOf_iff.mp hpk).2
    exact Subgroup.mem_centralizer_iff.mp hpW y hy.2

private theorem plane_fixedSub_card
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) = subW hW V ∧
      Nat.card V = 2 ^ l := by
  have hfixW : fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) =
      subW hW V := by
    have hfix0 := fixedSub_repW hW ψ hPH (S := Pc M V)
    rw [xOf_inf_centralizer_Pc_eq_V h] at hfix0
    simpa using hfix0
  refine ⟨hfixW, ?_⟩
  have h := card_inf_V_W0_eq_pow_of_isOrthModule (hW := hW) h hPH hVH hH hnM ψ hl
    (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H) horth
  rwa [inf_eq_left.mpr (le_xOf_self V H)] at h

private theorem exists_plane_data
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    ∃ (L : Subgroup G) (Lv : Submodule (ZMod 2)
        (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))) (C : Subgroup SL(2, F)),
      L ≤ Tim79a.xOf V H ∧ L ≤ Pc M V ∧ V < L ∧ Nat.card L = 2 ^ (2 * l) ∧
      Nat.card C = 2 ^ l ∧ C ≤ (imgK V H (Pc M V)).map ψ.toMonoidHom ∧
      subW hW L = Lv ∧
      (∀ w ∈ Lv, w ∉ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) →
        ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom,
          repW hW ψ a w = w ↔ a ∈ C) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hA2₀, hAcard₀, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hA2 : ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1 := hA2₀
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * l) := by
    rw [hAcard₀, hl]
  have horth' : Sec2.IsOrthModule hl (repW hW ψ) :=
    IsOrthModule.repW_of_subRepW (hW := hW) ψ hl horth
  obtain ⟨Lv, C, hfixLt, hLcomm, hLvcard, hCA, hCcard, hfix⟩ :=
    Sec2.IsOrthModule.exists_fixed_plane (hF := hl) horth'
      ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard'
  obtain ⟨hfixW, hVcard⟩ := plane_fixedSub_card (hW := hW) h hPH hVH hH hnM ψ hl horth
  let L : Subgroup G := subgroupOfSubW hW Lv
  have hL_le_W : L ≤ Tim79a.xOf V H := fun x hx => ((mem_subgroupOfSubW_iff hW).mp hx).1
  have hsubWL : subW hW L = Lv := subW_subgroupOfSubW hW Lv
  have hLv_le_comm : Lv ≤ subW hW ⁅Tim79a.xOf V H, Pc M V⁆ := by
    rw [← commSub_repW hW ψ hPH]
    exact hLcomm
  have hcomm_le : ⁅Tim79a.xOf V H, Pc M V⁆ ≤ Pc M V ⊓ Tim79a.xOf V H :=
    commutator_W0_Pc_le h hPH hVH (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)
  have hLleP : L ≤ Pc M V :=
    ((subW_le_subW_iff (hW := hW) (E := L)
      (F := ⁅Tim79a.xOf V H, Pc M V⁆) hL_le_W).mp
      (by rw [hsubWL]; exact hLv_le_comm)).trans (hcomm_le.trans inf_le_left)
  have hVL : V ≤ L :=
    (subW_le_subW_iff (hW := hW) (E := V) (F := L) (le_xOf_self V H)).mp (by
      rw [← hsubWL, hfixW] at hfixLt
      exact hfixLt.le)
  have hLcard : Nat.card L = 2 ^ (2 * l) := by
    rw [← natCard_subW hW hL_le_W, hsubWL]
    exact hLvcard
  have hq : 2 ≤ 2 ^ l := by
    rw [← hVcard]
    exact le_trans (by norm_num) h.four_le_card
  have hVne : V ≠ L := by
    intro hEq
    have hcard : Nat.card V = Nat.card L := by rw [hEq]
    rw [hVcard, hLcard] at hcard
    have hlt : 2 ^ l < 2 ^ (2 * l) := by
      rw [show 2 ^ (2 * l) = (2 ^ l) ^ 2 by rw [← pow_mul]; ring]
      calc 2 ^ l = 2 ^ l * 1 := by ring
        _ < 2 ^ l * 2 ^ l := Nat.mul_lt_mul_of_pos_left hq (pow_pos (by norm_num) l)
        _ = (2 ^ l) ^ 2 := by ring
    omega
  exact ⟨L, Lv, C, hL_le_W, hLleP, lt_of_le_of_ne hVL hVne, hLcard, hCcard, hCA,
    hsubWL, hfix⟩

private theorem plane_pointwise_centralizer
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H)))
    {L : Subgroup G} {Lv : Submodule (ZMod 2)
      (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))} {C : Subgroup SL(2, F)}
    (hL_le_W : L ≤ Tim79a.xOf V H) (hsubWL : subW hW L = Lv)
    (hfix : ∀ w ∈ Lv, w ∉ fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) →
      ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom,
        repW hW ψ a w = w ↔ a ∈ C) :
    ∀ x ∈ L, x ∉ V → ∀ p : G, (hpP : p ∈ Pc M V) →
      (ψ (piK V H ⟨p, hPH hpP⟩) ∈ C ↔
        p ∈ Subgroup.centralizer ({x} : Set G)) := by
  have hfixW : fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) =
      subW hW V := (plane_fixedSub_card (hW := hW) h hPH hVH hH hnM ψ hl horth).1
  intro x hxL hxV p hpP
  have hwx : ofW hW ⟨x, hL_le_W hxL⟩ ∈ Lv := by
    rw [← hsubWL]
    exact (mem_subW_iff hW).mpr hxL
  have hwfix : ofW hW ⟨x, hL_le_W hxL⟩ ∉
      fixedSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
    rw [hfixW, mem_subW_iff]
    intro hxV'
    exact hxV (by simpa using hxV')
  have ha : ψ (piK V H ⟨p, hPH hpP⟩) ∈ (imgK V H (Pc M V)).map ψ :=
    Subgroup.mem_map_of_mem _ (mem_imgK_iff.mpr ⟨⟨p, hPH hpP⟩, hpP, rfl⟩)
  have h := hfix _ hwx hwfix _ ha
  rw [← h]
  constructor
  · intro hρ
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ofW hW (conjH V H ⟨p, hPH hpP⟩ ⟨x, hL_le_W hxL⟩) =
        ofW hW ⟨x, hL_le_W hxL⟩ := by
      rw [← repW_apply_piK_ofMul hW ψ ⟨p, hPH hpP⟩ ⟨x, hL_le_W hxL⟩]
      exact hρ
    have h3 : conjH V H ⟨p, hPH hpP⟩ ⟨x, hL_le_W hxL⟩ = ⟨x, hL_le_W hxL⟩ :=
      ofW_injective hW h2
    have h4 := congrArg (fun z : ↥(Tim79a.xOf V H) => (z : G)) h3
    rw [conjH_apply_coe] at h4
    calc p * x = (p * x * p⁻¹) * p := by group
      _ = x * p := by rw [h4]
  · intro hpC
    rw [repW_apply_piK_ofMul hW ψ ⟨p, hPH hpP⟩ ⟨x, hL_le_W hxL⟩]
    congr 1
    refine Subtype.ext ?_
    rw [conjH_apply_coe]
    have hpcomm : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.mp hpC
    calc p * x * p⁻¹ = (x * p) * p⁻¹ := by rw [hpcomm]
      _ = x := by group

private theorem plane_centralizer_const
    (hPH : Pc M V ≤ H) {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {L : Subgroup G} {C : Subgroup SL(2, F)} (hVLt : V < L)
    (hxLv : ∀ x ∈ L, x ∉ V → ∀ p : G, (hpP : p ∈ Pc M V) →
      (ψ (piK V H ⟨p, hPH hpP⟩) ∈ C ↔
        p ∈ Subgroup.centralizer ({x} : Set G))) :
    (∀ p : G, (hpP : p ∈ Pc M V) →
      (ψ (piK V H ⟨p, hPH hpP⟩) ∈ C ↔
        p ∈ Subgroup.centralizer (L : Set G))) ∧
    (∀ x ∈ L, x ∉ V → Pc M V ⊓ Subgroup.centralizer ({x} : Set G) =
      Pc M V ⊓ Subgroup.centralizer (L : Set G)) := by
  have hex : ∃ x, x ∈ L ∧ x ∉ V := by
    by_contra hcon
    push Not at hcon
    exact hVLt.ne (le_antisymm hVLt.le (fun x hx => hcon x hx))
  have hcen_iff : ∀ p : G, (hpP : p ∈ Pc M V) →
      (ψ (piK V H ⟨p, hPH hpP⟩) ∈ C ↔
        p ∈ Subgroup.centralizer (L : Set G)) := by
    intro p hpP
    constructor
    · intro hpC
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hyV : y ∈ V
      · have hPV : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
        exact Subgroup.mem_centralizer_iff.mp (hPV hpP) y hyV
      · exact (Subgroup.mem_centralizer_singleton_iff.mp
          ((hxLv y hy hyV p hpP).mp hpC)).symm
    · intro hpC
      obtain ⟨x, hx, hxV⟩ := hex
      exact (hxLv x hx hxV p hpP).mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hpC x hx).symm)
  refine ⟨hcen_iff, ?_⟩
  intro x hx hxV
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpx⟩ := Subgroup.mem_inf.mp hp
    exact Subgroup.mem_inf.mpr ⟨hpP,
      (hcen_iff p hpP).mp ((hxLv x hx hxV p hpP).mpr hpx)⟩
  · intro hp
    obtain ⟨hpP, hpL⟩ := Subgroup.mem_inf.mp hp
    exact Subgroup.mem_inf.mpr ⟨hpP,
      (hxLv x hx hxV p hpP).mp ((hcen_iff p hpP).mpr hpL)⟩

private theorem plane_imgK_centralizer
    (hPH : Pc M V ≤ H) {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {L : Subgroup G} {C : Subgroup SL(2, F)}
    (hCA : C ≤ (imgK V H (Pc M V)).map ψ.toMonoidHom)
    (hcen_iff : ∀ p : G, (hpP : p ∈ Pc M V) →
      (ψ (piK V H ⟨p, hPH hpP⟩) ∈ C ↔
        p ∈ Subgroup.centralizer (L : Set G))) :
    (imgK V H (Pc M V ⊓ Subgroup.centralizer (L : Set G))).map ψ.toMonoidHom = C := by
  refine le_antisymm ?_ ?_
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨z, hz, hzy⟩ := mem_imgK_iff.mp hy
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
    have h := (hcen_iff (z : G) hzP).mpr hzC
    rw [← hzy, ← show (⟨z, hPH hzP⟩ : ↥H) = z from Subtype.ext rfl]
    exact h
  · intro c hc
    have hcA : c ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom := hCA hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hcA
    obtain ⟨z, hzP, hzy⟩ := mem_imgK_iff.mp hy
    have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      (hcen_iff (z : G) hzP).mp (by
        rw [show (⟨z, hPH hzP⟩ : ↥H) = z from Subtype.ext rfl, hzy]
        exact hc)
    exact Subgroup.mem_map.mpr ⟨piK V H z,
      mem_imgK_iff.mpr ⟨z, Subgroup.mem_inf.mpr ⟨hzP, hzC⟩, rfl⟩, by simp [hzy]⟩

private theorem plane_relIndex
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    {L : Subgroup G} (hL_le_W : L ≤ Tim79a.xOf V H)
    {C : Subgroup SL(2, F)} (hCcard : Nat.card C = 2 ^ l)
    (himg : (imgK V H (Pc M V ⊓ Subgroup.centralizer (L : Set G))).map ψ.toMonoidHom = C) :
    (Pc M V ⊓ Subgroup.centralizer (L : Set G)).relIndex (Pc M V) = 2 ^ l := by
  classical
  have hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * l) :=
    card_imgK_eq_two_pow h hPH hVH hH hnM ψ hl
  have hP0H : Pc M V ⊓ Subgroup.centralizer (L : Set G) ≤ H := inf_le_left.trans hPH
  have hP0K : (Pc M V ⊓ Subgroup.centralizer (L : Set G)) ⊓ kOf V H =
      Pc M V ⊓ kOf V H := by
    refine le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ?_
    refine le_inf (le_inf inf_le_left ?_) inf_le_right
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hpW : p ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := (mem_kOf_iff.mp hp.2).2
    exact Subgroup.mem_centralizer_iff.mp hpW y (hL_le_W hy)
  have hcardImg : Nat.card (imgK V H (Pc M V ⊓
      Subgroup.centralizer (L : Set G))) = 2 ^ l := by
    have h : Nat.card ((imgK V H (Pc M V ⊓ Subgroup.centralizer (L : Set G))).map
        ψ.toMonoidHom) = Nat.card (imgK V H (Pc M V ⊓
          Subgroup.centralizer (L : Set G))) :=
      Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective
    rw [himg, hCcard] at h
    exact h.symm
  have hP0card : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) =
      2 ^ l * Nat.card ↥(Pc M V ⊓ kOf V H : Subgroup G) := by
    have h := card_imgK_mul_card_inf (V := V) (H := H)
      (X := Pc M V ⊓ Subgroup.centralizer (L : Set G)) hP0H
    rw [hcardImg, hP0K] at h
    exact h.symm
  have hPcard : Nat.card ↥(Pc M V : Subgroup G) =
      2 ^ l * (2 ^ l * Nat.card ↥(Pc M V ⊓ kOf V H : Subgroup G)) := by
    have h := card_imgK_mul_card_inf (V := V) (H := H) (X := Pc M V) hPH
    rw [hPbar, show (2:ℕ) ^ (2 * l) = 2 ^ l * 2 ^ l by rw [← pow_add]; ring] at h
    rw [show 2 ^ l * (2 ^ l * Nat.card ↥(Pc M V ⊓ kOf V H : Subgroup G)) =
      (2 ^ l * 2 ^ l) * Nat.card ↥(Pc M V ⊓ kOf V H : Subgroup G) from by ring]
    exact h.symm
  have hrelmul := Subgroup.relIndex_mul_card
    (H := Pc M V ⊓ Subgroup.centralizer (L : Set G)) (K := Pc M V)
  rw [inf_eq_left.mpr (inf_le_left :
      Pc M V ⊓ Subgroup.centralizer (L : Set G) ≤ Pc M V), hP0card, hPcard] at hrelmul
  have hPKpos : 0 < Nat.card ↥(Pc M V ⊓ kOf V H : Subgroup G) := by
    haveI : Nonempty ↥(Pc M V ⊓ kOf V H : Subgroup G) :=
      ⟨⟨1, (Pc M V ⊓ kOf V H).one_mem⟩⟩
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (pow_pos (by norm_num) l) hPKpos) hrelmul

private theorem exists_plane_subgroup
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    ∃ L : Subgroup G, L ≤ Tim79a.xOf V H ∧ L ≤ Pc M V ∧ V < L ∧
      Nat.card L = 2 ^ (2 * l) ∧
      (Pc M V ⊓ Subgroup.centralizer (L : Set G)).relIndex (Pc M V) = 2 ^ l ∧
      (∀ x ∈ L, x ∉ V → Pc M V ⊓ Subgroup.centralizer ({x} : Set G) =
        Pc M V ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨L, Lv, C, hL_le_W, hLleP, hVLt, hLcard, hCcard, hCA, hsubWL, hfix⟩ :=
    exists_plane_data (hW := hW) h hPH hVH hH hnM ψ hl horth
  have hxLv := plane_pointwise_centralizer (hW := hW) h hPH hVH hH hnM ψ hl horth
    hL_le_W hsubWL hfix
  obtain ⟨hcen_iff, hcenL⟩ := plane_centralizer_const hPH ψ hVLt hxLv
  have himg : (imgK V H (Pc M V ⊓ Subgroup.centralizer (L : Set G))).map ψ.toMonoidHom = C :=
    plane_imgK_centralizer hPH ψ hCA hcen_iff
  exact ⟨L, hL_le_W, hLleP, hVLt, hLcard,
    plane_relIndex h hPH hVH hH hnM ψ hl hL_le_W hCcard himg, hcenL⟩

private theorem plane_conj_props
    {P₀ L : Subgroup G} {z : G} {l : ℕ}
    (hLP : L ≤ P₀) (hVL : V < L)
    (hcardL : Nat.card L = 2 ^ (2 * l))
    (hrel : (P₀ ⊓ Subgroup.centralizer (L : Set G)).relIndex P₀ = 2 ^ l)
    (hcen : ∀ x ∈ L, x ∉ V → P₀ ⊓ Subgroup.centralizer ({x} : Set G) =
      P₀ ⊓ Subgroup.centralizer (L : Set G))
    (hzP : conjSubgroup z P₀ = P₀) (hzV : conjSubgroup z V = V) :
    conjSubgroup z L ≤ P₀ ∧ V < conjSubgroup z L ∧
      Nat.card (conjSubgroup z L) = 2 ^ (2 * l) ∧
      (P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G)).relIndex P₀ = 2 ^ l ∧
      (∀ x ∈ conjSubgroup z L, x ∉ V → P₀ ⊓ Subgroup.centralizer ({x} : Set G) =
        P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G)) := by
  have hzL : conjSubgroup z L ≤ P₀ := by
    calc conjSubgroup z L ≤ conjSubgroup z P₀ := Subgroup.map_mono hLP
      _ = P₀ := hzP
  have hzVle : V ≤ conjSubgroup z L := by
    calc V = conjSubgroup z V := hzV.symm
      _ ≤ conjSubgroup z L := Subgroup.map_mono hVL.le
  have hzVne : V ≠ conjSubgroup z L := by
    intro hEq
    have h1 : conjSubgroup z V = conjSubgroup z L := by rw [hzV, hEq]
    exact hVL.ne (conjSubgroup_inj.mp h1)
  have hzLt : V < conjSubgroup z L := lt_of_le_of_ne hzVle hzVne
  have hzcard : Nat.card (conjSubgroup z L) = 2 ^ (2 * l) := by
    rw [conjSubgroup, Subgroup.card_map_of_injective
      (f := (MulAut.conj z).toMonoidHom) (MulAut.conj z).injective, hcardL]
  have hcen_sing : ∀ x : G, Subgroup.centralizer ({z * x * z⁻¹} : Set G) =
      conjSubgroup z (Subgroup.centralizer ({x} : Set G)) := by
    intro x
    have hzp : conjSubgroup z (Subgroup.zpowers x) = Subgroup.zpowers (z * x * z⁻¹) := by
      rw [conjSubgroup, MonoidHom.map_zpowers]
      rfl
    have hcz : ∀ a : G, Subgroup.centralizer (Subgroup.zpowers a : Set G) =
        Subgroup.centralizer ({a} : Set G) := by
      intro a
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h := centralizer_conjSubgroup_eq z (Subgroup.zpowers x)
    rw [hzp, hcz, hcz] at h
    exact h
  have hconjinf : conjSubgroup z (P₀ ⊓ Subgroup.centralizer (L : Set G)) =
      P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G) := by
    rw [conjSubgroup_inf, hzP, ← centralizer_conjSubgroup_eq]
  have hrel' : (P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G)).relIndex P₀ = 2 ^ l := by
    have hzPmap : Subgroup.map (MulAut.conj z).toMonoidHom P₀ = P₀ := hzP
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj z).toMonoidHom)
      (H := P₀ ⊓ Subgroup.centralizer (L : Set G)) (K := P₀) (MulAut.conj z).injective
    rw [hzPmap] at h
    rw [← hconjinf]
    simpa [conjSubgroup] using h.trans hrel
  have hcen' : ∀ x ∈ conjSubgroup z L, x ∉ V → P₀ ⊓ Subgroup.centralizer ({x} : Set G) =
      P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G) := by
    intro x hx hxV
    have hyL : z⁻¹ * x * z ∈ L := mem_conjSubgroup.mp hx
    have hyV : z⁻¹ * x * z ∉ V := by
      intro hyV
      apply hxV
      have hmem : z * (z⁻¹ * x * z) * z⁻¹ ∈ conjSubgroup z V :=
        Subgroup.mem_map.mpr ⟨z⁻¹ * x * z, hyV, rfl⟩
      rw [hzV] at hmem
      rwa [show z * (z⁻¹ * x * z) * z⁻¹ = x from by group] at hmem
    have hx_eq : x = z * (z⁻¹ * x * z) * z⁻¹ := by group
    have hsingle : Subgroup.centralizer ({x} : Set G) =
        conjSubgroup z (Subgroup.centralizer ({z⁻¹ * x * z} : Set G)) := by
      conv_lhs => rw [hx_eq]
      exact hcen_sing (z⁻¹ * x * z)
    calc P₀ ⊓ Subgroup.centralizer ({x} : Set G)
        = P₀ ⊓ conjSubgroup z (Subgroup.centralizer ({z⁻¹ * x * z} : Set G)) := by
            rw [hsingle]
      _ = conjSubgroup z (P₀ ⊓ Subgroup.centralizer ({z⁻¹ * x * z} : Set G)) := by
            rw [conjSubgroup_inf, hzP]
      _ = conjSubgroup z (P₀ ⊓ Subgroup.centralizer (L : Set G)) := by rw [hcen _ hyL hyV]
      _ = P₀ ⊓ Subgroup.centralizer (conjSubgroup z L : Set G) := hconjinf
  exact ⟨hzL, hzLt, hzcard, hrel', hcen'⟩

private theorem inf_xOf_le_center_inf_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) :
    Pc M V ⊓ Tim79a.xOf V H ≤
      (Pc M V ⊓ kOf V H) ⊓
        Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) := by
  refine le_inf ?_ ?_
  · exact le_inf inf_le_left (inf_le_right.trans (xOf_le_kOf h hPH hVH))
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxW : x ∈ Tim79a.xOf V H := hx.2
    have hyW : y ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
      (mem_kOf_iff.mp hy.2).2
    exact (Subgroup.mem_centralizer_iff.mp hyW x hxW).symm

private theorem exists_conj_plane_inf_kOf_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    ∃ L' : Subgroup G,
      L' ≤ Pc M V ∧ V < L' ∧ Nat.card L' = 2 ^ (2 * l) ∧
      (Pc M V ⊓ Subgroup.centralizer (L' : Set G)).relIndex (Pc M V) = 2 ^ l ∧
      (∀ x ∈ L', x ∉ V → Pc M V ⊓ Subgroup.centralizer ({x} : Set G) =
        Pc M V ⊓ Subgroup.centralizer (L' : Set G)) ∧
      L' ⊓ kOf V H = V ∧ Nat.card (imgK V H L') = 2 ^ l := by
  classical
  have hL : IsL2OrSz V H := isL2OrSz_of_sl2 (V := V) (H := H) ψ hl
  obtain ⟨L, hLW, hLP, hVL, hLcard, hrelL, hcenL⟩ :=
    exists_plane_subgroup (hW := hW) h hPH hVH hH hnM ψ hl horth
  have hLV : ¬ L ≤ V := fun hle => hVL.ne (le_antisymm hVL.le hle)
  obtain ⟨c, hcCV, hcLK⟩ :=
    h.exists_conj_not_le_kOf hPH hVH hH hnM hK hnab hL hLW hLV
  have hcM : c ∈ M := h.centralizer_le_M hcCV
  have hcP : conjSubgroup c (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hcM)
  have hcV : conjSubgroup c V = V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer (V : Set G) hcCV)
  obtain ⟨hL'P, hVL', hL'card, hrelL', hcenL'⟩ :=
    plane_conj_props (P₀ := Pc M V) (L := L) (z := c) hLP hVL hLcard hrelL hcenL hcP hcV
  have hL'K : conjSubgroup c L ⊓ kOf V H = V := by
    refine le_antisymm ?_ (le_inf hVL'.le (le_kOf h hPH hVH))
    intro a ha
    by_contra haV
    have hca : Pc M V ⊓ Subgroup.centralizer ({a} : Set G) =
        Pc M V ⊓ Subgroup.centralizer (conjSubgroup c L : Set G) :=
      hcenL' a ha.1 haV
    have hPW_le : Pc M V ⊓ Tim79a.xOf V H ≤
        Pc M V ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine le_inf inf_le_left ?_
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have haW : a ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
        (mem_kOf_iff.mp ha.2).2
      exact Subgroup.mem_centralizer_iff.mp haW w hw.2
    have hL'_le_cen : conjSubgroup c L ≤
        Subgroup.centralizer ((Pc M V ⊓ Tim79a.xOf V H : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup c L : Set G) := by
        have h0 : y ∈ Pc M V ⊓ Subgroup.centralizer ({a} : Set G) := hPW_le hy
        rwa [hca] at h0
      exact (Subgroup.mem_centralizer_iff.mp hy'.2 x hx).symm
    have hL'_le_PK : conjSubgroup c L ≤ Pc M V ⊓ kOf V H := by
      rw [← inf_centralizer_inf_xOf_eq_inf_kOf (hW := hW) h hPH hVH hH hnM ψ hl horth]
      exact le_inf hL'P hL'_le_cen
    exact hcLK (hL'_le_PK.trans inf_le_right)
  have hL'H : conjSubgroup c L ≤ H := hL'P.trans hPH
  have hVcard : Nat.card V = 2 ^ l :=
    (plane_fixedSub_card (hW := hW) h hPH hVH hH hnM ψ hl horth).2
  have hΛcard : Nat.card (imgK V H (conjSubgroup c L)) = 2 ^ l := by
    have h := card_imgK_mul_card_inf (V := V) (H := H) (X := conjSubgroup c L) hL'H
    rw [hL'K, hL'card, hVcard] at h
    rw [show (2:ℕ) ^ (2 * l) = 2 ^ l * 2 ^ l by rw [← pow_add]; ring] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) l) h
  exact ⟨conjSubgroup c L, hL'P, hVL', hL'card, hrelL', hcenL', hL'K, hΛcard⟩

private theorem exists_torus_conj_disjoint
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * l))
    {L : Subgroup G} (hLP : L ≤ Pc M V) (hΛcard : Nat.card (imgK V H L) = 2 ^ l) :
    ∃ r : HBar V H,
      r ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) ∧
      imgK V H L ⊓ conjSubgroup r (imgK V H L) = ⊥ := by
  classical
  have hL : IsL2OrSz V H := isL2OrSz_of_sl2 (V := V) (H := H) ψ hl
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · rw [h0, show 2 * 0 = 0 from rfl, pow_zero] at hl
      have := Fintype.one_lt_card (α := F)
      omega
    · exact hpos
  obtain ⟨R, hRN, hRcard, -, hRfpf⟩ :=
    exists_frobeniusComplement_imgK h hPH hVH hH hnM hL
  have hRcard' : Nat.card R = 2 ^ (2 * l) - 1 := by
    rw [hRcard, hPbar]
  have hΛle : imgK V H L ≤ imgK V H (Pc M V) := imgK_mono hLP
  have harith : (Nat.card (imgK V H L) - 1) ^ 2 < Nat.card R := by
    rw [hΛcard, hRcard']
    have hq : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl1
    have hlt : (2 ^ l - 1) ^ 2 < (2 ^ l) ^ 2 - 1 := by
      set q := 2 ^ l with hq_def
      have hq2 : 2 ≤ q := by rw [hq_def]; exact hq
      obtain ⟨r, hqr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [hqr, Nat.add_sub_cancel]
      have hsq : (r + 1) ^ 2 = r ^ 2 + (2 * r + 1) := by ring
      rw [hsq, Nat.add_sub_assoc (by omega : 1 ≤ 2 * r + 1), Nat.add_sub_cancel]
      have hr : 1 ≤ r := by omega
      omega
    rwa [show (2 ^ l) ^ 2 = 2 ^ (2 * l) by rw [← pow_mul]; ring] at hlt
  obtain ⟨r, hrR, hrdisj⟩ :=
    CFSG.GroupTheory.exists_inf_conjSubgroup_eq_bot_of_card (R := R)
      (Λ := imgK V H L)
      (fun r hr hr1 x hx => hRfpf r hr hr1 x (hΛle hx)) harith
  exact ⟨r, hRN hrR, hrdisj⟩

private theorem imgK_sup_conj_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H)
    {l : ℕ} {L : Subgroup G} {r : HBar V H}
    (hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * l))
    (hLP : L ≤ Pc M V) (hΛcard : Nat.card (imgK V H L) = 2 ^ l)
    (hrN : r ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)))
    (hrdisj : imgK V H L ⊓ conjSubgroup r (imgK V H L) = ⊥) :
    imgK V H L ⊔ conjSubgroup r (imgK V H L) = imgK V H (Pc M V) ∧
      (∀ a ∈ imgK V H L, ∀ b ∈ conjSubgroup r (imgK V H L), a * b = b * a) := by
  have hΛle : imgK V H L ≤ imgK V H (Pc M V) := imgK_mono hLP
  have hΛrle : conjSubgroup r (imgK V H L) ≤ imgK V H (Pc M V) := by
    have hrP : conjSubgroup r (imgK V H (Pc M V)) = imgK V H (Pc M V) :=
      conjSubgroup_eq_self_iff.mpr hrN
    calc conjSubgroup r (imgK V H L)
        ≤ conjSubgroup r (imgK V H (Pc M V)) := Subgroup.map_mono hΛle
      _ = imgK V H (Pc M V) := hrP
  have hcomm : ∀ a ∈ imgK V H L, ∀ b ∈ conjSubgroup r (imgK V H L), a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val ((isElemAbelian_imgK h hPH hVH).1.is_comm.comm
      ⟨a, hΛle ha⟩ ⟨b, hΛrle hb⟩)
  have hsupcard : Nat.card ↥(imgK V H L ⊔
      conjSubgroup r (imgK V H L) : Subgroup (HBar V H)) = 2 ^ (2 * l) := by
    have h := (@CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (HBar V H) _
      (inferInstance : Finite (HBar V H))
      (imgK V H L) (conjSubgroup r (imgK V H L)) hcomm).1
    have hconjcard : Nat.card (conjSubgroup r (imgK V H L)) =
        Nat.card (imgK V H L) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj r).toMonoidHom)
        (MulAut.conj r).injective
    rw [hrdisj, Subgroup.card_bot, hconjcard, hΛcard, mul_one, ← pow_add] at h
    rw [h]
    congr 1
    omega
  refine ⟨?_, hcomm⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le hΛle hΛrle) ?_
  rw [hsupcard, hPbar]

private theorem Pc_le_inf_kOf_sup_planes
    (hPH : Pc M V ≤ H)
    {L' : Subgroup G} {d : ↥H} {r : HBar V H}
    (hL'P : L' ≤ Pc M V) (hdP : conjSubgroup (d : G) (Pc M V) = Pc M V)
    (hd : piK V H d = r)
    (hΛsup : imgK V H L' ⊔ conjSubgroup r (imgK V H L') = imgK V H (Pc M V))
    (hcomm : ∀ a ∈ imgK V H L', ∀ b ∈ conjSubgroup r (imgK V H L'), a * b = b * a) :
    Pc M V ≤ (Pc M V ⊓ kOf V H) ⊔ L' ⊔ conjSubgroup (d : G) L' := by
  have hL'H : L' ≤ H := hL'P.trans hPH
  have hL''P : conjSubgroup (d : G) L' ≤ Pc M V :=
    (Subgroup.map_mono hL'P).trans (le_of_eq hdP)
  have hΛ'' : imgK V H (conjSubgroup (d : G) L') = conjSubgroup r (imgK V H L') := by
    rw [imgK_conjSubgroup d.2 hL'H, hd]
  intro p hp
  have hpbar : piK V H ⟨p, hPH hp⟩ ∈ imgK V H L' ⊔
      conjSubgroup r (imgK V H L') := by
    rw [hΛsup]
    exact mem_imgK_iff.mpr ⟨⟨p, hPH hp⟩, hp, rfl⟩
  change piK V H ⟨p, hPH hp⟩ ∈
    ((imgK V H L' ⊔ conjSubgroup r (imgK V H L') :
      Subgroup (HBar V H)) : Set (HBar V H)) at hpbar
  rw [(@CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (HBar V H) _
    (inferInstance : Finite (HBar V H))
    (imgK V H L')
    (conjSubgroup r (imgK V H L')) hcomm).2] at hpbar
  obtain ⟨lam, hlam, mu, hmu, hlamu⟩ := hpbar
  change lam ∈ imgK V H L' at hlam
  rw [← hΛ''] at hmu
  obtain ⟨x, hxL', hx⟩ := mem_imgK_iff.mp hlam
  obtain ⟨y, hyL'', hy⟩ := mem_imgK_iff.mp hmu
  have hxy : piK V H ⟨p, hPH hp⟩ = piK V H (x * y) := by
    rw [map_mul, hx, hy, ← hlamu]
  have hk : p * ((x : G) * (y : G))⁻¹ ∈ Pc M V ⊓ kOf V H := by
    refine ⟨(Pc M V).mul_mem hp
      ((Pc M V).inv_mem ((Pc M V).mul_mem (hL'P hxL') (hL''P hyL''))), ?_⟩
    have h1 : piK V H (⟨p, hPH hp⟩ * (x * y)⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact (piK_eq_one_iff _).mp h1
  have hp_eq : p = (p * ((x : G) * (y : G))⁻¹) * ((x : G) * (y : G)) := by group
  rw [hp_eq, ← mul_assoc]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hk hxL') hyL''

private theorem relIndex_inf_inf_le_two_pow
    {l : ℕ} {Z C1 C2 : Subgroup G} (hZP : Z ≤ Pc M V)
    (h1 : C1.relIndex (Pc M V) = 2 ^ l) (h2 : C2.relIndex (Pc M V) = 2 ^ l) :
    (Z ⊓ C1).relIndex Z ≤ 2 ^ l ∧ (Z ⊓ C1 ⊓ C2).relIndex (Z ⊓ C1) ≤ 2 ^ l := by
  have hC1P : C1.relIndex (Pc M V) ≠ 0 := by
    rw [h1]
    exact pow_ne_zero _ (by norm_num)
  have hC1Z : C1.relIndex Z ≠ 0 := fun h0 =>
    hC1P (Subgroup.relIndex_eq_zero_of_le_right hZP h0)
  have hC2P : C2.relIndex (Pc M V) ≠ 0 := by
    rw [h2]
    exact pow_ne_zero _ (by norm_num)
  have hC2Z : C2.relIndex Z ≠ 0 := fun h0 =>
    hC2P (Subgroup.relIndex_eq_zero_of_le_right hZP h0)
  constructor
  · rw [Subgroup.inf_relIndex_left]
    calc C1.relIndex Z ≤ C1.relIndex (Pc M V) :=
          Subgroup.relIndex_le_of_le_right hZP hC1P
      _ = 2 ^ l := h1
  · rw [Subgroup.inf_relIndex_left]
    calc C2.relIndex (Z ⊓ C1) ≤ C2.relIndex Z :=
          Subgroup.relIndex_le_of_le_right inf_le_left hC2Z
      _ ≤ C2.relIndex (Pc M V) :=
          Subgroup.relIndex_le_of_le_right hZP hC2P
      _ = 2 ^ l := h2

private theorem inf_planes_inf_le_V
    (h : RootHyp M V) {L' L'' : Subgroup G}
    (hPsup : Pc M V ≤ (Pc M V ⊓ kOf V H) ⊔ L' ⊔ L'') :
    ((Pc M V ⊓ kOf V H) ⊓
        Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G)) ⊓
      (Pc M V ⊓ Subgroup.centralizer (L' : Set G)) ⊓
      (Pc M V ⊓ Subgroup.centralizer (L'' : Set G)) ≤ V := by
  intro z hz
  have hzZ : z ∈ ((Pc M V ⊓ kOf V H) ⊓
      Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G)) := hz.1.1
  have hz1 : z ∈ Pc M V ⊓ Subgroup.centralizer (L' : Set G) := hz.1.2
  have hz2 : z ∈ Pc M V ⊓ Subgroup.centralizer (L'' : Set G) := hz.2
  have hzcenPK : z ∈ Subgroup.centralizer
      ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hzZ).2
  have hzcenL' : z ∈ Subgroup.centralizer (L' : Set G) :=
    (Subgroup.mem_inf.mp hz1).2
  have hzcenL'' : z ∈ Subgroup.centralizer (L'' : Set G) :=
    (Subgroup.mem_inf.mp hz2).2
  have h1 : (Pc M V ⊓ kOf V H) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzcenPK a ha
  have h2 : L' ≤ Subgroup.centralizer ({z} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzcenL' a ha
  have h3 : L'' ≤ Subgroup.centralizer ({z} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzcenL'' a ha
  have hsup : (Pc M V ⊓ kOf V H) ⊔ L' ⊔ L'' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (sup_le h1 h2) h3
  have hzPcen : z ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ Subgroup.centralizer ({z} : Set G) := hsup (hPsup hp)
    rw [Subgroup.mem_centralizer_singleton_iff] at hp'
    exact hp'
  rw [← h.toHyp.centralizer_Pc]
  exact hzPcen

private theorem card_inf_center_le_pow
    {l : ℕ} (hVcard : Nat.card V = 2 ^ l)
    {Z C1 C2 : Subgroup G}
    (h1 : (Z ⊓ C1).relIndex Z ≤ 2 ^ l)
    (h2 : (Z ⊓ C1 ⊓ C2).relIndex (Z ⊓ C1) ≤ 2 ^ l)
    (hZV : Z ⊓ C1 ⊓ C2 ≤ V) :
    Nat.card Z ≤ 2 ^ (3 * l) := by
  have hm : Nat.card ↥(Z ⊓ C1 ⊓ C2) ≤ 2 ^ l := by
    calc Nat.card ↥(Z ⊓ C1 ⊓ C2) ≤ Nat.card ↥V :=
          Nat.card_le_card_of_injective (fun x => ⟨(x : G), hZV x.2⟩)
            (fun a b h => Subtype.ext (congrArg (fun x : ↥V => (x : G)) h))
      _ = 2 ^ l := hVcard
  have h1' := Subgroup.relIndex_mul_card (H := Z ⊓ C1) (K := Z)
  rw [inf_eq_left.mpr (inf_le_left : Z ⊓ C1 ≤ Z)] at h1'
  have h2' := Subgroup.relIndex_mul_card (H := Z ⊓ C1 ⊓ C2) (K := Z ⊓ C1)
  rw [inf_eq_left.mpr (inf_le_left : Z ⊓ C1 ⊓ C2 ≤ Z ⊓ C1)] at h2'
  rw [← h1', ← h2']
  calc (Z ⊓ C1).relIndex Z * ((Z ⊓ C1 ⊓ C2).relIndex (Z ⊓ C1) *
      Nat.card ↥(Z ⊓ C1 ⊓ C2))
      ≤ 2 ^ l * (2 ^ l * 2 ^ l) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 hm)
    _ = 2 ^ (3 * l) := by
        rw [show 2 ^ l * (2 ^ l * 2 ^ l) = 2 ^ l * 2 ^ (l + l) by rw [← pow_add],
          show 2 ^ l * 2 ^ (l + l) = 2 ^ (l + (l + l)) by rw [← pow_add]]
        congr 1
        omega

theorem inf_kOf_inf_centralizer_eq_inf_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl
      (subRepW hW ψ (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H))) :
    Pc M V ⊓ kOf V H ⊓
        Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) =
      Pc M V ⊓ Tim79a.xOf V H := by
  classical
  have hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * l) :=
    card_imgK_eq_two_pow h hPH hVH hH hnM ψ hl
  have hVcard : Nat.card V = 2 ^ l :=
    (plane_fixedSub_card (hW := hW) h hPH hVH hH hnM ψ hl horth).2
  have hPWcard : Nat.card ↥(Pc M V ⊓ Tim79a.xOf V H) = 2 ^ (3 * l) :=
    card_inf_Pc_W0_eq_pow_of_isOrthModule (hW := hW) h hPH hVH hH hnM ψ hl
      (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H) horth
  have hPW_le_Z := inf_xOf_le_center_inf_kOf h hPH hVH
  obtain ⟨L', hL'P, hVL', hL'card, hrelL', hcenL', -, hΛcard⟩ :=
    exists_conj_plane_inf_kOf_eq (hW := hW) h hPH hVH hH hnM hK hnab ψ hl horth
  obtain ⟨r, hrN, hrdisj⟩ :=
    exists_torus_conj_disjoint h hPH hVH hH hnM ψ hl hPbar hL'P hΛcard
  obtain ⟨d, hd⟩ := piK_surjective V H r
  have hdN : piK V H d ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    rw [hd]
    exact hrN
  obtain ⟨hdM, -⟩ :=
    mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK h hPH hdN
  have hdP : conjSubgroup (d : G) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hdM)
  have hdV : conjSubgroup (d : G) V = V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.normalizer_eq.symm ▸ hdM)
  obtain ⟨-, -, -, hrelL'', -⟩ :=
    plane_conj_props (P₀ := Pc M V) (L := L') (z := (d : G))
      hL'P hVL' hL'card hrelL' hcenL' hdP hdV
  obtain ⟨hΛsup, hcomm⟩ :=
    imgK_sup_conj_eq h hPH hVH hPbar hL'P hΛcard hrN hrdisj
  have hPsup : Pc M V ≤ (Pc M V ⊓ kOf V H) ⊔ L' ⊔ conjSubgroup (d : G) L' :=
    Pc_le_inf_kOf_sup_planes (V := V) (H := H) (M := M)
      hPH hL'P hdP hd hΛsup hcomm
  set Z : Subgroup G := (Pc M V ⊓ kOf V H) ⊓
    Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) with hZ
  set C1 : Subgroup G := Pc M V ⊓ Subgroup.centralizer (L' : Set G) with hC1
  set C2 : Subgroup G :=
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup (d : G) L' : Set G) with hC2
  have hZP : Z ≤ Pc M V := fun x hx => (Subgroup.mem_inf.mp hx).1.1
  have hZV : Z ⊓ C1 ⊓ C2 ≤ V := inf_planes_inf_le_V (h := h) hPsup
  obtain ⟨hrel1, hrel2⟩ :=
    relIndex_inf_inf_le_two_pow (Z := Z) (C1 := C1) (C2 := C2) hZP hrelL' hrelL''
  have hZcard : Nat.card Z ≤ 2 ^ (3 * l) := card_inf_center_le_pow hVcard hrel1 hrel2 hZV
  refine (Subgroup.eq_of_le_of_card_ge hPW_le_Z ?_).symm
  rw [hPWcard]
  exact hZcard

end RootHyp

end CFSG.RankThree.GF2n.Tim81
