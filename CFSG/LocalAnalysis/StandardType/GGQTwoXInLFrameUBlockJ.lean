module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoNoTwoNodeKSide
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private lemma ggQTUbj_omega_primitive {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : ω ≠ 1) : IsPrimitiveRoot ω 3 := by
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hdvd : orderOf ω ∣ 3 := hcard ▸ orderOf_dvd_natCard ω
  have hne : orderOf ω ≠ 1 := fun ho => hω (orderOf_eq_one_iff.mp ho)
  have hord : orderOf ω = 3 := by
    have hle : orderOf ω ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 1 ≤ orderOf ω := orderOf_pos ω
    interval_cases orderOf ω
    · exact absurd rfl hne
    · omega
    · rfl
  exact hord ▸ IsPrimitiveRoot.orderOf ω

private noncomputable def ggQTUbj_delta {n : ℕ} {K : Type} [Field K] [Finite K]
    {X L : Subgroup G} {x : G} (C : GGQTwoXInLUCoord Bs X L x n K) (b : G) :
    Fin (n + 1) → Kˣ := by
  classical
  exact fun i => if h : b ∈ Bs then
    C.ω ^ (((C.ι (Additive.ofMul ⟨b, h⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i).val
  else 1

omit [Finite G] in
private lemma ggQTUbj_delta_of_mem {n : ℕ} {K : Type} [Field K] [Finite K]
    {X L : Subgroup G} {x : G} (C : GGQTwoXInLUCoord Bs X L x n K) {b : G} (hb : b ∈ Bs) :
    ggQTUbj_delta C b = fun i =>
      C.ω ^ (((C.ι (Additive.ofMul ⟨b, hb⟩) : ↥(GGQTwoXInLAug n)) :
        Fin (n + 1) → ZMod 3) i).val := by
  funext i
  simp only [ggQTUbj_delta, dif_pos hb]

omit [Finite G] in
private lemma ggQTUbj_pair {n : ℕ} {K : Type} [Field K] [Finite K]
    {X L : Subgroup G} {x : G} (C : GGQTwoXInLUCoord Bs X L x n K) (b : ↥Bs) :
    ((b : G), diagHom (n + 1) (ggQTUbj_delta C (b : G))) ∈ SUTorus.suPairs C.φ := by
  obtain ⟨s, hs, hφ⟩ := C.diag b
  rw [ggQTUbj_delta_of_mem C b.2]
  refine SUTorus.mem_suPairs.mpr ⟨?_, ?_⟩
  · rw [← hs]
    exact Subgroup.le_normalizer s.2
  · intro u v hv
    have hsuv : s * u * s⁻¹ = v := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hv, hs])
    calc (b : G) * C.φ u * (b : G)⁻¹ = C.φ s * C.φ u * (C.φ s)⁻¹ := by rw [← hφ]
      _ = C.φ (s * u * s⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = C.φ v := by rw [hsuv]

omit [Finite G] in
private lemma ggQTUbj_four_le_card {n : ℕ} {K : Type} [Field K] [Finite K]
    {X L : Subgroup G} {x : G} (C : GGQTwoXInLUCoord Bs X L x n K)
    {D J : Subgroup G} {δ : G → Fin (n + 1) → Kˣ}
    (hJcomp : IsComponentOf J (C.φ.range ⊓ Subgroup.centralizer (D : Set G)))
    {i : Fin (n + 1)}
    (hJi : J ≤ (TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass (D : Set G) δ i)).map C.φ) :
    4 ≤ (LinTorus.diagClass (D : Set G) δ i).card := by
  classical
  set S := LinTorus.diagClass (D : Set G) δ i
  have hiS : i ∈ S := LinTorus.self_mem_diagClass _ _ i
  by_contra hlt
  have hk1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hiS⟩
  have hk3 : S.card ≤ 3 := by omega
  have : Group.IsSolvable ↥(unitarySU 2 1 K S.card) :=
    WitSU.isSolvable_unitarySU_two_one C.field hk1 hk3
  let eI := TableBUE.blockSUEquiv (K := K) (n := 1) S C.field
  have : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) S) :=
    Group.isSolvable_of_isSolvable_injective (f := eI.symm.toMonoidHom)
      (fun x y hxy => eI.symm.injective hxy)
  have hsolv : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) S).map C.φ) := by
    have hres := Group.isSolvable_of_surjective
      (f := (C.φ.comp (TableBUE.blockSU (K := K) (n := 1) S).subtype).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hres
  have := hsolv
  have hsolvJ : Group.IsSolvable ↥J := by
    let eJ := Subgroup.subgroupOfEquivOfLe hJi
    have : Group.IsSolvable ↥(J.subgroupOf
        ((TableBUE.blockSU (K := K) (n := 1) S).map C.φ)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (J.subgroupOf ((TableBUE.blockSU (K := K) (n := 1) S).map C.φ)).subtype)
        (fun x y hxy => Subtype.ext hxy)
    exact Group.isSolvable_of_surjective (f := eJ.toMonoidHom) (fun z => ⟨eJ.symm z, by simp⟩)
  have : Group.IsPerfect ↥J := ⟨hJcomp.2.2.1⟩
  have : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJcomp.2.2
  exact Group.IsPerfect.not_isSolvable ↥J hsolvJ

private lemma ggQTUbj_omega_pow_val_injective {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 1 K) (ω : Kˣ) (hω : ω ≠ 1) :
    ∀ a b : ZMod 3, ω ^ a.val = ω ^ b.val → a = b := by
  classical
  have hcardU : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hω3 : ω ^ 3 = 1 := by
    have h' := pow_card_eq_one' (x := ω)
    rwa [hcardU] at h'
  have ho : orderOf ω = 3 := orderOf_eq_prime hω3 hω
  intro a b hab
  rw [pow_eq_pow_iff_modEq, ho] at hab
  have hval : a.val = b.val :=
    Nat.ModEq.eq_of_lt_of_lt hab (ZMod.val_lt a) (ZMod.val_lt b)
  exact ZMod.val_injective 3 hval

omit [Finite G] in
private lemma ggQTUbj_coord_eq {n : ℕ} {K : Type} [Field K] [Finite K]
    {X L : Subgroup G} {x : G} (C : GGQTwoXInLUCoord Bs X L x n K) {b : ↥Bs}
    {i j : Fin (n + 1)} (h : ggQTUbj_delta C (b : G) i = ggQTUbj_delta C (b : G) j) :
    ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
      ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) j := by
  rw [ggQTUbj_delta_of_mem C b.2] at h
  exact ggQTUbj_omega_pow_val_injective C.field C.ω C.ω_ne_one _ _ h

theorem ggQTwoXInLU_blockJ {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI : GGQTwoI1 Bs D J) (hn3 : 3 ∣ n) (hn6 : 6 ≤ n)
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) :
    ∃ S : Finset (Fin (n + 1)), 0 ∉ S ∧
      J = (TableBUE.blockSU (K := K) (n := 1) S).map C.φ ∧
      ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i ∈ S, ∀ j ∈ S,
        ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
          ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) j := by
  classical
  have _ : 3 ∣ n := hn3
  have _ : 6 ≤ n := hn6
  have hp : Nat.Prime 3 := by norm_num
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hstdsub : CFSG.Assembly.LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hBstar : GGBstar 3 B Bs := hcfg.2.1
  have hDB : D ≤ B := hstdsub.1.1
  have hBBs : B ≤ Bs := hBstar.1
  have hDBs : D ≤ Bs := hDB.trans hBBs
  have hxD : x ∈ D := hstdsub.1.2.2.2.1
  have hxBs : x ∈ Bs := hBBs hSstar.2.1
  have hδ : ∀ b ∈ Bs, ((b : G), diagHom (n + 1) (ggQTUbj_delta C b)) ∈ SUTorus.suPairs C.φ :=
    fun b hb => ggQTUbj_pair C ⟨b, hb⟩
  have hδD : ∀ e ∈ (D : Set G), (e, diagHom (n + 1) (ggQTUbj_delta C e)) ∈
      SUTorus.suPairs C.φ := fun e he => hδ e (hDBs he)
  have hJ0 := ggQ2_isComponentOf_jointCentralizer hS
  have hJ : IsComponentOf J (C.φ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rwa [← C.range_eq] at hJ0
  obtain ⟨i, hJi⟩ := SUTorus.exists_le_map_blockSU (m := n) (f := 1) C.field (p := 3) hp
    (by norm_num) C.ker_le hδD hJ
  set S := LinTorus.diagClass (D : Set G) (ggQTUbj_delta C) i
  have hS4 : 4 ≤ S.card := ggQTUbj_four_le_card C hJ hJi
  have hS3 : 3 ≤ S.card := by omega
  have hSq : (S.card, 2 ^ 1) ≠ (3, 2) := by
    intro hc
    have h1 := congrArg Prod.fst hc
    omega
  have hsubB : IsSubnormal ((TableBUE.blockSU (K := K) (n := 1) S).map C.φ)
      (C.φ.range ⊓ Subgroup.centralizer (D : Set G)) :=
    SUTorus.isSubnormal_map_blockSU (ψ := C.φ) C.ker_le hδD i
  have hqB : CFSG.Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := K) (n := 1) S).map C.φ) :=
    SUTorus.isQuasisimple_map_blockSU (f := 1) C.field (ψ := C.φ) C.ker_le hS3 hSq
  have hBcomp : IsComponentOf ((TableBUE.blockSU (K := K) (n := 1) S).map C.φ)
      (C.φ.range ⊓ Subgroup.centralizer (D : Set G)) :=
    ⟨isSubnormal_le_of_assembly hsubB, hsubB, hqB⟩
  have hJB : J = (TableBUE.blockSU (K := K) (n := 1) S).map C.φ := by
    rcases isComponentOf_le_or_commutator_eq_bot hBcomp hJ.2.1 with h | h
    · exact le_antisymm hJi h
    · exfalso
      apply commutator_ne_bot_of_isQuasisimple hJ.2.2
      exact le_bot_iff.1 ((Subgroup.commutator_mono hJi le_rfl).trans h.le)
  have hxarg : (⟨x, hxBs⟩ : ↥Bs) = ⟨x, C.mem_x⟩ := Subtype.ext rfl
  have hxcoord : (fun t => ((C.ι (Additive.ofMul ⟨x, hxBs⟩) :
      ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) t) =
      fun t => if t = 0 then 0 else -1 := by
    rw [show (((C.ι (Additive.ofMul ⟨x, hxBs⟩) : ↥(GGQTwoXInLAug n)) :
        Fin (n + 1) → ZMod 3)) =
      (((C.ι (Additive.ofMul ⟨x, C.mem_x⟩) : ↥(GGQTwoXInLAug n)) :
        Fin (n + 1) → ZMod 3)) from by rw [hxarg]]
    exact C.ι_x
  have hωprim : IsPrimitiveRoot C.ω 3 := ggQTUbj_omega_primitive C.field C.ω_ne_one
  have hdelta_x0 : ggQTUbj_delta C x 0 = 1 := by
    rw [ggQTUbj_delta_of_mem C hxBs]
    simp [hxcoord]
  have hdelta_xne : ∀ k : Fin (n + 1), k ≠ 0 → ggQTUbj_delta C x k = C.ω ^ (2 : ℕ) := by
    intro k hk
    rw [ggQTUbj_delta_of_mem C hxBs]
    have h1 : ((C.ι (Additive.ofMul ⟨x, hxBs⟩) : ↥(GGQTwoXInLAug n)) :
        Fin (n + 1) → ZMod 3) k = -1 := by
      rw [show (((C.ι (Additive.ofMul ⟨x, hxBs⟩) : ↥(GGQTwoXInLAug n)) :
          Fin (n + 1) → ZMod 3)) =
        (((C.ι (Additive.ofMul ⟨x, C.mem_x⟩) : ↥(GGQTwoXInLAug n)) :
          Fin (n + 1) → ZMod 3)) from by rw [hxarg]]
      simp only [C.ι_x]
      simp [hk]
    simp only [h1]
    have hneg : (-1 : ZMod 3).val = 2 := by decide
    rw [hneg]
  have h0S : (0 : Fin (n + 1)) ∉ S := by
    intro h0
    by_cases hi0 : i = 0
    ·
      have hSsingle : S = {0} := by
        ext k
        constructor
        · intro hk
          by_contra hk0
          have heq : ggQTUbj_delta C x k = ggQTUbj_delta C x i :=
            (LinTorus.mem_diagClass.mp hk) x hxD
          rw [hi0, hdelta_x0, hdelta_xne k (by simpa using hk0)] at heq
          have h2 : 3 ∣ 2 := (hωprim.pow_eq_one_iff_dvd 2).mp heq
          omega
        · intro hk
          rw [Finset.mem_singleton] at hk
          rw [hk, ← hi0]
          exact LinTorus.self_mem_diagClass _ _ i
      have hJbot : J = ⊥ := by
        have h := hJi
        rw [hSsingle, SUTorus.blockSU_singleton C.field, Subgroup.map_bot] at h
        exact le_bot_iff.mp h
      exact commutator_ne_bot_of_isQuasisimple hJ.2.2 (by simp [hJbot])
    · have heq : ggQTUbj_delta C x 0 = ggQTUbj_delta C x i :=
        (LinTorus.mem_diagClass.mp h0) x hxD
      rw [hdelta_x0, hdelta_xne i hi0] at heq
      have h2 : 3 ∣ 2 := (hωprim.pow_eq_one_iff_dvd 2).mp heq.symm
      omega
  refine ⟨S, h0S, hJB, ?_⟩
  intro b
  constructor
  · intro hbD i hi j hj
    exact ggQTUbj_coord_eq C (LinTorus.eq_of_mem_diagClass hi hj hbD)
  · intro hconst
    apply hI (b : G) b.2
    intro j hj
    have hd : ∀ i ∈ S, ∀ j ∈ S, ggQTUbj_delta C (b : G) i = ggQTUbj_delta C (b : G) j := by
      intro i hi j hj
      rw [ggQTUbj_delta_of_mem C b.2]
      exact congrArg (fun z : ZMod 3 => C.ω ^ z.val) (hconst i hi j hj)
    have hcent : (b : G) ∈ Subgroup.centralizer
        (((TableBUE.blockSU (K := K) (n := 1) S).map C.φ : Subgroup G) : Set G) :=
      SUTorus.mem_centralizer_map_blockSU (ψ := C.φ) (ggQTUbj_pair C b) hd
    rw [← hJB] at hcent
    exact (Subgroup.mem_centralizer_iff.mp hcent j hj).symm

end CFSG.StandardType

end
