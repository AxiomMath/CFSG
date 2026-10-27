module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Tr
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem527U4
import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528STr
import CFSG.Quasithin.H13.U4ParOuterFacts
public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Transport

theorem eq_map_subtype_top {X : Type} [Group X] (A : Subgroup X) :
    A = (⊤ : Subgroup ↥A).map A.subtype := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {G : Type} [Group G] {Y : Type} [Group Y] {G' : Subgroup G} {M : Subgroup Y}

theorem eq_map_comp_top (e : ↥G' ≃* ↥M) :
    M = (⊤ : Subgroup ↥G').map (M.subtype.comp e.toMonoidHom) := by
  rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem pCoreOf_eq_of_equiv (e : ↥G' ≃* ↥M) (h : pCoreOf 2 M = pCoreOf 2 (perfectCore M)) :
    pCoreOf 2 G' = pCoreOf 2 (perfectCore G') := by
  obtain ⟨K', -, -, hQg, hQf, -, -⟩ := model_data e
  have hg : Function.Injective G'.subtype := G'.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have h1 := U4Par.pCoreOf_map_of_inj hg 2 (⊤ : Subgroup ↥G')
  have h2 := U4Par.pCoreOf_map_of_inj hf 2 (⊤ : Subgroup ↥G')
  rw [← eq_map_subtype_top G'] at h1
  rw [← eq_map_comp_top e] at h2
  rw [h2, hQf] at h
  rw [h1, hQg, Subgroup.map_injective hf h]

theorem mem_pCoreOf_perfectCore_iff_of_equiv (e : ↥G' ≃* ↥M) (g : ↥G') :
    (g : G) ∈ pCoreOf 2 (perfectCore G') ↔ ((e g : ↥M) : Y) ∈ pCoreOf 2 (perfectCore M) := by
  obtain ⟨K', -, -, hQg, hQf, -, -⟩ := model_data e
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  rw [hQg, hQf]
  exact (Subgroup.mem_map_iff_mem G'.subtype_injective).trans (Subgroup.mem_map_iff_mem hf).symm

theorem pCoreOf_sup_zpowers_of_equiv (e : ↥G' ≃* ↥M) {S : Subgroup G} (hS : S ≤ G') (t : ↥G')
    (h : pCoreOf 2 (perfectCore M ⊔ (S.subgroupOf G').map (M.subtype.comp e.toMonoidHom)) =
      pCoreOf 2 (perfectCore M) ⊔ Subgroup.zpowers ((e t : ↥M) : Y)) :
    pCoreOf 2 (perfectCore G' ⊔ S) = pCoreOf 2 (perfectCore G') ⊔ Subgroup.zpowers (t : G) := by
  obtain ⟨K', hKg, hKf, hQg, hQf, -, -⟩ := model_data e
  have hg : Function.Injective G'.subtype := G'.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hSg : S = (S.subgroupOf G').map G'.subtype := (Subgroup.map_subgroupOf_eq_of_le hS).symm
  have ht : ((e t : ↥M) : Y) = (M.subtype.comp e.toMonoidHom) t := rfl
  rw [hQf, hKf, ← Subgroup.map_sup, U4Par.pCoreOf_map_of_inj hf, ht,
    ← MonoidHom.map_zpowers, ← Subgroup.map_sup] at h
  have h' := Subgroup.map_injective hf h
  have htg : (t : G) = G'.subtype t := rfl
  rw [hQg, hKg, htg, ← MonoidHom.map_zpowers, ← Subgroup.map_sup]
  conv_lhs => rw [hSg]
  rw [← Subgroup.map_sup, U4Par.pCoreOf_map_of_inj hg, h']

theorem inf_centralizer_equiv (e : ↥G' ≃* ↥M) (t : ↥G') :
    Nonempty (↥(perfectCore G' ⊓ Subgroup.centralizer ({(t : G)} : Set G)) ≃*
      ↥(perfectCore M ⊓ Subgroup.centralizer ({((e t : ↥M) : Y)} : Set Y))) := by
  obtain ⟨K', hKg, hKf, -, -, -, -⟩ := model_data e
  have hg : Function.Injective G'.subtype := G'.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  set C := K' ⊓ Subgroup.centralizer ({t} : Set ↥G') with hC
  have e1 : perfectCore G' ⊓ Subgroup.centralizer ({(t : G)} : Set G) = C.map G'.subtype := by
    rw [hC, U4Par.map_inf_centralizer_singleton hg, ← hKg]
    rfl
  have e2 : perfectCore M ⊓ Subgroup.centralizer ({((e t : ↥M) : Y)} : Set Y) =
      C.map (M.subtype.comp e.toMonoidHom) := by
    rw [hC, U4Par.map_inf_centralizer_singleton hf, ← hKf]
    rfl
  exact ⟨(MulEquiv.subgroupCongr e1).trans ((C.equivMapOfInjective _ hg).symm.trans
    ((C.equivMapOfInjective _ hf).trans (MulEquiv.subgroupCongr e2.symm)))⟩

theorem isSylowTwoOf_map_equiv {X : Subgroup G} {X' : Subgroup Y} (e : ↥X ≃* ↥X')
    {S : Subgroup G} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf ((S.subgroupOf X).map (X'.subtype.comp e.toMonoidHom)) X' := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (e s).2
  · have h1 : IsPGroup 2 ↥(S.subgroupOf X) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact h1.map _
  · have e1 : ((S.subgroupOf X).map (X'.subtype.comp e.toMonoidHom)).subgroupOf X' =
        (S.subgroupOf X).map (e : ↥X →* ↥X') := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.coe_comp,
        Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MonoidHom.coe_ofClass]
      constructor
      · rintro ⟨s, hs, hsy⟩
        exact ⟨s, hs, Subtype.ext hsy⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
    show ¬ 2 ∣ (((S.subgroupOf X).map (X'.subtype.comp e.toMonoidHom)).subgroupOf X').index
    rw [e1, Subgroup.index_map_equiv]
    exact hS.2.2

end Transport

section Amalgam

open F1

variable {X Y : Type} [Group X] [Group Y] {G₁ G₂ : Subgroup X} {M₁ M₂ : Subgroup Y}
  (Φ : (RankTwoAmalgam.ofSubgroups G₁ G₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))

theorem map_subgroupOf_isoφ2 {S : Subgroup X} (hS : S ≤ G₁) :
    (S.subgroupOf G₂).map (M₂.subtype.comp (isoφ2 Φ).toMonoidHom) =
      (S.subgroupOf (G₁ ⊓ G₂)).map ((M₁ ⊓ M₂).subtype.comp (isoφ12 Φ).toMonoidHom) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Subgroup.mem_inf.mpr ⟨hS ha, a.2⟩⟩, ha, coe_isoφ12_eq_φ2 Φ _⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, (Subgroup.mem_inf.mp b.2).2⟩, hb, (coe_isoφ12_eq_φ2 Φ b).symm⟩

theorem le_centralizer_of_isoφ12_mem_center (x : ↥(G₁ ⊓ G₂))
    (hx : ((isoφ12 Φ x : ↥(M₁ ⊓ M₂)) : Y) ∈ Subgroup.center Y) :
    G₁ ⊔ G₂ ≤ Subgroup.centralizer ({(x : X)} : Set X) := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [coe_isoφ12_eq_φ1] at hx
    have e1 : (⟨g, hg⟩ : ↥G₁) * ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ =
        ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ * ⟨g, hg⟩ := by
      apply (isoφ1 Φ).injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp hx _
    exact congrArg Subtype.val e1
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [coe_isoφ12_eq_φ2] at hx
    have e1 : (⟨g, hg⟩ : ↥G₂) * ⟨x, (Subgroup.mem_inf.mp x.2).2⟩ =
        ⟨x, (Subgroup.mem_inf.mp x.2).2⟩ * ⟨g, hg⟩ := by
      apply (isoφ2 Φ).injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp hx _
    exact congrArg Subtype.val e1

end Amalgam

theorem mem_pCoreOf_of_le_centralizer {G : Type} [Group G] [Finite G] {X : Subgroup G} {w : G}
    (hw : w ∈ X) (hw2 : w * w = 1) (hX : X ≤ Subgroup.centralizer ({w} : Set G)) :
    w ∈ pCoreOf 2 X := by
  have hle : Subgroup.zpowers w ≤ X := Subgroup.zpowers_le.mpr hw
  have hp : IsPGroup 2 ↥(Subgroup.zpowers w) :=
    isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one, pow_two, hw2])
  have hnorm : ((Subgroup.zpowers w).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute (g : G) w := Subgroup.mem_centralizer_singleton_iff.mp (hX g.2)
    have e : ((g * n * g⁻¹ : ↥X) : G) = n := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, (hc.zpow_right k).eq,
        mul_inv_cancel_right]
    rw [e]
    exact hn⟩
  exact le_pCoreOf 2 hle hnorm hp (Subgroup.mem_zpowers w)

namespace U4Ext

theorem mem_center_of_mem_centralizer_range {Ŷ : Type} [Group Ŷ] {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {ψ : hypSU h 2 0 →* Ŷ} (hψ : Function.Injective ψ)
    (hidx : ψ.range.index = 2) {z : Ŷ} (hz : z ∈ Subgroup.centralizer (ψ.range : Set Ŷ)) :
    z * z = 1 ∧ z ∈ Subgroup.center Ŷ := by
  have hZ : Subgroup.center (hypSU h 2 0) = ⊥ := by
    have := U4Par.isSimpleGroup_hypSU h
    obtain ⟨a, -, b, -, hab⟩ := U4Par.exists_radQ_ne_comm h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (hypSU h 2 0)) with h0 | h0
    · exact h0
    · have ha : a ∈ Subgroup.center (hypSU h 2 0) := h0 ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  have hRC : ∀ y ∈ ψ.range, y ∈ Subgroup.centralizer (ψ.range : Set Ŷ) → y = 1 := by
    rintro _ ⟨g, rfl⟩ hg
    have hgZ : g ∈ Subgroup.center (hypSU h 2 0) := Subgroup.mem_center_iff.mpr fun g' =>
      hψ (by rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_iff.mp hg (ψ g') ⟨g', rfl⟩)
    rw [hZ, Subgroup.mem_bot] at hgZ
    rw [hgZ, map_one]
  have hz2 : z * z = 1 :=
    hRC _ (Subgroup.mul_self_mem_of_index_two hidx z) ((Subgroup.centralizer _).mul_mem hz hz)
  refine ⟨hz2, Subgroup.mem_center_iff.mpr fun y => ?_⟩
  by_cases hzR : z ∈ ψ.range
  · rw [hRC z hzR hz, mul_one, one_mul]
  · by_cases hyR : y ∈ ψ.range
    · exact Subgroup.mem_centralizer_iff.mp hz y hyR
    · have hr : z⁻¹ * y ∈ ψ.range := (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h1 => absurd (inv_inv z ▸ ψ.range.inv_mem h1) hzR, fun h1 => absurd h1 hyR⟩
      have hc := Subgroup.mem_centralizer_iff.mp hz _ hr
      calc y * z = z * (z⁻¹ * y) * z := by group
        _ = z * (z * (z⁻¹ * y)) := by rw [mul_assoc, hc]
        _ = z * y := by group

end U4Ext

open F1

theorem stmt5_2_6_U4ext_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hRL : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) :
    Stmt5_2_6_U4ext := by
  intro G _ _ T M L V H B D L₂ n f hyp hf hA _ hsp _ _ _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)
  have h111₀ := hF11 G T M L V H B D L₂ n hyp
  have h111 := Hyp111R.of_hyp111 hRL h111₀
  have hL₂perf : ⁅L₂, L₂⁆ = L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact hK₁.2.1
    · exact hL₂P.2.1
  have hG1core : perfectCore (sec52G1 M L H B L₂) = L := by
    rw [hG1]
    have hAn : (L.subgroupOf (L ⊔ bigB L L₂ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h111).1)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111))
      (le_perfectCore_of_perfect le_sup_left h.commutator_eq)
  have hG2core : perfectCore (sec52G2 M H D L₂) = L₂ := by
    rw [hG2]
    have hAn : (L₂.subgroupOf (L₂ ⊔ bigB L L₂ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h111).2)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111))
      (le_perfectCore_of_perfect le_sup_left hL₂perf)
  have hLG₁ : L ≤ sec52G1 M L H B L₂ := le_sup_left.trans le_sup_left
  have hSG₁ : S ≤ sec52G1 M L H B L₂ := le_sup_right.trans le_sup_left
  have hL₂G₂ : L₂ ≤ sec52G2 M H D L₂ := le_sup_right
  have hSG₂ : S ≤ sec52G2 M H D L₂ := le_sup_right.trans le_sup_left
  obtain ⟨Y₀, _, Yh, _, ι, hY₀, hι, hidx, Th, Mh₁, Mh₂, hpair, ⟨Φ⟩⟩ := hA
  obtain ⟨K', _, hK', ⟨e⟩⟩ := U4Par.exists_hypSU_equiv_of_lieModel hY₀
  have hfin : Finite Yh :=
    (U4Par.exists_embedding (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩)).1
  have hψ₀ : Function.Injective (ι.comp e.toMonoidHom) := hι.comp e.injective
  have hidx₀ : (ι.comp e.toMonoidHom).range.index ≤ 2 := by
    rw [F431.U42.Am.range_comp_mulEquiv, hidx]
  obtain ⟨ψ, hψ, hrange, hU⟩ := U4V.exists_adapted hK' hψ₀ hidx₀ hpair.1
  have hidx2 : ψ.range.index = 2 := by
    rw [hrange, F431.U42.Am.range_comp_mulEquiv]
    exact hidx
  rw [← hrange] at hidx₀ hU
  have hC : Subgroup.centralizer (ψ.range : Set Yh) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hz2, hzc⟩ := U4Ext.mem_center_of_mem_centralizer_range hK' hψ hidx2 hz
    have hzN : z ∈ Subgroup.normalizer (Th : Set Yh) := Subgroup.center_le_normalizer _ hzc
    have hz₁ : z ∈ Mh₁ := ((hpair.2.2 Mh₁).mpr (Or.inl rfl)).2 hzN
    have hz₂ : z ∈ Mh₂ := ((hpair.2.2 Mh₂).mpr (Or.inr rfl)).2 hzN
    obtain ⟨x, hxz⟩ : ∃ x : ↥(sec52G1 M L H B L₂ ⊓ sec52G2 M H D L₂),
        ((isoφ12 Φ x : ↥(Mh₁ ⊓ Mh₂)) : Yh) = z :=
      ⟨(isoφ12 Φ).symm ⟨z, Subgroup.mem_inf.mpr ⟨hz₁, hz₂⟩⟩, by rw [MulEquiv.apply_symm_apply]⟩
    have hx2 : x * x = 1 := (isoφ12 Φ).injective (by
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, hxz, hz2, OneMemClass.coe_one])
    have hcen := le_centralizer_of_isoφ12_mem_center Φ x (by rw [hxz]; exact hzc)
    have hX : L ⊔ L₂ ⊔ S ≤ sec52G1 M L H B L₂ ⊔ sec52G2 M H D L₂ :=
      sup_le (sup_le (hLG₁.trans le_sup_left) (hL₂G₂.trans le_sup_right))
        (hSG₁.trans le_sup_left)
    have hG₁X : sec52G1 M L H B L₂ ≤ L ⊔ L₂ ⊔ S :=
      sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (inf_le_right.trans (le_sup_right.trans le_sup_left))
    have hmem := mem_pCoreOf_of_le_centralizer (hG₁X (Subgroup.mem_inf.mp x.2).1)
      (congrArg Subtype.val hx2) (hX.trans hcen)
    rw [h111₀.o2, Subgroup.mem_bot] at hmem
    rw [← hxz, show x = 1 from Subtype.ext hmem, map_one, OneMemClass.coe_one]
  have hsp₂ : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore Mh₂)) := by
    have hsp' : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
      rw [hG2core]
      exact hsp
    exact isSpecialPow_model (isoφ2 Φ) hsp'
  obtain ⟨hM₂, hM₂ψ, -, -⟩ := U4Par.recog_aux hK' hf ψ hψ hidx₀ hpair hU hsp₂
  obtain ⟨i₁, hM₁N, hM₁R⟩ :=
    U4V.inf_eq_of_adapted hK' ψ hψ hidx₀ (U4V.isYAmalgamPair_swap hpair) hU
  have hM₁ : Mh₁ = Subgroup.normalizer (((U4Par.parP2 hK').map ψ : Subgroup Yh) : Set Yh) ∧
      Mh₁ ⊓ ψ.range = (U4Par.parP2 hK').map ψ := by
    fin_cases i₁
    · exact absurd (hM₁N.trans hM₂.symm) hpair.2.1
    · exact ⟨hM₁N, hM₁R⟩
  have hS12 : IsSylowTwoOf S (sec52G1 M L H B L₂ ⊓ sec52G2 M H D L₂) := by
    rw [hG1, hG2, F1.parabolic_inf_parabolic h111]
    exact F112W.isSylowTwoOf_bigB h111
  obtain ⟨hO1, hO2, tY, htYS, htYo, htYQ, htYsup, F, _, _, hF, P, hP, ⟨eP⟩⟩ :=
    U4Par.ext_facts hK' hf hψ hidx2 hC hpair hU hM₁.1 hM₁.2 hM₂ hM₂ψ
      (isSylowTwoOf_map_equiv (isoφ12 Φ) hS12)
  refine ⟨?_, ?_, ?_⟩
  · rw [pCoreOf_eq_of_equiv (isoφ1 Φ) hO1, hG1core]
  · rw [pCoreOf_eq_of_equiv (isoφ2 Φ) hO2, hG2core]
  obtain ⟨s, -, rfl⟩ := htYS
  have hs₂ : (s : G) ∈ sec52G2 M H D L₂ := (Subgroup.mem_inf.mp s.2).2
  have hts : ((isoφ2 Φ ⟨s, hs₂⟩ : ↥Mh₂) : Yh) =
      ((Mh₁ ⊓ Mh₂).subtype.comp (isoφ12 Φ).toMonoidHom) s :=
    (coe_isoφ12_eq_φ2 Φ s).symm
  refine ⟨(s : G), ?_, ?_, ?_, F, inferInstance, inferInstance, hF, P, hP, ?_⟩
  · rw [← U4Ext.orderOf_coe_equiv (isoφ12 Φ) s]
    exact htYo
  · intro htQ
    apply htYQ
    rw [← hts]
    exact (mem_pCoreOf_perfectCore_iff_of_equiv (isoφ2 Φ) ⟨s, hs₂⟩).mp
      (by rw [hG2core]; exact htQ)
  · have hsup := pCoreOf_sup_zpowers_of_equiv (isoφ2 Φ) hSG₂ ⟨s, hs₂⟩
      (by rw [map_subgroupOf_isoφ2 Φ hSG₁, hts]; exact htYsup)
    rw [hG2core] at hsup
    exact hsup
  · have hne := inf_centralizer_equiv (isoφ2 Φ) ⟨s, hs₂⟩
    rw [hG2core, hts] at hne
    obtain ⟨e₁⟩ := hne
    exact ⟨e₁.trans eP⟩

end CFSG.Quasithin.H13
