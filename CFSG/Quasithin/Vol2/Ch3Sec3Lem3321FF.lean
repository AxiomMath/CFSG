module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GExt

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)}

theorem inf_centralizer_eq_of_model (h9 : Stmt3_3_9) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hD : FData G T M L D α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {Z₀ : Subgroup ↥(vPlus L T)}
    (D₀ : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) Z₀
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = liftPre α P2 := by
  obtain ⟨hML, -⟩ := h14 G T M L D h
  have hVe := (Hyp331.vPlus_reduced h.toSetup331).2.1
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  have hαs := hD.surj
  have hαU := hD.mapU
  have hP2C :
      liftPre α P2 ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_centralizer_of_fix h9 h hML l.2 fun v hvZ hvW => ?_
    have hvc : v ∈ commV (autOn L (vPlus L T)) := by
      rw [Ln2.commV_autOn_eq h]
      exact hvW
    have hfixU : ∀ s ∈ FLc.Ut 4, ρ s v = v := by
      intro s hs
      rw [← hαU] at hs
      obtain ⟨t', ht', rfl⟩ := hs
      rw [hαv]
      exact fix_of_mem_autOn_inf (FLc.mem_autOn_iff.2 ⟨(t' : G), L3317.le_normalizer_vPlus h t'.2,
        Subgroup.mem_subgroupOf.1 ht', rfl⟩) hvZ
    have key := FLc.fixQ_of_model D₀ hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => FLc.fix_extSq4 a ha i hi hic) hvc hfixU (α l) hl
    rw [hαv l] at key
    exact key
  set Pz : Subgroup SL4 :=
    ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).subgroupOf L).map α with hPz
  have hUPz : FLc.Ut 4 ≤ Pz := by
    rw [← hαU]
    refine Subgroup.map_mono (Subgroup.subgroupOf_mono L fun t ht => ⟨ht.2, ?_⟩)
    exact CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1
  have hP2Pz : P2 ≤ Pz := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hP2C ⟨l, hg, rfl⟩), rfl⟩
  have hkerC : ∀ l : ↥L, α l = 1 →
      (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    refine mem_centralizer_of_fix h9 h hML l.2 fun v _ _ => ?_
    have key := hαv l
    rw [hl, map_one] at key
    rw [← key, MulAut.one_apply]
  have hcuts : FLc.cuts Pz = {2} := by
    have h1 : FLc.cuts Pz ⊆ {2} := by
      have := hP2Pz
      rw [FLc.eq_QI_cuts hUPz] at this
      exact (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).1 this
    refine Set.Subset.antisymm h1 fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    by_contra h2
    have hempty : FLc.cuts Pz = ∅ := by
      ext j
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hj
      have := h1 hj
      rw [Set.mem_singleton_iff] at this
      subst this
      exact h2 hj
    apply inf_centralizer_ne hML e
    intro l hl
    have hlPz : α ⟨l, hl⟩ ∈ Pz := by
      rw [FLc.eq_QI_cuts hUPz, hempty]
      show α ⟨l, hl⟩ ∈ flagStabilizer 4 (ZMod 2) ∅
      rw [flagStabilizer_empty]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := hlPz
    have h3 := hkerC (c⁻¹ * ⟨l, hl⟩) (by rw [map_mul, map_inv, hcl, inv_mul_cancel])
    have h4 : (c : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mem_subgroupOf.1 hc
    have e1 : l = (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e1]
    exact (Subgroup.mul_mem _ h4 h3).2
  have hPzeq : Pz = P2 := by
    rw [FLc.eq_QI_cuts hUPz, hcuts]
  refine le_antisymm (fun x hx => ?_) hP2C
  have h1 : α ⟨x, hx.1⟩ ∈ Pz := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hPzeq] at h1
  exact ⟨⟨x, hx.1⟩, h1, rfl⟩

theorem vPlus_le_T (h : Hyp331 G T M L D) : vPlus L T ≤ T :=
  ((Hyp331.vPlus_reduced h.toSetup331).1.trans inf_le_left).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf)

theorem exists_mem_center_of_ne_bot {U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ v ∈ U, v ≠ 1 ∧ v ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h1
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h1, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := Subgroup.mem_inf.1 hy
  refine ⟨y, Subgroup.mem_subgroupOf.1 hyU, fun h1 => hy1 (Subtype.ext (Subtype.ext h1)),
    Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hyZ ⟨t, ht⟩)

theorem vPlus_inf_centralizer_eq_bot (he : Step3_3_21e) (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hmod : Mod3321 T L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    vPlus L T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hVe := (Hyp331.vPlus_reduced h.toSetup331).2.1
  have hTV := Hyp331.le_normalizer_vPlus L T
  have hUn : T ≤ Subgroup.normalizer
      ((vPlus L T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_inf (hTV ht) (mem_normalizer_centralizer (hTL ht))
  obtain ⟨v, hv, hv1, hvC⟩ := exists_mem_center_of_ne_bot h.sylow.1
    (inf_le_left.trans (vPlus_le_T h)) hUn hne
  have hvZ : v ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨vPlus_le_T h hv.1, hvC⟩, hVe.2 v hv.1⟩
  have h1 : v ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hvZ, hv.2⟩
  rw [he G T M L D h e hmod, Subgroup.mem_bot] at h1
  exact hv1 h1

theorem eq_bot_of_le_fixV [IsMulCommutative ↥(vPlus L T)] (h : Hyp331 G T M L D)
    (hVL : vPlus L T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {Z₀ : Subgroup ↥(vPlus L T)}
    (hZ₀ : Z₀ ≤ fixV (autOn L (vPlus L T))) : Z₀ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzC : (z : G) ∈ vPlus L T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have h1 := hZ₀ hz (conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h hl⟩)
      (FLc.mem_autOn_iff.2 ⟨l, _, hl, rfl⟩)
    have h2 := congrArg Subtype.val h1
    rw [FLc.conjAct_coe] at h2
    calc l * (z : G) = (l * z * l⁻¹) * l := by group
      _ = z * l := by rw [h2]
  rw [hVL, Subgroup.mem_bot] at hzC
  exact Subgroup.mem_bot.2 (Subtype.ext hzC)

omit [Finite G] in
theorem card_vPlus [IsMulCommutative ↥(vPlus L T)]
    (hcomm : commV (autOn L (vPlus L T)) = ⊤)
    (D₀ : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) ⊥
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    Nat.card ↥(vPlus L T) = 64 := by
  have h1 : Nat.card ↥(commV (autOn L (vPlus L T))) = 2 ^ 6 := by
    rw [← FLc.card_X_ext4]
    exact Nat.card_congr (Equiv.ofBijective D₀.β ⟨FLc.VModel.β_injective D₀, D₀.surj⟩)
  rw [hcomm, Subgroup.card_top] at h1
  rw [h1]
  norm_num

theorem vPlus_le_L (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : ⁅vPlus L T, L⁆ = vPlus L T) : vPlus L T ≤ L := by
  rw [← hV]
  exact Ch3Sec3.commutator_le_right_of_le_normalizer ((vPlus_le_T h).trans hTL)

theorem le_L (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (hD : FData G T M L D α)
    (hfQ : pCoreOf 2 (L ⊔ T) = vPlus L T) (hVL : vPlus L T ≤ L) : T ≤ L := by
  obtain ⟨hML, -⟩ := h14 G T M L D hD.hyp
  intro t ht
  obtain ⟨y, hyU, hy⟩ := hD.exists_conj ht
  have hyU' := hyU
  rw [← hD.mapU] at hyU'
  obtain ⟨s, hs, hse⟩ := hyU'
  have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
  set c : G := (s : G)⁻¹ * t with hc
  have hcT : c ∈ T := T.mul_mem (T.inv_mem hs'.1) ht
  have hcL : ∀ l : ↥L, ∃ k : ↥L, α k = 1 ∧ c * (l : G) * c⁻¹ = k * l := by
    intro l
    have hx : t * (l : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) l).mp l.2
    let m : ↥L := s⁻¹ * ⟨t * l * t⁻¹, hx⟩ * s
    have hm : (m : G) = c * l * c⁻¹ := by
      show (s : G)⁻¹ * (t * l * t⁻¹) * s = c * l * c⁻¹
      rw [hc]
      group
    refine ⟨m * l⁻¹, ?_, by rw [Subgroup.coe_mul, Subgroup.coe_inv, hm]; group⟩
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hy l hx, hse]
    group
  have hcV : c ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    have hle : vPlus L T ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (vPlus_le_conjClosure hML).trans (conjClosure_le fun l hl z hz => ?_)
      obtain ⟨k, hk1, hk⟩ := hcL ⟨l, hl⟩
      have hkV : (k : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := (hD.kerV k).1 hk1
      have hlz : l * z * l⁻¹ ∈ vPlus L T := by
        show l * z * l⁻¹ ∈ conjClosure (quasithinOmegaOneCenter T) (mPlus L T)
        rw [hML]
        exact Subgroup.subset_closure ⟨l, hl, z, hz, rfl⟩
      have hcz := conj_omegaOneCenter hcT hz
      have h1 : c * (l * z * l⁻¹) * c⁻¹ = l * z * l⁻¹ := by
        have e1 : c * (l * z * l⁻¹) * c⁻¹ =
            (c * l * c⁻¹) * (c * z * c⁻¹) * (c * l * c⁻¹)⁻¹ := by group
        rw [e1, hcz, hk]
        have h2 := Subgroup.mem_centralizer_iff.1 hkV _ hlz
        calc (k : G) * l * z * ((k : G) * l)⁻¹ = ((k : G) * (l * z * l⁻¹)) * (k : G)⁻¹ := by
              group
          _ = ((l * z * l⁻¹) * k) * (k : G)⁻¹ := by rw [← h2]
          _ = l * z * l⁻¹ := by group
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * z * l⁻¹ * c = (c * (l * z * l⁻¹) * c⁻¹) * c := by rw [h1]
        _ = c * (l * z * l⁻¹) := by group
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle hv))
  obtain ⟨⟨-, hCT⟩, -⟩ := h7 G T M L D hD.hyp
  rw [hML] at hCT
  have hcO : c ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← hCT]
    exact ⟨hcT, hcV⟩
  rw [hfQ] at hcO
  have : t = s * c := by rw [hc]; group
  rw [this]
  exact L.mul_mem hs'.2 (hVL hcO)

theorem card_le (hD : FData G T M L D α) (hTL : T ≤ L) (hfQ : pCoreOf 2 (L ⊔ T) = vPlus L T)
    (hV : Nat.card ↥(vPlus L T) = 64) : Nat.card ↥T ≤ 2 ^ 12 := by
  rw [card_eq_mul hD.ker hTL]
  have h1 : Nat.card ↥(T ⊓ pCoreOf 2 L) ≤ 64 := by
    rw [← hV]
    refine Subgroup.card_le_of_le (inf_le_right.trans ?_)
    rw [← hfQ]
    exact hD.pCoreOf_L_le le_rfl
  have h2 : Nat.card ↥(α.comp (Subgroup.inclusion hTL)).range ≤ 64 := by
    have hU : Nat.card ↥(FLc.Ut 4) = 64 := by
      have := card_unitriangular (K := ZMod 2) 4
      rw [Nat.card_zmod] at this
      simpa using this
    rw [← hU]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨t, rfl⟩
    exact hD.mem_Ut _ t.2
  calc Nat.card ↥(T ⊓ pCoreOf 2 L) * Nat.card ↥(α.comp (Subgroup.inclusion hTL)).range
      ≤ 64 * 64 := Nat.mul_le_mul h1 h2
    _ = 2 ^ 12 := by norm_num

end CFSG.Quasithin.H13.L3321
