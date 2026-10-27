module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4XNat
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape4
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzNatStar

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13 CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

private theorem exists_chiefMod_proj {L L' N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hNL' : N ≤ Subgroup.normalizer (L' : Set G)) (hLL' : L ≤ L') :
    ∃ π : Ch3z.chiefMod L N →* Ch3z.chiefMod L' N,
      π.comp (Ch3z.chiefIota hNL) = Ch3z.chiefIota hNL' := by
  have hker : (Ch3z.chiefIota hNL).ker ≤ (Ch3z.chiefIota hNL').ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [Ch3z.chiefIota_eq_one_iff] at hx ⊢
    exact hLL' hx
  refine ⟨MonoidHom.liftOfRightInverse (Ch3z.chiefIota hNL)
    (Function.surjInv (Ch3z.chiefIota_surjective hNL))
    (Function.rightInverse_surjInv _) ⟨Ch3z.chiefIota hNL', hker⟩, ?_⟩
  ext x
  exact congrArg Subtype.val
    (MonoidHom.liftOfRightInverse_comp_apply (f := Ch3z.chiefIota hNL)
      (f_inv := Function.surjInv (Ch3z.chiefIota_surjective hNL))
      (hf := Function.rightInverse_surjInv _) ⟨Ch3z.chiefIota hNL', hker⟩ x)

private theorem chiefMod_proj_iota {L L' N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hNL' : N ≤ Subgroup.normalizer (L' : Set G)) (hLL' : L ≤ L')
    {π : Ch3z.chiefMod L N →* Ch3z.chiefMod L' N}
    (hπ : π.comp (Ch3z.chiefIota hNL) = Ch3z.chiefIota hNL') (x : ↥N) :
    π (Ch3z.chiefIota hNL x) = Ch3z.chiefIota hNL' x := by
  have h := DFunLike.congr_fun hπ x
  simpa only [MonoidHom.comp_apply] using h

theorem str83G4_x1_le_commutator_sup_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83X1 L1 L2 S ≤ ⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆ ⊔
      Z1 L1 L2 S := by
  classical
  have hxeq := str83G4_x_eq_commutator_sup_z1 hfr d hX hB
  let H : Subgroup G := L1 ⊔ S
  let X : Subgroup G := str83X L1 L2 S
  let X1 : Subgroup G := str83X1 L1 L2 S
  let Z1 : Subgroup G := Z1 L1 L2 S
  let W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have ha : 1 ≤ a := hfr.2.2.1
  letI : Fintype K := Fintype.ofFinite K
  have hZ1X : Z1 ≤ X := str83G4_z1_le_x hfr
  have hZ1X1 : Z1 ≤ X1 := str83G4_z1_le_x1 hfr
  have hHNZ : H ≤ Subgroup.normalizer (X : Set G) := str83G4_sup_le_normalizer_x hfr
  have hHLZ : H ≤ Subgroup.normalizer (Z1 : Set G) := str83G4_sup_le_normalizer_z1 hfr
  have hXleCZ : X ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (B6.isElemAbelian_iff.mp hX).1 z (hZ1X hz) x hx
  have hNLZ : X ≤ Subgroup.normalizer (Z1 : Set G) :=
    hXleCZ.trans (Subgroup.centralizer_le_normalizer _)
  have hXleCX1 : X ≤ Subgroup.centralizer (X1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (B6.isElemAbelian_iff.mp hX).1 z (str83G4_x1_le_x L1 L2 S hz) x hx
  have hNL1 : X ≤ Subgroup.normalizer (X1 : Set G) :=
    hXleCX1.trans (Subgroup.centralizer_le_normalizer _)
  have hstep1 : IsChiefStep H X X1 X := str83G4_isChiefStep_x1_x hfr d hX hB
  have hnc1 : ¬ twoResidual H ≤ centralizerMod X1 H X :=
    str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB
  obtain ⟨hHL1, hHN1, hNL1', hE1, hO1, e, he, hnt1⟩ :=
    str83G4_exists_sectionSetup hfr hstep1 hZ1X1 hnc1
  have hC : ∀ s : G, s ∈ W ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S :=
    str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB
  have hquad : ⁅⁅X, W⁆, W⁆ = ⊥ := by
    simpa [X, W] using str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX
  letI : CommGroup (Ch3z.chiefMod X1 X) := l2ChiefSectionCommGroup hE1
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod X1 X)) := l2ChiefSectionModule hE1
  let ρ1 : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod X1 X)) :=
    sectionRep hHL1 hHN1 hNL1' hE1 hO1 e
  have hnat1 : IsSzNatural ρ1 :=
    sectionRep_isSzNatural_of_quadratic hfr hC hquad hstep1 hHL1 hHN1 hNL1' hE1 hO1 e he hnt1
  have hEZ : IsElemAbelian 2 (Ch3z.chiefMod Z1 X) := by
    refine isElemAbelian_secImg_normalizer ?_ ?_
    · intro x hx y hy
      have hxy : x * y = y * x := (B6.isElemAbelian_iff.mp hX).1 x hx y hy
      have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [hxy]
        group
      rw [h1]
      exact Z1.one_mem
    · intro x hx
      have h2 : x ^ 2 = 1 := (B6.isElemAbelian_iff.mp hX).2 x hx
      rw [h2]
      exact Z1.one_mem
  have hOZ : pCoreOf 2 H ≤ centralizerMod Z1 H X := by
    rw [show pCoreOf 2 H = Q1 L1 L2 S from str83G4_pCoreOf_sup_left hfr]
    intro q hq
    refine mem_centralizerMod.mpr ⟨?_, ?_, ?_⟩
    · exact (le_sup_right : S ≤ L1 ⊔ S) (str83G4_q1_le_s hfr hq)
    · exact hHLZ ((le_sup_right : S ≤ L1 ⊔ S) (str83G4_q1_le_s hfr hq))
    · intro x hx
      have hmem : ⁅q, x⁆ ∈ ⁅Q1 L1 L2 S, X⁆ :=
        Subgroup.commutator_mem_commutator hq hx
      rw [Subgroup.commutator_comm] at hmem
      exact str83G4_commutator_x_q1_le hfr hmem
  letI : CommGroup (Ch3z.chiefMod Z1 X) := l2ChiefSectionCommGroup hEZ
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod Z1 X)) := l2ChiefSectionModule hEZ
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod Z1 X)) :=
    sectionRep hHLZ hHNZ hNLZ hEZ hOZ e
  obtain ⟨π, hπ⟩ := exists_chiefMod_proj hNLZ hNL1 hZ1X1
  have hπι : ∀ x : ↥X, π (Ch3z.chiefIota hNLZ x) = Ch3z.chiefIota hNL1 x :=
    fun x => chiefMod_proj_iota hNLZ hNL1 hZ1X1 hπ x
  let πa : Additive (Ch3z.chiefMod Z1 X) →+ Additive (Ch3z.chiefMod X1 X) :=
    MonoidHom.toAdditive π
  have hπa : ∀ x : ↥X, πa (Additive.ofMul (Ch3z.chiefIota hNLZ x)) =
      Additive.ofMul (Ch3z.chiefIota hNL1 x) := by
    intro x
    show Additive.ofMul (π (Ch3z.chiefIota hNLZ x)) =
      Additive.ofMul (Ch3z.chiefIota hNL1 x)
    rw [hπι x]
  have hπ_surj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ch3z.chiefIota_surjective hNL1 y
    exact ⟨Ch3z.chiefIota hNLZ x, hπι x⟩
  have hπa_surj : Function.Surjective πa := by
    intro v
    obtain ⟨x, hx⟩ := hπ_surj v.toMul
    refine ⟨Additive.ofMul x, ?_⟩
    show Additive.ofMul (π x) = v
    rw [hx]
    exact ofMul_toMul v
  obtain ⟨c, φ, hφ⟩ := hnat1
  set N : Submodule (ZMod 2) (Additive (Ch3z.chiefMod Z1 X)) :=
    AddSubgroup.toZModSubmodule 2 πa.ker with hNdef
  let φ' : Additive (Ch3z.chiefMod Z1 X) →+ (Fin 4 → K) := φ.toAddMonoidHom.comp πa
  have hsurj' : Function.Surjective φ' := φ.surjective.comp hπa_surj
  have hker' : φ'.ker = N.toAddSubgroup := by
    rw [hNdef, AddSubgroup.toZModSubmodule_toAddSubgroup]
    ext m
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    exact φ.map_eq_zero_iff
  have hNtriv : ∀ g, ∀ m ∈ N, ρ g m = m := by
    intro g m hm
    obtain ⟨a, rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x, hx⟩ := Ch3z.chiefIota_surjective hNLZ m
    have hm' : m = Additive.ofMul (Ch3z.chiefIota hNLZ x) := by rw [hx]; rfl
    rw [hm']
    have hmker : πa (Additive.ofMul (Ch3z.chiefIota hNLZ x)) = 0 := by
      rw [hNdef, AddSubgroup.mem_toZModSubmodule, AddMonoidHom.mem_ker] at hm
      rw [hm'] at hm
      exact hm
    have hxX1 : (x : G) ∈ X1 := by
      have h1 : π (Ch3z.chiefIota hNLZ x) = 1 := by
        exact ofMul_eq_zero.mp hmker
      have h1' : Ch3z.chiefIota hNL1 x = 1 := by
        rw [← hπι x]
        exact h1
      exact (Ch3z.chiefIota_eq_one_iff hNL1 x).mp h1'
    have hxX : (x : G) ∈ X := x.2
    have hhX : (h : G) * (x : G) * (h : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHNZ h.2) (x : G)).mp hxX
    have hsec := sectionRep_chiefIota hHLZ hHNZ hNLZ hEZ hOZ e h x hhX
    rw [hsec]
    have hz : ((h : G) * (x : G) * (h : G)⁻¹) * (x : G)⁻¹ ∈ Z1 := by
      have hzeq : (h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹ =
          ((x : G) * (h : G) * (x : G)⁻¹ * (h : G)⁻¹)⁻¹ := by group
      rw [hzeq]
      exact Z1.inv_mem ((mem_str83X1.mp hxX1).2.2 (h : G) h.2)
    have hιeq : Ch3z.chiefIota hNLZ ⟨(h : G) * x * (h : G)⁻¹, hhX⟩ =
        Ch3z.chiefIota hNLZ x := by
      have hh1 : Ch3z.chiefIota hNLZ
          (⟨(h : G) * x * (h : G)⁻¹, hhX⟩ * x⁻¹) = 1 :=
        (Ch3z.chiefIota_eq_one_iff hNLZ _).mpr (by simpa using hz)
      calc Ch3z.chiefIota hNLZ ⟨(h : G) * x * (h : G)⁻¹, hhX⟩
          = (Ch3z.chiefIota hNLZ ⟨(h : G) * x * (h : G)⁻¹, hhX⟩ *
              (Ch3z.chiefIota hNLZ x)⁻¹) * Ch3z.chiefIota hNLZ x := by group
        _ = Ch3z.chiefIota hNLZ (⟨(h : G) * x * (h : G)⁻¹, hhX⟩ * x⁻¹) *
              Ch3z.chiefIota hNLZ x := by rw [map_mul, map_inv]
        _ = 1 * Ch3z.chiefIota hNLZ x := by rw [hh1]
        _ = Ch3z.chiefIota hNLZ x := one_mul _
    exact congrArg Additive.ofMul hιeq
  have hcommSubX : ⁅X, oTwoUpper H⁆ ≤ X := by
    refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
    have hvH : v ∈ H := oTwoUpper_le H hv
    have h1 : v * u⁻¹ * v⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHNZ hvH) u⁻¹).mp (X.inv_mem hu)
    have heq : ⁅u, v⁆ = u * (v * u⁻¹ * v⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact X.mul_mem hu h1
  let Csub : Subgroup (Ch3z.chiefMod Z1 X) :=
    (CFSG.QuasithinUnique.Setup.X7.commSub ρ
      (⊤ : Subgroup ↥(suzukiGroup a K))).toAddSubgroup.toSubgroup'
  have hCsub_mem : ∀ y : Ch3z.chiefMod Z1 X,
      y ∈ Csub ↔ Additive.ofMul y ∈
        CFSG.QuasithinUnique.Setup.X7.commSub ρ
          (⊤ : Subgroup ↥(suzukiGroup a K)) := by
    intro y
    exact AddSubgroup.mem_toSubgroup' _ y
  let T : Subgroup G := (Csub.comap (Ch3z.chiefIota hNLZ)).map X.subtype
  have hcomm_le_T : ⁅X, oTwoUpper H⁆ ≤ T := by
    refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
    have hvH : v ∈ H := oTwoUpper_le H hv
    have hvuX : v * u * v⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHNZ hvH) u).mp hu
    have hcommX' : ⁅u, v⁆ ∈ X := hcommSubX (Subgroup.commutator_mem_commutator hu hv)
    refine Subgroup.mem_map.mpr ⟨⟨⁅u, v⁆, hcommX'⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, hCsub_mem]
    have hsec := sectionRep_chiefIota hHLZ hHNZ hNLZ hEZ hOZ e
      ⟨v, hvH⟩ ⟨u, hu⟩ hvuX
    have hmemrange : Additive.ofMul (Ch3z.chiefIota hNLZ ⟨v * u * v⁻¹, hvuX⟩) -
        Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩) ∈
        LinearMap.range (ρ (e (QuotientGroup.mk ⟨v, hvH⟩)) - 1) := by
      refine LinearMap.mem_range.mpr ⟨Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩), ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply, hsec]
    have hcommv : Additive.ofMul (Ch3z.chiefIota hNLZ ⟨v * u * v⁻¹, hvuX⟩) -
        Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩) =
        -Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩) := by
      have h1 : (⟨v * u * v⁻¹, hvuX⟩ : ↥X) = ⟨⁅u, v⁆, hcommX'⟩⁻¹ * ⟨u, hu⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      calc Additive.ofMul (Ch3z.chiefIota hNLZ ⟨v * u * v⁻¹, hvuX⟩) -
            Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩)
          = Additive.ofMul (Ch3z.chiefIota hNLZ (⟨⁅u, v⁆, hcommX'⟩⁻¹ * ⟨u, hu⟩)) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩) := by rw [h1]
        _ = Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩⁻¹ *
              Ch3z.chiefIota hNLZ ⟨u, hu⟩) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩) := by rw [map_mul]
        _ = (Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩⁻¹) +
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩)) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨u, hu⟩) := by rw [ofMul_mul]
        _ = Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩⁻¹) := by abel
        _ = -Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩) := by
              rw [map_inv, ofMul_inv]
    have hmem : -Additive.ofMul (Ch3z.chiefIota hNLZ ⟨⁅u, v⁆, hcommX'⟩) ∈
        CFSG.QuasithinUnique.Setup.X7.commSub ρ
          (⊤ : Subgroup ↥(suzukiGroup a K)) :=
      range_le_commSub (Subgroup.mem_top _) (hcommv ▸ hmemrange)
    have hneg := Submodule.neg_mem (p := CFSG.QuasithinUnique.Setup.X7.commSub ρ
      (⊤ : Subgroup ↥(suzukiGroup a K))) (Submodule.neg_mem
      (p := CFSG.QuasithinUnique.Setup.X7.commSub ρ
        (⊤ : Subgroup ↥(suzukiGroup a K))) hmem)
    simpa using hneg
  have hM : CFSG.QuasithinUnique.Setup.X7.commSub ρ
      (⊤ : Subgroup ↥(suzukiGroup a K)) = ⊤ := by
    letI : CommGroup ↥X := commGroupOfElemAbelian hX
    refine eq_top_iff.mpr ?_
    intro m _
    obtain ⟨x, hx⟩ := Ch3z.chiefIota_surjective hNLZ m
    have hm : m = Additive.ofMul (Ch3z.chiefIota hNLZ x) := by rw [hx]; rfl
    rw [hm]
    have hxsupX : x ∈ (⁅X, oTwoUpper H⁆).subgroupOf X ⊔ Z1.subgroupOf X := by
      rw [← Subgroup.subgroupOf_sup hcommSubX hZ1X]
      exact Subgroup.mem_subgroupOf.mpr (by rw [← hxeq]; exact x.2)
    obtain ⟨n, hn, z, hz, hnz⟩ :=
      (Subgroup.mem_sup (s := (⁅X, oTwoUpper H⁆).subgroupOf X)
        (t := Z1.subgroupOf X) (x := x)).mp hxsupX
    have hnG : (n : G) ∈ ⁅X, oTwoUpper H⁆ := Subgroup.mem_subgroupOf.mp hn
    have hzZ1 : (z : G) ∈ Z1 := Subgroup.mem_subgroupOf.mp hz
    have hnT : (n : G) ∈ T := hcomm_le_T hnG
    have hιn : Additive.ofMul (Ch3z.chiefIota hNLZ n) ∈
        CFSG.QuasithinUnique.Setup.X7.commSub ρ
          (⊤ : Subgroup ↥(suzukiGroup a K)) := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hnT
      have hyxn : y = n := Subtype.ext hyx
      rw [hyxn] at hy
      rw [Subgroup.mem_comap, hCsub_mem] at hy
      exact hy
    have hιx : Ch3z.chiefIota hNLZ x = Ch3z.chiefIota hNLZ n := by
      have h1 : Ch3z.chiefIota hNLZ x = Ch3z.chiefIota hNLZ (n * z) := by rw [hnz]
      rw [h1, map_mul]
      have hz1 : Ch3z.chiefIota hNLZ z = 1 :=
        (Ch3z.chiefIota_eq_one_iff hNLZ z).mpr hzZ1
      rw [hz1, mul_one]
    rw [hιx]
    exact hιn
  have hNatStar : N ≤ CFSG.QuasithinUnique.Setup.X7.commSub ρ (suzukiZ0 a K) :=
    le_commSub_suzukiZ0_of_natural_quotient hK ha ρ N hNtriv
      ⟨c, φ', hsurj', hker', by
        intro g m
        obtain ⟨x, hx⟩ := Ch3z.chiefIota_surjective hNLZ m
        have hm : m = Additive.ofMul (Ch3z.chiefIota hNLZ x) := by rw [hx]; rfl
        rw [hm]
        obtain ⟨a, rfl⟩ := e.surjective g
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
        have hxX : (x : G) ∈ X := x.2
        have hhX : (h : G) * (x : G) * (h : G)⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hHNZ h.2) (x : G)).mp hxX
        have hsecZ := sectionRep_chiefIota hHLZ hHNZ hNLZ hEZ hOZ e h x hhX
        have hsec1 := sectionRep_chiefIota hHL1 hHN1 hNL1' hE1 hO1 e h x hhX
        have hcommπ : πa (ρ (e (QuotientGroup.mk h))
              (Additive.ofMul (Ch3z.chiefIota hNLZ x))) =
            ρ1 (e (QuotientGroup.mk h))
              (πa (Additive.ofMul (Ch3z.chiefIota hNLZ x))) := by
          calc πa (ρ (e (QuotientGroup.mk h))
                (Additive.ofMul (Ch3z.chiefIota hNLZ x)))
              = πa (Additive.ofMul (Ch3z.chiefIota hNLZ
                  ⟨(h : G) * x * (h : G)⁻¹, hhX⟩)) := by
                rw [hsecZ]
            _ = Additive.ofMul (Ch3z.chiefIota hNL1
                  ⟨(h : G) * x * (h : G)⁻¹, hhX⟩) := hπa _
            _ = ρ1 (e (QuotientGroup.mk h))
                  (Additive.ofMul (Ch3z.chiefIota hNL1 x)) := by
                rw [← hsec1]
            _ = ρ1 (e (QuotientGroup.mk h))
                  (πa (Additive.ofMul (Ch3z.chiefIota hNLZ x))) := by
                rw [hπa x]
        calc φ' (ρ (e (QuotientGroup.mk h))
              (Additive.ofMul (Ch3z.chiefIota hNLZ x)))
            = φ (πa (ρ (e (QuotientGroup.mk h))
                (Additive.ofMul (Ch3z.chiefIota hNLZ x)))) := rfl
          _ = φ (ρ1 (e (QuotientGroup.mk h))
                (πa (Additive.ofMul (Ch3z.chiefIota hNLZ x)))) := by rw [hcommπ]
          _ = ((((e (QuotientGroup.mk h) : GL (Fin 4) K)) :
                Matrix (Fin 4) (Fin 4) K).map (fun y => y ^ 2 ^ c)) *ᵥ
                φ (πa (Additive.ofMul (Ch3z.chiefIota hNLZ x))) :=
              hφ (e (QuotientGroup.mk h)) _
          _ = ((((e (QuotientGroup.mk h) : GL (Fin 4) K)) :
                Matrix (Fin 4) (Fin 4) K).map (fun y => y ^ 2 ^ c)) *ᵥ
                φ' (Additive.ofMul (Ch3z.chiefIota hNLZ x)) := rfl⟩
      hM
  set Lsub : Submodule (ZMod 2) (Additive (Ch3z.chiefMod Z1 X)) :=
    AddSubgroup.toZModSubmodule 2
      { carrier := {v | ∃ y : ↥X, (y : G) ∈ ⁅X, W⁆ ∧
          Additive.ofMul (Ch3z.chiefIota hNLZ y) = v}
        add_mem' := by
          rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
          exact ⟨y₁ * y₂, ⁅X, W⁆ |>.mul_mem hy₁ hy₂, by
            rw [map_mul, ofMul_mul]⟩
        zero_mem' := ⟨1, ⁅X, W⁆ |>.one_mem, by simp⟩
        neg_mem' := by
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨y⁻¹, ⁅X, W⁆ |>.inv_mem hy, by rw [map_inv, ofMul_inv]⟩ }
    with hLsubdef
  have hcommSub_le_L : CFSG.QuasithinUnique.Setup.X7.commSub ρ (suzukiZ0 a K) ≤
      Lsub := by
    have hZ0lift := str83G4_exists_mem_of_mem_suzukiZ0 hfr hC hK e he
    refine iSup₂_le fun z hz => ?_
    rintro _ ⟨m, rfl⟩
    obtain ⟨x, hx⟩ := Ch3z.chiefIota_surjective hNLZ m
    have hm : m = Additive.ofMul (Ch3z.chiefIota hNLZ x) := by rw [hx]; rfl
    rw [hm]
    obtain ⟨cH, hcW, hce⟩ := hZ0lift z hz
    have hcH : (cH : G) ∈ H :=
      (le_sup_right : S ≤ H) (str83G4_conjugate_x_le_s hfr d hX hcW)
    have hcxX : (cH : G) * (x : G) * (cH : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHNZ hcH) (x : G)).mp x.2
    have hdmem : ⁅(cH : G), (x : G)⁆ ∈ ⁅X, W⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hcW x.2
    let d : ↥X := ⟨⁅(cH : G), (x : G)⁆, (str83G4_commutator_x_conjugate_le hfr d hX hdmem).1⟩
    have hsec := sectionRep_chiefIota hHLZ hHNZ hNLZ hEZ hOZ e cH x hcxX
    have hdiff : (ρ z - 1) (Additive.ofMul (Ch3z.chiefIota hNLZ x)) =
        Additive.ofMul (Ch3z.chiefIota hNLZ d) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, ← hce, hsec]
      have h1 : (⟨(cH : G) * x * (cH : G)⁻¹, hcxX⟩ : ↥X) = d * ⟨x, x.2⟩ := by
        apply Subtype.ext
        show (cH : G) * (x : G) * (cH : G)⁻¹ = ⁅(cH : G), (x : G)⁆ * (x : G)
        rw [commutatorElement_def]
        group
      calc Additive.ofMul (Ch3z.chiefIota hNLZ ⟨(cH : G) * x * (cH : G)⁻¹, hcxX⟩) -
            Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, x.2⟩)
          = Additive.ofMul (Ch3z.chiefIota hNLZ (d * ⟨x, x.2⟩)) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, x.2⟩) := by rw [h1]
        _ = Additive.ofMul (Ch3z.chiefIota hNLZ d *
              Ch3z.chiefIota hNLZ ⟨x, x.2⟩) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, x.2⟩) := by rw [map_mul]
        _ = (Additive.ofMul (Ch3z.chiefIota hNLZ d) +
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, x.2⟩)) -
              Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, x.2⟩) := by rw [ofMul_mul]
        _ = Additive.ofMul (Ch3z.chiefIota hNLZ d) := by abel
    rw [hdiff]
    exact ⟨d, hdmem, rfl⟩
  intro x hx
  have hxX : (x : G) ∈ X := str83G4_x1_le_x L1 L2 S hx
  have hmN : Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, hxX⟩) ∈ N := by
    rw [hNdef, AddSubgroup.mem_toZModSubmodule, AddMonoidHom.mem_ker]
    show Additive.ofMul (π (Ch3z.chiefIota hNLZ ⟨x, hxX⟩)) = 0
    rw [hπι]
    have h1 : Ch3z.chiefIota hNL1 ⟨x, hxX⟩ = 1 :=
      (Ch3z.chiefIota_eq_one_iff hNL1 _).mpr hx
    rw [h1]
    rfl
  have hmL : Additive.ofMul (Ch3z.chiefIota hNLZ ⟨x, hxX⟩) ∈ Lsub :=
    (hNatStar.trans hcommSub_le_L) hmN
  rw [hLsubdef] at hmL
  obtain ⟨y, hy, hyx⟩ := hmL
  have hι : Ch3z.chiefIota hNLZ y = Ch3z.chiefIota hNLZ ⟨x, hxX⟩ :=
    Additive.ofMul.injective hyx
  have hz : ((y * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) : G) ∈ Z1 := by
    have h1 : Ch3z.chiefIota hNLZ (y * (⟨x, hxX⟩ : ↥X)⁻¹) = 1 := by
      rw [map_mul, map_inv, hι, mul_inv_cancel]
    exact (Ch3z.chiefIota_eq_one_iff hNLZ _).mp h1
  have hxeq' : x = (((y * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) : G)⁻¹) * (y : G) := by
    have hcoe : ((y * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) : G) = (y : G) * (x : G)⁻¹ := rfl
    rw [hcoe]
    group
  rw [hxeq']
  exact (⁅X, W⁆ ⊔ Z1).mul_mem (Subgroup.mem_sup_right (Z1.inv_mem hz))
    (Subgroup.mem_sup_left hy)

private theorem str83G4_z1_le_conjugate_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    Z1 L1 L2 S ≤ CFSG.conjugate (str83X L1 L2 S) d.w := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  have hZ2w : CFSG.conjugate (Z2 L1 L2 S) d.w = Z2 L1 L2 S :=
    str83G4_conjugate_z2_eq ⟨hF, hB, ha, hSz, hL2, hZI⟩ d
  calc Z1 L1 L2 S ≤ Z2 L1 L2 S := hZ1Z2
    _ = CFSG.conjugate (Z2 L1 L2 S) d.w := hZ2w.symm
    _ ≤ CFSG.conjugate (str83X L1 L2 S) d.w :=
        Subgroup.map_mono (z2_le_str83X L1 L2 S)

theorem str83G4_x1_le_x_inf_conjugate_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83X1 L1 L2 S ≤ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨str83G4_x1_le_x L1 L2 S hx, ?_⟩
  exact (sup_le ((str83G4_commutator_x_conjugate_le hfr d hX).trans inf_le_right)
    (str83G4_z1_le_conjugate_x hfr d))
    (str83G4_x1_le_commutator_sup_z1 hfr d hX hB hx)

theorem str83G4_x_inf_centralizer_conjugate_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83X L1 L2 S ⊓
        Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  have hWabel : IsElemAbelian 2 (CFSG.conjugate (str83X L1 L2 S) d.w) :=
    str83G4_isElemAbelian_conjugate_x d hX
  have ht_ex : ∃ t : G, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w ∧
      t ∉ Q1 L1 L2 S := by
    by_contra h
    apply hB
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  obtain ⟨t, htW, htQ⟩ := ht_ex
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxX, hxC⟩ := hx
    have hxt : x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y = t := by simpa using hy
      rw [hy']
      exact Subgroup.mem_centralizer_iff.mp hxC t htW
    have hxmem' : x ∈ str83X L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxX, hxt⟩
    have hxmem : x ∈ str83X1 L1 L2 S ⊔ ⁅str83X L1 L2 S, Subgroup.zpowers t⁆ := by
      rw [← str83G4_x_inf_centralizer_eq_x1_sup hfr d hX hB htW htQ,
        ← str83G4_x_inf_centralizer_eq_of_mem hfr d hX hB htW htQ]
      exact hxmem'
    have hle : str83X1 L1 L2 S ⊔ ⁅str83X L1 L2 S, Subgroup.zpowers t⁆ ≤
        str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w :=
      sup_le (str83G4_x1_le_x_inf_conjugate_x hfr d hX hB)
        ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr htW)).trans
          (str83G4_commutator_x_conjugate_le hfr d hX))
    exact hle hxmem
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (B6.isElemAbelian_iff.mp hWabel).1 y hy x hx.2

theorem str83G4_relIndex_x_inf_conjugate_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w).relIndex
      (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  have ht_ex : ∃ t : G, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w ∧
      t ∉ Q1 L1 L2 S := by
    by_contra h
    apply hB
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  obtain ⟨t, htW, htQ⟩ := ht_ex
  have hEq : str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w =
      str83X L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [← str83G4_x_inf_centralizer_conjugate_x hfr d hX hB,
      str83G4_x_inf_centralizer_eq_of_mem hfr d hX hB htW htQ]
  rw [hEq]
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcent, Subgroup.inf_relIndex_left]
  exact str83G4_relIndex_centralizer_x hfr d hX htW htQ

end CFSG.Quasithin.Stroth

end
