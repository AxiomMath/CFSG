module

public import CFSG.Quasithin.Background.C35InspSp4A
public import CFSG.Quasithin.Background.C35InspBase
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListTits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem sp_radical_data {F : Type} [Field F] [Finite F] [CharP F 2]
    (hK : ∃ k : ℕ, Nat.card F = 2 ^ k) (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2) :
    ∃ (act : ↥(perfectCore (Q2 F j)) →* SpecialLinearGroup (Fin 2) F)
      (c : ↥(perfectCore (Q2 F j)) → (Fin 2 → F)),
      Function.Surjective act ∧ IsPGroup 2 act.ker ∧
      (∀ r s, act r = 1 → act s = 1 → c (r * s) = c r + c s) ∧
      (∀ n r, act r = 1 → c r = 0 → n * r = r * n) ∧
      (∀ n r, act r = 1 → c (n * r * n⁻¹) =
        ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ c r) := by
  fin_cases j
  · have hact : ∀ r, ((CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).toMonoidHom.comp
        (blkN 0)) r = 1 ↔ blkN 0 r = 1 := fun r => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    refine ⟨(CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).toMonoidHom.comp (blkN 0), spc0,
      (CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).surjective.comp (blkN_surjective hK4 0),
      ?_, fun r s hr hs => spc0_mul r s ((hact r).1 hr) ((hact s).1 hs),
      fun n r hr h0 => sp0_central n r ((hact r).1 hr) h0, fun n r hr => ?_⟩
    · rintro ⟨r, hr⟩
      obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK 0 ⟨r, (hact r).1 hr⟩
      have h : r ^ 2 ^ k = 1 := (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      exact ⟨k, Subtype.ext ((SubgroupClass.coe_pow _ _).trans h)⟩
    · rw [sp0_conj n r ((hact r).1 hr)]
      rfl
  · have hact : ∀ r, ((frobSL (F := F)).comp (blkN 1)) r = 1 ↔ blkN 1 r = 1 := fun r => by
      rw [MonoidHom.comp_apply]
      exact map_eq_one_iff _ frobSL_bijective.1
    refine ⟨(frobSL (F := F)).comp (blkN 1), spc1, frobSL_bijective.2.comp (blkN_surjective hK4 1),
      ?_,
      fun r s hr hs => spc1_mul r s ((hact r).1 hr) ((hact s).1 hs),
      fun n r hr h0 => sp1_central n r ((hact r).1 hr) h0,
      fun n r hr => sp1_conj n r ((hact r).1 hr)⟩
    rintro ⟨r, hr⟩
    obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK 1 ⟨r, (hact r).1 hr⟩
    have h : r ^ 2 ^ k = 1 := (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
    exact ⟨k, Subtype.ext ((SubgroupClass.coe_pow _ _).trans h)⟩

theorem sp4_holds_base : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A),
    C35Base K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V := by
  intro A _ _ K Y M₀ V hD f hf2 hX
  classical
  have hX' := hX
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hX
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let ι : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_charTwo, proj_surjective⟩
  let φ : ↥K →* StatedSp 2 F := (e.trans ι.symm).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := (e.trans ι.symm).surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU : IsSylowTwoOf (unipotent 2 F) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  obtain ⟨g, hNY, hne, hns⟩ := hD.exists_conj_normalizer φ hφker.le hφs hU
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker]
  have hYK : Y ≤ K := hD.parabolic.1
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hYK
  have hZY : centerOf K ≤ Y := hD.center_le.trans (Subgroup.map_subtype_le _)
  have hB : borelSubgroup 2 F ≤ img θ Y := by
    rw [← normalizer_unipotent]
    exact hNY
  obtain ⟨j, hj⟩ := eq_Q2_of_overgroup hK hB hne hns
  have hMj : img θ M₀ = (perfectCore (Q2 F j)).map (MonoidHom.id (StatedSp 2 F)) := by
    rw [Subgroup.map_id, hD.eq_perfectCore, img_perfectCore θ hYK, hj]
  have hinj : Set.InjOn (MonoidHom.id (StatedSp 2 F))
      (perfectCore (Q2 F j) : Set (StatedSp 2 F)) := fun _ _ _ _ h => h
  set ν := liftHom hM₀K θ (MonoidHom.id (StatedSp 2 F)) (perfectCore (Q2 F j)) hinj hMj with hν
  have hνs := liftHom_surjective hM₀K θ (MonoidHom.id (StatedSp 2 F)) (perfectCore (Q2 F j))
    hinj hMj
  have hν1 : ∀ x : ↥M₀, ν x = 1 ↔ (x : A) ∈ centerOf K := by
    intro x
    rw [hν, liftHom_eq_one_iff, ← MonoidHom.mem_ker, hθker]
    exact mem_centerOf_iff.symm
  have hνker : IsPGroup 2 ν.ker := by
    rintro ⟨x, hx⟩
    have hxZ : (⟨x, hM₀K x.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
      mem_centerOf_iff.1 ((hν1 x).1 hx)
    obtain ⟨k, hk⟩ := isPGroup_center hD.center ⟨_, hxZ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hk
    simpa using this
  obtain ⟨act, c, hacts, hactker, hcmul, hcent, hceq⟩ := sp_radical_data hK hK4 j
  have hMV := le_normalizer_of_comm hD.V_comm
  obtain ⟨hVO, -⟩ := hD.le_pCoreOf
  have hVZ : ¬ V ≤ V ⊓ Subgroup.centralizer (M₀ : Set A) := by
    intro h
    apply hD.V_ne
    rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun v hv => (h hv).2
  have hperf : ⁅M₀, M₀⁆ = M₀ := hD.eq_perfectCore ▸ perfectCore_perfect Y
  have hcZ : ∀ (v : A) (hv : v ∈ V), act (ν ⟨v, hD.V_le hv⟩) = 1 →
      (c (ν ⟨v, hD.V_le hv⟩) = 0 ↔ v ∈ V ⊓ Subgroup.centralizer (M₀ : Set A)) := by
    intro v hv h1
    constructor
    · intro h0
      refine ⟨hv, mem_centralizer_of_comm_mem hM₀K hperf fun m hm => ?_⟩
      have hc := hcent (ν ⟨m, hm⟩) (ν ⟨v, hD.V_le hv⟩) h1 h0
      have h2 : ν (⟨v, hD.V_le hv⟩ * ⟨m, hm⟩ * (⟨v, hD.V_le hv⟩ : ↥M₀)⁻¹ *
          (⟨m, hm⟩ : ↥M₀)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
        group
      exact (hν1 _).1 h2
    · rintro ⟨-, hvC⟩
      refine eq_zero_of_central act hacts c hceq h1 fun n => ?_
      obtain ⟨m, rfl⟩ := hνs n
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hvC m m.2)
  obtain ⟨hOker, hnat⟩ := natural_of_radical hD.V_le hMV hVZ hVO hK4 ν hνs hνker act hacts
    hactker c hcmul hcZ hceq
  have hker2 : IsPGroup 2 (act.comp ν).ker := by
    rw [hOker]
    exact CFSG.pCore_isPGroup
  have hco : IsCoatom (img θ Y) := by
    rw [hj]
    exact isCoatom_Q2 j
  exact ⟨f, Or.inr (Or.inl hX'),
    isMaxParabolic2_of_coatom θ hθker.le hD.parabolic hD.ne_top hZY hco,
    isPSL2_modO2 hcard hf2 _ (hacts.comp hνs) hker2,
    Or.inr ⟨hX', F, inferInstance, Fintype.ofFinite F, by rw [Fintype.card_eq_nat_card, hcard],
      hnat⟩⟩

theorem sp4_holds : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V :=
  fun A _ _ K Y M₀ V hD => sp4_holds_base A K Y M₀ V hD.toBase

end CFSG.Quasithin.C35Pf
