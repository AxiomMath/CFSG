module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Loc
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110One
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.Quasithin.Background.C58Blocks

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.X6 (ResidualOvergroups ResidualOvergroupsAt)

@[expose] def FactF5113 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsRank2LieChar2 Y → ∀ U : Subgroup Y, IsSylowTwoOf U ⊤ →
    (∀ P : Subgroup Y, U ≤ P → P ⋖ ⊤ → ¬ Group.IsSolvable ↥P) →
    ∀ Z : Subgroup Y, U ≤ Z → Group.IsSolvable ↥Z → Z ≤ Subgroup.normalizer (U : Set Y)

theorem isRank2LieChar2_of_is2F4 {Y : Type} [Group Y] {f : ℕ} (h : Is2F4 f Y) :
    IsRank2LieChar2 Y := by
  obtain ⟨⟨-, -, -, -, hodd, hf3⟩, -⟩ := id h
  exact Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf3, h⟩))))⟩

theorem residualOvergroups_of_isSL3 {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : IsSL3 (2 ^ f) Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ResidualOvergroups Y U := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let φ : Matrix.SpecialLinearGroup (Fin 3) K ≃* Y :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).trans e.symm
  have hres := Vol2Native.A312L.linear_three_residual_of_cover ⟨f, hK⟩ φ.toMonoidHom
    φ.surjective (by
      intro x hx
      have : x = 1 := φ.injective (by simpa using hx)
      rw [this]
      exact Subgroup.one_mem _)
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf
      ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 K).map φ.toMonoidHom) ⊤ := by
    have h1 := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
    rw [hP] at h1
    have h2 := (Setup.Layer.isSylowTwoOf_map_mulEquiv φ).mpr h1
    rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h2
  exact ResidualOvergroups.of_isSylow (MulEquiv.refl Y) ⟨_, hres⟩ hU₀ hU

theorem residualOvergroups_of_rank2
    {Y : Type} [Group Y] [Finite Y] (hR : IsRank2LieChar2 Y) (hT : ¬ IsTits Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ResidualOvergroups Y U := by
  rcases hR with ⟨f, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h2, h⟩ | ⟨h1, h⟩ | ⟨hodd, h3, h⟩⟩ | h
  · exact Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU (Or.inl ⟨f, h⟩)
  · exact residualOvergroups_of_isSL3 h hU
  · exact Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU (Or.inr ⟨f, h⟩)
  · exact Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
      (Or.inl ⟨f, h2, h⟩)
  · exact Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
      (Or.inr (Or.inl ⟨f, h1, h⟩))
  · exact Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
      (Or.inr (Or.inr ⟨f, h3, hodd, h⟩))
  · exact absurd h hT

section General

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_of_perfect_of_le_sup {Q A P : Subgroup Γ} (hQ : ⁅Q, Q⁆ = Q) (hQAP : Q ≤ A ⊔ P)
    (hP : IsPGroup 2 P) (hPA : P ≤ Subgroup.normalizer (A : Set Γ)) : Q ≤ A :=
  (perfect_le_oTwoUpper le_rfl (Subgroup.isPerfect_iff.mpr hQ)).trans
    (C58.oTwoUpper_le_of_le_sup hQAP hP hPA)

theorem perfectCore_sup_eq {A P : Subgroup Γ} (hA : ⁅A, A⁆ = A) (hP : IsPGroup 2 P)
    (hPA : P ≤ Subgroup.normalizer (A : Set Γ)) : perfectCore (A ⊔ P) = A :=
  le_antisymm (le_of_perfect_of_le_sup (perfectCore_perfect _) (perfectCore_le _) hP hPA)
    (le_perfectCore_of_perfect le_sup_left hA)

theorem eq_of_isSubnormal_of_le_sup {K₁ Q : Subgroup Γ} :
    ∀ {A K : Subgroup Γ}, IsSubnormal A K → ⁅K, K⁆ = K → IsPGroup 2 Q → Q ≤ K →
      K ≤ K₁ ⊔ Q → K₁ ≤ A → A = K := by
  intro A K hA
  induction hA with
  | refl => intros; rfl
  | @step A' M' K' hAM hN hMK ih =>
    intro hK hQ hQK hle hK₁A
    have hM : M' = K' := ih hK hQ hQK hle (hK₁A.trans hAM)
    subst hM
    exact le_antisymm hAM (le_of_perfect_of_le_sup hK (hle.trans (sup_le_sup_right hK₁A Q)) hQ
      (hQK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hN)))

theorem mem_normalizer_of_normal_sylow {R U : Subgroup Γ} (hU : IsSylowTwoOf U R)
    (hRU : R ≤ Subgroup.normalizer (U : Set Γ)) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (R : Set Γ)) : g ∈ Subgroup.normalizer (U : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := U.map (MulAut.conj g).toMonoidHom with hP
  have hPR : P ≤ R := by
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg u).mp (hU.1 hu)
  have hP2 : IsPGroup 2 P := hU.2.1.map _
  have h2 := IsPGroup.to_sup_of_normal_right' hP2 hU.2.1 (hPR.trans hRU)
  have heq := hU.eq_of_le le_sup_right (sup_le hPR hU.1) h2
  have hPU : P ≤ U := heq ▸ le_sup_left
  have hPeq : P = U := Subgroup.eq_of_le_of_card_ge hPU
    (by rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact A38.map_conj_eq_iff.mp hPeq

theorem map_eq_of_residualOvergroupsAt {S : Type} [Group S] [Finite S] {U : Subgroup S}
    {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P) {A : Subgroup S}
    (hA : ⁅A, A⁆ = A) (hA1 : A ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUA : U ≤ Subgroup.normalizer (A : Set S)) (hne : A ⊔ U ≠ ⊤) {α : MulAut S}
    (hα : Odd (orderOf α)) (hαU : U.map α.toMonoidHom = U) : A.map α.toMonoidHom = A := by
  have hns : ¬ Group.IsSolvable ↥(A ⊔ U) := by
    intro hs
    have : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hA
    have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
    exact Group.IsPerfect.not_isSolvable ↥A
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_sup_left : A ≤ A ⊔ U)) (Subgroup.inclusion_injective _))
  have h := hP.2.2.2.2.2 α hα hαU (A ⊔ U) le_sup_right hne hns
  rwa [Vol2Native.A312L.dInf_eq_perfectCore, perfectCore_sup_eq hA hU2 hUA] at h

theorem exists_solvable_max_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ U P : Subgroup A, IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P) :
    ∃ U P : Subgroup B, IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P := by
  obtain ⟨U, P, hU, hUP, hP, hs⟩ := h
  refine ⟨U.map e.toMonoidHom, P.map e.toMonoidHom, ?_, Subgroup.map_mono hUP, ?_, ?_⟩
  · have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e).mpr hU
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  · have key : ∀ x y : Subgroup A, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
      fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
    have := (key P ⊤).mpr hP
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  · exact Group.isSolvable_of_surjective
      (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.surjective _)

end General

section Bar

variable {G : Type} [Group G]

theorem o2Map_mem_normalizer {X Y : Subgroup G} {x : ↥X}
    (hY : (x : G) ∈ Subgroup.normalizer (Y : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈
      Subgroup.normalizer ((modO2Image X Y : Subgroup (O2Q X)) : Set (O2Q X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hz
    refine ⟨x * z * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using (Subgroup.mem_normalizer_iff.mp hY _).mp hz'
  · rintro ⟨z, hz, hzy⟩
    have hz' : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hz
    refine ⟨x⁻¹ * z * x, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 : (x : G) * ((x : G)⁻¹ * z * x) * (x : G)⁻¹ ∈ Y := by simpa [mul_assoc] using hz'
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hY _).mpr h1
    · rw [map_mul, map_mul, map_inv, hzy]
      group

end Bar

namespace EmbLoc

variable {G : Type} [Group G] [Finite G]
variable {S X K Kh : Subgroup G} {k : ℕ} (l : EmbLoc G S X K Kh)
include l

theorem lie_normalizes
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactF5113)
    (htype : (SuzukiModel (O2Q K) 2 k ∧ Is2F4 k (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Kh)))
    (hres : ¬ ∃ U P : Subgroup (O2Q Kh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      P ⋖ ⊤ ∧ Group.IsSolvable ↥P)
    {A : Subgroup G} (hSA : S ≤ A) (hAX : A ≤ X) (hAs : Group.IsSolvable ↥A) {m : G}
    (hmA : m ∈ A) (hmodd : Odd (orderOf m)) : m ∈ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := l.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (O2Q K) := by
    rcases htype with ⟨hS, -⟩ | ⟨hL2, -⟩
    · exact isSimpleGroup_of_psl2_or_sz (Or.inr hS)
    · exact isSimpleGroup_of_lieModel_PSL2 hL2
  have hKX : K ≤ X := l.le_X
  have hKKh : K ≤ Kh := l.le_hat
  have hKperf : ⁅K, K⁆ = K := l.perfect
  have hloc : LocalSQTK G := (qtkeCore_of_cat l.nonabelian l.qtke).1
  have hXN : X ≤ Subgroup.normalizer (Kh : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 l.pCoreX l.sylowX
      l.hat_cComp
    rwa [l.conjClosure_hat] at this
  set Y := modO2Image X Kh with hY
  obtain ⟨eH⟩ := l.hat_equiv
  have hR : IsRank2LieChar2 ↥Y := by
    rcases htype with ⟨-, h2F4⟩ | ⟨-, hR⟩
    · exact IsRank2LieChar2.of_mulEquiv eH (isRank2LieChar2_of_is2F4 h2F4)
    · exact IsRank2LieChar2.of_mulEquiv eH hR
  have hres' : ¬ ∃ U P : Subgroup ↥Y, IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
      Group.IsSolvable ↥P :=
    fun h' => hres (exists_solvable_max_of_mulEquiv eH.symm h')
  set Ub := o2Img X S ⊓ Y with hUb
  have hUbY : IsSylowTwoOf Ub Y :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp l.hatBar_cComp) l.sylowBar
  set U := Ub.subgroupOf Y with hU
  have hUS : IsSylowTwoOf U ⊤ := isSylowTwoOf_top_subgroupOf hUbY
  set Kb := modO2Image X K with hKb
  have hKbY : Kb ≤ Y := Subgroup.map_mono fun x hx => hKKh hx
  set KS := Kb.subgroupOf Y with hKS
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥Kb := Group.IsPerfect.ofSurjective (barMap_surjective hKX)
    exact Subgroup.isPerfect_iff.mp this
  have hKSperf : ⁅KS, KS⁆ = KS := by
    have : Group.IsPerfect ↥Kb := Subgroup.isPerfect_iff.mpr hKbperf
    have : Group.IsPerfect ↥KS :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKbY).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Subgroup.isPerfect_iff.mp this
  have hKbne : Kb ≠ ⊥ := by
    intro hbot
    obtain ⟨eB⟩ := l.bar_equiv
    have : Subsingleton (ModO2 (modO2Image X K)) := by
      have : Subsingleton ↥(modO2Image X K) := by
        rw [← hKb, hbot]
        infer_instance
      infer_instance
    have : Nontrivial (O2Q K) := hsimple.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (O2Q K)
    exact hab (eB.injective (Subsingleton.elim _ _))
  have hKSne : KS ≠ ⊥ := by
    intro hbot
    apply hKbne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hKbY hx⟩ : ↥Y) ∈ KS := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hTKb : o2Img X S ≤ Subgroup.normalizer ((Kb : Subgroup (O2Q X)) : Set (O2Q X)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (l.normalizes (Subgroup.mem_subgroupOf.mp ht))
  have hUKS : U ≤ Subgroup.normalizer ((KS : Subgroup ↥Y) : Set ↥Y) :=
    le_normalizer_subgroupOf (inf_le_left.trans hTKb)
  have hU2 : IsPGroup 2 U := hUS.2.1
  have hSperf : Group.IsPerfect ↥Y := by
    have : Group.IsPerfect ↥Kh := Subgroup.isPerfect_iff.mpr l.hat_cComp.2.1
    have : Group.IsPerfect (O2Q Kh) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Kh))
    exact Group.IsPerfect.ofSurjective (f := eH.toMonoidHom) eH.surjective
  have hne : KS ⊔ U ≠ ⊤ := by
    intro htop
    have h1 : (⊤ : Subgroup ↥Y) ≤ KS :=
      le_of_perfect_of_le_sup (Subgroup.isPerfect_iff.mp inferInstance) htop.ge hU2 hUKS
    have h2 : Y ≤ Kb := by
      intro y hy
      exact h1 (Subgroup.mem_top (⟨y, hy⟩ : ↥Y))
    exact lt_irrefl _ (lt_of_lt_of_le l.bar_lt h2)
  have hTits : ¬ IsTits ↥Y := by
    intro hT
    obtain ⟨H', N', -, -, -, -, -, hlat, hHs, hNs⟩ :=
      Setup.X6.titsSylowOvergroupLattice ↥Y hT U hUS
    have hns : ¬ Group.IsSolvable ↥(KS ⊔ U) := by
      intro hs
      have : Group.IsPerfect ↥KS := Subgroup.isPerfect_iff.mpr hKSperf
      have : Nontrivial ↥KS := (Subgroup.nontrivial_iff_ne_bot KS).mpr hKSne
      exact Group.IsPerfect.not_isSolvable ↥KS
        (Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (le_sup_left : KS ≤ KS ⊔ U)) (Subgroup.inclusion_injective _))
    rcases hlat (KS ⊔ U) le_sup_right with h1 | h1 | h1 | h1
    · apply hns
      rw [h1]
      have := hU2.isNilpotent
      infer_instance
    · exact hns (h1 ▸ hHs)
    · exact hns (h1 ▸ hNs)
    · exact hne h1
  obtain ⟨P, hP⟩ := residualOvergroups_of_rank2 hR hTits hUS
  set Ab := modO2Image X A with hAb
  have hAbs : Group.IsSolvable ↥Ab :=
    Group.isSolvable_of_surjective (barMap_surjective hAX)
  set ZS := (Ab ⊓ Y).subgroupOf Y with hZS
  have hZSs : Group.IsSolvable ↥ZS := by
    have h1 : Group.IsSolvable ↥(Ab ⊓ Y) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : Ab ⊓ Y ≤ Ab)) (Subgroup.inclusion_injective _)
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : Ab ⊓ Y ≤ Y)).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hSAb : o2Img X S ≤ Ab :=
    Subgroup.map_mono (show S.subgroupOf X ≤ A.subgroupOf X from fun x hx => hSA hx)
  have hUZ : U ≤ ZS := by
    intro u hu
    exact ⟨hSAb hu.1, u.2⟩
  have hZN : ZS ≤ Subgroup.normalizer ((U : Subgroup ↥Y) : Set ↥Y) :=
    hF ↥Y hR U hUS (fun P' hUP' hcov hs => hres' ⟨U, P', hUS, hUP', hcov, hs⟩) ZS hUZ hZSs
  have hmX : m ∈ X := hAX hmA
  set mb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hmX⟩ with hmb
  have hmbY : mb ∈ Subgroup.normalizer ((Y : Subgroup (O2Q X)) : Set (O2Q X)) :=
    o2Map_mem_normalizer (hXN hmX)
  have hmbAb : mb ∈ Ab := ⟨⟨m, hmX⟩, hmA, rfl⟩
  have hmbU : mb ∈ Subgroup.normalizer ((Ub : Subgroup (O2Q X)) : Set (O2Q X)) := by
    have hR' : Ab ⊓ Y ≤ Subgroup.normalizer ((Ub : Subgroup (O2Q X)) : Set (O2Q X)) := by
      intro z hz
      have := hZN (show (⟨z, hz.2⟩ : ↥Y) ∈ ZS from hz)
      exact mem_normalizer_of_mem_normalizer_subgroupOf hUbY.1 this
    have hUbR : IsSylowTwoOf Ub (Ab ⊓ Y) := A4.isSylowTwoOf_mono hUbY
      (le_inf (inf_le_left.trans hSAb) inf_le_right) inf_le_right
    refine mem_normalizer_of_normal_sylow hUbR hR' ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hmbAb, hmbY⟩
  set α := Y.normalizerMonoidHom ⟨mb, hmbY⟩ with hα
  have hαapp : ∀ y : ↥Y, ((α y : ↥Y) : O2Q X) = mb * y * mb⁻¹ := fun y => rfl
  have hαodd : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) :=
      orderOf_map_dvd _ _
    have h2 : orderOf (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) ∣ orderOf m := by
      rw [Subgroup.orderOf_mk, hmb]
      exact (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
    exact Odd.of_dvd_nat hmodd (h1.trans h2)
  have hαU : U.map α.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
    rintro _ ⟨u, hu, rfl⟩
    show ((α u : ↥Y) : O2Q X) ∈ Ub
    rw [hαapp]
    exact (Subgroup.mem_normalizer_iff.mp hmbU _).mp hu
  have hαK := map_eq_of_residualOvergroupsAt hP hKSperf hKSne hU2 hUKS hne hαodd hαU
  have hmbK : ∀ x ∈ Kb, mb * x * mb⁻¹ ∈ Kb := by
    intro x hx
    have h1 : α ⟨x, hKbY hx⟩ ∈ KS.map α.toMonoidHom := ⟨⟨x, hKbY hx⟩, hx, rfl⟩
    rw [hαK] at h1
    have h2 : ((α ⟨x, hKbY hx⟩ : ↥Y) : O2Q X) ∈ Kb := h1
    rwa [hαapp] at h2
  have hPX : pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) :=
    (F7.isSylowTwoOf_pCoreOf_le l.sylowX).trans l.normalizes
  have hconj : ∀ x ∈ K, m * x * m⁻¹ ∈ K := by
    have hmK : (K.map (MulAut.conj m).toMonoidHom) ≤ K := by
      refine le_of_perfect_of_le_sup (by rw [← Subgroup.map_commutator, hKperf]) ?_
        (pCoreOf_isPGroup 2 X) hPX
      rintro _ ⟨x, hx, rfl⟩
      have hxX : x ∈ X := hKX hx
      have h1 := hmbK _ ⟨⟨x, hxX⟩, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h1
      have h2 : y⁻¹ * (⟨m, hmX⟩ * ⟨x, hxX⟩ * ⟨m, hmX⟩⁻¹) ∈ CFSG.pCore 2 ↥X := by
        have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y =
            QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨m, hmX⟩ * ⟨x, hxX⟩ * ⟨m, hmX⟩⁻¹) := by
          rw [hyx, hmb, map_mul, map_mul, map_inv]
        rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
      have h2' : y⁻¹ * (⟨m, hmX⟩ * ⟨x, hxX⟩ * ⟨m, hmX⟩⁻¹) ∈ CFSG.Open.pCore 2 ↥X := by
        exact h2
      have h3 : (MulAut.conj m).toMonoidHom x = (y : G) *
          ((y⁻¹ * (⟨m, hmX⟩ * ⟨x, hxX⟩ * ⟨m, hmX⟩⁻¹) : ↥X) : G) := by
        simp [MulAut.conj_apply]
      rw [h3]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
        (Subgroup.mem_sup_right ⟨_, h2', rfl⟩)
    intro x hx
    exact hmK ⟨x, hx, rfl⟩
  exact mem_normalizer_of_conj_mem' hconj

end EmbLoc

namespace Emb512

variable {G : Type} [Group G] [Finite G]
variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem eq_of_isSimpleGroup (hs : IsSimpleGroup (O2Q (oTwoUpper H))) : K₁ = oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  have hK₁K : K₁ ≤ K := e.K₁_le_K
  have hsub : IsSubnormal K₁ K := A4.subnormal_of_le_of_le e.comp.2.2.1 hK₁K (oTwoUpper_le H)
  have hKperf : ⁅K, K⁆ = K := by
    rw [hKdef, e.closure]
    exact A3.conjClosure_perfect e.comp.2.1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hsub' : ((K₁.subgroupOf K).map π).IsSubnormal := by
    have h1 : IsSubnormal (K₁.subgroupOf K) (K.subgroupOf K) := A4.subnormal_subgroupOf K hsub
    rw [Subgroup.subgroupOf_self] at h1
    exact (A3.subnormal_top_iff.mp h1).map (QuotientGroup.mk'_surjective _)
  rcases hsub'.eq_bot_or_top_of_isSimpleGroup hs with hbot | htop
  · exfalso
    have hle : K₁.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      intro x hx
      have : π x ∈ (K₁.subgroupOf K).map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    have h2 : IsPGroup 2 ↥K₁ :=
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hle).of_equiv
        (Subgroup.subgroupOfEquivOfLe hK₁K)
    have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr e.comp.2.1
    have : Nontrivial ↥K₁ := (Subgroup.nontrivial_iff_ne_bot K₁).mpr e.comp.1
    have : Group.IsNilpotent ↥K₁ := h2.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥K₁ inferInstance
  · have hle : K ≤ K₁ ⊔ pCoreOf 2 K := by
      intro x hx
      have hmem : π ⟨x, hx⟩ ∈ (K₁.subgroupOf K).map π := by rw [htop]; trivial
      obtain ⟨y, hy, hyx⟩ := hmem
      have h1 : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
        exact hyx
      have h1' : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.Open.pCore 2 ↥K := by
        exact h1
      have hx' : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : G) := by simp
      rw [hx']
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
        (Subgroup.mem_sup_right ⟨_, h1', rfl⟩)
    exact eq_of_isSubnormal_of_le_sup hsub hKperf (pCoreOf_isPGroup 2 K) (pCoreOf_le 2 K) hle
      le_rfl

theorem lie_normalizes
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactF5113)
    (htype : (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))))
    (hres : ¬ ∃ U P : Subgroup (O2Q (conjClosure Kh₁ T)), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      P ⋖ ⊤ ∧ Group.IsSolvable ↥P) :
    D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have h := e.hyp.toHyp5_0_1
  have hsimple : IsSimpleGroup (O2Q (oTwoUpper H)) := by
    rcases htype with ⟨hS, -⟩ | ⟨hL2, -⟩
    · exact isSimpleGroup_of_psl2_or_sz (Or.inr hS)
    · exact isSimpleGroup_of_lieModel_PSL2 hL2
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup hsimple
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  rw [hcl] at htype hres
  rw [← heq] at htype ⊢
  have hD := e.nota.2.1
  have hDcyc := (h.isCyclic_card_of_isHall l2TorusFact hD).1
  have hDs : Group.IsSolvable ↥D := by
    have := hDcyc
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  have hTLs : Group.IsSolvable ↥(T ⊓ L) := by
    have := (h.sylow.1.to_le (inf_le_left : T ⊓ L ≤ T)).isNilpotent
    infer_instance
  have hBs : Group.IsSolvable ↥(borelL T L) := by
    rw [← h.borelL_eq_sup hD, sup_comm]
    exact A3.isSolvable_sup_of_le_normalizer (hD.1.trans inf_le_right)
  have hBTs : Group.IsSolvable ↥(borelL T L ⊔ T) := by
    have : Group.IsSolvable ↥T := by
      have := h.sylow.1.isNilpotent
      infer_instance
    exact A3.isSolvable_sup_of_le_normalizer h.T_le_normalizer_borel
  have hA₀s : Group.IsSolvable ↥((borelL T L ⊔ T) ⊓ X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : (borelL T L ⊔ T) ⊓ X ≤ _))
      (Subgroup.inclusion_injective _)
  intro m hm
  have hmodd : Odd (orderOf m) := Odd.of_dvd_nat hD.2.1 (by
    have := orderOf_dvd_natCard (⟨m, hm.1⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this)
  exact (e.toLoc heq).lie_normalizes h37 h38 hF htype hres
    (le_inf le_sup_right e.T_le_X) inf_le_right hA₀s
    ⟨Subgroup.mem_sup_left (hD.1 hm.1), hm.2⟩ hmodd

end Emb512

theorem stmt5_1_13_loc_lie_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactF5113) :
    Stmt5_1_13_loc_lie := by
  intro G _ _ hs hnab hQ S X K Kh A k hOX hSX hKX hK hSK hhat hlt htype hres hSA hAX hAs m hm
    hmodd
  exact (⟨hs, hnab, hQ, hOX, hSX, hKX, hK, hSK, hhat, hlt⟩ : EmbLoc G S X K Kh).lie_normalizes
    h37 h38 hF htype hres hSA hAX hAs hm hmodd

end CFSG.Quasithin.H13
