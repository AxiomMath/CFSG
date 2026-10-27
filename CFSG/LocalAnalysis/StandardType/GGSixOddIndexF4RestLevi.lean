module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLocal
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

namespace F4Rest

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.RankThree.Chevalley Matrix

local instance f4RestLeviNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Linear

theorem card_le_pow_of_injective_GL {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {φ : G →* GL ι K} (hφ : Function.Injective φ) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (Fintype.card ι / OrdPNS.ordQ K p) := by
  let f : G → Module.End K (ι → K) := fun g => Matrix.toLinAlgEquiv' ((φ g : GL ι K) : Matrix ι ι K)
  have hf : Function.Injective f := fun a b h =>
    hφ (Units.ext (Matrix.toLinAlgEquiv'.injective h))
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [f, map_mul, Units.val_mul]
  have h := OrdPNS.card_le_pow_ordQ (V := ι → K) hp hpK (f '' (E : Set G))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      change f a * f b = f b * f a
      rw [← hfmul, ← hfmul, hab])
    (by
      rintro _ ⟨a, ha, rfl⟩
      have hpow : ∀ n : ℕ, f a ^ n = f (a ^ n) := fun n => by
        induction n with
        | zero => simp [f]
        | succ n ih => rw [pow_succ, ih, ← hfmul, ← pow_succ]
      rw [hpow, hE.2 a ha]
      simp [f])
  rw [Module.finrank_fintype_fun_eq_card] at h
  calc Nat.card E = Nat.card (f '' (E : Set G)) := (Nat.card_image_of_injective hf _).symm
    _ ≤ _ := h

theorem two_le_ordQ {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hpq : ¬ p ∣ Nat.card K - 1) : 2 ≤ OrdPNS.ordQ K p := by
  have h0 := OrdPNS.ordQ_pos hp hpK
  by_contra h
  have h1 : OrdPNS.ordQ K p = 1 := by omega
  rw [OrdPNS.ordQ_def, orderOf_eq_one_iff] at h1
  apply hpq
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hK1, h1, Nat.cast_one, sub_self]

theorem div_le_div_two {n d : ℕ} (hd : 2 ≤ d) : n / d ≤ n / 2 :=
  Nat.div_le_div_left hd (by norm_num)

theorem card_le_of_le_of_injective_GL {G : Type*} [Group G] {X : Subgroup G} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {φ : X →* GL ι K} (hφ : Function.Injective φ) {E : Subgroup G}
    (hEX : E ≤ X) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (Fintype.card ι / OrdPNS.ordQ K p) := by
  have h := card_le_pow_of_injective_GL hp hpK hφ (isElemAbelian_subgroupOf X hE)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv] at h

theorem natCast_ne_zero_of_charTwo {K : Type*} [Field K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm

end Linear

section Span

variable {τ : Tag} {K : Type} [Field K]

theorem subsystemGroup_le_rootSpan {A : Set (Fin τ.rank)} {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ j ∈ A, Pi.single j 1 ∈ S ∧ -Pi.single j 1 ∈ S) :
    subsystemGroup τ K A ≤ rootSpan τ K S := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup τ K α) _ (hS j hj).1
      (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [← pinnedX_neg_single]
    exact le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup τ K α) _ (hS j hj).2
      (Subgroup.subset_closure ⟨c, rfl⟩)

theorem subsystemGroup_mono {A B : Set (Fin τ.rank)} (h : A ⊆ B) :
    subsystemGroup τ K A ≤ subsystemGroup τ K B :=
  Subgroup.closure_mono fun _ ⟨j, hj, c, hc⟩ => ⟨j, h hj, c, hc⟩

theorem subsystemGroup_union (A B : Set (Fin τ.rank)) :
    subsystemGroup τ K (A ∪ B) = subsystemGroup τ K A ⊔ subsystemGroup τ K B := by
  rw [subsystemGroup, subsystemGroup, subsystemGroup, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨j, hj | hj, c, hc⟩
    · exact Or.inl ⟨j, hj, c, hc⟩
    · exact Or.inr ⟨j, hj, c, hc⟩
  · rintro (⟨j, hj, c, hc⟩ | ⟨j, hj, c, hc⟩)
    · exact ⟨j, Or.inl hj, c, hc⟩
    · exact ⟨j, Or.inr hj, c, hc⟩

end Span

section Sp6

variable {K : Type} [Field K]

theorem single_mem_c3LeviRoots {j : Fin Tag.F4.rank} (hj : j ≠ 0) :
    Pi.single j 1 ∈ c3LeviRoots ∧ -Pi.single j 1 ∈ c3LeviRoots :=
  ⟨mem_c3LeviRoots.2 ⟨isRoot_single _ j, Pi.single_eq_of_ne (Ne.symm hj) _⟩,
    mem_c3LeviRoots.2 ⟨IsRoot.neg (isRoot_single _ j), by
      show -((Pi.single j 1 : Fin Tag.F4.rank → ℤ) 0) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hj), neg_zero]⟩⟩

theorem single_mem_b3LeviRoots {j : Fin Tag.F4.rank} (hj : j ≠ 3) :
    Pi.single j 1 ∈ b3LeviRoots ∧ -Pi.single j 1 ∈ b3LeviRoots :=
  ⟨mem_b3LeviRoots.2 ⟨isRoot_single _ j, Pi.single_eq_of_ne (Ne.symm hj) _⟩,
    mem_b3LeviRoots.2 ⟨IsRoot.neg (isRoot_single _ j), by
      show -((Pi.single j 1 : Fin Tag.F4.rank → ℤ) 3) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hj), neg_zero]⟩⟩

theorem pow_six_div_le {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hd : 2 ≤ OrdPNS.ordQ K p) :
    p ^ (Fintype.card (Fin 3 ⊕ Fin 3) / OrdPNS.ordQ K p) ≤ p ^ 3 := by
  refine Nat.pow_le_pow_right hp.pos ?_
  rw [Fintype.card_sum, Fintype.card_fin]
  exact (div_le_div_two hd).trans (by norm_num)

theorem card_le_of_le_subsystemGroup_zero
    [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL .F4 K)} (hE : E ≤ subsystemGroup .F4 K {j | j ≠ 0})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpK := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have hle : rootSpan .F4 K c3LeviRoots ≤ adjointGroup .F4 K := rootSpan_le_adjointGroup K _
  let φ : rootSpan .F4 K c3LeviRoots →* GL (Fin 3 ⊕ Fin 3) K :=
    (Subgroup.subtype _).comp ((c3LeviEquiv K).symm.toMonoidHom.comp
      (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
  have hφ : Function.Injective φ := (Subgroup.subtype_injective _).comp
    ((c3LeviEquiv K).symm.injective.comp (Subgroup.subgroupOfEquivOfLe hle).symm.injective)
  exact (card_le_of_le_of_injective_GL hp hpK hφ
    (hE.trans (subsystemGroup_le_rootSpan fun j hj => single_mem_c3LeviRoots hj)) hEel).trans
    (pow_six_div_le hp (two_le_ordQ hp hpK hpq))

theorem card_le_of_le_subsystemGroup_three
    [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL .F4 K)} (hE : E ≤ subsystemGroup .F4 K {j | j ≠ 3})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpK := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have hle : rootSpan .F4 K b3LeviRoots ≤ adjointGroup .F4 K := rootSpan_le_adjointGroup K _
  let φ : rootSpan .F4 K b3LeviRoots →* GL (Fin 3 ⊕ Fin 3) K :=
    (Subgroup.subtype _).comp ((b3LeviEquiv (K := K)).symm.toMonoidHom.comp
      (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
  have hφ : Function.Injective φ := (Subgroup.subtype_injective _).comp
    ((b3LeviEquiv (K := K)).symm.injective.comp (Subgroup.subgroupOfEquivOfLe hle).symm.injective)
  exact (card_le_of_le_of_injective_GL hp hpK hφ
    (hE.trans (subsystemGroup_le_rootSpan fun j hj => single_mem_b3LeviRoots hj)) hEel).trans
    (pow_six_div_le hp (two_le_ordQ hp hpK hpq))

end Sp6

section Commute

theorem root_support_one_three_check :
    ∀ γ ∈ rootFinset .F4, γ 0 = 0 → γ 2 = 0 → γ 1 = 0 ∨ γ 3 = 0 := by
  decide +kernel

theorem root_support_zero_two_check :
    ∀ γ ∈ rootFinset .F4, γ 1 = 0 → γ 3 = 0 → γ 0 = 0 ∨ γ 2 = 0 := by
  decide +kernel

theorem pair_cond_of_check
    {a b c d : Fin Tag.F4.rank} (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b)
    (hch : ∀ γ ∈ rootFinset .F4, γ c = 0 → γ d = 0 → γ a = 0 ∨ γ b = 0) :
    ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → (∀ k, k ≠ a → k ≠ b → γ k = 0) →
      γ a = 0 ∨ γ b = 0 :=
  fun γ hγ hk => hch γ (mem_rootFinset.2 hγ) (hk c hca hcb) (hk d hda hdb)

variable {K : Type} [Field K]

theorem commute_pinnedX_single {a b : Fin Tag.F4.rank} (hab : a ≠ b)
    (hcheck : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → (∀ k, k ≠ a → k ≠ b → γ k = 0) →
      γ a = 0 ∨ γ b = 0)
    {s t : Fin Tag.F4.rank → ℤ} (hs : s = Pi.single a 1 ∨ s = -Pi.single a 1)
    (ht : t = Pi.single b 1 ∨ t = -Pi.single b 1) (c d : K) :
    Commute (pinnedX .F4 K s c) (pinnedX .F4 K t d) := by
  have hsr : IsRoot .F4 s := by
    rcases hs with rfl | rfl
    exacts [isRoot_single _ a, IsRoot.neg (isRoot_single _ a)]
  have htr : IsRoot .F4 t := by
    rcases ht with rfl | rfl
    exacts [isRoot_single _ b, IsRoot.neg (isRoot_single _ b)]
  have hsa : s a ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have hta : t a = 0 := by rcases ht with rfl | rfl <;> simp [hab]
  refine CFSG.LieType.Ree.commute_pinnedX_of_forall_not_isRoot K hsr htr ?_ ?_ ?_ c d
  · intro h
    apply hsa
    rw [h, hta]
  · intro h
    apply hsa
    rw [h, Pi.neg_apply, hta, neg_zero]
  · intro m n hm hn hroot
    have hk : ∀ k, k ≠ a → k ≠ b → (m • s + n • t) k = 0 := by
      intro k hka hkb
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hka, hkb]
    rcases hcheck _ hroot hk with h | h
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hab] at h <;> omega
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [Ne.symm hab] at h <;> omega

theorem commute_subsystemGroup {A B : Set (Fin Tag.F4.rank)}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ →
      (∀ k, k ≠ a → k ≠ b → γ k = 0) → γ a = 0 ∨ γ b = 0) :
    ∀ x ∈ subsystemGroup .F4 K A, ∀ y ∈ subsystemGroup .F4 K B, Commute x y := by
  have hgen : ∀ x ∈ {g | ∃ i ∈ A, ∃ c : K, g = xUnit .F4 K i c ∨ g = yUnit .F4 K i c},
      ∀ y ∈ {g | ∃ i ∈ B, ∃ c : K, g = xUnit .F4 K i c ∨ g = yUnit .F4 K i c}, Commute x y := by
    rintro _ ⟨a, ha, c, rfl | rfl⟩ _ ⟨b, hb, d, rfl | rfl⟩ <;>
      [rw [← pinnedX_single, ← pinnedX_single]; rw [← pinnedX_single, ← pinnedX_neg_single];
        rw [← pinnedX_neg_single, ← pinnedX_single];
        rw [← pinnedX_neg_single, ← pinnedX_neg_single]] <;>
      exact commute_pinnedX_single (h a ha b hb).1 (h a ha b hb).2 (by simp) (by simp) c d
  intro x hx y hy
  have hle : subsystemGroup .F4 K B ≤ Subgroup.centralizer (subsystemGroup .F4 K A : Set _) := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hle' : subsystemGroup .F4 K A ≤ Subgroup.centralizer ({y} : Set (ModGL .F4 K)) :=
      (Subgroup.closure_le _).2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (hgen x hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle' hx)
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

end Commute

section Inter

variable {K : Type} [Field K]

theorem cartan_F4_entries :
    Tag.F4.cartan 0 0 = 2 ∧ Tag.F4.cartan 0 1 = -1 ∧ Tag.F4.cartan 0 2 = 0 ∧
    Tag.F4.cartan 0 3 = 0 ∧ Tag.F4.cartan 1 0 = -1 ∧ Tag.F4.cartan 1 1 = 2 ∧
    Tag.F4.cartan 1 2 = -1 ∧ Tag.F4.cartan 1 3 = 0 ∧ Tag.F4.cartan 2 0 = 0 ∧
    Tag.F4.cartan 2 1 = -2 ∧ Tag.F4.cartan 2 2 = 2 ∧ Tag.F4.cartan 2 3 = -1 ∧
    Tag.F4.cartan 3 0 = 0 ∧ Tag.F4.cartan 3 1 = 0 ∧ Tag.F4.cartan 3 2 = -1 ∧
    Tag.F4.cartan 3 3 = 2 := by
  decide

theorem eq_one_of_sq_eq_one [CharP K 2] {u : Kˣ} (hu : u ^ 2 = 1) : u = 1 := by
  have hu' : (u : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h : ((u : K) - 1) ^ 2 = 0 := by linear_combination hu' - ((u : K) - 1) * h2
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h))

theorem eq_one_of_torus_long_eq_short
    [CharP K 2] {ω a b : Kˣ} (hω : ω ^ 3 = 1)
    (h : torusElt .F4 K 0 ω * torusElt .F4 K 1 ω⁻¹ = torusElt .F4 K 2 a * torusElt .F4 K 3 b) :
    ω = 1 := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h
  have h' := rootDiagUnit_injective h
  obtain ⟨-, c01, c02, -, -, c11, c12, -, -, c21, c22, c23, -, c31, c32, c33⟩ := cartan_F4_entries
  have h1 := congrFun h' 1
  have h2 := congrFun h' 2
  have h3 := congrFun h' 3
  simp only [Pi.mul_apply, c01, c11, c21, c31, c02, c12, c22, c32, c23, c33] at h1 h2 h3
  have h03 : Tag.F4.cartan 0 3 = 0 := by decide
  have h13 : Tag.F4.cartan 1 3 = 0 := by decide
  rw [h03, h13] at h3
  have ha : a = 1 := by
    apply eq_one_of_sq_eq_one
    have e : ω ^ (-1 : ℤ) * ω⁻¹ ^ (2 : ℤ) = (ω ^ 3)⁻¹ := by group
    rw [e, hω, inv_one, zpow_zero, mul_one] at h1
    have : a ^ (2 : ℤ) = 1 := by rw [← _root_.inv_inj, ← _root_.zpow_neg, ← h1, inv_one]
    exact_mod_cast this
  subst ha
  have hb : b = 1 := by
    apply eq_one_of_sq_eq_one
    simp at h3
    exact_mod_cast h3.symm
  subst hb
  simpa using h2

theorem eq_one_of_torus_short_eq_long
    [CharP K 2] {ω a b : Kˣ} (hω : ω ^ 3 = 1)
    (h : torusElt .F4 K 2 ω * torusElt .F4 K 3 ω⁻¹ = torusElt .F4 K 0 a * torusElt .F4 K 1 b) :
    ω = 1 := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h
  have h' := rootDiagUnit_injective h
  obtain ⟨c00, c01, c02, -, c10, c11, c12, -, c20, c21, c22, -, c30, c31, c32, -⟩ :=
    cartan_F4_entries
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  have h2 := congrFun h' 2
  simp only [Pi.mul_apply, c00, c01, c02, c10, c11, c12, c20, c21, c22, c30, c31, c32] at h0 h1 h2
  have hb : b = 1 := by
    have e : ω ^ (2 : ℤ) * ω⁻¹ ^ (-1 : ℤ) = ω ^ 3 := by group
    rw [e, hω, zpow_zero, one_mul] at h2
    have : b ^ (-1 : ℤ) = 1 := h2.symm
    simpa using this
  subst hb
  have ha : a = 1 := by
    apply eq_one_of_sq_eq_one
    simp at h0
    exact_mod_cast h0.symm
  subst ha
  apply eq_one_of_sq_eq_one
  simpa using h1


theorem eq_torus_of_central (κ : F4A2Kind) {z : ModGL .F4 K}
    (hz : z ∈ subsystemGroup .F4 K {κ.i, κ.j})
    (hc : ∀ y ∈ subsystemGroup .F4 K {κ.i, κ.j}, Commute z y) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ z = torusElt .F4 K κ.i ω * torusElt .F4 K κ.j ω⁻¹ := by
  obtain ⟨-, -, htor, -⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics
    (K := K) κ
  set r := f4A2Equiv K κ with hr
  have hcen : r ⟨z, hz⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨y, rfl⟩ := r.surjective B
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).eq.symm
  obtain ⟨ω₀, hω₀, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  have hω₀' : ω₀ ^ 3 = 1 := by simpa using hω₀
  have hω0 : ω₀ ≠ 0 := by
    rintro rfl
    norm_num at hω₀'
  set ω : Kˣ := Units.mk0 ω₀ hω0 with hωdef
  refine ⟨ω, Units.ext (by simp [ω, hω₀']), ?_⟩
  have hinv : ω₀⁻¹ * ω₀⁻¹ = ω₀ := by
    calc ω₀⁻¹ * ω₀⁻¹ = ω₀⁻¹ * ω₀⁻¹ * ω₀ ^ 3 := by rw [hω₀', mul_one]
      _ = ω₀ := by field_simp
  have e := htor ω ω⁻¹
  have hrz : r ⟨z, hz⟩ = r ⟨torusElt .F4 K κ.i ω * torusElt .F4 K κ.j ω⁻¹,
      SteinbergBN.torusElt_pair_mem κ.i κ.j ω ω⁻¹⟩ := by
    apply Subtype.ext
    rw [← hscal, e, Matrix.scalar_apply]
    congr 1
    funext k
    fin_cases k
    · simp [ω]
    · simp [ω, hinv]
    · simp [ω]
  exact congrArg Subtype.val (r.injective hrz)

theorem commute_long_three :
    ∀ x ∈ subsystemGroup .F4 K {0, 1}, ∀ y ∈ subsystemGroup .F4 K {3}, Commute x y := by
  refine commute_subsystemGroup ?_
  rintro a (rfl | rfl) b rfl
  · exact ⟨by decide, pair_cond_of_check (c := 1) (d := 2) (by decide) (by decide) (by decide)
      (by decide) f4_root_support_zero_three_check⟩
  · refine ⟨by decide, pair_cond_of_check (c := 0) (d := 2) (by decide) (by decide) (by decide)
      (by decide) root_support_one_three_check⟩

theorem commute_zero_short :
    ∀ x ∈ subsystemGroup .F4 K {0}, ∀ y ∈ subsystemGroup .F4 K {2, 3}, Commute x y := by
  refine commute_subsystemGroup ?_
  rintro a rfl b (rfl | rfl)
  · exact ⟨by decide, pair_cond_of_check (c := 1) (d := 3) (by decide) (by decide) (by decide)
      (by decide) root_support_zero_two_check⟩
  · exact ⟨by decide, pair_cond_of_check (c := 1) (d := 2) (by decide) (by decide) (by decide)
      (by decide) f4_root_support_zero_three_check⟩

theorem inf_eq_bot_long_three [CharP K 2] :
    subsystemGroup .F4 K {0, 1} ⊓ subsystemGroup .F4 K {3} = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzA, hzB⟩
  rw [Subgroup.mem_bot]
  have hc : ∀ y ∈ subsystemGroup .F4 K {0, 1}, Commute z y := fun y hy =>
    (commute_long_three y hy z hzB).symm
  obtain ⟨ω, hω, hz⟩ := eq_torus_of_central F4A2Kind.long hzA hc
  obtain ⟨-, -, -, -, hinf, -⟩ :=
    F4_native_long_and_short_A2_faithful_SL3_all_characteristics (K := K) F4A2Kind.short
  have hzT : z ∈ subsystemGroup .F4 K {F4A2Kind.short.i, F4A2Kind.short.j} ⊓ torusGroup .F4 K :=
    ⟨subsystemGroup_mono (fun x hx => Or.inr hx) hzB, by
      rw [hz]
      exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)⟩
  obtain ⟨a, b, hab⟩ := (hinf z).1 hzT
  have hω1 := eq_one_of_torus_long_eq_short hω (hz.symm.trans hab)
  rw [hz, hω1, inv_one, torusElt_one, torusElt_one, mul_one]

theorem inf_eq_bot_zero_short [CharP K 2] :
    subsystemGroup .F4 K {0} ⊓ subsystemGroup .F4 K {2, 3} = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzA, hzB⟩
  rw [Subgroup.mem_bot]
  have hc : ∀ y ∈ subsystemGroup .F4 K {2, 3}, Commute z y := fun y hy =>
    commute_zero_short z hzA y hy
  obtain ⟨ω, hω, hz⟩ := eq_torus_of_central F4A2Kind.short hzB hc
  obtain ⟨-, -, -, -, hinf, -⟩ :=
    F4_native_long_and_short_A2_faithful_SL3_all_characteristics (K := K) F4A2Kind.long
  have hzT : z ∈ subsystemGroup .F4 K {F4A2Kind.long.i, F4A2Kind.long.j} ⊓ torusGroup .F4 K :=
    ⟨subsystemGroup_mono (fun x hx => Or.inl hx) hzA, by
      rw [hz]
      exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)⟩
  obtain ⟨a, b, hab⟩ := (hinf z).1 hzT
  have hω1 := eq_one_of_torus_short_eq_long hω (hz.symm.trans hab)
  rw [hz, hω1, inv_one, torusElt_one, torusElt_one, mul_one]

end Inter

section Product

theorem card_le_mul_of_le_sup {G : Type*} [Group G] [Finite G] {p : ℕ} {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hdisj : A ⊓ B = ⊥) {a b : ℕ}
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ a)
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F ≤ b)
    {E : Subgroup G} (hE : E ≤ A ⊔ B) (hEel : IsElemAbelian p E) : Nat.card E ≤ a * b := by
  set Φ := A.subtype.noncommCoprod B.subtype (commute_subtype_subtype hcomm) with hΦdef
  have hΦ : Function.Injective Φ := injective_noncommCoprod_subtype hcomm hdisj
  have hrange : Φ.range = A ⊔ B := range_noncommCoprod_subtype hcomm
  set Et := E.comap Φ with hEtdef
  have hcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map Φ) := (Subgroup.card_map_of_injective hΦ).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self (hrange.symm ▸ hE)]
  have hel : IsElemAbelian p Et := isElemAbelian_comap hΦ hEel
  have h1 := hA (Et.map (MonoidHom.fst A B)) (isElemAbelian_map _ hel)
  have h2 := hB (Et.map (MonoidHom.snd A B)) (isElemAbelian_map _ hel)
  have hinj : Nat.card Et ≤
      Nat.card (Et.map (MonoidHom.fst A B)) * Nat.card (Et.map (MonoidHom.snd A B)) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.1.1, x.1, x.2, rfl⟩, ⟨x.1.2, x.1, x.2, rfl⟩)) ?_
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hxy.1) (congrArg Subtype.val hxy.2))
  rw [← hcard]
  exact hinj.trans (Nat.mul_le_mul h1 h2)

variable {K : Type} [Field K]

theorem card_le_of_le_A2 (κ : F4A2Kind) [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) {X : Subgroup (ModGL .F4 K)}
    (hX : X ≤ subsystemGroup .F4 K {κ.i, κ.j}) (F : Subgroup X) (hF : IsElemAbelian p F) :
    Nat.card F ≤ p := by
  have hpK := natCast_ne_zero_of_charTwo (K := K) hp hp2
  let φ : X →* GL (Fin 3) K :=
    (Matrix.SpecialLinearGroup.toGL.comp (f4A2Equiv K κ).toMonoidHom).comp
      (Subgroup.inclusion hX)
  have hφ : Function.Injective φ := (Matrix.SpecialLinearGroup.toGL_injective.comp
    (f4A2Equiv K κ).injective).comp (Subgroup.inclusion_injective hX)
  calc Nat.card F ≤ p ^ (Fintype.card (Fin 3) / OrdPNS.ordQ K p) :=
        card_le_pow_of_injective_GL hp hpK hφ hF
    _ ≤ p ^ 1 := by
        refine Nat.pow_le_pow_right hp.pos ?_
        rw [Fintype.card_fin]
        exact (div_le_div_two (two_le_ordQ hp hpK hpq)).trans (by norm_num)
    _ = p := pow_one p

theorem card_le_of_le_subsystemGroup_two [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) {E : Subgroup (ModGL .F4 K)}
    (hE : E ≤ subsystemGroup .F4 K {j | j ≠ 2}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  have : Finite (ModGL .F4 K) := finite_modGL
  have hset : ({j | j ≠ 2} : Set (Fin Tag.F4.rank)) = {0, 1} ∪ {3} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases j <;> decide
  rw [hset, subsystemGroup_union] at hE
  have h := card_le_mul_of_le_sup commute_long_three inf_eq_bot_long_three
    (card_le_of_le_A2 F4A2Kind.long hp hp2 hpq le_rfl)
    (card_le_of_le_A2 F4A2Kind.short hp hp2 hpq (subsystemGroup_mono fun x hx => Or.inr hx))
    hE hEel
  calc Nat.card E ≤ p * p := h
    _ ≤ p ^ 3 := by
        rw [← pow_two]
        exact Nat.pow_le_pow_right hp.pos (by norm_num)

theorem card_le_of_le_subsystemGroup_one [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) {E : Subgroup (ModGL .F4 K)}
    (hE : E ≤ subsystemGroup .F4 K {j | j ≠ 1}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  have : Finite (ModGL .F4 K) := finite_modGL
  have hset : ({j | j ≠ 1} : Set (Fin Tag.F4.rank)) = {0} ∪ {2, 3} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases j <;> decide
  rw [hset, subsystemGroup_union] at hE
  have h := card_le_mul_of_le_sup commute_zero_short inf_eq_bot_zero_short
    (card_le_of_le_A2 F4A2Kind.long hp hp2 hpq (subsystemGroup_mono fun x hx => Or.inl hx))
    (card_le_of_le_A2 F4A2Kind.short hp hp2 hpq le_rfl) hE hEel
  calc Nat.card E ≤ p * p := h
    _ ≤ p ^ 3 := by
        rw [← pow_two]
        exact Nat.pow_le_pow_right hp.pos (by norm_num)

end Product

section Main

theorem ggF4LeviRankInput_holds
    {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) :
    GGF4LeviRankInput K p := by
  intro i E hE hEel
  fin_cases i
  · exact card_le_of_le_subsystemGroup_zero hp hp2 hpq hE hEel
  · exact card_le_of_le_subsystemGroup_one hp hp2 hpq hE hEel
  · exact card_le_of_le_subsystemGroup_two hp hp2 hpq hE hEel
  · exact card_le_of_le_subsystemGroup_three hp hp2 hpq hE hEel

theorem ggF4TwoLocalRankInput_holds :
    GGF4TwoLocalRankInput :=
  ggF4TwoLocalRankInput_of_levi fun _ _ _ _ _ hp hp2 hpq => ggF4LeviRankInput_holds hp hp2 hpq

end Main

end F4Rest

end CFSG.StandardType
