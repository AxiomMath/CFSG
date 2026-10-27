module

public import CFSG.Quasithin.H13.A6S13821d
public import CFSG.Quasithin.H13.A6S13825p
public import CFSG.Quasithin.H13.A6S13821c

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def Case13821Hat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 6))

@[expose] def Case13821Hat7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7))

@[expose] def Case13821M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ IsSporadic .M22 (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Case13821HatM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22)

@[expose] def Case13821L32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) → S.L1 ≤ K

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem ker_starHom_eq {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) :
    (S1549C.starHom hF).ker = CFSG.pCore 2 ↥H := by
  ext x
  rw [MonoidHom.mem_ker, S1549C.starHom_eq_one_iff hF, ← pCoreOf_subgroupOf_eq H,
    Subgroup.mem_subgroupOf]

@[expose] noncomputable def modO2EquivKst {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H) :
    (↥H ⧸ CFSG.pCore 2 ↥H) ≃* ↥(S.KSt H H) :=
  ((QuotientGroup.quotientMulEquivOfEq (S.ker_starHom_eq hF).symm).trans
    (QuotientGroup.quotientKerEquivRange (S1549C.starHom hF))).trans
    (MulEquiv.subgroupCongr (S.kst_top hF).symm)

theorem map_modO2EquivKst {H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    {K : Subgroup G} (hKH : K ≤ H) :
    ((modO2Image H K).map (S.modO2EquivKst hF).toMonoidHom).map (S.KSt H H).subtype =
      S.KSt H K := by
  rw [S.kst_eq hF hKH, modO2Image, Subgroup.map_map, Subgroup.map_map]
  congr 1

end Setting4

theorem card_outer_dvd_two_of_l32 {X : Type} [Group X] [Finite X] (h : IsPSL 3 2 1 X) :
    Nat.card (Outer X) ∣ 2 := by
  have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl Nat.prime_two le_rfl h).1
  refine hb.trans ?_
  simp [CFSG.RankThree.OuterOrder.determinantParameter]

theorem nonempty_aut_of_l32 {Q : Type} [Group Q] [Finite Q] {Kb : Subgroup Q} [Kb.Normal]
    (hC : Subgroup.centralizer (Kb : Set Q) = ⊥) (hq : CFSG.IsQuasisimple ↥Kb)
    (hP : IsPSL 3 2 1 ↥Kb) (hne : Kb ≠ ⊤) : Nonempty (Q ≃* MulAut ↥Kb) := by
  have : Finite (MulAut ↥Kb) :=
    Finite.of_injective (fun f : MulAut ↥Kb => (f : ↥Kb → ↥Kb)) DFunLike.coe_injective
  let φ : Q →* MulAut ↥Kb := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun f : MulAut ↥Kb => ((f ⟨y, hy⟩ : ↥Kb) : Q)) (MonoidHom.mem_ker.mp hx)
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hout := card_outer_dvd_two_of_l32 hP
  have hidx := L32A.C.index_dvd_card_outer hC
  have hidx1 : Kb.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hidx2 : Kb.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (hidx.trans hout) with h | h
    · exact absurd h hidx1
    · exact h
  have hout2 : Nat.card (Outer ↥Kb) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hout with h | h
    · rw [h] at hidx
      rw [hidx2] at hidx
      exact absurd hidx (by norm_num)
    · exact h
  have hZ : Subgroup.center ↥Kb = ⊥ :=
    L32A.C.center_eq_bot_of_list47 hq (Or.inl ⟨3, hP⟩)
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Kb with hInn
  have hinner : Nat.card ↥Inn = Nat.card ↥Kb := by
    have hinj : Function.Injective (MulAut.conj : ↥Kb →* MulAut ↥Kb) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun f : MulAut ↥Kb => f y) (MonoidHom.mem_ker.mp hx)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    rw [hInn, CFSG.ComponentClassification.OuterAutomorphisms.inner,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcardA : Nat.card (MulAut ↥Kb) = Nat.card ↥Kb * 2 := by
    rw [← Inn.card_mul_index, hinner, Subgroup.index, hInn, hout2]
  have hcardQ : Nat.card Q = Nat.card ↥Kb * 2 := by
    rw [← Kb.card_mul_index, hidx2]
  have hb : Function.Bijective φ :=
    (Function.Injective.bijective_of_nat_card_le hφ (by rw [hcardA, hcardQ]))
  exact ⟨MulEquiv.ofBijective φ hb⟩

theorem lem13821_of_cases
    (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (h19 : Lem13819)
    (h20 : Lem13820) (hHat6 : Case13821Hat6) (hHat7 : Case13821Hat7) (hM22 : Case13821M22)
    (hHatM22 : Case13821HatM22) (hL32 : Case13821L32) : Lem13821 := by
  intro G _ _ T L V S hS H hH K hK
  have hall : ∀ K' ∈ cComp H, S.L1 ≤ K' ∧ IsList13821 (↥K' ⧸ CFSG.pCore 2 ↥K') := fun K' hK' =>
    S.lem13821_list h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391 hI4 h20 hS hH hK'
      (hHat6 G T L V S hS H hH K' hK') (hHat7 G T L V S hS H hH K' hK')
      (hM22 G T L V S hS H hH K' hK') (hHatM22 G T L V S hS H hH K' hK')
      (hL32 G T L V S hS H hH K' hK')
  have hq : ∀ K' ∈ cComp H, CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') := fun K' hK' =>
    S.isQuasisimple_modO2 h36c h139 h1334 h13 hS hH hK'
  have hZ : ∀ K' ∈ cComp H, Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := fun K' hK' =>
    L32A.C.center_eq_bot_of_list47 (hq K' hK') (hall K' hK').2.list47
  obtain ⟨hL1K, hlist⟩ := hall K hK
  have huniq : cComp H = {K} := by
    ext K'
    rw [Set.mem_singleton_iff]
    constructor
    · intro hK'
      exact S.eq_of_mem_cComp_of_L1_le h37 hH hK' hK (hall K' hK').1 hL1K (hZ K' hK')
    · rintro rfl
      exact hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  have hKbn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hqb : CFSG.IsQuasisimple ↥(modO2Image H K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (hq K hK)
  have hlb : IsList13821 ↥(modO2Image H K) := hlist.of_mulEquiv e
  have hZb := L32A.C.center_eq_bot_of_list47 hqb hlb.list47
  have hC := S.centralizer_modO2_eq_bot h139 h1334 h13 hS hH huniq hL1K hZb
  have hdvd := L32A.C.index_dvd_card_outer hC
  have : Finite (MulAut ↥(modO2Image H K)) :=
    Finite.of_injective (fun f : MulAut ↥(modO2Image H K) => (f : ↥(modO2Image H K) → _))
      DFunLike.coe_injective
  obtain ⟨m, hm⟩ := (L32A.C.isPGroup_two_outer_of_list47 hqb hlb.list47).exists_card_eq
  rw [hm] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hHKT : H = K ⊔ T := S.eq_sup_T_of_index hH hKH hj
  obtain ⟨E⟩ := S.kst_equiv hS hH hK
  have hF91 := (hS.hF H hH).toHypF91
  refine ⟨hL1K, ?_, ⟨hHKT.symm, fun hP => ?_⟩, S.commutator_UH_eq_of_L1_le hKH hKN hL1K⟩
  · have h := hlist.of_mulEquiv E
    rcases h with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  ·
    set Θ := S.modO2EquivKst hF91 with hΘ
    have hmap := S.map_modO2EquivKst hF91 hKH
    let eK : ↥(modO2Image H K) ≃* ↥(S.KSt H K) :=
      ((Subgroup.equivMapOfInjective (modO2Image H K) Θ.toMonoidHom Θ.injective).trans
        (Subgroup.equivMapOfInjective _ (S.KSt H H).subtype
          (S.KSt H H).subtype_injective)).trans (MulEquiv.subgroupCongr hmap)
    have hPb : IsPSL 3 2 1 ↥(modO2Image H K) := IsPSL.of_mulEquiv eK.symm hP
    have hne : modO2Image H K ≠ ⊤ := by
      intro htop
      apply h19 G T L V S hS H hH
      refine IsPSL.of_mulEquiv ?_ hPb
      exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans Θ
    obtain ⟨φ⟩ := nonempty_aut_of_l32 hC hqb hPb hne
    exact ⟨(Θ.symm.trans φ).trans (MulAut.congr eK)⟩

end CFSG.Quasithin.H13.A6
