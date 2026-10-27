module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D42Tor
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113TypeF
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Bar
public import CFSG.Quasithin.EmptyFaithful.T1515eE

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

theorem D42C.map_eq_of_card_eq_three_mul {Y : Type*} [Group Y] [Finite Y] {R U : Subgroup Y}
    (hU : IsSylowTwoOf U R)
    (h3 : Nat.card R = 3 * Nat.card ↥(R ⊓ Subgroup.normalizer (U : Set Y)))
    {α : MulAut Y} (hαR : R.map α.toMonoidHom = R) {r : ℕ} (hr : α ^ r = 1)
    (hr6 : Nat.Coprime r 6) : U.map α.toMonoidHom = U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUR : U ≤ R := hU.1
  have hP2 : IsPGroup 2 ↥(U.subgroupOf R) :=
    hU.2.1.comap_of_injective R.subtype R.subtype_injective
  set S₀ : Sylow 2 ↥R := hP2.toSylow hU.2.2 with hS₀def
  have hS₀ : (S₀ : Subgroup ↥R) = U.subgroupOf R := IsPGroup.toSylow_coe _ _
  have hcard : Nat.card (Sylow 2 ↥R) = 3 := by
    rw [Sylow.card_eq_index_normalizer S₀]
    change (Subgroup.normalizer ((S₀ : Subgroup ↥R) : Set ↥R)).index = 3
    rw [hS₀, ← Subgroup.subgroupOf_normalizer_eq hUR]
    have h1 := Subgroup.relIndex_mul_card (Subgroup.normalizer (U : Set Y)) R
    have hpos : 0 < Nat.card ↥(R ⊓ Subgroup.normalizer (U : Set Y)) := Nat.card_pos
    rw [inf_comm, h3] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  let β : MulAut ↥R := (α.subgroupMap R).trans (MulEquiv.subgroupCongr hαR)
  have hβ : ∀ x : ↥R, ((β x : ↥R) : Y) = α x := fun x => rfl
  have hβpow : ∀ k : ℕ, ∀ x : ↥R, (((β ^ k) x : ↥R) : Y) = (α ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hβ]
  have hβr : β ^ r = 1 := by
    ext x
    rw [hβpow, hr]
    rfl
  let π := MulAction.toPermHom (MulAut ↥R) (Sylow 2 ↥R)
  have hπr : (π β) ^ r = 1 := by rw [← map_pow, hβr, map_one]
  have hπ1 : π β = 1 := by
    have h1 : orderOf (π β) ∣ r := orderOf_dvd_of_pow_eq_one hπr
    have h2 : orderOf (π β) ∣ 6 := by
      have := orderOf_dvd_natCard (π β)
      rwa [Nat.card_perm, hcard] at this
    have h3' : orderOf (π β) ∣ Nat.gcd r 6 := Nat.dvd_gcd h1 h2
    rw [hr6.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3'
    exact h3'
  have hfix : β • S₀ = S₀ := congrArg (fun p : Equiv.Perm (Sylow 2 ↥R) => p S₀) hπ1
  have hle : U.map α.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    have hmem : (⟨u, hUR hu⟩ : ↥R) ∈ (S₀ : Subgroup ↥R) := by
      rw [hS₀]
      exact hu
    have h1 : β • (⟨u, hUR hu⟩ : ↥R) ∈ ((β • S₀ : Sylow 2 ↥R) : Subgroup ↥R) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ β _ hmem
    rw [hfix, hS₀] at h1
    exact h1
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge

namespace EmbLoc

variable {G : Type} [Group G] [Finite G]
variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem d42_local
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hsimple : IsSimpleGroup (O2Q K)) (hD4 : Is3D4 2 1 ↥(modO2Image X Kh))
    {A : Subgroup G} (hSA : S ≤ A) (hAX : A ≤ X) (hAs : Group.IsSolvable ↥A) :
    (∀ m ∈ A, Odd (orderOf m) → m ∈ Subgroup.normalizer (K : Set G)) ∨
      ((∀ m ∈ A, Odd (orderOf m) → Nat.Coprime (orderOf m) 3 →
          m ∈ Subgroup.normalizer (K : Set G)) ∧
        ¬ 9 ∣ Nat.card ↥(modO2Image X A ⊓ modO2Image X Kh) ∧
        ∀ F : Subgroup (O2Q X), F ≤ modO2Image X A ⊓ modO2Image X Kh → Nat.card F = 3 →
          ∃ u ∈ o2Img X S ⊓ modO2Image X Kh, ∀ f ∈ F, u * f * u⁻¹ = f⁻¹) := by
  have : IsSimpleGroup G := l.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  obtain ⟨K₀, _, _, σ₀, φ₀, -, -, -, hP, -⟩ :=
    Setup.X6.even_rank_two_residual_triality hD4 hUS
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
  have hPX : pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) :=
    (F7.isSylowTwoOf_pCoreOf_le l.sylowX).trans l.normalizes
  have tail : ∀ (m : G) (hmX : m ∈ X), Odd (orderOf m) →
      U.map (Y.normalizerMonoidHom ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hmX⟩,
        o2Map_mem_normalizer (hXN hmX)⟩).toMonoidHom = U →
      m ∈ Subgroup.normalizer (K : Set G) := by
    intro m hmX hmodd hαU
    set mb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hmX⟩ with hmb
    have hmbY : mb ∈ Subgroup.normalizer ((Y : Subgroup (O2Q X)) : Set (O2Q X)) :=
      o2Map_mem_normalizer (hXN hmX)
    set α := Y.normalizerMonoidHom ⟨mb, hmbY⟩ with hα
    have hαapp : ∀ y : ↥Y, ((α y : ↥Y) : O2Q X) = mb * y * mb⁻¹ := fun y => rfl
    have hαodd : Odd (orderOf α) := by
      have h1 : orderOf α ∣ orderOf (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) :=
        orderOf_map_dvd _ _
      have h2 : orderOf (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) ∣ orderOf m := by
        rw [Subgroup.orderOf_mk, hmb]
        exact (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
      exact Odd.of_dvd_nat hmodd (h1.trans h2)
    have hαK := map_eq_of_residualOvergroupsAt hP hKSperf hKSne hU2 hUKS hne hαodd hαU
    refine mem_normalizer_of_modO2Image hKX hKperf hPX hmX ?_
    refine D42C.mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 : α ⟨x, hKbY hx⟩ ∈ KS.map α.toMonoidHom := ⟨⟨x, hKbY hx⟩, hx, rfl⟩
    rw [hαK] at h1
    have h2 : ((α ⟨x, hKbY hx⟩ : ↥Y) : O2Q X) ∈ Kb := h1
    rwa [hαapp] at h2
  have hAZ : ∀ (m : G) (hmA : m ∈ A),
      ZS.map (Y.normalizerMonoidHom ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hAX hmA⟩,
        o2Map_mem_normalizer (hXN (hAX hmA))⟩).toMonoidHom = ZS := by
    intro m hmA
    have hmbAb : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hAX hmA⟩ ∈ Ab :=
      ⟨⟨m, hAX hmA⟩, hmA, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨Ab.mul_mem (Ab.mul_mem hmbAb hz.1) (Ab.inv_mem hmbAb), Subtype.coe_prop _⟩
  rcases D42C.solvable_overgroup_3d42 hD4 hUS hUZ hZSs with hZN | ⟨h3, h9, hinv⟩
  ·
    left
    intro m hmA hmodd
    have hmX := hAX hmA
    refine tail m hmX hmodd ?_
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
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
    rintro _ ⟨u, hu, rfl⟩
    show mb * (u : O2Q X) * mb⁻¹ ∈ Ub
    exact (Subgroup.mem_normalizer_iff.mp hmbU _).mp hu
  · right
    refine ⟨fun m hmA hmodd hm3 => ?_, ?_, ?_⟩
    · have hmX := hAX hmA
      refine tail m hmX hmodd ?_
      set mb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨m, hmX⟩ with hmb
      have hmbY : mb ∈ Subgroup.normalizer ((Y : Subgroup (O2Q X)) : Set (O2Q X)) :=
        o2Map_mem_normalizer (hXN hmX)
      have hdvd : orderOf (Y.normalizerMonoidHom ⟨mb, hmbY⟩) ∣ orderOf m := by
        have h1 := orderOf_map_dvd (Y.normalizerMonoidHom) ⟨mb, hmbY⟩
        have h2 : orderOf (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) ∣
            orderOf m := by
          rw [Subgroup.orderOf_mk, hmb]
          exact (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
        exact h1.trans h2
      have hr6 : Nat.Coprime (orderOf m) 6 := by
        have h2 : Nat.Coprime (orderOf m) 2 :=
          Nat.coprime_two_right.mpr hmodd
        exact Nat.Coprime.mul_right h2 hm3
      exact D42C.map_eq_of_card_eq_three_mul (A4.isSylowTwoOf_mono hUS hUZ le_top) h3
        (hAZ m hmA) (orderOf_dvd_iff_pow_eq_one.mp hdvd) hr6
    · have hc : Nat.card ZS = Nat.card ↥(Ab ⊓ Y) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Ab ⊓ Y ≤ Y)).toEquiv
      rwa [← hc]
    · intro F hF hF3
      have hFY : F ≤ Y := hF.trans inf_le_right
      have hF' : F.subgroupOf Y ≤ ZS := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hF (Subgroup.mem_subgroupOf.mp hx))
      have hF'3 : Nat.card (F.subgroupOf Y) = 3 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv).trans hF3
      obtain ⟨u, hu, hinvu⟩ := hinv _ hF' hF'3
      refine ⟨(u : O2Q X), Subgroup.mem_subgroupOf.mp hu, fun f hf => ?_⟩
      have := hinvu ⟨f, hFY hf⟩ (Subgroup.mem_subgroupOf.mpr hf)
      exact congrArg Subtype.val this

end EmbLoc

section Vocabulary

variable {G : Type} [Group G]

@[expose] def Type3D4 (T D X Kh K : Subgroup G) : Prop :=
  Is3D4 2 1 (O2Q Kh) ∧ Kh = oThreePrimeResidual X ∧
    ∃ D₃ : Subgroup G, D₃ ≤ D ⊓ Kh ∧ Nat.card D₃ = 3 ∧
      ¬ D₃ ≤ Subgroup.normalizer (K : Set G) ∧ ¬ 9 ∣ Nat.card ↥(D ⊓ Kh) ∧
      Nat.card ↥(D ⊓ Kh) ∣ 211341312 ∧ ∃ t ∈ T ⊓ Kh, ∀ d ∈ D₃, t * d * t⁻¹ = d⁻¹

end Vocabulary

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem type3D4
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h37' : Vol2Native.A37ForSQTKCat) (h38' : Vol2Native.A38ForSQTKCat)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) {k : ℕ} (hk : IsFieldParam510 T H k)
    (htype : (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))))
    (hres : ∃ U P : Subgroup (O2Q (conjClosure Kh₁ T)), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
      Group.IsSolvable ↥P) :
    LieModel (O2Q (oTwoUpper H)) .PSL 2 2 3 ∧
      Type3D4 T D X (conjClosure Kh₁ T) (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have e := m.toEmb512 hk
  have hsimple : IsSimpleGroup (O2Q (oTwoUpper H)) := by
    rcases htype with ⟨hS, -⟩ | ⟨hL2, -⟩
    · exact isSimpleGroup_of_psl2_or_sz (Or.inr hS)
    · exact isSimpleGroup_of_lieModel_PSL2 hL2
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup hsimple
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  rw [hcl] at htype hres ⊢
  have hnotK : ¬ D ⊓ X ≤ Subgroup.normalizer (K₁ : Set G) := heq ▸ m.not_le
  rw [← heq] at htype hsimple ⊢
  have l := e.toLoc heq
  obtain ⟨hL8, hD4⟩ := D42.is3D4_bar l htype hres
  refine ⟨hL8, ?_⟩
  have hD := m.nota.2.1
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
  have hDA : D ⊓ X ≤ (borelL T L ⊔ T) ⊓ X :=
    inf_le_inf_right X (hD.1.trans le_sup_left)
  rcases l.d42_local h37' h38' hsimple hD4 (le_inf le_sup_right e.T_le_X) inf_le_right hA₀s with
    hall | ⟨h3', h9, hinv⟩
  · exfalso
    apply hnotK
    intro d hd
    refine hall d (hDA hd) (Odd.of_dvd_nat hD.2.1 ?_)
    have := orderOf_dvd_natCard (⟨d, hd.1⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hKhX : Kh₁ ≤ X := le_of_mem_cComp hKhc
  have hTX : T ≤ X := e.T_le_X
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  have hDodd : Odd (Nat.card ↥D) := hD.2.1
  have hoddD : ∀ d ∈ D, Odd (orderOf d) := fun d hd => Odd.of_dvd_nat hDodd (by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this)
  have hD2 : ∀ d ∈ D, d ∈ pCoreOf 2 X → d = 1 := by
    intro d hdD hd2
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 X) ⟨d, hd2⟩
    have hda : d ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hodd : Odd (orderOf d) := hoddD d hdD
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hda)
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (by simp [Nat.even_pow])
  have hπ2 : ∀ (x : G) (hx : x ∈ X), QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ = 1 →
      x ∈ pCoreOf 2 X := by
    intro x hx h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    exact ⟨_, h1, rfl⟩
  obtain ⟨eH⟩ := modO2_mulEquiv hKhc
  have hS : A318Exclusion ↥(modO2Image X Kh₁) :=
    a318Exclusion_d42 (fun _ _ _ h => two_le_pRank_of_is3D4_two1515e h) hD4
  have hSK : A318Exclusion (O2Q Kh₁) := A318Exclusion.of_mulEquiv eH hS
  have hKh3 : Kh₁ = oThreePrimeResidual X := m.hat_eq_oThreePrimeResidual hF h36 h38 hSK
  have h3el : ∀ d ∈ X, (∃ k : ℕ, d ^ 3 ^ k = 1) → d ∈ Kh₁ := by
    intro d hd hk
    rw [hKh3]
    exact Subgroup.subset_closure ⟨hd, hk⟩
  have hDKX : D ⊓ Kh₁ ≤ X := inf_le_right.trans hKhX
  let ψ : ↥(D ⊓ Kh₁) →* O2Q X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hDKX)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 := hD2 _ d.2.1 (hπ2 _ (hDKX d.2) hd)
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hψA : ψ.range ≤ modO2Image X ((borelL T L ⊔ T) ⊓ X) ⊓ modO2Image X Kh₁ := by
    rintro _ ⟨d, rfl⟩
    exact ⟨⟨⟨d, hDKX d.2⟩, Subgroup.mem_subgroupOf.mpr (hDA ⟨d.2.1, hDKX d.2⟩), rfl⟩,
      ⟨⟨d, hDKX d.2⟩, Subgroup.mem_subgroupOf.mpr d.2.2, rfl⟩⟩
  have hDK9 : ¬ 9 ∣ Nat.card ↥(D ⊓ Kh₁) := by
    intro h9'
    apply h9
    rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv] at h9'
    exact h9'.trans (Subgroup.card_dvd_of_le hψA)
  have hDKc : Nat.card ↥(D ⊓ Kh₁) ∣ 211341312 := by
    have hY : Nat.card ↥(modO2Image X Kh₁) = 211341312 := by
      rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD4]
      show ordTrialityD4 (2 ^ 1) = 211341312
      decide
    rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, ← hY]
    exact Subgroup.card_dvd_of_le (hψA.trans inf_le_right)
  obtain ⟨d₀, hd₀, hd₀N⟩ := Set.not_subset.mp hnotK
  have ho : orderOf d₀ ≠ 0 := (isOfFinOrder_of_finite d₀).orderOf_pos.ne'
  set s₀ := 3 ^ (orderOf d₀).factorization 3 with hs₀
  set r₀ := orderOf d₀ / s₀ with hr₀
  have h3r₀ : Nat.Coprime 3 r₀ := Nat.coprime_ordCompl Nat.prime_three ho
  have hsr₀ : Nat.Coprime s₀ r₀ := Nat.Coprime.pow_left _ h3r₀
  have hd₀1 : d₀ ^ (s₀ * r₀) = 1 := by
    rw [hs₀, hr₀, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hds : d₀ ^ s₀ ∈ Subgroup.normalizer (K₁ : Set G) := by
    have hmem : d₀ ^ s₀ ∈ D ⊓ X := ⟨D.pow_mem hd₀.1 _, X.pow_mem hd₀.2 _⟩
    refine h3' _ (hDA hmem) (hoddD _ hmem.1) ?_
    have h1 : orderOf (d₀ ^ s₀) ∣ r₀ := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, hd₀1])
    exact Nat.Coprime.coprime_dvd_left h1 h3r₀.symm
  set w := d₀ ^ r₀ with hw
  have hwN : w ∉ Subgroup.normalizer (K₁ : Set G) := fun hwN =>
    hd₀N (mem_of_pow_mem_of_coprime_5113 hds hwN hsr₀)
  have hwD : w ∈ D := D.pow_mem hd₀.1 _
  have hwX : w ∈ X := X.pow_mem hd₀.2 _
  have hws : w ^ s₀ = 1 := by rw [hw, ← pow_mul, mul_comm, hd₀1]
  have hwK : w ∈ Kh₁ := h3el w hwX ⟨_, hws⟩
  have hwDK : w ∈ D ⊓ Kh₁ := Subgroup.mem_inf.mpr ⟨hwD, hwK⟩
  have hw1 : w ≠ 1 := fun h1 => hwN (h1 ▸ Subgroup.one_mem _)
  have hwb : orderOf (ψ ⟨w, hwDK⟩) = orderOf w := by
    rw [orderOf_injective ψ hψinj, Subgroup.orderOf_mk]
  have hw3 : orderOf w = 3 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one hws)
    have hdvd : orderOf w ∣ Nat.card ↥(modO2Image X ((borelL T L ⊔ T) ⊓ X) ⊓
        modO2Image X Kh₁) := by
      rw [← hwb, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr (hψA ⟨_, rfl⟩))
    rcases i with _ | _ | i
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hi', pow_zero])) hw1
    · rw [hi', pow_one]
    · exfalso
      apply h9
      refine dvd_trans ⟨3 ^ i, ?_⟩ hdvd
      rw [hi']
      ring
  have hD₃le : Subgroup.zpowers w ≤ D ⊓ Kh₁ :=
    (Subgroup.zpowers_le).mpr hwDK
  have hcard3 : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
  have hD₃K : ¬ Subgroup.zpowers w ≤ Subgroup.normalizer (K₁ : Set G) := fun hle =>
    hwN (hle (Subgroup.mem_zpowers w))
  set Fb := Subgroup.zpowers (ψ ⟨w, hwDK⟩) with hFb
  have hFb3 : Nat.card Fb = 3 := by rw [hFb, Nat.card_zpowers, hwb, hw3]
  obtain ⟨tb, htb₁, htinv⟩ := hinv Fb ((Subgroup.zpowers_le).mpr (hψA ⟨_, rfl⟩)) hFb3
  change tb ∈ modO2Image X T ⊓ modO2Image X Kh₁ at htb₁
  rw [modO2Image_inf_of_pCoreOf_le hOT] at htb₁
  obtain ⟨t₀', ht₀', rfl⟩ := htb₁
  have ht₀ : (t₀' : G) ∈ T ⊓ Kh₁ := Subgroup.mem_subgroupOf.mp ht₀'
  set t₀ : G := (t₀' : G) with ht₀def
  set P := pCoreOf 2 X ⊓ Kh₁ with hPdef
  have hinvG : ∀ d ∈ Subgroup.zpowers w, t₀ * d * t₀⁻¹ * d ∈ P := by
    intro d hd
    have hdK : d ∈ D ⊓ Kh₁ := hD₃le hd
    have hdX : d ∈ X := hKhX hdK.2
    have hwX' : t₀ * d * t₀⁻¹ * d ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem t₀'.2 hdX) (X.inv_mem t₀'.2)) hdX
    have hwK' : t₀ * d * t₀⁻¹ * d ∈ Kh₁ :=
      Kh₁.mul_mem (Kh₁.mul_mem (Kh₁.mul_mem ht₀.2 hdK.2) (Kh₁.inv_mem ht₀.2)) hdK.2
    have hdF : ψ ⟨d, hdK⟩ ∈ Fb := by
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hd
      refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hz)
    have h1 := htinv _ hdF
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t₀ * d * t₀⁻¹ * d, hwX'⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀' * ψ ⟨d, hdK⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀')⁻¹ * ψ ⟨d, hdK⟩ := by
      rw [← map_inv]
      show _ = QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀' *
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hdX⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) t₀'⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hdX⟩
      rw [← map_mul, ← map_mul, ← map_mul]
      rfl
    have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t₀ * d * t₀⁻¹ * d, hwX'⟩ = 1 := by
      rw [h2, h1, inv_mul_cancel]
    exact ⟨hπ2 _ hwX' h3, hwK'⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 X).to_le inf_le_left
  have hD₃P : Subgroup.zpowers w ≤ Subgroup.normalizer (P : Set G) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 X (hKhX (hD₃le hd).2), Subgroup.le_normalizer (hD₃le hd).2⟩
  have hV : Nat.card ↥((Subgroup.zpowers w).map (MulAut.conj t₀).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t₀).injective, hcard3]
  have hVY : (Subgroup.zpowers w).map (MulAut.conj t₀).toMonoidHom ≤ Subgroup.zpowers w ⊔ P := by
    rintro _ ⟨d, hd, rfl⟩
    have e' : (MulAut.conj t₀).toMonoidHom d = (t₀ * d * t₀⁻¹ * d) * d⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e']
    exact (Subgroup.zpowers w ⊔ P).mul_mem (Subgroup.mem_sup_right (hinvG d hd))
      (Subgroup.mem_sup_left ((Subgroup.zpowers w).inv_mem hd))
  obtain ⟨p, hp, hVp⟩ := exists_conj_eq_of_card_three hcard3 hV hP2 hD₃P hVY
  have hpT : p ∈ T := hOT hp.1
  refine ⟨Is3D4.of_mulEquiv eH.symm hD4, hKh3, Subgroup.zpowers w, hD₃le, hcard3, hD₃K, hDK9,
    hDKc, p⁻¹ * t₀, ⟨T.mul_mem (T.inv_mem hpT) ht₀.1, Kh₁.mul_mem (Kh₁.inv_mem hp.2) ht₀.2⟩, ?_⟩
  intro d hd
  have hc : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ ∈ Subgroup.zpowers w := by
    have hm : t₀ * d * t₀⁻¹ ∈ (Subgroup.zpowers w).map (MulAut.conj p).toMonoidHom := by
      rw [← hVp]
      exact ⟨d, hd, rfl⟩
    obtain ⟨d', hd', hdd'⟩ := hm
    have hdd'' : p * d' * p⁻¹ = t₀ * d * t₀⁻¹ := hdd'
    have e' : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ = d' := by
      calc p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ = p⁻¹ * (t₀ * d * t₀⁻¹) * p := by group
        _ = p⁻¹ * (p * d' * p⁻¹) * p := by rw [hdd'']
        _ = d' := by group
    rw [e']
    exact hd'
  have hw' : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d ∈ Subgroup.zpowers w :=
    (Subgroup.zpowers w).mul_mem hc hd
  have hwO : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d ∈ pCoreOf 2 X := by
    have h1 : p⁻¹ * t₀ * d * (p⁻¹ * t₀)⁻¹ * d =
        p⁻¹ * (t₀ * d * t₀⁻¹ * d) * (d⁻¹ * p * d) := by group
    rw [h1]
    have hdX : d ∈ X := hKhX (hD₃le hd).2
    have hn := le_normalizer_pCoreOf 2 X (X.inv_mem hdX)
    have h2 : d⁻¹ * p * d⁻¹⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp hn p).mp hp.1
    rw [inv_inv] at h2
    exact (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hp.1)
      (hinvG d hd).1) h2
  have h1 := hD2 _ (hD₃le hw').1 hwO
  exact eq_inv_of_mul_eq_one_left h1

end Main513

end CFSG.Quasithin.H13
