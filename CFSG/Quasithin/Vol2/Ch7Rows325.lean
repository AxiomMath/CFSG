module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Vol2.Ch7NotFFS7
public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.HA7Rec
public import CFSG.Quasithin.Background.HSp4A6
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Certificate7022
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem commutator_eq_top_of_surjective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (h : commutator A = ⊤) : commutator B = ⊤ := by
  have h1 := map_commutator_eq A f
  rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf] at h1
  rw [_root_.commutator_def]
  exact h1.symm

theorem commutator_eq_top_of_perfect {L : Subgroup G} (h : ⁅L, L⁆ = L) : commutator ↥L = ⊤ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_statedSp_ne_top
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    commutator ↥(StatedSp 2 K) ≠ ⊤ := by
  intro h
  let ψ := CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr
    (ringEquivZModTwo hK) 2
  have h2 : commutator ↥(StatedSp 2 (ZMod 2)) = ⊤ :=
    commutator_eq_top_of_surjective (f := ψ.toMonoidHom) ψ.surjective h
  have h3 : Sp4A6.Γ₆ = StatedSp 2 (ZMod 2) := by
    rw [Sp4A6.Γ₆_eq_commutator, h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h4 : Nat.card Sp4A6.Γ₆ = 360 := by
    rw [← Nat.card_congr Sp4A6.psiEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have h5 : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  rw [h3, h5] at h4
  omega

theorem isTwistedPair_of_325 {T L I : Subgroup G}
    (h : (∃ t ∈ T, t ∉ Subgroup.normalizer (I : Set G)) ∧
      ∀ t ∈ T, t ∉ Subgroup.normalizer (I : Set G) →
        conjClosure (conjClosure I T) (Subgroup.normalizer (L : Set G)) = conjClosure I T ∧
          conjClosure I T = I ⊔ CFSG.conjugate I t ∧ I ⊓ CFSG.conjugate I t = ⊥ ∧
          ¬ IsXSectionIso₂ L I ⊥ (CFSG.conjugate I t) ⊥) :
    IsTwistedPair T L I := by
  obtain ⟨t, htT, htN⟩ := h.1
  obtain ⟨-, hV, hinf, hniso⟩ := h.2 t htT htN
  exact ⟨t, htT, hV.symm, hinf, hniso⟩

section Restrict

variable {L V I : Subgroup G}

theorem coe_conjAct_apply_val (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G)))
    (v : ↥V) : ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

theorem autOn_mem_subgroupOf (hLI : L ≤ Subgroup.normalizer (I : Set G)) :
    ∀ a ∈ autOn L V, ∀ u ∈ I.subgroupOf V, a u ∈ I.subgroupOf V := by
  intro a ha u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_subgroupOf] at hu ⊢
  rw [coe_conjAct_apply_val]
  exact (Subgroup.mem_normalizer_iff.mp (hLI (Subgroup.mem_subgroupOf.mp hx)) _).mp hu

theorem exists_conj_ne (hC : I ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hI : I ≠ ⊥) :
    ∃ l ∈ L, ∃ y ∈ I, l * y * l⁻¹ ≠ y := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hI
  have hyC : y ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have : y ∈ I ⊓ Subgroup.centralizer (L : Set G) := ⟨hy, h⟩
    rw [hC, Subgroup.mem_bot] at this
    exact hy1 (Subtype.ext this)
  rw [Subgroup.mem_centralizer_iff] at hyC
  push Not at hyC
  obtain ⟨l, hl, hne⟩ := hyC
  refine ⟨l, hl, y, hy, fun h => hne ?_⟩
  calc l * y = (l * y * l⁻¹) * l := by group
    _ = y * l := by rw [h]

variable [IsMulCommutative ↥V] [IsMulCommutative ↥I]

theorem realizes_section [Finite G] {D : FFModel} (hIV : I ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLI : L ≤ Subgroup.normalizer (I : Set G))
    (hcard : Nat.card ↥(autOn L V) ≤ Nat.card ↥(autOn L I))
    (h : D.Realizes (V := ↥I) (autOn L I) ⊤ ⊥) :
    D.Realizes (V := ↥V) (autOn L V) (I.subgroupOf V) ⊥ := by
  classical
  have hU := autOn_mem_subgroupOf (V := V) hLI
  let j : ↥(I.subgroupOf V) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIV
  let r₀ : ↥(autOn L V) →* MulAut ↥I :=
    (MulAut.congr j).toMonoidHom.comp (CFSG.Quasithin.H.resHom hU)
  have hr₀ : ∀ (x : ↥(Subgroup.normalizer (V : Set G)))
      (hx : x ∈ L.subgroupOf (Subgroup.normalizer (V : Set G))) (y : ↥I),
      ((r₀ ⟨conjAct V x, Subgroup.mem_map_of_mem _ hx⟩ y : ↥I) : G) = x * y * (x : G)⁻¹ :=
    fun x _ y => coe_conjAct_apply_val V x ⟨(y : G), hIV y.2⟩
  have hmaps : ∀ a, r₀ a ∈ autOn L I := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hLI hxL⟩, Subgroup.mem_subgroupOf.mpr hxL, ?_⟩
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [coe_conjAct_apply_val]
    exact (hr₀ x hx y).symm
  let r₁ : ↥(autOn L V) →* ↥(autOn L I) := r₀.codRestrict _ hmaps
  have hsurj : Function.Surjective r₁ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
    have hxV' : (⟨x, hLV hxL⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈
        L.subgroupOf (Subgroup.normalizer (V : Set G)) := Subgroup.mem_subgroupOf.mpr hxL
    refine ⟨⟨conjAct V ⟨x, hLV hxL⟩, Subgroup.mem_map_of_mem _ hxV'⟩, ?_⟩
    apply Subtype.ext
    refine MulEquiv.ext fun y => Subtype.ext ?_
    change ((r₀ ⟨conjAct V ⟨x, hLV hxL⟩, Subgroup.mem_map_of_mem _ hxV'⟩ y : ↥I) : G) = _
    rw [hr₀ _ hxV', coe_conjAct_apply_val]
  let r : ↥(autOn L V) ≃* ↥(autOn L I) :=
    MulEquiv.ofBijective r₁ (hsurj.bijective_of_nat_card_le hcard)
  exact FFModel.realizes_of_equiv hU j r (fun _ _ => rfl) h

end Restrict

section Rows

variable {T L I : Subgroup G}

abbrev TwistData325 (T L I : Subgroup G) : Prop :=
  (∃ t ∈ T, t ∉ Subgroup.normalizer (I : Set G)) ∧
    ∀ t ∈ T, t ∉ Subgroup.normalizer (I : Set G) →
      conjClosure (conjClosure I T) (Subgroup.normalizer (L : Set G)) = conjClosure I T ∧
        conjClosure I T = I ⊔ CFSG.conjugate I t ∧ I ⊓ CFSG.conjugate I t = ⊥ ∧
        ¬ IsXSectionIso₂ L I ⊥ (CFSG.conjugate I t) ⊥

theorem le_normalizer_I [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T) :
    L ≤ Subgroup.normalizer (I : Set G) := by
  have h := hfsu.irrPlus.2.2.1
  rw [← hL] at h
  exact h

theorem le_normalizer_V (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  (le_fsuL0 T L).trans (le_sup_left.trans hN)

variable [IsMulCommutative ↥(fsuV T I)]

theorem row711SL3Pair_of_325 [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {n : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hiso : Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K))
    (hnat : ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 3 n)
    (htw : TwistData325 T L I) : Row711SL3Pair T L I n := by
  obtain ⟨_, hnat⟩ := hnat
  have hL0 : fsuL0 T L = L := hL.symm
  refine ⟨isTwistedPair_of_325 htw, ?_⟩
  obtain ⟨K₂, _, _, hK₂, hreal⟩ := hnat
  refine ⟨K₂, inferInstance, inferInstance, hK₂, ?_⟩
  rw [hL0]
  refine realizes_section (le_fsuV I T) (le_normalizer_V hN) (le_normalizer_I hfsu hL) ?_ hreal
  obtain ⟨e⟩ := hiso
  obtain ⟨K₃, _, _, hK₃, ⟨e₃⟩⟩ :=
    BinaryNaturalSL.exists_equiv (H := autOn L I) ⟨K₂, inferInstance, inferInstance, hK₂, hreal⟩
  have h1 : Nat.card ↥(autOn L (fsuV T I)) = Nat.card (StatedSL 3 K) :=
    (Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv)
  have h2 : Nat.card ↥(autOn L I) = Nat.card (StatedSL 3 K₃) := (Nat.card_congr e₃.toEquiv).symm
  rw [h1, h2, CFSG.SectionRank.OddCover.card_statedSL_three,
    CFSG.SectionRank.OddCover.card_statedSL_three, hK, hK₃]

theorem row711Sp4Pair_of_325
    [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {n : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hiso : Nonempty (↥(autOn L (conjClosure I T)) ≃* ↥(StatedSp 2 K)))
    (hnat : ∃ _ : IsMulCommutative ↥I, BinaryNaturalSp4 (V := ↥I) (autOn L I) ⊤ ⊥ n)
    (htw : TwistData325 T L I) : Row711Sp4Pair T L I := by
  obtain ⟨_, hnat⟩ := hnat
  have hL0 : fsuL0 T L = L := hL.symm
  obtain ⟨e⟩ := hiso
  have hLV := le_normalizer_V hN
  have hn : 2 ≤ n := by
    by_contra hn
    have hn1 : n = 0 ∨ n = 1 := by omega
    rcases hn1 with rfl | rfl
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      exact lt_irrefl 1 this
    · apply commutator_statedSp_ne_top (K := K) (by rw [hK, pow_one])
      refine commutator_eq_top_of_surjective (f := e.toMonoidHom) e.surjective ?_
      have hperf : ⁅L, L⁆ = L := hfsu.maximal.1.2.1.2.1
      let f : ↥L →* ↥(autOn L (conjClosure I T)) :=
        { toFun := fun l => ⟨conjAct (conjClosure I T) ⟨l, hLV l.2⟩,
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr l.2)⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul (conjAct (conjClosure I T))
            ⟨a, hLV a.2⟩ ⟨b, hLV b.2⟩) }
      refine commutator_eq_top_of_surjective (f := f) ?_ (commutator_eq_top_of_perfect hperf)
      rintro ⟨a, ha⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  refine ⟨isTwistedPair_of_325 htw, Or.inl ⟨n, hn, ?_⟩⟩
  obtain ⟨K₂, _, _, hK₂, hreal⟩ := hnat
  refine ⟨K₂, inferInstance, inferInstance, hK₂, ?_⟩
  rw [hL0]
  refine realizes_section (le_fsuV I T) hLV (le_normalizer_I hfsu hL) ?_ hreal
  obtain ⟨K₃, _, _, hK₃, ⟨e₃⟩⟩ :=
    BinaryNaturalSp4.exists_equiv (H := autOn L I) ⟨K₂, inferInstance, inferInstance, hK₂, hreal⟩
  have h1 : Nat.card ↥(autOn L (fsuV T I)) = Nat.card (StatedSp 2 K) := Nat.card_congr e.toEquiv
  have h2 : Nat.card ↥(autOn L I) = Nat.card (StatedSp 2 K₃) := (Nat.card_congr e₃.toEquiv).symm
  rw [h1, h2, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hK₃]

theorem row711Sp4Pair_of_325_A6 [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hC : I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hiso : Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 6)))
    (hnat : ∃ _ : IsMulCommutative ↥I, AlternatingNatural (V := ↥I) (autOn L I) ⊤ ⊥ 6)
    (htw : TwistData325 T L I) : Row711Sp4Pair T L I := by
  obtain ⟨_, hnat⟩ := hnat
  have hL0 : fsuL0 T L = L := hL.symm
  have hLI := le_normalizer_I hfsu hL
  refine ⟨isTwistedPair_of_325 htw, Or.inr ?_⟩
  rw [hL0]
  refine realizes_section (le_fsuV I T) (le_normalizer_V hN) hLI ?_ hnat
  obtain ⟨e⟩ := hiso
  have hA6 : IsSimpleGroup (FFModel.altDn 6).Gam :=
    (alternatingGroup.isSimpleGroup (by simp) : IsSimpleGroup (alternatingGroup (Fin 6)))
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  obtain ⟨π, hπ⟩ := hnat
  obtain ⟨l, hl, y, hy, hne⟩ := exists_conj_ne hC hfsu.irrPlus.2.1
  have hπinj : Function.Injective π := by
    rcases (MonoidHom.normal_ker π).eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk
    · exfalso
      obtain ⟨σ, hσ⟩ := hπ.1 ⟨conjAct I ⟨l, hLI hl⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)⟩
      have h1 : π σ = 1 := MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top σ)
      rw [h1] at hσ
      apply hne
      have h2 := congrArg (fun a : ↥(autOn L I) => (((a : MulAut ↥I) ⟨y, hy⟩ : ↥I) : G)) hσ
      exact h2.symm
  have h1 : Nat.card ↥(autOn L (fsuV T I)) = 360 := (Nat.card_congr e.toEquiv).trans h6
  have h2 : Nat.card ↥(autOn L I) = 360 :=
    (Nat.card_congr (MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩).toEquiv).symm.trans h6
  rw [h1, h2]

theorem row711S7Pair_of_325 [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hV : CFSG.Open.IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hC : I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hiso : Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 7)))
    (hcard : Nat.card I = 2 ^ 4) (htw : TwistData325 T L I) : Row711S7Pair T L I := by
  have hL0 : fsuL0 T L = L := hL.symm
  have hLI := le_normalizer_I hfsu hL
  have hLV := le_normalizer_V hN
  have hIV : I ≤ fsuV T I := le_fsuV I T
  refine ⟨isTwistedPair_of_325 htw, ?_⟩
  rw [hL0]
  refine A7.a7Four_of_nontrivial hiso (autOn_mem_subgroupOf hLI) (fun u _ => ?_) ?_ ?_
  · apply Subtype.ext
    change (u : G) * u = 1
    rw [← sq]
    exact hV.2 _ u.2
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIV).toEquiv, hcard]
  · obtain ⟨l, hl, y, hy, hne⟩ := exists_conj_ne hC hfsu.irrPlus.2.1
    refine ⟨conjAct (fsuV T I) ⟨l, hLV hl⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl), ⟨y, hIV hy⟩,
      Subgroup.mem_subgroupOf.mpr hy, fun h => hne ?_⟩
    have := congrArg Subtype.val h
    exact this

abbrev LinearCase325 (T L I : Subgroup G) : Prop :=
  (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 4 1) ∨
    (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
      ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 5 1)

theorem twistedRows_of_325
    [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hV : CFSG.Open.IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (h3 : I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 3 n) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure I T)) ≃* ↥(StatedSp 2 K)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSp4 (V := ↥I) (autOn L I) ⊤ ⊥ n) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 6)) ∧
          ∃ _ : IsMulCommutative ↥I, AlternatingNatural (V := ↥I) (autOn L I) ⊤ ⊥ 6) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 4 1) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 5 1) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 7)) ∧
          Nat.card I = 2 ^ 4)) ∧
      TwistData325 T L I) :
    (∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨ Row711S7Pair T L I ∨
      (IsTwistedPair T L I ∧ LinearCase325 T L I) := by
  obtain ⟨hC, hcases, htw⟩ := h3
  rcases hcases with ⟨n, K, _, _, hK, hiso, hnat⟩ | ⟨n, K, _, _, hK, hiso, hnat⟩ |
    ⟨hiso, hnat⟩ | h4 | h5 | ⟨hiso, hcard⟩
  · exact Or.inl ⟨n, row711SL3Pair_of_325 hfsu hL hN hK hiso hnat htw⟩
  · exact Or.inr (Or.inl (row711Sp4Pair_of_325 hfsu hL hN hK hiso hnat htw))
  · exact Or.inr (Or.inl (row711Sp4Pair_of_325_A6 hfsu hL hN hC hiso hnat htw))
  · exact Or.inr (Or.inr (Or.inr ⟨isTwistedPair_of_325 htw, Or.inl h4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨isTwistedPair_of_325 htw, Or.inr h5⟩))
  · exact Or.inr (Or.inr (Or.inl (row711S7Pair_of_325 hfsu hL hV hN hC hiso hcard htw)))

theorem not_concl701FF_or_325
    [Finite G] (hfsu : FSU G T L I) (hL : L = conjClosure L T)
    (hV : CFSG.Open.IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (h3 : I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 3 n) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure I T)) ≃* ↥(StatedSp 2 K)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSp4 (V := ↥I) (autOn L I) ⊤ ⊥ n) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 6)) ∧
          ∃ _ : IsMulCommutative ↥I, AlternatingNatural (V := ↥I) (autOn L I) ⊤ ⊥ 6) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 4 1) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥I, BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 5 1) ∨
        (Nonempty (↥(autOn L (conjClosure I T)) ≃* alternatingGroup (Fin 7)) ∧
          Nat.card I = 2 ^ 4)) ∧
      TwistData325 T L I) :
    ¬ Concl701FF T L I ∨ (IsTwistedPair T L I ∧ LinearCase325 T L I) := by
  rcases twistedRows_of_325 hfsu hL hV hN h3 with h | h | h | h
  · exact Or.inl (not_concl701FF_twistedPair hV hN hNM inferInstance (Or.inl h))
  · exact Or.inl (not_concl701FF_twistedPair hV hN hNM inferInstance (Or.inr (Or.inl h)))
  · exact Or.inl (not_concl701FF_twistedPair hV hN hNM inferInstance (Or.inr (Or.inr h)))
  · exact Or.inr h

end Rows

end CFSG.Quasithin.H13
