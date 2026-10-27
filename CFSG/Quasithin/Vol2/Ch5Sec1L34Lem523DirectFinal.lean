module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectS5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectTr
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs9
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectV1
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.H13.Abs523 CFSG.Quasithin.H13.Tr523

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem sq_one_of_mem_N {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m)
    (hm : Nat.card D.K = 2 ^ m) [CharP D.K 2] {x : G} (hx : x ∈ N) : x * x = 1 := by
  have h2 : (2 : D.K) = 0 := by exact_mod_cast CharP.cast_eq_zero D.K 2
  have hc : coordN D (x * x) (N.mul_mem hx hx) = 0 := by
    rw [coordN_mul D hx hx (N.mul_mem hx hx)]
    have : ∀ w : Fin 2 → D.K, w + w = 0 := fun w => by
      funext i
      show w i + w i = 0
      rw [← two_mul, h2, zero_mul]
    exact this _
  have h1 : coordN D (1 : G) N.one_mem = 0 := by
    unfold coordN
    simp
  exact coordN_injective D (N.mul_mem hx hx) N.one_mem (hc.trans h1.symm)

abbrev commGroupOfComm523 {A : Type} [Group A] (h : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { ‹Group A› with mul_comm := h }

theorem conjUt_eq_one_of {X : Subgroup G} {a : ↥(Subgroup.normalizer (Z₁ : Set G))} (h : a = 1)
    {ha : (a : G) ∈ Subgroup.normalizer (X : Set G)} : conjUt a ha = 1 := by
  subst h
  refine MulEquiv.ext fun x => Subtype.ext ?_
  simp [conjUt_val]

@[expose] def conjHomU523 (Z₁ X : Subgroup G) :
    ↥(Subgroup.normalizer (Z₁ : Set G) ⊓ Subgroup.normalizer (X : Set G)) →*
      MulAut ↥(tildeOf Z₁ X) where
  toFun a := conjUt ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩ (Subgroup.mem_inf.mp a.2).2
  map_one' := conjUt_eq_one_of (Subtype.ext rfl)
  map_mul' a b := conjUt_mul (a := ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩)
    (b := ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩)
    (ha := (Subgroup.mem_inf.mp a.2).2) (hb := (Subgroup.mem_inf.mp b.2).2)
    (hab := (Subgroup.mem_inf.mp (mul_mem a.2 b.2)).2)

theorem conjHomU523_val {X : Subgroup G}
    (w : ↥(Subgroup.normalizer (Z₁ : Set G) ⊓ Subgroup.normalizer (X : Set G)))
    (x : ↥(tildeOf Z₁ X)) :
    ((conjHomU523 Z₁ X w) x).1 =
      secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩ * x.1 *
        (secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)⁻¹ :=
  rfl

theorem E_contra (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) (h521 : Stmt5_1_21) (hH47 : CFSG.ASVolI.H_4_7)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    {N : Subgroup G} (D' : NatL2Data L N 2) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (B₁ B₂ B₃ B₄ : (Fin 2 → D'.K) ≃+ (Fin 2 → D'.K))
    (hcases : ∀ u ∈ Ugrp Z₁ D₃, ∀ hu : u ∈ Subgroup.normalizer (N : Set G),
      D'.conj ⟨u, hu⟩ = B₁ ∨ D'.conj ⟨u, hu⟩ = B₂ ∨ D'.conj ⟨u, hu⟩ = B₃ ∨
        D'.conj ⟨u, hu⟩ = B₄)
    {u₁ : G} (hu₁ : u₁ ∈ Ugrp Z₁ D₃) {v : G} (hvN : v ∈ N) (hvT : v ∈ T)
    {d z k₀ : G} (hcomm : u₁ * v * u₁⁻¹ * v⁻¹ = d * z * d⁻¹) (hk₀ : k₀ ∈ oTwoUpper H)
    (hk₀' : (d * z * d⁻¹)⁻¹ * (k₀ * (d * z * d⁻¹) * k₀⁻¹) ∉ Z₁) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP D'.K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D'.card
  have hcl := s.hyp.l34.statedClassicalModel (by decide)
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hΩ := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hZH : ∀ x ∈ Z₁, ∀ h ∈ H, h * x = x * h := fun x hx h hh =>
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hΩ (s.z1.1 hx)) h hh
  have hKG : oTwoUpper H ≤ Subgroup.centralizer (Z₁ : Set G) := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hZH x hx k (oTwoUpper_le H hk)).symm
  have hKN1 : oTwoUpper H ≤ Subgroup.normalizer (Z₁ : Set G) :=
    hKG.trans (Subgroup.centralizer_le_normalizer _)
  have hKN2 : oTwoUpper H ≤ Subgroup.normalizer (Ugrp Z₁ D₃ : Set G) := fun k hk =>
    CFSG.Quasithin.le_normalizer_conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)) (hKG hk)
  have hKHs : oTwoUpper H ≤ Subgroup.normalizer (Z₁ : Set G) ⊓
      Subgroup.normalizer (Ugrp Z₁ D₃ : Set G) := fun k hk =>
    Subgroup.mem_inf.mpr ⟨hKN1 hk, hKN2 hk⟩
  have hNz : Ugrp Z₁ D₃ ≤ Subgroup.normalizer (Z₁ : Set G) := s.U_le_normalizer_Z₁ h5114 hF
  have hUT : Ugrp Z₁ D₃ ≤ T := s.U_le_T h5114 hF
  have hvG1 : v ∈ Subgroup.centralizer (Z₁ : Set G) := T_le_centralizer_Z₁ s hvT
  have hvN1 : v ∈ Subgroup.normalizer (Z₁ : Set G) := Subgroup.centralizer_le_normalizer _ hvG1
  have hvN2 : v ∈ Subgroup.normalizer (Ugrp Z₁ D₃ : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)) hvG1
  have hvK : v ∈ Subgroup.normalizer (oTwoUpper H : Set G) :=
    le_normalizer_oTwoUpper H (hTH hvT)
  have hvHs : v ∈ Subgroup.normalizer (Z₁ : Set G) ⊓ Subgroup.normalizer (Ugrp Z₁ D₃ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hvN1, hvN2⟩
  have hvv : v * v = 1 := sq_one_of_mem_N D' D'.card hvN
  have hab_U := s.isElemAbelian_tildeOf_U h5114 hF
  letI : CommGroup ↥(tildeOf Z₁ (Ugrp Z₁ D₃)) :=
    commGroupOfComm523 (fun a b => hab_U.1.is_comm.comm a b)
  have hE2 : ∀ x : ↥(tildeOf Z₁ (Ugrp Z₁ D₃)), x ^ 2 = 1 :=
    fun x => Subtype.ext (hab_U.2 x.1 x.2)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ↥(Subgroup.normalizer (Z₁ : Set G) ⊓
      Subgroup.normalizer (Ugrp Z₁ D₃ : Set G)) →* MulAut ↥(tildeOf Z₁ (Ugrp Z₁ D₃)),
      Θ = conjHomU523 Z₁ (Ugrp Z₁ D₃) := ⟨_, rfl⟩
  have hΘval : ∀ (w : ↥(Subgroup.normalizer (Z₁ : Set G) ⊓
        Subgroup.normalizer (Ugrp Z₁ D₃ : Set G)))
      (x : ↥(tildeOf Z₁ (Ugrp Z₁ D₃))),
      (Θ w x).1 = secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩ *
        x.1 * (secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩)⁻¹ := by
    intro w x
    rw [hΘ]
    exact conjHomU523_val w x
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(oTwoUpper H) →* MulAut ↥(tildeOf Z₁ (Ugrp Z₁ D₃)),
      ∀ k : ↥(oTwoUpper H), φ k = Θ ⟨k.1, hKHs k.2⟩ :=
    ⟨Θ.comp (Subgroup.inclusion hKHs), fun k => rfl⟩
  have hcommU : u₁ * v * u₁⁻¹ * v⁻¹ ∈ Ugrp Z₁ D₃ := by
    have e : u₁ * v * u₁⁻¹ * v⁻¹ = u₁ * (v * u₁⁻¹ * v⁻¹) := by group
    rw [e]
    exact mul_mem hu₁ ((Subgroup.mem_normalizer_iff.mp hvN2 u₁⁻¹).mp (inv_mem hu₁))
  have hcommNz : u₁ * v * u₁⁻¹ * v⁻¹ ∈ Subgroup.normalizer (Z₁ : Set G) :=
    mul_mem (mul_mem (mul_mem (hNz hu₁) hvN1) (inv_mem (hNz hu₁))) (inv_mem hvN1)
  have hdzU : d * z * d⁻¹ ∈ Ugrp Z₁ D₃ := by
    rw [← hcomm]
    exact hcommU
  have hdzN : d * z * d⁻¹ ∈ Subgroup.normalizer (Z₁ : Set G) := by
    rw [← hcomm]
    exact hcommNz
  obtain ⟨c₀, hc₀⟩ : ∃ c : ↥(tildeOf Z₁ (Ugrp Z₁ D₃)),
      c.1 = secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨d * z * d⁻¹, hdzN⟩ :=
    ⟨⟨secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨d * z * d⁻¹, hdzN⟩,
      secMk_mem_secImg (x := ⟨d * z * d⁻¹, hdzN⟩) hdzU⟩, rfl⟩
  have hnc : φ ⟨k₀, hk₀⟩ c₀ ≠ c₀ := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [hφ, hΘval, hc₀] at h1
    have e : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁
        (⟨k₀, hKN1 hk₀⟩ * ⟨d * z * d⁻¹, hdzN⟩ * (⟨k₀, hKN1 hk₀⟩)⁻¹) =
        secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨d * z * d⁻¹, hdzN⟩ := by
      rw [map_mul, map_mul, map_inv]
      exact h1
    exact hk₀' (secMk_eq_secMk_iff.mp e.symm)
  have hpC : ∀ k : ↥(oTwoUpper H), k ∈ CFSG.pCore 2 ↥(oTwoUpper H) → φ k = 1 := by
    intro k hk
    have hkp : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have hs : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨k.1, hKN1 k.2⟩ ∈
        tildeOf Z₁ (pCoreOf 2 (oTwoUpper H)) :=
      secMk_mem_secImg (x := ⟨k.1, hKN1 k.2⟩) hkp
    have hc := Subgroup.mem_centralizer_iff.mp
      (s.tildeOf_pCoreOf_K_le_centralizer h5114 h521 hnot hs)
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have hcy := hc y.1 y.2
    rw [hφ, MulAut.one_apply, hΘval]
    dsimp only
    rw [← hcy]
    group
  have hpC_ker : CFSG.pCore 2 ↥(oTwoUpper H) ≤ φ.ker :=
    fun k hk => MonoidHom.mem_ker.mpr (hpC k hk)
  haveI hN'N : ((φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H)))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hsimpO : IsSimpleGroup (O2Q (oTwoUpper H)) :=
    CFSG.RankThree.PartTwo.Sec3.isSimpleGroup_of_statedClassicalModel_psl hcl
  have hU' : ∀ u ∈ Ugrp Z₁ D₃, u ∈ Subgroup.normalizer (N : Set G) :=
    fun u hu => hTN (hUT hu)
  obtain ⟨F, hFc, hF4⟩ := comm_finset D' hvN hU' B₁ B₂ B₃ B₄ hcases
  obtain ⟨hE, hEdef⟩ : ∃ hE : G → ↥(tildeOf Z₁ (Ugrp Z₁ D₃)), ∀ (g : G) (hg : g ∈ Ugrp Z₁ D₃),
      hE g = ⟨secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨g, hNz hg⟩,
        secMk_mem_secImg (x := ⟨g, hNz hg⟩) hg⟩ :=
    ⟨fun g => if hg : g ∈ Ugrp Z₁ D₃ then
        ⟨secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨g, hNz hg⟩,
          secMk_mem_secImg (x := ⟨g, hNz hg⟩) hg⟩ else 1,
      fun g hg => dif_pos hg⟩
  have hXc : (hE '' (F : Set G)).ncard ≤ 4 :=
    (Set.ncard_image_le (Finset.finite_toSet F)).trans (by rw [Set.ncard_coe_finset]; exact hFc)
  have hcm : ∀ x : ↥(tildeOf Z₁ (Ugrp Z₁ D₃)), x * (Θ ⟨v, hvHs⟩ x)⁻¹ ∈ hE '' (F : Set G) := by
    intro x
    obtain ⟨a, ha, hax⟩ := mem_secImg.mp x.2
    have haN : a.1 ∈ Subgroup.normalizer (N : Set G) := hTN (hUT ha)
    have hgU : a.1 * v * a.1⁻¹ * v⁻¹ ∈ Ugrp Z₁ D₃ := by
      have e : a.1 * v * a.1⁻¹ * v⁻¹ = a.1 * (v * a.1⁻¹ * v⁻¹) := by group
      rw [e]
      exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp hvN2 a.1⁻¹).mp (inv_mem ha))
    refine ⟨a.1 * v * a.1⁻¹ * v⁻¹, hF4 a.1 ha haN, ?_⟩
    rw [hEdef _ hgU]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hΘval]
    dsimp only
    rw [← hax]
    have key : (⟨a.1 * v * a.1⁻¹ * v⁻¹, hNz hgU⟩ : ↥(Subgroup.normalizer (Z₁ : Set G))) =
        a * ⟨v, hvN1⟩ * a⁻¹ * (⟨v, hvN1⟩)⁻¹ := Subtype.ext rfl
    rw [key, map_mul, map_mul, map_mul, map_inv, map_inv]
    group
  obtain ⟨x₁, hx₁⟩ : ∃ x : ↥(tildeOf Z₁ (Ugrp Z₁ D₃)),
      x.1 = secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨u₁, hNz hu₁⟩ :=
    ⟨⟨secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ ⟨u₁, hNz hu₁⟩,
      secMk_mem_secImg (x := ⟨u₁, hNz hu₁⟩) hu₁⟩, rfl⟩
  have hx1 : x₁ * (Θ ⟨v, hvHs⟩ x₁)⁻¹ = c₀ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hΘval, hx₁, hc₀]
    dsimp only
    have key : (⟨d * z * d⁻¹, hdzN⟩ : ↥(Subgroup.normalizer (Z₁ : Set G))) =
        ⟨u₁, hNz hu₁⟩ * ⟨v, hvN1⟩ * (⟨u₁, hNz hu₁⟩)⁻¹ * (⟨v, hvN1⟩)⁻¹ :=
      Subtype.ext hcomm.symm
    rw [key, map_mul, map_mul, map_mul, map_inv, map_inv]
    group
  have hconj : ∀ w : ↥(Subgroup.normalizer (Z₁ : Set G) ⊓ Subgroup.normalizer (Ugrp Z₁ D₃ : Set G)),
      w.1 ∈ Subgroup.normalizer (oTwoUpper H : Set G) →
      ∀ g ∈ φ.range, Θ w * g * (Θ w)⁻¹ ∈ φ.range := by
    intro w hwK g hg
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
    have hkw : w.1 * k.1 * w.1⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp hwK k.1).mp k.2
    refine MonoidHom.mem_range.mpr ⟨⟨w.1 * k.1 * w.1⁻¹, hkw⟩, ?_⟩
    have e1 : φ ⟨w.1 * k.1 * w.1⁻¹, hkw⟩ = Θ (w * ⟨k.1, hKHs k.2⟩ * w⁻¹) := by
      rw [hφ]
      exact congrArg Θ (Subtype.ext rfl)
    have e2 : Θ w * φ k * (Θ w)⁻¹ = Θ (w * ⟨k.1, hKHs k.2⟩ * w⁻¹) := by
      rw [hφ, map_mul, map_mul, map_inv]
    rw [e1, e2]
  have hvvE : Θ ⟨v, hvHs⟩ * Θ ⟨v, hvHs⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨v, hvHs⟩ * ⟨v, hvHs⟩ : ↥(Subgroup.normalizer (Z₁ : Set G) ⊓
        Subgroup.normalizer (Ugrp Z₁ D₃ : Set G))) = 1 := Subtype.ext hvv
    rw [h1, map_one]
  have hvNorm : Θ ⟨v, hvHs⟩ ∈ Subgroup.normalizer
      ((φ.range : Subgroup (MulAut ↥(tildeOf Z₁ (Ugrp Z₁ D₃)))) :
        Set (MulAut ↥(tildeOf Z₁ (Ugrp Z₁ D₃)))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact hconj ⟨v, hvHs⟩ hvK g hg
    · intro hg
      have h1 := hconj (⟨v, hvHs⟩⁻¹) (inv_mem hvK) _ hg
      rw [map_inv] at h1
      have e : (Θ ⟨v, hvHs⟩)⁻¹ * (Θ ⟨v, hvHs⟩ * g * (Θ ⟨v, hvHs⟩)⁻¹) *
          ((Θ ⟨v, hvHs⟩)⁻¹)⁻¹ = g := by group
      rwa [e] at h1
  have hKmem : ∀ k : ↥(oTwoUpper H), φ k ∈ φ.range :=
    fun k => MonoidHom.mem_range.mpr ⟨k, rfl⟩
  rcases hsimpO.eq_bot_or_eq_top_of_normal
      ((φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H)))) with hb | ht
  ·
    have hker : φ.ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
      refine le_antisymm (fun x hx => ?_) hpC_ker
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H)) x ∈
          (φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H))) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hb, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    have eK : O2Q (oTwoUpper H) ≃* ↥φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans (QuotientGroup.quotientKerEquivRange φ)
    have hsimpR : IsSimpleGroup ↥φ.range := MulEquiv.isSimpleGroup eK.symm
    haveI : IsSimpleGroup ↥φ.range := hsimpR
    have hcardR : Nat.card ↥φ.range = 20160 :=
      (Nat.card_congr eK.symm.toEquiv).trans
        (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hcl)
    have hab : ¬ IsMulCommutative ↥φ.range := by
      intro hc
      letI : CommGroup ↥φ.range := commGroupOfComm523 (fun a b => hc.is_comm.comm a b)
      have hp := IsSimpleGroup.prime_card (α := ↥φ.range)
      rw [hcardR] at hp
      norm_num at hp
    obtain ⟨-, K', hK'field, hK'fin, hK'card, ⟨eO⟩⟩ := hcl
    haveI : CharP K' 2 :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hK'card
    have hK4 : Nat.card K' = 4 := by rw [hK'card]; norm_num
    have hisoR : Nonempty (↥φ.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K') :=
      ⟨eK.symm.trans (eO.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K').symm)⟩
    have hfix := abs_main hH47 K' hK4 φ.range hab (by rw [hcardR]; norm_num) hisoR hE2
      (Θ ⟨v, hvHs⟩) hvvE hvNorm (hE '' (F : Set G)) hXc hcm
    have hfix2 := hfix (φ ⟨k₀, hk₀⟩) (hKmem ⟨k₀, hk₀⟩) x₁
    rw [hx1] at hfix2
    exact hnc hfix2
  ·
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H)) ⟨k₀, hk₀⟩ ∈
        (φ.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H))) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨n₀, hn₀, hnk⟩ := Subgroup.mem_map.mp hmk
    have hrel : n₀⁻¹ * ⟨k₀, hk₀⟩ ∈ CFSG.pCore 2 ↥(oTwoUpper H) := QuotientGroup.eq.mp hnk
    have hφk0 : φ ⟨k₀, hk₀⟩ = 1 := by
      have e : (⟨k₀, hk₀⟩ : ↥(oTwoUpper H)) = n₀ * (n₀⁻¹ * ⟨k₀, hk₀⟩) := by group
      rw [e, map_mul, MonoidHom.mem_ker.mp hn₀, hpC _ hrel, one_mul]
    exact hnc (by rw [hφk0, MulAut.one_apply])

theorem stmt5_1_23_direct (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h520 : Stmt5_1_20)
    (h522 : Stmt5_1_22) (hH47 : CFSG.ASVolI.H_4_7) : Stmt5_1_23 := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hZ1
  have hnle : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3, hnle, hZ1⟩
  by_contra hU
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨hn, N, hzN, hNVZ, hLN, hTN, -, D, hroot⟩ :=
    exists_natural_z s h5114 hF h522 hz hz1
  have hNT : N ≤ T :=
    hNVZ.trans (s.hyp.hyp.toHyp5_0_1.V_le_T (isCh5Module_VZ s.hyp h5114))
  obtain ⟨-, -, -, -, hV2⟩ := step1_coord s h5114 hF D hroot hn hLN hz hz1 hzN
  rcases hn with rfl | rfl
  ·
    obtain ⟨d, hd, hd1⟩ := s.exists_d
    have hdz : d * z * d⁻¹ ∈ conjClosure Z₁ D₃ := mem_conjClosure hd hz
    obtain ⟨c, hc0, u₁, hu₁, hu₁N, hρ⟩ :=
      Ugrp_has_uB s h5114 hF hU D hz hz1 hzN hTN hroot hV2
    obtain ⟨a₀, ha₀, hwa⟩ := coord_z_eq s D hroot hTN hz hz1 hzN
    obtain ⟨-, -, -, uA, -, huAN, -, -, -, c', -, -, hlist⟩ :=
      U_action_list s h5114 hF hU D hz hz1 hzN hTN hroot hV2
    obtain ⟨v, hvN, hvT, hcomm⟩ :=
      exists_v s D hzN hTN hNT ha₀ hwa hV2 hc0 hu₁ hu₁N hρ hdz
    obtain ⟨k₀, hk₀, hk₀'⟩ :=
      exists_k_moves_z' s h5114 hF h520 hyp not59 hmod hl34 hnot hD₃ h3 hU D hz hz1 hzN hTN
        hroot hV2 hd hd1
    exact E_contra s h5114 hF (stmt5_1_21_of_inputs h5114 h520 hF) hH47 hnot D hTN (uB 0)
      (uB c') ((D.conj ⟨uA, huAN⟩).trans (uB 0)) ((D.conj ⟨uA, huAN⟩).trans (uB c')) hlist hu₁
      hvN hvT hcomm hk₀ hk₀'
  ·
    exact false_of_n4 s h5114 hF hU D (fun a ha b hb => D.mem_comm ha hb) hz hz1 hzN hLN hTN hV2

end CFSG.Quasithin.H13
