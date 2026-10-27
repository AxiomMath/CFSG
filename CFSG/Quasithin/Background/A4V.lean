module

public import CFSG.Quasithin.Background.A4Aut
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace A4

theorem centerOf_le (R : Subgroup G) : centerOf R ≤ R := inf_le_left

theorem centerOf_le_centralizer (R : Subgroup G) :
    centerOf R ≤ Subgroup.centralizer (R : Set G) := inf_le_right

theorem omegaOneCenterOf_le_centerOf (R : Subgroup G) : omegaOneCenterOf R ≤ centerOf R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem omegaOneCenterOf_le (R : Subgroup G) : omegaOneCenterOf R ≤ R :=
  (omegaOneCenterOf_le_centerOf R).trans (centerOf_le R)

theorem sq_eq_one_of_mem_omegaOneCenterOf {R : Subgroup G} {z : G} (hz : z ∈ omegaOneCenterOf R) :
    z ^ 2 = 1 :=
  sq_eq_one_of_mem_omegaOneCenter R hz

theorem mul_comm_of_mem_omegaOneCenterOf {R : Subgroup G} {x y : G}
    (hx : x ∈ omegaOneCenterOf R) (hy : y ∈ omegaOneCenterOf R) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (centerOf_le_centralizer R (omegaOneCenterOf_le_centerOf R hx))
    y (omegaOneCenterOf_le R hy)).symm

theorem normalizer_le_normalizer_centerOf (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (centerOf R : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ c ∈ centerOf R, g * c * g⁻¹ ∈ centerOf R := by
    intro g hg c hc
    have hcent : g * c * g⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R := (Subgroup.mem_normalizer_iff''.mp hg r).mp hr
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hr'
      calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * r := by group
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hc.1, hcent⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_omegaOneOf (Z : Subgroup G) :
    Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (omegaOneOf Z : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Z : Set G), ∀ y ∈ omegaOneOf Z,
      g * y * g⁻¹ ∈ omegaOneOf Z := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
      have : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
      rw [this, hx.2]
      group
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (omegaOneOf Z).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (omegaOneOf Z).inv_mem ih
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_omegaOneCenterOf (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (omegaOneCenterOf R : Set G) :=
  (normalizer_le_normalizer_centerOf R).trans (normalizer_le_normalizer_omegaOneOf _)

end A4

theorem VYR_le_inf {Y R : Subgroup G} (hR : IsSignalizer (Subgroup.normalizer (Y : Set G)) Y R) :
    VYR Y R ≤ Y ⊓ omegaOneCenterOf R := by
  refine le_inf ?_ ?_
  ·
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((omegaOneCenterOf_le R).trans hR.1)
  ·
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hR.2.2.trans (normalizer_le_normalizer_omegaOneCenterOf R))

theorem VYR_le_omegaOneCenterOf {Y R : Subgroup G}
    (hR : IsSignalizer (Subgroup.normalizer (Y : Set G)) Y R) : VYR Y R ≤ omegaOneCenterOf R :=
  (VYR_le_inf hR).trans inf_le_right

theorem VYR_eq_commutator {Y R : Subgroup G} (hY : Y = oTwoUpper Y)
    (hR : IsSignalizer (Subgroup.normalizer (Y : Set G)) Y R) : VYR Y R = ⁅VYR Y R, Y⁆ := by
  set Ω := omegaOneCenterOf R with hΩ
  have hΩY : Y ≤ Subgroup.normalizer (Ω : Set G) :=
    hR.2.2.trans (normalizer_le_normalizer_omegaOneCenterOf R)
  have hWΩ : ⁅Ω, Y⁆ ≤ Ω := Subgroup.le_normalizer_iff_commutator_le_left.mp hΩY
  have hYW : Y ≤ Subgroup.normalizer (⁅Ω, Y⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right Ω Y
  have hW'W : ⁅⁅Ω, Y⁆, Y⁆ ≤ ⁅Ω, Y⁆ := Subgroup.le_normalizer_iff_commutator_le_left.mp hYW
  have hcomm : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_omegaOneCenterOf hx hy
  have hW'Ω : ⁅⁅Ω, Y⁆, Y⁆ ≤ Ω := hW'W.trans hWΩ
  have hΩW' : Ω ≤ Subgroup.normalizer (⁅⁅Ω, Y⁆, Y⁆ : Subgroup G) := by
    refine Subgroup.le_normalizer_iff_commutator_le_left.mpr ?_
    have h1 : ⁅⁅Ω, Y⁆, Y⁆ ≤ Subgroup.centralizer (Ω : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x (hW'Ω hx)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1]
    exact bot_le
  have key := commutator_le_of_oTwoUpper (A := Y) (N := ⁅⁅Ω, Y⁆, Y⁆) (B := ⁅Ω, Y⁆) (D := Ω)
    (Subgroup.normalizer_commutator_ge_right ⁅Ω, Y⁆ Y) hΩW' hWΩ
    (fun d hd => ⟨1, by rw [pow_one, sq_eq_one_of_mem_omegaOneCenterOf hd]; exact Subgroup.one_mem _⟩)
    (le_of_eq (Subgroup.commutator_comm Y Ω)) (le_of_eq (Subgroup.commutator_comm Y ⁅Ω, Y⁆))
  rw [← hY] at key
  show ⁅Ω, Y⁆ = ⁅⁅Ω, Y⁆, Y⁆
  exact le_antisymm ((Subgroup.commutator_comm Ω Y).le.trans key) hW'W

section Finite

variable [Finite G]

namespace A4

theorem isSignalizer_pCoreOf (Y : Subgroup G) :
    IsSignalizer (Subgroup.normalizer (Y : Set G)) Y (pCoreOf 2 Y) :=
  ⟨(pCoreOf_le 2 Y).trans Subgroup.le_normalizer, pCoreOf_isPGroup 2 Y,
    le_normalizer_pCoreOf 2 Y⟩

end A4

theorem VY_eq_commutator {Y : Subgroup G} (hY : Y = oTwoUpper Y) : VY Y = ⁅VY Y, Y⁆ :=
  VYR_eq_commutator hY (isSignalizer_pCoreOf Y)

structure A48Hyp (X M R S : Subgroup G) : Prop where
  xclass : IsXClass X
  subnormal : IsSubnormal X M
  signalizerR : IsSignalizer M X R
  signalizerS : IsSignalizer M X S
  vle : VYR X S ≤ R
  rle : R ≤ S
  o2le : pCoreOf 2 X ≤ S

namespace A4

omit [Finite G] in
theorem isSignalizer_normalizer {X M R : Subgroup G} (hX : X = oTwoUpper X)
    (hXM : IsSubnormal X M) (hR : IsSignalizer M X R) :
    IsSignalizer (Subgroup.normalizer (X : Set G)) X R :=
  ⟨Subgroup.le_normalizer_iff_commutator_le_left.mpr
    ((a4_2_3 hX hXM hR).trans (pCoreOf_le 2 X)), hR.2.1, hR.2.2⟩

theorem VY_le_pCoreOf (X : Subgroup G) : VY X ≤ pCoreOf 2 X :=
  (VYR_le_omegaOneCenterOf (isSignalizer_pCoreOf X)).trans (omegaOneCenterOf_le _)

omit [Finite G] in
theorem normalizer_VY (X : Subgroup G) : X ≤ Subgroup.normalizer (VY X : Set G) :=
  Subgroup.normalizer_commutator_ge_right (omegaOneCenterOf (pCoreOf 2 X)) X

theorem pCoreOf_le_centralizer_VY (X : Subgroup G) :
    pCoreOf 2 X ≤ Subgroup.centralizer (VY X : Set G) := by
  have h1 : VY X ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) :=
    ((VYR_le_omegaOneCenterOf (isSignalizer_pCoreOf X)).trans
      (omegaOneCenterOf_le_centerOf _)).trans (centerOf_le_centralizer _)
  exact Subgroup.le_centralizer_iff.mp h1

end A4

omit [Finite G] in
theorem A48Hyp.of_self {X M S : Subgroup G} (hXc : IsXClass X) (hXM : IsSubnormal X M)
    (hS : IsSignalizer M X S) (hO : pCoreOf 2 X ≤ S) : A48Hyp X M S S :=
  ⟨hXc, hXM, hS, hS,
    (VYR_le_omegaOneCenterOf (isSignalizer_normalizer hXc.2.1 hXM hS)).trans (omegaOneCenterOf_le S),
    le_rfl, hO⟩

variable {X M R S : Subgroup G}

theorem a4_8_1 (h : A48Hyp X M R S) :
    pCoreOf 2 X ≤ Subgroup.centralizer (VY X : Set G) ∧
      autOn R (VY X) ≤ Subgroup.centralizer (autOn X (VY X) : Set (MulAut (VY X))) :=
  ⟨pCoreOf_le_centralizer_VY X, autOn_le_centralizer_autOn
    ((a4_2_3 h.xclass.2.1 h.subnormal h.signalizerR).trans (pCoreOf_le_centralizer_VY X))⟩

theorem a4_8_2_center (h : A48Hyp X M R S) (hchief : NoncentralTwoChiefFactorsInO2 X) :
    pCoreOf 2 (autOn X (VY X)) ≤ centerOf (autOn X (VY X)) :=
  pCoreOf_autOn_le_centerOf (normalizer_VY X) h.xclass.2.1 hchief (pCoreOf_le_centralizer_VY X)

theorem a4_8_2_bot (_h : A48Hyp X M R S) (hall : TwoChiefFactorsInO2 X) :
    pCoreOf 2 (autOn X (VY X)) = ⊥ :=
  pCoreOf_autOn_eq_bot (normalizer_VY X) hall (pCoreOf_le_centralizer_VY X)

omit [Finite G] in
theorem a4_8_3 (h : A48Hyp X M R S) :
    VYR X S = ⁅VYR X R ⊓ Subgroup.centralizer (S : Set G), X⁆ := by
  have hXX := h.xclass.2.1
  have hRN := isSignalizer_normalizer hXX h.subnormal h.signalizerR
  have hSN := isSignalizer_normalizer hXX h.subnormal h.signalizerS
  have hVS_le := VYR_le_inf hSN
  have hVR_le := VYR_le_inf hRN
  have hΩS_cent : omegaOneCenterOf S ≤ Subgroup.centralizer (S : Set G) :=
    (omegaOneCenterOf_le_centerOf S).trans (centerOf_le_centralizer S)
  have hVS_R : VYR X S ≤ omegaOneCenterOf R := by
    intro v hv
    have hvS := (hVS_le hv).2
    have hvcent : v ∈ Subgroup.centralizer (R : Set G) :=
      Subgroup.centralizer_le (h.rle : (R : Set G) ⊆ S) (hΩS_cent hvS)
    exact Subgroup.subset_closure ⟨⟨h.vle hv, hvcent⟩, sq_eq_one_of_mem_omegaOneCenterOf hvS⟩
  apply le_antisymm
  · calc VYR X S = ⁅VYR X S, X⁆ := VYR_eq_commutator hXX hSN
      _ ≤ ⁅VYR X R ⊓ Subgroup.centralizer (S : Set G), X⁆ := by
        refine Subgroup.commutator_mono (le_inf ?_ fun v hv => hΩS_cent (hVS_le hv).2) le_rfl
        calc VYR X S = ⁅VYR X S, X⁆ := VYR_eq_commutator hXX hSN
          _ ≤ ⁅omegaOneCenterOf R, X⁆ := Subgroup.commutator_mono hVS_R le_rfl
  ·
    have hle : VYR X R ⊓ Subgroup.centralizer (S : Set G) ≤ omegaOneCenterOf S := by
      rintro v ⟨hvR, hvS⟩
      have hvΩ := (hVR_le hvR).2
      have hvRR := omegaOneCenterOf_le R hvΩ
      exact Subgroup.subset_closure ⟨⟨h.rle hvRR, hvS⟩, sq_eq_one_of_mem_omegaOneCenterOf hvΩ⟩
    exact Subgroup.commutator_mono hle le_rfl

theorem a4_8_4 (h : A48Hyp X M R S) :
    VYR X S = ⁅VY X ⊓ Subgroup.centralizer (S : Set G), X⁆ := by
  have hXX := h.xclass.2.1
  have hSN := isSignalizer_normalizer hXX h.subnormal h.signalizerS
  have hO2 : IsSignalizer M X (pCoreOf 2 X) :=
    ⟨(pCoreOf_le 2 X).trans (subnormal_le h.subnormal), pCoreOf_isPGroup 2 X,
      le_normalizer_pCoreOf 2 X⟩
  have hVS : VYR X S ≤ pCoreOf 2 X :=
    calc VYR X S = ⁅VYR X S, X⁆ := VYR_eq_commutator hXX hSN
      _ ≤ ⁅S, X⁆ :=
        Subgroup.commutator_mono ((VYR_le_omegaOneCenterOf hSN).trans (omegaOneCenterOf_le S)) le_rfl
      _ = ⁅X, S⁆ := Subgroup.commutator_comm S X
      _ ≤ pCoreOf 2 X := a4_2_3 hXX h.subnormal h.signalizerS
  exact a4_8_3 (R := pCoreOf 2 X)
    ⟨h.xclass, h.subnormal, hO2, h.signalizerS, hVS, h.o2le, h.o2le⟩

theorem a4_8_5 (h : A48Hyp X M R S) : VYR X S ≠ ⊥ ↔ VY X ≠ ⊥ := by
  have hXX := h.xclass.2.1
  have hSN := isSignalizer_normalizer hXX h.subnormal h.signalizerS
  have h4 := a4_8_4 h
  constructor
  · intro hne hVY
    apply hne
    rw [h4, hVY]
    simp
  · intro hne hVS
    apply hne
    rw [hVS] at h4
    have hfix : X ≤ Subgroup.centralizer
        ((VY X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4.symm)
    have hS2 : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k ∈ Subgroup.centralizer (VY X : Set G) := by
      intro s hs
      obtain ⟨k, hk⟩ := h.signalizerS.2.1 ⟨s, hs⟩
      exact ⟨k, by rw [show s ^ 2 ^ k = 1 from congrArg Subtype.val hk]; exact Subgroup.one_mem _⟩
    have hXV := thompson_axb ((pCoreOf_isPGroup 2 X).to_le (VY_le_pCoreOf X)) hXX
      (normalizer_VY X)
      (fun s hs => mem_normalizer_commutator
        (normalizer_le_normalizer_omegaOneCenterOf _
          (normalizer_le_normalizer_pCoreOf 2 X (hSN.1 hs))) (hSN.1 hs))
      hS2 ((a4_2_3 hXX h.subnormal h.signalizerS).trans (pCoreOf_le_centralizer_VY X)) hfix
    have h1 : ⁅VY X, X⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hXV)
    rw [VY_eq_commutator hXX, h1]

theorem a4_9 (hXc : IsXClass X) (hXM : IsSubnormal X M) :
    ⁅omegaOneCenterOf (pCoreOf 2 M), X⁆ ≠ ⊥ ↔ ⁅omegaOneCenterOf (pCoreOf 2 X), X⁆ ≠ ⊥ := by
  have hS : IsSignalizer M X (pCoreOf 2 M) :=
    ⟨pCoreOf_le 2 M, pCoreOf_isPGroup 2 M, (subnormal_le hXM).trans (le_normalizer_pCoreOf 2 M)⟩
  exact a4_8_5 (A48Hyp.of_self hXc hXM hS (pCoreOf_le_of_subnormal 2 hXM))

namespace A4

omit [Finite G] in
theorem centralizerSection_inf_normalizer (M X Z : Subgroup G) :
    centralizerSection (M ⊓ Subgroup.normalizer (X : Set G)) X Z = centralizerSection M X Z := by
  ext m
  simp only [mem_centralizerSection, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2⟩⟩

omit [Finite G] in
theorem centralizerSection_eq_inf {T K : Subgroup G} (hTK : T ≤ K) (X Z : Subgroup G) :
    centralizerSection T X Z =
      (T ⊓ Subgroup.normalizer (X : Set G)) ⊓ centralizerSection K X Z := by
  ext m
  simp only [mem_centralizerSection, Subgroup.mem_inf]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, hTK h.1, h.2⟩, fun h => ⟨h.1.1, h.2.2⟩⟩

theorem charTwo_sup {Y T : Subgroup G} (hY : CharTwo Y) (hT : T ≤ Subgroup.normalizer (Y : Set G))
    (hT2 : IsPGroup 2 T) : CharTwo (Y ⊔ T) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hY hT2 hT

end A4

structure A410Hyp (X Y T : Subgroup G) : Prop where
  xclass : IsXClass X
  yclass : IsXClass Y
  xy : X ≤ Y
  normalizes : T ≤ Subgroup.normalizer (Y : Set G)
  sylowT : IsSylowTwoOf T (Y ⊔ T)
  o2le : pCoreOf 2 (Y ⊔ T) ≤ T ⊓ Subgroup.normalizer (X : Set G)
  sylowNT : IsSylowTwoOf (T ⊓ Subgroup.normalizer (X : Set G))
    ((Y ⊔ T) ⊓ Subgroup.normalizer (X : Set G))

theorem a4_10_1 {X Y T : Subgroup G} (h : A410Hyp X Y T) :
    IsMaxSignalizer ((Y ⊔ T) ⊓ Subgroup.normalizer (X : Set G)) X
      (centralizerSection T X (pCoreOf 2 X)) := by
  have hXM : IsSubnormal X ((Y ⊔ T) ⊓ Subgroup.normalizer (X : Set G)) :=
    subnormal_of_normal (le_inf (h.xy.trans le_sup_left) Subgroup.le_normalizer)
      (Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right)
  rw [A4.centralizerSection_eq_inf (le_sup_right : T ≤ Y ⊔ T)]
  refine (a4_2_4 h.xclass.2.1 hXM _).mpr ?_
  rw [A4.centralizerSection_inf_normalizer]
  exact isSylowTwoOf_inf_centralizerSection h.sylowNT

namespace A4

theorem pCoreOf_sup_le_centralizerSection {X Y T : Subgroup G} (h : A410Hyp X Y T) :
    pCoreOf 2 (Y ⊔ T) ≤ centralizerSection T X (pCoreOf 2 X) := by
  have hmax := a4_10_1 h
  set K := Y ⊔ T with hK
  set S := centralizerSection T X (pCoreOf 2 X) with hS
  have hP : IsSignalizer ((Y ⊔ T) ⊓ Subgroup.normalizer (X : Set G)) X (pCoreOf 2 K ⊔ S) := by
    refine ⟨sup_le (le_inf (pCoreOf_le 2 K) (h.o2le.trans inf_le_right)) hmax.1.1, ?_, ?_⟩
    · exact IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 K) hmax.1.2.1
        (hmax.1.1.trans (inf_le_left.trans (le_normalizer_pCoreOf 2 K)))
    · intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_pCoreOf 2 K (h.xy.trans le_sup_left hx), hmax.1.2.2 hx⟩
  have := hmax.eq_of_le hP le_sup_right
  rw [← this]
  exact le_sup_left

end A4

theorem a4_10_2 {X Y T : Subgroup G} (h : A410Hyp X Y T) :
    VYR X (centralizerSection T X (pCoreOf 2 X)) ≤ VYR Y (pCoreOf 2 (Y ⊔ T)) := by
  set S := centralizerSection T X (pCoreOf 2 X) with hS
  set P := pCoreOf 2 (Y ⊔ T) with hP
  have hCT : CharTwo (Y ⊔ T) := A4.charTwo_sup h.yclass.2.2 h.normalizes h.sylowT.2.1
  have hPS : P ≤ S := A4.pCoreOf_sup_le_centralizerSection h
  have hSN : IsSignalizer (Subgroup.normalizer (X : Set G)) X S :=
    ⟨centralizerSection_le_normalizer_left T X _, (a4_10_1 h).1.2.1, (a4_10_1 h).1.2.2⟩
  have hZ : centerOf S ≤ centerOf P := by
    intro z hz
    have hzP : z ∈ Subgroup.centralizer (P : Set G) :=
      Subgroup.centralizer_le (fun x hx => hPS hx) hz.2
    have hzT : z ∈ T := centralizerSection_le_left T X _ hz.1
    have hzK : z ∈ Y ⊔ T := (le_sup_right : T ≤ Y ⊔ T) hzT
    exact ⟨hCT ⟨hzK, hzP⟩, hzP⟩
  have hΩ : omegaOneCenterOf S ≤ omegaOneCenterOf P :=
    Subgroup.closure_mono fun x hx => ⟨hZ hx.1, hx.2⟩
  calc VYR X S = ⁅VYR X S, X⁆ := VYR_eq_commutator h.xclass.2.1 hSN
    _ ≤ VYR Y P := Subgroup.commutator_mono
        ((VYR_le_omegaOneCenterOf hSN).trans hΩ) h.xy

theorem a4_10_3 {X Y T : Subgroup G} (h : A410Hyp X Y T) (hf : IsXf X) : IsXf Y := by
  set S := centralizerSection T X (pCoreOf 2 X) with hS
  set K := Y ⊔ T with hK
  set P := pCoreOf 2 K with hP
  have hmax := a4_10_1 h
  have hXM : IsSubnormal X ((Y ⊔ T) ⊓ Subgroup.normalizer (X : Set G)) :=
    subnormal_of_normal (le_inf (h.xy.trans le_sup_left) Subgroup.le_normalizer)
      (Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right)
  have hVS : VYR X S ≠ ⊥ :=
    (a4_8_5 (A48Hyp.of_self h.xclass hXM hmax.1
      (pCoreOf_le_of_isMaxSignalizer_of_subnormal h.xclass.2.1 hXM hmax))).mpr hf.2
  have hYK : IsSubnormal Y K :=
    subnormal_of_normal le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le Subgroup.le_normalizer h.normalizes))
  have hPsig : IsSignalizer K Y P :=
    ⟨pCoreOf_le 2 K, pCoreOf_isPGroup 2 K,
      (le_sup_left : Y ≤ K).trans (le_normalizer_pCoreOf 2 K)⟩
  have hVP : VYR Y P ≤ VY Y := by
    have h4 := a4_8_4 (A48Hyp.of_self h.yclass hYK hPsig (pCoreOf_le_of_subnormal 2 hYK))
    rw [h4]
    calc ⁅VY Y ⊓ Subgroup.centralizer (P : Set G), Y⁆ ≤ ⁅VY Y, Y⁆ :=
          Subgroup.commutator_mono inf_le_left le_rfl
      _ = VY Y := (VY_eq_commutator h.yclass.2.1).symm
  refine ⟨h.yclass, fun hVY => hVS ?_⟩
  exact le_bot_iff.mp ((a4_10_2 h).trans (hVP.trans hVY.le))

end Finite

end CFSG.Quasithin
