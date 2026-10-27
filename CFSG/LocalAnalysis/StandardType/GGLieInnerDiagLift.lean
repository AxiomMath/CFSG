module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly

private theorem ltlift_fixSubgroup_conj_eq_centralizer {R : Type*} [Group R] (x : R) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set R) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have h' : x * y = y * x := by
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h]
    exact h'.symm
  · intro h
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h.symm]
      _ = y := by group

private theorem ltlift_largeEvenInduces_eq_comm {X : Type*} [Group X] {J : Subgroup X}
    {R : Type} [Group R] (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) {a : MulAut X} {φ : MulAut R} :
    LargeEvenInduces θ (fun l l' : ↥J => a (l : X) = (l' : X)) φ ↔
      LargeEvenInduces θ (fun l l' : ↥J => (l' : X) = a (l : X)) φ :=
  ⟨fun h l l' hl => h l l' hl.symm, fun h l l' hl => h l l' hl.symm⟩

private theorem ltlift_ggMarkingAll_induces_I (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {X : Type*} [Group X] {ι : Type*}
    (rel : ι → X → X → Prop) (S : Set ι)
    (h : ∀ s ∈ S, LargeEvenMarking X fun _ _ _ I _ θ =>
      ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (rel s) φ) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ =>
      ∀ s ∈ S, ∃ φ ∈ I, LargeEvenInduces θ (rel s) φ := by
  intro P hP
  obtain ⟨hX, lab, hlab, hrawP⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_
    (hraw 3 Nat.prime_three (by norm_num) lab hlab _ (hiso lab hlab _ hrawP))⟩
  rintro R _ I F ⟨⟨⟨hs, hna, θ, hθ⟩, hisoR⟩, hinnR⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hinnR hs hna
  refine ⟨hs, hna, θ, hθ, fun s hsS => ?_⟩
  obtain ⟨-, labₛ, hlabₛ, hrawₛ⟩ := h s hsS
  obtain ⟨Rₛ, _, Iₛ, Fₛ, ⟨hss, hnas, θₛ, φₛ, hφₛ, hind⟩, hisoₛ⟩ :=
    largeEvenRawDatum_exists (hisoR hs hna labₛ hlabₛ _ hrawₛ)
  have hmem : (MulAut.congr (θ.symm.trans θₛ)).symm φₛ ∈ ggInndiag R I :=
    (hisoₛ hss hnas (θ.symm.trans θₛ) _).2 (by
      rw [MulEquiv.apply_symm_apply]; exact Subgroup.mem_sup_right hφₛ)
  refine ⟨_, (ggL45_mem_ggInndiag_iff hmul hinv hinn).1 hmem, ?_⟩
  intro l l' hl
  simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, hind l l' hl]

theorem ggLieInnerDiag_of_lift (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    {G : Type} [Group G] (hG : Subgroup.center G = ⊥) (ψ : X →* G)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center X)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hinn : ∀ a ∈ A, ∃ s : G, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹)
    (hcomps : GGInnerDiagOnComps G) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite G := Finite.of_surjective ψ hψ
  let E : Set G := {s | ∃ a ∈ A, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹}
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro s hs t ht
    obtain ⟨a, ha, hsa⟩ := hs
    obtain ⟨b, hb, htb⟩ := ht
    have hab : a * b = b * a := by
      have h := (isMulCommutative_iff.mp hl.1.1) ⟨a, ha⟩ ⟨b, hb⟩
      simpa using congrArg Subtype.val h
    have hkey : ∀ y : G, (s * t) * y * (s * t)⁻¹ = (t * s) * y * (t * s)⁻¹ := by
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      calc (s * t) * ψ x * (s * t)⁻¹
          = s * (t * ψ x * t⁻¹) * s⁻¹ := by group
        _ = s * ψ (b x) * s⁻¹ := by rw [← htb x]
        _ = ψ (a (b x)) := (hsa (b x)).symm
        _ = ψ (b (a x)) := by
              rw [show a (b x) = b (a x) from congrArg (fun f : MulAut X => f x) hab]
        _ = t * ψ (a x) * t⁻¹ := htb (a x)
        _ = t * (s * ψ x * s⁻¹) * t⁻¹ := by rw [hsa x]
        _ = (t * s) * ψ x * (t * s)⁻¹ := by group
    have hcentral : (t * s)⁻¹ * (s * t) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3' : (s * t) * y = (t * s) * y * (t * s)⁻¹ * (s * t) := by
        have h := congrArg (fun z => z * (s * t)) (hkey y)
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
      have hmain : (t * s)⁻¹ * (s * t) * y = y * ((t * s)⁻¹ * (s * t)) := by
        calc (t * s)⁻¹ * (s * t) * y = (t * s)⁻¹ * ((s * t) * y) := by group
          _ = (t * s)⁻¹ * ((t * s) * y * (t * s)⁻¹ * (s * t)) := by rw [h3']
          _ = y * ((t * s)⁻¹ * (s * t)) := by group
      exact hmain.symm
    have hu1 : (t * s)⁻¹ * (s * t) = 1 := by
      rw [hG] at hcentral
      simpa using hcentral
    have hst : s * t = t * s := by
      have h := congrArg (fun z => (t * s) * z) hu1
      rw [mul_one, mul_inv_cancel_left] at h
      exact h
    exact hst
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro s hs
    obtain ⟨a, ha, hsa⟩ := hs
    have ha3 : a ^ 3 = 1 := hl.1.2 a ha
    have hcentral : s ^ 3 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      have hiter : ψ ((a ^ 3) x) = s ^ 3 * ψ x * (s ^ 3)⁻¹ := by
        calc ψ ((a ^ 3) x) = ψ (a (a (a x))) := by
              rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
          _ = s * ψ (a (a x)) * s⁻¹ := hsa (a (a x))
          _ = s * (s * ψ (a x) * s⁻¹) * s⁻¹ := by rw [hsa (a x)]
          _ = s * (s * (s * ψ x * s⁻¹) * s⁻¹) * s⁻¹ := by rw [hsa x]
          _ = s ^ 3 * ψ x * (s ^ 3)⁻¹ := by rw [pow_three]; group
      have hxx : ψ ((a ^ 3) x) = ψ x := by rw [ha3, MulAut.one_apply]
      rw [hxx] at hiter
      have hcomm3 : ψ x * s ^ 3 = s ^ 3 * ψ x := by
        conv_lhs => rw [hiter]
        rw [pow_three]
        group
      exact hcomm3
    rw [hG] at hcentral
    simpa using hcentral
  obtain ⟨d, hd⟩ := hinn δ hl.2.1
  have hdE : d ∈ E := ⟨δ, hl.2.1, hd⟩
  have hd1 : d ≠ 1 := by
    intro hd1
    have hg1 : ggInducedAut (MulEquiv.refl (X ⧸ Subgroup.center X)) δ = 1 := by
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change ggInducedAut (MulEquiv.refl (X ⧸ Subgroup.center X)) δ
        ((MulEquiv.refl (X ⧸ Subgroup.center X)) (x : X ⧸ Subgroup.center X)) =
        (1 : MulAut (X ⧸ Subgroup.center X)) ↑x
      rw [ggInducedAut_apply, MulAut.one_apply, MulEquiv.refl_apply]
      have hψeq : ψ (δ x) = ψ x := by
        rw [hd x, hd1]
        group
      have hmem : (δ x)⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, inv_mul_cancel]
      rw [hker] at hmem
      exact QuotientGroup.eq.mpr hmem
    have hδ1 : δ = 1 :=
      ggInducedAut_injective_of_perfect hX (MulEquiv.refl (X ⧸ Subgroup.center X))
        (by rw [hg1, map_one])
    exact hl.2.2.1 hδ1
  have hd3 : d ^ 3 = 1 := hE3 d hdE
  have hS4 : (ggAutFixedSubgroup δ).map ψ = Subgroup.centralizer ({d} : Set G) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hd x
      rw [show δ x = x from hx] at h
      conv_lhs => rw [h]
      group
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      obtain ⟨x, rfl⟩ := hψ y
      have hconj : d * ψ x * d⁻¹ = ψ x := by
        rw [← hy, mul_assoc, mul_inv_cancel, mul_one]
      have hfixδ : ψ (δ x) = ψ x := by rw [hd x, hconj]
      have hfix : ∀ φ ∈ Subgroup.zpowers δ, ψ (φ x) = ψ x := by
        intro φ hφ
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφ
        have hδ3z : δ ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact hl.1.2 δ hl.2.1
        rw [← hk, zpow_eq_zpow_emod k hδ3z]
        obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        · rw [h, zpow_zero, MulAut.one_apply]
        · rw [h, zpow_one]
          exact hfixδ
        · rw [h]
          have h2 : (δ ^ (2 : ℤ)) x = δ (δ x) := by
            rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
              show (2 : ℕ) = 1 + 1 by norm_num, pow_add, pow_one, MulAut.mul_apply]
          rw [h2, hd (δ x), hfixδ, hconj]
      have hF : IsPGroup 3 (Subgroup.zpowers δ) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers]
        have hdvd : orderOf δ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hl.1.2 δ hl.2.1)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
        · exact absurd (orderOf_eq_one_iff.mp h1) hl.2.2.1
        · rw [h3', pow_one]
      have hFker : ∀ φ ∈ Subgroup.zpowers δ, ∀ c ∈ ψ.ker, φ c ∈ ψ.ker := by
        intro φ hφ c hc
        rw [hker] at hc ⊢
        rw [Subgroup.mem_center_iff] at hc ⊢
        intro w
        calc w * φ c = φ ((φ⁻¹) w) * φ c := by simp
          _ = φ ((φ⁻¹) w * c) := by rw [map_mul]
          _ = φ (c * (φ⁻¹) w) := by rw [hc]
          _ = φ c * φ ((φ⁻¹) w) := by rw [map_mul]
          _ = φ c * w := by simp
      obtain ⟨j, -, hjψ, hjfix⟩ :=
        ggLieSU3Fixed_exists_fixed_lift (p := 3) ψ (by rw [hker]; exact h3)
          (Subgroup.zpowers δ) hF hFker ⊤ (fun _ _ j _ => trivial) trivial hfix
      exact ⟨j, (mem_ggAutFixedSubgroup δ j).mpr (hjfix δ (Subgroup.mem_zpowers δ)), hjψ⟩
  have hker_le : ψ.ker ≤ Subgroup.center X := hker ▸ le_rfl
  have hJan : Assembly.IsComponentOf (J.map ψ) (Subgroup.centralizer ({d} : Set G)) := by
    have h := CFSG.ComponentClassification.HarrisLit.N36.isComponentOf_map_of_ker_le_center
      ψ hker_le hl.2.2.2.1
    rwa [hS4] at h
  have hJperf : ⁅J, J⁆ = J :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hl.2.2.2.1.2.2.1)
  have hJcompO : CFSG.Open.IsComponentOf (J.map ψ)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj d)) := by
    rw [ltlift_fixSubgroup_conj_eq_centralizer]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJan
  intro P hP
  have hT : LargeEvenMarking ↥J (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hP
  have hMmap : LargeEvenMarking ↥(J.map ψ) (fun _ _ _ _ _ _ => True) :=
    (largeEvenMarking_map_iff hker_le hJperf (fun _ => True)).1 hT
  have hnotout : ∀ a ∈ A, ¬ GGOutsideInndiag J a := by
    intro a ha
    obtain ⟨s, hs⟩ := hinn a ha
    have hsE : s ∈ E := ⟨a, ha, hs⟩
    have hs3 : s ^ 3 = 1 := hE3 s hsE
    have hcomm : d * s = s * d := hEcomm d hdE s hsE
    have hnotmap : ¬ GGOutsideInndiag (J.map ψ) (MulAut.conj s) :=
      not_ggOutsideInndiag_of_innerDiagOnComps hcomps hd3 hd1 hs3 hcomm hJcompO hMmap
    have hφ : ∀ l : X, MulAut.conj s (ψ l) = ψ (a l) := fun l => (hs l).symm
    intro hout
    exact hnotmap ((ggOutsideInndiag_map_iff hker_le hφ hJperf).1 hout)
  have h : ∀ a ∈ A, LargeEvenMarking ↥J fun _ _ _ I _ θ =>
      ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun l l' : ↥J => a (l : X) = (l' : X)) φ := by
    intro a ha
    have hmaps_a : ∀ l ∈ J, a l ∈ J := hl.2.2.2.2 a ha
    have hM_or : LargeEvenMarking ↥J
        (fun lab R _ I F θ =>
          (∃ φ ∈ Subgroup.closure I,
              LargeEvenInduces θ (fun l l' : ↥J => (l' : X) = a (l : X)) φ) ∨
            ¬ ∃ φ ∈ Subgroup.closure I,
              LargeEvenInduces θ (fun l l' : ↥J => (l' : X) = a (l : X)) φ) :=
      largeEvenMarking_mono (fun lab R _ I F θ _ =>
        em (∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ (fun l l' : ↥J => (l' : X) = a (l : X)) φ)) hP
    rcases largeEvenMarking_or hM_or with hE | hQ
    · exact largeEvenMarking_mono (fun _ _ _ I _ θ hEcl => by
        obtain ⟨φ, hφ, hind⟩ := hEcl
        exact ⟨φ, hφ, (ltlift_largeEvenInduces_eq_comm θ).2 hind⟩) hE
    · exact absurd
        (ggMarkingAll_not_induces hraw hiso
          (rel := fun l l' : ↥J => (l' : X) = a (l : X)) hQ)
        (fun hQall => hnotout a ha ⟨hmaps_a, hQall⟩)
  exact ltlift_ggMarkingAll_induces_I hraw hiso
    (rel := fun (a : MulAut X) (l : ↥J) (l' : ↥J) => a (l : X) = (l' : X)) (S := A) h P hP

end CFSG.StandardType.SCFourCover

end
