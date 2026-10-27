module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67AltRed

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem mkr_commutatorElement_central {L : Type} [Group L] {z : L}
    (hz : z ∈ Subgroup.center L) (x y : L) :
    (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  letI : Bracket L L := commutatorElement
  show ⁅x * z, y⁆ = ⁅x, y⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hz1 : ⁅z, y⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz y).symm
  rw [hz1, mul_one]
  group

private theorem mkr_commutatorElement_central_right {L : Type} [Group L] {z : L}
    (hz : z ∈ Subgroup.center L) (x y : L) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  letI : Bracket L L := commutatorElement
  show ⁅x, y * z⁆ = ⁅x, y⁆
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hz1 : ⁅x, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp hz x
  rw [hz1, mul_one]
  group

private theorem mkr_commutatorElement_out {L : Type} [Group L] (a b : L) :
    (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
        (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
        (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ *
        (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ =
      a * b * a⁻¹ * b⁻¹ := by
  letI : Bracket L L := commutatorElement
  show ⁅(Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L),
      (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁆ = ⁅a, b⁆
  have ha : (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ *
      a ∈ Subgroup.center L := by
    refine QuotientGroup.eq.mp ?_
    simpa using Quotient.out_eq (QuotientGroup.mk a : L ⧸ Subgroup.center L)
  have hb : (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ *
      b ∈ Subgroup.center L := by
    refine QuotientGroup.eq.mp ?_
    simpa using Quotient.out_eq (QuotientGroup.mk b : L ⧸ Subgroup.center L)
  have ha' : a = (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
      ((Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ * a) := by group
  have hb' : b = (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
      ((Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ * b) := by group
  conv_rhs => rw [ha', hb']
  change (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
      (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
      (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ *
      (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ =
    ((Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
        ((Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ * a)) *
      ((Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
        ((Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ * b)) *
      ((Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
        ((Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ * a))⁻¹ *
      ((Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
        ((Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ * b))⁻¹
  rw [mkr_commutatorElement_central ha, mkr_commutatorElement_central_right hb]

private theorem mkr_finite_commutatorSet {L : Type} [Group L]
    [Finite (L ⧸ Subgroup.center L)] : Finite (commutatorSet L) := by
  classical
  let f : (L ⧸ Subgroup.center L) × (L ⧸ Subgroup.center L) → ↥(commutatorSet L) :=
    fun p => ⟨(Quotient.out p.1 : L) * (Quotient.out p.2 : L) *
        (Quotient.out p.1 : L)⁻¹ * (Quotient.out p.2 : L)⁻¹,
      by
        letI : Bracket L L := commutatorElement
        rw [commutatorSet_def]
        exact ⟨_, _, rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨w, hw⟩
  letI : Bracket L L := commutatorElement
  rw [commutatorSet_def] at hw
  obtain ⟨a, b, hab⟩ := hw
  refine ⟨((QuotientGroup.mk a : L ⧸ Subgroup.center L),
    (QuotientGroup.mk b : L ⧸ Subgroup.center L)), ?_⟩
  apply Subtype.ext
  show (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L) *
      (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L) *
      (Quotient.out (QuotientGroup.mk a : L ⧸ Subgroup.center L) : L)⁻¹ *
      (Quotient.out (QuotientGroup.mk b : L ⧸ Subgroup.center L) : L)⁻¹ = w
  rw [mkr_commutatorElement_out]
  exact hab

private theorem mkr_finite_of_quotient_center {L : Type} [Group L]
    (hperf : commutator L = ⊤) [Finite (L ⧸ Subgroup.center L)] : Finite L := by
  haveI : Finite (commutatorSet L) := mkr_finite_commutatorSet
  haveI : Finite (commutator L) := inferInstance
  haveI : Finite ↥(⊤ : Subgroup L) := by
    simpa [hperf] using (inferInstance : Finite (commutator L))
  exact Finite.of_injective (Subgroup.topEquiv.symm) Subgroup.topEquiv.symm.injective

private theorem mkr_inner_of_marking {G : Type} [Group G] {Bs L : Subgroup G} {R : Type} [Group R]
    (hperf : commutator ↥L = ⊤) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hinn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)
    {b : G} (hb : b ∈ Bs) :
    ∃ k ∈ L, ∀ l : ↥L, b * (l : G) * b⁻¹ = (k : G) * (l : G) * (k : G)⁻¹ := by
  obtain ⟨φ, hφI, hφ⟩ := hI b⁻¹ (Bs.inv_mem hb)
  obtain ⟨r, hr⟩ := hinn φ hφI
  obtain ⟨x, hx⟩ := θ.surjective r
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x
  have hθk : θ (QuotientGroup.mk k) = r := by rw [hk, hx]
  let l' : ↥L → ↥L := fun l =>
    ⟨b * (l : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hBsN hb) (l : G)).mp l.2⟩
  have hl' : ∀ l : ↥L, (l' l : G) = b * (l : G) * b⁻¹ := fun l => rfl
  have hrel : ∀ l : ↥L, (l' l : G) = (b⁻¹)⁻¹ * (l : G) * b⁻¹ := by
    intro l
    rw [hl' l, inv_inv]
  let z : ↥L → ↥L := fun l => (l' l)⁻¹ * (k * l * k⁻¹)
  have hz : ∀ l : ↥L, z l ∈ Subgroup.center ↥L := by
    intro l
    have hind := hφ l (l' l) (hrel l)
    have hEq : θ (QuotientGroup.mk (l' l)) = θ (QuotientGroup.mk (k * l * k⁻¹)) := by
      rw [← hind, hr, MulAut.conj_apply, ← hθk]
      simp
    exact QuotientGroup.eq.mp (θ.injective hEq)
  let σ : MulAut ↥L := ggConjAut L (hBsN hb)
  have hσ : ∀ l : ↥L, σ l = l' l := by
    intro l
    apply Subtype.ext
    rw [ggConjAut_apply]
  have hαmod : ∀ y : ↥L, y⁻¹ * (MulAut.conj (k⁻¹) * σ) y ∈ Subgroup.center ↥L := by
    intro y
    have hαy : (MulAut.conj (k⁻¹) * σ) y = k⁻¹ * l' y * k := by
      rw [MulAut.mul_apply, MulAut.conj_apply, hσ]
      simp
    rw [hαy]
    have hzq : l' y * z y = k * y * k⁻¹ := by
      show l' y * ((l' y)⁻¹ * (k * y * k⁻¹)) = k * y * k⁻¹
      group
    have hleq : l' y = (k * y * k⁻¹) * (z y)⁻¹ := by
      calc l' y = l' y * z y * (z y)⁻¹ := by group
        _ = (k * y * k⁻¹) * (z y)⁻¹ := by rw [hzq]
    have hz' : (z y)⁻¹ ∈ Subgroup.center ↥L := Subgroup.inv_mem _ (hz y)
    have hconj : k⁻¹ * (z y)⁻¹ * k ∈ Subgroup.center ↥L := by
      simpa using Subgroup.Normal.conj_mem (Subgroup.instNormalCenter (G := ↥L))
        (z y)⁻¹ hz' k⁻¹
    have heq : y⁻¹ * (k⁻¹ * l' y * k) = k⁻¹ * (z y)⁻¹ * k := by
      rw [hleq]
      group
    rw [heq]
    exact hconj
  have hα1 : MulAut.conj (k⁻¹) * σ = 1 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.eq_one_of_forall_mem_center
      (Group.isPerfect_def.mpr hperf) _ hαmod
  refine ⟨k, k.2, fun l => ?_⟩
  have h := congrArg (fun f : MulAut ↥L => (f l : ↥L)) hα1
  have hαl : (MulAut.conj (k⁻¹) * σ) l = k⁻¹ * l' l * k := by
    rw [MulAut.mul_apply, MulAut.conj_apply, hσ]
    simp
  have h1 : k⁻¹ * l' l * k = l := by
    rw [← hαl]
    simpa using h
  have h2 : l' l = k * l * k⁻¹ := by
    calc l' l = k * (k⁻¹ * l' l * k) * k⁻¹ := by group
      _ = k * l * k⁻¹ := by rw [h1]
  have h3 := congrArg Subtype.val h2
  simpa [l'] using h3

private theorem mkr_F4_witness {n : ℕ} {Q : LargeEvenRawCont}
    (h : CFSG.StandardType.LargeEvenRawDatum ⟨.F4, 0, n⟩ Q) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (I F : Set (MulAut R)), Q R I F := by
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  obtain ⟨K, _, hfin, _, hq⟩ := h
  letI := hfin
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) :=
    CFSG.StandardType.TCJ.tcjDatum_finite_chevH_false
      CFSG.Blueprint.Chevalley.Tag.F4 K
  exact ⟨_, inferInstance, inferInstance, _, _, hq⟩

private theorem mkr_E6_witness {n : ℕ} {Q : LargeEvenRawCont}
    (h : CFSG.StandardType.LargeEvenRawDatum ⟨.E6, 0, n⟩ Q) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (I F : Set (MulAut R)), Q R I F := by
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  obtain ⟨K, _, hfin, _, hq⟩ := h
  letI := hfin
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    CFSG.StandardType.TCJ.tcjDatum_finite_chevH_false
      CFSG.Blueprint.Chevalley.Tag.E6 K
  exact ⟨_, inferInstance, inferInstance, _, _, hq⟩

private theorem mkr_twE6_witness {n : ℕ} {Q : LargeEvenRawCont}
    (h : CFSG.StandardType.LargeEvenRawDatum ⟨.twE6, 0, n⟩ Q) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (I F : Set (MulAut R)), Q R I F := by
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  obtain ⟨K, _, hfin, hK, hq⟩ := h
  letI := hfin
  haveI : CharP K 2 :=
    CFSG.StandardType.TCJ.tcjDatum_charP_two_of_card (by rw [hK, pow_mul])
  haveI : Finite (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    CFSG.StandardType.TCJ.tcjDatum_finite_twistedH
      CFSG.Blueprint.Chevalley.TwistTag.E6 n K
      (iterateFrobenius K 2 n) (fun c => by rw [iterateFrobenius_def])
  exact ⟨_, inferInstance, inferInstance, _, _, hq⟩

private theorem mkr_rest {G : Type} [Group G] {Bs L : Subgroup G} {R : Type} [Group R]
    (hperf : commutator ↥L = ⊤) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (hZ : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ g ∈ Subgroup.center L', Nat.Coprime 3 (orderOf g))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)
    [Finite R] :
    commutator ↥L = ⊤ ∧
      (∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) ∧
      (∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g)) := by
  haveI : Finite (↥L ⧸ Subgroup.center ↥L) :=
    Finite.of_injective (θ : _ → R) θ.injective
  haveI : Finite ↥L := mkr_finite_of_quotient_center hperf
  refine ⟨hperf, ?_, ?_⟩
  · intro b hb
    obtain ⟨k, hk, hkl⟩ := mkr_inner_of_marking hperf θ hinn hBsN hI hb
    exact ⟨k, hk, fun l hl => hkl ⟨l, hl⟩⟩
  · intro g hg
    let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hsurj : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : ψ.ker ≤ Subgroup.center ↥L := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hmk : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        θ.injective (by simpa [ψ] using hx)
      rwa [QuotientGroup.eq_one_iff] at hmk
    exact hZ ↥L ψ hsurj hker hperf g hg

theorem ggR4Meet_marking_of_row (hrow : GGR4SurvivorRow)
    {G : Type} [Group G] {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .F4 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1))
      3 Bs L) :
    commutator ↥L = ⊤ ∧
      (∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) ∧
      (∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g)) ∧
      ∃ f : ℕ, 1 ≤ f ∧
        (GGHasLabel ⟨.F4, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∨
          (GGHasLabel ⟨.E6, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∧ 3 ∣ 2 ^ f + 1) ∨
          (GGHasLabel ⟨.twE6, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∧ 3 ∣ 2 ^ f - 1)) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hS : t = .F4 ∨ (t = .E6 ∧ 3 ∣ 2 ^ n + 1) ∨ (t = .twE6 ∧ 3 ∣ 2 ^ n - 1) :=
    GGDichotomy.rawDatum_elim_const (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, hP⟩ := hq
      exact hP.1) hraw)
  have hcomb := hrow ⟨t, l, n⟩ hlab hS _ hraw
  rcases hS with hF4 | ⟨hE6, h3E6⟩ | ⟨hT6, h3T6⟩
  · subst hF4
    have hl : l = 0 := hlab.2
    subst hl
    obtain ⟨R, hRgrp, hRfin, I, F, hq⟩ := mkr_F4_witness hcomb
    letI := hRgrp
    letI := hRfin
    obtain ⟨⟨-, -, θ, hP⟩, hrowfact⟩ := hq
    obtain ⟨-, hBsN, hI⟩ := hP
    obtain ⟨hp, hi, hc⟩ := mkr_rest hperf θ hBsN hrowfact.1 hrowfact.2 hI
    refine ⟨hp, hi, hc, n, hn, Or.inl ?_⟩
    show GGHasLabel ⟨.F4, 0, n⟩ (↥L ⧸ Subgroup.center ↥L)
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, -⟩ := hq
      exact ⟨θ⟩) hraw
  · subst hE6
    have hl : l = 0 := hlab.2
    subst hl
    obtain ⟨R, hRgrp, hRfin, I, F, hq⟩ := mkr_E6_witness hcomb
    letI := hRgrp
    letI := hRfin
    obtain ⟨⟨-, -, θ, hP⟩, hrowfact⟩ := hq
    obtain ⟨-, hBsN, hI⟩ := hP
    obtain ⟨hp, hi, hc⟩ := mkr_rest hperf θ hBsN hrowfact.1 hrowfact.2 hI
    refine ⟨hp, hi, hc, n, hn, Or.inr (Or.inl ⟨?_, h3E6⟩)⟩
    show GGHasLabel ⟨.E6, 0, n⟩ (↥L ⧸ Subgroup.center ↥L)
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, -⟩ := hq
      exact ⟨θ⟩) hraw
  · subst hT6
    have hl : l = 0 := hlab.2
    subst hl
    obtain ⟨R, hRgrp, hRfin, I, F, hq⟩ := mkr_twE6_witness hcomb
    letI := hRgrp
    letI := hRfin
    obtain ⟨⟨-, -, θ, hP⟩, hrowfact⟩ := hq
    obtain ⟨-, hBsN, hI⟩ := hP
    obtain ⟨hp, hi, hc⟩ := mkr_rest hperf θ hBsN hrowfact.1 hrowfact.2 hI
    refine ⟨hp, hi, hc, n, hn, Or.inr (Or.inr ⟨?_, h3T6⟩)⟩
    show GGHasLabel ⟨.twE6, 0, n⟩ (↥L ⧸ Subgroup.center ↥L)
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, -⟩ := hq
      exact ⟨θ⟩) hraw

end CFSG.StandardType

end
