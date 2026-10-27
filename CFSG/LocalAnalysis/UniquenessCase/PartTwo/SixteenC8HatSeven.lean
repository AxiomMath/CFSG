module

import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofGL
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.Quasithin.Background.A1cSL2Facts
import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix
open scoped MatrixGroups commutatorElement

private lemma c8h_five_le_of_prime_gt_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  rw [not_le] at h
  have hp4 : p = 4 := by omega
  subst hp4
  norm_num at hp

private lemma c8h_perfect_image {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1) (ψ : Γ →* GL (Fin 2) (ZMod p))
    (hker : ψ.ker ≤ CFSG.pPrimeCore 3 Γ) :
    ∃ E : Subgroup Γ, Group.IsPerfect E ∧
      E.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)) = ⊤ ∧
      Nonempty (↥(E.map ψ) ≃* SL(2, ZMod p)) ∧ p * (p ^ 2 - 1) = 2 * 168 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set I := CFSG.pPrimeCore 3 Γ with hI
  obtain ⟨hsimple, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hl3
  haveI : IsSimpleGroup (Γ ⧸ I) := hsimple
  have hperfT : Group.IsPerfect (Γ ⧸ I) := by
    refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative ?_
    intro hc
    have hp' : (Nat.card (Γ ⧸ I)).Prime := Group.is_simple_iff_prime_card.mp hsimple
    rw [hcard] at hp'
    norm_num at hp'
  obtain ⟨-, -, hJperf, -⟩ := CFSG.perfect_residual_characterization (G := Γ)
  set J := CFSG.perfectResidual Γ with hJ
  have hψJ : J.map (QuotientGroup.mk' I) = ⊤ :=
    CFSG.RankThree.PartTwo.Sec13.Res7Proof.map_perfectResidual_eq_top
      (QuotientGroup.mk' I) (QuotientGroup.mk'_surjective I)
  set R := J.map ψ with hR
  have hRperf : Group.IsPerfect R := by
    rw [hR]
    exact Group.IsPerfect.map ψ
  haveI : Group.IsPerfect R := hRperf
  set f : J →* R := ψ.subgroupMap J with hf
  have hfs : Function.Surjective f := ψ.subgroupMap_surjective J
  set g : J →* Γ ⧸ I := (QuotientGroup.mk' I).comp J.subtype with hg
  have hfg : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : ψ (x : Γ) = 1 := by
      have h := congrArg (fun r : R => (r : GL (Fin 2) (ZMod p))) hx
      exact h
    exact (QuotientGroup.eq_one_iff (x : Γ)).mpr (hker hx')
  set ψR : R →* Γ ⧸ I := f.liftOfRightInverse (Function.surjInv hfs)
    (Function.rightInverse_surjInv hfs) ⟨g, hfg⟩ with hψR
  have hψRf : ∀ x : J, ψR (f x) = g x := fun x =>
    f.liftOfRightInverse_comp_apply (Function.surjInv hfs) (Function.rightInverse_surjInv hfs)
      ⟨g, hfg⟩ x
  have hψRs : Function.Surjective ψR := by
    intro t
    have ht : t ∈ J.map (QuotientGroup.mk' I) := hψJ ▸ Subgroup.mem_top t
    obtain ⟨y, hy, rfl⟩ := ht
    exact ⟨f ⟨y, hy⟩, by rw [hψRf]; rfl⟩
  have hRbot : R ≠ ⊥ := by
    intro hbot
    obtain ⟨t, ht⟩ := exists_ne (1 : Γ ⧸ I)
    obtain ⟨r, rfl⟩ := hψRs t
    apply ht
    have hr : r = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall R).mp hbot r r.2)
    rw [hr, map_one]
  rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv (by omega : p ≠ 2) R hRbot with
    he | he
  · obtain ⟨e⟩ := he
    have hφ : Function.Surjective (ψR.comp e.symm.toMonoidHom) :=
      hψRs.comp e.symm.surjective
    rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.card_eq_of_surj_SL2
      (c8h_five_le_of_prime_gt_three hp hp3) _ hφ with h | h
    · exfalso
      rw [hcard] at h
      have hp8 : p ≤ 8 := by
        by_contra hlt
        rw [not_le] at hlt
        have hge : 9 * (9 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
          Nat.mul_le_mul (by omega : 9 ≤ p)
            (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega : 9 ≤ p) 2) 1)
        omega
      interval_cases p <;> first | rfl | (norm_num at h)
    · rw [hcard] at h
      exact ⟨J, hJperf, hψJ, ⟨e⟩, h⟩
  · obtain ⟨e⟩ := he
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hφ : Function.Surjective (ψR.comp e.symm.toMonoidHom) :=
      hψRs.comp e.symm.surjective
    rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.card_eq_of_surj_SL2 le_rfl _ hφ with h | h
    · exfalso; rw [hcard] at h; norm_num at h
    · exfalso; rw [hcard] at h; norm_num at h

theorem c8h_p_eq_seven {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1) (ψ : Γ →* GL (Fin 2) (ZMod p))
    (hker : ψ.ker ≤ CFSG.pPrimeCore 3 Γ) : p = 7 := by
  obtain ⟨-, -, -, -, hcard⟩ := c8h_perfect_image hp hp3 hl3 ψ hker
  have hp8 : p ≤ 8 := by
    by_contra hlt
    rw [not_le] at hlt
    have hge : 9 * (9 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul (by omega : 9 ≤ p)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega : 9 ≤ p) 2) 1)
    omega
  interval_cases p <;> first | rfl | (norm_num at hcard)

theorem c8h_sl2_of_gl2 {Γ : Type} [Group Γ] [Finite Γ]
    (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1) (ψ : Γ →* GL (Fin 2) (ZMod 7))
    (hker : ψ.ker ≤ CFSG.pPrimeCore 3 Γ) :
    ∃ ρ : Γ →* ↥(StatedSL 2 (ZMod 7)), Function.Surjective ρ ∧
      ∀ γ : Γ, ((ρ γ : ↥(StatedSL 2 (ZMod 7))) : GL (Fin 2) (ZMod 7)) = ψ γ := by
  classical
  obtain ⟨E, hEperf, hEmap, he, -⟩ :=
    c8h_perfect_image (by norm_num : Nat.Prime 7) (by norm_num : 3 < 7) hl3 ψ hker
  haveI : Group.IsPerfect E := hEperf
  set I := CFSG.pPrimeCore 3 Γ with hI
  set R := E.map ψ with hR
  have hRperf : Group.IsPerfect R := by
    rw [hR]
    exact Group.IsPerfect.map ψ
  haveI : Group.IsPerfect R := hRperf
  have hle : R ≤ StatedSL 2 (ZMod 7) := by
    intro g hg
    exact CFSG.Open.StatedAPI.mem_statedSL_of_det
      (CFSG.SectionRank.Ccomm.det_eq_one_of_perfect R hg)
  have hRS : R = StatedSL 2 (ZMod 7) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [CFSG.Open.StatedAPI.card_statedSL (2 : ℕ) (ZMod 7)]
    exact le_of_eq (Nat.card_congr he.some.toEquiv).symm
  haveI : Group.IsPerfect ↥(StatedSL 2 (ZMod 7)) := by
    rw [← hRS]
    exact hRperf
  have hIn : I.Normal := by
    rw [hI]
    exact CFSG.pPrimeCore_normal
  set M := I.map ψ with hM
  have hMcard : Nat.card M ∣ Nat.card I := by
    rw [hM]
    exact Subgroup.card_map_dvd I ψ
  have hIcop : Nat.Coprime 3 (Nat.card I) := by
    rw [hI]
    exact CFSG.pPrimeCore_coprime_card
  have hMcop : Nat.Coprime 3 (Nat.card M) := hIcop.coprime_dvd_right hMcard
  have h3n : ¬ 3 ∣ Nat.card M := by
    intro h3
    have hg : 3 ∣ Nat.gcd 3 (Nat.card M) := Nat.dvd_gcd dvd_rfl h3
    rw [hMcop.gcd_eq_one] at hg
    norm_num at hg
  have hdvd : Nat.gcd 6 (Nat.card M) ∣ 2 := by
    have hcopd3 : Nat.Coprime (Nat.gcd 6 (Nat.card M)) 3 := by
      rw [Nat.coprime_comm]
      exact (Nat.prime_three.coprime_iff_not_dvd).2
        (fun h3 => h3n (h3.trans (Nat.gcd_dvd_right 6 (Nat.card M))))
    refine hcopd3.dvd_of_dvd_mul_left ?_
    have h6 : Nat.gcd 6 (Nat.card M) ∣ 6 := Nat.gcd_dvd_left 6 (Nat.card M)
    simpa [show (3 : ℕ) * 2 = 6 by norm_num] using h6
  have hMn : ∀ s : GL (Fin 2) (ZMod 7), s ∈ ψ.range → ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro s hs m hm
    obtain ⟨γ, rfl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hm
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem ψ (hIn.conj_mem i hi γ)
  have hStSL_le_range : StatedSL 2 (ZMod 7) ≤ ψ.range := by
    rw [← hRS]
    exact Subgroup.map_le_range (f := ψ) E
  set N := M ⊓ StatedSL 2 (ZMod 7) with hN
  have hNs : (StatedSL 2 (ZMod 7)).Normal := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
    infer_instance
  have hcommM : ∀ m ∈ M, ∀ s ∈ StatedSL 2 (ZMod 7), m * s * m⁻¹ * s⁻¹ ∈ M := by
    intro m hm s hs
    have h1 : s * m⁻¹ * s⁻¹ ∈ M := hMn s (hStSL_le_range hs) m⁻¹ (M.inv_mem hm)
    rw [show m * s * m⁻¹ * s⁻¹ = m * (s * m⁻¹ * s⁻¹) by group]
    exact M.mul_mem hm h1
  have hcommSL : ∀ m ∈ M, ∀ s ∈ StatedSL 2 (ZMod 7),
      m * s * m⁻¹ * s⁻¹ ∈ StatedSL 2 (ZMod 7) := by
    intro m hm s hs
    have h1 : m * s * m⁻¹ ∈ StatedSL 2 (ZMod 7) := hNs.conj_mem s hs m
    exact (StatedSL 2 (ZMod 7)).mul_mem h1 ((StatedSL 2 (ZMod 7)).inv_mem hs)
  have hNnorm : ∀ s ∈ StatedSL 2 (ZMod 7), ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    obtain ⟨hnM, hnS⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨hMn s (hStSL_le_range hs) n hnM, hNs.conj_mem n hnS s⟩
  set N' : Subgroup (SL(2, ZMod 7)) := N.comap SpecialLinearGroup.toGL with hN'
  have hN'normal : N'.Normal := by
    refine ⟨fun n hn s => ?_⟩
    rw [hN'] at hn ⊢
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_inv, map_mul]
    exact hNnorm (SpecialLinearGroup.toGL s) (by
      rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      exact ⟨s, rfl⟩) (SpecialLinearGroup.toGL n) hn
  haveI : N'.Normal := hN'normal
  have hN'cases := CFSG.Quasithin.A1c.normal_le_center_or_eq_top (p := 7) (by norm_num) N'
  have hcentN : ∀ n ∈ N, ∀ s ∈ StatedSL 2 (ZMod 7), n * s = s * n := by
    rcases hN'cases with hcenter | htop
    · intro n hn s hs
      obtain ⟨hnM, hnS⟩ := Subgroup.mem_inf.mp hn
      have hnSrange : n ∈ (SpecialLinearGroup.toGL :
          SL(2, ZMod 7) →* GL (Fin 2) (ZMod 7)).range := by
        rwa [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      obtain ⟨s0, hs0⟩ := hnSrange
      have hs0mem : s0 ∈ N' := by
        rw [Subgroup.mem_comap]
        rwa [hs0]
      have hc := hcenter hs0mem
      have hsrange : s ∈ (SpecialLinearGroup.toGL :
          SL(2, ZMod 7) →* GL (Fin 2) (ZMod 7)).range := by
        rwa [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      obtain ⟨s1, hs1⟩ := hsrange
      rw [← hs0, ← hs1, ← map_mul, ← map_mul]
      exact (congrArg SpecialLinearGroup.toGL (Subgroup.mem_center_iff.mp hc s1)).symm
    · exfalso
      have hle' : StatedSL 2 (ZMod 7) ≤ M := by
        intro s hs
        have hsrange : s ∈ (SpecialLinearGroup.toGL :
            SL(2, ZMod 7) →* GL (Fin 2) (ZMod 7)).range := by
          rwa [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
        obtain ⟨t, rfl⟩ := hsrange
        have ht : t ∈ N' := htop ▸ Subgroup.mem_top t
        exact (Subgroup.mem_comap.mp ht).1
      have hdvd' : Nat.card (StatedSL 2 (ZMod 7)) ∣ Nat.card M := Subgroup.card_dvd_of_le hle'
      have h336 : Nat.card (StatedSL 2 (ZMod 7)) = 336 := by
        rw [CFSG.Open.StatedAPI.card_statedSL_two (ZMod 7), Nat.card_zmod]
        norm_num
      have h3dvd : 3 ∣ Nat.card M := by
        have h' : 3 ∣ Nat.card (StatedSL 2 (ZMod 7)) := by rw [h336]; norm_num
        exact h'.trans hdvd'
      have hg : 3 ∣ Nat.gcd 3 (Nat.card M) := Nat.dvd_gcd dvd_rfl h3dvd
      rw [hMcop.gcd_eq_one] at hg
      norm_num at hg
  have hNH : ⁅N, StatedSL 2 (ZMod 7)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro n hn s hs
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcentN n hn s hs
  have hMH : ⁅M, StatedSL 2 (ZMod 7)⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro m hm s hs
    rw [commutatorElement_def]
    exact Subgroup.mem_inf.mpr ⟨hcommM m hm s hs, hcommSL m hm s hs⟩
  have hN1 : ⁅⁅M, StatedSL 2 (ZMod 7)⁆, StatedSL 2 (ZMod 7)⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono hMH le_rfl).trans (le_of_eq hNH)
  have hN2 : ⁅⁅StatedSL 2 (ZMod 7), M⁆, StatedSL 2 (ZMod 7)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (StatedSL 2 (ZMod 7)) M]
    exact hN1
  have hHM : ⁅⁅StatedSL 2 (ZMod 7), StatedSL 2 (ZMod 7)⁆, M⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := StatedSL 2 (ZMod 7)) (H₂ := StatedSL 2 (ZMod 7)) (H₃ := M) hN2 hN1
  have hHH : ⁅StatedSL 2 (ZMod 7), StatedSL 2 (ZMod 7)⁆ = StatedSL 2 (ZMod 7) :=
    Subgroup.commutator_eq_self (H := StatedSL 2 (ZMod 7))
  have hHM' : ⁅StatedSL 2 (ZMod 7), M⁆ = ⊥ := by
    rw [hHH] at hHM
    exact hHM
  have hcentM : ∀ m ∈ M, ∀ h ∈ StatedSL 2 (ZMod 7), m * h = h * m := by
    intro m hm h hh
    have hc : ⁅h, m⁆ = 1 := by
      have hmem : ⁅h, m⁆ ∈ ⁅StatedSL 2 (ZMod 7), M⁆ :=
        Subgroup.commutator_mem_commutator hh hm
      rwa [hHM', Subgroup.mem_bot] at hmem
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm
  have hscalar : ∀ m ∈ M, ∃ c : ZMod 7,
      (m : Matrix (Fin 2) (Fin 2) (ZMod 7)) = Matrix.scalar (Fin 2) c := by
    intro m hm
    refine CFSG.ClassicalInvolution.Generic.exists_scalar_of_comm_sl2 _ ?_
    intro s
    have hc := hcentM m hm (SpecialLinearGroup.toGL s) (by
      rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
      exact ⟨s, rfl⟩)
    have hc' := congrArg (fun g : GL (Fin 2) (ZMod 7) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod 7))) hc
    simpa using hc'
  have hdetI : ∀ i ∈ I,
      ((ψ i : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 1 := by
    intro i hi
    have hm : ψ i ∈ M := by
      rw [hM]
      exact Subgroup.mem_map_of_mem ψ hi
    obtain ⟨c, hc⟩ := hscalar (ψ i) hm
    have h1 : (ψ i : GL (Fin 2) (ZMod 7)) ^ Nat.card M = 1 := by
      have h0 : (⟨ψ i, hm⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have h1' := congrArg (Subgroup.subtype M) h0
      rw [map_pow, map_one] at h1'
      exact h1'
    have h3 : ((ψ i : GL (Fin 2) (ZMod 7)) :
        Matrix (Fin 2) (Fin 2) (ZMod 7)) ^ Nat.card M = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h2 : (Matrix.scalar (Fin 2) c) ^ Nat.card M = 1 := by
      rw [hc] at h3
      exact h3
    have hc0 : c ≠ 0 := by
      intro hc0
      have hdet0 : ((ψ i : GL (Fin 2) (ZMod 7)).val).det = 0 := by
        change ((ψ i : Matrix (Fin 2) (Fin 2) (ZMod 7))).det = 0
        rw [hc]
        simp [hc0]
      exact Matrix.GeneralLinearGroup.det_ne_zero (ψ i) hdet0
    have hc6 : c ^ 6 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one (p := 7) hc0
    have hpow : c ^ Nat.card M = 1 := by
      have h2' : Matrix.scalar (Fin 2) (c ^ Nat.card M) = 1 := by
        rw [map_pow]
        exact h2
      exact Matrix.scalar_inj.mp (by rw [h2', map_one])
    have hgcd : c ^ Nat.gcd 6 (Nat.card M) = 1 := pow_gcd_eq_one.mpr ⟨hc6, hpow⟩
    have hc2 : c ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, hgcd, one_pow]
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, ← pow_two, hc2]
  have hdecomp : ∀ γ : Γ, ∃ e ∈ E, ∃ i ∈ I, γ = e * i := by
    intro γ
    have h : (QuotientGroup.mk' I) γ ∈ E.map (QuotientGroup.mk' I) := by
      rw [hEmap]
      exact Subgroup.mem_top _
    obtain ⟨e, he, heq⟩ := h
    refine ⟨e, he, e⁻¹ * γ, ?_, ?_⟩
    · have h1 : (QuotientGroup.mk' I) (e⁻¹ * γ) = 1 := by
        rw [map_mul, map_inv, heq, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    · group
  have hmem : ∀ γ : Γ, ψ γ ∈ StatedSL 2 (ZMod 7) := by
    intro γ
    obtain ⟨e, he, i, hi, rfl⟩ := hdecomp γ
    rw [map_mul]
    refine (StatedSL 2 (ZMod 7)).mul_mem ?_ ?_
    · have hmemE : ψ e ∈ E.map ψ := Subgroup.mem_map_of_mem ψ he
      have hmemR : ψ e ∈ R := by rw [hR]; exact hmemE
      rwa [← hRS]
    · exact CFSG.Open.StatedAPI.mem_statedSL_of_det (hdetI i hi)
  refine ⟨ψ.codRestrict (StatedSL 2 (ZMod 7)) hmem, ?_, fun γ => rfl⟩
  intro s
  have hsS : (s : GL (Fin 2) (ZMod 7)) ∈ R := by rw [hRS]; exact s.2
  have hsE : (s : GL (Fin 2) (ZMod 7)) ∈ E.map ψ := by rwa [hR] at hsS
  obtain ⟨e, he, heq⟩ := hsE
  refine ⟨e, ?_⟩
  apply Subtype.ext
  exact heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
