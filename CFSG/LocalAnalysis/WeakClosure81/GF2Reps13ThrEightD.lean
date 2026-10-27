module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightDG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_eq_inv_of_surjective_mul_inv {G : Type*} [Group G]
    (τ : G →* G) (hτ : ∀ x : G, τ (τ x) = x)
    (hsurj : Function.Surjective (fun x : G => τ x * x⁻¹)) :
    ∀ x : G, τ x = x⁻¹ := by
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  change τ y * y⁻¹ = x at hy
  calc τ x = τ (τ y * y⁻¹) := by rw [hy]
    _ = τ (τ y) * τ (y⁻¹) := by rw [map_mul]
    _ = y * (τ y)⁻¹ := by rw [hτ y, map_inv]
    _ = (τ y * y⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [hy]

theorem s13_eight_N_comm_t (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N) : ⁅N, Subgroup.zpowers t⁆ ≠ ⊥ := by
  classical
  intro hbot
  obtain ⟨hPle, hPgrp, hPne, htP, hcomm, hOP⟩ := s13_P_facts (p := 3) h
  set P : Subgroup (MulAut W) := ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ with hPdef
  have htP' : ∀ x ∈ P, t * x * t⁻¹ ∈ P := by
    intro x hx
    rw [hPdef] at hx ⊢
    exact htP x hx
  have hcomm' : ⁅P, Subgroup.zpowers t⁆ = P := by rw [hPdef]; exact hcomm
  have hNP' : N ≤ P := by rw [hPdef]; exact hD.hNP
  haveI hPinst : CFSG.IsExtraspecial 3 ↥P := hD.hP.1
  have htt : t * t = 1 := by
    have h2 := h.ht2
    rwa [pow_two] at h2
  let τ : ↥P →* ↥P :=
    { toFun := fun x => ⟨t * (x : MulAut W) * t⁻¹, htP' x x.2⟩
      map_one' := by
        apply Subtype.ext
        show t * (1 : MulAut W) * t⁻¹ = 1
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show t * ((x * y : ↥P) : MulAut W) * t⁻¹ =
          (t * (x : MulAut W) * t⁻¹) * (t * (y : MulAut W) * t⁻¹)
        rw [Subgroup.coe_mul]
        group }
  have hττ : ∀ x : ↥P, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show t * (t * (x : MulAut W) * t⁻¹) * t⁻¹ = (x : MulAut W)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    calc t * (t * (x : MulAut W) * t⁻¹) * t⁻¹
        = (t * t) * (x : MulAut W) * (t⁻¹ * t⁻¹) := by group
      _ = (x : MulAut W) := by rw [htt, htinv, htt]; group
  haveI : IsElementaryAbelian 3 (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥P
  haveI : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    IsMulCommutative.of_comm fun a b => IsMulCommutative.is_comm.comm a b
  have hτsurj : Function.Surjective τ := fun y => ⟨τ y, hττ y⟩
  have hCmap : Subgroup.center ↥P ≤ (Subgroup.center ↥P).comap τ :=
    (Subgroup.map_le_iff_le_comap).mp
      (Subgroup.map_center_le_center (f := τ) hτsurj)
  let τbar : (↥P ⧸ Subgroup.center ↥P) →* (↥P ⧸ Subgroup.center ↥P) :=
    QuotientGroup.map (Subgroup.center ↥P) (Subgroup.center ↥P) τ hCmap
  have hmk : ∀ x : ↥P,
      τbar (QuotientGroup.mk' (Subgroup.center ↥P) x) =
        QuotientGroup.mk' (Subgroup.center ↥P) (τ x) :=
    fun x => QuotientGroup.map_mk' (Subgroup.center ↥P) (Subgroup.center ↥P) τ hCmap x
  have hτbarτbar : ∀ a : ↥P ⧸ Subgroup.center ↥P, τbar (τbar a) = a := by
    intro a
    refine QuotientGroup.induction_on a fun x => ?_
    change τbar (τbar (QuotientGroup.mk' (Subgroup.center ↥P) x)) =
      QuotientGroup.mk' (Subgroup.center ↥P) x
    rw [hmk x, hmk (τ x), hττ x]
  let SW : Set (MulAut W) := {c | ∃ p ∈ P, t * p * t⁻¹ * p⁻¹ = c}
  have hSWle : SW ⊆ (P : Set (MulAut W)) := by
    rintro c ⟨p, hp, rfl⟩
    exact P.mul_mem (htP' p hp) (P.inv_mem hp)
  have hgenW : Subgroup.closure SW = P := by
    apply le_antisymm
    · rw [Subgroup.closure_le]; exact hSWle
    · rw [← hcomm', Subgroup.commutator_def, Subgroup.closure_le]
      rintro c ⟨p, hp, s, hs, rfl⟩
      have hs' : s = 1 ∨ s = t := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
        have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact htt
        have hmod := zpow_eq_zpow_emod k h2
        rcases Int.emod_two_eq_zero_or_one k with hk | hk
        · left; rw [hmod, hk, zpow_zero]
        · right; rw [hmod, hk, zpow_one]
      rcases hs' with h1 | h1
      · rw [h1]; simp
      · rw [h1]
        have h2 : ⁅p, t⁆ = (t * p * t⁻¹ * p⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p, hp, rfl⟩)
  let S : Set ↥P := {c | (c : MulAut W) ∈ SW}
  have hS_eq : S = {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c} := by
    ext c; constructor
    · intro hc
      obtain ⟨p, hp, hpv⟩ := hc
      refine ⟨⟨p, hp⟩, ?_⟩
      apply Subtype.ext
      show ((τ ⟨p, hp⟩ * ⟨p, hp⟩⁻¹ : ↥P) : MulAut W) = (c : MulAut W)
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      show t * p * t⁻¹ * p⁻¹ = (c : MulAut W)
      rw [← hpv]
    · rintro ⟨p, rfl⟩
      refine ⟨(p : MulAut W), p.2, ?_⟩
      show t * (p : MulAut W) * t⁻¹ * (p : MulAut W)⁻¹ =
        ((τ p * p⁻¹ : ↥P) : MulAut W)
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
  have hQmap : (Subgroup.closure S).map P.subtype = P := by
    apply le_antisymm
    · exact (Subgroup.map_le_iff_le_comap).mpr fun x _ => x.2
    · have hsub : Subgroup.closure SW ≤ (Subgroup.closure S).map P.subtype := by
        rw [Subgroup.closure_le]
        rintro c ⟨p, hp, hc⟩
        refine Subgroup.mem_map.mpr ⟨⟨c, hSWle ⟨p, hp, hc⟩⟩, ?_, rfl⟩
        exact Subgroup.subset_closure ⟨p, hp, hc⟩
      rwa [hgenW] at hsub
  have hQtop : Subgroup.closure S = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hQmap, Subgroup.map_top, Subgroup.range_subtype]
  have hS'top : Subgroup.closure {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c} = ⊤ := by
    rw [← hS_eq, hQtop]
  let ψ : (↥P ⧸ Subgroup.center ↥P) →* (↥P ⧸ Subgroup.center ↥P) :=
    { toFun := fun a => τbar a * a⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        show τbar (a * b) * (a * b)⁻¹ = (τbar a * a⁻¹) * (τbar b * b⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hImg : QuotientGroup.mk' (Subgroup.center ↥P) ''
      {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c} ⊆ ψ.range := by
    rintro _ ⟨c, ⟨p, rfl⟩, rfl⟩
    refine ⟨QuotientGroup.mk' (Subgroup.center ↥P) p, ?_⟩
    show τbar (QuotientGroup.mk' (Subgroup.center ↥P) p) *
        (QuotientGroup.mk' (Subgroup.center ↥P) p)⁻¹ =
      QuotientGroup.mk' (Subgroup.center ↥P) (τ p * p⁻¹)
    rw [hmk p, ← map_inv, map_mul]
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥P) a
    have hle : Subgroup.closure {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c} ≤
        (Subgroup.closure (QuotientGroup.mk' (Subgroup.center ↥P) ''
          {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c})).comap
          (QuotientGroup.mk' (Subgroup.center ↥P)) := by
      rw [Subgroup.closure_le]
      rintro c ⟨p, hp⟩
      exact Subgroup.subset_closure ⟨c, ⟨p, hp⟩, rfl⟩
    have hx : x ∈ Subgroup.closure {c : ↥P | ∃ p : ↥P, τ p * p⁻¹ = c} := by
      rw [hS'top]; trivial
    exact (Subgroup.closure_le ψ.range).mpr hImg (hle hx)
  have hτinv : ∀ a : ↥P ⧸ Subgroup.center ↥P, τbar a = a⁻¹ :=
    w16g_eq_inv_of_surjective_mul_inv τbar hτbarτbar hsurj
  have hcent : N ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hNcard : Nat.card ↥N = 9 := by
    have hh := w16g_card_of_isElemAbelianOfRank hD.hN
    norm_num at hh
    exact hh
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hD.hz3]
  have hNneZ : ∃ n ∈ N, n ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    let f : ↥N → ↥(Subgroup.zpowers z) :=
      fun n => ⟨(n : MulAut W), hcon (n : MulAut W) n.2⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : ↥(Subgroup.zpowers z) => (x : MulAut W)) hab
    have hle := Nat.card_le_card_of_injective f hfinj
    rw [hNcard, hzcard] at hle
    omega
  obtain ⟨n, hnN, hnZ⟩ := hNneZ
  have hnP : n ∈ P := hNP' hnN
  let nP : ↥P := ⟨n, hnP⟩
  have htn : t * n = n * t :=
    (Subgroup.mem_centralizer_iff.mp (hcent hnN)) t (Subgroup.mem_zpowers t)
  have hfixn : τ nP = nP := by
    apply Subtype.ext
    show t * n * t⁻¹ = n
    rw [htn]
    group
  have hbarfix : τbar (QuotientGroup.mk' (Subgroup.center ↥P) nP) =
      QuotientGroup.mk' (Subgroup.center ↥P) nP := by
    rw [hmk nP, hfixn]
  have hxeq : QuotientGroup.mk' (Subgroup.center ↥P) nP =
      (QuotientGroup.mk' (Subgroup.center ↥P) nP)⁻¹ :=
    hbarfix.symm.trans (hτinv (QuotientGroup.mk' (Subgroup.center ↥P) nP))
  have hx2 : (QuotientGroup.mk' (Subgroup.center ↥P) nP) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxeq]
    rw [mul_inv_cancel]
  have hx3 : (QuotientGroup.mk' (Subgroup.center ↥P) nP) ^ 3 = 1 := by
    rw [← map_pow (QuotientGroup.mk' (Subgroup.center ↥P)) nP 3, hD.hP.2.2 nP, map_one]
  have hx1 : QuotientGroup.mk' (Subgroup.center ↥P) nP = 1 := by
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥P) nP) ^ 3 =
        QuotientGroup.mk' (Subgroup.center ↥P) nP := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hx2, one_mul]
    rw [← h1, hx3]
  have hnC : nP ∈ Subgroup.center ↥P :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center ↥P) nP).mp hx1
  have hnZp : n ∈ Subgroup.zpowers z := by
    apply hD.hZP n hnP
    intro y hy
    have h1 := Subgroup.mem_center_iff.mp hnC ⟨y, hy⟩
    simpa using congrArg Subtype.val h1
  exact hnZ hnZp

theorem s13_eight_components (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N) :
    ∃ Δ : Fin 3 → Subgroup W,
      Function.Injective Δ ∧ iSupIndep Δ ∧ (⨆ i, Δ i) = commSub ⊤ N ∧ (∀ i, rk ↥(Δ i) = 2) ∧
      (∀ i, IsIrrOn N (Δ i) ⊥ ∧ IsEntireIsotypic N (Δ i)) ∧
      (∃ a ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, ∀ i, (Δ i).map a.toMonoidHom = Δ (i + 1)) ∧
      ∃ i₀, (Δ i₀).map t.toMonoidHom = Δ i₀ ∧ (Δ (i₀ + 1)).map t.toMonoidHom = Δ (i₀ + 2) ∧
        (Δ (i₀ + 2)).map t.toMonoidHom = Δ (i₀ + 1) := by
  classical
  obtain ⟨k, a, hG⟩ := s13_eight_generators h hD (s13_eight_N_comm_t h hD)
  obtain ⟨hidep, hsum, hrk⟩ := s13_eight_decomp h hD hG
  refine ⟨fun i : Fin 3 => s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ))),
    ?_, hidep, hsum, hrk, ?_, ?_, ?_⟩
  · refine hidep.injective (fun i hi => ?_)
    have h2 := hrk i
    rw [hi, rk_bot] at h2
    omega
  · intro i
    exact ⟨s13_eight_comp_irr h hD hG i, s13_eight_comp_isotypic h hD hG i⟩
  · exact ⟨a, hG.haP, fun i => s13_eight_comp_map_a hD hG i⟩
  · refine ⟨0, ?_, ?_, ?_⟩
    · have hn0 : (-0 : Fin 3) = 0 := by decide
      simpa [hn0] using s13_eight_comp_map_t hD hG 0
    · have h01 : (0 + 1 : Fin 3) = 1 := by decide
      have h02 : (0 + 2 : Fin 3) = 2 := by decide
      have hn1 : (-1 : Fin 3) = 2 := by decide
      simpa [h01, h02, hn1] using s13_eight_comp_map_t hD hG 1
    · have h01 : (0 + 1 : Fin 3) = 1 := by decide
      have h02 : (0 + 2 : Fin 3) = 2 := by decide
      have hn2 : (-2 : Fin 3) = 1 := by decide
      simpa [h01, h02, hn2] using s13_eight_comp_map_t hD hG 2

end CFSG.LocalAnalysis.WeakClosure81
