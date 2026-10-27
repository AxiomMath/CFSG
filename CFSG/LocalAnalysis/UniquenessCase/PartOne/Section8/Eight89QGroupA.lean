module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

open scoped commutatorElement

private def k89qa_frattiniOf {G : Type*} [Group G] (D : Subgroup G) : Subgroup G :=
  (frattini D).map D.subtype

private lemma k89qa_frattiniOf_le {G : Type*} [Group G] (D : Subgroup G) :
    k89qa_frattiniOf D ≤ D :=
  Subgroup.map_subtype_le _

private lemma k89qa_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] {M : Subgroup G} {C : Subgroup M} (hC : C.Characteristic) :
    Subgroup.normalizer (M : Set G) ≤
      Subgroup.normalizer ((C.map M.subtype : Subgroup G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let α := Subgroup.normalizerMonoidHom M ⟨d, hd⟩
  have hfix : C.map α.toMonoidHom = C := (Subgroup.characteristic_iff_map_eq.mp hC) α
  have hcomp : M.subtype.comp α.toMonoidHom = (MulAut.conj d).toMonoidHom.comp M.subtype := by
    ext m
    exact Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨d, hd⟩ m
  calc (C.map M.subtype).map (MulAut.conj d).toMonoidHom
      = C.map ((MulAut.conj d).toMonoidHom.comp M.subtype) := by rw [Subgroup.map_map]
    _ = C.map (M.subtype.comp α.toMonoidHom) := by rw [hcomp]
    _ = (C.map α.toMonoidHom).map M.subtype := by rw [Subgroup.map_map]
    _ = C.map M.subtype := by rw [hfix]

private lemma k89qa_le_normalizer_of_conj_mem {G : Type*} [Group G] {A N : Subgroup G}
    (h : ∀ d ∈ A, ∀ x ∈ N, d * x * d⁻¹ ∈ N) :
    A ≤ Subgroup.normalizer (N : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h d hd x hx, fun hx => by
    have := h d⁻¹ (A.inv_mem hd) (d * x * d⁻¹) hx
    simpa [mul_assoc] using this⟩

theorem s889_qmin : S889QMin := by
  intro G _ _ q hq hq2 A D₀ hD0 hAq hAD0 hcomm0
  have : Fact q.Prime := ⟨hq⟩
  classical
  obtain ⟨D, hPD, hmin⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup.exists_minimal_subgroup
      (fun W : Subgroup G => W ≤ D₀ ∧ A ≤ Subgroup.normalizer (W : Set G) ∧ ⁅W, A⁆ ≠ ⊥)
      ⟨D₀, le_rfl, hAD0, hcomm0⟩
  obtain ⟨hD_le, hAD, hDA_ne⟩ := hPD
  have hDq : IsPGroup q D := hD0.to_le hD_le
  have : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  have hcopA : Nat.Coprime q (Nat.card A) := (hq.coprime_iff_not_dvd).2 hAq
  obtain ⟨n, hn⟩ := hDq.exists_card_eq
  have hcop : (Nat.card A).Coprime (Nat.card D) := by
    rw [hn]
    exact (hcopA.pow_left n).symm
  have hDA_le_D : ⁅D, A⁆ ≤ D := (Subgroup.le_normalizer_iff_commutator_le_left).mp hAD
  have hcommAA : ⁅⁅D, A⁆, A⁆ = ⁅D, A⁆ :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_coprime hAD hcop
  have hDA_eq : ⁅D, A⁆ = D := by
    refine hmin ⁅D, A⁆ ⟨hDA_le_D.trans hD_le, Subgroup.normalizer_commutator_ge_right D A, ?_⟩ hDA_le_D
    rw [hcommAA]
    exact hDA_ne
  have hproper : ∀ W : Subgroup G, W ≤ D → A ≤ Subgroup.normalizer (W : Set G) → W ≠ D →
      ⁅W, A⁆ = ⊥ := by
    intro W hWD hAW hWne
    by_contra hWc
    exact hWne (hmin W ⟨hWD.trans hD_le, hAW, hWc⟩ hWD)
  have hD_ne_bot : D ≠ ⊥ := by
    intro h
    exact hDA_ne (by rw [h]; simp)
  have hΦ_le : k89qa_frattiniOf D ≤ D := k89qa_frattiniOf_le D
  have hΦ_inv : A ≤ Subgroup.normalizer (k89qa_frattiniOf D : Set G) :=
    hAD.trans (k89qa_normalizer_le_normalizer_map_subtype_of_characteristic
      (M := D) (C := frattini ↥D) (inferInstance : (frattini ↥D).Characteristic))
  have hD_le_normalizer_Φ : D ≤ Subgroup.normalizer (k89qa_frattiniOf D : Set G) :=
    Subgroup.le_normalizer.trans (k89qa_normalizer_le_normalizer_map_subtype_of_characteristic
      (M := D) (C := frattini ↥D) (inferInstance : (frattini ↥D).Characteristic))
  have hΦ_lt_D : k89qa_frattiniOf D < D := by
    refine lt_of_le_of_ne hΦ_le ?_
    intro h
    have htop : frattini ↥D = ⊤ := by
      apply Subgroup.map_injective D.subtype_injective
      show (frattini ↥D).map D.subtype = (⊤ : Subgroup ↥D).map D.subtype
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact h
    have hbot : (⊥ : Subgroup ↥D) = ⊤ :=
      frattini_nongenerating (K := (⊥ : Subgroup ↥D)) (by rw [htop, bot_sup_eq])
    have hD_eq_bot : D = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥D) ∈ (⊥ : Subgroup ↥D) := by
        rw [hbot]; exact Subgroup.mem_top _
      simpa using hx'
    exact hD_ne_bot hD_eq_bot
  have hΦA_bot : ⁅k89qa_frattiniOf D, A⁆ = ⊥ :=
    hproper (k89qa_frattiniOf D) hΦ_le hΦ_inv (ne_of_lt hΦ_lt_D)
  have hΦD_le_Φ : ⁅k89qa_frattiniOf D, D⁆ ≤ k89qa_frattiniOf D :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hD_le_normalizer_Φ
  have hDΦ_bot : ⁅D, k89qa_frattiniOf D⁆ = ⊥ := by
    have h1 : ⁅⁅A, k89qa_frattiniOf D⁆, D⁆ = ⊥ := by
      rw [Subgroup.commutator_comm A (k89qa_frattiniOf D), hΦA_bot]
      simp
    have h2 : ⁅⁅k89qa_frattiniOf D, D⁆, A⁆ = ⊥ := by
      have hle : ⁅⁅k89qa_frattiniOf D, D⁆, A⁆ ≤ ⁅k89qa_frattiniOf D, A⁆ :=
        Subgroup.commutator_mono_left hΦD_le_Φ
      rw [hΦA_bot] at hle
      exact le_bot_iff.mp hle
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := D) (H₂ := A)
      (H₃ := k89qa_frattiniOf D) h1 h2
    rwa [hDA_eq] at h3
  have hDD_le_Φ : ⁅D, D⁆ ≤ k89qa_frattiniOf D := by
    have hmap := Subgroup.map_mono (f := D.subtype)
      (CFSG.commutator_le_frattini_of_isPGroup (R := ↥D) (p := q))
    rwa [Subgroup.map_subtype_commutator] at hmap
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).2 hD_ne_bot
  have : Group.IsNilpotent ↥D := IsPGroup.isNilpotent (G := ↥D) (p := q) hDq
  have : Group.IsSolvable ↥D := inferInstance
  have hDD_lt : ⁅D, D⁆ < D := by
    have hlt : _root_.commutator ↥D < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥D)
    have hle : ⁅D, D⁆ ≤ D := by
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.map_subtype_le _
    refine lt_of_le_of_ne hle ?_
    intro heq
    have htop : _root_.commutator ↥D = ⊤ := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact heq
    exact hlt.ne htop
  have hIrred : ∀ W : Subgroup G, k89qa_frattiniOf D ≤ W → W ≤ D →
      A ≤ Subgroup.normalizer (W : Set G) → W = k89qa_frattiniOf D ∨ W = D := by
    intro W hΦW hWD hAW
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hWneΦ, hWneD⟩ := hcon
    have hΦW_lt : k89qa_frattiniOf D < W := lt_of_le_of_ne hΦW (Ne.symm hWneΦ)
    have hW_lt_D : W < D := lt_of_le_of_ne hWD hWneD
    have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ k89qa_frattiniOf D := by
      intro x hx y hy
      exact hDD_le_Φ (Subgroup.commutator_mem_commutator hx hy)
    have hpow : ∀ x ∈ D, x ^ q ∈ k89qa_frattiniOf D := by
      intro x hx
      have hxmem : (⟨x, hx⟩ : ↥D) ^ q ∈ frattini ↥D :=
        CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥D) (p := q) ⟨x, hx⟩
      exact Subgroup.mem_map_of_mem D.subtype hxmem
    have hDQ : ∀ d ∈ A, ∀ x ∈ D, d * x * d⁻¹ ∈ D := by
      intro d hd x hx
      exact (Subgroup.mem_normalizer_iff.mp (hAD hd) x).mp hx
    have hDΦ : ∀ d ∈ A, ∀ x ∈ k89qa_frattiniOf D, d * x * d⁻¹ ∈ k89qa_frattiniOf D := by
      intro d hd x hx
      exact (Subgroup.mem_normalizer_iff.mp (hΦ_inv hd) x).mp hx
    have hDW : ∀ d ∈ A, ∀ x ∈ W, d * x * d⁻¹ ∈ W := by
      intro d hd x hx
      exact (Subgroup.mem_normalizer_iff.mp (hAW hd) x).mp hx
    obtain ⟨N, hΦN, hND, hN_inv, hWN, hWN_inf⟩ :=
      CFSG.GH74.BNPair.exists_invariant_complement_interval (p := q) (X := G)
        (Q := D) (Φ := k89qa_frattiniOf D) (D := A) (T := W)
        hΦ_le hcomm hpow hcopA hDQ hDΦ hΦW hWD hDW
    have hAN : A ≤ Subgroup.normalizer (N : Set G) := k89qa_le_normalizer_of_conj_mem hN_inv
    have hN_ne_D : N ≠ D := by
      intro hND_eq
      have : W ⊓ N = W := by rw [hND_eq, inf_eq_left.mpr hWD]
      rw [hWN_inf] at this
      exact (ne_of_gt hΦW_lt) this.symm
    have hN_lt_D : N < D := lt_of_le_of_ne hND hN_ne_D
    have hWA_bot : ⁅W, A⁆ = ⊥ := hproper W hWD hAW hWneD
    have hNA_bot : ⁅N, A⁆ = ⊥ := hproper N hND hAN hN_ne_D
    have hDA_bot : ⁅D, A⁆ = ⊥ := by
      rw [← hWN]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (sup_le ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hWA_bot)
          ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hNA_bot))
    exact hDA_ne hDA_bot
  have hΦ_central : frattini ↥D ≤ Subgroup.center ↥D := by
    intro f hf
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hfd : ((f : ↥D) : G) ∈ k89qa_frattiniOf D := Subgroup.mem_map_of_mem D.subtype hf
    have hle : D ≤ Subgroup.centralizer (k89qa_frattiniOf D : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hDΦ_bot
    have hcomm_fd : ((f : ↥D) : G) * ((d : ↥D) : G) = ((d : ↥D) : G) * ((f : ↥D) : G) :=
      Subgroup.mem_centralizer_iff.mp (hle d.2) ((f : ↥D) : G) hfd
    exact hcomm_fd.symm
  obtain ⟨-, -, ⟨θ, hθ, hker⟩, -, -, -⟩ :=
    CFSG.SectionRank.Ccomm.central_frattini_odd_power_map (H := ↥D) (p := q) hq2 hDq hΦ_central
  have hOmega_top : omega₁ (G := ↥D) (p := q) = ⊤ := by
    by_contra hΩ
    have hΩ_lt : omega₁ (G := ↥D) (p := q) < ⊤ := lt_of_le_of_ne le_top hΩ
    set ΩG : Subgroup G := (omega₁ (G := ↥D) (p := q)).map D.subtype with hΩG
    have hΩG_le : ΩG ≤ D := by rw [hΩG]; exact Subgroup.map_subtype_le _
    have hΩG_ne : ΩG ≠ D := by
      intro heq
      apply hΩ
      have hmap_eq : (omega₁ (G := ↥D) (p := q)).map D.subtype =
          (⊤ : Subgroup ↥D).map D.subtype := by
        rw [← hΩG, heq, Subgroup.map_top, Subgroup.range_subtype]
      exact Subgroup.map_injective D.subtype_injective hmap_eq
    have hΩG_lt : ΩG < D := lt_of_le_of_ne hΩG_le hΩG_ne
    have hΩG_inv : A ≤ Subgroup.normalizer (ΩG : Set G) := by
      have h := k89qa_normalizer_le_normalizer_map_subtype_of_characteristic (M := D)
        (C := omega₁ (G := ↥D) (p := q)) (CFSG.omega₁_characteristic ↥D)
      rw [hΩG]
      exact hAD.trans h
    have hΩG_A : ⁅ΩG, A⁆ = ⊥ := hproper ΩG hΩG_le hΩG_inv (ne_of_lt hΩG_lt)
    have hDA_bot : ⁅D, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haD : a ∈ Subgroup.normalizer (D : Set G) := hAD ha
      have hα1 : Subgroup.normalizerMonoidHom D ⟨a, haD⟩ = 1 := by
        refine CFSG.SectionRank.Ccomm.central_frattini_odd_aut_detection hq2 hDq hΦ_central
          (Subgroup.normalizerMonoidHom D ⟨a, haD⟩) ?_ ?_
        · have hdvd1 : orderOf (Subgroup.normalizerMonoidHom D ⟨a, haD⟩) ∣ orderOf a := by
            have h := orderOf_map_dvd (Subgroup.normalizerMonoidHom D)
              (⟨a, haD⟩ : Subgroup.normalizer (D : Set G))
            rwa [Subgroup.orderOf_mk] at h
          have hdvd : orderOf (Subgroup.normalizerMonoidHom D ⟨a, haD⟩) ∣ Nat.card A :=
            hdvd1.trans (Subgroup.orderOf_dvd_natCard A ha)
          exact (hcopA.coprime_dvd_right hdvd).symm
        · intro y hy
          apply Subtype.ext
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          have hyΩG : (y : G) ∈ ΩG := Subgroup.mem_map_of_mem D.subtype hy
          have hcomm1 : ⁅(y : G), a⁆ = 1 := by
            have : ⁅(y : G), a⁆ ∈ ⁅ΩG, A⁆ := Subgroup.commutator_mem_commutator hyΩG ha
            rw [hΩG_A] at this
            simpa using this
          have hya : (y : G) * a = a * (y : G) :=
            (commutatorElement_eq_one_iff_mul_comm).mp hcomm1
          rw [← hya, mul_assoc, mul_inv_cancel, mul_one]
      have hcent : a * x * a⁻¹ = x := by
        have h := congrArg (fun f : MulAut ↥D => f ⟨x, hx⟩) hα1
        rw [MulAut.one_apply] at h
        have h2 := congrArg Subtype.val h
        simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
      calc a * x = (a * x * a⁻¹) * a := by group
        _ = x * a := by rw [hcent]
    exact hDA_ne hDA_bot
  have hExp : ∀ x ∈ D, x ^ q = 1 := by
    intro x hx
    have hxker : (⟨x, hx⟩ : ↥D) ∈ θ.ker := by
      rw [hker, hOmega_top]
      exact Subgroup.mem_top _
    have h1 : (⟨x, hx⟩ : ↥D) ^ q = 1 := by
      rw [← hθ ⟨x, hx⟩, hxker]
      rfl
    simpa using congrArg Subtype.val h1
  have hClass : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    have h1 : ⁅⁅D, D⁆, D⁆ ≤ ⁅k89qa_frattiniOf D, D⁆ := Subgroup.commutator_mono_left hDD_le_Φ
    rw [Subgroup.commutator_comm (k89qa_frattiniOf D) D, hDΦ_bot] at h1
    exact le_bot_iff.mp h1
  have hPhi_eq_DD : k89qa_frattiniOf D = ⁅D, D⁆ := by
    have hfr : frattini ↥D = _root_.commutator ↥D := by
      rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥D) (p := q)]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro y hy
        rcases hy with hy | hy
        · exact hy
        · rcases hy with ⟨z, rfl⟩
          change z ^ q ∈ (_root_.commutator ↥D : Subgroup ↥D)
          have hz : z ^ q = 1 := by
            apply Subtype.ext
            simpa using hExp (z : G) z.2
          rw [hz]
          exact Subgroup.one_mem _
      · intro y hy
        exact Subgroup.subset_closure (Or.inl hy)
    calc k89qa_frattiniOf D = (frattini ↥D).map D.subtype := rfl
      _ = (_root_.commutator ↥D).map D.subtype := by rw [hfr]
      _ = ⁅D, D⁆ := Subgroup.map_subtype_commutator D
  refine ⟨D, hD_le, hAD, hExp, hClass, ?_, ?_⟩
  · rw [hDA_eq]
    exact not_le_of_gt hDD_lt
  · intro W hW hWD hAW
    rw [← hPhi_eq_DD] at hW
    have := hIrred W hW hWD hAW
    rwa [hPhi_eq_DD] at this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
