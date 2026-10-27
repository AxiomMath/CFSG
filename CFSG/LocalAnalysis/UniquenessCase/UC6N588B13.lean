module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B12
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_perfectResidual_uc6b {C : Subgroup G} {n : G}
    (hn : n ∈ normalizer (C : Set G)) :
    n ∈ normalizer (((CFSG.perfectResidual ↥C).map C.subtype : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (C : Set G), ∀ z ∈ (CFSG.perfectResidual ↥C).map C.subtype,
      n' * z * n'⁻¹ ∈ (CFSG.perfectResidual ↥C).map C.subtype := by
    intro n' hn' z hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨Subgroup.normalizerMonoidHom C ⟨n', hn'⟩ x, ?_, by simp⟩
    have hfix : (CFSG.perfectResidual ↥C).map
        (Subgroup.normalizerMonoidHom C ⟨n', hn'⟩).toMonoidHom = CFSG.perfectResidual ↥C :=
      Subgroup.characteristic_iff_map_eq.1 inferInstance _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · exact key n hn z
  · intro hz
    have := key n⁻¹ (inv_mem hn) _ hz
    simpa [mul_assoc] using this

theorem mem_normalizer_inf_uc6b {A B : Subgroup G} {n : G} (hA : n ∈ normalizer (A : Set G))
    (hB : n ∈ normalizer (B : Set G)) : n ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf, hA x, hB x]

theorem mem_normalizer_zpowers_uc6b {a g : G} (hg : g ∈ centralizer ({a} : Set G)) :
    g ∈ normalizer ((zpowers a : Subgroup G) : Set G) := by
  have hga : g * a * g⁻¹ = a := by
    rw [← mem_centralizer_iff.1 hg a rfl]
    group
  refine mem_normalizer_of_forward_uc6 fun x hx => ?_
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hga]
  exact zpow_mem_zpowers a k

namespace Mz614

namespace A10Setup

variable {m : Mz614 G} (D : A10Setup m)

include D in
theorem isSolvable_CHL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) :
    Group.IsSolvable ↥(centralizer (m.L : Set G) ⊓ m.H) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set C := centralizer (m.L : Set G) ⊓ m.H with hC
  set J₀ := CFSG.perfectResidual ↥C with hJ₀
  set J := J₀.map C.subtype with hJ
  have hres := CFSG.perfect_residual_characterization (G := ↥C)
  haveI hJperf : Group.IsPerfect ↥J₀ := hres.2.2.1
  have hcardJ : Nat.card J = Nat.card J₀ := Subgroup.card_map_of_injective C.subtype_injective
  have hJC : J ≤ C := Subgroup.map_subtype_le _
  have hHJ : m.H ≤ normalizer (J : Set G) := by
    intro h hh
    apply mem_normalizer_perfectResidual_uc6b
    exact mem_normalizer_inf_uc6b (mem_normalizer_centralizer_uc6 (m.H_le_normalizer_L hh))
      (Subgroup.le_normalizer hh)
  have hEJ : m.E ≤ normalizer (J : Set G) := m.hZ.E_le_centralizer.trans hHJ
  have h5 : ¬ 5 ∣ Nat.card J₀ := by
    intro hdvd
    obtain ⟨P⟩ : Nonempty (Sylow 5 ↥J₀) := inferInstance
    apply CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect
      (Group.isPerfect_def.1 hJperf) hdvd P
    intro x hx
    rw [mem_center_iff]
    intro y
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hk' : ((x : ↥C) : G) ^ 5 ^ k = 1 := by
      have := congrArg (fun t : ↥(P : Subgroup ↥J₀) => (((t : ↥J₀) : ↥C) : G)) hk
      simpa using this
    have hxZ := D.mem_Z_of_pow_prime_pow h69 h620 hr hw₁ hw₂ (x : ↥C).2 hk'
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (y : ↥C).2.2 _ hxZ).symm
  have hJM : J ≤ m.M := by
    have hEel : IsElemAbelian 5 m.E := by rw [← hr]; exact m.d.E_el
    have hEcard : 5 ^ 2 ≤ Nat.card m.E := by rw [m.d.E_card, hr]
    have hcop : Nat.Coprime 5 (Nat.card J) := by
      rw [hcardJ]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5
    rw [← CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_five hEel
      hEcard hEJ hcop]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    refine inf_le_right.trans fun g hg => ?_
    have haE : zpowers a ≤ m.E := (zpowers_le).2 ha
    have ha1' : zpowers a ≠ ⊥ := by
      intro h
      apply ha1
      rw [← mem_bot, ← h]
      exact mem_zpowers a
    exact m.d.normalizer_le_of_le_pGroup m.hC haE ha1' le_rfl (m.d.E_el.isPGroup.to_le haE)
      (mem_normalizer_zpowers_uc6b hg)
  have hodd : Odd (Nat.card J₀) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have h2' : 2 ∣ Nat.card J := by rw [hcardJ]; exact h2
    have hE5 : IsPGroup 5 m.E := by rw [← hr]; exact m.d.E_el.isPGroup
    obtain ⟨T, -, hTJ, hT2, hTidx, hET⟩ :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.exists_invariant_sylow_containing_of_pGroup
        Nat.prime_five Nat.prime_two hE5 hEJ (by rw [hcardJ]; exact h5) bot_le IsPGroup.of_bot
        (fun e _ => mem_normalizer_iff.2 fun x => by simp [mem_bot])
    have hT1 : T ≠ ⊥ := by
      rintro rfl
      apply hTidx
      rw [Subgroup.relIndex_bot_left]
      exact h2'
    have hNT : normalizer (T : Set G) ≤ m.M := m.normalizer_le_M_of_E_normalizes hT2 hT1 hET
    have hTsyl : IsSylowOf 2 T J := isSylowOf_iff.2 ⟨hTJ, hT2, hTidx⟩
    have hfr := frattini_of_isSylowOf (hJC.trans inf_le_right) hHJ hTsyl
    apply m.hZ.not_le
    show m.H ≤ m.M
    rw [hfr]
    exact sup_le hJM (inf_le_right.trans hNT)
  have hJsolv : Group.IsSolvable ↥J₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hJbot : J₀ = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥J₀ := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥J₀ hJsolv
  exact hres.2.2.2.2.2.1 hJbot

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
