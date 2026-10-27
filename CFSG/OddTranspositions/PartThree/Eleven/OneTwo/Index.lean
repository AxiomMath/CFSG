module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Frame
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Kernel
public import CFSG.OddTranspositions.PartThree.CardWidth
public import CFSG.GroupTheory.SylowOrbitCard
public import CFSG.Holt.PermFactsInvolutions

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Index

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoHyp

variable {hC : HypothesisC D}

theorem index_commutator (h : ElevenTwoHyp hC) : (commutator G).index = 2 := by
  classical
  have hle : (commutator G).index ≤ 2 := hC.setup.index_commutator_le_two
  have hu : hC.d ∉ commutator G := by
    obtain ⟨S, T, r, hF⟩ := h.exists_frame
    letI : Fintype D := Fintype.ofFinite D
    haveI : CFSG.GroupTheory.NormalizesSet ⊤ D :=
      ⟨fun a _ x hx => hC.setup.normal a x hx⟩
    let σ : Equiv.Perm D := MulAction.toPermHom G D hC.d
    let ψ : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G D)
    have hσ2 : σ ^ 2 = 1 := by
      change (MulAction.toPermHom G D hC.d) ^ 2 = 1
      rw [← map_pow]
      have hd2 : hC.d ^ 2 = 1 := by
        rw [pow_two]
        exact hC.setup.oddT.mul_self_eq_one hC.hd
      rw [hd2, map_one]
    have hcoe : ∀ x : D, (σ x : G) = hC.d * (x : G) * hC.d⁻¹ := by
      intro x
      change (((MulAction.toPermHom G D) hC.d) x : G) = hC.d * (x : G) * hC.d⁻¹
      rw [MulAction.toPermHom_apply]
      exact CFSG.GroupTheory.conjMulActionOfTop_smul_coe D
        (inferInstance : CFSG.GroupTheory.NormalizesSet ⊤ D) hC.d x
    have hiff : ∀ x : D, (σ x = x) ↔ ((x : G) ∈ centSet D hC.d) := by
      intro x
      constructor
      · intro hx
        have hval : (σ x : G) = (x : G) := congrArg Subtype.val hx
        rw [hcoe x] at hval
        refine ⟨x.2, ?_⟩
        have h2 : (x : G) * hC.d = hC.d * (x : G) := by
          have h3 : hC.d * (x : G) = (x : G) * hC.d := by
            calc hC.d * (x : G) = hC.d * (x : G) * hC.d⁻¹ * hC.d := by group
              _ = (x : G) * hC.d := by rw [hval]
          exact h3.symm
        show (x : G) * hC.d = hC.d * (x : G)
        exact h2
      · rintro ⟨-, hc⟩
        apply Subtype.ext
        rw [hcoe x]
        have h2 : (x : G) * hC.d = hC.d * (x : G) := hc.eq
        rw [← h2]
        group
    have hcent : centSet D hC.d = insert hC.d (commSet D hC.d) := by
      ext x
      simp only [centSet, commSet, Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨hxD, hcomm⟩
        by_cases hxu : x = hC.d
        · exact Or.inl hxu
        · exact Or.inr ⟨hxD, hcomm, hxu⟩
      · rintro (rfl | ⟨hxD, hcomm, -⟩)
        · exact ⟨hC.hd, Commute.refl hC.d⟩
        · exact ⟨hxD, hcomm⟩
    have hcardcent : (centSet D hC.d).ncard = 66 := by
      rw [hcent, Set.ncard_insert_of_notMem (by simp [commSet]), h.ncard_commSet]
    let e : Function.fixedPoints σ ≃ ↥(centSet D hC.d) :=
      (Equiv.subtypeEquivRight hiff).trans
        (Equiv.subtypeSubtypeEquivSubtype (p := fun x : G => x ∈ D)
          (q := fun x : G => x ∈ centSet D hC.d) (fun {x} hx => hx.1))
    have hfixcard : Nat.card (Function.fixedPoints σ) = 66 := by
      rw [Nat.card_congr e]
      exact hcardcent
    have hDge66 : 66 ≤ Nat.card D := by
      rw [← hcardcent]
      exact Set.ncard_le_ncard (fun x hx => hx.1)
    have hmod8 : Nat.card D ≡ 4 [MOD 8] := by
      have hwidth : Nat.card ↥((S : Set G) ∩ D) = 4 := by
        rw [Nat.card_coe_set_eq]
        exact ElevenTwoFrame.ncard_inter h hF
      have hpv : padicValNat 2 (4 : ℕ) = 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
      have h := card_modEq_two_part_width hC.setup.isClass hC.setup.oddT S
      rw [hwidth, hpv] at h
      norm_num at h
      exact h
    have h4D : 4 ∣ Nat.card D := (hmod8.dvd_iff (by norm_num : 4 ∣ 8)).mpr (dvd_refl 4)
    have hnot4 : ¬ 4 ∣ Nat.card D - 66 := by
      intro h4sub
      obtain ⟨m, hm⟩ := h4D
      obtain ⟨k, hk⟩ := h4sub
      omega
    have hsign : Equiv.Perm.sign σ = -1 := by
      by_contra hne
      have h1 : Equiv.Perm.sign σ = 1 := (Int.units_eq_one_or _).resolve_right hne
      have h4 : 4 ∣ Nat.card D - Nat.card (Function.fixedPoints σ) :=
        (CFSG.Holt.sign_eq_one_iff_four_dvd_card_sub hσ2).mp h1
      rw [hfixcard] at h4
      exact hnot4 h4
    have hsignψ : ψ hC.d = -1 := by
      simpa [ψ, σ] using hsign
    have hcomm : commutator G ≤ ψ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    intro hmem
    have h1 : ψ hC.d = 1 := MonoidHom.mem_ker.mp (hcomm hmem)
    rw [hsignψ] at h1
    exact absurd h1 (by decide)
  have hidx_ne_one : (commutator G).index ≠ 1 := by
    intro h1
    exact hu (by rw [Subgroup.index_eq_one.mp h1]; trivial)
  have hne0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := commutator G)
  omega

theorem not_mem_commutator (h : ElevenTwoHyp hC) : ∀ x ∈ D, x ∉ commutator G := by
  intro x hx hxcomm
  have hDsub : D ⊆ commutator G := by
    intro y hy
    obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hx hy)
    rw [← hg]
    exact (inferInstance : (commutator G).Normal).conj_mem x hxcomm g
  have htop : commutator G = ⊤ := by
    rw [eq_top_iff, ← hC.setup.gen, Subgroup.closure_le]
    exact hDsub
  have hone : (commutator G).index = 1 := Subgroup.index_eq_one.mpr htop
  rw [index_commutator h] at hone
  exact absurd hone (by norm_num)

end ElevenTwoHyp

end Index

end CFSG.OddTranspositions.PartThree
