module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_not_commutator_le_q1
    (hfr : Str83G4Frame L1 L2 S a) {A : Subgroup G} (hsup : A ⊔ Q1 L1 L2 S = S) :
    ¬ ⁅A, A⁆ ≤ Q1 L1 L2 S := by
  classical
  intro hA
  have ha : 1 ≤ a := hfr.2.2.1
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  have hpCore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  have hAS : A ≤ S := le_sup_left.trans hsup.le
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hmemQ : ∀ u : ↥(L1 ⊔ S), (u : G) ∈ Q1 L1 L2 S → u ∈ pCore 2 ↥(L1 ⊔ S) := by
    intro u hu
    rw [← CFSG.openPCoreOf_subgroupOf 2 (L1 ⊔ S), hpCore]
    exact Subgroup.mem_subgroupOf.mpr hu
  have hmk : ∀ s : ↥(L1 ⊔ S), (s : G) ∈ S → ∃ t : ↥(L1 ⊔ S), (t : G) ∈ A ∧
      (QuotientGroup.mk s : oTwoQuot ↥(L1 ⊔ S)) = QuotientGroup.mk t := by
    intro s hs
    have hs' : (s : G) ∈ ((A ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
      rw [hsup]
      exact hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A (Q1 L1 L2 S) (hAS.trans hSNQ1)] at hs'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hs'
    refine ⟨⟨x, (le_sup_right : S ≤ L1 ⊔ S) (hAS hx)⟩, hx, ?_⟩
    rw [QuotientGroup.eq]
    refine hmemQ _ ?_
    have e : ((s⁻¹ * ⟨x, (le_sup_right : S ≤ L1 ⊔ S) (hAS hx)⟩ : ↥(L1 ⊔ S)) : G) = y⁻¹ := by
      push_cast
      rw [← hxy]
      group
    rw [e]
    exact (Q1 L1 L2 S).inv_mem hy
  have hUcomm : ∀ u ∈ suzukiU a (GaloisField 2 (2 * a + 1)),
      ∀ v ∈ suzukiU a (GaloisField 2 (2 * a + 1)), u * v = v * u := by
    intro u hu v hv
    rw [← he] at hu hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨t, htA, ht⟩ := hmk s (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨t', ht'A, ht'⟩ := hmk s' (Subgroup.mem_subgroupOf.mp hs')
    simp only [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [ht, ht', ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    rw [QuotientGroup.eq]
    refine hmemQ _ ?_
    have e : (((t * t')⁻¹ * (t' * t) : ↥(L1 ⊔ S)) : G) = ⁅(t' : G)⁻¹, (t : G)⁻¹⁆ := by
      push_cast
      rw [commutatorElement_def]
      group
    rw [e]
    exact hA (Subgroup.commutator_mem_commutator (A.inv_mem ht'A) (A.inv_mem htA))
  have hbot : commutator ↥(suzukiU a (GaloisField 2 (2 * a + 1))) = ⊥ :=
    (commutator_eq_bot_iff _).mpr ⟨⟨fun x y => Subtype.ext (hUcomm _ x.2 _ y.2)⟩⟩
  have hz0 : suzukiSElt a (GaloisField 2 (2 * a + 1)) 0 1 ∈
      suzukiZ0 a (GaloisField 2 (2 * a + 1)) :=
    (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩
  have hU : suzukiSElt a (GaloisField 2 (2 * a + 1)) 0 1 ∈
      suzukiU a (GaloisField 2 (2 * a + 1)) :=
    suzukiZ0_le_suzukiU hz0
  have hmem : (⟨_, hU⟩ : suzukiU a (GaloisField 2 (2 * a + 1))) ∈
      (suzukiZ0 a (GaloisField 2 (2 * a + 1))).subgroupOf
        (suzukiU a (GaloisField 2 (2 * a + 1))) :=
    Subgroup.mem_subgroupOf.mpr hz0
  rw [← commutator_suzukiU hK ha, hbot] at hmem
  have h1 : suzukiSElt a (GaloisField 2 (2 * a + 1)) 0 1 =
      suzukiSElt a (GaloisField 2 (2 * a + 1)) 0 0 := by
    simpa [suzukiSElt_zero_zero hK] using congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  exact one_ne_zero (suzukiSElt_inj.mp h1).2

theorem str83G4_commutator_q1_not_le
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hA : Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊔ CFSG.conjugate (Q1 L1 L2 S) d.w =
      CFSG.conjugate S d.w) :
    ¬ ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤ CFSG.conjugate (Q1 L1 L2 S) d.w := by
  intro hQ
  have hw2 : d.w * d.w ∈ S := str83G4_q2_le_s hfr (str83G4_w_mul_self_mem_q2 hfr d)
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ1ww : CFSG.conjugate (CFSG.conjugate (Q1 L1 L2 S) d.w) d.w = Q1 L1 L2 S := by
    rw [CFSG.conjugate_conjugate]
    exact CFSG.conjugate_eq_self_of_mem_normalizer (hSNQ1 hw2)
  have hSww : CFSG.conjugate (CFSG.conjugate S d.w) d.w = S := by
    rw [CFSG.conjugate_conjugate]
    exact CFSG.conjugate_eq_self_of_mem_normalizer (Subgroup.le_normalizer hw2)
  have hsup : CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w ⊔ Q1 L1 L2 S = S := by
    have h : CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊔ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w =
        CFSG.conjugate (CFSG.conjugate S d.w) d.w := congrArg (fun H => CFSG.conjugate H d.w) hA
    rw [show CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊔ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w =
        CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w ⊔
          CFSG.conjugate (CFSG.conjugate (Q1 L1 L2 S) d.w) d.w from Subgroup.map_sup _ _ _,
      hQ1ww, hSww] at h
    exact h
  refine str83G4_not_commutator_le_q1 hfr hsup ?_
  have hle : CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w ≤ CFSG.conjugate (Q1 L1 L2 S) d.w :=
    Subgroup.map_mono inf_le_left
  calc ⁅CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w,
        CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w⁆
      ≤ ⁅CFSG.conjugate (Q1 L1 L2 S) d.w, CFSG.conjugate (Q1 L1 L2 S) d.w⁆ :=
        Subgroup.commutator_mono hle hle
    _ = CFSG.conjugate ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ d.w := (Subgroup.map_commutator _ _ _).symm
    _ ≤ CFSG.conjugate (CFSG.conjugate (Q1 L1 L2 S) d.w) d.w := Subgroup.map_mono hQ
    _ = Q1 L1 L2 S := hQ1ww

end CFSG.Quasithin.Stroth

end
