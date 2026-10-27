module

public import CFSG.Quasithin.Recognition.CertR2aBridges
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Rel

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Open CFSG.QuasithinUnique

theorem u33_rel {w : List (Fin 5 × Bool)} (hw : w ∈ u33PresRels) :
    wordProd u33GenPG (w.map fun l => (l.1.val, l.2)) = 1 := by
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}
      (FreeGroup.mk w) : U33G) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map.2 ⟨w, hw, rfl⟩)
  have h2 : PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk} =
      FreeGroup.lift (fun i : Fin 5 => (PresentedGroup.of i : U33G)) := by
    apply FreeGroup.ext_hom
    intro i
    simp [PresentedGroup.mk, PresentedGroup.of]
  rw [h2] at h1
  have h3 : (fun i : Fin 5 => (PresentedGroup.of i : U33G)) = fun i => u33GenPG i.val :=
    funext fun i => (u33GenPG_of i).symm
  rw [h3, lift_mk'] at h1
  exact h1

theorem u33_rel_of {w : List (Fin 5 × Bool)} (hw : w ∈ u33PresRels) {l : List (ℕ × Bool)}
    (e : w.map (fun l => (l.1.val, l.2)) = l) : wordProd u33GenPG l = 1 := by
  rw [← e]; exact u33_rel hw

theorem u33_r1 : u33GenPG 0 * u33GenPG 0 * u33GenPG 0 * u33GenPG 0 = 1 := by
  have h := u33_rel_of (w := u33Word "aaaa") (by decide +kernel)
    (l := [(0, true), (0, true), (0, true), (0, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r2 : u33GenPG 1 * u33GenPG 1 * u33GenPG 1 * u33GenPG 1 = 1 := by
  have h := u33_rel_of (w := u33Word "bbbb") (by decide +kernel)
    (l := [(1, true), (1, true), (1, true), (1, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r3 : u33GenPG 2 * u33GenPG 2 = 1 := by
  have h := u33_rel_of (w := u33Word "ss") (by decide +kernel)
    (l := [(2, true), (2, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r4 : (u33GenPG 0)⁻¹ * (u33GenPG 1)⁻¹ * u33GenPG 0 * u33GenPG 1 = 1 := by
  have h := u33_rel_of (w := u33Word "ABab") (by decide +kernel)
    (l := [(0, false), (1, false), (0, true), (1, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r5 : u33GenPG 2 * u33GenPG 0 * u33GenPG 2 * (u33GenPG 1)⁻¹ = 1 := by
  have h := u33_rel_of (w := u33Word "sasB") (by decide +kernel)
    (l := [(2, true), (0, true), (2, true), (1, false)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r6 : u33GenPG 2 * u33GenPG 1 * u33GenPG 2 * (u33GenPG 0)⁻¹ = 1 := by
  have h := u33_rel_of (w := u33Word "sbsA") (by decide +kernel)
    (l := [(2, true), (1, true), (2, true), (0, false)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r7 : u33GenPG 3 * u33GenPG 3 * u33GenPG 3 = 1 := by
  have h := u33_rel_of (w := u33Word "xxx") (by decide +kernel)
    (l := [(3, true), (3, true), (3, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r8 : (u33GenPG 3)⁻¹ * u33GenPG 0 * u33GenPG 3 * (u33GenPG 1)⁻¹ = 1 := by
  have h := u33_rel_of (w := u33Word "XaxB") (by decide +kernel)
    (l := [(3, false), (0, true), (3, true), (1, false)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r9 : (u33GenPG 3)⁻¹ * u33GenPG 1 * u33GenPG 3 * u33GenPG 1 * u33GenPG 0 = 1 := by
  have h := u33_rel_of (w := u33Word "Xbxba") (by decide +kernel)
    (l := [(3, false), (1, true), (3, true), (1, true), (0, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r10 : u33GenPG 3 * u33GenPG 2 * u33GenPG 3 * u33GenPG 2 = 1 := by
  have h := u33_rel_of (w := u33Word "xsxs") (by decide +kernel)
    (l := [(3, true), (2, true), (3, true), (2, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r11 : u33GenPG 4 * u33GenPG 4 * u33GenPG 4 = 1 := by
  have h := u33_rel_of (w := u33Word "yyy") (by decide +kernel)
    (l := [(4, true), (4, true), (4, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r12 : (u33GenPG 4)⁻¹ * u33GenPG 0 * u33GenPG 1 * u33GenPG 2 * u33GenPG 4 *
    u33GenPG 2 * u33GenPG 0 * u33GenPG 0 = 1 := by
  have h := u33_rel_of (w := u33Word "Yabsysaa") (by decide +kernel)
    (l := [(4, false), (0, true), (1, true), (2, true), (4, true), (2, true), (0, true),
      (0, true)]) (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r13 : (u33GenPG 4)⁻¹ * u33GenPG 2 * u33GenPG 0 * u33GenPG 0 * u33GenPG 4 *
    u33GenPG 1 * (u33GenPG 0)⁻¹ = 1 := by
  have h := u33_rel_of (w := u33Word "YsaaybA") (by decide +kernel)
    (l := [(4, false), (2, true), (0, true), (0, true), (4, true), (1, true), (0, false)])
    (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_r14 : (u33GenPG 0)⁻¹ * u33GenPG 2 * u33GenPG 4 * u33GenPG 2 * u33GenPG 0 *
    u33GenPG 4 = 1 := by
  have h := u33_rel_of (w := u33Word "Asysay") (by decide +kernel)
    (l := [(0, false), (2, true), (4, true), (2, true), (0, true), (4, true)])
    (by decide +kernel)
  simpa [wordProd, mul_assoc] using h

theorem u33_tRel : TRel (u33GenPG 0) (u33GenPG 1) (u33GenPG 2) :=
  TRel.of_relators u33_r1 u33_r2 u33_r3 u33_r4 u33_r5 u33_r6

theorem u33_aRel : ARel (u33GenPG 0) (u33GenPG 1) (u33GenPG 2) (u33GenPG 3) :=
  ARel.of_relators u33_tRel u33_r7 u33_r8 u33_r9 u33_r10

theorem u33_bRel : BRel (u33GenPG 0) (u33GenPG 1) (u33GenPG 2) (u33GenPG 4) :=
  BRel.of_relators u33_tRel u33_r11 u33_r12 u33_r13 u33_r14

section Model


theorem u33Data_T : u33Data.T = Subgroup.closure
    ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G) := rfl

theorem u33Data_A : u33Data.A = Subgroup.closure
    ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3} : Set U33G) := rfl

theorem u33Data_B : u33Data.B = Subgroup.closure
    ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4} : Set U33G) := rfl

theorem u33_card_T' : Nat.card (Subgroup.closure
    ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G)) = 32 := u33_card_T

theorem u33_inf : Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4} : Set U33G) ⊓
    Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3} : Set U33G) =
    Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G) := by
  rw [← u33Data_A, ← u33Data_B, inf_comm]
  exact u33Data.inf_AB

theorem u33_finite : Finite U33G := u33Pres_finite_card_le.1

theorem u33_isTwoLocalAmalgam : IsTwoLocalAmalgam u33Data.B u33Data.A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨u33Extra.isMaximalTwoLocal_B, u33Extra.isMaximalTwoLocal_A, ?_, ?_⟩
  · intro h
    apply u33Data.T_ne_B
    rw [← u33Data.inf_AB, ← h]
    exact inf_idem _
  · refine ⟨u33_syl.1.toSylow u33_syl.2, ?_⟩
    show u33Data.T = u33Data.B ⊓ u33Data.A
    rw [inf_comm]
    exact u33Data.inf_AB.symm

end Model

theorem isG22Prime_u33
    : IsG22Prime U33G := by
  have h2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_zmod]
  obtain ⟨c⟩ := g2_quotient_commutator_equiv (ZMod 2) h2
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  exact ⟨AdjointQuotient Tag.G2 (ZMod 2), inferInstance,
    ⟨ZMod 2, inferInstance, inferInstance, h2, ⟨MulEquiv.refl _⟩⟩, ⟨e.trans c.symm⟩⟩

end CFSG.Quasithin.F6.GoldAmL4
