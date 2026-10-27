module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86_le_lhat_of_isPGroup {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {X : Subgroup G}
    (hX : IsPGroup 2 X) :
    (X ≤ P1 L1 L2 S → X ≤ L1 ⊔ S) ∧ (X ≤ P2 L1 L2 S → X ≤ u3H L1 L2 S) := by
  have hF := hI.hF
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  constructor
  · intro hXP
    have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
    have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB
        (Or.inr (Or.inl ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩))
    have hSH : S ≤ L1 ⊔ Q1 L1 L2 S :=
      hS1.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    have heq : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
      le_antisymm (sup_le le_sup_left hSH) (sup_le le_sup_left (hQ1S.trans le_sup_right))
    have hNP : L1 ⊔ S ≤ P1 L1 L2 S := sup_le le_sup_left (hSB'.trans le_sup_right)
    have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
      bigB_le_normalizer_of_hyp111 hF.1
    have hPN : P1 L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) := by
      rw [heq]
      exact F1.le_normalizer_sup (sup_le Subgroup.le_normalizer hBL1)
        (le_normalizer_pCoreOf 2 _)
    have hS := f112_isSylowTwoOf_P1 hF.toW
    have hodd : ¬ 2 ∣ (L1 ⊔ S).relIndex (P1 L1 L2 S) := fun h2 => by
      have hmul := Subgroup.relIndex_mul_relIndex S (L1 ⊔ S) (P1 L1 L2 S) le_sup_right hNP
      have h' : 2 ∣ S.relIndex (P1 L1 L2 S) := hmul ▸ h2.mul_left _
      exact hS.2.2 h'
    exact B6.le_of_isPGroup_of_odd_relIndex hXP hX hNP hPN hodd
  · intro hXP
    have hNP : u3H L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
    have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
      have := bigB_le_normalizer_of_hyp111 hF.1.symm
      rwa [bigB_comm] at this
    have hPN : P2 L1 L2 S ≤ Subgroup.normalizer ((u3H L1 L2 S : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (sup_le Subgroup.le_normalizer hBL2) (le_normalizer_pCoreOf 2 _)
    have hSN : S ≤ u3H L1 L2 S := str86_s_le_u3H hF.toW hI.hSB hI.hm hI.hL2
    have hS := f112_isSylowTwoOf_P2 hF.toW
    have hodd : ¬ 2 ∣ (u3H L1 L2 S).relIndex (P2 L1 L2 S) := fun h2 => by
      have hmul := Subgroup.relIndex_mul_relIndex S (u3H L1 L2 S) (P2 L1 L2 S) hSN hNP
      have h' : 2 ∣ S.relIndex (P2 L1 L2 S) := hmul ▸ h2.mul_left _
      exact hS.2.2 h'
    exact B6.le_of_isPGroup_of_odd_relIndex hXP hX hNP hPN hodd

theorem str86_conj_z2_ne {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {h : G}
    (hh : h ∈ P1 L1 L2 S) (hhB : h ∉ bigB L1 L2 S) :
    MulAut.conj h • Z2 L1 L2 S ≠ Z2 L1 L2 S := by
  intro hc
  have hF := hI.hF
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hP2Z2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hP2Z2
  have hhN : h ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [← hc, mem_conj_smul_iff']
      have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
      rw [e]
      exact hn
    · intro hn
      rw [← hc] at hn
      have hn' := mem_conj_smul_iff'.mp hn
      have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
      rwa [e] at hn'
  have hP1Z2 : P1 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rcases F1.bigB_maximal_in_parabolic hR (P1 L1 L2 S ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G))
        (le_inf le_sup_right hBZ) inf_le_left with hM | hM
    · exact absurd (hM ▸ (Subgroup.mem_inf.mpr ⟨hh, hhN⟩ :
        h ∈ P1 L1 L2 S ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G))) hhB
    · exact inf_eq_left.mp hM
  have hG0 : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1Z2 hP2Z2
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hZS : Z2 L1 L2 S ≤ S := (omegaOneCenterOf_le _).trans hQ2S
  have hZO : Z2 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 (hZS.trans le_sup_right) hG0 (hF.1.h1.pgroup.to_le hZS)
  rw [hF.1.o2] at hZO
  exact hI.critHypN.ne_bot (le_bot_iff.mp hZO)

theorem str86_conjClosure_frame {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    conjClosure (Z2 L1 L2 S) L1 ≤ Q1 L1 L2 S ∧
      P1 L1 L2 S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) ∧
      ∀ h ∈ P1 L1 L2 S, MulAut.conj h • Z2 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 := by
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hI.hF.1
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have key : ∀ c ∈ bigB L1 L2 S, ∀ x ∈ conjClosure (Z2 L1 L2 S) L1,
      c * x * c⁻¹ ∈ conjClosure (Z2 L1 L2 S) L1 := by
    intro c hc x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, z, hz, rfl⟩ := hx
      have hl' : c * l * c⁻¹ ∈ L1 := (Subgroup.mem_normalizer_iff.mp (hBL hc) l).mp hl
      have hz' : c * z * c⁻¹ ∈ Z2 L1 L2 S := (Subgroup.mem_normalizer_iff.mp (hBZ hc) z).mp hz
      rw [show c * (l * z * l⁻¹) * c⁻¹ =
        (c * l * c⁻¹) * (c * z * c⁻¹) * (c * l * c⁻¹)⁻¹ by group]
      exact mem_conjClosure hl' hz'
    | one => simpa using (conjClosure (Z2 L1 L2 S) L1).one_mem
    | mul x y _ _ ihx ihy =>
      rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) by group]
      exact (conjClosure (Z2 L1 L2 S) L1).mul_mem ihx ihy
    | inv x _ ih =>
      rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ by group]
      exact (conjClosure (Z2 L1 L2 S) L1).inv_mem ih
  refine ⟨?_, ?_, ?_⟩
  · refine conjClosure_le fun h hh z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) ((le_sup_left : L1 ≤ P1 L1 L2 S) hh)) z).mp
        (hZQ hz)
  · refine sup_le (le_normalizer_conjClosure _ _) fun c hc => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c hc x, fun hx => ?_⟩
    have h' := key c⁻¹ ((bigB L1 L2 S).inv_mem hc) _ hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h'
  · intro h hh
    obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hh
    intro x hx
    have hx' := mem_conj_smul_iff'.mp hx
    have hbz : b * ((l * b)⁻¹ * x * (l * b)) * b⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hBZ hb) _).mp hx'
    have e : l * (b * ((l * b)⁻¹ * x * (l * b)) * b⁻¹) * l⁻¹ = x := by group
    rw [← e]
    exact mem_conjClosure hl hbz

end CFSG.Quasithin.Stroth

end
