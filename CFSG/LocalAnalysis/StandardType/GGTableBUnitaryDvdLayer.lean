module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.StandardType

namespace TableBUD

open CFSG.Assembly TableBSymp

section Lift

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem commutator_le_ggFix (a : MulAut L') {Y : Subgroup L'}
    (h : ∀ y ∈ Y, a y * y⁻¹ ∈ Subgroup.center L') : ⁅Y, Y⁆ ≤ ggFix a := by
  rw [Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  rw [mem_ggFix, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  have e₁ : a y₁ = (a y₁ * y₁⁻¹) * y₁ := by group
  have e₂ : a y₂ = (a y₂ * y₂⁻¹) * y₂ := by group
  calc a y₁ * a y₂ * (a y₁)⁻¹ * (a y₂)⁻¹ = ((a y₁ * y₁⁻¹) * y₁) * ((a y₂ * y₂⁻¹) * y₂) *
        ((a y₁ * y₁⁻¹) * y₁)⁻¹ * ((a y₂ * y₂⁻¹) * y₂)⁻¹ := by rw [← e₁, ← e₂]
    _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := commutator_mul_central (h y₁ hy₁) (h y₂ hy₂)

theorem mul_inv_mem_center_of_fix (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'}
    {ab : MulAut R} (hab : ∀ l, ab (ψ l) = ψ (a l)) {l : L'} (hl : ab (ψ l) = ψ l) :
    a l * l⁻¹ ∈ Subgroup.center L' :=
  hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hab, hl, mul_inv_cancel])

theorem layer_ggFix_lift (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {ab : MulAut R} (hab : ∀ l, ab (ψ l) = ψ (a l))
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix ab)) (ggFix ab)) :
    LargeEvenLayer (ggFix a) =
        ⁅(LargeEvenLayer (ggFix ab)).comap ψ, (LargeEvenLayer (ggFix ab)).comap ψ⁆ ∧
      IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  set Ct := ggFix ab with hCt
  set Kb := LargeEvenLayer Ct with hKb
  set C := ggFix a with hC
  set Y := Kb.comap ψ with hY
  set K := ⁅Y, Y⁆ with hK
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker hKbq
  have hKC : K ≤ C := commutator_le_ggFix a fun y hy =>
    mul_inv_mem_center_of_fix hker hab (mem_ggFix.mp (hcomp.1 hy))
  have hCCt : ∀ c ∈ C, ψ c ∈ Ct := fun c hc => by
    rw [hCt, mem_ggFix, hab, mem_ggFix.mp hc]
  have hCY : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    show ψ (c * y * c⁻¹) ∈ Kb
    rw [map_mul, map_mul, map_inv]
    exact largeEvenLayer_conj_mem (hCCt c hc) hy
  have hCK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have hle : K.map (MulAut.conj c).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_commutator]
      have hYc : Y.map (MulAut.conj c).toMonoidHom ≤ Y := by
        rintro _ ⟨y, hy, rfl⟩
        exact hCY c hc y hy
      exact Subgroup.commutator_mono hYc hYc
    exact hle ⟨k, hk, rfl⟩
  have hKcomp : IsComponentOf K C := by
    refine ⟨hKC, IsSubnormal.step hKC ?_ (IsSubnormal.refl C), (isQuasisimple_iff _).mpr hKq⟩
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro k c hk hc
    exact hCK c hc k hk
  set Chat := Ct.comap ψ with hChat
  have hCChat : C ≤ Chat := fun c hc => hCCt c hc
  have hCn : (C.subgroupOf Chat).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCChat]
    intro c g hc hg
    have hz := mul_inv_mem_center_of_fix hker hab (mem_ggFix.mp hg)
    have hag : a g = (a g * g⁻¹) * g := by group
    rw [hC, mem_ggFix] at hc ⊢
    rw [map_mul, map_mul, map_inv, hc, hag]
    have e := Subgroup.mem_center_iff.mp hz (g * c * g⁻¹)
    calc a g * g⁻¹ * g * c * (a g * g⁻¹ * g)⁻¹
        = (a g * g⁻¹) * (g * c * g⁻¹) * (a g * g⁻¹)⁻¹ := by group
      _ = (g * c * g⁻¹) * (a g * g⁻¹) * (a g * g⁻¹)⁻¹ := by rw [e]
      _ = g * c * g⁻¹ := by group
  have hle_all : ∀ K' : Subgroup L', IsComponentOf K' C → K' ≤ K := by
    intro K' hK'
    have hK'q : CFSG.IsQuasisimple K' := (isQuasisimple_iff _).mp hK'.2.2
    have hsub : IsSubnormal K' Chat := isSubnormal_trans_normal hK'.2.1 hCChat hCn
    have hsubR : IsSubnormal (K'.map ψ) Ct := by
      have := isSubnormal_map_hom ψ hsub
      rwa [hChat, Subgroup.map_comap_eq_self_of_surjective hψ] at this
    have hrange : (ψ.comp K'.subtype).range = K'.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hqR : CFSG.IsQuasisimple (K'.map ψ) := by
      have h := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hK'q (ψ.comp K'.subtype)
        (by
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) y))
      rw [hrange] at h
      exact h
    have hcompR : IsComponentOf (K'.map ψ) Ct := by
      refine ⟨?_, hsubR, (isQuasisimple_iff _).mpr hqR⟩
      rintro _ ⟨k, hk, rfl⟩
      exact hCCt k (hK'.1 hk)
    have hK'Y : K' ≤ Y := by
      rw [hY, ← Subgroup.map_le_iff_le_comap]
      exact le_sSup hcompR
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    rw [← hK'perf]
    exact Subgroup.commutator_mono hK'Y hK'Y
  have hlayer : LargeEvenLayer C = K :=
    le_antisymm (sSup_le fun K' hK' => hle_all K' hK') (le_sSup hKcomp)
  exact ⟨hlayer, hlayer ▸ hKcomp⟩

theorem induced_zpow {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (m : ℤ) :
    ∀ l, (φ ^ m) (ψ l) = ψ ((a ^ m) l) := by
  intro l
  cases m with
  | ofNat k => exact TypeA.induced_pow ψ h k l
  | negSucc k =>
    rw [zpow_negSucc, zpow_negSucc]
    apply (φ ^ (k + 1)).injective
    rw [MulAut.apply_inv_self, TypeA.induced_pow ψ h (k + 1), MulAut.apply_inv_self]

theorem apply_eq_of_mem_zpowers {G : Type*} [Group G] {a a' : MulAut G}
    (ha' : a' ∈ Subgroup.zpowers a) {j : G} (hj : a j = j) : a' j = j := by
  have hstab : a ∈ MulAction.stabilizer (MulAut G) j :=
    MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hj)
  have h1 := MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hstab) ha')
  rwa [MulAut.smul_def] at h1

theorem endNode_of_induced (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    (hR : ∃ ab ∈ TypeA.inducedSub ψ A, ab ≠ 1 ∧
      IsComponentOf (LargeEvenLayer (ggFix ab)) (ggFix ab) ∧
      ∀ ab' ∈ TypeA.inducedSub ψ A,
        ((∀ j ∈ LargeEvenLayer (ggFix ab), ab' j = j) ↔ ab' ∈ Subgroup.zpowers ab)) :
    ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  obtain ⟨ab, ⟨a, haA, hab⟩, hab1, hcomp, hcent⟩ := hR
  obtain ⟨hlayer, hcompL⟩ := layer_ggFix_lift hψ hker hab hcomp
  set Kb := LargeEvenLayer (ggFix ab) with hKb
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hmapK := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hKbperf
  refine ⟨a, haA, ?_, hcompL, fun a' ha' => ?_⟩
  · rintro rfl
    apply hab1
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [hab]
    rfl
  obtain ⟨ab', hab'⟩ := hind a' ha'
  have hab'A : ab' ∈ TypeA.inducedSub ψ A := ⟨a', ha', hab'⟩
  rw [hlayer]
  constructor
  · intro hfix
    have h1 : ∀ j ∈ Kb, ab' j = j := by
      intro j hj
      rw [← hmapK] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      rw [hab', hfix k hk]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ((hcent ab' hab'A).mp h1)
    have h2 : a ^ m = a' := TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by
      rw [← induced_zpow hab m l, hm, hab']
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, h2⟩
  · intro hmem j hj
    exact apply_eq_of_mem_zpowers hmem (hcompL.1 (hlayer ▸ hj))

end Lift

@[expose] def GGEndNodeAut (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
    p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

theorem ggEndNode_of_aut {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGEndNodeAut p r R I) : GGEndNode p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  have hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  have hcard := TypeA.card_inducedSub hψ hker hperf hind
  refine endNode_of_induced hψ hker hperf hind (h _ (TypeA.isElemAbelian_inducedSub hψ hA) ?_
    (hcard ▸ hr) (hcard ▸ h3))
  rintro φ ⟨a, ha, hφ⟩
  obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
  rwa [TypeA.induced_unique ψ hψ hφ hφ']

end TableBUD

end CFSG.StandardType
