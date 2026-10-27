module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux5
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux4

public section

open CFSG.Open
open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

@[expose] def ChiefCyclic (p : ℕ) (X : Subgroup Γ) : Prop :=
  ∀ M N : Subgroup Γ, IsChiefFactorOf X M N → ∀ [(N.subgroupOf M).Normal],
    ∀ P : Subgroup (MulAut (↥M ⧸ N.subgroupOf M)), IsPGroup p P → IsCyclic P

variable [Finite Γ]

omit [Finite Γ] in
theorem isChiefFactorOf_component {X J : Subgroup Γ} (hX : IsDirectProduct (lcal X) X)
    (hJ : J ∈ lcal X) : IsChiefFactorOf X J ⊥ := by
  obtain ⟨hJX, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
  have hJbot : ⊥ < J := by
    refine bot_lt_iff_ne_bot.mpr fun h => hnc ?_
    rw [h]
    infer_instance
  refine ⟨⟨bot_le, Subgroup.le_normalizer_of_normal⟩, ⟨hJX, hX.le_normalizer hJ⟩, hJbot,
    fun K hK hbK hKJ => ?_⟩
  have hnorm : ∀ u ∈ K, ∀ j ∈ J, j * u * j⁻¹ ∈ K := fun u hu j hj =>
    (Subgroup.mem_normalizer_iff.mp (hK.2 (hJX hj)) u).mp hu
  exact eq_bot_or_eq_of_conj_mem hJs hKJ hnorm

omit [Finite Γ] in
theorem cycStab_of_chiefCyclic {p : ℕ} {A X : Subgroup Γ} (h : DiagSetting p A X)
    (hH : ChiefCyclic p X) : CycStab A X := by
  intro J hJ
  have hcf := isChiefFactorOf_component h.direct hJ
  have hnorm : ((⊥ : Subgroup Γ).subgroupOf J).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  obtain ⟨n, hnD, hn⟩ := exists_cyclic_acting (A := A) (M := J) (N := ⊥)
    (D := A ⊓ Subgroup.normalizer (J : Set Γ)) bot_le h.elemAbelian inf_le_left inf_le_right
    Subgroup.le_normalizer_of_normal (hH J ⊥ hcf)
  refine ⟨n, hnD.1, hn.trans (sup_le_sup_right ?_ _)⟩
  intro g hg
  obtain ⟨hgD, hgS⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨hgD.1, ?_⟩
  refine mem_centralizer_of_centralizes_component h hJ hgD.1 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hgS.2.2 y hy
  rw [Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem le_wSub_or_le_cenIn_of_chief {p : ℕ} (hp : p.Prime) {A B X : Subgroup Γ}
    (hA : IsElemAbelian p A) (hAX : Admits A X) (hcop : Nat.Coprime p (Nat.card X))
    (hB : B ≤ A) (hchief : IsChiefFactorOf (X ⊔ A) X ⊥) (hH : ChiefCyclic p X) :
    X ≤ wSub A B X ∨ X ≤ cenIn X (B : Set Γ) := by
  by_cases hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  · have hXne : X ≠ ⊥ := ne_of_gt hchief.2.2.1
    have hmin : ∀ Y : Subgroup Γ, Y ≤ X → Admits A Y → Y = ⊥ ∨ Y = X := by
      intro Y hYX hAY
      refine hchief.2.2.2 Y ⟨hYX.trans le_sup_left, sup_le ?_ hAY⟩ bot_le hYX
      intro x hx
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => hab y (hYX hy) x hx)
    obtain ⟨a, ha, hAa⟩ := exists_cyclic_of_abelian_chief hp hA hAX hcop hmin hXne
    exact le_wSub_or_le_cenIn_of_cyclic hp hA inf_le_left inf_le_right hB ha hAa
  · push Not at hab
    have hASimple : IsASimple A X := by
      refine ⟨hAX, hab, fun N hNX hNn hAN => ?_⟩
      have hXN : X ≤ Subgroup.normalizer (N : Set Γ) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp hNn
      exact hchief.2.2.2 N ⟨hNX.trans le_sup_left, sup_le hXN hAN⟩ bot_le hNX
    have hSC : IsDirectProduct (simpleComponents X) X :=
      AChief.isDirectProduct_simpleComponents hASimple
    have hss : IsSemisimple X := hSC
    have hlcal : lcal X = simpleComponents X := hss.lcal_eq
    have hne : (lcal X).Nonempty := hlcal ▸ hASimple.simpleComponents_nonempty
    have hDS : DiagSetting p A X :=
      ⟨hp, hA, hAX, hss.isDirectProduct_lcal, hne, fun J hJ J' hJ' => by
        rw [hlcal] at hJ hJ'
        exact hASimple.components_transitive hJ hJ'⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hsolv : Group.IsSolvable X := CFSG.SignalizerFunctorTheorem.isSolvable_of_coprime_two X
        hcop
      obtain ⟨J, hJ⟩ := hne
      obtain ⟨hJX, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
      have : Group.IsSolvable J :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJX)
      have := hJs
      exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))
    exact le_wSub_or_le_cenIn_of_diagSetting hp2 _ A X B hDS (cycStab_of_chiefCyclic hDS hH) hB rfl

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
