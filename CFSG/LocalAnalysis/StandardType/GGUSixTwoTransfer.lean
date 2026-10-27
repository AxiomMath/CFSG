module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.Line63.H5
open scoped commutatorElement

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}

theorem qAutHom_compat (a : MulAut L') : ∀ l, qAutHom L' a (qmk L' l) = qmk L' (a l) :=
  fun l => qAutHom_mk a l

theorem mul_comm_of_mem (hA : CFSG.Open.IsElemAbelian 3 A) {a a' : MulAut L'} (ha : a ∈ A)
    (ha' : a' ∈ A) : a * a' = a' * a :=
  congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)

theorem layer_invariant_A (hA : CFSG.Open.IsElemAbelian 3 A) {a : MulAut L'} (ha : a ∈ A) :
    ∀ a' ∈ A, ∀ e ∈ LargeEvenLayer (ggFix a), a' e ∈ LargeEvenLayer (ggFix a) :=
  fun a' ha' => layer_invariant (mul_comm_of_mem hA ha ha')

theorem mem_zpowers_iff_qAutHom (hperf : commutator L' = ⊤) (a a₀ : MulAut L') :
    a ∈ Subgroup.zpowers a₀ ↔ qAutHom L' a ∈ Subgroup.zpowers (qAutHom L' a₀) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zpow]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, qAutHom_injective hperf (by rw [map_zpow]; exact hk)⟩

theorem cent_iff (hperf : commutator L' = ⊤) (a a' : MulAut L') :
    ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) ↔
      ((∀ jb ∈ LargeEvenLayer (ggFix (qAutHom L' a)), qAutHom L' a' jb = jb) ↔
        qAutHom L' a' ∈ Subgroup.zpowers (qAutHom L' a)) := by
  rw [fix_layer_iff qmk_surjective qmk_ker_le_center (qAutHom_compat a) (qAutHom_compat a'),
    mem_zpowers_iff_qAutHom hperf a' a]

theorem isEndNode_iff (hperf : commutator L' = ⊤) {a : MulAut L'} :
    GGIsEndNode A a ↔ GGIsEndNode (A.map (qAutHom L')) (qAutHom L' a) := by
  constructor
  · rintro ⟨haA, ha1, hcomp, hcent⟩
    refine ⟨⟨a, haA, rfl⟩, fun h => ha1 (qAutHom_injective hperf (by rw [h, map_one])),
      isComponentOf_layer_down qmk_surjective qmk_ker_le_center (qAutHom_compat a) hcomp, ?_⟩
    rintro _ ⟨a', ha', rfl⟩
    exact (cent_iff hperf a a').mp (hcent a' ha')
  · rintro ⟨⟨a₁, ha₁, ha₁a⟩, ha1, hcomp, hcent⟩
    have hea : a₁ = a := qAutHom_injective hperf ha₁a
    subst hea
    refine ⟨ha₁, fun h => ha1 (by rw [h, map_one]),
      (layer_eq_commutator_comap qmk_surjective qmk_ker_le_center (qAutHom_compat a₁) hcomp).2,
      fun a' ha' => ?_⟩
    exact (cent_iff hperf a₁ a').mpr (hcent (qAutHom L' a') ⟨a', ha', rfl⟩)

theorem smallHyp_down (hperf : commutator L' = ⊤) (hA : CFSG.Open.IsElemAbelian 3 A)
    {a : MulAut L'} (haA : a ∈ A) (h : GGStdSubSmallHyp 3 A a) :
    GGStdSubSmallHyp 3 (A.map (qAutHom L')) (qAutHom L' a) := by
  intro Eb hEb hEbL hEbfix hcase
  have hA3 : IsPGroup 3 A := isPGroup_three_of_isElemAbelian hA
  have hmap := layer_map_eq (π := qmk L') qmk_surjective qmk_ker_le_center (qAutHom_compat a)
  obtain ⟨E, hEL, hE, hEmap, hEfix, hEcard⟩ := exists_elemAbelian_lift_fixed hA3
    (layer_invariant_A hA haA) hEb (by rw [hmap]; exact hEbL)
    (fun a' ha' x hx => hEbfix _ ⟨a', ha', rfl⟩ x hx)
  rw [← hEcard]
  refine h E hE hEL hEfix ?_
  have hEEb : ∀ e ∈ E, qmk L' e ∈ Eb := fun e he => by
    rw [← hEmap]
    exact ⟨e, he, rfl⟩
  rcases hcase with hconj | ⟨Ub, hUb1, hUb2, hUbA, hEbN⟩
  · left
    intro e he
    obtain ⟨a'', ha'', hxx⟩ := hconj (qmk L' e) (hEEb e he)
    have : a'' = MulAut.conj e := qAutHom_injective hperf (by rw [hxx, qAutHom_conj])
    rw [← this]
    exact ha''
  · right
    refine ⟨Ub.comap (qmk L'), ?_, ?_, ?_, ?_⟩
    · intro hbot
      apply hUb1
      rw [eq_bot_iff]
      intro ub hub
      obtain ⟨u, rfl⟩ := qmk_surjective ub
      have hu : u ∈ Ub.comap (qmk L') := hub
      rw [hbot, Subgroup.mem_bot] at hu
      rw [hu, map_one]
      exact Subgroup.one_mem _
    · have := isPGroup_two_inf_comap hUb2 ⊤
      rwa [top_inf_eq] at this
    · intro a' ha' u hu
      show qmk L' (a' u) ∈ Ub
      rw [← qAutHom_mk]
      exact hUbA _ ⟨a', ha', rfl⟩ _ hu
    · intro e he
      have hn := Subgroup.mem_normalizer_iff.mp (hEbN (hEEb e he))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        show qmk L' (e * y * e⁻¹) ∈ Ub
        rw [map_mul, map_mul, map_inv]
        exact (hn (qmk L' y)).mp hy
      · intro hy
        have h2 : qmk L' (e * y * e⁻¹) ∈ Ub := hy
        rw [map_mul, map_mul, map_inv] at h2
        exact (hn (qmk L' y)).mpr h2

theorem concl_up (hperf : commutator L' = ⊤) (hA : CFSG.Open.IsElemAbelian 3 A)
    {a : MulAut L'} (haA : a ∈ A)
    (h : GGStdSubTwoTorusConcl 3 (A.map (qAutHom L')) (qAutHom L' a)) :
    GGStdSubTwoTorusConcl 3 A a := by
  obtain ⟨Ub, hUb1, hUb2, hUbL, hUbA, tb, htbL, htb3, htbfix, htbN, jb, hjbL, hjbc⟩ := h
  have hA3 : IsPGroup 3 A := isPGroup_three_of_isElemAbelian hA
  have hmap := layer_map_eq (π := qmk L') qmk_surjective qmk_ker_le_center (qAutHom_compat a)
  set E := LargeEvenLayer (ggFix a) with hE
  have hlift : ∀ xb ∈ LargeEvenLayer (ggFix (qAutHom L' a)), ∃ x ∈ E, qmk L' x = xb :=
    fun xb hxb => by
      rw [← hmap] at hxb
      obtain ⟨x, hx, rfl⟩ := hxb
      exact ⟨x, hx, rfl⟩
  obtain ⟨t, htE, htb, ht3, htfix⟩ := exists_fixed_cube_lift hA3 (H := E)
    (layer_invariant_A hA haA) (xb := tb) (by rw [hmap]; exact htbL)
    (fun a' ha' => htbfix _ ⟨a', ha', rfl⟩) htb3
  obtain ⟨j, hjE, hjb⟩ := hlift jb hjbL
  refine ⟨E ⊓ Ub.comap (qmk L'), ?_, isPGroup_two_inf_comap hUb2 E, inf_le_left, ?_,
    t, htE, ht3, htfix, ?_, j, hjE, fun hcomm => hjbc ?_⟩
  · intro hbot
    apply hUb1
    rw [eq_bot_iff]
    intro ub hub
    obtain ⟨u, huE, rfl⟩ := hlift ub (hUbL hub)
    have hu : u ∈ E ⊓ Ub.comap (qmk L') := ⟨huE, hub⟩
    rw [hbot, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact Subgroup.one_mem _
  · intro a' ha' u hu
    refine ⟨layer_invariant_A hA haA a' ha' u hu.1, ?_⟩
    show qmk L' (a' u) ∈ Ub
    rw [← qAutHom_mk]
    exact hUbA _ ⟨a', ha', rfl⟩ _ hu.2
  · have hn := Subgroup.mem_normalizer_iff.mp htbN
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyE, hyU⟩
      refine ⟨E.mul_mem (E.mul_mem htE hyE) (E.inv_mem htE), ?_⟩
      show qmk L' (t * y * t⁻¹) ∈ Ub
      rw [map_mul, map_mul, map_inv, htb]
      exact (hn (qmk L' y)).mp hyU
    · rintro ⟨hyE, hyU⟩
      refine ⟨?_, ?_⟩
      · have h1 := E.mul_mem (E.mul_mem (E.inv_mem htE) hyE) htE
        have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
        rwa [e] at h1
      · have h2 : qmk L' (t * y * t⁻¹) ∈ Ub := hyU
        rw [map_mul, map_mul, map_inv, htb] at h2
        exact (hn (qmk L' y)).mpr h2
  · rw [← htb, ← hjb, ← map_mul, ← map_mul, hcomm]

end CFSG.StandardType.USixTwo

end
