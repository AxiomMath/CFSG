module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.EmptyFaithful.S153LComp

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section General

variable {Γ : Type} [Group Γ]

theorem qs_perfect_ne_bot {N : Subgroup Γ} [Finite Γ] (hq : CFSG.IsQuasisimple ↥N) :
    ⁅N, N⁆ = N ∧ N ≠ ⊥ :=
  ⟨S153L.comp_perfect_of_isQuasisimple hq, SBc3.ne_bot_of_isQuasisimple hq⟩

theorem not_le_centralizer_self_of_qs [Finite Γ] {N : Subgroup Γ} (hq : CFSG.IsQuasisimple ↥N) :
    ¬ N ≤ Subgroup.centralizer (N : Set Γ) := by
  intro h
  obtain ⟨hp, hne⟩ := qs_perfect_ne_bot hq
  exact hne (hp.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h))

theorem eq_of_normal_qs [Finite Γ] {N M : Subgroup Γ} (hNM : N ≤ M)
    (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hqN : CFSG.IsQuasisimple ↥N)
    (hqM : CFSG.IsQuasisimple ↥M) : N = M := by
  have hn : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNM).2 fun h k hh hk => hNn k hk h hh
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqM hn with htop | hcen
  · refine le_antisymm hNM fun m hm => ?_
    have : (⟨m, hm⟩ : ↥M) ∈ N.subgroupOf M := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    apply not_le_centralizer_self_of_qs hqN
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := Subgroup.mem_center_iff.mp
      (hcen (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hNM hx⟩ : ↥M) ∈ _)) ⟨y, hNM hy⟩
    exact congrArg Subtype.val h

theorem eq_of_normal_simple [Finite Γ] {N M : Subgroup Γ} (hNM : N ≤ M)
    (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hqN : CFSG.IsQuasisimple ↥N)
    (hs : IsSimpleGroup ↥M) : N = M := by
  have hn : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNM).2 fun h k hh hk => hNn k hk h hh
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn with hbot | htop
  · exfalso
    apply (qs_perfect_ne_bot hqN).2
    rw [eq_bot_iff]
    intro n hn'
    have : (⟨n, hNM hn'⟩ : ↥M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hn'
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · refine le_antisymm hNM fun m hm => ?_
    have : (⟨m, hm⟩ : ↥M) ∈ N.subgroupOf M := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem not_qs_of_le_solvable [Finite Γ] {N M : Subgroup Γ} (hNM : N ≤ M)
    (hM : Group.IsSolvable ↥M) (hq : CFSG.IsQuasisimple ↥N) : False := by
  obtain ⟨hp, hne⟩ := qs_perfect_ne_bot hq
  have : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNM)
      (Subgroup.inclusion_injective hNM)
  apply hne
  rw [← perfectCore_eq_self_of_perfect hp]
  exact (isSolvable_iff_perfectCore_eq_bot N).mp this

theorem isComponentOf_of_qs_normal {N J : Subgroup Γ} (hNJ : N ≤ J)
    (hNn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) :
    IsComponentOf N J :=
  ⟨hNJ, IsSubnormal.step hNJ ((Subgroup.normal_subgroupOf_iff hNJ).2 fun h k hh hk =>
    hNn k hk h hh) (IsSubnormal.refl J), B1Red.isQuasisimple_to_open hq⟩

end General

section List

variable {V : Type} [CommGroup V] [Finite V]

theorem le_or_le_of_qs_normal {G₁ G₂ J N : Subgroup (MulAut V)} (hsup : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hNJ : N ≤ J)
    (hNn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) :
    N ≤ G₁ ∨ N ≤ G₂ := by
  have hcomp := isComponentOf_of_qs_normal hNJ hNn hq
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
  have hsub : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      IsSubnormal A J := fun {A B} hAB hcAB => by
    have hAJ : A ≤ J := hAB ▸ le_sup_left
    have hn := S153L.comp_normal_in_join hAB hcAB le_rfl fun g hg n hn =>
      A.mul_mem (A.mul_mem hg hn) (A.inv_mem hg)
    exact IsSubnormal.step hAJ ((Subgroup.normal_subgroupOf_iff hAJ).2 fun h k hh hk =>
      hn k hk h hh) (IsSubnormal.refl J)
  rcases B113.component_le_or_commutator_eq_bot hcomp (hsub hsup hc) with h1 | h1
  · exact Or.inl h1
  rcases B113.component_le_or_commutator_eq_bot hcomp (hsub hsup' hc') with h2 | h2
  · exact Or.inr h2
  exfalso
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
  apply not_le_centralizer_self_of_qs hq
  have hJ : J ≤ Subgroup.centralizer (N : Set (MulAut V)) := by
    rw [← hsup]
    exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  exact hNJ.trans hJ

noncomputable def statedSLEquivSL (n : ℕ) (K : Type) [Field K] :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (MulEquiv.subgroupCongr (CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL n K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem sl2_four_of_alt5 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) := by
  obtain ⟨e₀⟩ := sl2_four_equiv_alt5 (GaloisField 2 2) card_gf4 card_sl2_gf4
  exact ⟨2, GaloisField 2 2, inferInstance, inferInstance, by rw [card_gf4]; norm_num,
    ⟨(e.trans e₀.symm).trans (statedSLEquivSL 2 (GaloisField 2 2)).symm⟩⟩

theorem list_of_le_perm_five {N Gi : Subgroup (MulAut V)} (e : ↥Gi ≃* Equiv.Perm (Fin 5))
    (hNG : N ≤ Gi) (hNn : ∀ g ∈ Gi, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) :
    B56QuasisimpleList ↥N := by
  obtain ⟨hp, hne⟩ := qs_perfect_ne_bot hq
  set N' : Subgroup ↥Gi := N.subgroupOf Gi with hN'
  set M : Subgroup (Equiv.Perm (Fin 5)) := N'.map e.toMonoidHom with hM
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff hNG).2 fun h k hh hk => hNn k hk h hh
  have hMn : M.Normal := Subgroup.Normal.map hN'n _ e.surjective
  have eN : ↥N ≃* ↥M := (Subgroup.subgroupOfEquivOfLe hNG).symm.trans
    (N'.equivMapOfInjective e.toMonoidHom e.injective)
  have hMne : M ≠ ⊥ := by
    intro h
    apply hne
    have h1 : N' = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNG hn⟩ : ↥Gi) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
    rw [h1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hMA : alternatingGroup (Fin 5) ≤ M :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((Subgroup.nontrivial_iff_ne_bot M).mpr hMne)
  have hMp : ⁅M, M⁆ = M := by
    have h1 : ⁅N', N'⁆ = N' := by
      apply Subgroup.map_injective Gi.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNG, hp]
    rw [hM, ← Subgroup.map_commutator, h1]
  have hAM : M ≤ alternatingGroup (Fin 5) := by
    rw [← hMp, ← alternatingGroup.commutator_perm_eq (by simp), commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hMeq : M = alternatingGroup (Fin 5) := le_antisymm hAM hMA
  exact Or.inl (sl2_four_of_alt5 (eN.trans (MulEquiv.subgroupCongr hMeq)))

theorem list_of_le_factor {N Gi : Subgroup (MulAut V)} (hf : B56FactorList ↥Gi) (hNG : N ≤ Gi)
    (hNn : ∀ g ∈ Gi, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) :
    B56QuasisimpleList ↥N := by
  obtain ⟨hp, -⟩ := qs_perfect_ne_bot hq
  rcases hf with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, hm1, hm, hF, ⟨e⟩⟩
  · rcases S153L.factor_sl2 hn hF e with ⟨-, -, hFN⟩ | ⟨hFN, -⟩
    · exfalso
      exact (qs_perfect_ne_bot hq).2 (le_bot_iff.mp (hFN.2.2.2 N hNG hp))
    · have hqG : CFSG.IsQuasisimple ↥Gi := hFN.2.2.1.resolve_left (fun h => by
        have := (qs_perfect_ne_bot hq).2
        exact this (le_bot_iff.mp (h ▸ hNG)))
      have hNe : N = Gi := eq_of_normal_qs hNG hNn hq hqG
      exact Or.inl ⟨n, F, inferInstance, inferInstance, hF,
        ⟨(MulEquiv.subgroupCongr hNe).trans e⟩⟩
  · exact list_of_le_perm_five e hNG hNn hq
  · obtain ⟨hFN, hne⟩ := S153L.factor_sl3 hm hF hm1 e
    have hqG : CFSG.IsQuasisimple ↥Gi := hFN.2.2.1.resolve_left hne
    have hNe : N = Gi := eq_of_normal_qs hNG hNn hq hqG
    exact Or.inr (Or.inl ⟨m, F, inferInstance, inferInstance, hF,
      ⟨(MulEquiv.subgroupCongr hNe).trans e⟩⟩)

end List

end CFSG.Quasithin.H13.A5
