module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Background.B1MoreTenA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B113

section Offenders

variable {V : Type*} [CommGroup V]

theorem ffJP_eq_ffJ {G T : Subgroup (MulAut V)} (hTG : T ≤ G) :
    ffJP {A | IsFFStarOffender G A} T = ffJ T := by
  unfold ffJP ffJ
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAT => ?_
    exact le_iSup_of_le A (le_iSup_of_le (⟨hAT, hA.2⟩ : IsFFStarOffender T A) le_rfl)
  · refine iSup_le fun A => iSup_le fun hA => ?_
    exact le_iSup_of_le A (le_iSup_of_le
      (show A ∈ {A | IsFFStarOffender G A} from ⟨hA.1.trans hTG, hA.2⟩)
      (le_iSup_of_le hA.1 le_rfl))

theorem le_ffJ_of_offender {G T A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hAT : A ≤ T) : A ≤ ffJ T :=
  le_iSup_of_le A (le_iSup_of_le (⟨hAT, hA.2⟩ : IsFFStarOffender T A) le_rfl)

theorem exists_offender_not_le_centralizer {G T X : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hX : ⁅X, ffJ T⁆ ≠ ⊥) :
    ∃ A, IsFFStarOffender G A ∧ A ≤ T ∧ ¬ A ≤ Subgroup.centralizer (X : Set (MulAut V)) := by
  by_contra hcon
  push Not at hcon
  apply hX
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact iSup_le fun A => iSup_le fun hA => hcon A ⟨hA.1.trans hTG, hA.2⟩ hA.1

variable [Finite V]

theorem exists_offender_commutator_eq {G T X : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hXJ : ⁅X, ffJ T⁆ = X) (hX0 : X ≠ ⊥)
    (hX : CFSG.Open.IsQuasisimple ↥X ∨ Nat.card ↥X = 3) :
    ∃ A, IsFFStarOffender G A ∧ A ≤ T ∧ ⁅X, A⁆ = X := by
  obtain ⟨A, hA, hAT, hAc⟩ := exists_offender_not_le_centralizer hTG (by rw [hXJ]; exact hX0)
  refine ⟨A, hA, hAT, ?_⟩
  have hAn : A ≤ Subgroup.normalizer (X : Set (MulAut V)) :=
    (le_ffJ_of_offender hA hAT).trans (le_normalizer_of_commutator_eq hXJ)
  have hAX : ∀ b ∈ A, ∀ k ∈ X, b * k * b⁻¹ ∈ X := fun b hb k hk =>
    B19Aux.conj_mem_of_le_normalizer hAn hb hk
  rcases B1Red.commutator_eq_or_commute hX hAX with h | h
  · exact h
  · exact absurd (fun b hb => Subgroup.mem_centralizer_iff.2 fun k hk => (h b hb k hk).symm) hAc

omit [Finite V] in
theorem ne_bot_of_quasisimple_or_card_three {X : Subgroup (MulAut V)}
    (hX : CFSG.Open.IsQuasisimple ↥X ∨ Nat.card ↥X = 3) : X ≠ ⊥ := by
  rcases hX with hq | h3
  · have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot X).1 this
  · intro h
    rw [h, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)

end Offenders

section Timmesfeld

variable {V : Type} [CommGroup V] [Finite V]

theorem ffJ_le_normalizer_comps (hP4 : AsB15Part4) (hV : ∀ v : V, v ^ 2 = 1)
    {G T : Subgroup (MulAut V)} (hTG : T ≤ G) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) : ffJ T ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  iSup_le fun A => iSup_le fun hA => hP4 V hV G A ⟨hA.1.trans hTG, hA.2⟩ L hL

end Timmesfeld

section Centralizes

variable {V : Type} [CommGroup V] [Finite V]

theorem case_centralizes_components {G K : Subgroup (MulAut V)} (hKG : K ≤ G)
    (hKF : K ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V)))
    (hcomp : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G →
      K ≤ Subgroup.centralizer (L : Set (MulAut V)))
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    Nat.card ↥K = 3 ∧ K ≤ fittingOf G ∧
      K ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V)) := by
  set Fs := quasithinGenFitting G with hFs
  have hFsK : Fs ≤ Subgroup.centralizer (K : Set (MulAut V)) := by
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNG, hNn, hNnil⟩
      have hn : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
        intro x hx n hn
        have := hNn.conj_mem ⟨n, hNG hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨x, hx⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hNF : N ≤ fittingOf G := B1Red.le_fittingOf_of_nilpotent_normal hNG hn
      intro f hf
      exact Subgroup.mem_centralizer_iff.2 fun k hk => ((Subgroup.mem_centralizer_iff.1
        (hKF hk)) f (hNF hf)).symm
    · intro L hL f hf
      exact Subgroup.mem_centralizer_iff.2 fun k hk => ((Subgroup.mem_centralizer_iff.1
        (hcomp L hL hk)) f hf).symm
  have hKFs : K ≤ Subgroup.centralizer (Fs : Set (MulAut V)) := fun k hk =>
    Subgroup.mem_centralizer_iff.2 fun f hf =>
      ((Subgroup.mem_centralizer_iff.1 (hFsK hf)) k hk).symm
  have hKinFs : K ≤ Fs := fun k hk => centralizer_quasithinGenFitting_le G ⟨hKG hk, hKFs hk⟩
  have hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.1 (hKFs hx)) y (hKinFs hy)).symm
  have hK3 : Nat.card ↥K = 3 := by
    rcases hK with hq | h3
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (hKab a a.2 b b.2))
    · exact h3
  refine ⟨hK3, ?_, hKF⟩
  set Z : Subgroup (MulAut V) := Fs ⊓ Subgroup.centralizer (Fs : Set (MulAut V)) with hZ
  have hZG : Z ≤ G := inf_le_left.trans (quasithinGenFitting_le G)
  have hZn : ∀ g ∈ G, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    have hgF : ∀ f, f ∈ Fs ↔ g * f * g⁻¹ ∈ Fs := fun f =>
      Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting G hg) f
    refine ⟨(hgF z).1 hz.1, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
    have hf' : g⁻¹ * f * g ∈ Fs := by
      have := (hgF (g⁻¹ * f * g)).2 (by simpa [mul_assoc] using hf)
      exact this
    have h1 := Subgroup.mem_centralizer_iff.1 hz.2 (g⁻¹ * f * g) hf'
    calc f * (g * z * g⁻¹) = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * f := by group
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.1 hx.2) y hy.1).symm
  have : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext (hZab a a.2 b b.2)⟩⟩
  have hZF : Z ≤ fittingOf G := B1Red.le_fittingOf_of_nilpotent_normal hZG hZn
  intro k hk
  exact hZF ⟨hKinFs hk, hKFs hk⟩

end Centralizes

section Components

variable {V : Type} [CommGroup V] [Finite V]

theorem commutator_comp_eq_of_normalizes {K L : Subgroup (MulAut V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hKL : ∀ b ∈ K, ∀ l ∈ L, b * l * b⁻¹ ∈ L)
    (hnc : ¬ K ≤ Subgroup.centralizer (L : Set (MulAut V))) : ⁅L, K⁆ = L := by
  rcases B1Red.commutator_eq_or_commute (Or.inl hq) hKL with h | h
  · exact h
  · exact absurd (fun b hb => Subgroup.mem_centralizer_iff.2 fun k hk => (h b hb k hk).symm) hnc

end Components

end B113

end CFSG.Quasithin
