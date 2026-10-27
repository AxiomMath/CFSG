module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wa
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

namespace P22w

theorem center_eq_bot_of_isSimpleGroup {P : Type} [Group P] [IsSimpleGroup P] (hP : CFSG.Open.IsQuasisimple P) :
    Subgroup.center P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h0 | h0
  · exact h0
  · exfalso
    have h1 : commutator P = ⊥ := (commutator_eq_bot_iff_center_eq_top P).2 h0
    rw [hP.1] at h1
    obtain ⟨a, ha⟩ := exists_ne (1 : P)
    have : a ∈ (⊤ : Subgroup P) := Subgroup.mem_top a
    rw [h1, Subgroup.mem_bot] at this
    exact ha this

theorem quotCenter_equiv {P Q : Type} [Group P] [Group Q] (hP : CFSG.Open.IsQuasisimple P)
    (hQ : CFSG.Open.IsQuasisimple Q) (ψ : P →* Q) (hψ : Function.Surjective ψ) :
    Nonempty ((P ⧸ Subgroup.center P) ≃* (Q ⧸ Subgroup.center Q)) := by
  have hle : Subgroup.center P ≤ (Subgroup.center Q).comap ψ := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨p, rfl⟩ := hψ q
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) p]
  have hge : (Subgroup.center Q).comap ψ ≤ Subgroup.center P := by
    haveI : ((Subgroup.center Q).comap ψ).Normal := Subgroup.Normal.comap inferInstance ψ
    refine P22sj.le_center_of_quasisimple hP inferInstance fun htop => ?_
    haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
    obtain ⟨a, ha⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨p, rfl⟩ := hψ q
    have hp : p ∈ (Subgroup.center Q).comap ψ := htop ▸ Subgroup.mem_top p
    exact ha ((QuotientGroup.eq_one_iff _).2 hp)
  refine ⟨MulEquiv.ofBijective (QuotientGroup.map _ _ ψ hle) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
    exact (QuotientGroup.eq_one_iff _).2 (hge hx)
  · intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨p, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk p, rfl⟩

theorem mulEquiv_of_isSimpleGroup {P Q : Type} [Group P] [Group Q] [IsSimpleGroup P]
    (hP : CFSG.Open.IsQuasisimple P) (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center P) : Nonempty (P ≃* Q) := by
  refine ⟨MulEquiv.ofBijective ψ ⟨?_, hψ⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_eq_bot_of_isSimpleGroup hP]
  exact hker

end P22w

theorem uc22p22wb_compShape_of_shape (D : Data G) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hcomp : IsComponentOf (mbarImage D.M D.U K) ⊤)
    (hshape : (∃ n : ℕ, IsSU3 (Bar2 K) n) ∨ (∃ n : ℕ, IsL2 (Bar2 K) n) ∨ (∃ n : ℕ, IsSz (Bar2 K) n) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 K) p) ∨ IsJ1 (Bar2 K)) :
    CompShape148 (mbarImage D.M D.U K) := by
  have hq : CFSG.Open.IsQuasisimple ↥(mbarImage D.M D.U K) := hcomp.2.2
  have hne : mbarImage D.M D.U K ≠ ⊥ := by
    intro h0
    haveI : Nontrivial ↥(mbarImage D.M D.U K) := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance h0
  obtain ⟨ψ, hψs, hψk, -⟩ := uc22p22wa_onto D hK hne
  have hKq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hiso : IsSimpleGroup (Bar2 K) → Nonempty (Bar2 K ≃* ↥(mbarImage D.M D.U K)) := fun hs => by
    haveI := hs
    exact P22w.mulEquiv_of_isSimpleGroup hKq ψ hψs hψk
  rcases hshape with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨p, hp, -, hn⟩ | hn
  · obtain ⟨e₁⟩ := P22w.quotCenter_equiv hKq hq ψ hψs
    exact Or.inr (Or.inl ⟨n, Or.inl ⟨hq, CFSG.Blueprint.LieModel.of_mulEquiv e₁ hn.2⟩⟩)
  · obtain ⟨e₁⟩ := hiso (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hn)
    exact Or.inr (Or.inl ⟨n, Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e₁ hn))⟩)
  · obtain ⟨e₁⟩ := hiso (uc22p22r_lieModel_isSimple_twistedB2 hn)
    exact Or.inr (Or.inl ⟨n, Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e₁ hn))⟩)
  · obtain ⟨e₁⟩ := hiso (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hn)
    exact Or.inr (Or.inr (Or.inl ⟨p, hp, CFSG.Blueprint.LieModel.of_mulEquiv e₁ hn⟩))
  · obtain ⟨e₀⟩ := hn
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.isSimpleGroup_J1
    haveI : IsSimpleGroup (Bar2 K) := e₀.isSimpleGroup
    obtain ⟨e₁⟩ := hiso inferInstance
    exact Or.inr (Or.inr (Or.inr ⟨e₁.symm.trans e₀⟩))

end CFSG.LocalAnalysis.UniquenessCase.UC22
