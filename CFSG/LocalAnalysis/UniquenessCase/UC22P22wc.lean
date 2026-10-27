module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wi
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p22wc_compShape_of_diag (D : Data G) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hcomp : IsComponentOf (mbarImage D.M D.U K) ⊤) {n : ℕ} (hsp : IsSp4 (Bar2 K) n) {t : G} (htT : t ∈ D.T)
    (ht : ActsNontrivOnDiagram K t) : CompShape148 (mbarImage D.M D.U K) := by
  set Lb := mbarImage D.M D.U K with hLb
  have hq : CFSG.Open.IsQuasisimple ↥Lb := hcomp.2.2
  have hne : Lb ≠ ⊥ := by
    intro h0
    haveI : Nontrivial ↥Lb := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance h0
  obtain ⟨ψ, hψs, hψk, hψc⟩ := uc22p22wa_onto D hK hne
  have hKq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  haveI : IsSimpleGroup (Bar2 K) := uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl rfl))) hsp
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← P22w.center_eq_bot_of_isSimpleGroup hKq]
    exact hψk
  set e₁ : Bar2 K ≃* ↥Lb := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩ with he₁
  have he₁c : ∀ k : ↥K, ((e₁ (QuotientGroup.mk k) : ↥Lb) : MBar D.M D.U) =
      QuotientGroup.mk (Subgroup.inclusion hK.1.le k) := hψc
  refine Or.inl ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv e₁ hsp, ?_⟩
  obtain ⟨htN, θ, hθ, hθn⟩ := ht
  have htM : t ∈ D.M := D.sylowM.le htT
  set g : MBar D.M D.U := QuotientGroup.mk ⟨t, htM⟩ with hg
  have htK : ∀ k : ↥K, t * (k : G) * t⁻¹ ∈ K := fun k => (Subgroup.mem_normalizer_iff.1 htN _).1 k.2
  have htK' : ∀ k : ↥K, t⁻¹ * (k : G) * t⁻¹⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htN) _).1 k.2
  have himg : ∀ k : ↥K, (QuotientGroup.mk (Subgroup.inclusion hK.1.le k) : MBar D.M D.U) ∈ Lb :=
    fun k => ⟨Subgroup.inclusion hK.1.le k, k.2, rfl⟩
  have hconj : ∀ k : ↥K, g * QuotientGroup.mk (Subgroup.inclusion hK.1.le k) * g⁻¹ =
      (QuotientGroup.mk (Subgroup.inclusion hK.1.le ⟨t * (k : G) * t⁻¹, htK k⟩) : MBar D.M D.U) := by
    intro k
    rw [hg, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hgN : g ∈ normalizer (Lb : Set (MBar D.M D.U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      have h1 := hconj ⟨m, hm⟩
      exact h1 ▸ himg _
    · intro hx
      obtain ⟨m, hm, hmx⟩ := hx
      rw [QuotientGroup.mk'_apply] at hmx
      have h2 : x = g⁻¹ * QuotientGroup.mk m * g⁻¹⁻¹ := by
        rw [hmx]
        group
      rw [h2]
      have h3 : g⁻¹ * QuotientGroup.mk (Subgroup.inclusion hK.1.le ⟨(m : G), hm⟩) * g⁻¹⁻¹ =
          (QuotientGroup.mk (Subgroup.inclusion hK.1.le ⟨t⁻¹ * (m : G) * t⁻¹⁻¹, htK' ⟨m, hm⟩⟩) :
            MBar D.M D.U) := by
        rw [hg, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      have hmm : (QuotientGroup.mk m : MBar D.M D.U) =
          QuotientGroup.mk (Subgroup.inclusion hK.1.le ⟨(m : G), hm⟩) := rfl
      rw [hmm, h3]
      exact himg _
  set ε : (Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* (↥Lb ⧸ Subgroup.center ↥Lb) :=
    QuotientGroup.congr (Subgroup.center (Bar2 K)) (Subgroup.center ↥Lb) e₁ (Subgroup.map_center_eq e₁) with hε
  refine ⟨g, hgN, MulAut.congr ε θ, fun a a' haa' => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := e₁.surjective a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    set k' : ↥K := ⟨t * (k : G) * t⁻¹, htK k⟩ with hk'
    have ha' : a' = e₁ (QuotientGroup.mk k') := by
      apply Subtype.ext
      rw [haa', he₁c, he₁c, hconj]
    rw [ha']
    show ε (θ (ε.symm (QuotientGroup.mk (e₁ (QuotientGroup.mk k))))) = QuotientGroup.mk (e₁ (QuotientGroup.mk k'))
    have hs : ε.symm (QuotientGroup.mk (e₁ (QuotientGroup.mk k))) = QuotientGroup.mk (QuotientGroup.mk k) := by
      rw [MulEquiv.symm_apply_eq, hε, QuotientGroup.congr_mk]
    rw [hs, hθ k k' rfl, hε, QuotientGroup.congr_mk]
  · rwa [uc22p22wi_isInnDiagFieldAut_congr ε θ]

end CFSG.LocalAnalysis.UniquenessCase.UC22
