module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.GGL45TGSU
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

theorem kgLangS1A_uni_cover
    {d n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) (hd : 3 ≤ d) (hn : 2 ≤ n) {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (hK : commutator K = ⊤) {u₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hu₀ : u₀ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (LargeEvenGUSet (Fin d) F (2 ^ n))) :
    ∃ κ' : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* K, Function.Surjective κ' ∧
      κ'.ker ≤ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) ∧
      (∀ g, θ (QuotientGroup.mk (κ' g)) = u₀ (LargeEvenProjMk _ g)) ∧
      (∀ (α : MulAut K)
        (B : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))),
        u₀⁻¹ * kgInducedAut θ α * u₀ = TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) B →
        ∀ g, α (κ' g) = κ' ((LargeEvenSUGroup (Fin d) F (2 ^ n)).normalizerMonoidHom B g)) ∧
      ∀ (α : MulAut K) (σ : F ≃+* F)
        (f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))
        (ψ₀ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))),
        (∀ g, ((ψ₀ g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) : GL (Fin d) F) =
          Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F)) →
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
            ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀ →
        kgInducedAut θ α = u₀ * f₀ * u₀⁻¹ →
        ∀ g, α (κ' g) = κ' (ψ₀ g) := by
  let SU := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let R := LargeEvenProj SU
  obtain ⟨κ, hκsurj, hκker, hκθ⟩ := GGL45TG.SU.exists_cover_unitary h hd hn hK θ
  have hN : LargeEvenGUSet (Fin d) F (2 ^ n) ⊆
      Subgroup.normalizer (SU : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer h
  obtain ⟨g₀, hg₀GU, hu₀eq⟩ := TableB.exists_eq_projConj hN hu₀
  have hg₀norm : g₀ ∈ Subgroup.normalizer (SU : Set (GL (Fin d) F)) := hN hg₀GU
  let cg₀ : SU →* SU := (SU.normalizerMonoidHom ⟨g₀, hg₀norm⟩).toMonoidHom
  let κ' : SU →* K := κ.comp cg₀
  have hκ' : ∀ g : SU, θ (QuotientGroup.mk (κ' g)) =
      TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU g) := by
    intro g
    rw [show κ' g = κ (cg₀ g) from rfl, hκθ (cg₀ g)]
    change LargeEvenProjMk SU (cg₀ g) =
      TableB.projConj SU ⟨g₀, hg₀norm⟩ ((g : LargeEvenProj SU))
    rw [TableB.projConj_mk]
    rfl
  have hκ'u₀ : ∀ g, θ (QuotientGroup.mk (κ' g)) = u₀ (LargeEvenProjMk SU g) := by
    intro g
    rw [hκ' g, hu₀eq]
  have hκ'surj : Function.Surjective κ' := by
    intro k
    obtain ⟨x, hx⟩ := hκsurj k
    obtain ⟨g, hg⟩ := (SU.normalizerMonoidHom ⟨g₀, hg₀norm⟩).surjective x
    refine ⟨g, ?_⟩
    change κ ((SU.normalizerMonoidHom ⟨g₀, hg₀norm⟩) g) = k
    rw [hg, hx]
  have hκ'ker : κ'.ker ≤ Subgroup.center SU := by
    intro h hh
    have h1 : u₀ (LargeEvenProjMk SU h) = 1 := by
      rw [← hκ'u₀ h, MonoidHom.mem_ker.mp hh, QuotientGroup.mk_one, map_one]
    have h2 : LargeEvenProjMk SU h = 1 := by
      have h2' := congrArg (fun x => u₀⁻¹ x) h1
      simpa using h2'
    have h3 : ((h : SU) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      have h4 : h ∈ (LargeEvenScalars (Fin d) F).subgroupOf SU := by
        rw [← QuotientGroup.eq_one_iff]
        exact h2
      exact Subgroup.mem_subgroupOf.mp h4
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (TableB.scalars_le_center h3)) (x : GL (Fin d) F)
  have hH : commutator SU = ⊤ := by
    haveI hSUperf : Group.IsPerfect SU :=
      Subgroup.isPerfect_iff.mpr (GGL45TG.SU.commutator_su h hd hn)
    exact Group.IsPerfect.commutator_eq_top
  have hconj : ∀ (α : MulAut K)
      (B : Subgroup.normalizer (SU : Set (GL (Fin d) F))),
      u₀⁻¹ * kgInducedAut θ α * u₀ = TableB.projConj SU B →
      ∀ g, α (κ' g) = κ' (SU.normalizerMonoidHom B g) := by
    intro α B hαeq g
    refine kgLangTorA_act (H := SU) (K := K) (R := R) hH θ κ' α
      ((SU.normalizerMonoidHom B).toMonoidHom) ?_ g
    intro h
    rw [hκ' h, hκ' ((SU.normalizerMonoidHom B).toMonoidHom h)]
    have hαeq' : kgInducedAut θ α = u₀ * TableB.projConj SU B * u₀⁻¹ := by
      rw [← hαeq]
      group
    rw [hαeq', hu₀eq]
    have h2 : ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU B *
        (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹ : MulAut R) *
        TableB.projConj SU ⟨g₀, hg₀norm⟩) =
        TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU B := by group
    calc ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU B *
          (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹) *
          TableB.projConj SU ⟨g₀, hg₀norm⟩) (LargeEvenProjMk SU h)
        = (TableB.projConj SU ⟨g₀, hg₀norm⟩ * TableB.projConj SU B)
            (LargeEvenProjMk SU h) := by rw [h2]
      _ = TableB.projConj SU ⟨g₀, hg₀norm⟩
            (TableB.projConj SU B (LargeEvenProjMk SU h)) := rfl
      _ = TableB.projConj SU ⟨g₀, hg₀norm⟩
            (LargeEvenProjMk SU ((SU.normalizerMonoidHom B).toMonoidHom h)) := by
          apply (TableB.projConj SU ⟨g₀, hg₀norm⟩).injective
          rw [show TableB.projConj SU B (LargeEvenProjMk SU h) =
              LargeEvenProjMk SU ((SU.normalizerMonoidHom B).toMonoidHom h) from by
            change TableB.projConj SU B ((h : LargeEvenProj SU)) =
              LargeEvenProjMk SU ((SU.normalizerMonoidHom B).toMonoidHom h)
            rw [TableB.projConj_mk]
            rfl]
  have hfield : ∀ (α : MulAut K) (σ : F ≃+* F)
      (f₀ : MulAut R)
      (ψ₀ : SU →* SU),
      (∀ g, ((ψ₀ g : SU) : GL (Fin d) F) =
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F)) →
      LargeEvenGraphAut (LargeEvenProjMk SU)
        (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀ →
      kgInducedAut θ α = u₀ * f₀ * u₀⁻¹ →
      ∀ g, α (κ' g) = κ' (ψ₀ g) := by
    intro α σ f₀ ψ₀ hψ₀ hgraph hαeq g
    refine kgLangTorA_act (H := SU) (K := K) (R := R) hH θ κ' α ψ₀ ?_ g
    intro h
    rw [hκ' h, hκ' (ψ₀ h)]
    rw [hαeq, hu₀eq]
    have h2 : ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ *
        (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹ : MulAut R) *
        TableB.projConj SU ⟨g₀, hg₀norm⟩) =
        TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ := by group
    calc ((TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀ *
          (TableB.projConj SU ⟨g₀, hg₀norm⟩)⁻¹) *
          TableB.projConj SU ⟨g₀, hg₀norm⟩) (LargeEvenProjMk SU h)
        = (TableB.projConj SU ⟨g₀, hg₀norm⟩ * f₀) (LargeEvenProjMk SU h) := by rw [h2]
      _ = TableB.projConj SU ⟨g₀, hg₀norm⟩ (f₀ (LargeEvenProjMk SU h)) := rfl
      _ = TableB.projConj SU ⟨g₀, hg₀norm⟩ (LargeEvenProjMk SU (ψ₀ h)) := by
          congr 1
          have hrel : ((ψ₀ h : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
              ((h : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ := by
            rw [hψ₀ h]
            rfl
          exact hgraph h (ψ₀ h) hrel
  exact ⟨κ', hκ'surj, hκ'ker, hκ'u₀, hconj, hfield⟩

end CFSG.StandardType
