module

public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.SimsD1TransMod
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.Quasithin.H13

open Subgroup

variable {A G : Type} [Group A] [Group G]

theorem IsXSectionIso₂.map_bot {X J K : Subgroup A} (φ : A →* G) (hφ : Function.Injective φ)
    (h : IsXSectionIso₂ X J ⊥ K ⊥) :
    IsXSectionIso₂ (X.map φ) (J.map φ) ⊥ (K.map φ) ⊥ := by
  obtain ⟨_, _, e, he⟩ := h
  let eJ : ↥J ≃* ↥(J.map φ) := J.equivMapOfInjective φ hφ
  let eK : ↥K ≃* ↥(K.map φ) := K.equivMapOfInjective φ hφ
  let eJq : ↥J ⧸ (⊥ : Subgroup A).subgroupOf J ≃*
      ↥(J.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (J.map φ) :=
    QuotientGroup.congr _ _ eJ (by simp)
  let eKq : ↥K ⧸ (⊥ : Subgroup A).subgroupOf K ≃*
      ↥(K.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (K.map φ) :=
    QuotientGroup.congr _ _ eK (by simp)
  have eJq_mk : ∀ j : ↥J, eJq (QuotientGroup.mk j) = QuotientGroup.mk (eJ j) :=
    fun j => QuotientGroup.congr_mk _ _ eJ (by simp) j
  have eKq_mk : ∀ k : ↥K, eKq (QuotientGroup.mk k) = QuotientGroup.mk (eK k) :=
    fun k => QuotientGroup.congr_mk _ _ eK (by simp) k
  have hkey : ∀ (j : ↥J) (k : ↥K),
      (eJq.symm.trans (e.trans eKq)) (QuotientGroup.mk (eJ j)) =
          QuotientGroup.mk (eK k) ↔
        e (QuotientGroup.mk j) = QuotientGroup.mk k := by
    intro j k
    have h1 : eJq.symm (QuotientGroup.mk (eJ j)) = QuotientGroup.mk j := by
      rw [← eJq_mk j, MulEquiv.symm_apply_apply]
    have h2 : eKq (QuotientGroup.mk k) = QuotientGroup.mk (eK k) := eKq_mk k
    change eKq (e (eJq.symm (QuotientGroup.mk (eJ j)))) =
        QuotientGroup.mk (eK k) ↔ e (QuotientGroup.mk j) = QuotientGroup.mk k
    rw [h1, ← h2]
    exact eKq.injective.eq_iff
  refine ⟨?_, ?_, eJq.symm.trans (e.trans eKq), ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  intro x' hx' j' k' hj' hk' hjk'
  obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hx'
  obtain ⟨j, rfl⟩ := eJ.surjective j'
  obtain ⟨k, rfl⟩ := eK.surjective k'
  have hj : x * (j : A) * x⁻¹ ∈ J := by
    rw [← Subgroup.mem_map_iff_mem hφ]
    simpa [eJ] using hj'
  have hk : x * (k : A) * x⁻¹ ∈ K := by
    rw [← Subgroup.mem_map_iff_mem hφ]
    simpa [eK] using hk'
  have hjk : e (QuotientGroup.mk j) = QuotientGroup.mk k := (hkey j k).mp hjk'
  have he' := he x hxX j k hj hk hjk
  have hclassJ :
      ((eJ ⟨x * (j : A) * x⁻¹, hj⟩ : ↥(J.map φ)) :
        ↥(J.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (J.map φ)) =
      ((⟨φ x * (eJ j : G) * (φ x)⁻¹, hj'⟩ : ↥(J.map φ)) :
        ↥(J.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (J.map φ)) := by
    congr 1
    exact Subtype.ext (by simp [eJ])
  have hclassK :
      ((eK ⟨x * (k : A) * x⁻¹, hk⟩ : ↥(K.map φ)) :
        ↥(K.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (K.map φ)) =
      ((⟨φ x * (eK k : G) * (φ x)⁻¹, hk'⟩ : ↥(K.map φ)) :
        ↥(K.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (K.map φ)) := by
    congr 1
    exact Subtype.ext (by simp [eK])
  calc
    (eJq.symm.trans (e.trans eKq))
        ((⟨φ x * (eJ j : G) * (φ x)⁻¹, hj'⟩ : ↥(J.map φ)) :
          ↥(J.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (J.map φ))
        = (eJq.symm.trans (e.trans eKq))
            ((eJ ⟨x * (j : A) * x⁻¹, hj⟩ : ↥(J.map φ)) :
              ↥(J.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (J.map φ)) := by rw [hclassJ]
    _ = ((eK ⟨x * (k : A) * x⁻¹, hk⟩ : ↥(K.map φ)) :
          ↥(K.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (K.map φ)) := (hkey _ _).mpr he'
    _ = ((⟨φ x * (eK k : G) * (φ x)⁻¹, hk'⟩ : ↥(K.map φ)) :
          ↥(K.map φ) ⧸ (⊥ : Subgroup G).subgroupOf (K.map φ)) := by
      rw [hclassK]

theorem IsNaturalSumUnder.map {n : ℕ} {L V : Subgroup A} (φ : A →* G) (hφ : Function.Injective φ)
    (h : IsNaturalSumUnder n L V) : IsNaturalSumUnder n (L.map φ) (V.map φ) := by
  obtain ⟨k, W, hk, hW, hiso, hind, hsup⟩ := h
  refine ⟨k, fun i => (W i).map φ, hk, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hWV, hLW, hcomm, hBN⟩ := hW i
    haveI : IsMulCommutative ↥(W i) := hcomm
    haveI : IsMulCommutative ↥((W i).map φ) :=
      CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        ((W i).equivMapOfInjective φ hφ) hcomm
    letI : CommGroup ↥(W i) := IsMulCommutative.instCommGroup
    letI : CommGroup ↥((W i).map φ) := IsMulCommutative.instCommGroup
    refine ⟨Subgroup.map_mono hWV, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hx
      exact (CFSG.Quasithin.SimsD1.TransMod.map_mem_normalizer_iff φ hφ (W i) l).2 (hLW hlL)
    · exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        ((W i).equivMapOfInjective φ hφ) hcomm
    · obtain ⟨K, hKfield, hKfinite, hKcard, hReal⟩ := hBN
      refine ⟨K, hKfield, hKfinite, hKcard, ?_⟩
      have hReal' := CFSG.Quasithin.H.LU.realizes_map
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K))
        ((W i).equivMapOfInjective φ hφ) hReal
      change (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).Realizes
        (autOn (L.map φ) ((W i).map φ)) ⊤ ⊥
      rwa [← CFSG.Quasithin.SimsD1.TransMod.autOn_map φ hφ L (W i)] at hReal'
  · intro i j
    exact IsXSectionIso₂.map_bot φ hφ (hiso i j)
  · exact CFSG.LocalCores.iSupIndep_map_of_injective hφ hind
  · rw [← Subgroup.map_iSup, hsup]

end CFSG.Quasithin.H13
