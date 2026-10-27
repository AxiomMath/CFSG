module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Faithful

open TableBExc.E6Three

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_conj_mem_rootSpan_of_isRoot (a : Fin τ.rank → Kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {x : ModGL τ K}
    (hx : x ∈ rootSpan τ K S) :
    rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ ∈ rootSpan τ K S := by
  have hle : rootSpan τ K S ≤
      (rootSpan τ K S).comap (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      rootDiagUnit_conj_pinnedX a (hS α hα)]
    exact (le_iSup₂ (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) α hα)
      (Subgroup.subset_closure ⟨_, rfl⟩)
  exact hle hx

theorem rootDiagUnit_conj_mem_posUnipotent (a : Fin τ.rank → Kˣ) {x : ModGL τ K}
    (hx : x ∈ posUnipotent τ K) :
    rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ ∈ posUnipotent τ K :=
  rootDiagUnit_conj_mem_rootSpan_of_isRoot (τ := τ) (K := K) a
    (S := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}) (fun _ hα => hα.1) hx

theorem rootDiagUnit_conj_mem_negUnipotent (a : Fin τ.rank → Kˣ) {x : ModGL τ K}
    (hx : x ∈ negUnipotent τ K) :
    rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ ∈ negUnipotent τ K :=
  rootDiagUnit_conj_mem_rootSpan_of_isRoot (τ := τ) (K := K) a
    (S := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ height α < 0}) (fun _ hα => hα.1) hx

theorem hatAut_rootDiagUnit (a : Fin τ.rank → Kˣ) :
    hatAut τ K ⟨rootDiagUnit τ a, rootDiagUnit_mem_hatGroup a⟩ = rootDiagAutHom τ K a :=
  MulEquiv.ext fun g => Subtype.ext rfl

theorem hatAut_injective : Function.Injective (hatAut τ K) := by
  refine (injective_iff_map_eq_one (hatAut τ K)).mpr fun z hz => ?_
  obtain ⟨c, hc, a, hza⟩ := z.2
  set da : ModGL τ K := rootDiagUnit τ a with hda
  have hzeca : (z : ModGL τ K) = c * da := by rw [hza, hda]
  have hcomm : ∀ h ∈ adjointGroup τ K, c * da * h * (c * da)⁻¹ = h := by
    intro h hh
    have e := congrArg Subtype.val (DFunLike.congr_fun hz (⟨h, hh⟩ : adjointGroup τ K))
    rw [coe_hatAut_apply, hzeca] at e
    exact e
  have hconj_eq : ∀ u ∈ adjointGroup τ K, c * u * c⁻¹ = da⁻¹ * u * da := by
    intro u hu
    have hmem : da⁻¹ * u * da ∈ adjointGroup τ K := by
      simpa [da, rootDiagUnit_inv] using
        conj_rootDiagUnit_mem_adjointGroup (τ := τ) (K := K) a⁻¹ hu
    have hfix := hcomm _ hmem
    calc c * u * c⁻¹ = (c * da) * (da⁻¹ * u * da) * (c * da)⁻¹ := by group
      _ = da⁻¹ * u * da := hfix
  have hUconj : ∀ u ∈ posUnipotent τ K, c * u * c⁻¹ ∈ posUnipotent τ K := by
    intro u hu
    have h1 : da⁻¹ * u * da ∈ posUnipotent τ K := by
      simpa [da, rootDiagUnit_inv] using
        rootDiagUnit_conj_mem_posUnipotent (τ := τ) (K := K) a⁻¹ hu
    rw [hconj_eq u (posUnipotent_le_adjointGroup hu)]
    exact h1
  have hUsurj : ∀ u ∈ posUnipotent τ K, ∃ v ∈ posUnipotent τ K, c * v * c⁻¹ = u := by
    intro u hu
    have hdaU : da * u * da⁻¹ ∈ posUnipotent τ K := by
      simpa [da] using rootDiagUnit_conj_mem_posUnipotent (τ := τ) (K := K) a hu
    refine ⟨da * u * da⁻¹, hdaU, ?_⟩
    have h2 := hconj_eq _ (posUnipotent_le_adjointGroup hdaU)
    calc c * (da * u * da⁻¹) * c⁻¹ = da⁻¹ * (da * u * da⁻¹) * da := h2
      _ = u := by group
  have hUmap : (posUnipotent τ K).map (MulAut.conj c) = posUnipotent τ K := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact hUconj u hu
    · intro x hx
      obtain ⟨v, hv, hvc⟩ := hUsurj x hx
      exact ⟨v, hv, hvc⟩
  have hcU : c ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hUmap
  have hNconj : ∀ u ∈ negUnipotent τ K, c * u * c⁻¹ ∈ negUnipotent τ K := by
    intro u hu
    have h1 : da⁻¹ * u * da ∈ negUnipotent τ K := by
      simpa [da, rootDiagUnit_inv] using
        rootDiagUnit_conj_mem_negUnipotent (τ := τ) (K := K) a⁻¹ hu
    rw [hconj_eq u (negUnipotent_le_adjointGroup hu)]
    exact h1
  have hNsurj : ∀ u ∈ negUnipotent τ K, ∃ v ∈ negUnipotent τ K, c * v * c⁻¹ = u := by
    intro u hu
    have hdaN : da * u * da⁻¹ ∈ negUnipotent τ K := by
      simpa [da] using rootDiagUnit_conj_mem_negUnipotent (τ := τ) (K := K) a hu
    refine ⟨da * u * da⁻¹, hdaN, ?_⟩
    have h2 := hconj_eq _ (negUnipotent_le_adjointGroup hdaN)
    calc c * (da * u * da⁻¹) * c⁻¹ = da⁻¹ * (da * u * da⁻¹) * da := h2
      _ = u := by group
  have hNmap : (negUnipotent τ K).map (MulAut.conj c) = negUnipotent τ K := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact hNconj u hu
    · intro x hx
      obtain ⟨v, hv, hvc⟩ := hNsurj x hx
      exact ⟨v, hv, hvc⟩
  have hcV : c ∈ Subgroup.normalizer (negUnipotent τ K : Set (ModGL τ K)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hNmap
  have hB : c ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨hc, hcU⟩
  have hB' : c ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨hc, hcV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  have hT : c ∈ torusGroup τ K := by
    rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := τ) (K := K) hT
  have hz_ba : (z : ModGL τ K) = rootDiagUnit τ (b * a) := by
    rw [hzeca, hda, hb, ← rootDiagUnit_mul]
  have hz_aut : hatAut τ K z = rootDiagAutHom τ K (b * a) := by
    rw [show z = ⟨rootDiagUnit τ (b * a), rootDiagUnit_mem_hatGroup (b * a)⟩ from
      Subtype.ext hz_ba, hatAut_rootDiagUnit]
  rw [hz_aut] at hz
  have hba : b * a = 1 := rootDiagAutHom_injective (by rw [hz, map_one])
  exact Subtype.ext (by rw [hz_ba, hba, rootDiagUnit_one]; rfl)

end Faithful

end NoOffE6Three

end CFSG.StandardType
