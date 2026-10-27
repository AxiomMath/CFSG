module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux1
import CFSG.LocalAnalysis.StandardType.GGQ2OrthType
import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Background.C118BridgeAlg
import CFSG.ClassicalInvolution.SmallCases.Exclusion
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.Monster.Existence.BabyThreeSwapIndex

public section

namespace CFSG.StandardType.CommonJOmPlusTwo

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.StandardType.GGQ2Frame
  CFSG.StandardType.GGQ2Frame.OrthBlocks CFSG.StandardType.GGQ2Frame.PlaneRaw

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem card_le_of_isElemAbelian_omegaQ (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (E : Subgroup ↥(omegaQ (K := K) m 1)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : QuadraticForm K (Fin (m + 1) ⊕ Fin (m + 1) → K) := planeQForm K m 1
  have hQcoe : ⇑Q = planeQ (K := K) m 1 := coe_planeQForm K m 1
  let f : ↥(StatedOmega (planeQ (K := K) m 1)) →* ↥(orthDerived Q) :=
    MonoidHom.codRestrict
      (((toLinEquiv (Fin (m + 1) ⊕ Fin (m + 1)) K).toMonoidHom).comp
        (StatedOmega (planeQ (K := K) m 1)).subtype)
      (orthDerived Q) (fun x => by
        have hx : (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) ∈
            StatedOmega (planeQ (K := K) m 1) := x.2
        have hx' : (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) ∈
            (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
              TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap
                (toLinEquiv (Fin (m + 1) ⊕ Fin (m + 1)) K).toMonoidHom := by
          rwa [← CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQcoe]
        simpa using hx')
  let EΩ : Subgroup ↥(orthDerived Q) := E.map f
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (toLinEquiv (Fin (m + 1) ⊕ Fin (m + 1)) K).injective
    exact congrArg Subtype.val hxy
  have hEΩelem : IsElemAbelian 3 EΩ := TableB.isElemAbelian_map hE f
  have hEΩcard : Nat.card EΩ = Nat.card E := Subgroup.card_map_of_injective hfinj
  haveI : Finite (Fin (m + 1) ⊕ Fin (m + 1) → K) := inferInstance
  haveI : Finite ((Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
      (Fin (m + 1) ⊕ Fin (m + 1) → K)) :=
    Finite.of_injective (fun e : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
      (Fin (m + 1) ⊕ Fin (m + 1) → K) => (e : _ → _))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  haveI : Finite ↥(orthDerived Q) := Subtype.finite
  obtain ⟨M, hEΩM, hMelem, hMmax⟩ := otc_exists_max_isElemAbelian_le hEΩelem
  have hEMcard : Nat.card EΩ ≤ Nat.card M := hMmax EΩ le_rfl hEΩelem
  have hMsc := otc_selfCent_of_max_isElemAbelian hEΩM hMelem hMmax
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    simpa [Q] using nondegenerate_planeQForm (K := K) (t := m) (δ := 1)
  have hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by
    rw [hK]
    norm_num
  have hdim : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hsing : ∃ T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 := by
    simpa [Q] using exists_totallySingular_planeQForm (K := K) (t := m) (δ := 1) (by omega)
  have hchar : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3] := by
    have h := charSum_planeQForm_modEq (K := K) (t := m) (δ := 1) hK
    simpa [Q] using h
  have hbound : Nat.card M ≤ 3 ^ m := by
    by_cases h3 : 3 ^ 3 ≤ Nat.card M
    · have hcardM := ggQ2OrthNonFull_card_of_charSum (Q := Q) (m := m + 1) hnd hpq hdim
        hsing hchar hMelem h3 hMsc
      rw [hcardM, Nat.add_sub_cancel]
    · have hMle : Nat.card M ≤ 3 ^ 3 - 1 := by omega
      have hpow : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  calc Nat.card E = Nat.card EΩ := hEΩcard.symm
    _ ≤ Nat.card M := hEMcard
    _ ≤ 3 ^ m := hbound

theorem ggCommonJOmPlusTwo_selfCent (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) (hme : Even m)
    (T : Subgroup ↥(omegaQ (K := K) m 1)) (hT : IsElemAbelian 3 T)
    (hcard : Nat.card T = 3 ^ m) :
    ∀ g : ↥(omegaQ (K := K) m 1), (∀ e ∈ T, g * e = e * g) → g ^ 3 = 1 → g ∈ T := by
  intro g hgcomm hg3
  by_contra hgT
  have hsup : IsElemAbelian 3 (T ⊔ Subgroup.zpowers g) :=
    hT.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hg3) (fun a ha b hb => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute a g from (hgcomm a ha).symm).zpow_right n).eq)
  have hle : T ≤ T ⊔ Subgroup.zpowers g := le_sup_left
  have hcardle : Nat.card ↥(T ⊔ Subgroup.zpowers g) ≤ Nat.card T := by
    have h := card_le_of_isElemAbelian_omegaQ hK hm (T ⊔ Subgroup.zpowers g) hsup
    rw [← hcard] at h
    exact h
  have heq : T ⊔ Subgroup.zpowers g = T :=
    (Subgroup.eq_of_le_of_card_ge hle hcardle).symm
  have hgK : g ∈ T ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rw [heq] at hgK
  exact hgT hgK

private theorem range_eq_commutator_of_injective (hK : Nat.card K = 2)
    (ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) :
    ζ.range = commutator (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨t, ht, hcomm⟩ := CFSG.Quasithin.exists_commutator_eq_zpowers (F := K) hK'
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
    rw [CFSG.ClassicalInvolution.natCard_specialLinearGroup_fin_two, hK]
    norm_num
  have hz3 : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht]
  have hcommcard : Nat.card (commutator (Matrix.SpecialLinearGroup (Fin 2) K)) = 3 := by
    rw [hcomm, hz3]
  have hζcard : Nat.card ζ.range = 3 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hζ).toEquiv.symm
    rw [h]
    simp
  have hζidx : ζ.range.index = 2 := by
    have h := Subgroup.card_mul_index ζ.range
    rw [hζcard, hSL] at h
    omega
  have hcommidx : (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).index = 2 := by
    have h := Subgroup.card_mul_index (commutator (Matrix.SpecialLinearGroup (Fin 2) K))
    rw [hcommcard, hSL] at h
    omega
  exact CFSG.Monster.Existence.eq_commutator_of_index_eq_two hcommidx hζidx

private theorem exists_otau_eq_of_range_eq {t : ℕ} {δ : Fin 2}
    {ζ ζ' : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (h : ζ.range = ζ'.range) (u : PlaneRaw.V t) :
    ∃ u' : PlaneRaw.V t, otau ζ t δ u = otau ζ' t δ u' := by
  classical
  choose b hb using fun i : Fin t =>
    MonoidHom.mem_range.mp
      (h ▸ (show ζ (Multiplicative.ofAdd (u i)) ∈ ζ.range from ⟨_, rfl⟩))
  refine ⟨fun i => (b i).toAdd, ?_⟩
  have hsp : SpBlocks.tau ζ (t + δ.val) (liftV t δ u) =
      SpBlocks.tau ζ' (t + δ.val) (liftV t δ (fun i => (b i).toAdd)) := by
    apply TorC.spPlaneTorus_eq_of_forall
    intro j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · simpa [liftV, Fin.append_left] using (hb i).symm
    · simp [liftV, Fin.append_right]
  simpa [otau] using congrArg (fun x : ↥(CFSG.Open.StatedSp (t + δ.val) K) =>
    (x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hsp

theorem ggCommonJOmPlusTwo_conj (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) (hme : Even m)
    (T : Subgroup ↥(omegaQ (K := K) m 1)) (hT : IsElemAbelian 3 T)
    (hcard : Nat.card T = 3 ^ m) :
    ∃ α : ↥(omegaQ (K := K) m 1) ≃* ↥(omegaQ (K := K) m 1),
      T = (ggCommonJOmPlusTwo_tau hK m).range.map α.toMonoidHom := by
  classical
  have hsc := ggCommonJOmPlusTwo_selfCent hK hm hme T hT hcard
  obtain ⟨ζ, P, hζ, hPisom, hiff⟩ :=
    orthTorusConj_holds (K := K) m 1 hK (by omega) T hT hsc
  have hζcomm : ζ.range = (otc_zeta K).range := by
    rw [range_eq_commutator_of_injective hK ζ hζ,
      range_eq_commutator_of_injective hK (otc_zeta K) (otc_zeta_injective K)]
  have hiff' : ∀ x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K,
      (∃ a ∈ T, x = P * (a : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * P⁻¹) ↔
        ∃ u : PlaneRaw.V m, x = otau (otc_zeta K) m 1 u := by
    intro x
    rw [hiff x]
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨u', hu'⟩ := exists_otau_eq_of_range_eq hζcomm u
      exact ⟨u', hu'⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨u', hu'⟩ := exists_otau_eq_of_range_eq hζcomm.symm u
      exact ⟨u', hu'⟩
  let ΩH : Subgroup (GL (Fin (m + 1) ⊕ Fin (m + 1)) K) := omegaQ (K := K) m 1
  let O : Subgroup (GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :=
    LargeEvenOrthGroup (planeQ (K := K) m 1)
  have hPO : P ∈ O := by
    rw [show O = LargeEvenOrthGroup (planeQ (K := K) m 1) from rfl, largeEvenOrthGroup_def]
    exact Subgroup.subset_closure (by simpa using hPisom)
  have hmapO : O.map (MulAut.conj P).toMonoidHom ≤ O := by
    rintro y ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using O.mul_mem (O.mul_mem hPO hz) (O.inv_mem hPO)
  have hmapOinv : O.map (MulAut.conj P⁻¹).toMonoidHom ≤ O := by
    rintro y ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using O.mul_mem (O.mul_mem (O.inv_mem hPO) hz) hPO
  have hmapΩ : ΩH.map (MulAut.conj P).toMonoidHom ≤ ΩH := by
    change (LargeEvenOmega (planeQ (K := K) m 1)).map _ ≤ _
    rw [largeEvenOmega_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapO hmapO
  have hmapΩinv : ΩH.map (MulAut.conj P⁻¹).toMonoidHom ≤ ΩH := by
    change (LargeEvenOmega (planeQ (K := K) m 1)).map _ ≤ _
    rw [largeEvenOmega_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapOinv hmapOinv
  have hPnorm : P ∈ Subgroup.normalizer (ΩH : Set (GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hmapΩ ⟨x, hx, rfl⟩, fun hx => by
      have h := hmapΩinv ⟨P * x * P⁻¹, hx, rfl⟩
      change P⁻¹ * (P * x * P⁻¹) * P ∈ ΩH at h
      have hx' : P⁻¹ * (P * x * P⁻¹) * P = x := by group
      rwa [hx'] at h⟩
  have hPinvNorm : P⁻¹ ∈ Subgroup.normalizer
      (ΩH : Set (GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hmapΩinv ⟨x, hx, rfl⟩, fun hx => by
      have h := hmapΩ ⟨P⁻¹ * x * (P⁻¹)⁻¹, hx, rfl⟩
      change P * (P⁻¹ * x * (P⁻¹)⁻¹) * P⁻¹ ∈ ΩH at h
      have hx' : P * (P⁻¹ * x * (P⁻¹)⁻¹) * P⁻¹ = x := by group
      rwa [hx'] at h⟩
  let α : MulAut ↥ΩH := ΩH.normalizerMonoidHom ⟨P⁻¹, hPinvNorm⟩
  have hα : ∀ y : ↥ΩH, (α y : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
      P⁻¹ * (y : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * P := by
    intro y
    rfl
  refine ⟨α, ?_⟩
  apply le_antisymm
  · intro x hx
    have h1 : ∃ u : PlaneRaw.V m, P * (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * P⁻¹ =
        otau (otc_zeta K) m 1 u :=
      (hiff' (P * (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * P⁻¹)).mp ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := h1
    refine Subgroup.mem_map.mpr ⟨ggCommonJOmPlusTwo_tau hK m
      (fun i => Multiplicative.ofAdd (u i)), ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · apply Subtype.ext
      change ((α (ggCommonJOmPlusTwo_tau hK m
          (fun i => Multiplicative.ofAdd (u i))) : ↥ΩH) :
            GL (Fin (m + 1) ⊕ Fin (m + 1)) K) = (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)
      rw [hα]
      have htau : ((ggCommonJOmPlusTwo_tau hK m
          (fun i => Multiplicative.ofAdd (u i)) : ↥ΩH) :
            GL (Fin (m + 1) ⊕ Fin (m + 1)) K) = otau (otc_zeta K) m 1 u := rfl
      rw [htau, ← hu]
      group
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hy
    have hR : ∃ u : PlaneRaw.V m,
        ((ggCommonJOmPlusTwo_tau hK m f : ↥ΩH) : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
          otau (otc_zeta K) m 1 u := ⟨fun i => (f i).toAdd, rfl⟩
    obtain ⟨a, ha, hae⟩ := (hiff' ((ggCommonJOmPlusTwo_tau hK m f : ↥ΩH) :
      GL (Fin (m + 1) ⊕ Fin (m + 1)) K)).mpr hR
    have hx_eq : α (ggCommonJOmPlusTwo_tau hK m f) = a := by
      apply Subtype.ext
      change ((α (ggCommonJOmPlusTwo_tau hK m f) : ↥ΩH) :
        GL (Fin (m + 1) ⊕ Fin (m + 1)) K) = (a : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)
      rw [hα, hae]
      group
    change α (ggCommonJOmPlusTwo_tau hK m f) ∈ T
    rwa [hx_eq]

end CFSG.StandardType.CommonJOmPlusTwo

end
