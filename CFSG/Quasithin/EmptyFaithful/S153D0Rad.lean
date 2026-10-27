module

public import CFSG.Quasithin.EmptyFaithful.S153D16

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {Yp S I M : Subgroup G}

omit [Finite G] in
theorem conj_mem_sup_of_conj_mem {A B D : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ D) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ D) :
    ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ D := by
  intro x hx
  have : A ⊔ B ≤ D.comap (MulAut.conj g).toMonoidHom := sup_le hA hB
  exact this hx

theorem pCoreOf_sup_eq_inf_centralizerSection (hYI : Yp ≤ I) (hSI : IsSylowTwoOf S I)
    (hSM : S ≤ M) (hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I) :
    pCoreOf 2 (Yp ⊔ S) = S ⊓ centralizerSection (M ⊓ I) Yp (pCoreOf 2 Yp) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Yp ⊔ S) with hR
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hnorm]
    exact inf_le_right
  have hSMI : S ≤ M ⊓ I := le_inf hSM hSI.1
  have hSN : S ≤ Subgroup.normalizer (Yp : Set G) := hSMI.trans hMIN
  have hYSI : Yp ⊔ S ≤ I := sup_le hYI hSI.1
  have hSYS : IsSylowTwoOf S (Yp ⊔ S) := A4.isSylowTwoOf_mono hSI le_sup_right hYSI
  have hRle : R ≤ Yp ⊔ S := pCoreOf_le 2 _
  have hRn : Yp ⊔ S ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
  have hRp : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hRS : R ≤ S :=
    A4.le_of_normal_of_isSylowTwoOf hSYS hRle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mpr hRn) hRp
  have hYR : Yp ⊓ R ≤ pCoreOf 2 Yp :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, hRn (Subgroup.mem_sup_left hg)⟩)
      (hRp.to_le inf_le_right)
  apply le_antisymm
  · refine le_inf hRS ?_
    rw [le_centralizerSection_iff (pCoreOf_le 2 Yp)]
    refine ⟨hRS.trans hSMI, Subgroup.commutator_le.mpr fun y hy r hr => ?_⟩
    have h1 : y * r * y⁻¹ * r⁻¹ ∈ Yp := by
      have e : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
      rw [e]
      exact Yp.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hSN (hRS hr)) y⁻¹).mp (Yp.inv_mem hy))
    have h2 : y * r * y⁻¹ * r⁻¹ ∈ R := by
      refine R.mul_mem ?_ (R.inv_mem hr)
      exact (Subgroup.mem_normalizer_iff.mp (hRn (Subgroup.mem_sup_left hy)) r).mp hr
    exact hYR ⟨h1, h2⟩
  · set C₀ : Subgroup G := S ⊓ centralizerSection (M ⊓ I) Yp (pCoreOf 2 Yp) with hC₀
    have hC₀S : C₀ ≤ S := inf_le_left
    have hC₀cs : C₀ ≤ centralizerSection (M ⊓ I) Yp (pCoreOf 2 Yp) := inf_le_right
    have hC₀N : C₀ ≤ Subgroup.normalizer (pCoreOf 2 Yp : Set G) := fun c hc =>
      normalizer_le_normalizer_pCoreOf 2 Yp (hSN (hC₀S hc))
    have hP2 : IsPGroup 2 (C₀ ⊔ pCoreOf 2 Yp : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (hSI.2.1.to_le hC₀S) (pCoreOf_isPGroup 2 Yp) hC₀N
    have hPle : C₀ ⊔ pCoreOf 2 Yp ≤ Yp ⊔ S :=
      sup_le (hC₀S.trans le_sup_right) ((pCoreOf_le 2 Yp).trans le_sup_left)
    have hYnorm : Yp ≤ Subgroup.normalizer ((C₀ ⊔ pCoreOf 2 Yp : Subgroup G) : Set G) :=
      le_normalizer_of_conj_mem fun g hg x hx => by
        refine conj_mem_sup_of_conj_mem (fun c hc => ?_) (fun o ho => ?_) x hx
        · have h1 : g * c * g⁻¹ * c⁻¹ ∈ pCoreOf 2 Yp := (hC₀cs hc).2.2.2 g hg
          have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hc)
        · exact Subgroup.mem_sup_right
            ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Yp hg) o).mp ho)
    have hSnorm : S ≤ Subgroup.normalizer ((C₀ ⊔ pCoreOf 2 Yp : Subgroup G) : Set G) :=
      le_normalizer_of_conj_mem fun g hg x hx => by
        refine conj_mem_sup_of_conj_mem (fun c hc => ?_) (fun o ho => ?_) x hx
        · refine Subgroup.mem_sup_left ⟨?_, ?_⟩
          · exact S.mul_mem (S.mul_mem hg (hC₀S hc)) (S.inv_mem hg)
          · exact conj_mem_centralizerSection (Subgroup.le_normalizer (hSMI hg)) (hSN hg)
              (normalizer_le_normalizer_pCoreOf 2 Yp (hSN hg)) (hC₀cs hc)
        · exact Subgroup.mem_sup_right
            ((Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 Yp (hSN hg)) o).mp
              ho)
    have hPnorm : Yp ⊔ S ≤ Subgroup.normalizer ((C₀ ⊔ pCoreOf 2 Yp : Subgroup G) : Set G) :=
      sup_le hYnorm hSnorm
    exact le_sup_left.trans (le_pCoreOf_of_le_normalizer 2 hPle hPnorm hP2)

omit [Finite G] in
theorem inf_normalizer_eq {R : Subgroup G} (h : Subgroup.normalizer (R : Set G) ≤ M) :
    I ⊓ Subgroup.normalizer (R : Set G) = (M ⊓ I) ⊓ Subgroup.normalizer (R : Set G) := by
  ext g
  exact ⟨fun hg => ⟨⟨h hg.2, hg.1⟩, hg.2⟩, fun hg => ⟨hg.1.2, hg.2⟩⟩

theorem sylow_radical_of_normalizer_le (hYo : Yp = oTwoUpper Yp) (hYI : Yp ≤ I)
    (hSI : IsSylowTwoOf S I) (hSM : S ≤ M)
    (hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I)
    (hR1 : pCoreOf 2 (Yp ⊔ S) ≠ ⊥)
    (hNR : Subgroup.normalizer ((pCoreOf 2 (Yp ⊔ S) : Subgroup G) : Set G) ≤ M) :
    IsSylowTwoOf (pCoreOf 2 (Yp ⊔ S)) (conjClosure (pCoreOf 2 (Yp ⊔ S)) (M ⊓ I)) ∧
      IsTwoRadicalIn I (pCoreOf 2 (Yp ⊔ S)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hnorm]
    exact inf_le_right
  have hSMI : S ≤ M ⊓ I := le_inf hSM hSI.1
  have hYMI : Yp ≤ M ⊓ I := by
    rw [← hnorm]
    exact le_inf hYI Subgroup.le_normalizer
  have hnormal : (Yp.subgroupOf (M ⊓ I)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYMI).mpr hMIN
  have hSsyl : IsSylowTwoOf S ((M ⊓ I) ⊓ Subgroup.normalizer (Yp : Set G)) := by
    rw [inf_eq_left.mpr hMIN]
    exact A4.isSylowTwoOf_mono hSI hSMI inf_le_right
  have hcs := isSylowTwoOf_inf_centralizerSection hSsyl
  rw [← pCoreOf_sup_eq_inf_centralizerSection hYI hSI hSM hnorm] at hcs
  obtain ⟨h1, h2⟩ := c1_2_four hYo hYMI hnormal hcs hR1
  refine ⟨h1, h2.1.trans inf_le_right |> fun hRI => ⟨hRI, h2.2.1, ?_⟩⟩
  rw [inf_normalizer_eq hNR]
  exact h2.2.2

end S153D

end CFSG.Quasithin
