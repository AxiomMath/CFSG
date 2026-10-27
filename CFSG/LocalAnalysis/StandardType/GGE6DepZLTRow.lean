module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTHat
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement


theorem tFrame_zl_row {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) (w : Fin 6 → L') (hw : ∀ i, ψ (w i) = D.nb i) :
    ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
      ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) := by
  obtain ⟨q, û, ĥ, hqs, _hqk, hqn, hqV, hqc, hqcl⟩ :=
    tFrame_hat hn hK σ hσ Fr hFr h3 hL hζ hζo hD
  haveI := TwE6DD2.finite_twistedE6Group n
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* twistedE6Group 2 n), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hc hcop => TwE6DD2.exists_section_sc hn E π hπ hc hcop
  have hodd' : ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1 := by
    intro y hy hy2
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h2 : orderOf y ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hy
    have hcop : Nat.Coprime (orderOf y) (Nat.card ψ.ker) :=
      Nat.Coprime.coprime_dvd_left h1 hodd.coprime_two_left
    exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd h2)
  obtain ⟨α, hα, hαs⟩ :=
    StdSubRestU.exists_surjective_of_oddKernel hqs hsplit hψ hker hperf hodd'
  refine ⟨fun i => α (ĥ i), fun i => ?_, ?_⟩
  · rw [hα (ĥ i)]
    exact hqV i
  · have hcomm : ∀ i, ⁅w i, α (ĥ i)⁆ = α (ĥ i) := by
      intro i
      have hz : w i * (α (û i))⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hα (û i), hw i, hqn i, mul_inv_cancel]
      calc ⁅w i, α (ĥ i)⁆
          = ⁅(w i * (α (û i))⁻¹) * α (û i), (1 : L') * α (ĥ i)⁆ := by
            rw [inv_mul_cancel_right, one_mul]
        _ = ⁅α (û i), α (ĥ i)⁆ :=
            CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center
              (hker hz) (Subgroup.one_mem _) _ _
        _ = α (ĥ i) := by
            rw [← map_commutatorElement, hqc i]
    have hfun : (fun i => ⁅w i, α (ĥ i)⁆) = fun i => α (ĥ i) := funext hcomm
    rw [hfun]
    intro y hy
    obtain ⟨u, rfl⟩ := hαs y
    have hu : u ∈ q.ker := by
      rw [MonoidHom.mem_ker, ← hα u]
      exact (MonoidHom.mem_ker).1 hy
    have hrange : α '' Set.range ĥ = Set.range fun i => α (ĥ i) := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ĥ i, ⟨i, rfl⟩, rfl⟩
    have h1 : α u ∈ (Subgroup.closure (Set.range ĥ)).map α := ⟨u, hqcl hu, rfl⟩
    rw [MonoidHom.map_closure, hrange] at h1
    exact h1

end CFSG.StandardType.E6Dep.ZL

end
