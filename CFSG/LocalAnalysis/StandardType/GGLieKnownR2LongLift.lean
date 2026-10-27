module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

theorem four_lift_of_odd_central_ker
    {U X : Type} [Group U] [Group X] [Finite X] {ψ : U →* X}
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card ψ.ker)) {S : Subgroup U} (hS : IsPGroup 2 S)
    (hcomm : ⁅pCoreOf 2 (Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X)),
        pCoreOf 2 (Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X))⁆ ≤ S.map ψ)
    (hcent : pCoreOf 2 (Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X)) ≤
      Subgroup.centralizer ((S.map ψ : Subgroup X) : Set X)) :
    ⁅pCoreOf 2 (Subgroup.normalizer (S : Set U)), pCoreOf 2 (Subgroup.normalizer (S : Set U))⁆ ≤
        S ∧
      pCoreOf 2 (Subgroup.normalizer (S : Set U)) ≤ Subgroup.centralizer (S : Set U) := by
  haveI : Finite U := finite_of_odd_card_ker hodd
  set Q : Subgroup U := pCoreOf 2 (Subgroup.normalizer (S : Set U)) with hQ
  set QX : Subgroup X :=
    pCoreOf 2 (Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X)) with hQX
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact GGRootNorm.isPGroup_pCoreOf _
  have hkerN : ψ.ker ≤ Subgroup.normalizer (S : Set U) :=
    hker.trans (Subgroup.center_le_normalizer (S : Set U))
  have hmapN : (Subgroup.normalizer (S : Set U)).map ψ =
      Subgroup.normalizer ((S.map ψ : Subgroup X) : Set X) := by
    rw [map_normalizer_eq_range_inf_normalizer_map hker hodd hS]
    simp [MonoidHom.range_eq_top.mpr hsurj]
  have hmapQ : Q.map ψ = QX := by
    rw [hQ, hQX, map_pCoreOf_eq_of_odd_central_ker hker hodd hkerN, hmapN]
  have hSQ : S ≤ Q := by
    rw [hQ]
    refine GGRootNorm.le_pCoreOf_of_normalized Subgroup.le_normalizer hS ?_
    intro m hm t ht
    exact (Subgroup.mem_normalizer_iff.mp hm t).mp ht
  have hdisj : Q ⊓ ψ.ker = ⊥ := by
    have h2 : IsPGroup 2 (Q ⊓ ψ.ker : Subgroup U) := hQ2.to_inf_left
    have hdvd : Nat.card (Q ⊓ ψ.ker : Subgroup U) ∣ Nat.card ψ.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    have hnot : ¬ 2 ∣ Nat.card (Q ⊓ ψ.ker : Subgroup U) :=
      fun h => hodd.not_two_dvd_nat (h.trans hdvd)
    exact Subgroup.card_eq_one.mp ((h2.card_eq_or_dvd).resolve_right hnot)
  refine ⟨?_, ?_⟩
  · refine Subgroup.commutator_le.mpr fun x hx x' hx' => ?_
    have hψx : ψ x ∈ QX := by
      rw [← hmapQ]
      exact Subgroup.mem_map_of_mem ψ hx
    have hψx' : ψ x' ∈ QX := by
      rw [← hmapQ]
      exact Subgroup.mem_map_of_mem ψ hx'
    have hmem : ψ ⁅x, x'⁆ ∈ S.map ψ := by
      rw [map_commutatorElement]
      exact hcomm (Subgroup.commutator_mem_commutator hψx hψx')
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
    have hker_elt : ⁅x, x'⁆ * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyeq]
      group
    have hcommQ : ⁅x, x'⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx hx') (Q.inv_mem hx)) (Q.inv_mem hx')
    have hQelt : ⁅x, x'⁆ * y⁻¹ ∈ Q := Q.mul_mem hcommQ (Q.inv_mem (hSQ hy))
    have hz : ⁅x, x'⁆ * y⁻¹ ∈ Q ⊓ ψ.ker := ⟨hQelt, hker_elt⟩
    have hone : ⁅x, x'⁆ * y⁻¹ = 1 := by
      have hmem' := hz
      rw [hdisj] at hmem'
      simpa using hmem'
    rw [mul_inv_eq_one.mp hone]
    exact hy
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hψx : ψ x ∈ QX := by
      rw [← hmapQ]
      exact Subgroup.mem_map_of_mem ψ hx
    have hψy : ψ y ∈ S.map ψ := Subgroup.mem_map_of_mem ψ hy
    have h1 : ψ ⁅y, x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hcent hψx)) (ψ y) hψy
    have hker_elt : ⁅y, x⁆ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    have hcommQ : ⁅y, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem (hSQ hy) hx) (Q.inv_mem (hSQ hy)))
        (Q.inv_mem hx)
    have hz : ⁅y, x⁆ ∈ Q ⊓ ψ.ker := ⟨hcommQ, hker_elt⟩
    have hone : ⁅y, x⁆ = 1 := by
      have hmem' := hz
      rw [hdisj] at hmem'
      simpa using hmem'
    exact commutatorElement_eq_one_iff_mul_comm.mp hone

theorem coreFour_long_of_core
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {r : Fin D.rank → ℤ} (hr : r ∈ D.roots)
    (hmax : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) → γ₀ = r)
    (hcf : ⁅pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)),
        pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K))⁆ ≤ D.rootGroup r ∧
      pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ≤
        Subgroup.centralizer (D.rootGroup r : Set K))
    {β : Fin D.rank → ℤ} (hl : GGLongRoot D β) (u : K)
    {Rr Q : Subgroup K}
    (hRr : Rr = ggRootSub D (MonoidHom.id K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set K) := by
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hγ₀ : γ₀ = r := hmax γ₀ hγ₀mem hγ₀max
  have hβr : β = weylAction D.isFiniteType w r := by rw [hβeq, hγ₀]
  set m : K := nrep hct w with hm
  have ham : ActsAs D m w := by rw [hm]; exact actsAs_nrep hct w
  set e : MulAut K := MulAut.conj (u * m) with he
  have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      e.toMonoidHom := by
    ext x
    rw [he]
    change u * (m * x * m⁻¹) * u⁻¹ = (u * m) * x * (u * m)⁻¹
    group
  have hβmap : D.rootGroup β = (D.rootGroup r).map (MulAut.conj m).toMonoidHom := by
    rw [hβr, ← ham r hr]
  have hRrX : Rr = (D.rootGroup r).map e.toMonoidHom := by
    rw [hRr, ggRootSub, Subgroup.map_id, hβmap, Subgroup.map_map, hcomp]
  set Qr : Subgroup K := pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) with hQrdef
  have hQr : Q = Qr.map e.toMonoidHom := by
    rw [hQ, hRrX]
    exact (map_pCoreOf_normalizer_mulEquiv e (D.rootGroup r)).symm
  have hcf' : ⁅Qr, Qr⁆ ≤ D.rootGroup r ∧
      Qr ≤ Subgroup.centralizer (D.rootGroup r : Set K) := hcf
  refine ⟨?_, ?_⟩
  · calc ⁅Q, Q⁆ = ⁅Qr.map e.toMonoidHom, Qr.map e.toMonoidHom⁆ := by rw [hQr]
      _ = (⁅Qr, Qr⁆).map e.toMonoidHom :=
          (Subgroup.map_commutator (H₁ := Qr) (H₂ := Qr) e.toMonoidHom).symm
      _ ≤ (D.rootGroup r).map e.toMonoidHom := Subgroup.map_mono (f := e.toMonoidHom) hcf'.1
      _ = Rr := hRrX.symm
  · calc Q = Qr.map e.toMonoidHom := hQr
      _ ≤ (Subgroup.centralizer (D.rootGroup r : Set K)).map e.toMonoidHom :=
          Subgroup.map_mono (f := e.toMonoidHom) hcf'.2
      _ ≤ Subgroup.centralizer (Rr : Set K) := by
          rw [hRrX]
          exact Subgroup.map_centralizer_le_centralizer_image (D.rootGroup r : Set K)
            e.toMonoidHom

end CFSG.StandardType.LieKnownR2
