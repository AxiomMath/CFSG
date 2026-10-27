module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmShape
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMain

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Block

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem exists_factor_of_mem [Fact p.Prime] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp2 : p ≠ 2)
    (F : SevOm.Frame Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {E J : Subgroup (V ≃ₗ[K] V)} (hEA : E ≤ A)
    (hJ : IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V))))
    {t : Fin r → ZMod p} (ht : F.ι (ofAdd t) ∈ E) :
    ∃ h ∈ primaryFactors (F.ι (ofAdd t)).toLinearMap,
      J ≤ supportedBlock Q (F.ι (ofAdd t)) h ∧
      ∀ m : Fin r, F.ι (ofAdd (Pi.single m 1)) ∉ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) →
        F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap h := by
  classical
  have hp : p.Prime := Fact.out
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    frame_comm F (hEA ha) (hEA hb)
  have hx : OddOrderIsometry Q p (F.ι (ofAdd t)) := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd t)
  obtain ⟨h, hh, hJB⟩ := exists_le_supportedBlock_of_comm hx ht hEc hJ
  refine ⟨h, hh, hJB, fun m hm => ?_⟩
  rcases frame_piece_dichotomy hQ hT hp hp2 F hAΩ hmax (ofAdd t) hh m with h1 | h1
  · exact h1
  · exfalso
    apply hm
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    refine commute_of_triv hx hh (hJB hg) (Subgroup.mem_centralizer_singleton_iff.mpr
      (frame_comm F (F.mem _) (F.mem _))) (frame_triv_orbit F hx hh fun m' hm' => ?_)
    have : m' = m := by
      by_contra hne
      exact hm' (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    rw [this]
    exact h1

theorem eq_X_sub_one_of_apply_eq_zero [Fact p.Prime]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp2 : p ≠ 2) (F : SevOm.Frame Q p A r)
    (hAΩ : A ≤ orthDerived Q) {t : Fin r → ZMod p} {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd t)).toLinearMap) {m : Fin r} (htm : t m = 0)
    (hU : F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap h) : h = X - 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hx : OddOrderIsometry Q p (F.ι (ofAdd t)) := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd t)
  by_contra hX
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot m)
  exact hu0 (eq_zero_of_fix_orbit hx hp hp2 hh hX (hU hu)
    (F.triv (ofAdd t) m (by simpa using htm) u hu))

theorem apply_eq_zero_of_le_orbitSpace_X_sub_one [Fact p.Prime] (F : SevOm.Frame Q p A r)
    {t : Fin r → ZMod p} {m : Fin r}
    (hU : F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap (X - 1)) : t m = 0 := by
  classical
  by_contra h0
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot m)
  have h1 := hU hu
  rw [orbitSpace_X_sub_one] at h1
  exact hu0 (F.fpf (ofAdd t) m (by simpa using h0) u hu (mem_fixedSpace.mp h1))

theorem isComponentOf_centralizer_of_le_block {b : V ≃ₗ[K] V} (hb : OddOrderIsometry Q p b)
    {h : K[X]} (hh : h ∈ primaryFactors b.toLinearMap) {E J : Subgroup (V ≃ₗ[K] V)}
    (hbE : b ∈ E)
    (hJ : IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V))))
    (hJB : J ≤ supportedBlock Q b h)
    (hE : ∀ e ∈ E, ∃ n : ℕ, ∃ y : V ≃ₗ[K] V,
      y ∈ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V)) ∧ e = b ^ n * y ∧
        ∀ u ∈ orbitSpace b.toLinearMap h, y u = u) :
    IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V))) := by
  classical
  have hHEM : orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) ≤
      orthDerived Q ⊓ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V)) :=
    le_inf inf_le_left fun g hg => by
      have hgc : g ∈ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hg).2
      rw [Subgroup.mem_centralizer_iff] at hgc ⊢
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hgc b hbE
  have hNcent : supportedBlock Q b h ⊓ orthDerived Q ≤
      Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨m, y, hyc, heq, hytriv⟩ := hE e he
    have hnB : n ∈ supportedBlock Q b h := (Subgroup.mem_inf.mp hn).1
    have hnb : Commute n b :=
      Subgroup.mem_centralizer_singleton_iff.mp (supportedBlock_le_centralizer h hnB)
    have hny : Commute n y := commute_of_triv hb hh hnB hyc hytriv
    rw [heq]
    exact ((hnb.pow_right m).mul_right hny).symm
  have hNE : supportedBlock Q b h ⊓ orthDerived Q ≤
      orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) :=
    le_inf inf_le_right hNcent
  have hNM : supportedBlock Q b h ⊓ orthDerived Q ≤
      orthDerived Q ⊓ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V)) :=
    le_inf inf_le_right fun n hn => supportedBlock_le_centralizer h (Subgroup.mem_inf.mp hn).1
  have hNsub : IsSubnormal (supportedBlock Q b h ⊓ orthDerived Q)
      (orthDerived Q ⊓ Subgroup.centralizer ({b} : Set (V ≃ₗ[K] V))) :=
    LayerCores.ggSubnormal_of_normal hNM fun u hu s hs => by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact conj_mem_supportedBlock
          (Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (Subgroup.mem_inf.mp hu).1,
            (Subgroup.mem_inf.mp hu).2⟩) (Subgroup.mem_inf.mp hs).1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.mp hu).1
          (Subgroup.mem_inf.mp hs).2) (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hu).1)
  have hJN : J ≤ supportedBlock Q b h ⊓ orthDerived Q :=
    le_inf hJB (hJ.1.trans inf_le_left)
  have hJsubN : IsSubnormal J (supportedBlock Q b h ⊓ orthDerived Q) :=
    ggIsSubnormal_of_le_of_le hJ.2.1 hJN hNE
  exact ⟨hJ.1.trans hHEM, hJsubN.trans hNsub, hJ.2.2⟩

end Block

section Counting

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem card_ge_of_two [Fact p.Prime] (F : SevOm.Frame Q p A r) {H : Subgroup (V ≃ₗ[K] V)}
    [Finite H] {v₁ v₂ : Fin r → ZMod p} (h₁ : F.ι (ofAdd v₁) ∈ H) (h₂ : F.ι (ofAdd v₂) ∈ H)
    {k₁ k₂ : Fin r} (hv₁ : v₁ k₁ ≠ 0) (hv₂ : v₂ k₂ ≠ 0) (h12 : v₁ k₂ = 0) :
    p ^ 2 ≤ Nat.card H := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ a : ZMod p × ZMod p,
      F.ι (ofAdd (a.1 • v₁ + a.2 • v₂)) ∈ H := by
    intro a
    rw [ofAdd_add, map_mul]
    exact H.mul_mem (StepTwoToral.ofAdd_smul_mem h₁ _) (StepTwoToral.ofAdd_smul_mem h₂ _)
  have hinj : Function.Injective fun a : ZMod p × ZMod p => (⟨_, hmem a⟩ : H) := by
    intro a b hab
    have h0 : a.1 • v₁ + a.2 • v₂ = b.1 • v₁ + b.2 • v₂ :=
      ofAdd.injective (F.inj (congrArg Subtype.val hab))
    have e2 := congrFun h0 k₂
    have e1 := congrFun h0 k₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h12, mul_zero, zero_add] at e2
    have hc : a.2 = b.2 := mul_right_cancel₀ hv₂ e2
    rw [hc] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e1
    have ha : a.1 = b.1 := mul_right_cancel₀ hv₁ e1
    exact Prod.ext ha hc
  have hcard : Nat.card (ZMod p × ZMod p) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod]
    ring
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [hcard] at h

theorem exists_ne_zero_apply_eq_zero [Fact p.Prime] (F : SevOm.Frame Q p A r)
    {E : Subgroup (V ≃ₗ[K] V)} (hEA : E ≤ A) (hE : Nat.card E = p ^ 2) (k : Fin r) :
    ∃ t : Fin r → ZMod p, F.ι (ofAdd t) ∈ E ∧ t ≠ 0 ∧ t k = 0 := by
  have hD : E ≤ F.ι.range := by rw [F.range]; exact hEA
  obtain ⟨t, ht0, htk, htE⟩ := StepTwoToral.exists_ne_zero_mem_ker hD hE
    (AddMonoidHom.mk' (fun s : Fin r → ZMod p => s k) fun x y => rfl)
  exact ⟨t, htE, ht0, htk⟩

end Counting

end CoordOm

end CFSG.StandardType
