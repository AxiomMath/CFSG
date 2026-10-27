module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltNorm
import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)

private theorem s168e3_altAct_eq_of_agree_on_S
    {Q : Type} [CommGroup Q] {Hq : Subgroup (MulAut Q)} {S : Subgroup Q} {n : ℕ}
    (hn : 5 ≤ n) (π : alternatingGroup (Fin n) →* ↥Hq)
    (β : ↥S ≃* Multiplicative (altHeart n))
    (hHS : ∀ g : ↥Hq, ∀ u ∈ S, (g : MulAut Q) u ∈ S)
    (hβ : ∀ (γ : alternatingGroup (Fin n)) (u : ↥S)
      (hu : ((π γ : ↥Hq) : MulAut Q) (u : Q) ∈ S),
      β ⟨((π γ : ↥Hq) : MulAut Q) (u : Q), hu⟩ =
        Multiplicative.ofAdd
          (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β u))))
    {γ γ' : alternatingGroup (Fin n)}
    (h : ∀ u : ↥S, ((π γ : ↥Hq) : MulAut Q) (u : Q) =
      ((π γ' : ↥Hq) : MulAut Q) (u : Q)) : γ = γ' := by
  have hact : ∀ v : altHeart n,
      altAct (γ : Equiv.Perm (Fin n)) v = altAct (γ' : Equiv.Perm (Fin n)) v := by
    intro v
    obtain ⟨u, hu⟩ := β.surjective (Multiplicative.ofAdd v)
    have huS : ((π γ : ↥Hq) : MulAut Q) (u : Q) ∈ S := hHS (π γ) (u : Q) u.2
    have huS' : ((π γ' : ↥Hq) : MulAut Q) (u : Q) ∈ S := hHS (π γ') (u : Q) u.2
    have hsub : (⟨((π γ : ↥Hq) : MulAut Q) (u : Q), huS⟩ : ↥S) =
        ⟨((π γ' : ↥Hq) : MulAut Q) (u : Q), huS'⟩ :=
      Subtype.ext (h u)
    have h1 := hβ γ u huS
    have h2 := hβ γ' u huS'
    have hβeq : β ⟨((π γ : ↥Hq) : MulAut Q) (u : Q), huS⟩ =
        β ⟨((π γ' : ↥Hq) : MulAut Q) (u : Q), huS'⟩ := congrArg β hsub
    have hcoord : Multiplicative.ofAdd
          (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β u))) =
        Multiplicative.ofAdd
          (altAct (γ' : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β u))) :=
      h1.symm.trans (hβeq.trans h2)
    have := Multiplicative.ofAdd.injective hcoord
    simpa [hu] using this
  exact Subtype.ext ((CFSG.RankThree.PartTwo.Sec19.SolEven.altAct_eq_iff hn).1 hact)

private theorem s168e3_hq_eq_of_agree_on_S
    {Q : Type} [CommGroup Q] {Hq : Subgroup (MulAut Q)} {S : Subgroup Q} {n : ℕ}
    (hn : 5 ≤ n) (π : alternatingGroup (Fin n) →* ↥Hq) (hπ : Function.Surjective π)
    (β : ↥S ≃* Multiplicative (altHeart n))
    (hHS : ∀ g : ↥Hq, ∀ u ∈ S, (g : MulAut Q) u ∈ S)
    (hβ : ∀ (γ : alternatingGroup (Fin n)) (u : ↥S)
      (hu : ((π γ : ↥Hq) : MulAut Q) (u : Q) ∈ S),
      β ⟨((π γ : ↥Hq) : MulAut Q) (u : Q), hu⟩ =
        Multiplicative.ofAdd
          (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β u))))
    {a b : ↥Hq}
    (h : ∀ u : ↥S, (a : MulAut Q) (u : Q) = (b : MulAut Q) (u : Q)) : a = b := by
  obtain ⟨γ, rfl⟩ := hπ a
  obtain ⟨γ', rfl⟩ := hπ b
  have hγγ : γ = γ' :=
    s168e3_altAct_eq_of_agree_on_S hn π β hHS hβ (fun u => h u)
  rw [hγγ]

theorem s168e3_rank_one_heart_conjugation
    {Q H : Type} [CommGroup Q] [Finite Q] [Group H]
    {Hq : Subgroup (MulAut Q)} {S : Subgroup Q} {n : ℕ}
    (hn : 5 ≤ n) (hQ : ∀ q : Q, q ^ 2 = 1)
    (π : alternatingGroup (Fin n) →* ↥Hq) (hπ : Function.Surjective π)
    (β : ↥S ≃* Multiplicative (altHeart n))
    (hHS : ∀ g : ↥Hq, ∀ u ∈ S, (g : MulAut Q) u ∈ S)
    (hβ : ∀ (γ : alternatingGroup (Fin n)) (u : ↥S)
      (hu : ((π γ : ↥Hq) : MulAut Q) (u : Q) ∈ S),
      β ⟨((π γ : ↥Hq) : MulAut Q) (u : Q), hu⟩ =
        Multiplicative.ofAdd
          (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β u))))
    (theta : H →* ↥Hq) (htheta : Function.Bijective theta)
    (δ : H →* H) (τ : MulAut Q)
    (hTheta : ∀ h : H,
      (theta (δ h) : MulAut Q) = τ * (theta h : MulAut Q) * τ⁻¹)
    (hN : Hq.map (MulAut.conj τ).toMonoidHom = Hq)
    (hτS : S.map τ.toMonoidHom = S)
    (hRank : E3.mQuot S (S ⊓ fixV (Subgroup.zpowers τ)) = 1) :
    ∃ (σ : Equiv.Perm (Fin n)) (p : alternatingGroup (Fin n) ≃* H),
      σ.IsSwap ∧ Equiv.Perm.sign σ = -1 ∧
      (∀ (u : ↥S) (hτu : τ (u : Q) ∈ S),
        Multiplicative.toAdd (β ⟨τ (u : Q), hτu⟩) =
          altAct σ (Multiplicative.toAdd (β u))) ∧
      (∀ γ : alternatingGroup (Fin n), theta (p γ) = π γ) ∧
      ∀ γ : alternatingGroup (Fin n),
        δ (p γ) = p (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ γ) := by
  classical
  have hτ_mem : ∀ u : Q, u ∈ S → τ u ∈ S := by
    intro u hu
    have h : τ u ∈ S.map τ.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [hτS] at h
  have hτinv_mem : ∀ u : Q, u ∈ S → τ⁻¹ u ∈ S := by
    intro u hu
    have h : u ∈ S.map τ.toMonoidHom := by rw [hτS]; exact hu
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.mp h
    have h' : τ⁻¹ ((MulEquiv.toMonoidHom τ) s) = s := by
      change τ⁻¹ (τ s) = s
      exact MulAut.inv_apply_self Q τ s
    rw [← hsu, h']
    exact hs
  let F : Subgroup Q := fixV (Subgroup.zpowers τ)
  let J : Subgroup Q := S ⊓ F
  have hRankJ : E3.mQuot S J = 1 := hRank
  have hsq : ∀ v : ↥S, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hQ (v : Q))
  have hP : IsPGroup 2 ↥S := CFSG.Quasithin.isPGroup_two_of_sq_eq_one hsq
  have hJindex : (J.subgroupOf S).index = 2 := by
    have h := E3.relIndex_eq_two_pow hP J
    rw [hRankJ, pow_one] at h
    exact h
  have hJfixed : ∀ e ∈ J, τ e = e := fun e he =>
    (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 he.2
  obtain ⟨K, hKindex, hKmem⟩ := s16c167_exists_hyperplane hQ hRankJ β
  have hDisplacement : ∀ e ∈ S, τ e * e⁻¹ ∈ J := by
    intro e he
    have hτeS : τ e ∈ S := hτ_mem e he
    have hiffS : τ e ∈ J ↔ e ∈ J := by
      constructor
      · intro hτeJ
        have hfix : τ (τ e) = τ e :=
          (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 hτeJ.2
        have hτee : τ e = e := τ.injective hfix
        exact ⟨he, (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).2 hτee⟩
      · intro heJ
        have hfixe : τ e = e := (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 heJ.2
        refine ⟨hτeS, (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).2 ?_⟩
        simp [hfixe]
    have hinv : e⁻¹ ∈ J ↔ e ∈ J := Subgroup.inv_mem_iff J
    have hiff : (⟨τ e, hτeS⟩ ∈ J.subgroupOf S) ↔
        (⟨e⁻¹, S.inv_mem he⟩ ∈ J.subgroupOf S) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hiffS, hinv]
    have hmem : (⟨τ e, hτeS⟩ * ⟨e⁻¹, S.inv_mem he⟩) ∈ J.subgroupOf S :=
      (Subgroup.mul_mem_iff_of_index_two (H := J.subgroupOf S) hJindex).2 hiff
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa using this
  obtain ⟨t, htβ, htnorm, htK, htT⟩ :=
    s16c167_altNatural_transvection hπ hβ hHS hN hτS hKmem hJfixed hDisplacement
  have hTne : t ≠ AddEquiv.refl (altHeart n) := by
    intro ht1
    have hfixS : ∀ u : ↥S, τ (u : Q) = (u : Q) := by
      intro u
      have hτuS : τ (u : Q) ∈ S := hτ_mem (u : Q) u.2
      have h1 : Multiplicative.toAdd (β ⟨τ (u : Q), hτuS⟩) =
          Multiplicative.toAdd (β u) := by
        have h2 := htβ (u : Q) u.2 hτuS
        rw [ht1] at h2
        simpa using h2
      have h2 : β ⟨τ (u : Q), hτuS⟩ = β u :=
        Multiplicative.ofAdd.injective (by simpa using h1)
      exact congrArg Subtype.val (β.injective h2)
    have htop : J.subgroupOf S = ⊤ := by
      apply le_antisymm le_top
      intro x _
      exact Subgroup.mem_subgroupOf.2
        ⟨x.2, (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).2 (hfixS x)⟩
    rw [htop, Subgroup.index_top] at hJindex
    omega
  obtain ⟨σ, hσswap, hσact, -⟩ :=
    s16c167_altHeart_transvection_eq_swap hn t htnorm hKindex htK htT hTne
  have hσsign : Equiv.Perm.sign σ = -1 := hσswap.sign_eq
  have hτβ : ∀ (u : ↥S) (hτu : τ (u : Q) ∈ S),
      Multiplicative.toAdd (β ⟨τ (u : Q), hτu⟩) =
        altAct σ (Multiplicative.toAdd (β u)) := by
    intro u hτu
    rw [htβ (u : Q) u.2 hτu, hσact]
  have hπinj : Function.Injective π := by
    intro γ γ' hγγ'
    exact s168e3_altAct_eq_of_agree_on_S hn π β hHS hβ
      (fun u => by rw [hγγ'])
  let eTheta : H ≃* ↥Hq := MulEquiv.ofBijective theta htheta
  let pbar : alternatingGroup (Fin n) ≃* ↥Hq := MulEquiv.ofBijective π ⟨hπinj, hπ⟩
  let p : alternatingGroup (Fin n) ≃* H := pbar.trans eTheta.symm
  have hp : ∀ γ : alternatingGroup (Fin n), theta (p γ) = π γ := by
    intro γ
    have hbar : pbar γ = π γ := MulEquiv.ofBijective_apply π ⟨hπinj, hπ⟩ γ
    have h1 : p γ = eTheta.symm (π γ) := by
      calc p γ = eTheta.symm (pbar γ) := rfl
        _ = eTheta.symm (π γ) := by rw [hbar]
    rw [h1]
    have h2 : eTheta (eTheta.symm (π γ)) = π γ := eTheta.apply_symm_apply (π γ)
    rw [show eTheta (eTheta.symm (π γ)) =
        theta (eTheta.symm (π γ)) from rfl] at h2
    exact h2
  have hfaith : ∀ {a b : ↥Hq},
      (∀ u : ↥S, (a : MulAut Q) (u : Q) = (b : MulAut Q) (u : Q)) → a = b :=
    fun {a b} h => s168e3_hq_eq_of_agree_on_S hn π hπ β hHS hβ h
  refine ⟨σ, p, hσswap, hσsign, hτβ, hp, ?_⟩
  intro γ
  let κ : MulAut (alternatingGroup (Fin n)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin n)) σ
  have hcomp : ∀ (u : Q) (hu : u ∈ S),
      τ (((π γ : ↥Hq) : MulAut Q) u) =
        ((π (κ γ) : ↥Hq) : MulAut Q) (τ u) := by
    intro u hu
    have hxS : ((π γ : ↥Hq) : MulAut Q) u ∈ S := hHS (π γ) u hu
    have htxS : τ (((π γ : ↥Hq) : MulAut Q) u) ∈ S := hτ_mem _ hxS
    have hτuS : τ u ∈ S := hτ_mem u hu
    have hκτuS : ((π (κ γ) : ↥Hq) : MulAut Q) (τ u) ∈ S :=
      hHS (π (κ γ)) (τ u) hτuS
    have hβx : β ⟨((π γ : ↥Hq) : MulAut Q) u, hxS⟩ =
        Multiplicative.ofAdd
          (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β ⟨u, hu⟩))) :=
      hβ γ ⟨u, hu⟩ hxS
    have hβτu : β ⟨τ u, hτuS⟩ =
        Multiplicative.ofAdd
          (altAct σ (Multiplicative.toAdd (β ⟨u, hu⟩))) :=
      hτβ ⟨u, hu⟩ hτuS
    have hβτx : Multiplicative.toAdd
          (β ⟨τ (((π γ : ↥Hq) : MulAut Q) u), htxS⟩) =
        t (Multiplicative.toAdd
          (β ⟨((π γ : ↥Hq) : MulAut Q) u, hxS⟩)) :=
      htβ _ hxS htxS
    have hβκ : Multiplicative.toAdd
          (β ⟨((π (κ γ) : ↥Hq) : MulAut Q) (τ u), hκτuS⟩) =
        altAct ((κ γ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β ⟨τ u, hτuS⟩)) := by
      have h3 := hβ (κ γ) ⟨τ u, hτuS⟩ hκτuS
      simpa using congrArg Multiplicative.toAdd h3
    have hκval : ((κ γ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (γ : Equiv.Perm (Fin n)) * σ⁻¹ := MulAut.conjNormal_apply σ γ
    have hconj : altAct ((κ γ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
          (altAct σ (Multiplicative.toAdd (β ⟨u, hu⟩))) =
        altAct σ (altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β ⟨u, hu⟩))) := by
      rw [hκval, CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_mul,
        CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_mul,
        CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_inv_apply]
    have hleft : Multiplicative.toAdd
          (β ⟨τ (((π γ : ↥Hq) : MulAut Q) u), htxS⟩) =
        altAct σ (altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β ⟨u, hu⟩))) := by
      rw [hβτx, hσact, hβx, toAdd_ofAdd]
    have hright : Multiplicative.toAdd
          (β ⟨((π (κ γ) : ↥Hq) : MulAut Q) (τ u), hκτuS⟩) =
        altAct σ (altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β ⟨u, hu⟩))) := by
      rw [hβκ, hβτu, toAdd_ofAdd]
      exact hconj
    have hβeq : β ⟨τ (((π γ : ↥Hq) : MulAut Q) u), htxS⟩ =
        β ⟨((π (κ γ) : ↥Hq) : MulAut Q) (τ u), hκτuS⟩ :=
      Multiplicative.ofAdd.injective (hleft.trans hright.symm)
    exact congrArg Subtype.val (β.injective hβeq)
  have hmem : τ * (π γ : MulAut Q) * τ⁻¹ ∈ Hq := by
    have hconj : MulAut.conj τ (π γ : MulAut Q) ∈ Hq := by
      have h : MulAut.conj τ (π γ : MulAut Q) ∈
          Hq.map (MulAut.conj τ).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(π γ : MulAut Q), (π γ).2, rfl⟩
      rw [hN] at h
      exact h
    simpa [MulAut.conj_apply] using hconj
  have hκeq : (⟨τ * (π γ : MulAut Q) * τ⁻¹, hmem⟩ : ↥Hq) = π (κ γ) := by
    apply hfaith
    intro u
    have h := hcomp (τ⁻¹ (u : Q)) (hτinv_mem (u : Q) u.2)
    have happ : τ (τ⁻¹ (u : Q)) = (u : Q) := MulAut.apply_inv_self Q τ (u : Q)
    simpa [MulAut.mul_apply, happ] using h
  have htheta_delta : theta (δ (p γ)) =
      (⟨τ * (π γ : MulAut Q) * τ⁻¹, hmem⟩ : ↥Hq) := by
    apply Subtype.ext
    rw [hTheta (p γ), hp γ]
  have hEq : theta (δ (p γ)) = theta (p (κ γ)) := by
    rw [htheta_delta, hκeq]
    exact (hp (κ γ)).symm
  exact htheta.injective hEq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
