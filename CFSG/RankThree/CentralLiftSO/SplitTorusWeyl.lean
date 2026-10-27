module

public import CFSG.RankThree.CentralLiftSO.SplitWeyl

public section

namespace CFSG.RankThree.CentralLiftSO.SplitO

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)

theorem odd_split_orthogonal_central_large_prime_faithful_torus_and_weyl {k : Type} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) {r : ℕ} (hr : 3 ≤ r) {E : Type*} [Group E] [Finite E]
    {π : E →* orthElementaryGroup (quadPlus r k)} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    (∀ (i j : Fin r) (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) k),
      ((etaPlus i j hij A : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) =
        cSwap j * (etaMinus i j hij A : (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) *
          cSwap j) ∧
    (∀ (i j : Fin r) (hij : i ≠ j), Function.Injective (etaMinus (k := k) i j hij) ∧
      Function.Injective (etaPlus (k := k) i j hij)) ∧
    (∀ (i j : Fin r) (hij : i ≠ j),
      (∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = etaMinus i j hij) ∧
      (∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = etaPlus i j hij) ∧
      π.comp (etaMinusLift π i j hij) = etaMinus i j hij ∧
      π.comp (etaPlusLift π i j hij) = etaPlus i j hij) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (g g' : SpecialLinearGroup (Fin 2) k),
      Commute (etaMinusLift π i j hij g) (etaPlusLift π i j hij g')) ∧
    (∀ x ∈ hGens π, ∀ y ∈ hGens π, Commute x y) ∧
    (∀ (i j l : Fin r) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : kˣ),
      hMinus π i l hil a = hMinus π i j hij a * hMinus π j l hjl a ∧
        hPlus π i j hij a = hPlus π i l hil a * hMinus π j l hjl a) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (a : kˣ),
      hMinus π j i hij.symm a = hMinus π i j hij a⁻¹ ∧
        hPlus π j i hij.symm a = hPlus π i j hij a) ∧
    (∀ (i : Fin r) (h : i.val + 1 < r) (a : kˣ),
      hSimple π i a = hMinus π i ⟨i.val + 1, h⟩ (ne_succ_of_lt h) a) ∧
    (∀ a : kˣ, hSimple π ⟨r - 1, by omega⟩ a =
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) a) ∧
    (∃ Θ : (Fin r → kˣ) →* E,
      (∀ u, Θ u = (List.ofFn fun i => hSimple π i (u i)).prod) ∧
      Θ.range = liftTorus π ∧
      (∀ u : Fin r → kˣ, ∃ a : Fin r → kˣ,
        ((π (Θ u) : orthElementaryGroup (quadPlus r k)) :
          (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = torusElt r k a ∧
        a ⟨0, by omega⟩ = u ⟨0, by omega⟩ ∧
        (∀ (j : Fin r) (_ : 1 ≤ j.val), j.val + 3 ≤ r →
          a j = (u ⟨j.val - 1, by omega⟩)⁻¹ * u j) ∧
        a ⟨r - 2, by omega⟩ =
          (u ⟨r - 3, by omega⟩)⁻¹ * u ⟨r - 2, by omega⟩ * u ⟨r - 1, by omega⟩ ∧
        a ⟨r - 1, by omega⟩ = (u ⟨r - 2, by omega⟩)⁻¹ * u ⟨r - 1, by omega⟩) ∧
      ((orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp Θ)).range = sqTorus r k) ∧
    liftTorus π ⊓ π.ker =
      Subgroup.zpowers (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) ∧
    (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) ^ 2 = 1 ∧
    Nat.card (liftTorus π ⊓ π.ker : Subgroup E) ≤ 2 ∧
    liftTorus π ≤ liftWeyl π ∧
    liftWeyl π ≤ Subgroup.normalizer (liftTorus π : Set E) ∧
    (∀ i : Fin r, sLift π i ^ 2 ∈ liftTorus π) ∧
    (∀ i : Fin r, ((π (sLift π i) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = (weylElt r k i)⁻¹) ∧
    (∃ hN₀ : ∀ v ∈ liftWeyl π, ((π v : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ torusWeyl r k,
      (∀ (v : E) (hv : v ∈ liftWeyl π) (α : Fin r → ℤ), α ∈ roots r →
        (rootSubgroup r k α).map (MulAut.conj ((π v : orthElementaryGroup (quadPlus r k)) :
            (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))).toMonoidHom =
          rootSubgroup r k (((torusWeylNu r k (by omega) ⟨_, hN₀ v hv⟩ : weylGroup r) :
            (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α)) ∧
      ∃ φ : liftWeyl π →* weylGroup r,
        (∀ v : liftWeyl π, φ v = torusWeylNu r k (by omega) ⟨_, hN₀ v v.2⟩) ∧
        (∀ (v : liftWeyl π) (c : Fin r ⊕ Fin r), ∃ (μ : kˣ) (c' : Fin r ⊕ Fin r),
          ((π v : orthElementaryGroup (quadPlus r k)) :
              (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) (Pi.single c 1) =
              (μ : k) • Pi.single c' 1 ∧
            coordWt c' = ((φ v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (coordWt c)) ∧
        Function.Surjective φ ∧ φ.ker = (liftTorus π).subgroupOf (liftWeyl π) ∧
        ∃ _ : ((liftTorus π).subgroupOf (liftWeyl π)).Normal,
          ∃ e : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* weylGroup r,
            ∀ v : liftWeyl π, e v = φ v) ∧
    hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) = 1 ∧
    hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) *
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) (-1) = 1 ∧
    liftTorus π ⊓ π.ker = ⊥ ∧
    Function.Injective (π.comp (liftTorus π).subtype) ∧
    Function.Injective (π.comp (liftWeyl π).subtype) := by
  have hS : LargeHyp π := ⟨hk, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hr2 : 2 ≤ r := by omega
  have hN := normal_liftTorus_subgroupOf hS hr2
  have hlast : ∀ a : kˣ, hSimple π ⟨r - 1, by omega⟩ a =
      hPlus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) a := by
    intro a
    rw [hSimple_of_not_lt (by simp; omega) (by simp; omega)]
    exact hPlus_congr_left (Fin.ext (by simp; omega)) _ _ a
  have hpen : ∀ a : kˣ, hSimple π ⟨r - 2, by omega⟩ a =
      hMinus π ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ (Fin.ne_of_val_ne (by simp; omega)) a := by
    intro a
    rw [hSimple_of_lt (by simp; omega)]
    congr 1
    exact Fin.ext (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact fun i j hij A => coe_etaPlus hij A
  · exact fun i j hij => ⟨etaMinus_injective hij, etaPlus_injective hij⟩
  · exact fun i j hij => ⟨existsUnique_lift_large hk hS.ext _, existsUnique_lift_large hk hS.ext _,
      comp_sl2Lift_large hk hS.ext _, comp_sl2Lift_large hk hS.ext _⟩
  · exact fun i j hij g g' => commute_etaMinusLift_etaPlusLift hS hij g g'
  · exact fun x hx y hy => commute_of_mem_hGens hS hx hy
  · exact fun i j l hij hjl hil a => ⟨hMinus_trans hS hij hjl hil a, hPlus_trans hS hij hjl hil a⟩
  · exact fun i j hij a => ⟨hMinus_symm hS hij a, hPlus_symm hS hij a⟩
  · exact fun i h a => hSimple_of_lt h a
  · exact hlast
  · exact ⟨thetaHom hS, thetaHom_apply hS, range_thetaHom hS hr2, fun u => ⟨_, coe_pi_thetaHom hS u,
      prod_simpleDiag_zero hr u _ rfl,
      fun j _ hj' => prod_simpleDiag_mid u j _ (by simp; omega) hj',
      prod_simpleDiag_pen u _ _ _ (by simp; omega) (by simp; omega) (by simp; omega),
      prod_simpleDiag_last u _ _ (by simp; omega) (by simp; omega)⟩,
      range_pi_thetaHom hS hr2⟩
  · exact liftTorus_inf_ker hS hr
  · exact epsilon_sq hS hr
  · exact card_liftTorus_inf_ker_le_two hS hr
  · exact liftTorus_le_liftWeyl
  · exact liftWeyl_le_normalizer hS hr2
  · exact sLift_sq_mem
  · exact coe_pi_sLift hS hr2
  · exact ⟨fun v hv => coe_pi_mem_torusWeyl hS hr2 hv,
      fun v hv α hα => map_conj_rootSubgroup_torusWeyl hr2
        ⟨_, coe_pi_mem_torusWeyl hS hr2 hv⟩ hα,
      weylHom hS hr2, fun v => rfl, apply_single_weylHom hS hr2, weylHom_surjective hS hr2 hr,
      ker_weylHom hS hr2, hN, weylQuotientEquiv hS hr2 hr,
      weylQuotientEquiv_mk hS hr2 hr⟩
  · exact epsilon_eq_one hS hr
  · rw [← hpen, ← hlast]
    exact epsilon_eq_one hS hr
  · exact liftTorus_inf_ker_eq_bot hS hr
  · exact injective_pi_liftTorus hS hr
  · exact injective_pi_liftWeyl hS hr

end CFSG.RankThree.CentralLiftSO.SplitO
