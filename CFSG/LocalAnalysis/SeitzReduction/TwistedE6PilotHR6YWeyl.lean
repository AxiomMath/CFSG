module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6YBasic
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint RootSpace

local instance twistedE6PilotHR6YWeylNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotHR6YWeylNeZero' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

theorem coeff_eq_of_dvd {Q x0 y0 x5 y5 : ℤ} (hQ : 4 ≤ Q) (hx0 : -1 ≤ x0 ∧ x0 ≤ 1)
    (hy0 : -1 ≤ y0 ∧ y0 ≤ 1) (hx5 : -1 ≤ x5 ∧ x5 ≤ 1) (hy5 : -1 ≤ y5 ∧ y5 ≤ 1)
    (h : (Q ^ 2 - 1) ∣ (Q * (x0 + Q * y0) - (x5 + Q * y5))) : x5 = y0 ∧ y5 = x0 := by
  obtain ⟨m, hm⟩ := h
  have hZ : Q * (x0 - y5) + (y0 - x5) = (Q ^ 2 - 1) * (m - y0) := by linear_combination hm
  have hm0 : m - y0 = 0 := by
    rcases lt_trichotomy (m - y0) 0 with hlt | heq | hgt
    · exfalso
      have h1 : m - y0 ≤ -1 := by omega
      have h2 : 0 ≤ Q ^ 2 - 1 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      nlinarith
    · exact heq
    · exfalso
      have h1 : 1 ≤ m - y0 := by omega
      have h2 : 0 ≤ Q ^ 2 - 1 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      nlinarith
  rw [hm0, mul_zero] at hZ
  have hd : x0 - y5 = 0 := by
    rcases lt_trichotomy (x0 - y5) 0 with hlt | heq | hgt
    · exfalso
      have : Q * (x0 - y5) ≤ -Q := by nlinarith
      omega
    · exact heq
    · exfalso
      have : Q * (x0 - y5) ≥ Q := by nlinarith
      omega
  rw [hd, mul_zero, zero_add] at hZ
  omega

@[expose] def shortV : Fin Tag.E6.rank → ℤ := (![2, 2, 3, 4, 3, 2] : Fin 6 → ℤ)

theorem shortV_check :
    (∀ δ ∈ rootFinset .E6, iform shortV δ = δ 0 + δ 5) ∧
      (∀ j : Fin 6, iform shortV (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        (Pi.single j 1 : Fin 6 → ℤ) 0 + (Pi.single j 1 : Fin 6 → ℤ) 5) := by
  decide +kernel

@[expose] def classVec : Fin Tag.E6.rank → ℤ := (![1, 0, -1, 0, 1, -1] : Fin 6 → ℤ)

theorem classVec_cartan : ∀ i : Fin Tag.E6.rank, (∑ j, classVec j * Tag.E6.cartan i j) % 3 = 0 := by
  decide

@[expose] noncomputable def psiW (u : WeylGroup .E6) : ℤ :=
  ∑ j, classVec j * (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0

theorem psiW_mul_simple (u : WeylGroup .E6) (i : Fin Tag.E6.rank) :
    psiW (u * simple .E6 i) =
      psiW u - (∑ j, classVec j * Tag.E6.cartan i j) * (u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 0 := by
  have h : ∀ j, ((u * simple .E6 i) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 =
      (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 -
        Tag.E6.cartan i j * (u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 0 := by
    intro j
    rw [mul_smul, simple_smul, reflect]
    have hs : (∑ l, Tag.E6.cartan i l * (Pi.single j 1 : Fin Tag.E6.rank → ℤ) l) =
        Tag.E6.cartan i j := by
      simp [Pi.single_apply]
    rw [hs, smul_sub, Pi.sub_apply]
    have hz : u • (Tag.E6.cartan i j • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
        Tag.E6.cartan i j • (u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      map_zsmul (DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) u) _ _
    rw [hz, Pi.smul_apply, smul_eq_mul]
  simp only [psiW, h, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem psiW_emod (u : WeylGroup .E6) : psiW u % 3 = 1 := by
  induction u using (coxeterSystem .E6).simple_induction_right with
  | one =>
    change (∑ j, classVec j * ((1 : WeylGroup .E6) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0)
      % 3 = 1
    simp only [one_smul]
    decide
  | mul_simple_right w i ih =>
    rw [psiW_mul_simple]
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (classVec_cartan i)
    rw [hm]
    have e : psiW w - 3 * m * (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 0 =
        psiW w - 3 * (m * (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 0) := by ring
    rw [e]
    omega

section Main


variable {f : ℕ} {K : Type} [Field K]

theorem mem_setD_iff' : ∀ j : Fin Tag.E6.rank, j ∈ setD ↔ j ≠ 0 ∧ j ≠ 5 := by
  intro j
  revert j
  change ∀ j : Fin 6, j ∈ setD ↔ j ≠ 0 ∧ j ≠ 5
  intro j
  fin_cases j <;> simp [setD]

theorem sum_classVec (g : Fin Tag.E6.rank → ℤ) :
    ∑ j, classVec j * g j = g 0 - g 2 + g 4 - g 5 := by
  change ∑ j : Fin 6, classVec j * g j = g (0 : Fin 6) - g (2 : Fin 6) + g (4 : Fin 6) - g (5 : Fin 6)
  simp only [Fin.sum_univ_six, classVec]
  simp
  ring

theorem mem_kernelReflectionGroup_of_coeff {μ : Kˣ}
    (hμ : 3 ≤ orderOf μ) {u : WeylGroup .E6} (hu : u ∈ rootCharStabilizer (d4CentralDiag μ μ))
    (h05 : (u • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 =
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5)
    (h55 : (u • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5 =
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0) :
    u ∈ kernelReflectionGroup (d4CentralDiag μ μ) := by
  have hker : rootCharKernel (d4CentralDiag μ μ) = parabolicRoots .E6 setD :=
    rootCharKernel_w1Diag hμ
  have hroot : ∀ j, IsRoot .E6 (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
    fun j => IsRoot.smul (isRoot_single .E6 j) u
  have hD : ∀ j : Fin Tag.E6.rank, j ∈ setD →
      (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 = 0 ∧
        (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 5 = 0 := by
    intro j hj
    obtain ⟨hj0, hj5⟩ := (mem_setD_iff' j).1 hj
    have hj' : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel (d4CentralDiag μ μ) := by
      rw [hker, mem_parabolicRoots_setD_iff]
      exact ⟨isRoot_single .E6 j, Pi.single_eq_of_ne (Ne.symm hj0) 1,
        Pi.single_eq_of_ne (Ne.symm hj5) 1⟩
    have hu' : u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        rootCharKernel (d4CentralDiag μ μ) := ⟨IsRoot.smul hj'.1 u, (hu _).trans hj'.2⟩
    rw [hker, mem_parabolicRoots_setD_iff] at hu'
    exact ⟨hu'.2.1, hu'.2.2⟩
  have h2 : (2 : Fin Tag.E6.rank) ∈ setD := (mem_setD_iff' 2).2 ⟨by decide, by decide⟩
  have h4 : (4 : Fin Tag.E6.rank) ∈ setD := (mem_setD_iff' 4).2 ⟨by decide, by decide⟩
  have bx0 : -1 ≤ (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 ∧
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 ≤ 1 := coeff_zero_bound (hroot 0)
  have by0 : -1 ≤ (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 ∧
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 ≤ 1 := coeff_five_bound (hroot 0)
  have hψ := psiW_emod u
  rw [psiW, sum_classVec, (hD 2 h2).1, (hD 4 h4).1, h05] at hψ
  have hWa := hu (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)
  rw [rootChar_d4CentralDiag, rootChar_d4CentralDiag] at hWa
  have e1 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) 0 = 1 := Pi.single_eq_same _ _
  have e5 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) 5 = 0 := Pi.single_eq_of_ne (by decide) _
  rw [e1, e5, zpow_one, zpow_zero, mul_one, ← zpow_add] at hWa
  have hWa' : μ ^ ((u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 - 1) = 1 := by
    rw [zpow_sub, zpow_one, hWa, mul_inv_cancel]
  have hz := eq_zero_of_zpow_eq_one_of_three_le hμ ⟨by omega, by omega⟩ hWa'
  have hx0 : (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 = 1 ∧
      (u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 = 0 := by omega
  have hV : ∀ j : Fin Tag.E6.rank, iform shortV (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
      iform shortV (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    intro j
    rw [shortV_check.1 _ (mem_rootFinset.2 (hroot j)), shortV_check.2 j]
    by_cases hj0 : j = 0
    · subst hj0
      rw [hx0.1, hx0.2]
      decide
    by_cases hj5 : j = 5
    · subst hj5
      rw [h05, h55, hx0.1, hx0.2]
      decide
    · have hjD : j ∈ setD := (mem_setD_iff' j).2 ⟨hj0, hj5⟩
      rw [(hD j hjD).1, (hD j hjD).2]
      have e0 : (Pi.single j 1 : Fin 6 → ℤ) 0 = 0 := Pi.single_eq_of_ne (Ne.symm hj0) _
      have e5 : (Pi.single j 1 : Fin 6 → ℤ) 5 = 0 := Pi.single_eq_of_ne (Ne.symm hj5) _
      rw [e0, e5]
  have huV : u • shortV = shortV := F4Pilot.smul_eq_self_of_iform_smul_single hV
  have hstab : u ∈ weylStabilizer .E6 (ofLattice shortV) := by
    change weylAct .E6 u (ofLattice shortV) = ofLattice shortV
    rw [weylAct_ofLattice, huV]
  obtain ⟨cc, hcc, hform⟩ := (exceptional_Lang_Weyl_chamber_point_stabilizers .E6).1
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E6).2.2.2.2.2 (ofLattice shortV)]
    at hstab
  refine (Subgroup.closure_le _).2 ?_ hstab
  rintro _ ⟨α, hα, hinner, rfl⟩
  have hiform : ((iform α shortV : ℤ) : ℝ) =
      ∑ i, ∑ j, (ofLattice α) i * ((Tag.E6.symmetrizedCartan i j : ℤ) : ℝ) *
        (ofLattice shortV) j := by
    simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]
  rw [hform, ← hiform] at hinner
  have h0 : iform α shortV = 0 := by
    have : ((iform α shortV : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.1 hinner with h | h
      · exact absurd h hcc.ne'
      · exact h
    exact_mod_cast this
  have hαker : α ∈ rootCharKernel (d4CentralDiag μ μ) := by
    rw [hker, mem_parabolicRoots_setD_iff]
    have e := shortV_check.1 α (mem_rootFinset.2 hα)
    rw [iform_comm, h0] at e
    exact ⟨hα, coeff_zero_five_eq_zero hα e.symm⟩
  obtain ⟨u', j, huj⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [rootReflection_eq_conj huj]
  exact Subgroup.subset_closure ⟨u', j, huj ▸ hαker, rfl⟩


theorem twistHom_eq_of_conj {t : TwistTag} {σ : K →+* K} {g d d' : ModGL t.tag K}
    (hgd : g * d * g⁻¹ = d') (hg : twistHom t K σ g = g) (hd : twistHom t K σ d = d) :
    twistHom t K σ d' = d' := by
  rw [← hgd, map_mul, map_mul, map_inv, hg, hd]

theorem mem_toralRootGroup_of_twistHom_eq (hf2 : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {μ : Kˣ} (hμ : 3 ≤ orderOf μ)
    {g : ModGL Tag.E6 K} (hg : g ∈ toralCentralizer .E6 K (d4CentralDiag μ μ))
    (hF : twistHom TwistTag.E6 K σ g = g) :
    g ∈ toralRootGroup .E6 K (d4CentralDiag μ μ) := by
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have hσσ : ∀ c, σ (σ c) = c := apply_apply_eq hK hσ
  have hker : rootCharKernel (d4CentralDiag μ μ) = parabolicRoots .E6 setD :=
    rootCharKernel_w1Diag hμ
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K (d4CentralDiag μ μ)).1 g hg
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  set ζ' := Units.map σ.toMonoidHom ζ with hζ'def
  have hζ'q : ζ' = ζ ^ (2 ^ f) := Units.ext (by
    rw [hζ'def, Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ _)
  have hσζ' : Units.map σ.toMonoidHom ζ' = ζ := Units.ext (by
    rw [hζ'def, Units.coe_map, Units.coe_map]
    exact hσσ _)
  set b₀ := d4CentralDiag ζ ζ' with hb₀
  have hF0 : twistHom TwistTag.E6 K σ (rootDiagUnit Tag.E6 b₀) = rootDiagUnit Tag.E6 b₀ := by
    rw [hb₀, twistHom_rootDiagUnit_d4CentralDiag, hσζ']
  have hwinv : w⁻¹ ∈ rootCharStabilizer (d4CentralDiag μ μ) :=
    (rootCharStabilizerSubgroup (d4CentralDiag μ μ)).inv_mem hw
  set b' := weylTuple w b₀ with hb'
  have hker0 : rootCharKernel (d4CentralDiag μ μ) ⊆ rootCharKernel b₀ := by
    rw [hker]
    exact parabolicRoots_setD_subset_rootCharKernel ζ ζ'
  have hker' : rootCharKernel (d4CentralDiag μ μ) ⊆ rootCharKernel b' := by
    intro δ hδ
    refine ⟨hδ.1, ?_⟩
    rw [hb', rootChar_weylTuple]
    have h1 : w⁻¹ • δ ∈ rootCharKernel (d4CentralDiag μ μ) :=
      ⟨IsRoot.smul hδ.1 _, (hwinv δ).trans hδ.2⟩
    exact (hker0 h1).2
  have hconj := canonicalRep_conj_rootDiagUnit (K := K) w b₀
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  have hvd : v * rootDiagUnit .E6 b₀ = rootDiagUnit .E6 b₀ * v :=
    mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer b₀ (Set.inter_subset_left.trans hker0) hv)
  have hud : u * rootDiagUnit .E6 b' = rootDiagUnit .E6 b' * u :=
    mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer b' (Set.inter_subset_left.trans hker') hu)
  have hhd : rootDiagUnit .E6 b' * h = h * rootDiagUnit .E6 b' :=
    rootDiagUnit_mul_comm_of_mem_torusGroup b' hh
  have hgd : (h * u * n * v) * rootDiagUnit .E6 b₀ * (h * u * n * v)⁻¹ =
      rootDiagUnit .E6 b' := by
    calc (h * u * n * v) * rootDiagUnit .E6 b₀ * (h * u * n * v)⁻¹ =
          h * u * (n * (v * rootDiagUnit .E6 b₀ * v⁻¹) * n⁻¹) * u⁻¹ * h⁻¹ := by group
      _ = h * u * (n * rootDiagUnit .E6 b₀ * n⁻¹) * u⁻¹ * h⁻¹ := by
          rw [hvd, mul_inv_cancel_right]
      _ = h * (u * rootDiagUnit .E6 b' * u⁻¹) * h⁻¹ := by rw [hconj, ← hb']; group
      _ = h * rootDiagUnit .E6 b' * h⁻¹ := by rw [hud, mul_inv_cancel_right]
      _ = rootDiagUnit .E6 b' := by rw [← hhd, mul_inv_cancel_right]
  have hFb' : twistHom TwistTag.E6 K σ (rootDiagUnit Tag.E6 b') = rootDiagUnit Tag.E6 b' :=
    twistHom_eq_of_conj (t := TwistTag.E6) hgd hF hF0
  have hFb'' := (twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := σ) b').symm.trans hFb'
  have hb5 : Units.map σ.toMonoidHom (b' 0) = b' 5 := by
    have h5 := congrFun (rootDiagUnit_injective hFb'') (5 : Fin TwistTag.E6.tag.rank)
    have hs : TwistTag.E6.perm.symm (5 : Fin TwistTag.E6.tag.rank) = 0 := by decide
    rw [hs] at h5
    exact h5
  have hb'j : ∀ j : Fin Tag.E6.rank, b' j =
      ζ ^ ((w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 +
        2 ^ f * (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 5) := by
    intro j
    change rootChar b₀ (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = _
    rw [hb₀, rootChar_d4CentralDiag, hζ'q, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    push_cast
    ring_nf
  rw [hb'j, hb'j, map_zpow, ← hζ'def, hζ'q, ← zpow_natCast, ← zpow_mul] at hb5
  have hone : ζ ^ (((2 ^ f : ℕ) : ℤ) * ((w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
        2 ^ f * (w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5) -
      ((w⁻¹ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 +
        2 ^ f * (w⁻¹ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5)) = 1 := by
    rw [zpow_sub, hb5, mul_inv_cancel]
  have hdvd := (orderOf_dvd_iff_zpow_eq_one (x := ζ)).2 hone
  rw [hζ] at hdvd
  have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  push_cast [Nat.cast_sub hq1] at hdvd
  have hQ : (4 : ℤ) ≤ 2 ^ f := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf2
  have hroot : ∀ j, IsRoot .E6 (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
    fun j => IsRoot.smul (isRoot_single .E6 j) w⁻¹
  obtain ⟨h05, h55⟩ := coeff_eq_of_dvd hQ (coeff_zero_bound (hroot 0)) (coeff_five_bound (hroot 0))
    (coeff_zero_bound (hroot 5)) (coeff_five_bound (hroot 5)) hdvd
  have hkr := mem_kernelReflectionGroup_of_coeff hμ hwinv h05 h55
  have hwk : w ∈ kernelReflectionGroup (d4CentralDiag μ μ) := by
    simpa using (kernelReflectionGroup (d4CentralDiag μ μ)).inv_mem hkr
  have hnM : n ∈ toralRootGroup .E6 K (d4CentralDiag μ μ) := by
    have h1 := kernelReflectionGroup_le_ker (K := K) (d4CentralDiag μ μ)
      (x := ⟨w, hw⟩) (Subgroup.mem_subgroupOf.2 hwk)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have hM : ∀ {S : Set (Fin Tag.E6.rank → ℤ)}, S ⊆ rootCharKernel (d4CentralDiag μ μ) →
      rootSpan .E6 K S ≤ toralRootGroup .E6 K (d4CentralDiag μ μ) := fun hS =>
    (rootSpan_mono hS).trans le_sup_right
  exact mul_mem (mul_mem (mul_mem (le_sup_left (a := torusGroup .E6 K) hh)
    (hM Set.inter_subset_left hu)) hnM) (hM Set.inter_subset_left hv)


end Main

end CFSG.SeitzReduction.TwistedE6Pilot
