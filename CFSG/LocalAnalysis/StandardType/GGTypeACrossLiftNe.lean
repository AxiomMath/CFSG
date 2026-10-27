module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftRot
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarEnd
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.StandardType.TypeAReflOver

theorem GGFarCtx.permAut_commute_of_commute {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {n : ℕ} {F : Type} [Field F] {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {π π' : Equiv.Perm (Fin (n + 1))}
    (h : Commute (φ₂ (slPerm hC.two π')) (φ₁ (slPerm hC.two π))) :
    hC.permAut₁ π * hC.permAut₂ π' = hC.permAut₂ π' * hC.permAut₁ π := by
  refine MulEquiv.ext fun b => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, GGFarCtx.permAut₁_apply, GGFarCtx.permAut₂_apply]
  have hc : φ₂ (slPerm hC.two π') * φ₁ (slPerm hC.two π) =
      φ₁ (slPerm hC.two π) * φ₂ (slPerm hC.two π') := h.eq
  have hc' : (φ₁ (slPerm hC.two π))⁻¹ * (φ₂ (slPerm hC.two π'))⁻¹ =
      (φ₂ (slPerm hC.two π'))⁻¹ * (φ₁ (slPerm hC.two π))⁻¹ := by
    have h := congrArg Inv.inv hc
    simpa only [_root_.mul_inv_rev] using h
  calc φ₁ (slPerm hC.two π) * (φ₂ (slPerm hC.two π') * (b : G) *
        (φ₂ (slPerm hC.two π'))⁻¹) * (φ₁ (slPerm hC.two π))⁻¹
      = (φ₁ (slPerm hC.two π) * φ₂ (slPerm hC.two π')) * (b : G) *
          ((φ₂ (slPerm hC.two π'))⁻¹ * (φ₁ (slPerm hC.two π))⁻¹) := by group
    _ = (φ₂ (slPerm hC.two π') * φ₁ (slPerm hC.two π)) * (b : G) *
          ((φ₁ (slPerm hC.two π))⁻¹ * (φ₂ (slPerm hC.two π'))⁻¹) := by
        rw [← hc, ← hc']
    _ = φ₂ (slPerm hC.two π') * (φ₁ (slPerm hC.two π) * (b : G) *
          (φ₁ (slPerm hC.two π))⁻¹) * (φ₂ (slPerm hC.two π'))⁻¹ := by group

theorem GGFarCtx.permAut₂_last_commute {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ}
    {F : Type} [Field F] {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hfar : Commute (φ₂ (weylRep n F j)) (φ₁ (weylRep n F i))) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) :
    hC.permAut₂ (Equiv.swap j.castSucc j.succ) * hC.permAut₁ σ =
      hC.permAut₁ σ * hC.permAut₂ (Equiv.swap j.castSucc j.succ) := by
  have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
  have hj0 : j = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  have hn2 : 2 ≤ n := by
    have h := hC.three_le
    omega
  have hfar' : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩))
      (φ₁ (weylRep n F ⟨0, by omega⟩)) := by
    simpa only [hi0, hj0] using hfar
  obtain ⟨s, hs⟩ := exists_slUpperBlockHom_eq_slPerm hC.two hσ
  have hcomm : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩))
      (φ₁ (slUpperBlockHom n F s)) :=
    commute_slUpperBlockHom_of_transvection hn2
      (fun a b hab ha hb c => slCompat_commute hC.two hC.three_le hC.lifts.compat hfar'
        hab ha hb c) s
  have hT : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) (φ₁ (slPerm hC.two σ)) := by
    rw [← hs]
    exact hcomm
  have hmb : Commute (φ₂ (slPerm hC.two (Equiv.swap j.castSucc j.succ)))
      (φ₁ (slPerm hC.two σ)) := by
    rw [slPerm_swap_castSucc_succ hC.two j]
    simpa only [← hj0] using hT
  exact (GGFarCtx.permAut_commute_of_commute hC hmb).symm

theorem GGFarCtx.permAut₂_swap_ne_of_cross {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    {y₃ : G} {K₃ : Subgroup G} (hNC : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hN₃ : GGTypeANbr p B Bs x L D J n f y₃ K₃) (hK₃ : ¬ K₃ ≤ L ⊔ K)
    {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃)
    (hK : φ₂.range = K) (hK₃' : φ₃.range = K₃) (j : Fin n)
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b))) :
    hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) ≠ hX.permAut₂ (Equiv.swap j.castSucc j.succ) := by
  classical
  intro hEq
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hyfix : ∀ τ : Equiv.Perm (Fin (n + 1)),
      hX.permAut₂ τ ⟨y, hX.y_mem⟩ = ⟨y, hX.y_mem⟩ := by
    intro τ
    apply Subtype.ext
    rw [GGFarCtx.permAut₂_apply, ← hX.y_comm (slPerm hX.two τ)]
    group
  have hy₃fix : ∀ τ : Equiv.Perm (Fin (n + 1)),
      hX₃.permAut₂ τ ⟨y₃, hX₃.y_mem⟩ = ⟨y₃, hX₃.y_mem⟩ := by
    intro τ
    apply Subtype.ext
    rw [GGFarCtx.permAut₂_apply, ← hX₃.y_comm (slPerm hX₃.two τ)]
    group
  have hperm₁ : hX₃.permAut₁ = hX.permAut₁ := rfl
  have hκ₁₃ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX₃.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)) := by
    intro σ b
    rw [hperm₁]
    exact hκ₁ σ b
  have hy_coord : ∀ a b : Fin n,
      coordPerm p n (Equiv.swap a.succ b.succ) (κ (Additive.ofMul ⟨y, hX.y_mem⟩)) =
        κ (Additive.ofMul ⟨y, hX.y_mem⟩) := by
    intro a b
    rw [← hκ₁ (Equiv.swap a.succ b.succ) ⟨y, hX.y_mem⟩, hX.permAut_compat a b,
      hyfix (Equiv.swap a.castSucc b.castSucc)]
  have hy_refl : kRefl p n (κ (Additive.ofMul ⟨y, hX.y_mem⟩)) =
      κ (Additive.ofMul ⟨y, hX.y_mem⟩) := by
    rw [← hκ₂ ⟨y, hX.y_mem⟩, hyfix (Equiv.swap j.castSucc j.succ)]
  have hy_single : κ (Additive.ofMul ⟨y, hX.y_mem⟩) =
      Pi.single 0 (κ (Additive.ofMul ⟨y, hX.y_mem⟩) 0) :=
    eq_single_zero_of_fixed _ hy_coord hy_refl
  have hy₃_coord : ∀ a b : Fin n,
      coordPerm p n (Equiv.swap a.succ b.succ) (κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩)) =
        κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) := by
    intro a b
    rw [← hκ₁₃ (Equiv.swap a.succ b.succ) ⟨y₃, hX₃.y_mem⟩, hX₃.permAut_compat a b,
      hy₃fix (Equiv.swap a.castSucc b.castSucc)]
  have hy₃_refl : kRefl p n (κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩)) =
      κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) := by
    rw [← hκ₂ ⟨y₃, hX₃.y_mem⟩, ← hEq, hy₃fix (Equiv.swap j.castSucc j.succ)]
  have hy₃_single : κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) =
      Pi.single 0 (κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) 0) :=
    eq_single_zero_of_fixed _ hy₃_coord hy₃_refl
  have hy_ne_zero : κ (Additive.ofMul ⟨y, hX.y_mem⟩) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y, hX.y_mem⟩ : ↥Bs) = 0 := by
      apply κ.injective
      rw [map_zero]
      exact h0
    exact hX.y_ne (Subtype.ext_iff.mp (ofMul_eq_zero.mp h1))
  have hy0 : κ (Additive.ofMul ⟨y, hX.y_mem⟩) 0 ≠ 0 := by
    intro h0
    exact hy_ne_zero (by rw [hy_single, h0, Pi.single_zero])
  have hy₃_ne_zero : κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y₃, hX₃.y_mem⟩ : ↥Bs) = 0 := by
      apply κ.injective
      rw [map_zero]
      exact h0
    exact hX₃.y_ne (Subtype.ext_iff.mp (ofMul_eq_zero.mp h1))
  have hy₃0 : κ (Additive.ofMul ⟨y₃, hX₃.y_mem⟩) 0 ≠ 0 := by
    intro h0
    exact hy₃_ne_zero (by rw [hy₃_single, h0, Pi.single_zero])
  have mem_zpowers_of_single : ∀ u v : ↥Bs,
      κ (Additive.ofMul u) = Pi.single 0 (κ (Additive.ofMul u) 0) →
      κ (Additive.ofMul v) = Pi.single 0 (κ (Additive.ofMul v) 0) →
      κ (Additive.ofMul u) 0 ≠ 0 → (v : G) ∈ Subgroup.zpowers (u : G) := by
    intro u v hu hv hu0
    set c : ZMod p := κ (Additive.ofMul v) 0 / κ (Additive.ofMul u) 0 with hc
    have hsmul : c • κ (Additive.ofMul u) = κ (Additive.ofMul v) := by
      rw [hu, hv]
      funext i
      by_cases hi : i = 0
      · subst hi
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, hc]
        exact div_mul_cancel₀ _ hu0
      · rw [Pi.smul_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, smul_zero]
    have hpow : Additive.ofMul v = c.val • Additive.ofMul u := by
      apply κ.injective
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val, ZMod.natCast_zmod_val,
        hsmul]
    have hpow' : Additive.ofMul v = Additive.ofMul (u ^ c.val) := by
      rw [hpow, ← ofMul_pow]
    have hv_eq : (v : G) = (u : G) ^ c.val := by
      simpa only [Subgroup.coe_pow] using
        congrArg (fun w : ↥Bs => (w : G)) (Additive.ofMul.injective hpow')
    rw [hv_eq]
    exact Subgroup.npow_mem_zpowers (u : G) c.val
  have hzy₃ : y₃ ∈ Subgroup.zpowers y :=
    mem_zpowers_of_single ⟨y, hX.y_mem⟩ ⟨y₃, hX₃.y_mem⟩ hy_single hy₃_single hy0
  have hzy : y ∈ Subgroup.zpowers y₃ :=
    mem_zpowers_of_single ⟨y₃, hX₃.y_mem⟩ ⟨y, hX.y_mem⟩ hy₃_single hy_single hy₃0
  have hz : Subgroup.zpowers y = Subgroup.zpowers y₃ := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr hzy
    · exact Subgroup.zpowers_le.mpr hzy₃
  have hcent : Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({y₃} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq hz
  have hNC₃ : GGTypeANbrCfg p B Bs x L D J n f y₃ K₃ :=
    ⟨hNC.1, hNC.2.1, hNC.2.2.1, hNC.2.2.2.1, hN₃⟩
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNC.pComponent_K
  have hK₃comp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K₃ := by
    rw [hcent]
    exact hNC₃.pComponent_K
  have hn3 : 3 ≤ n := hX.three_le
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN2 : 2 ≤ N + 1 := by omega
  have hN2' : 2 ≤ N := by omega
  let P : Subgroup G := (φ₁.comp (slLowerBlockHom (N + 1) (GaloisField 2 f))).range
  have hPK : P ≤ K := by
    rw [← hK]
    rintro _ ⟨s, rfl⟩
    exact ⟨slUpperBlockHom (N + 1) (GaloisField 2 f) s, by
      rw [MonoidHom.comp_apply]
      exact (DFunLike.congr_fun hX.lifts.compat s).symm⟩
  have hPK₃ : P ≤ K₃ := by
    rw [← hK₃']
    rintro _ ⟨s, rfl⟩
    exact ⟨slUpperBlockHom (N + 1) (GaloisField 2 f) s, by
      rw [MonoidHom.comp_apply]
      exact (DFunLike.congr_fun hX₃.lifts.compat s).symm⟩
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin (N + 1)) (GaloisField 2 f)) :=
    slPerfect_of_four_le_card hN2 hNC.four_le_natCard
  have hPperf : P ≤ ⁅P, P⁆ :=
    range_le_commutator_of_isPerfect hperfSL _
  obtain ⟨g, hgP, hg1, hgp⟩ :=
    exists_orderP_mem_lowerLower (F := GaloisField 2 f) (X := G) (p := p)
      hNC.dvd_natCard_units (m := N) hN2' hX.lifts.ker₁
  have hgP' : g ∈ P := by
    obtain ⟨s, hs⟩ := hgP
    exact ⟨slLowerBlockHom N (GaloisField 2 f) s, hs⟩
  have hKeq : K = K₃ :=
    eq_of_pComponents_of_perfect_common hKcomp hK₃comp hPK hPK₃ hPperf hgP' hg1 hgp
  exact hK₃ (by rw [← hKeq]; exact le_sup_right)

end CFSG.StandardType

end
