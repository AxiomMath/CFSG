module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.StandardType Matrix Certificates.A8Nbr476

private theorem a8ka_blk_zero_zero (M : M3) : blk M 0 0 = 1 := by
  simp [blk]

private theorem a8ka_blk_zero_succ (M : M3) (j : Fin 3) : blk M 0 j.succ = 0 := by
  simp [blk]

private theorem a8ka_blk_succ_zero (M : M3) (i : Fin 3) : blk M i.succ 0 = 0 := by
  simp [blk]

private theorem a8ka_blk_succ_succ (M : M3) (i j : Fin 3) : blk M i.succ j.succ = M i j := by
  simp [blk, Fin.pred_succ]

private theorem a8ka_vecMul_blk_zero (v : Fin 4 → ZMod 7) (M : M3) :
    vecMul v (blk M) 0 = v 0 := by
  change (∑ j : Fin 4, v j * blk M j 0) = v 0
  rw [Fin.sum_univ_succ, Fin.sum_univ_three]
  simp only [a8ka_blk_zero_zero, a8ka_blk_succ_zero, a8ka_blk_zero_succ, a8ka_blk_succ_succ]
  ring

private theorem a8ka_vecMul_blk_succ (v : Fin 4 → ZMod 7) (M : M3) (i : Fin 3) :
    vecMul v (blk M) i.succ = vecMul (fun j => v j.succ) M i := by
  change (∑ j : Fin 4, v j * blk M j i.succ) = (∑ j : Fin 3, v j.succ * M j i)
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  simp only [a8ka_blk_zero_zero, a8ka_blk_succ_zero, a8ka_blk_zero_succ, a8ka_blk_succ_succ]
  ring

private theorem a8ka_vecMul_blk (j : ZMod 7) (f : Fin 3 → ZMod 7) (M : M3) :
    vecMul (Fin.cases j f) (blk M) = Fin.cases j (vecMul f M) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [a8ka_vecMul_blk_zero]
    simp
  · rw [a8ka_vecMul_blk_succ]
    simp

private theorem a8ka_single_nsmul (m : ℕ) :
    m • (Pi.single 0 1 : Fin 4 → ZMod 7) = Fin.cases (m : ZMod 7) (0 : Fin 3 → ZMod 7) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp [Pi.smul_apply, nsmul_eq_mul]

private theorem a8ka_cases_add (a b : ZMod 7) (f g : Fin 3 → ZMod 7) :
    Fin.cases a f + Fin.cases b g = (Fin.cases (a + b) (f + g) : Fin 4 → ZMod 7) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

private theorem a8ka_factor {G : Type} [Group G] {Bs K : Subgroup G} {y : G} {hy : y ∈ Bs}
    {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)} {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    (hF : GGA8KFrame Bs K y hy ρ ι) (b : ↥Bs) :
    ∃ e : ↥Bs, (e : G) ∈ K ∧
      b = (⟨y, hy⟩ : ↥Bs) ^ (ι (Additive.ofMul b) 0).val * e ∧
      ι (Additive.ofMul e) 0 = 0 ∧
      (∀ i : Fin 3, ι (Additive.ofMul e) i.succ = ι (Additive.ofMul b) i.succ) := by
  let m : ℕ := (ι (Additive.ofMul b) 0).val
  let yc : ↥Bs := ⟨y, hy⟩
  let e : ↥Bs := Additive.toMul (-(m • Additive.ofMul yc) + Additive.ofMul b)
  have hyc_coord : ι (Additive.ofMul yc) = Pi.single 0 1 := hF.1
  have h_e : Additive.ofMul e = -(m • Additive.ofMul yc) + Additive.ofMul b :=
    ofMul_toMul _
  have hsub : ι (Additive.ofMul e) = -(m • ι (Additive.ofMul yc)) + ι (Additive.ofMul b) := by
    rw [h_e, map_add, map_neg, map_nsmul]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · have h0 : ι (Additive.ofMul e) 0 = 0 := by
      rw [hsub, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hyc_coord, Pi.single_eq_same,
        nsmul_eq_mul, mul_one,
        show (m : ZMod 7) = ι (Additive.ofMul b) 0 from ZMod.natCast_zmod_val _]
      exact neg_add_cancel _
    exact (hF.2.1 e).mp h0
  · have h1 : Additive.ofMul b = m • Additive.ofMul yc + Additive.ofMul e := by
      rw [h_e]
      exact (add_neg_cancel_left (m • Additive.ofMul yc) (Additive.ofMul b)).symm
    have h2 := congrArg Additive.toMul h1
    simp only [toMul_add, toMul_nsmul, toMul_ofMul] at h2
    exact h2
  · rw [hsub, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hyc_coord, Pi.single_eq_same,
      nsmul_eq_mul, mul_one,
      show (m : ZMod 7) = ι (Additive.ofMul b) 0 from ZMod.natCast_zmod_val _]
    exact neg_add_cancel _
  · intro i
    rw [hsub, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hyc_coord,
      Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero]
    rw [show (-0 : ZMod 7) = 0 from rfl]
    exact zero_add _

private theorem a8ka_exists_K_of_torus {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    {hy : y ∈ Bs} {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} (hF : GGA8KFrame Bs K y hy ρ ι)
    (f : Fin 3 → ZMod 7) :
    ∃ (b : ↥Bs) (hb : (b : G) ∈ K),
      ι (Additive.ofMul b) = Fin.cases 0 f ∧
      ρ ⟨b, hb⟩ = ggSL9TorusCoord (Multiplicative.ofAdd f) := by
  let b : ↥Bs := Additive.toMul (ι.symm (Fin.cases 0 f))
  have hbcoord : ι (Additive.ofMul b) = Fin.cases 0 f := by
    change ι (Additive.ofMul (Additive.toMul (ι.symm (Fin.cases 0 f)))) = Fin.cases 0 f
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hb0 : ι (Additive.ofMul b) 0 = 0 := by simp [hbcoord]
  have hbK : (b : G) ∈ K := (hF.2.1 b).mp hb0
  refine ⟨b, hbK, hbcoord, ?_⟩
  have hsucc : (fun i : Fin 3 => ι (Additive.ofMul b) i.succ) = f := by
    funext i; simp [hbcoord]
  rw [hF.2.2 b hbK, hsucc]

private theorem a8ka_coord_of_rho {G : Type} [Group G] {Bs K : Subgroup G} {y : G} {hy : y ∈ Bs}
    {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)} {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    (hF : GGA8KFrame Bs K y hy ρ ι) {b : ↥Bs} (hb : (b : G) ∈ K) {f : Fin 3 → ZMod 7}
    (h : ρ ⟨b, hb⟩ = ggSL9TorusCoord (Multiplicative.ofAdd f)) :
    ι (Additive.ofMul b) = Fin.cases 0 f := by
  have h2 := hF.2.2 b hb
  rw [h] at h2
  have hco : (fun i : Fin 3 => ι (Additive.ofMul b) i.succ) = f := by
    have h3 := ggSL9TorusCoord_injective h2
    simpa using (congrArg Multiplicative.toAdd h3).symm
  have hb0 : ι (Additive.ofMul b) 0 = 0 := (hF.2.1 b).mpr hb
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hb0
  · simpa using congrFun hco i

private theorem a8ka_conj_mem_torus {G : Type} [Group G] {Bs K : Subgroup G} {y : G} {hy : y ∈ Bs}
    {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)} {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    (hF : GGA8KFrame Bs K y hy ρ ι) (g : G) (hgK : g ∈ K)
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    {t : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (ht : t ∈ ggSL9Torus) :
    ρ ⟨g, hgK⟩ * t * (ρ ⟨g, hgK⟩)⁻¹ ∈ ggSL9Torus := by
  rw [← range_ggSL9TorusCoord] at ht
  obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp ht
  obtain ⟨b, hbK, -, hbρ⟩ := a8ka_exists_K_of_torus hF f
  have ht_eq : t = ρ ⟨b, hbK⟩ := (hbρ.trans hf).symm
  have hcBs : g * (b : G) * g⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hgN (b : G)).mp b.2
  let c : ↥Bs := ⟨g * (b : G) * g⁻¹, hcBs⟩
  have hcK : (c : G) ∈ K := by
    change g * (b : G) * g⁻¹ ∈ K
    exact K.mul_mem (K.mul_mem hgK hbK) (K.inv_mem hgK)
  have hsub : (⟨c, hcK⟩ : ↥K) = ⟨g, hgK⟩ * ⟨b, hbK⟩ * (⟨g, hgK⟩)⁻¹ := by
    apply Subtype.ext
    simp [c, Subgroup.coe_mul]
  have hprod : ρ ⟨g, hgK⟩ * t * (ρ ⟨g, hgK⟩)⁻¹ = ρ ⟨c, hcK⟩ := by
    rw [ht_eq, hsub, map_mul, map_mul, map_inv]
  rw [hprod, hF.2.2 c hcK, ← range_ggSL9TorusCoord]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem a8ka_mem_normalizer_torus {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    {hy : y ∈ Bs} {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} (hF : GGA8KFrame Bs K y hy ρ ι) (g : G)
    (hgK : g ∈ K) (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) :
    ρ ⟨g, hgK⟩ ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
  refine Subgroup.mem_normalizer_iff.mpr fun t => ⟨?_, ?_⟩
  · intro ht
    exact a8ka_conj_mem_torus hF g hgK hgN ht
  · intro ht
    have hgK' : g⁻¹ ∈ K := K.inv_mem hgK
    have hgN' : g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hgN
    have hconj : ρ ⟨g⁻¹, hgK'⟩ * (ρ ⟨g, hgK⟩ * t * (ρ ⟨g, hgK⟩)⁻¹) *
        (ρ ⟨g⁻¹, hgK'⟩)⁻¹ = t := by
      have hρinv : (ρ ⟨g, hgK⟩)⁻¹ = ρ ⟨g⁻¹, hgK'⟩ := by
        rw [← map_inv]
        exact congrArg ρ (Subtype.ext (by simp))
      rw [hρinv.symm]; group
    rw [← hconj]
    exact a8ka_conj_mem_torus hF g⁻¹ hgK' hgN' ht

theorem ggA8Nbr_kAut {G : Type} [Group G] {Bs K : Subgroup G} {y : G} (hy : y ∈ Bs)
    (hyK : ∀ k ∈ K, y * k = k * y) {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} (hF : GGA8KFrame Bs K y hy ρ ι) (φ : MulAut ↥Bs) :
    φ ∈ ggAutomizer K Bs ↔ ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3), ∀ b : ↥Bs,
      ι (Additive.ofMul (φ b)) = vecMul (ι (Additive.ofMul b)) (a8MonK π k) := by
  constructor
  · intro hφ
    obtain ⟨g, hgK, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨π, k, hnk⟩ := ggSL9_normalizer_torus (a8ka_mem_normalizer_torus hF g hgK hgN)
    refine ⟨π, k, fun b => ?_⟩
    let M : M3 := a8MonK3 π k
    let yc : ↥Bs := ⟨y, hy⟩
    have hyc_coord : ι (Additive.ofMul yc) = Pi.single 0 1 := hF.1
    have hM : a8MonK π k = blk M := rfl
    obtain ⟨e, heK, hb_eq, he0, hesucc⟩ := a8ka_factor hF b
    let n : ℕ := (ι (Additive.ofMul b) 0).val
    have hb_eq' : b = yc ^ n * e := hb_eq
    let f : Fin 3 → ZMod 7 := fun i => ι (Additive.ofMul e) i.succ
    have he_coord : ι (Additive.ofMul e) = Fin.cases 0 f := by
      funext j; refine Fin.cases ?_ (fun i => ?_) j
      · simpa [f] using he0
      · simp [f]
    have heρ : ρ ⟨e, heK⟩ = ggSL9TorusCoord (Multiplicative.ofAdd f) := hF.2.2 e heK
    have hgegBs : g * (e : G) * g⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hgN (e : G)).mp e.2
    let geg : ↥Bs := ⟨g * (e : G) * g⁻¹, hgegBs⟩
    have hgegK : (geg : G) ∈ K := by
      change g * (e : G) * g⁻¹ ∈ K
      exact K.mul_mem (K.mul_mem hgK heK) (K.inv_mem hgK)
    have hgegρ : ρ ⟨geg, hgegK⟩ =
        ggSL9TorusCoord (Multiplicative.ofAdd (vecMul f M)) := by
      have hsub : (⟨geg, hgegK⟩ : ↥K) = ⟨g, hgK⟩ * ⟨e, heK⟩ * (⟨g, hgK⟩)⁻¹ := by
        apply Subtype.ext; simp [geg, Subgroup.coe_mul]
      rw [hsub, map_mul, map_mul, map_inv, heρ]
      exact hnk f
    have hgegcoord : ι (Additive.ofMul geg) = Fin.cases 0 (vecMul f M) :=
      a8ka_coord_of_rho hF hgegK hgegρ
    have hcomm : Commute g (yc : G) := by
      apply (commute_iff_eq g (yc : G)).mpr
      simpa [yc] using (hyK g hgK).symm
    have hgypow : g * (yc : G) ^ n * g⁻¹ = (yc : G) ^ n := by
      rw [(hcomm.pow_right n).eq]; group
    have hgypow' : g * (yc : G) ^ n = (yc : G) ^ n * g := by
      calc g * (yc : G) ^ n = (g * (yc : G) ^ n * g⁻¹) * g := by group
        _ = (yc : G) ^ n * g := by rw [hgypow]
    have hconj_eq : ggConjAut Bs hgN b = yc ^ n * geg := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      have hstep : g * ((yc : G) ^ n * (e : G)) * g⁻¹ =
          (yc : G) ^ n * (g * (e : G) * g⁻¹) := by
        rw [← mul_assoc, hgypow']; group
      rw [hb_eq', Subgroup.coe_mul, Subgroup.coe_pow, hstep]
      rfl
    have hι_conj : ι (Additive.ofMul (ggConjAut Bs hgN b)) =
        n • (Pi.single 0 1 : Fin 4 → ZMod 7) + Fin.cases 0 (vecMul f M) := by
      calc ι (Additive.ofMul (ggConjAut Bs hgN b))
          = ι (Additive.ofMul (yc ^ n * geg)) := by rw [hconj_eq]
        _ = ι (Additive.ofMul (yc ^ n)) + ι (Additive.ofMul geg) := by
              rw [ofMul_mul, map_add]
        _ = n • ι (Additive.ofMul yc) + ι (Additive.ofMul geg) := by
              rw [ofMul_pow, map_nsmul]
        _ = n • (Pi.single 0 1 : Fin 4 → ZMod 7) + Fin.cases 0 (vecMul f M) := by
              rw [hyc_coord, hgegcoord]
    have hι_b : ι (Additive.ofMul b) = Fin.cases (ι (Additive.ofMul b) 0) f := by
      funext j; refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simpa [f] using (hesucc i).symm
    have hφeq : φ b = ggConjAut Bs hgN b := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hφg b
    calc ι (Additive.ofMul (φ b)) = ι (Additive.ofMul (ggConjAut Bs hgN b)) := by rw [hφeq]
      _ = n • (Pi.single 0 1 : Fin 4 → ZMod 7) + Fin.cases 0 (vecMul f M) := hι_conj
      _ = Fin.cases (ι (Additive.ofMul b) 0) (vecMul f M) := by
            rw [a8ka_single_nsmul, a8ka_cases_add]
            simp only [add_zero, zero_add]
            rw [show (n : ZMod 7) = ι (Additive.ofMul b) 0 from ZMod.natCast_zmod_val _]
      _ = vecMul (ι (Additive.ofMul b)) (a8MonK π k) := by
            rw [hι_b, hM]
            exact (a8ka_vecMul_blk (ι (Additive.ofMul b) 0) f M).symm
  · rintro ⟨π, k, hφ⟩
    let M : M3 := a8MonK3 π k
    let yc : ↥Bs := ⟨y, hy⟩
    have hyc_coord : ι (Additive.ofMul yc) = Pi.single 0 1 := hF.1
    have hM : a8MonK π k = blk M := rfl
    obtain ⟨n, hn⟩ := ggSL9_exists_monomial π k
    let gK : ↥K := ρ.symm n
    let g : G := (gK : G)
    have hgK : g ∈ K := gK.2
    have hρg : ρ gK = n := ρ.apply_symm_apply n
    have hvec1 : vecMul (Pi.single 0 1 : Fin 4 → ZMod 7) (a8MonK π k) = Pi.single 0 1 := by
      have hsingle : (Pi.single 0 1 : Fin 4 → ZMod 7) = Fin.cases 1 (0 : Fin 3 → ZMod 7) := by
        simpa using a8ka_single_nsmul 1
      rw [hsingle, hM, a8ka_vecMul_blk, zero_vecMul]
    have hφy : φ yc = yc := by
      have h1 : ι (Additive.ofMul (φ yc)) = ι (Additive.ofMul yc) := by
        rw [hφ yc, hyc_coord, hvec1]
      exact Additive.ofMul.injective (ι.injective h1)
    have hconj_e : ∀ e : ↥Bs, (e : G) ∈ K → g * (e : G) * g⁻¹ = (φ e : G) := by
      intro e heK
      let f : Fin 3 → ZMod 7 := fun i => ι (Additive.ofMul e) i.succ
      have he0 : ι (Additive.ofMul e) 0 = 0 := (hF.2.1 e).mpr heK
      have he_coord : ι (Additive.ofMul e) = Fin.cases 0 f := by
        funext j; refine Fin.cases ?_ (fun i => ?_) j
        · simpa [f] using he0
        · simp [f]
      have hφe : ι (Additive.ofMul (φ e)) = Fin.cases 0 (vecMul f M) := by
        rw [hφ e, he_coord, hM, a8ka_vecMul_blk]
      have hφe0 : ι (Additive.ofMul (φ e)) 0 = 0 := by rw [hφe]; simp
      have hφeK : (φ e : G) ∈ K := (hF.2.1 (φ e)).mp hφe0
      have heρ : ρ ⟨e, heK⟩ = ggSL9TorusCoord (Multiplicative.ofAdd f) := hF.2.2 e heK
      have hφeρ : ρ ⟨φ e, hφeK⟩ =
          ggSL9TorusCoord (Multiplicative.ofAdd (vecMul f M)) := by
        rw [hF.2.2 (φ e) hφeK]
        exact congrArg ggSL9TorusCoord (congrArg Multiplicative.ofAdd
          (by funext i; rw [hφe]; simp))
      have heqK : (gK * ⟨e, heK⟩ * gK⁻¹ : ↥K) = ⟨φ e, hφeK⟩ := by
        apply ρ.injective
        rw [map_mul, map_mul, map_inv, hρg, heρ]
        exact (hn f).trans hφeρ.symm
      have hval := congrArg (fun x : ↥K => (x : G)) heqK
      simpa [g, gK, Subgroup.coe_mul] using hval
    have hcomm : Commute g (yc : G) := by
      apply (commute_iff_eq g (yc : G)).mpr
      simpa [yc] using (hyK g hgK).symm
    have hgypow : ∀ m : ℕ, g * (yc : G) ^ m * g⁻¹ = (yc : G) ^ m := by
      intro m
      rw [(hcomm.pow_right m).eq]; group
    have hφypow : ∀ m : ℕ, (φ (yc ^ m) : G) = (yc : G) ^ m := by
      intro m
      rw [map_pow, hφy, Subgroup.coe_pow]
    have hforward_eq : ∀ b : ↥Bs, g * (b : G) * g⁻¹ = (φ b : G) := by
      intro b
      obtain ⟨e, heK, hb_eq, he0, hesucc⟩ := a8ka_factor hF b
      let m : ℕ := (ι (Additive.ofMul b) 0).val
      have hb_eq' : b = yc ^ m * e := hb_eq
      have hge : g * (e : G) * g⁻¹ = (φ e : G) := hconj_e e heK
      have hstep : g * ((yc : G) ^ m * (e : G)) * g⁻¹ =
          (g * (yc : G) ^ m * g⁻¹) * (g * (e : G) * g⁻¹) := by
        group
      calc g * (b : G) * g⁻¹
          = g * ((yc : G) ^ m * (e : G)) * g⁻¹ := by
              rw [hb_eq', Subgroup.coe_mul, Subgroup.coe_pow]
        _ = (g * (yc : G) ^ m * g⁻¹) * (g * (e : G) * g⁻¹) := hstep
        _ = (yc : G) ^ m * (φ e : G) := by
              rw [hgypow m, hge]
        _ = (φ (yc ^ m) : G) * (φ e : G) := by
              rw [← hφypow m]
        _ = (φ (yc ^ m * e) : G) := by
              rw [← Subgroup.coe_mul, ← map_mul]
        _ = (φ b : G) := by rw [← hb_eq']
    have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h := hforward_eq ⟨x, hx⟩
        rw [h]
        exact (φ ⟨x, hx⟩).2
      · intro hx
        let xb : ↥Bs := ⟨g * x * g⁻¹, hx⟩
        let b : ↥Bs := φ.symm xb
        have hφb : (φ b : G) = g * x * g⁻¹ := by
          have h := congrArg (fun z : ↥Bs => (z : G)) (φ.apply_symm_apply xb)
          simpa [b, xb] using h
        have hfb := hforward_eq b
        have heq : (b : G) = x := by
          exact mul_left_cancel (mul_right_cancel (hfb.trans hφb))
        rw [← heq]
        exact b.2
    have hφeq : φ = ggConjAut Bs hgN := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact (hforward_eq b).symm
    rw [hφeq]
    exact ggConjAut_mem_ggAutomizer hgK hgN

end CFSG.StandardType.A8Coord

end
