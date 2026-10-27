module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem a11fa_nsmul_single (d c : ZMod 7) (i : Fin 4) :
    d.val • (Pi.single i c : Fin 4 → ZMod 7) = Pi.single i (d * c) := by
  funext j
  by_cases h : j = i
  · subst h; simp [Pi.single_eq_same, nsmul_eq_mul]
  · simp [Pi.single_eq_of_ne h]

private theorem a11fa_single_val_nsmul (v : Fin 4 → ZMod 7) (i : Fin 4) :
    Pi.single i (v i) = (v i).val • (Pi.single i (1 : ZMod 7) : Fin 4 → ZMod 7) := by
  rw [a11fa_nsmul_single (v i) 1 i]; simp

private theorem a11fa_fBasis_span_top (a : ZMod 7) (ha : a ≠ 0) :
    AddSubgroup.closure (Set.range (fun i => (fBasis a) i)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  apply AddSubgroup.pi_mem_of_single_mem v
  intro i
  have hrow0 : (fBasis a) 0 = (Pi.single 1 (1 : ZMod 7) : Fin 4 → ZMod 7) := by
    funext j; fin_cases j <;> simp [fBasis]
  have hrow1 : (fBasis a) 1 = (Pi.single 2 (1 : ZMod 7) : Fin 4 → ZMod 7) := by
    funext j; fin_cases j <;> simp [fBasis]
  have hrow2 : (fBasis a) 2 = (Pi.single 3 (1 : ZMod 7) : Fin 4 → ZMod 7) := by
    funext j; fin_cases j <;> simp [fBasis]
  have hrow3 : (fBasis a) 3 = (Pi.single 0 a : Fin 4 → ZMod 7) := by
    funext j; fin_cases j <;> simp [fBasis]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h0 : (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) = (a⁻¹).val • (fBasis a) 3 := by
    rw [hrow3, a11fa_nsmul_single (a⁻¹) a 0, inv_mul_cancel₀ ha]
  have hmem : (Pi.single i (1 : ZMod 7) : Fin 4 → ZMod 7) ∈
      AddSubgroup.closure (Set.range (fun j => (fBasis a) j)) := by
    fin_cases i
    · change (Pi.single (0 : Fin 4) (1 : ZMod 7) : Fin 4 → ZMod 7) ∈ _
      rw [h0]
      exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self 3)) _
    · change (Pi.single (1 : Fin 4) (1 : ZMod 7) : Fin 4 → ZMod 7) ∈ _
      rw [← hrow0]; exact AddSubgroup.subset_closure (Set.mem_range_self 0)
    · change (Pi.single (2 : Fin 4) (1 : ZMod 7) : Fin 4 → ZMod 7) ∈ _
      rw [← hrow1]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
    · change (Pi.single (3 : Fin 4) (1 : ZMod 7) : Fin 4 → ZMod 7) ∈ _
      rw [← hrow2]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)
  rw [a11fa_single_val_nsmul v i]
  exact AddSubgroup.nsmul_mem _ hmem _

private theorem a11fa_fBasis_row (a : ZMod 7) :
    (fBasis a) 0 = (Pi.single 1 (1 : ZMod 7) : Fin 4 → ZMod 7) ∧
    (fBasis a) 1 = (Pi.single 2 (1 : ZMod 7) : Fin 4 → ZMod 7) ∧
    (fBasis a) 2 = (Pi.single 3 (1 : ZMod 7) : Fin 4 → ZMod 7) ∧
    (fBasis a) 3 = (Pi.single 0 a : Fin 4 → ZMod 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext j <;> fin_cases j <;> simp [fBasis]

private theorem a11fa_fBasis_castSucc (a : ZMod 7) (i : Fin 3) :
    (fBasis a) i.castSucc = (Pi.single i.succ (1 : ZMod 7) : Fin 4 → ZMod 7) := by
  fin_cases i <;> funext j <;> fin_cases j <;> simp [fBasis]

private theorem a11fa_fBasis_ne_zero (a : ZMod 7) (ha : a ≠ 0) (i : Fin 4) :
    (fBasis a) i ≠ 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro h
  fin_cases i
  · have hh : (1 : ZMod 7) = 0 := by simpa [fBasis] using congrFun h 1
    exact one_ne_zero hh
  · have hh : (1 : ZMod 7) = 0 := by simpa [fBasis] using congrFun h 2
    exact one_ne_zero hh
  · have hh : (1 : ZMod 7) = 0 := by simpa [fBasis] using congrFun h 3
    exact one_ne_zero hh
  · exact ha (by simpa [fBasis] using congrFun h 0)

private theorem a11fa_single_succ (i : Fin 3) :
    (fun j : Fin 3 => (Pi.single i.succ (1 : ZMod 7) : Fin 4 → ZMod 7) j.succ) =
      (Pi.single i (1 : ZMod 7) : Fin 3 → ZMod 7) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · have h' : j.succ ≠ i.succ := fun e => h (Fin.succ_inj.mp e)
    simp [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

private theorem a11fa_single_zero (a : ZMod 7) (ha : a ≠ 0) :
    (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) =
      (a⁻¹).val • (Pi.single 0 a : Fin 4 → ZMod 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [a11fa_nsmul_single (a⁻¹) a 0, inv_mul_cancel₀ ha]

private theorem a11fa_ofMul_mul {M : Type} [Mul M] (x y : M) :
    Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y := rfl

private theorem a11fa_ofMul_pow {M : Type} [Monoid M] (x : M) (n : ℕ) :
    Additive.ofMul (x ^ n) = n • Additive.ofMul x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, show Additive.ofMul (x ^ n * x) =
      Additive.ofMul (x ^ n) + Additive.ofMul x from rfl, ih, succ_nsmul]

private theorem a11fa_tC_add (c d : Fin 3 → ZMod 7) : tC c * tC d = tC (c + d) := by
  show ggSL9TorusCoord (Multiplicative.ofAdd c) * ggSL9TorusCoord (Multiplicative.ofAdd d) =
    ggSL9TorusCoord (Multiplicative.ofAdd (c + d))
  rw [← map_mul]
  apply congrArg ggSL9TorusCoord
  rfl

private theorem a11fa_fBasis_mul_fBasisInv (a : ZMod 7) (ha : a ≠ 0) :
    fBasis a * fBasisInv a = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fBasis, fBasisInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    exact mul_inv_cancel₀ ha

private theorem a11fa_fBasis_mul_fPerm (a : ZMod 7) (ha : a ≠ 0) (σ : Equiv.Perm (Fin 4)) :
    fBasis a * fPerm a σ = a8PermMat σ * fBasis a := by
  calc fBasis a * fPerm a σ
      = fBasis a * (fBasisInv a * a8PermMat σ * fBasis a) := rfl
    _ = fBasis a * fBasisInv a * (a8PermMat σ * fBasis a) := by noncomm_ring
    _ = a8PermMat σ * fBasis a := by rw [a11fa_fBasis_mul_fBasisInv a ha, one_mul]

private theorem a11fa_a8PermMat_mul_fBasis (a : ZMod 7) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (a8PermMat σ * fBasis a) i = fBasis a (σ i) := by
  funext j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · simp [a8PermMat]
  · intro b _ hb
    simp only [a8PermMat, Matrix.of_apply]
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (σ i)) h

private theorem a11fa_vecMul_fBasis_fPerm (a : ZMod 7) (ha : a ≠ 0) (σ : Equiv.Perm (Fin 4))
    (i : Fin 4) : Matrix.vecMul (fBasis a i) (fPerm a σ) = fBasis a (σ i) := by
  have h1 : Matrix.vecMul (fBasis a i) (fPerm a σ) = (fBasis a * fPerm a σ) i := by
    funext j
    simp only [Matrix.vecMul_apply, Matrix.mul_apply, dotProduct, Matrix.col_apply]
  rw [h1, a11fa_fBasis_mul_fPerm a ha σ, a11fa_a8PermMat_mul_fBasis a σ i]

private theorem a11fa_fBasis_closure {G : Type} [Group G] (Bs : Subgroup G)
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (a : ZMod 7) (ha : a ≠ 0) :
    Subgroup.closure (Set.range (fun i => ((Additive.toMul (ι.symm ((fBasis a) i)) : ↥Bs) : G))) =
      Bs := by
  let fb : Fin 4 → ↥Bs := fun i => Additive.toMul (ι.symm ((fBasis a) i))
  let f : Fin 4 → G := fun i => (fb i : G)
  have hfb : ∀ i, ι (Additive.ofMul (fb i)) = (fBasis a) i := by
    intro i
    simp [fb]
  apply le_antisymm
  · apply (Subgroup.closure_le Bs).mpr
    rintro x ⟨i, rfl⟩
    exact (fb i).2
  · set H : Subgroup G := Subgroup.closure (Set.range f) with hH
    set H' : Subgroup ↥Bs := H.subgroupOf Bs with hH'
    set A : AddSubgroup (Additive ↥Bs) :=
      AddSubgroup.closure (Set.range (fun i => Additive.ofMul (fb i))) with hA
    have hAle : A ≤ H'.toAddSubgroup := by
      apply (AddSubgroup.closure_le H'.toAddSubgroup).mpr
      rintro x ⟨i, rfl⟩
      show fb i ∈ H'
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hmap : AddSubgroup.map ι.toAddMonoidHom A = ⊤ := by
      rw [eq_top_iff, ← a11fa_fBasis_span_top a ha]
      apply (AddSubgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      change (fBasis a) i ∈ AddSubgroup.map ι.toAddMonoidHom A
      rw [← hfb i]
      exact AddSubgroup.mem_map.mpr ⟨Additive.ofMul (fb i),
        AddSubgroup.subset_closure (Set.mem_range_self i), rfl⟩
    have hAtop : A = ⊤ := by
      refine AddSubgroup.map_injective (f := ι.toAddMonoidHom) ι.injective ?_
      rw [hmap, AddSubgroup.map_top]
      exact (AddMonoidHom.range_eq_top.mpr ι.surjective).symm
    have hH'top : H' = ⊤ := by
      rw [eq_top_iff]
      intro b _
      have hbA : Additive.ofMul b ∈ A := by rw [hAtop]; trivial
      have := hAle hbA
      simpa using this
    have hBsle : Bs ≤ H := Subgroup.subgroupOf_eq_top.mp hH'top
    intro b hb
    exact hBsle hb

private theorem a11fa_centralizer_zpowers_eq {G : Type} [Group G] {y z : G}
    (hzp : Subgroup.zpowers y = Subgroup.zpowers z) :
    Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    have hzy : z ∈ Subgroup.zpowers y := by rw [hzp]; exact Subgroup.mem_zpowers z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzy
    rw [← hk]
    exact (Commute.zpow_right (show Commute w y from hw) k).eq
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    have hyz : y ∈ Subgroup.zpowers z := by rw [← hzp]; exact Subgroup.mem_zpowers y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
    rw [← hk]
    exact (Commute.zpow_right (show Commute w z from hw) k).eq

private theorem a11fa_conj_fb {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (a : ZMod 7) (ha : a ≠ 0)
    (fb : Fin 4 → ↥Bs) (hfb : ∀ i, ι (Additive.ofMul (fb i)) = fBasis a i)
    (σ : Equiv.Perm (Fin 4)) (g : G) (ψ : MulAut ↥Bs)
    (hψ : ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * (b : G) * g⁻¹)
    (hperm : ∀ b : ↥Bs, ι (Additive.ofMul (ψ b)) =
      Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ))
    (i : Fin 4) : g * (fb i : G) * g⁻¹ = (fb (σ i) : G) := by
  have h1 : ψ (fb i) = fb (σ i) := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [hperm (fb i), hfb i, a11fa_vecMul_fBasis_fPerm a ha σ i, hfb (σ i)]
  have := hψ (fb i)
  rw [h1] at this
  exact this.symm

theorem a11FrameAssembleInput_holds : A11FrameAssembleInput := by
  intro G _ _ B Bs x L D J hR hA y K hy hx ρ ι a Θ hnb hJK h7 ha hF hxι hL hJ hΘ
  classical
  let φ₃ : SL 9 →* G := K.subtype.comp ((ρ.symm.toMonoidHom).comp Θ.toMonoidHom)
  let fb : Fin 4 → ↥Bs := fun i => Additive.toMul (ι.symm ((fBasis a) i))
  let f : Fin 4 → G := fun i => (fb i : G)
  have hfb : ∀ i, ι (Additive.ofMul (fb i)) = (fBasis a) i := by
    intro i; simp [fb]
  have hEab : IsElemAbelian 7 Bs := hR.1.2.1.2.1
  have hcommBs : ∀ u v : ↥Bs, u * v = v * u := isMulCommutative_iff.mp hEab.1
  have hpowBs : ∀ u : ↥Bs, u ^ 7 = 1 := by
    intro u
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hEab.2 (u : G) u.2
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hR.1.2.2.1.2.2.2.2.2.1
  have hJcentD : J ≤ Subgroup.centralizer (D : Set G) :=
    fun g hg => (Subgroup.mem_inf.mp (hJcomp.1 hg)).2
  have hJq : Assembly.IsQuasisimple ↥J := hJcomp.2.2
  have hφinj : Function.Injective φ₃ := by
    intro s t h
    change ((ρ.symm (Θ s) : ↥K) : G) = ((ρ.symm (Θ t) : ↥K) : G) at h
    exact Θ.injective (ρ.symm.injective (Subtype.coe_injective h))
  have hrange : φ₃.range = K := by
    apply le_antisymm
    · rintro z ⟨s, rfl⟩
      exact (ρ.symm (Θ s)).2
    · intro k hk
      refine ⟨Θ.symm (ρ ⟨k, hk⟩), ?_⟩
      change ((ρ.symm (Θ (Θ.symm (ρ ⟨k, hk⟩))) : ↥K) : G) = k
      rw [Θ.apply_symm_apply, ρ.symm_apply_apply]
  have hφT9 : ∀ i : Fin 3, φ₃ (T9 i) = f i.castSucc := by
    intro i
    have hbK : ((fb i.castSucc : ↥Bs) : G) ∈ K := by
      refine (hF.2.1 (fb i.castSucc)).mp ?_
      rw [hfb i.castSucc]
      obtain ⟨h0, h1, h2, h3⟩ := a11fa_fBasis_row a
      fin_cases i <;> simp [h0, h1, h2]
    have hρ : ρ ⟨fb i.castSucc, hbK⟩ = tC (Pi.single i 1) := by
      rw [hF.2.2 (fb i.castSucc) hbK]
      have hfun : (fun j : Fin 3 => ι (Additive.ofMul (fb i.castSucc)) j.succ) =
          (Pi.single i (1 : ZMod 7) : Fin 3 → ZMod 7) := by
        rw [show (fun j : Fin 3 => ι (Additive.ofMul (fb i.castSucc)) j.succ) =
            (fun j : Fin 3 => (Pi.single i.succ (1 : ZMod 7) : Fin 4 → ZMod 7) j.succ) from by
          funext j; rw [hfb i.castSucc, a11fa_fBasis_castSucc a i]]
        exact a11fa_single_succ i
      rw [hfun]
    change ((ρ.symm (Θ (T9 i)) : ↥K) : G) = (fb i.castSucc : G)
    rw [hΘ i, ← hρ, ρ.symm_apply_apply]
  have hf_comm : ∀ i j, f i * f j = f j * f i := by
    intro i j
    show (fb i : G) * (fb j : G) = (fb j : G) * (fb i : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcommBs (fb i) (fb j)]
  have hf_ne_one : ∀ i, f i ≠ 1 := by
    intro i h
    have h1 : fb i = 1 := Subtype.ext h
    have h2 : ι (Additive.ofMul (fb i)) = 0 := by
      rw [h1, show Additive.ofMul (1 : ↥Bs) = 0 from rfl, map_zero]
    exact a11fa_fBasis_ne_zero a ha i (by rw [← hfb i, h2])
  have hf_order : ∀ i, orderOf (f i) = 7 := by
    intro i
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ (hf_ne_one i)
    show ((fb i : ↥Bs) : G) ^ 7 = 1
    rw [← Subgroup.coe_pow, hpowBs (fb i)]
    rfl
  have hclosure : Subgroup.closure (Set.range f) = Bs := by
    simpa [fb, f] using a11fa_fBasis_closure Bs ι a ha
  have hcard_closure : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 := by
    rw [hclosure]
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr (Additive.ofMul (α := ↥Bs))
      _ = Nat.card (Fin 4 → ZMod 7) := Nat.card_congr ι.toEquiv
      _ = 7 ^ 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]; norm_num
  have hx_f : x = f 0 * f 1 * f 2 * f 3 := by
    have hxsub : (⟨x, hx⟩ : ↥Bs) = fb 0 * fb 1 * fb 2 * fb 3 := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [hxι]
      rw [show Additive.ofMul (fb 0 * fb 1 * fb 2 * fb 3) =
          Additive.ofMul (fb 0) + Additive.ofMul (fb 1) + Additive.ofMul (fb 2) +
            Additive.ofMul (fb 3) from rfl]
      rw [map_add, map_add, map_add, hfb 0, hfb 1, hfb 2, hfb 3]
      obtain ⟨h0, h1, h2, h3⟩ := a11fa_fBasis_row a
      funext j
      fin_cases j <;> simp [h0, h1, h2, h3]
    have := congrArg (Subtype.val) hxsub
    simpa [f] using this
  have hy7 : y ^ 7 = 1 := hnb.1.1.1.2 y hnb.1.2.1
  have hyorder : orderOf y = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hy7 hnb.1.2.2.1
  have hy_sub : (⟨y, hy⟩ : ↥Bs) = (fb 3) ^ ((a⁻¹).val) := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [hF.1, a11fa_ofMul_pow, map_nsmul, hfb 3]
    rw [show (fBasis a) 3 = (Pi.single 0 a : Fin 4 → ZMod 7) from (a11fa_fBasis_row a).2.2.2]
    exact a11fa_single_zero a ha
  have hy_zpow : y ∈ Subgroup.zpowers (f 3) := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨((a⁻¹).val : ℤ), ?_⟩
    rw [zpow_natCast]
    change ((fb 3 : ↥Bs) : G) ^ ((a⁻¹).val) = y
    rw [← Subgroup.coe_pow, ← hy_sub]
  have hzpy : Subgroup.zpowers y = Subgroup.zpowers (f 3) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hy_zpow
    · rw [Nat.card_zpowers, Nat.card_zpowers, hyorder, hf_order 3]
  have hD : D = Subgroup.closure ({x, f 3} : Set G) := by
    rw [hnb.2.1]
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro z (rfl | hz)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hz; subst hz
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hy_zpow
    · apply (Subgroup.closure_le _).mpr
      rintro z (rfl | hz)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hz; subst hz
        have : f 3 ∈ Subgroup.zpowers y := by rw [hzpy]; exact Subgroup.mem_zpowers (f 3)
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) this
  have hcent_eq : Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({f 3} : Set G) :=
    a11fa_centralizer_zpowers_eq hzpy
  have hK_cent_f3 : K ≤ Subgroup.centralizer ({f 3} : Set G) := by
    rw [← hcent_eq]; exact hnb.1.2.2.2.1
  have hK_sub : IsSubnormal K (Subgroup.centralizer ({f 3} : Set G)) := by
    rw [← hcent_eq]; exact hnb.1.2.2.2.2.1.2.1
  have hKq : Assembly.IsQuasisimple ↥K :=
    Assembly.IsQuasisimple.of_mulEquiv (ρ.trans Θ.symm)
      (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
        (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 9 F2
          (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))))
  have hcomp_f3 : IsComponentOf φ₃.range (Subgroup.centralizer ({f 3} : Set G)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hrange]; exact hK_cent_f3
    · rw [hrange]; exact hK_sub
    · rw [hrange]; exact hKq
  set c0 : SL 9 := T9 0 * T9 1 * T9 2 with hc0
  have harg : (Pi.single 0 (1 : ZMod 7) : Fin 3 → ZMod 7) +
      (Pi.single 1 (1 : ZMod 7) : Fin 3 → ZMod 7) +
      (Pi.single 2 (1 : ZMod 7) : Fin 3 → ZMod 7) = (fun _ : Fin 3 => 1) := by
    funext j; fin_cases j <;> simp
  have hΘc0 : Θ c0 = tC (fun _ : Fin 3 => 1) := by
    rw [hc0, map_mul, map_mul, hΘ 0, hΘ 1, hΘ 2, a11fa_tC_add, a11fa_tC_add, harg]
  let w0 : Fin 4 → ZMod 7 := ![0, 1, 1, 1]
  let b0 : ↥Bs := Additive.toMul (ι.symm w0)
  have hb0_iota : ι (Additive.ofMul b0) = w0 := by simp [b0]
  have harg0 : (fun j : Fin 3 => w0 j.succ) = (fun _ : Fin 3 => 1) := by
    change (fun j : Fin 3 => (![0, 1, 1, 1] : Fin 4 → ZMod 7) j.succ) = (fun _ : Fin 3 => 1)
    funext j; fin_cases j <;> rfl
  have hb0K : ((b0 : ↥Bs) : G) ∈ K := by
    refine (hF.2.1 b0).mp ?_
    rw [hb0_iota]; simp [w0]
  have hρb0 : ρ ⟨b0, hb0K⟩ = tC (fun _ : Fin 3 => 1) := by
    rw [hF.2.2 b0 hb0K]
    apply congrArg ggSL9TorusCoord
    apply congrArg Multiplicative.ofAdd
    rw [hb0_iota]
    exact harg0
  have hφc0 : φ₃ c0 = (b0 : G) := by
    change ((ρ.symm (Θ c0) : ↥K) : G) = (b0 : G)
    rw [hΘc0, ← hρb0, ρ.symm_apply_apply]
  have hb0_eq : b0 = (⟨x, hx⟩ : ↥Bs) * (⟨y, hy⟩ : ↥Bs) ^ ((-a).val) := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [hb0_iota]
    change (![0, 1, 1, 1] : Fin 4 → ZMod 7) = ι (Additive.ofMul
      ((⟨x, hx⟩ : ↥Bs) * (⟨y, hy⟩ : ↥Bs) ^ ((-a).val)))
    rw [a11fa_ofMul_mul, a11fa_ofMul_pow]
    rw [map_add, map_nsmul, hxι, hF.1]
    rw [a11fa_nsmul_single (-a) 1 0]
    funext j
    fin_cases j <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne, _root_.add_neg_cancel]
  have hb0D : (b0 : G) ∈ D := by
    rw [hb0_eq, Subgroup.coe_mul, Subgroup.coe_pow]
    simp only [Subtype.coe_mk]
    refine D.mul_mem ?_ (D.pow_mem ?_ _)
    · rw [hnb.2.1]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [hnb.2.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJcent_b0 : J ≤ Subgroup.centralizer ({φ₃ c0} : Set G) :=
    le_trans hJcentD (Subgroup.centralizer_le (by rintro z rfl; rw [hφc0]; exact hb0D))
  let C : Subgroup G := K ⊓ Subgroup.centralizer ({φ₃ c0} : Set G)
  have hJ_C : J ≤ C := le_inf hJK hJcent_b0
  have hmapC0 : (Subgroup.centralizer ({c0} : Set (SL 9))).map φ₃ = C := by
    apply le_antisymm
    · rintro y ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hrange]; exact ⟨u, rfl⟩
      · change φ₃ u ∈ Subgroup.centralizer ({φ₃ c0} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_centralizer_singleton_iff.mp hu
    · intro y hy
      obtain ⟨hyK, hycent⟩ := Subgroup.mem_inf.mp hy
      have hyrange : y ∈ φ₃.range := by rw [hrange]; exact hyK
      obtain ⟨u, rfl⟩ := hyrange
      refine ⟨u, ?_, rfl⟩
      show u ∈ Subgroup.centralizer ({c0} : Set (SL 9))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hycent
      rw [← map_mul, ← map_mul] at h
      exact hφinj h
  have hJ9def : J9 = ⁅Subgroup.centralizer ({c0} : Set (SL 9)),
      Subgroup.centralizer ({c0} : Set (SL 9))⁆ := by
    unfold J9
    rw [← hc0]
  have hJ9 : ⁅C, C⁆ = J9.map φ₃ := by
    rw [hJ9def, Subgroup.map_commutator (Subgroup.centralizer ({c0} : Set (SL 9)))
      (Subgroup.centralizer ({c0} : Set (SL 9))) φ₃, hmapC0]
  have hJleJ9 : J ≤ J9.map φ₃ := by
    haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
    have hcommJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
    rw [← hcommJ, ← hJ9]
    exact Subgroup.commutator_mono hJ_C hJ_C
  let ψL : (l : Fin 4) → MulAut ↥Bs := fun l => Classical.choose (hL (Equiv.swap l 3))
  have hψL : ∀ l, ψL l ∈ ggAutomizer L Bs ∧ ∀ b : ↥Bs,
      ι (Additive.ofMul (ψL l b)) =
        Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a (Equiv.swap l 3)) :=
    fun l => Classical.choose_spec (hL (Equiv.swap l 3))
  let gL : Fin 4 → G := fun l => Classical.choose (mem_ggAutomizer_iff.mp (hψL l).1)
  have hgL : ∀ l, gL l ∈ L ∧ gL l ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, (((ψL l) b : ↥Bs) : G) = gL l * (b : G) * (gL l)⁻¹ :=
    fun l => Classical.choose_spec (mem_ggAutomizer_iff.mp (hψL l).1)
  let n : Fin 4 → G := fun l => if l = 3 then 1 else gL l
  have hn3 : n 3 = 1 := by simp [n]
  have hnL : ∀ l, n l ∈ L := by
    intro l
    by_cases hl : l = 3
    · subst hl; rw [hn3]; exact L.one_mem
    · simp only [n, if_neg hl]; exact (hgL l).1
  have hnact : ∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i) := by
    intro l i
    by_cases hl : l = 3
    · subst hl
      rw [hn3]
      simp
    · have hn : n l = gL l := by simp [n, if_neg hl]
      rw [hn]
      exact a11fa_conj_fb ι a ha fb hfb (Equiv.swap l 3) (gL l) (ψL l)
        (hgL l).2.2 (hψL l).2 i
  refine ⟨φ₃, f, n, ?_, ?_⟩
  · refine ⟨?_, hrange, hnb, hclosure, hx_f, hy_zpow, hD, hnL, hJK, hJleJ9⟩
    refine ⟨hφinj, ?_, hf_comm, hf_order, hcard_closure, hn3, hnact, hcomp_f3⟩
    intro i; exact (hφT9 i).symm
  · refine ⟨h7, ?_⟩
    intro σ hσ3
    obtain ⟨ψ, hψmem, hψperm⟩ := hJ σ hσ3
    obtain ⟨g, hgJ, hgN, hgconj⟩ := mem_ggAutomizer_iff.mp hψmem
    exact ⟨g, hgJ, hgN, fun i => a11fa_conj_fb ι a ha fb hfb σ g ψ hgconj hψperm i⟩

end CFSG.StandardType.A11

end
