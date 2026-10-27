module

public import CFSG.RankThree.SubgroupLists.MonomialFourCardinality
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import TauCeti.GroupTheory.Perm.FinThree.Basic

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix Equiv CFSG.RankThree.PartOne.N1322

variable {K : Type*} [Field K]

theorem det_mono_val (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    ((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (Equiv.Perm.sign σ : K) * ∏ j, (a j : K) := by
  have hM : ((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (Matrix.diagonal (fun j => (a j : K))).submatrix σ.symm id := by
    ext i j
    by_cases h : i = σ j
    · subst h
      simp [mono_val, monoMat_apply, Matrix.diagonal_apply]
    · have h' : σ.symm i ≠ j := fun hs => h (by rw [← hs]; simp)
      simp [mono_val, monoMat_apply, Matrix.diagonal_apply, h, h']
  rw [hM, Matrix.det_permute, Matrix.det_diagonal, Equiv.Perm.sign_symm]

theorem det_mono_eq_prod_of_mem_alternating (σ : Perm (Fin 3))
    (hσ : σ ∈ alternatingGroup (Fin 3)) (a : Fin 3 → Kˣ) :
    Matrix.GeneralLinearGroup.det (mono σ a) = ∏ j, a j := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_mono_val]
  have hsign : (Equiv.Perm.sign σ : K) = 1 := by
    rw [Equiv.Perm.mem_alternatingGroup.mp hσ]
    norm_num
  rw [hsign, one_mul]
  simp

theorem mono_cube (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    (mono σ a : GL (Fin 3) K) ^ 3 =
      mono (σ ^ 3) (fun j => a ((σ ^ 2) j) * a (σ j) * a j) := by
  have h2 : (mono σ a : GL (Fin 3) K) ^ 2 =
      mono (σ ^ 2) (fun j => a (σ j) * a j) := by
    rw [pow_two, mono_mul, pow_two]
  calc (mono σ a : GL (Fin 3) K) ^ 3
      = (mono σ a : GL (Fin 3) K) ^ 2 * mono σ a := by rw [pow_succ]
    _ = mono (σ ^ 2) (fun j => a (σ j) * a j) * mono σ a := by rw [h2]
    _ = mono (σ ^ 2 * σ) (fun j => (a (σ (σ j)) * a (σ j)) * a j) := by
      rw [mono_mul]
    _ = mono (σ ^ 3) (fun j => a ((σ ^ 2) j) * a (σ j) * a j) := by
      congr 1

private theorem unit_pow_three_eq_one (hcard : Nat.card Kˣ = 3) (u : Kˣ) : u ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := u)
  rwa [hcard] at h

private theorem cube_mono_eq_one_of_mem_alternating (hcard : Nat.card Kˣ = 3)
    {σ : Perm (Fin 3)} (hσ : σ ∈ alternatingGroup (Fin 3)) {a : Fin 3 → Kˣ}
    (hprod : ∏ j, a j = 1) : (mono σ a : GL (Fin 3) K) ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨σ, hσ⟩ : alternatingGroup (Fin 3)))
    rw [TauCeti.card_alternatingGroup_fin_three] at h
    exact Subtype.ext_iff.mp h
  have hunit : ∀ u : Kˣ, u ^ 3 = 1 := unit_pow_three_eq_one hcard
  rw [mono_cube, hσ3]
  have hb : (fun j : Fin 3 => a ((σ ^ 2) j) * a (σ j) * a j) = fun _ => (1 : Kˣ) := by
    by_cases hσ1 : σ = 1
    · funext j
      simp only [hσ1, pow_one, pow_two]
      show a j * a j * a j = 1
      simpa [pow_three, mul_assoc] using hunit (a j)
    · have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp hσ
      have hsupp_ge : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hσ1
      have hsupp_le : σ.support.card ≤ 3 := by
        simpa using Finset.card_le_univ σ.support
      have hsupp_ne_two : σ.support.card ≠ 2 := by
        intro h2
        have hswap : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp h2
        rw [hswap.sign_eq] at hsign
        norm_num at hsign
      have hsupp3 : σ.support.card = 3 := by
        have hne1 : σ.support.card ≠ 1 := Equiv.Perm.card_support_ne_one σ
        omega
      have hcyc : σ.IsThreeCycle := card_support_eq_three_iff.mp hsupp3
      have hsupp_univ : σ.support = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hsupp3, Fintype.card_fin]
      funext j
      have hnodup : ([j, σ j, σ (σ j)] : List (Fin 3)).Nodup :=
        hcyc.nodup_iff_mem_support.mpr (by rw [hsupp_univ]; exact Finset.mem_univ j)
      have hlist_univ : ([j, σ j, σ (σ j)] : List (Fin 3)).toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup hnodup, Fintype.card_fin]
        simp
      have hprod3 : (∏ i, a i) = a ((σ ^ 2) j) * a (σ j) * a j := by
        calc ∏ i, a i = ([j, σ j, σ (σ j)] : List (Fin 3)).toFinset.prod a := by
              rw [hlist_univ]
          _ = (([j, σ j, σ (σ j)] : List (Fin 3)).map a).prod := by
              rw [List.prod_toFinset _ hnodup]
          _ = a j * a (σ j) * a (σ (σ j)) := by simp [mul_assoc]
          _ = a ((σ ^ 2) j) * a (σ j) * a j := by
              rw [pow_two]
              ac_rfl
      rw [← hprod3, hprod]
  rw [hb, mono_one]

private theorem mono_one_const_eq_scalar (u : Kˣ) :
    (mono 1 (fun _ : Fin 3 => u) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  ext i j
  by_cases h : i = j <;>
    simp [mono_val, monoMat_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, h]

private def threeCycle : Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem threeCycle_mem_alternating : threeCycle ∈ alternatingGroup (Fin 3) := by
  rw [Equiv.Perm.mem_alternatingGroup, threeCycle, map_mul]
  rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]
  rw [Equiv.Perm.sign_swap (by decide : (1 : Fin 3) ≠ 2)]
  norm_num

private theorem threeCycle_inv_zero : threeCycle⁻¹ 0 = 2 := by
  decide

private theorem det_kernel_structure_of_even_monomial_frame [Finite K]
    (hK : Nat.card K = 4) {W : Subgroup (GL (Fin 3) K)}
    (hW : ∀ g : GL (Fin 3) K, g ∈ W ↔ ∃ σ : Perm (Fin 3),
      σ ∈ alternatingGroup (Fin 3) ∧ ∃ a : Fin 3 → Kˣ, g = mono σ a) :
    let H := W ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
    Nat.card H = 27 ∧
      (∀ x ∈ H, x ^ 3 = 1) ∧
      (∃ x y : H, x * y ≠ y * x) ∧
      CFSG.IsExtraspecialPGroup 3 H ∧
      ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := by
  classical
  let H := W ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
  have hcard_units : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  haveI : Nontrivial Kˣ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard_units]; norm_num)
  obtain ⟨lam, hlam⟩ := exists_ne (1 : Kˣ)
  let dvec : Fin 3 → Kˣ := ![lam, lam⁻¹, 1]
  let d : GL (Fin 3) K := mono 1 dvec
  let c : GL (Fin 3) K := mono threeCycle (fun _ => 1)
  let f : (alternatingGroup (Fin 3)) × (Kˣ × Kˣ) → H := fun p =>
    ⟨mono (p.1 : Perm (Fin 3)) ![p.2.1, p.2.2, (p.2.1 * p.2.2)⁻¹], by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hW]
        exact ⟨(p.1 : Perm (Fin 3)), p.1.2, _, rfl⟩
      · rw [MonoidHom.mem_ker, det_mono_eq_prod_of_mem_alternating _ p.1.2]
        simp [Fin.prod_univ_three]⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨σ, u, v⟩ ⟨τ, u', v'⟩ h
    have hmono : (mono σ ![u, v, (u * v)⁻¹] : GL (Fin 3) K) =
        mono τ ![u', v', (u' * v')⁻¹] := congrArg Subtype.val h
    obtain ⟨hστ, ha⟩ := mono_injective hmono
    have hu : u = u' := by
      have := congrFun ha 0
      simpa using this
    have hv : v = v' := by
      have := congrFun ha 1
      simpa using this
    subst hu
    subst hv
    exact Prod.ext (Subtype.ext hστ) rfl
  have hf_surj : Function.Surjective f := by
    intro x
    have hxW : (x : GL (Fin 3) K) ∈ W := x.2.1
    obtain ⟨σ, hσ, a, ha⟩ := (hW (x : GL (Fin 3) K)).mp hxW
    have hxdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 3) K) = 1 := by
      simpa [MonoidHom.mem_ker] using x.2.2
    have hprod : ∏ j, a j = 1 := by
      have := hxdet
      rw [ha, det_mono_eq_prod_of_mem_alternating σ hσ] at this
      exact this
    have h2 : a 2 = (a 0 * a 1)⁻¹ := by
      have h3 : a 0 * a 1 * a 2 = 1 := by
        simpa [Fin.prod_univ_three] using hprod
      simpa [mul_assoc] using congrArg (fun z => (a 0 * a 1)⁻¹ * z) h3
    refine ⟨⟨⟨σ, hσ⟩, a 0, a 1⟩, ?_⟩
    apply Subtype.ext
    change (mono σ ![a 0, a 1, (a 0 * a 1)⁻¹] : GL (Fin 3) K) = (x : GL (Fin 3) K)
    rw [ha]
    congr 1
    funext j
    fin_cases j <;> simp [h2]
  have hcardH : Nat.card H = 27 := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)]
    rw [Nat.card_prod, Nat.card_prod, hcard_units,
      TauCeti.card_alternatingGroup_fin_three]
  have hcube : ∀ x ∈ H, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨σ, hσ, a, ha⟩ := (hW (x : GL (Fin 3) K)).mp hx.1
    have hxdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 3) K) = 1 := by
      simpa [MonoidHom.mem_ker] using hx.2
    have hprod : ∏ j, a j = 1 := by
      have := hxdet
      rw [ha, det_mono_eq_prod_of_mem_alternating σ hσ] at this
      exact this
    have hx3 : (x : GL (Fin 3) K) ^ 3 = 1 := by
      rw [ha]
      exact cube_mono_eq_one_of_mem_alternating hcard_units hσ hprod
    simpa using hx3
  have hdW : d ∈ W := by
    rw [hW]
    exact ⟨1, by simp, dvec, rfl⟩
  have hdDet : d ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    rw [MonoidHom.mem_ker, det_mono_eq_prod_of_mem_alternating 1 (by simp)]
    simp [dvec, Fin.prod_univ_three]
  have hdH : d ∈ H := Subgroup.mem_inf.mpr ⟨hdW, hdDet⟩
  have hcW : c ∈ W := by
    rw [hW]
    exact ⟨threeCycle, threeCycle_mem_alternating, fun _ => 1, rfl⟩
  have hcDet : c ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    rw [MonoidHom.mem_ker, det_mono_eq_prod_of_mem_alternating threeCycle
      threeCycle_mem_alternating]
    simp
  have hcH : c ∈ H := Subgroup.mem_inf.mpr ⟨hcW, hcDet⟩
  have hcd : c * d * c⁻¹ ≠ d := by
    intro h
    have hmono : (mono (1 : Perm (Fin 3)) (fun j => dvec (threeCycle⁻¹ j)) : GL (Fin 3) K) =
        mono (1 : Perm (Fin 3)) dvec := by
      simpa [c, d, mono_mul_diag_mul_inv] using h
    have hfun := (mono_injective hmono).2
    have h0 := congrFun hfun 0
    rw [threeCycle_inv_zero] at h0
    simp [dvec] at h0
    exact hlam h0.symm
  have hneqcd : c * d ≠ d * c := by
    intro h
    apply hcd
    calc c * d * c⁻¹ = d * c * c⁻¹ := by rw [h]
      _ = d := by simp
  have hncH : ∃ x y : H, x * y ≠ y * x := by
    refine ⟨⟨c, hcH⟩, ⟨d, hdH⟩, ?_⟩
    intro h
    apply hneqcd
    have := congrArg Subtype.val h
    simpa using this
  have hscalar : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ H := by
    intro u
    have hu3 : u ^ 3 = 1 := unit_pow_three_eq_one hcard_units u
    have hscW : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ W := by
      rw [hW]
      exact ⟨1, by simp, fun _ => u, (mono_one_const_eq_scalar u).symm⟩
    have hscDet : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈
        (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
      rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.det_scalar]
      simpa using hu3
    exact Subgroup.mem_inf.mpr ⟨hscW, hscDet⟩
  have hnc : ¬ IsMulCommutative H := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hncH
    exact hxy (isMulCommutative_iff.mp hcomm x y)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 H := IsPGroup.of_card (n := 3) (by rw [hcardH]; norm_num)
  have hext : CFSG.IsExtraspecialPGroup 3 H :=
    CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP
      (fun x : H => Subtype.ext (by
        have hx3 := hcube (x : GL (Fin 3) K) x.2
        simpa using hx3)) hcardH hnc
  exact ⟨hcardH, hcube, hncH, hext, hscalar⟩

theorem det_kernel_structure_of_transitive_monomial_card_eighty_one
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {J : Subgroup (GL (Fin 3) K)}
    (hmono : IsTransitiveMonomial J) (hcard : Nat.card J = 81) :
    let H := J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
    Nat.card H = 27 ∧
      (∀ x ∈ H, x ^ 3 = 1) ∧
      (∃ x y : H, x * y ≠ y * x) ∧
      CFSG.IsExtraspecialPGroup 3 H ∧
      ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := by
  classical
  obtain ⟨P, hframe⟩ := exists_even_monomial_frame_of_card_eighty_one hK hmono hcard
  let e : GL (Fin 3) K →* GL (Fin 3) K := (MulAut.conj P).toMonoidHom
  let J' : Subgroup (GL (Fin 3) K) := J.map e
  have hframe' : ∀ g : GL (Fin 3) K, g ∈ J' ↔ ∃ σ : Perm (Fin 3),
      σ ∈ alternatingGroup (Fin 3) ∧ ∃ a : Fin 3 → Kˣ, g = mono σ a := hframe
  obtain ⟨hcardH', hcubeH', hncH', _, hscalarH'⟩ :=
    det_kernel_structure_of_even_monomial_frame hK hframe'
  let H := J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
  have hinj : Function.Injective e := (MulAut.conj P).injective
  have he_symm : ∀ z : GL (Fin 3) K, e ((MulAut.conj P).symm z) = z := by
    intro z
    change (MulAut.conj P) ((MulAut.conj P).symm z) = z
    exact MulEquiv.apply_symm_apply (MulAut.conj P) z
  have hker : (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker.map e =
      (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    simpa [e] using Subgroup.Normal.map_conj_eq
      (H := (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker) P
  have hmap : H.map e = J' ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    change (J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker).map e = _
    rw [Subgroup.map_inf _ _ _ (show Function.Injective e from hinj), hker]
  have hcardH : Nat.card H = 27 := by
    calc Nat.card H = Nat.card (H.map e) :=
          (Subgroup.card_map_of_injective (f := e) hinj).symm
      _ = Nat.card ↥(J' ⊓ (Matrix.GeneralLinearGroup.det :
            GL (Fin 3) K →* Kˣ).ker) := by rw [hmap]
      _ = 27 := hcardH'
  have hcubeH : ∀ x ∈ H, x ^ 3 = 1 := by
    intro x hx
    have hx' : e x ∈ J' ⊓ (Matrix.GeneralLinearGroup.det :
        GL (Fin 3) K →* Kˣ).ker := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hx'3 : (e x) ^ 3 = 1 := hcubeH' (e x) hx'
    have hxe : e (x ^ 3) = 1 := by
      rw [map_pow]
      exact hx'3
    exact hinj (by simpa using hxe)
  have hncH : ∃ x y : H, x * y ≠ y * x := by
    obtain ⟨x', y', hxy'⟩ := hncH'
    have hxpre : (MulAut.conj P).symm (x' : GL (Fin 3) K) ∈ H := by
      rw [← Subgroup.mem_map_iff_mem (f := e) hinj, hmap, he_symm]
      exact x'.2
    have hypre : (MulAut.conj P).symm (y' : GL (Fin 3) K) ∈ H := by
      rw [← Subgroup.mem_map_iff_mem (f := e) hinj, hmap, he_symm]
      exact y'.2
    let x : H := ⟨(MulAut.conj P).symm (x' : GL (Fin 3) K), hxpre⟩
    let y : H := ⟨(MulAut.conj P).symm (y' : GL (Fin 3) K), hypre⟩
    refine ⟨x, y, ?_⟩
    intro h
    apply hxy'
    apply Subtype.ext
    have hex : e (x : GL (Fin 3) K) = (x' : GL (Fin 3) K) := by
      dsimp [x]
      exact he_symm (x' : GL (Fin 3) K)
    have hey : e (y : GL (Fin 3) K) = (y' : GL (Fin 3) K) := by
      dsimp [y]
      exact he_symm (y' : GL (Fin 3) K)
    have h' := congrArg (fun z : H => e (z : GL (Fin 3) K)) h
    simp only [Subgroup.coe_mul, map_mul, hex, hey] at h'
    exact h'
  have hscalarH : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := by
    intro c
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈
        J' ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
      hscalarH' c
    have hcmap : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H.map e := by
      rwa [hmap]
    have hcpre : (MulAut.conj P).symm (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ∈ H := by
      rw [← Subgroup.mem_map_iff_mem (f := e) hinj, he_symm]
      exact hcmap
    have hcenter : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈
        Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hfix : (MulAut.conj P).symm (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [MulAut.conj_symm_apply]
      calc P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * P =
            Matrix.GeneralLinearGroup.scalar (Fin 3) c * P⁻¹ * P := by
              rw [Subgroup.mem_center_iff.mp hcenter P⁻¹]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by simp
    rw [hfix] at hcpre
    exact hcpre
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnc : ¬ IsMulCommutative H := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hncH
    exact hxy (isMulCommutative_iff.mp hcomm x y)
  have hP : IsPGroup 3 H := IsPGroup.of_card (n := 3) (by rw [hcardH]; norm_num)
  have hext : CFSG.IsExtraspecialPGroup 3 H :=
    CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP
      (fun x : H => Subtype.ext (by
        have hx3 := hcubeH (x : GL (Fin 3) K) x.2
        simpa using hx3)) hcardH hnc
  exact ⟨hcardH, hcubeH, hncH, hext, hscalarH⟩

end CFSG.RankThree.SubgroupLists
