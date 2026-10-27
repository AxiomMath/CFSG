module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggQ2s08r4_model_x_eq_sum_basis
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) :
    M.model (Additive.ofMul ⟨x, M.hx⟩) = ∑ i, ggQ2s08r4_basis M f hf i := by
  rw [ggQ2s08r4_model_x M f hf]
  exact Finset.sum_congr rfl fun j _ => (ggQ2s08r4_basis_apply M f hf j).symm

theorem ggQ2s08r4_diagEquiv_sum
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (s : Fin N → ZMod 3) (hs : ∀ i, s i ≠ 0) (c : Fin N → ZMod 3) :
    ggQ2s08r4_diagEquiv M b s hs (∑ i, c i • b i) = ∑ i, (c i * s i) • b i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_smul, ggQ2s08r4_diagEquiv_basis, smul_smul]

theorem ggQ2s08r4_singleEquiv_model_x_sum
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (k : Fin N) :
    ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
        (M.model (Additive.ofMul ⟨x, M.hx⟩)) =
      ∑ i, ggQ2s08r4_singleSign k i • ggQ2s08r4_basis M f hf i := by
  rw [ggQ2s08r4_model_x_eq_sum_basis M f hf, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [ggQ2s08r4_singleEquiv_basis]

theorem ggQ2s08r4_diagEquiv_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (v : M.V)
    (hne : ∀ i, (ggQ2s08r4_basis M f hf).repr v i ≠ 0) :
    ggQ2s08r4_diagEquiv M (ggQ2s08r4_basis M f hf)
        (fun i => (ggQ2s08r4_basis M f hf).repr v i) hne
        (M.model (Additive.ofMul ⟨x, M.hx⟩)) = v := by
  rw [ggQ2s08r4_model_x_eq_sum_basis M f hf]
  conv_lhs => rw [show (∑ i, ggQ2s08r4_basis M f hf i) =
    ∑ i, (1 : ZMod 3) • ggQ2s08r4_basis M f hf i by simp]
  rw [ggQ2s08r4_diagEquiv_sum]
  simp only [one_mul]
  exact (ggQ2s08r4_basis M f hf).sum_repr v

theorem ggQ2s08r4_diagEquiv_single_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (k : Fin N) (v : M.V)
    (hne : ∀ i, ggQ2s08r4_singleSign k i * (ggQ2s08r4_basis M f hf).repr v i ≠ 0) :
    ggQ2s08r4_diagEquiv M (ggQ2s08r4_basis M f hf)
        (fun i => ggQ2s08r4_singleSign k i * (ggQ2s08r4_basis M f hf).repr v i) hne
        (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
          (M.model (Additive.ofMul ⟨x, M.hx⟩))) = v := by
  rw [ggQ2s08r4_singleEquiv_model_x_sum M f hf k, ggQ2s08r4_diagEquiv_sum]
  conv_rhs => rw [← (ggQ2s08r4_basis M f hf).sum_repr v]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← mul_assoc, ggQ2s08r4_singleSign_sq, one_mul]

theorem ggQ2s08r4_repr_single_apply
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (k : Fin N) (u : M.V) (i : Fin N) :
    (ggQ2s08r4_basis M f hf).repr
        (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k u) i =
      (ggQ2s08r4_basis M f hf).repr u i +
        (ggQ2s08r4_basis M f hf).repr u k * (if i = k then 1 else 0) := by
  rw [ggQ2s08r4_singleEquiv_apply, map_add, map_smul, Module.Basis.repr_self]
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : k = i
  · rw [if_pos h, if_pos h.symm]
    simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    simp

theorem ggQ2s08r4_sign_K_le
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (h2 : 2 ≤ N)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (Q : Fin N → Subgroup G)
    (hQle : ∀ j, Q j ≤ L)
    (hQcomp : ∀ j, LargeEvenPComponent 3 (Subgroup.centralizer
      ({x, ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G)) (Q j))
    (hQnorm : ∀ j, Bs ≤ Subgroup.normalizer (Q j : Set G))
    (hQa : ∀ j, 4 ∣ Nat.card ↥(ggAutomizer (Q j) Bs))
    (hQgen : ∀ i j, i ≠ j → Q i ⊔ Q j = L)
    (hD : ∀ T : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f T →
      ∃ (m : G) (θ : MulAut ↥Bs), GGQ2Ind Bs m θ ∧
        m ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧
        ggLin (p := 3) M.model θ = T)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    {k : Fin N} (hlin : ggLin (p := 3) M.model φ =
      ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k)
    {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K) :
    K.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
  classical
  have hLpair : GGStdPair' 3 Bs x L := ggStdPair'_L hP hS.1 hCav
  have hLg_le : L.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J :=
    ggQ2s08r4_sign_L_le hLB hP hS hCav M h2 f hf Q hQle hQcomp hQnorm hQa hQgen hD hInd hlin
  have hKpair : GGStdPair' 3 Bs y K := ggStdPair'_nbr hLB hP hS.1 hCav hnbr
  let yB : ↥Bs := ⟨y, hKpair.1⟩
  let wB : ↥Bs := φ yB
  let v : M.V := M.model (Additive.ofMul wB)
  have hv_single : v = ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
      (M.model (Additive.ofMul yB)) := by
    change M.model (Additive.ofMul wB) = _
    rw [show M.model (Additive.ofMul wB) =
        ggLin (p := 3) M.model φ (M.model (Additive.ofMul yB)) from
      (ggLin_apply_ofMul M.model φ yB).symm, hlin]
  have hKg_pair : GGStdPair' 3 Bs (wB : G) (K.map (MulAut.conj g).toMonoidHom) := by
    have h := ggStdPair'_conj hInd.1 hKpair
    rw [show g * y * g⁻¹ = (wB : G) from by
      rw [show y = (yB : G) from rfl]; exact ggQ2s08r4_conj_eq hInd yB] at h
    exact h
  by_cases hzero : ∃ j : Fin N, (ggQ2s08r4_basis M f hf).repr
      (M.model (Additive.ofMul yB)) j = 0
  ·
    obtain ⟨j, hj⟩ := hzero
    have hTeven : GGQ2S08MonoEven f
        (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k *
          ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) j) :=
      ggQ2s08r4_monoEven_mul_single M f hf j k
    obtain ⟨m, θ, hIndm, hmG0, hmlin⟩ := hD _ hTeven
    have hmy : m * y * m⁻¹ = (wB : G) := by
      have h := ggQ2s08r4_conj_eq_of_lin M hIndm yB wB ?_
      · simpa using h
      · rw [hmlin, LinearEquiv.mul_apply,
          ggQ2s08r4_singleEquiv_eq_self M (ggQ2s08r4_basis M f hf) j hj,
          show M.model (Additive.ofMul wB) = v from rfl]
        exact hv_single.symm
    have hKm_pair : GGStdPair' 3 Bs (wB : G) (K.map (MulAut.conj m).toMonoidHom) := by
      have h := ggStdPair'_conj hIndm.1 hKpair
      rwa [hmy] at h
    have hKm_le : K.map (MulAut.conj m).toMonoidHom ≤ ggG0 3 B x L D J :=
      calc K.map (MulAut.conj m).toMonoidHom
          ≤ (ggG0 3 B x L D J).map (MulAut.conj m).toMonoidHom :=
            Subgroup.map_mono (le_ggG0_of_ggNbr hnbr)
        _ = ggG0 3 B x L D J := map_conj_eq_of_mem_normalizer hmG0
    have huniq : K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj m).toMonoidHom :=
      ggStdPair'_unique hLB hS.1 rfl hKg_pair hKm_pair
    rw [huniq]
    exact hKm_le
  ·
    have hne_y : ∀ i, (ggQ2s08r4_basis M f hf).repr (M.model (Additive.ofMul yB)) i ≠ 0 :=
      fun i hi => hzero ⟨i, hi⟩
    have hne_v : ∀ i, (ggQ2s08r4_basis M f hf).repr v i ≠ 0 := by
      intro i
      rw [hv_single, ggQ2s08r4_repr_single_apply]
      by_cases hik : i = k
      · rw [if_pos hik, hik, mul_one, ← two_mul]
        exact mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hne_y k)
      · rw [if_neg hik, mul_zero, add_zero]
        exact hne_y i
    by_cases he : (∏ i, (ggQ2s08r4_basis M f hf).repr v i) = 1
    ·
      have hTeven : GGQ2S08MonoEven f
          (ggQ2s08r4_diagEquiv M (ggQ2s08r4_basis M f hf)
            (fun i => (ggQ2s08r4_basis M f hf).repr v i) hne_v) :=
        ggQ2s08r4_monoEven_diag M f hf _ hne_v he
      obtain ⟨m, θ, hIndm, hmG0, hmlin⟩ := hD _ hTeven
      have hmx : m * x * m⁻¹ = (wB : G) := by
        have h := ggQ2s08r4_conj_eq_of_lin M hIndm ⟨x, M.hx⟩ wB ?_
        · simpa using h
        · rw [hmlin]
          exact ggQ2s08r4_diagEquiv_x M f hf v hne_v
      have hLm_pair : GGStdPair' 3 Bs (wB : G) (L.map (MulAut.conj m).toMonoidHom) := by
        have h := ggStdPair'_conj hIndm.1 hLpair
        rwa [hmx] at h
      have hLm_le : L.map (MulAut.conj m).toMonoidHom ≤ ggG0 3 B x L D J :=
        calc L.map (MulAut.conj m).toMonoidHom
            ≤ (ggG0 3 B x L D J).map (MulAut.conj m).toMonoidHom :=
              Subgroup.map_mono (le_ggG0_left 3 B x L D J)
          _ = ggG0 3 B x L D J := map_conj_eq_of_mem_normalizer hmG0
      have huniq : K.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj m).toMonoidHom :=
        ggStdPair'_unique hLB hS.1 rfl hKg_pair hLm_pair
      rw [huniq]
      exact hLm_le
    ·
      have hpsq : (∏ i, (ggQ2s08r4_basis M f hf).repr v i) *
          (∏ i, (ggQ2s08r4_basis M f hf).repr v i) = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => ggQ2s08r4_zmod3_sq _ (hne_v i)
      have heneg : (∏ i, (ggQ2s08r4_basis M f hf).repr v i) = -1 :=
        ggQ2s08r4_zmod3_eq_neg_one _ he hpsq
      let s : Fin N → ZMod 3 := fun i =>
        ggQ2s08r4_singleSign k i * (ggQ2s08r4_basis M f hf).repr v i
      have hs : ∀ i, s i ≠ 0 := fun i =>
        mul_ne_zero (ggQ2s08r4_singleSign_ne_zero k i) (hne_v i)
      have hprod : ∏ i, s i = 1 := by
        rw [Finset.prod_mul_distrib, ggQ2s08r4_singleSign_prod, heneg]
        decide
      have hTeven : GGQ2S08MonoEven f
          (ggQ2s08r4_diagEquiv M (ggQ2s08r4_basis M f hf) s hs) :=
        ggQ2s08r4_monoEven_diag M f hf s hs hprod
      obtain ⟨m, θ, hIndm, hmG0, hmlin⟩ := hD _ hTeven
      let x'B : ↥Bs := φ ⟨x, M.hx⟩
      have hx'model : M.model (Additive.ofMul x'B) =
          ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
            (M.model (Additive.ofMul ⟨x, M.hx⟩)) := by
        rw [show M.model (Additive.ofMul x'B) =
            ggLin (p := 3) M.model φ (M.model (Additive.ofMul ⟨x, M.hx⟩)) from
          (ggLin_apply_ofMul M.model φ ⟨x, M.hx⟩).symm, hlin]
      have hmx' : m * (x'B : G) * m⁻¹ = (wB : G) := by
        have h := ggQ2s08r4_conj_eq_of_lin M hIndm x'B wB ?_
        · exact h
        · rw [hmlin, hx'model]
          exact ggQ2s08r4_diagEquiv_single_x M f hf k v hs
      have hLg_pair : GGStdPair' 3 Bs (x'B : G) (L.map (MulAut.conj g).toMonoidHom) := by
        have h := ggStdPair'_conj hInd.1 hLpair
        rwa [show g * x * g⁻¹ = (x'B : G) from
          ggQ2s08r4_conj_eq hInd ⟨x, M.hx⟩] at h
      have hLgm_pair : GGStdPair' 3 Bs (wB : G)
          ((L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m).toMonoidHom) := by
        have h := ggStdPair'_conj hIndm.1 hLg_pair
        rwa [hmx'] at h
      have hLgm_le : (L.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj m).toMonoidHom ≤ ggG0 3 B x L D J :=
        calc (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m).toMonoidHom
            ≤ (ggG0 3 B x L D J).map (MulAut.conj m).toMonoidHom :=
              Subgroup.map_mono hLg_le
          _ = ggG0 3 B x L D J := map_conj_eq_of_mem_normalizer hmG0
      have huniq : K.map (MulAut.conj g).toMonoidHom =
          (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m).toMonoidHom :=
        ggStdPair'_unique hLB hS.1 rfl hKg_pair hLgm_pair
      rw [huniq]
      exact hLgm_le

theorem ggQ2s08r4_sign
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (h2 : 2 ≤ N)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (Q : Fin N → Subgroup G)
    (hQle : ∀ j, Q j ≤ L)
    (hQcomp : ∀ j, LargeEvenPComponent 3 (Subgroup.centralizer
      ({x, ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G)) (Q j))
    (hQnorm : ∀ j, Bs ≤ Subgroup.normalizer (Q j : Set G))
    (hQa : ∀ j, 4 ∣ Nat.card ↥(ggAutomizer (Q j) Bs))
    (hQgen : ∀ i j, i ≠ j → Q i ⊔ Q j = L)
    (hD : ∀ T : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f T →
      ∃ (m : G) (θ : MulAut ↥Bs), GGQ2Ind Bs m θ ∧
        m ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧
        ggLin (p := 3) M.model θ = T)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    (hcase : ∃ k : Fin N, ggLin (p := 3) M.model φ =
      ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  obtain ⟨k, hk⟩ := hcase
  exact ggQ2s08r4_final hS hInd.1
    (ggQ2s08r4_sign_L_le hLB hP hS hCav M h2 f hf Q hQle hQcomp hQnorm hQa hQgen hD hInd hk)
    fun y K hnbr =>
      ggQ2s08r4_sign_K_le hLB hP hS hCav M h2 f hf Q hQle hQcomp hQnorm hQa hQgen hD hInd hk hnbr

end CFSG.StandardType

end
