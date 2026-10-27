module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs
import CFSG.ClassicalInvolution.Phan.PhanD4Tor

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

@[expose] noncomputable def chiE (M : CoxeterMatrix (Fin n)) (i j : Fin n)
    (x : normOne (unitaryInvolution K 2 f)) : normOne (unitaryInvolution K 2 f) :=
  if i = j then x * x else if M i j = 3 then x⁻¹ else 1

@[expose] noncomputable def rhoE (M : CoxeterMatrix (Fin n)) (j : Fin n)
    (t : Fin n → normOne (unitaryInvolution K 2 f)) : normOne (unitaryInvolution K 2 f) :=
  ∏ i, chiE M i j (t i)

section Helpers

private theorem hmbTor_chiE_mul (i j : Fin n) (x y : normOne (unitaryInvolution K 2 f)) :
    chiE M i j (x * y) = chiE M i j x * chiE M i j y := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [chiE, if_pos rfl]
    exact mul_mul_mul_comm x y x y
  · by_cases h3 : M i j = 3
    · simp only [chiE, if_neg hij, if_pos h3, mul_inv_rev]
      exact mul_comm _ _
    · simp only [chiE, if_neg hij, if_neg h3, mul_one]

private theorem hmbTor_chiE_one (i j : Fin n) :
    chiE M i j (1 : normOne (unitaryInvolution K 2 f)) = 1 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [chiE]
  · by_cases h3 : M i j = 3
    · simp only [chiE, if_neg hij, if_pos h3, inv_one]
    · simp only [chiE, if_neg hij, if_neg h3]

private theorem hmbTor_rhoE_mul (j : Fin n) (t u : Fin n → normOne (unitaryInvolution K 2 f)) :
    rhoE M j (t * u) = rhoE M j t * rhoE M j u := by
  simp only [rhoE, Pi.mul_apply]
  have h : (∏ i, chiE M i j (t i * u i)) =
      ∏ i, chiE M i j (t i) * chiE M i j (u i) :=
    Finset.prod_congr rfl fun i _ => hmbTor_chiE_mul i j (t i) (u i)
  rw [h, Finset.prod_mul_distrib]

private theorem hmbTor_rhoE_one (j : Fin n) :
    rhoE M j (1 : Fin n → normOne (unitaryInvolution K 2 f)) = 1 := by
  simp [rhoE, hmbTor_chiE_one]

private theorem hmbTor_rhoE_mulSingle (a j : Fin n) (x : normOne (unitaryInvolution K 2 f)) :
    rhoE M j (Pi.mulSingle a x) = chiE M a j x := by
  rw [rhoE]
  refine (Finset.prod_eq_single a ?_ ?_).trans ?_
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb]
    exact hmbTor_chiE_one b j
  · intro ha
    exact absurd (Finset.mem_univ a) ha
  · rw [Pi.mulSingle_eq_same]

end Helpers

theorem PhanFamilyE.nodeTor_comm (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) (i j : Fin n)
    (x y : normOne (unitaryInvolution K 2 f)) :
    S.nodeTor i x * S.nodeTor j y = S.nodeTor j y * S.nodeTor i x := by
  rcases eq_or_ne i j with rfl | hij
  · rw [← map_mul, ← map_mul]
    exact congrArg _ (mul_comm x y)
  · rcases hM i j hij with h2 | h3
    · simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
      exact S.comm i j h2 _ _
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hi : S.ι i (torusTwo (unitaryInvolution K 2 f) x) =
            S.θ i j (embSUid (unitaryInvolution K 2 f) 2
              (torusTwo (unitaryInvolution K 2 f) x)) :=
          (DFunLike.congr_fun (S.left i j hlt h3) _).symm
        have hj : S.ι j (torusTwo (unitaryInvolution K 2 f) y) =
            S.θ i j (embSUid (unitaryInvolution K 2 f) 0
              (torusTwo (unitaryInvolution K 2 f) y)) :=
          (DFunLike.congr_fun (S.right i j hlt h3) _).symm
        simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
        rw [hi, hj, ← map_mul, ← map_mul]
        exact congrArg (S.θ i j) (embSUid_two_torus_comm x y)
      · have h3' : M j i = 3 := (M.symmetric j i).trans h3
        have hi : S.ι i (torusTwo (unitaryInvolution K 2 f) x) =
            S.θ j i (embSUid (unitaryInvolution K 2 f) 0
              (torusTwo (unitaryInvolution K 2 f) x)) :=
          (DFunLike.congr_fun (S.right j i hgt h3') _).symm
        have hj : S.ι j (torusTwo (unitaryInvolution K 2 f) y) =
            S.θ j i (embSUid (unitaryInvolution K 2 f) 2
              (torusTwo (unitaryInvolution K 2 f) y)) :=
          (DFunLike.congr_fun (S.left j i hgt h3') _).symm
        simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
        rw [hi, hj, ← map_mul, ← map_mul]
        exact congrArg (S.θ j i) (embSUid_two_torus_comm y x).symm

theorem PhanFamilyE.nodeTor_conj_ι (hK : Nat.card K = (2 ^ f) ^ 2) (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) (i j : Fin n)
    (x : normOne (unitaryInvolution K 2 f)) (A : Su K 2 f 2) :
    S.nodeTor i x * S.ι j A * (S.nodeTor i x)⁻¹ = S.ι j (conjDiag hK ![chiE M i j x, 1] A) := by
  rcases eq_or_ne i j with hij | hij
  · rw [hij]
    rw [show chiE M j j x = x * x by simp [chiE]]
    show S.ι j (torusTwo (unitaryInvolution K 2 f) x) * S.ι j A *
        (S.ι j (torusTwo (unitaryInvolution K 2 f) x))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, PhanD4.torusTwo_mul_mul_inv hK]
  · rcases hM i j hij with h2 | h3
    · rw [show chiE M i j x = 1 by simp [chiE, hij, h2]]
      have hc : S.nodeTor i x * S.ι j A = S.ι j A * S.nodeTor i x := by
        simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
        exact S.comm i j h2 _ _
      rw [hc, mul_inv_cancel_right]
      congr 1
      have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K 2 f)) = 1 := by
        ext k
        fin_cases k <;> rfl
      rw [h11, PhanD4.conjDiag_one]
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · rw [show chiE M i j x = x⁻¹ by simp [chiE, hij, h3]]
        simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
        have hi : S.ι i (torusTwo (unitaryInvolution K 2 f) x) =
            S.θ i j (embSUid (unitaryInvolution K 2 f) 2
              (torusTwo (unitaryInvolution K 2 f) x)) :=
          (DFunLike.congr_fun (S.left i j hlt h3) _).symm
        have hj : S.ι j A = S.θ i j (embSUid (unitaryInvolution K 2 f) 0 A) :=
          (DFunLike.congr_fun (S.right i j hlt h3) A).symm
        rw [hi, hj, ← map_inv, ← map_mul, ← map_mul, PhanD4.embSUid_two_torus_conj_zero hK]
        exact DFunLike.congr_fun (S.right i j hlt h3) _
      · rw [show chiE M i j x = x⁻¹ by simp [chiE, hij, h3]]
        simp only [PhanFamilyE.nodeTor, MonoidHom.comp_apply]
        have h3' : M j i = 3 := (M.symmetric j i).trans h3
        have hi : S.ι i (torusTwo (unitaryInvolution K 2 f) x) =
            S.θ j i (embSUid (unitaryInvolution K 2 f) 0
              (torusTwo (unitaryInvolution K 2 f) x)) :=
          (DFunLike.congr_fun (S.right j i hgt h3') _).symm
        have hj : S.ι j A = S.θ j i (embSUid (unitaryInvolution K 2 f) 2 A) :=
          (DFunLike.congr_fun (S.left j i hgt h3') A).symm
        rw [hi, hj, ← map_inv, ← map_mul, ← map_mul, PhanD4.embSUid_zero_torus_conj_two hK]
        exact DFunLike.congr_fun (S.left j i hgt h3') _

@[expose] noncomputable def PhanFamilyE.mTor (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) :
    (Fin n → normOne (unitaryInvolution K 2 f)) →* G :=
  MonoidHom.noncommPiCoprod (fun i => S.nodeTor i) (fun i j _ x y => S.nodeTor_comm hM i j x y)

theorem PhanFamilyE.mTor_mulSingle (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) (i : Fin n)
    (x : normOne (unitaryInvolution K 2 f)) : S.mTor hM (Pi.mulSingle i x) = S.nodeTor i x :=
  MonoidHom.noncommPiCoprod_mulSingle (N := fun _ => normOne (unitaryInvolution K 2 f))
    (fun i => S.nodeTor i) i x

theorem PhanFamilyE.range_mTor (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) : (S.mTor hM).range = S.torus := by
  show (MonoidHom.noncommPiCoprod (fun i => S.nodeTor i)
    (fun i j _ x y => S.nodeTor_comm hM i j x y)).range = ⨆ i, (S.nodeTor i).range
  exact MonoidHom.noncommPiCoprod_range (H := fun _ => normOne (unitaryInvolution K 2 f))
    (ϕ := fun i => S.nodeTor i)

theorem PhanFamilyE.Good.mTor_injective {S : PhanFamilyE K 2 f M G} (hg : S.Good) :
    Function.Injective (S.mTor hg.simplyLaced) := by
  show Function.Injective (MonoidHom.noncommPiCoprod (fun i => S.nodeTor i)
    (fun i j _ x y => S.nodeTor_comm hg.simplyLaced i j x y))
  exact MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    (H := fun _ => normOne (unitaryInvolution K 2 f)) (ϕ := fun i => S.nodeTor i) hg.indep
    (fun i => (hg.inj i).comp (torusTwo_injective (unitaryInvolution K 2 f)))

theorem PhanFamilyE.mTor_conj_ι (hK : Nat.card K = (2 ^ f) ^ 2) (S : PhanFamilyE K 2 f M G)
    (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3)
    (t : Fin n → normOne (unitaryInvolution K 2 f)) (j : Fin n) (A : Su K 2 f 2) :
    S.mTor hM t * S.ι j A * (S.mTor hM t)⁻¹ = S.ι j (conjDiag hK ![rhoE M j t, 1] A) := by
  have hmul : ∀ t u : Fin n → normOne (unitaryInvolution K 2 f),
      (∀ B : Su K 2 f 2, S.mTor hM t * S.ι j B * (S.mTor hM t)⁻¹ =
        S.ι j (conjDiag hK ![rhoE M j t, 1] B)) →
      (∀ B : Su K 2 f 2, S.mTor hM u * S.ι j B * (S.mTor hM u)⁻¹ =
        S.ι j (conjDiag hK ![rhoE M j u, 1] B)) →
      ∀ B : Su K 2 f 2, S.mTor hM (t * u) * S.ι j B * (S.mTor hM (t * u))⁻¹ =
        S.ι j (conjDiag hK ![rhoE M j (t * u), 1] B) := by
    intro t u ht hu B
    rw [map_mul, hmbTor_rhoE_mul j t u]
    calc (S.mTor hM t * S.mTor hM u) * S.ι j B * (S.mTor hM t * S.mTor hM u)⁻¹
        = S.mTor hM t * (S.mTor hM u * S.ι j B * (S.mTor hM u)⁻¹) *
            (S.mTor hM t)⁻¹ := by group
      _ = S.mTor hM t * S.ι j (conjDiag hK ![rhoE M j u, 1] B) * (S.mTor hM t)⁻¹ := by
            rw [hu B]
      _ = S.ι j (conjDiag hK ![rhoE M j t, 1] (conjDiag hK ![rhoE M j u, 1] B)) :=
            ht (conjDiag hK ![rhoE M j u, 1] B)
      _ = S.ι j (conjDiag hK ![rhoE M j t * rhoE M j u, 1] B) := by
            congr 1
            rw [PhanD4.conjDiag_two_mul]
  have h1 : ∀ B : Su K 2 f 2, S.mTor hM 1 * S.ι j B * (S.mTor hM 1)⁻¹ =
      S.ι j (conjDiag hK ![rhoE M j 1, 1] B) := by
    intro B
    rw [map_one, one_mul, inv_one, mul_one, hmbTor_rhoE_one j]
    congr 1
    have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K 2 f)) = 1 := by
      ext k
      fin_cases k <;> rfl
    rw [h11, PhanD4.conjDiag_one]
  have hgen : ∀ (a : Fin n) (x : normOne (unitaryInvolution K 2 f)),
      ∀ B : Su K 2 f 2, S.mTor hM (Pi.mulSingle a x) * S.ι j B *
        (S.mTor hM (Pi.mulSingle a x))⁻¹ =
        S.ι j (conjDiag hK ![rhoE M j (Pi.mulSingle a x), 1] B) := by
    intro a x B
    rw [S.mTor_mulSingle hM a x, hmbTor_rhoE_mulSingle a j x]
    exact S.nodeTor_conj_ι hK hM a j x B
  have hfin : ∀ s : Finset (Fin n), ∀ B : Su K 2 f 2,
      S.mTor hM (∏ i ∈ s, Pi.mulSingle i (t i)) * S.ι j B *
        (S.mTor hM (∏ i ∈ s, Pi.mulSingle i (t i)))⁻¹ =
      S.ι j (conjDiag hK ![rhoE M j (∏ i ∈ s, Pi.mulSingle i (t i)), 1] B) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using h1
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact hmul _ _ (hgen a (t a)) ih
  rw [show t = ∏ i, Pi.mulSingle i (t i) from (Finset.univ_prod_mulSingle t).symm]
  exact hfin Finset.univ A

theorem PhanFamilyE.torus_le_normalizer (hK : Nat.card K = (2 ^ f) ^ 2)
    (S : PhanFamilyE K 2 f M G) (hM : ∀ i j : Fin n, i ≠ j → M i j = 2 ∨ M i j = 3) (j : Fin n) :
    S.torus ≤ Subgroup.normalizer ((S.ι j).range : Set G) := by
  rw [← S.range_mTor hM]
  rintro g hg
  obtain ⟨t, rfl⟩ := hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ u : Fin n → normOne (unitaryInvolution K 2 f),
      ∀ x ∈ (S.ι j).range, S.mTor hM u * x * (S.mTor hM u)⁻¹ ∈ (S.ι j).range := by
    rintro u _ ⟨B, rfl⟩
    rw [S.mTor_conj_ι hK hM u j B]
    exact ⟨_, rfl⟩
  refine ⟨key t x, fun hx => ?_⟩
  have h2 := key t⁻¹ _ hx
  rw [map_inv] at h2
  simpa [mul_assoc] using h2

@[expose] noncomputable def PhanFamilyE.Good.phiT {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) : S.torus →* Y :=
  (F.mTor hg.simplyLaced).comp
    (((MulEquiv.subgroupCongr (S.range_mTor hg.simplyLaced)).symm.trans
      (MonoidHom.ofInjective hg.mTor_injective).symm).toMonoidHom)

theorem PhanFamilyE.Good.phiT_nodeTor {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] (F : PhanFamilyE K 2 f M Y) (i : Fin n) (x : normOne (unitaryInvolution K 2 f))
    (h : S.nodeTor i x ∈ S.torus) : hg.phiT F ⟨S.nodeTor i x, h⟩ = F.nodeTor i x := by
  have hinner : (MonoidHom.ofInjective hg.mTor_injective).symm
      ((MulEquiv.subgroupCongr (S.range_mTor hg.simplyLaced)).symm ⟨S.nodeTor i x, h⟩) =
      Pi.mulSingle i x := by
    apply (MonoidHom.ofInjective hg.mTor_injective).injective
    rw [MulEquiv.apply_symm_apply]
    ext
    rw [MulEquiv.subgroupCongr_symm_apply, MonoidHom.ofInjective_apply,
      S.mTor_mulSingle hg.simplyLaced i x]
  show (F.mTor hg.simplyLaced) ((MonoidHom.ofInjective hg.mTor_injective).symm
      ((MulEquiv.subgroupCongr (S.range_mTor hg.simplyLaced)).symm ⟨S.nodeTor i x, h⟩)) =
    F.nodeTor i x
  rw [hinner]
  exact F.mTor_mulSingle hg.simplyLaced i x

end CFSG.ClassicalInvolution.Phan.PhanE
