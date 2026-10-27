module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.MultiplierDefs
import CFSG.GroupTheory.CentralCoverTorus
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicWeyl
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylLift
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)

@[expose] def Deg5Frame (X : Type) [Group X] : Prop :=
  ∃ e₀ e₁ e₂ w₀ w₁ w₂ : X,
    Commute e₀ e₁ ∧ Commute e₀ e₂ ∧ Commute e₁ e₂ ∧
    e₀ ^ 5 = 1 ∧ e₁ ^ 5 = 1 ∧ e₂ ^ 5 = 1 ∧
    (∀ a b c : ℕ, e₀ ^ a * e₁ ^ b * e₂ ^ c = 1 → 5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c) ∧
    w₀ * e₀ * w₀⁻¹ = e₀⁻¹ ∧ w₀ * e₁ * w₀⁻¹ = e₁ ∧ w₀ * e₂ * w₀⁻¹ = e₂ ∧
    w₁ * e₁ * w₁⁻¹ = e₁⁻¹ ∧ w₁ * e₂ * w₁⁻¹ = e₂ ∧
    w₂ * e₂ * w₂⁻¹ = e₂⁻¹

theorem Deg5Frame.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Deg5Frame X') : Deg5Frame X := by
  obtain ⟨e₀, e₁, e₂, w₀, w₁, w₂, hc₀₁, hc₀₂, hc₁₂, he₀, he₁, he₂, hind,
    hw₀e₀, hw₀e₁, hw₀e₂, hw₁e₁, hw₁e₂, hw₂e₂⟩ := h
  refine ⟨e.symm e₀, e.symm e₁, e.symm e₂, e.symm w₀, e.symm w₁, e.symm w₂,
    hc₀₁.map e.symm, hc₀₂.map e.symm, hc₁₂.map e.symm, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, he₀, map_one]
  · rw [← map_pow, he₁, map_one]
  · rw [← map_pow, he₂, map_one]
  · intro a b c h
    refine hind a b c ?_
    have h' := congrArg (fun x => e x) h
    simpa [map_mul, map_pow] using h'
  · apply e.injective
    simpa [map_mul, map_inv] using hw₀e₀
  · apply e.injective
    simpa [map_mul, map_inv] using hw₀e₁
  · apply e.injective
    simpa [map_mul, map_inv] using hw₀e₂
  · apply e.injective
    simpa [map_mul, map_inv] using hw₁e₁
  · apply e.injective
    simpa [map_mul, map_inv] using hw₁e₂
  · apply e.injective
    simpa [map_mul, map_inv] using hw₂e₂

private theorem uc22s2112r34_deg5_pow_eq_one_of_conj_inv {Y : Type} [Group Y]
    {e w z : Y} {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y) (hz : z ∈ Z)
    (hz5 : z ^ 5 = 1) (he5 : e ^ 5 ∈ Z) (he25 : e ^ 25 = 1)
    (hconj : w * e * w⁻¹ = e⁻¹ * z) : e ^ 5 = 1 := by
  have hcz : Commute e⁻¹ z := Subgroup.mem_center_iff.mp (hZ hz) e⁻¹
  have hzpow : (e⁻¹ * z) ^ 5 = (e ^ 5)⁻¹ := by
    rw [hcz.mul_pow, hz5, mul_one, inv_pow]
  have hconj5 : (w * e * w⁻¹) ^ 5 = w * e ^ 5 * w⁻¹ := by
    simpa [MulAut.conj_apply, mul_assoc] using (map_pow (MulAut.conj w) e 5).symm
  have h1 : w * e ^ 5 * w⁻¹ = (e ^ 5)⁻¹ := by
    rw [← hconj5, hconj, hzpow]
  have h2 : w * e ^ 5 * w⁻¹ = e ^ 5 := by
    rw [Subgroup.mem_center_iff.mp (hZ he5) w, mul_assoc, mul_inv_cancel, mul_one]
  have h5inv : e ^ 5 = (e ^ 5)⁻¹ := h2.symm.trans h1
  have h10 : e ^ 10 = 1 := by
    have h := congrArg (fun x => x * e ^ 5) h5inv
    rw [inv_mul_cancel] at h
    simpa [← pow_add] using h
  have hg : e ^ Nat.gcd 10 25 = 1 := pow_gcd_eq_one.mpr ⟨h10, he25⟩
  norm_num at hg
  exact hg

private theorem uc22s2112r34_deg5_noncommProd_univ_four {M : Type*} [Group M] (f : Fin 4 → M)
    (comm : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise
      (fun x y => Commute (f x) (f y))) :
    (Finset.univ : Finset (Fin 4)).noncommProd f comm = f 0 * f 1 * f 2 * f 3 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.noncommProd_univ_fin f comm]
  simp [List.ofFn, List.prod, Fin.foldr, Fin.foldr.loop, mul_assoc]

theorem four_le_pRank_of_deg5Frame {Y X : Type} [Group Y] [Finite Y] [Group X] (φ : Y →* X)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (hexp : ∀ z ∈ φ.ker, z ^ 5 = 1) (hnt : φ.ker ≠ ⊥) (hF : Deg5Frame X) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e₀, e₁, e₂, w₀, w₁, w₂, hc₀₁, hc₀₂, hc₁₂, he₀, he₁, he₂, hind,
    hw₀e₀, hw₀e₁, hw₀e₂, hw₁e₁, hw₁e₂, hw₂e₂⟩ := hF
  let S : Set X := {e₀, e₁, e₂}
  have hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    intro s hs t ht
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact Commute.refl _
    · exact hc₀₁
    · exact hc₀₂
    · exact hc₀₁.symm
    · exact Commute.refl _
    · exact hc₁₂
    · exact hc₀₂.symm
    · exact hc₁₂.symm
    · exact Commute.refl _
  have hodd : ∀ s ∈ S, Odd (orderOf s) := by
    intro s hs
    have h5 : s ^ 5 = 1 := by
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl <;> assumption
    rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h5) with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hinv : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (∃ g : X, g * s * g⁻¹ = s⁻¹ ∧ g * t * g⁻¹ = t) ∨
        (∃ g : X, g * t * g⁻¹ = t⁻¹ ∧ g * s * g⁻¹ = s) := by
    intro s hs t ht hst
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact absurd rfl hst
    · exact Or.inl ⟨w₀, hw₀e₀, hw₀e₁⟩
    · exact Or.inl ⟨w₀, hw₀e₀, hw₀e₂⟩
    · exact Or.inr ⟨w₀, hw₀e₀, hw₀e₁⟩
    · exact absurd rfl hst
    · exact Or.inl ⟨w₁, hw₁e₁, hw₁e₂⟩
    · exact Or.inr ⟨w₀, hw₀e₀, hw₀e₂⟩
    · exact Or.inr ⟨w₁, hw₁e₁, hw₁e₂⟩
    · exact absurd rfl hst
  have hcomm := CFSG.GroupTheory.comap_closure_comm_of_inverters hφ hker hS hodd hinv
  obtain ⟨E₀, hE₀⟩ := hφ e₀
  obtain ⟨E₁, hE₁⟩ := hφ e₁
  obtain ⟨E₂, hE₂⟩ := hφ e₂
  obtain ⟨W₀, hW₀⟩ := hφ w₀
  obtain ⟨W₁, hW₁⟩ := hφ w₁
  obtain ⟨W₂, hW₂⟩ := hφ w₂
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hnt)
  have hzK : (z : Y) ∈ φ.ker := z.2
  have hzmem : (z : Y) ∈ (Subgroup.closure S).comap φ := by
    rw [Subgroup.mem_comap]
    simp [MonoidHom.mem_ker.mp hzK]
  have hmem₀ : E₀ ∈ (Subgroup.closure S).comap φ := by
    rw [Subgroup.mem_comap, hE₀]
    exact Subgroup.subset_closure (by simp [S])
  have hmem₁ : E₁ ∈ (Subgroup.closure S).comap φ := by
    rw [Subgroup.mem_comap, hE₁]
    exact Subgroup.subset_closure (by simp [S])
  have hmem₂ : E₂ ∈ (Subgroup.closure S).comap φ := by
    rw [Subgroup.mem_comap, hE₂]
    exact Subgroup.subset_closure (by simp [S])
  have hE₀powker : E₀ ^ 5 ∈ φ.ker := by
    simp [MonoidHom.mem_ker, map_pow, hE₀, he₀]
  have hE₁powker : E₁ ^ 5 ∈ φ.ker := by
    simp [MonoidHom.mem_ker, map_pow, hE₁, he₁]
  have hE₂powker : E₂ ^ 5 ∈ φ.ker := by
    simp [MonoidHom.mem_ker, map_pow, hE₂, he₂]
  have hpow₀ : E₀ ^ 5 = 1 := by
    have hz₀ : E₀ * (W₀ * E₀ * W₀⁻¹) ∈ φ.ker := by
      simp [MonoidHom.mem_ker, map_mul, map_inv, hW₀, hE₀, hw₀e₀]
    refine uc22s2112r34_deg5_pow_eq_one_of_conj_inv (Z := φ.ker) (w := W₀)
      hker hz₀ (hexp _ hz₀) hE₀powker ?_ ?_
    · have h := hexp (E₀ ^ 5) hE₀powker
      simpa [← pow_mul] using h
    · group
  have hpow₁ : E₁ ^ 5 = 1 := by
    have hz₁ : E₁ * (W₁ * E₁ * W₁⁻¹) ∈ φ.ker := by
      simp [MonoidHom.mem_ker, map_mul, map_inv, hW₁, hE₁, hw₁e₁]
    refine uc22s2112r34_deg5_pow_eq_one_of_conj_inv (Z := φ.ker) (w := W₁)
      hker hz₁ (hexp _ hz₁) hE₁powker ?_ ?_
    · have h := hexp (E₁ ^ 5) hE₁powker
      simpa [← pow_mul] using h
    · group
  have hpow₂ : E₂ ^ 5 = 1 := by
    have hz₂ : E₂ * (W₂ * E₂ * W₂⁻¹) ∈ φ.ker := by
      simp [MonoidHom.mem_ker, map_mul, map_inv, hW₂, hE₂, hw₂e₂]
    refine uc22s2112r34_deg5_pow_eq_one_of_conj_inv (Z := φ.ker) (w := W₂)
      hker hz₂ (hexp _ hz₂) hE₂powker ?_ ?_
    · have h := hexp (E₂ ^ 5) hE₂powker
      simpa [← pow_mul] using h
    · group
  have hzord : orderOf (z : Y) = 5 := by
    refine orderOf_eq_prime (hexp (z : Y) hzK) ?_
    intro h
    exact hz1 (Subtype.ext h)
  let x : Fin 4 → Y := ![E₀, E₁, E₂, (z : Y)]
  have hxpow : ∀ i, x i ^ 5 = 1 := by
    intro i
    fin_cases i
    · simpa [x] using hpow₀
    · simpa [x] using hpow₁
    · simpa [x] using hpow₂
    · simpa [x] using hexp (z : Y) hzK
  have hxcomm : ∀ i j, i ≠ j → Commute (x i) (x j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [x, commute_iff_eq] using hcomm E₀ hmem₀ E₁ hmem₁
    · simpa [x, commute_iff_eq] using hcomm E₀ hmem₀ E₂ hmem₂
    · simpa [x, commute_iff_eq] using hcomm E₀ hmem₀ (z : Y) hzmem
    · simpa [x, commute_iff_eq] using (hcomm E₀ hmem₀ E₁ hmem₁).symm
    · exact absurd rfl hij
    · simpa [x, commute_iff_eq] using hcomm E₁ hmem₁ E₂ hmem₂
    · simpa [x, commute_iff_eq] using hcomm E₁ hmem₁ (z : Y) hzmem
    · simpa [x, commute_iff_eq] using (hcomm E₀ hmem₀ E₂ hmem₂).symm
    · simpa [x, commute_iff_eq] using (hcomm E₁ hmem₁ E₂ hmem₂).symm
    · exact absurd rfl hij
    · simpa [x, commute_iff_eq] using hcomm E₂ hmem₂ (z : Y) hzmem
    · simpa [x, commute_iff_eq] using (hcomm E₀ hmem₀ (z : Y) hzmem).symm
    · simpa [x, commute_iff_eq] using (hcomm E₁ hmem₁ (z : Y) hzmem).symm
    · simpa [x, commute_iff_eq] using (hcomm E₂ hmem₂ (z : Y) hzmem).symm
    · exact absurd rfl hij
  let ϕ : ∀ i : Fin 4, Multiplicative (ZMod 5) →* Y := fun i => {
    toFun := fun k => x i ^ (Multiplicative.toAdd k).val
    map_one' := by simp
    map_mul' := by
      intro a b
      rw [toAdd_mul, ZMod.val_add,
        ← pow_eq_pow_mod (a := x i) (m := (Multiplicative.toAdd a).val +
          (Multiplicative.toAdd b).val) (hxpow i), pow_add] }
  have hϕcomm : Pairwise fun i j : Fin 4 => ∀ a b : Multiplicative (ZMod 5),
      Commute (ϕ i a) (ϕ j b) := by
    intro i j hij a b
    exact (hxcomm i j hij).pow_pow _ _
  let F : (Fin 4 → Multiplicative (ZMod 5)) →* Y := MonoidHom.noncommPiCoprod ϕ hϕcomm
  have hFapply : ∀ v : Fin 4 → Multiplicative (ZMod 5),
      F v = x 0 ^ (v 0).toAdd.val * x 1 ^ (v 1).toAdd.val *
        x 2 ^ (v 2).toAdd.val * x 3 ^ (v 3).toAdd.val := by
    intro v
    change (MonoidHom.noncommPiCoprod ϕ hϕcomm) v = _
    rw [MonoidHom.noncommPiCoprod_apply]
    exact uc22s2112r34_deg5_noncommProd_univ_four _ _
  have hF : Function.Injective F := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hv1 : F v = 1 := MonoidHom.mem_ker.mp hv
    rw [hFapply v] at hv1
    have hφv : e₀ ^ (v 0).toAdd.val * e₁ ^ (v 1).toAdd.val *
        e₂ ^ (v 2).toAdd.val = 1 := by
      have h := congrArg φ hv1
      simpa [x, map_mul, map_pow, hE₀, hE₁, hE₂, MonoidHom.mem_ker.mp hzK] using h
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ hφv
    have h0 : (v 0).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt ha (ZMod.val_lt _)
    have h1 : (v 1).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt _)
    have h2 : (v 2).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hc (ZMod.val_lt _)
    have hzpow : (z : Y) ^ (v 3).toAdd.val = 1 := by
      have h := hv1
      simpa [x, h0, h1, h2] using h
    have h3 : (v 3).toAdd.val = 0 := by
      apply Nat.eq_zero_of_dvd_of_lt _ (ZMod.val_lt _)
      simpa [hzord] using orderOf_dvd_of_pow_eq_one hzpow
    funext i
    fin_cases i
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h0)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h1)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h2)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h3)
  have hcard : Nat.card (Fin 4 → Multiplicative (ZMod 5)) = 5 ^ 4 := by
    rw [Nat.card_pi]
    simp [Finset.prod_const]
  have hpowA : ∀ a : Fin 4 → Multiplicative (ZMod 5), a ^ 5 = 1 := by
    intro a
    funext i
    rw [Pi.pow_apply, ← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]
    rfl
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 5)
    (fun a b => mul_comm' a b) hpowA hcard F hF le_top

private noncomputable def uc22s2112r34_deg5_E0 {K : Type} [Field K] (u : Kˣ) :
    GL (Fin 5) K :=
  CFSG.SectionRank.ClassicalEven.torusDiag ![u, u⁻¹, 1, 1, 1]

private noncomputable def uc22s2112r34_deg5_E1 {K : Type} [Field K] (u : Kˣ) :
    GL (Fin 5) K :=
  CFSG.SectionRank.ClassicalEven.torusDiag ![1, 1, u, u⁻¹, 1]

private noncomputable def uc22s2112r34_deg5_E2 {K : Type} [Field K] (u : Kˣ) :
    GL (Fin 5) K :=
  CFSG.SectionRank.ClassicalEven.torusDiag ![u, u, 1, 1, u⁻¹ ^ 2]

private noncomputable def uc22s2112r34_deg5_E3 {K : Type} [Field K] (η : Kˣ) :
    GL (Fin 5) K :=
  CFSG.SectionRank.ClassicalEven.torusDiag ![η, η, η, η, η⁻¹ ^ 4]

private def uc22s2112r34_deg5_sgn0 {K : Type} [Field K] : Fin 5 → K :=
  ![1, -1, 1, 1, 1]

private def uc22s2112r34_deg5_sgn1 {K : Type} [Field K] : Fin 5 → K :=
  ![1, 1, 1, -1, 1]

private def uc22s2112r34_deg5_sgn2 {K : Type} [Field K] : Fin 5 → K :=
  ![1, 1, 1, 1, 1]

private noncomputable def uc22s2112r34_deg5_W0M {K : Type} [Field K] :
    Matrix (Fin 5) (Fin 5) K :=
  CFSG.LieType.Universal.SpecialLinear.signedPerm (Equiv.swap 0 1)
    (uc22s2112r34_deg5_sgn0 (K := K))

private noncomputable def uc22s2112r34_deg5_W1M {K : Type} [Field K] :
    Matrix (Fin 5) (Fin 5) K :=
  CFSG.LieType.Universal.SpecialLinear.signedPerm (Equiv.swap 2 3)
    (uc22s2112r34_deg5_sgn1 (K := K))

private noncomputable def uc22s2112r34_deg5_W2M {K : Type} [Field K] :
    Matrix (Fin 5) (Fin 5) K :=
  CFSG.LieType.Universal.SpecialLinear.signedPerm (Equiv.swap 0 2 * Equiv.swap 1 3)
    (uc22s2112r34_deg5_sgn2 (K := K))

private theorem uc22s2112r34_deg5_det_W0M {K : Type} [Field K] :
    (uc22s2112r34_deg5_W0M (K := K)).det = 1 := by
  rw [uc22s2112r34_deg5_W0M,
    CFSG.ClassicalGroups.UnitaryFlag.det_signedPerm (K := K),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)]
  simp [uc22s2112r34_deg5_sgn0, Fin.prod_univ_five]

private theorem uc22s2112r34_deg5_det_W1M {K : Type} [Field K] :
    (uc22s2112r34_deg5_W1M (K := K)).det = 1 := by
  rw [uc22s2112r34_deg5_W1M,
    CFSG.ClassicalGroups.UnitaryFlag.det_signedPerm (K := K),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 5) ≠ 3)]
  simp [uc22s2112r34_deg5_sgn1, Fin.prod_univ_five]

private theorem uc22s2112r34_deg5_det_W2M {K : Type} [Field K] :
    (uc22s2112r34_deg5_W2M (K := K)).det = 1 := by
  rw [uc22s2112r34_deg5_W2M,
    CFSG.ClassicalGroups.UnitaryFlag.det_signedPerm (K := K),
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 5) ≠ 3)]
  simp [uc22s2112r34_deg5_sgn2, Fin.prod_univ_five]

private noncomputable def uc22s2112r34_deg5_W0 {K : Type} [Field K] :
    GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uc22s2112r34_deg5_W0M (K := K))
    (by rw [uc22s2112r34_deg5_det_W0M]; exact one_ne_zero)

private noncomputable def uc22s2112r34_deg5_W1 {K : Type} [Field K] :
    GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uc22s2112r34_deg5_W1M (K := K))
    (by rw [uc22s2112r34_deg5_det_W1M]; exact one_ne_zero)

private noncomputable def uc22s2112r34_deg5_W2 {K : Type} [Field K] :
    GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uc22s2112r34_deg5_W2M (K := K))
    (by rw [uc22s2112r34_deg5_det_W2M]; exact one_ne_zero)

private theorem uc22s2112r34_deg5_unitary_W0M {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    Matrix.transpose ((uc22s2112r34_deg5_W0M (K := K)).map (fun x => x ^ q)) *
      uc22s2112r34_deg5_W0M = 1 := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hmap : (uc22s2112r34_deg5_W0M (K := K)).map (fun x => x ^ q) =
      uc22s2112r34_deg5_W0M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uc22s2112r34_deg5_W0M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
        hq.neg_one_pow, zero_pow hq0, Equiv.swap_apply_def,
        uc22s2112r34_deg5_sgn0]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34_deg5_W0M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Equiv.swap_apply_def,
      uc22s2112r34_deg5_sgn0]

private theorem uc22s2112r34_deg5_unitary_W1M {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    Matrix.transpose ((uc22s2112r34_deg5_W1M (K := K)).map (fun x => x ^ q)) *
      uc22s2112r34_deg5_W1M = 1 := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hmap : (uc22s2112r34_deg5_W1M (K := K)).map (fun x => x ^ q) =
      uc22s2112r34_deg5_W1M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uc22s2112r34_deg5_W1M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
        hq.neg_one_pow, zero_pow hq0, Equiv.swap_apply_def,
        uc22s2112r34_deg5_sgn1]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34_deg5_W1M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Equiv.swap_apply_def,
      uc22s2112r34_deg5_sgn1]

private theorem uc22s2112r34_deg5_unitary_W2M {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    Matrix.transpose ((uc22s2112r34_deg5_W2M (K := K)).map (fun x => x ^ q)) *
      uc22s2112r34_deg5_W2M = 1 := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hmap : (uc22s2112r34_deg5_W2M (K := K)).map (fun x => x ^ q) =
      uc22s2112r34_deg5_W2M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uc22s2112r34_deg5_W2M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
        zero_pow hq0, Equiv.swap_apply_def,
        uc22s2112r34_deg5_sgn2]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34_deg5_W2M, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Equiv.swap_apply_def,
      uc22s2112r34_deg5_sgn2]

private theorem uc22s2112r34_deg5_W0_mem_statedSL {K : Type} [Field K] :
    uc22s2112r34_deg5_W0 ∈ StatedSL 5 K := by
  refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
  simpa [uc22s2112r34_deg5_W0] using uc22s2112r34_deg5_det_W0M

private theorem uc22s2112r34_deg5_W1_mem_statedSL {K : Type} [Field K] :
    uc22s2112r34_deg5_W1 ∈ StatedSL 5 K := by
  refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
  simpa [uc22s2112r34_deg5_W1] using uc22s2112r34_deg5_det_W1M

private theorem uc22s2112r34_deg5_W2_mem_statedSL {K : Type} [Field K] :
    uc22s2112r34_deg5_W2 ∈ StatedSL 5 K := by
  refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
  simpa [uc22s2112r34_deg5_W2] using uc22s2112r34_deg5_det_W2M

private theorem uc22s2112r34_deg5_W0_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    uc22s2112r34_deg5_W0 ∈ StatedSU 5 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · simpa [uc22s2112r34_deg5_W0] using uc22s2112r34_deg5_det_W0M
  · simpa [uc22s2112r34_deg5_W0] using uc22s2112r34_deg5_unitary_W0M hq

private theorem uc22s2112r34_deg5_W1_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    uc22s2112r34_deg5_W1 ∈ StatedSU 5 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · simpa [uc22s2112r34_deg5_W1] using uc22s2112r34_deg5_det_W1M
  · simpa [uc22s2112r34_deg5_W1] using uc22s2112r34_deg5_unitary_W1M hq

private theorem uc22s2112r34_deg5_W2_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : Odd q) :
    uc22s2112r34_deg5_W2 ∈ StatedSU 5 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · simpa [uc22s2112r34_deg5_W2] using uc22s2112r34_deg5_det_W2M
  · simpa [uc22s2112r34_deg5_W2] using uc22s2112r34_deg5_unitary_W2M hq

private theorem uc22s2112r34_deg5_scalar_mem_statedScalars {K : Type} [Field K] (u : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 5) u ∈ StatedScalars (Fin 5) K :=
  ⟨u, rfl⟩

private theorem uc22s2112r34_deg5_E0_mem_statedSL {K : Type} [Field K] {u : Kˣ}
    (_hu5 : u ^ 5 = 1) : uc22s2112r34_deg5_E0 u ∈ StatedSL 5 K := by
  rw [uc22s2112r34_deg5_E0]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
  rw [Fin.prod_univ_five]
  simp

private theorem uc22s2112r34_deg5_E1_mem_statedSL {K : Type} [Field K] {u : Kˣ}
    (_hu5 : u ^ 5 = 1) : uc22s2112r34_deg5_E1 u ∈ StatedSL 5 K := by
  rw [uc22s2112r34_deg5_E1]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
  rw [Fin.prod_univ_five]
  simp

private theorem uc22s2112r34_deg5_E2_mem_statedSL {K : Type} [Field K] {u : Kˣ}
    (_hu5 : u ^ 5 = 1) : uc22s2112r34_deg5_E2 u ∈ StatedSL 5 K := by
  rw [uc22s2112r34_deg5_E2]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
  rw [Fin.prod_univ_five]
  have hu : u * u * (u⁻¹ ^ 2) = 1 := by
    rw [← pow_two, inv_pow, mul_inv_cancel]
  simpa [hu]

private theorem uc22s2112r34_deg5_E0_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    {u : Kˣ} (huq1 : u ^ (q + 1) = 1) : uc22s2112r34_deg5_E0 u ∈ StatedSU 5 q K := by
  rw [uc22s2112r34_deg5_E0]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq
  · rw [Fin.prod_univ_five]; simp
  · funext i
    fin_cases i <;> simp [Pi.pow_apply, huq1, inv_pow]

private theorem uc22s2112r34_deg5_E1_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    {u : Kˣ} (huq1 : u ^ (q + 1) = 1) : uc22s2112r34_deg5_E1 u ∈ StatedSU 5 q K := by
  rw [uc22s2112r34_deg5_E1]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq
  · rw [Fin.prod_univ_five]; simp
  · funext i
    fin_cases i <;> simp [Pi.pow_apply, huq1, inv_pow]

private theorem uc22s2112r34_deg5_E2_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    {u : Kˣ} (huq1 : u ^ (q + 1) = 1) : uc22s2112r34_deg5_E2 u ∈ StatedSU 5 q K := by
  rw [uc22s2112r34_deg5_E2]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq
  · rw [Fin.prod_univ_five]
    have hu : u * u * (u⁻¹ ^ 2) = 1 := by
      rw [← pow_two, inv_pow, mul_inv_cancel]
    simpa [hu]
  · have hupow : (u ^ 2) ^ (q + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, huq1, one_pow]
    funext i
    fin_cases i <;> simp [Pi.pow_apply, huq1, hupow, inv_pow]

private theorem uc22s2112r34_deg5_conj_signedPerm_torusDiag {K : Type} [Field K]
    (π : Equiv.Perm (Fin 5)) (ε : Fin 5 → K)
    (W : GL (Fin 5) K) (hW : (W : Matrix (Fin 5) (Fin 5) K) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm π ε)
    (d : Fin 5 → Kˣ) :
    W * CFSG.SectionRank.ClassicalEven.torusDiag d * W⁻¹ =
      CFSG.SectionRank.ClassicalEven.torusDiag (fun i => d (π.symm i)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul]
  have hW' : ((W : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm π ε := hW
  have hd1 : ((CFSG.SectionRank.ClassicalEven.torusDiag d : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal (fun i => (d i : K)) :=
    CFSG.SectionRank.ClassicalEven.coe_torusDiag _
  have hd2 : ((CFSG.SectionRank.ClassicalEven.torusDiag (fun i => d (π.symm i)) :
      GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal (fun i => (d (π.symm i) : K)) :=
    CFSG.SectionRank.ClassicalEven.coe_torusDiag _
  rw [hW', hd1, hd2]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = π j
  · simp only [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, if_pos h]
    have hsym : π.symm i = j := by rw [h, Equiv.symm_apply_apply]
    rw [hsym]
    ring
  · simp [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, h]

private theorem uc22s2112r34_deg5_W0_conj_E0 {K : Type} [Field K] (u : Kˣ) :
    uc22s2112r34_deg5_W0 * uc22s2112r34_deg5_E0 u * uc22s2112r34_deg5_W0⁻¹ =
      (uc22s2112r34_deg5_E0 u)⁻¹ := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag (π := Equiv.swap 0 1)
    (ε := uc22s2112r34_deg5_sgn0 (K := K))
    (W := uc22s2112r34_deg5_W0) (by rfl) (d := ![u, u⁻¹, (1 : Kˣ), 1, 1])
  rw [uc22s2112r34_deg5_E0, h, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.symm_swap, Equiv.swap_apply_def]

private theorem uc22s2112r34_deg5_W0_conj_E1 {K : Type} [Field K] (u : Kˣ) :
    uc22s2112r34_deg5_W0 * uc22s2112r34_deg5_E1 u * uc22s2112r34_deg5_W0⁻¹ =
      uc22s2112r34_deg5_E1 u := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag (π := Equiv.swap 0 1)
    (ε := uc22s2112r34_deg5_sgn0 (K := K))
    (W := uc22s2112r34_deg5_W0) (by rfl) (d := ![(1 : Kˣ), 1, u, u⁻¹, 1])
  rw [uc22s2112r34_deg5_E1, h]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.symm_swap, Equiv.swap_apply_def]

private theorem uc22s2112r34_deg5_W0_conj_E2 {K : Type} [Field K] (u : Kˣ) :
    uc22s2112r34_deg5_W0 * uc22s2112r34_deg5_E2 u * uc22s2112r34_deg5_W0⁻¹ =
      uc22s2112r34_deg5_E2 u := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag (π := Equiv.swap 0 1)
    (ε := uc22s2112r34_deg5_sgn0 (K := K))
    (W := uc22s2112r34_deg5_W0) (by rfl) (d := ![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2])
  rw [uc22s2112r34_deg5_E2, h]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.symm_swap, Equiv.swap_apply_def]

private theorem uc22s2112r34_deg5_W1_conj_E1 {K : Type} [Field K] (u : Kˣ) :
    uc22s2112r34_deg5_W1 * uc22s2112r34_deg5_E1 u * uc22s2112r34_deg5_W1⁻¹ =
      (uc22s2112r34_deg5_E1 u)⁻¹ := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag (π := Equiv.swap 2 3)
    (ε := uc22s2112r34_deg5_sgn1 (K := K))
    (W := uc22s2112r34_deg5_W1) (by rfl) (d := ![(1 : Kˣ), 1, u, u⁻¹, 1])
  rw [uc22s2112r34_deg5_E1, h, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.symm_swap, Equiv.swap_apply_def]

private theorem uc22s2112r34_deg5_W1_conj_E2 {K : Type} [Field K] (u : Kˣ) :
    uc22s2112r34_deg5_W1 * uc22s2112r34_deg5_E2 u * uc22s2112r34_deg5_W1⁻¹ =
      uc22s2112r34_deg5_E2 u := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag (π := Equiv.swap 2 3)
    (ε := uc22s2112r34_deg5_sgn1 (K := K))
    (W := uc22s2112r34_deg5_W1) (by rfl) (d := ![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2])
  rw [uc22s2112r34_deg5_E2, h]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.symm_swap, Equiv.swap_apply_def]

private theorem uc22s2112r34_deg5_W2_conj_E2 {K : Type} [Field K] {u : Kˣ} (hu5 : u ^ 5 = 1) :
    uc22s2112r34_deg5_W2 * uc22s2112r34_deg5_E2 u * uc22s2112r34_deg5_W2⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) u * (uc22s2112r34_deg5_E2 u)⁻¹ := by
  have h := uc22s2112r34_deg5_conj_signedPerm_torusDiag
    (π := Equiv.swap 0 2 * Equiv.swap 1 3)
    (ε := uc22s2112r34_deg5_sgn2 (K := K))
    (W := uc22s2112r34_deg5_W2) (by rfl) (d := ![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2])
  rw [uc22s2112r34_deg5_E2, h]
  rw [CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
  rw [← map_inv, ← map_mul]
  congr 1
  have hu3 : u ^ 3 = u⁻¹ ^ 2 := by
    rw [inv_pow, eq_inv_iff_mul_eq_one, ← pow_add, show 3 + 2 = 5 by norm_num, hu5]
  have hu4 : u * u ^ 2 = (u ^ 2)⁻¹ := by
    rw [mul_comm, ← pow_succ, show 2 + 1 = 3 by norm_num, hu3, inv_pow]
  funext i
  have hsymm : (Equiv.symm (Equiv.swap (0 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3)) i =
      (Equiv.swap (0 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3) i := by
    fin_cases i <;> decide
  rw [hsymm]
  fin_cases i <;> simp [Equiv.swap_apply_def, hu4]

private theorem uc22s2112r34_deg5_E0_pow {K : Type} [Field K] {u : Kˣ} (hu5 : u ^ 5 = 1) :
    (uc22s2112r34_deg5_E0 u) ^ 5 = 1 := by
  rw [uc22s2112r34_deg5_E0, ← map_pow]
  have hd : (![u, u⁻¹, (1 : Kˣ), 1, 1] : Fin 5 → Kˣ) ^ 5 = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply, inv_pow, hu5]
  rw [hd, map_one]

private theorem uc22s2112r34_deg5_E1_pow {K : Type} [Field K] {u : Kˣ} (hu5 : u ^ 5 = 1) :
    (uc22s2112r34_deg5_E1 u) ^ 5 = 1 := by
  rw [uc22s2112r34_deg5_E1, ← map_pow]
  have hd : (![(1 : Kˣ), 1, u, u⁻¹, 1] : Fin 5 → Kˣ) ^ 5 = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply, inv_pow, hu5]
  rw [hd, map_one]

private theorem uc22s2112r34_deg5_E2_pow {K : Type} [Field K] {u : Kˣ} (hu5 : u ^ 5 = 1) :
    (uc22s2112r34_deg5_E2 u) ^ 5 = 1 := by
  rw [uc22s2112r34_deg5_E2, ← map_pow]
  have hd : (![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2] : Fin 5 → Kˣ) ^ 5 = 1 := by
    funext i
    fin_cases i
    · simpa [Pi.pow_apply] using hu5
    · simpa [Pi.pow_apply] using hu5
    · simp [Pi.pow_apply]
    · simp [Pi.pow_apply]
    · change (u⁻¹ ^ 2) ^ 5 = 1
      rw [← pow_mul, show 2 * 5 = 10 by norm_num, inv_pow]
      have h10 : u ^ 10 = 1 := by
        rw [show 10 = 5 * 2 by norm_num, pow_mul, hu5, one_pow]
      rw [h10, inv_one]
  rw [hd, map_one]

theorem deg5Frame_statedSL {K : Type} [Field K] {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) :
    Deg5Frame (StatedProj (StatedSL 5 K)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ5
  let u : Kˣ := Units.mk0 ζ hζ0
  have hu5 : u ^ 5 = 1 := by
    apply Units.ext
    simpa [u] using hζ5
  have hu1 : u ≠ 1 := by
    intro h
    apply hζ1
    have := congrArg (fun x : Kˣ => (x : K)) h
    simpa [u] using this
  let H := StatedSL 5 K
  have hE0 : uc22s2112r34_deg5_E0 u ∈ H := uc22s2112r34_deg5_E0_mem_statedSL hu5
  have hE1 : uc22s2112r34_deg5_E1 u ∈ H := uc22s2112r34_deg5_E1_mem_statedSL hu5
  have hE2 : uc22s2112r34_deg5_E2 u ∈ H := uc22s2112r34_deg5_E2_mem_statedSL hu5
  have hW0 : uc22s2112r34_deg5_W0 ∈ H := uc22s2112r34_deg5_W0_mem_statedSL
  have hW1 : uc22s2112r34_deg5_W1 ∈ H := uc22s2112r34_deg5_W1_mem_statedSL
  have hW2 : uc22s2112r34_deg5_W2 ∈ H := uc22s2112r34_deg5_W2_mem_statedSL
  let e0 : H := ⟨uc22s2112r34_deg5_E0 u, hE0⟩
  let e1 : H := ⟨uc22s2112r34_deg5_E1 u, hE1⟩
  let e2 : H := ⟨uc22s2112r34_deg5_E2 u, hE2⟩
  let w0 : H := ⟨uc22s2112r34_deg5_W0, hW0⟩
  let w1 : H := ⟨uc22s2112r34_deg5_W1, hW1⟩
  let w2 : H := ⟨uc22s2112r34_deg5_W2, hW2⟩
  let π : H →* StatedProj H := QuotientGroup.mk' _
  have he0pow : e0 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E0_pow hu5
  have he1pow : e1 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E1_pow hu5
  have he2pow : e2 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E2_pow hu5
  have hc01 : Commute e0 e1 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hc02 : Commute e0 e2 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hc12 : Commute e1 e2 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hind : ∀ a b c : ℕ,
      e0 ^ a * e1 ^ b * e2 ^ c ∈ (StatedScalars (Fin 5) K).subgroupOf H →
      5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c := by
    intro a b c hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp hmem
    have hvec : (![u, u⁻¹, (1 : Kˣ), 1, 1] : Fin 5 → Kˣ) ^ a *
        (![(1 : Kˣ), 1, u, u⁻¹, 1] : Fin 5 → Kˣ) ^ b *
        (![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2] : Fin 5 → Kˣ) ^ c = fun _ => lam := by
      apply CFSG.SectionRank.ClassicalEven.torusDiag_injective
      rw [← CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
      rw [hlam]
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      simp [e0, e1, e2,
        uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E2, inv_pow]
    have h0 : u ^ a * u ^ c = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 0
    have h1 : (u⁻¹) ^ a * u ^ c = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 1
    have h2 : u ^ b = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 2
    have h3 : (u⁻¹) ^ b = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 3
    have huord : orderOf u = 5 := orderOf_eq_prime hu5 hu1
    have ha : 5 ∣ a := by
      have h : u ^ a = (u⁻¹) ^ a := by
        have h' := h0.trans h1.symm
        exact mul_right_cancel h'
      have h2a : u ^ (2 * a) = 1 := by
        have h' := congrArg (fun x => x * u ^ a) h
        rw [inv_pow, inv_mul_cancel] at h'
        rw [← pow_add] at h'
        simpa [two_mul] using h'
      have hdvd : 5 ∣ 2 * a := by
        have := orderOf_dvd_of_pow_eq_one h2a
        rwa [huord] at this
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
      · omega
      · exact h'
    have hb : 5 ∣ b := by
      have h : u ^ b = (u⁻¹) ^ b := h2.trans h3.symm
      have h2b : u ^ (2 * b) = 1 := by
        have h' := congrArg (fun x => x * u ^ b) h
        rw [inv_pow, inv_mul_cancel] at h'
        rw [← pow_add] at h'
        simpa [two_mul] using h'
      have hdvd : 5 ∣ 2 * b := by
        have := orderOf_dvd_of_pow_eq_one h2b
        rwa [huord] at this
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
      · omega
      · exact h'
    have hua : u ^ a = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
    have hub : u ^ b = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
    have hlam1 : lam = 1 := by rw [← h2, hub]
    have hc : 5 ∣ c := by
      have h : u ^ c = 1 := by
        have h' := h0
        rw [hlam1] at h'
        rwa [hua, one_mul] at h'
      have := orderOf_dvd_of_pow_eq_one h
      rwa [huord] at this
    exact ⟨ha, hb, hc⟩
  have hscalar : Matrix.GeneralLinearGroup.scalar (Fin 5) u ∈ H := by
    rw [CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
    apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
    simp [Finset.prod_const, hu5]
  have hw0e0 : w0 * e0 * w0⁻¹ = e0⁻¹ := by
    apply Subtype.ext
    simpa [e0, w0] using uc22s2112r34_deg5_W0_conj_E0 u
  have hw0e1 : w0 * e1 * w0⁻¹ = e1 := by
    apply Subtype.ext
    simpa [e1, w0] using uc22s2112r34_deg5_W0_conj_E1 u
  have hw0e2 : w0 * e2 * w0⁻¹ = e2 := by
    apply Subtype.ext
    simpa [e2, w0] using uc22s2112r34_deg5_W0_conj_E2 u
  have hw1e1 : w1 * e1 * w1⁻¹ = e1⁻¹ := by
    apply Subtype.ext
    simpa [e1, w1] using uc22s2112r34_deg5_W1_conj_E1 u
  have hw1e2 : w1 * e2 * w1⁻¹ = e2 := by
    apply Subtype.ext
    simpa [e2, w1] using uc22s2112r34_deg5_W1_conj_E2 u
  refine ⟨π e0, π e1, π e2, π w0, π w1, π w2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc01.map π
  · exact hc02.map π
  · exact hc12.map π
  · rw [← map_pow, he0pow, map_one]
  · rw [← map_pow, he1pow, map_one]
  · rw [← map_pow, he2pow, map_one]
  · intro a b c h
    apply hind a b c
    have h' : π (e0 ^ a * e1 ^ b * e2 ^ c) = 1 := by
      simpa [map_mul, map_pow] using h
    change QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf H) _ = 1 at h'
    rw [QuotientGroup.mk'_apply] at h'
    exact (QuotientGroup.eq_one_iff _).mp h'
  · simp only [← map_mul, ← map_inv]
    rw [hw0e0]
  · simp only [← map_mul, ← map_inv]
    rw [hw0e1]
  · simp only [← map_mul, ← map_inv]
    rw [hw0e2]
  · simp only [← map_mul, ← map_inv]
    rw [hw1e1]
  · simp only [← map_mul, ← map_inv]
    rw [hw1e2]
  · have hW2H : (⟨uc22s2112r34_deg5_W2, hW2⟩ : H) * e2 *
        (⟨uc22s2112r34_deg5_W2, hW2⟩ : H)⁻¹ =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin 5) u, hscalar⟩ : H) * e2⁻¹ := by
      apply Subtype.ext
      simpa [e2] using uc22s2112r34_deg5_W2_conj_E2 hu5
    have hker : π (⟨Matrix.GeneralLinearGroup.scalar (Fin 5) u, hscalar⟩ : H) = 1 := by
      change QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf H) _ = 1
      rw [QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf]
      exact uc22s2112r34_deg5_scalar_mem_statedScalars u
    simp only [← map_mul, ← map_inv]
    rw [hW2H, map_mul, hker, one_mul]

theorem deg5Frame_statedSU {K : Type} [Field K] {q : ℕ} (hq : Odd q) {ζ : K}
    (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hζq : ζ ^ q = ζ⁻¹) :
    Deg5Frame (StatedProj (StatedSU 5 q K)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ5
  let u : Kˣ := Units.mk0 ζ hζ0
  have hq0 : q ≠ 0 := hq.pos.ne'
  have huq : u ^ q = u⁻¹ := by
    apply Units.ext
    simpa [u] using hζq
  have huq1 : u ^ (q + 1) = 1 := by
    rw [pow_succ, huq, inv_mul_cancel]
  have hu5 : u ^ 5 = 1 := by
    apply Units.ext
    simpa [u] using hζ5
  have hu1 : u ≠ 1 := by
    intro h
    apply hζ1
    have := congrArg (fun x : Kˣ => (x : K)) h
    simpa [u] using this
  let H := StatedSU 5 q K
  have hE0 : uc22s2112r34_deg5_E0 u ∈ H := uc22s2112r34_deg5_E0_mem_statedSU hq0 huq1
  have hE1 : uc22s2112r34_deg5_E1 u ∈ H := uc22s2112r34_deg5_E1_mem_statedSU hq0 huq1
  have hE2 : uc22s2112r34_deg5_E2 u ∈ H := uc22s2112r34_deg5_E2_mem_statedSU hq0 huq1
  have hW0 : uc22s2112r34_deg5_W0 ∈ H := uc22s2112r34_deg5_W0_mem_statedSU hq
  have hW1 : uc22s2112r34_deg5_W1 ∈ H := uc22s2112r34_deg5_W1_mem_statedSU hq
  have hW2 : uc22s2112r34_deg5_W2 ∈ H := uc22s2112r34_deg5_W2_mem_statedSU hq
  let e0 : H := ⟨uc22s2112r34_deg5_E0 u, hE0⟩
  let e1 : H := ⟨uc22s2112r34_deg5_E1 u, hE1⟩
  let e2 : H := ⟨uc22s2112r34_deg5_E2 u, hE2⟩
  let w0 : H := ⟨uc22s2112r34_deg5_W0, hW0⟩
  let w1 : H := ⟨uc22s2112r34_deg5_W1, hW1⟩
  let w2 : H := ⟨uc22s2112r34_deg5_W2, hW2⟩
  let π : H →* StatedProj H := QuotientGroup.mk' _
  have he0pow : e0 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E0_pow hu5
  have he1pow : e1 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E1_pow hu5
  have he2pow : e2 ^ 5 = 1 := by
    apply Subtype.ext
    exact uc22s2112r34_deg5_E2_pow hu5
  have hc01 : Commute e0 e1 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hc02 : Commute e0 e2 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hc12 : Commute e1 e2 := by
    apply Subtype.ext
    exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
  have hind : ∀ a b c : ℕ,
      e0 ^ a * e1 ^ b * e2 ^ c ∈ (StatedScalars (Fin 5) K).subgroupOf H →
      5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c := by
    intro a b c hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp hmem
    have hvec : (![u, u⁻¹, (1 : Kˣ), 1, 1] : Fin 5 → Kˣ) ^ a *
        (![(1 : Kˣ), 1, u, u⁻¹, 1] : Fin 5 → Kˣ) ^ b *
        (![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2] : Fin 5 → Kˣ) ^ c = fun _ => lam := by
      apply CFSG.SectionRank.ClassicalEven.torusDiag_injective
      rw [← CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
      rw [hlam]
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      simp [e0, e1, e2,
        uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E2, inv_pow]
    have h0 : u ^ a * u ^ c = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 0
    have h1 : (u⁻¹) ^ a * u ^ c = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 1
    have h2 : u ^ b = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 2
    have h3 : (u⁻¹) ^ b = lam := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 3
    have huord : orderOf u = 5 := orderOf_eq_prime hu5 hu1
    have ha : 5 ∣ a := by
      have h : u ^ a = (u⁻¹) ^ a := by
        have h' := h0.trans h1.symm
        exact mul_right_cancel h'
      have h2a : u ^ (2 * a) = 1 := by
        have h' := congrArg (fun x => x * u ^ a) h
        rw [inv_pow, inv_mul_cancel] at h'
        rw [← pow_add] at h'
        simpa [two_mul] using h'
      have hdvd : 5 ∣ 2 * a := by
        have := orderOf_dvd_of_pow_eq_one h2a
        rwa [huord] at this
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
      · omega
      · exact h'
    have hb : 5 ∣ b := by
      have h : u ^ b = (u⁻¹) ^ b := h2.trans h3.symm
      have h2b : u ^ (2 * b) = 1 := by
        have h' := congrArg (fun x => x * u ^ b) h
        rw [inv_pow, inv_mul_cancel] at h'
        rw [← pow_add] at h'
        simpa [two_mul] using h'
      have hdvd : 5 ∣ 2 * b := by
        have := orderOf_dvd_of_pow_eq_one h2b
        rwa [huord] at this
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
      · omega
      · exact h'
    have hua : u ^ a = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
    have hub : u ^ b = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
    have hlam1 : lam = 1 := by rw [← h2, hub]
    have hc : 5 ∣ c := by
      have h : u ^ c = 1 := by
        have h' := h0
        rw [hlam1] at h'
        rwa [hua, one_mul] at h'
      have := orderOf_dvd_of_pow_eq_one h
      rwa [huord] at this
    exact ⟨ha, hb, hc⟩
  have hscalar : Matrix.GeneralLinearGroup.scalar (Fin 5) u ∈ H := by
    rw [CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
    apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq0
    · simp [Finset.prod_const, hu5]
    · funext i
      simp [Pi.pow_apply, huq1]
  have hw0e0 : w0 * e0 * w0⁻¹ = e0⁻¹ := by
    apply Subtype.ext
    simpa [e0, w0] using uc22s2112r34_deg5_W0_conj_E0 u
  have hw0e1 : w0 * e1 * w0⁻¹ = e1 := by
    apply Subtype.ext
    simpa [e1, w0] using uc22s2112r34_deg5_W0_conj_E1 u
  have hw0e2 : w0 * e2 * w0⁻¹ = e2 := by
    apply Subtype.ext
    simpa [e2, w0] using uc22s2112r34_deg5_W0_conj_E2 u
  have hw1e1 : w1 * e1 * w1⁻¹ = e1⁻¹ := by
    apply Subtype.ext
    simpa [e1, w1] using uc22s2112r34_deg5_W1_conj_E1 u
  have hw1e2 : w1 * e2 * w1⁻¹ = e2 := by
    apply Subtype.ext
    simpa [e2, w1] using uc22s2112r34_deg5_W1_conj_E2 u
  refine ⟨π e0, π e1, π e2, π w0, π w1, π w2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc01.map π
  · exact hc02.map π
  · exact hc12.map π
  · rw [← map_pow, he0pow, map_one]
  · rw [← map_pow, he1pow, map_one]
  · rw [← map_pow, he2pow, map_one]
  · intro a b c h
    apply hind a b c
    have h' : π (e0 ^ a * e1 ^ b * e2 ^ c) = 1 := by
      simpa [map_mul, map_pow] using h
    change QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf H) _ = 1 at h'
    rw [QuotientGroup.mk'_apply] at h'
    exact (QuotientGroup.eq_one_iff _).mp h'
  · simp only [← map_mul, ← map_inv]
    rw [hw0e0]
  · simp only [← map_mul, ← map_inv]
    rw [hw0e1]
  · simp only [← map_mul, ← map_inv]
    rw [hw0e2]
  · simp only [← map_mul, ← map_inv]
    rw [hw1e1]
  · simp only [← map_mul, ← map_inv]
    rw [hw1e2]
  · have hW2H : (⟨uc22s2112r34_deg5_W2, hW2⟩ : H) * e2 *
        (⟨uc22s2112r34_deg5_W2, hW2⟩ : H)⁻¹ =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin 5) u, hscalar⟩ : H) * e2⁻¹ := by
      apply Subtype.ext
      simpa [e2] using uc22s2112r34_deg5_W2_conj_E2 hu5
    have hker : π (⟨Matrix.GeneralLinearGroup.scalar (Fin 5) u, hscalar⟩ : H) = 1 := by
      change QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf H) _ = 1
      rw [QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf]
      exact uc22s2112r34_deg5_scalar_mem_statedScalars u
    simp only [← map_mul, ← map_inv]
    rw [hW2H, map_mul, hker, one_mul]

theorem deg5Frame_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel X t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) : Deg5Frame X := by
  rcases ht with h | h
  · rw [h] at hX h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hX' := hX.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hX'
    let _ := hKfield
    let _ := hKfinite
    have h5' : 5 ∣ p ^ f - 1 := by
      simpa [genericOrders] using (Nat.dvd_gcd_iff.mp h5).2
    have hcard_units : Nat.card Kˣ = p ^ f - 1 := by
      rw [Nat.card_units, hKcard]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5
      (by rw [hcard_units]; exact h5')
    have hζ5' : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hζ5 : (ζ : K) ^ 5 = 1 := congrArg (fun x : Kˣ => (x : K)) hζ5'
    have hζ1 : (ζ : K) ≠ 1 := by
      intro h
      have h' : ζ = 1 := Units.ext h
      have : orderOf ζ = 1 := by rw [h']; exact orderOf_one
      omega
    exact Deg5Frame.of_mulEquiv e (deg5Frame_statedSL hζ5 hζ1)
  · rw [h] at hX h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hX' := hX.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hX'
    let _ := hKfield
    let _ := hKfinite
    have h5' : 5 ∣ p ^ f + 1 := by
      simpa [genericOrders] using (Nat.dvd_gcd_iff.mp h5).2
    have hcard_units : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
      rw [Nat.card_units, hKcard]
    have h5dvd : 5 ∣ Nat.card Kˣ := by
      rw [hcard_units]
      have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
        have h1 : (p ^ f) ^ 2 - 1 = (p ^ f) ^ 2 - 1 ^ 2 := by norm_num
        rw [h1, Nat.sq_sub_sq]
        ring
      rw [hsq]
      exact dvd_mul_of_dvd_right h5' _
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5 h5dvd
    have hζ5' : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hζ5 : (ζ : K) ^ 5 = 1 := congrArg (fun x : Kˣ => (x : K)) hζ5'
    have hζ1 : (ζ : K) ≠ 1 := by
      intro h
      have h' : ζ = 1 := Units.ext h
      have : orderOf ζ = 1 := by rw [h']; exact orderOf_one
      omega
    have hmod : p ^ f % 5 = 4 := by
      have hpos : 0 < p ^ f := pow_pos hp.pos f
      omega
    have hζq : (ζ : K) ^ (p ^ f) = (ζ : K)⁻¹ := by
      rw [pow_eq_pow_mod (p ^ f) hζ5, hmod]
      have h4 : (ζ : K) ^ 4 * (ζ : K) = 1 := by
        rw [← pow_succ, show 4 + 1 = 5 by norm_num]
        exact hζ5
      exact eq_inv_of_mul_eq_one_left h4
    have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    exact Deg5Frame.of_mulEquiv e (deg5Frame_statedSU hq hζ5 hζ1 hζq)

private theorem uc22s2112r34_deg5_exists_order_25 {α : Type} [Group α] [Finite α] [IsCyclic α]
    (h : 25 ∣ Nat.card α) : ∃ η : α, orderOf η = 25 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  let N := Nat.card α
  obtain ⟨k, hk⟩ := h
  have hN : N ≠ 0 := by
    have : 0 < N := Nat.card_pos
    omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [mul_zero] at hk
      exact absurd hk hN
    · exact hkpos
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow, hg]
  have hgdvd : k ∣ N := by rw [show N = 25 * k from hk]; exact Nat.dvd_mul_left k 25
  rw [Nat.gcd_eq_right hgdvd]
  rw [hk, Nat.mul_div_left 25 hkpos]

private theorem uc22s2112r34_deg5_E3_mem_statedSL {K : Type} [Field K] {η : Kˣ} :
    uc22s2112r34_deg5_E3 η ∈ StatedSL 5 K := by
  rw [uc22s2112r34_deg5_E3]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
  rw [Fin.prod_univ_five]
  simp [inv_pow]
  group

private theorem uc22s2112r34_deg5_E3_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    {η : Kˣ} (hηq1 : η ^ (q + 1) = 1) : uc22s2112r34_deg5_E3 η ∈ StatedSU 5 q K := by
  rw [uc22s2112r34_deg5_E3]
  apply CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq
  · rw [Fin.prod_univ_five]
    simp [inv_pow]
    group
  · have hη4 : (η ^ 4) ^ (q + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hηq1, one_pow]
    funext i
    fin_cases i <;> simp [Pi.pow_apply, hηq1, hη4, inv_pow]

private theorem uc22s2112r34_deg5_E3_pow {K : Type} [Field K] {η : Kˣ} (hη25 : orderOf η = 25) :
    (uc22s2112r34_deg5_E3 η) ^ 5 ∈ StatedScalars (Fin 5) K := by
  rw [uc22s2112r34_deg5_E3, ← map_pow]
  have h25 : η ^ 25 = 1 := by rw [← hη25]; exact pow_orderOf_eq_one η
  have h20 : η ^ 20 = (η ^ 5)⁻¹ := by
    have h : η ^ 20 * η ^ 5 = 1 := by
      rw [← pow_add, show 20 + 5 = 25 by norm_num, h25]
    exact eq_inv_of_mul_eq_one_left h
  have hvec : (![η, η, η, η, η⁻¹ ^ 4] : Fin 5 → Kˣ) ^ 5 = fun _ => η ^ 5 := by
    funext i
    fin_cases i
    · simp [Pi.pow_apply]
    · simp [Pi.pow_apply]
    · simp [Pi.pow_apply]
    · simp [Pi.pow_apply]
    · change ((η⁻¹) ^ 4) ^ 5 = η ^ 5
      rw [← pow_mul, show 4 * 5 = 20 by norm_num, inv_pow, h20, inv_inv]
  rw [hvec, ← CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
  exact MonoidHom.mem_range.mpr ⟨η ^ 5, rfl⟩

private theorem uc22s2112r34_deg5_four_diag_independent {K : Type} [Field K] (u η : Kˣ)
    (huord : orderOf u = 5) (hη25 : orderOf η = 25) (_huη : u = η ^ 5) {a b c d : ℕ}
    (h : uc22s2112r34_deg5_E0 u ^ a * uc22s2112r34_deg5_E1 u ^ b *
      uc22s2112r34_deg5_E2 u ^ c * uc22s2112r34_deg5_E3 η ^ d ∈ StatedScalars (Fin 5) K) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
  obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp h
  have hvec : (![u, u⁻¹, (1 : Kˣ), 1, 1] : Fin 5 → Kˣ) ^ a *
      (![(1 : Kˣ), 1, u, u⁻¹, 1] : Fin 5 → Kˣ) ^ b *
      (![u, u, (1 : Kˣ), 1, u⁻¹ ^ 2] : Fin 5 → Kˣ) ^ c *
      (![η, η, η, η, η⁻¹ ^ 4] : Fin 5 → Kˣ) ^ d = fun _ => lam := by
    apply CFSG.SectionRank.ClassicalEven.torusDiag_injective
    rw [← CFSG.SectionRank.ClassicalEven.scalar_eq_torusDiag]
    rw [hlam]
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    simp [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E2,
      uc22s2112r34_deg5_E3, inv_pow]
  have h0 : u ^ a * u ^ c * η ^ d = lam := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 0
  have h1 : (u⁻¹) ^ a * u ^ c * η ^ d = lam := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 1
  have h2 : u ^ b * η ^ d = lam := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 2
  have h3 : (u⁻¹) ^ b * η ^ d = lam := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 3
  have h4 : (u⁻¹ ^ 2) ^ c * (η⁻¹ ^ 4) ^ d = lam := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun hvec 4
  have ha : 5 ∣ a := by
    have h : u ^ a = (u⁻¹) ^ a := by
      have h' := h0.trans h1.symm
      exact mul_right_cancel (mul_right_cancel h')
    have h2a : u ^ (2 * a) = 1 := by
      have h' := congrArg (fun x => x * u ^ a) h
      rw [inv_pow, inv_mul_cancel] at h'
      rw [← pow_add] at h'
      simpa [two_mul] using h'
    have hdvd : 5 ∣ 2 * a := by
      have := orderOf_dvd_of_pow_eq_one h2a
      rwa [huord] at this
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
    · omega
    · exact h'
  have hb : 5 ∣ b := by
    have h : u ^ b = (u⁻¹) ^ b := by
      have h' := h2.trans h3.symm
      exact mul_right_cancel h'
    have h2b : u ^ (2 * b) = 1 := by
      have h' := congrArg (fun x => x * u ^ b) h
      rw [inv_pow, inv_mul_cancel] at h'
      rw [← pow_add] at h'
      simpa [two_mul] using h'
    have hdvd : 5 ∣ 2 * b := by
      have := orderOf_dvd_of_pow_eq_one h2b
      rwa [huord] at this
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h' | h'
    · omega
    · exact h'
  have hua : u ^ a = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
  have hub : u ^ b = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
  have hc : 5 ∣ c := by
    have h : u ^ c = 1 := by
      have h' := h0.trans h2.symm
      have h'' := mul_right_cancel h'
      rw [hua, one_mul, hub] at h''
      exact h''
    have := orderOf_dvd_of_pow_eq_one h
    rwa [huord] at this
  have huc : u ^ c = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rwa [huord])
  have hc'' : (u⁻¹ ^ 2) ^ c = 1 := by
    rw [← pow_mul, inv_pow, show 2 * c = c * 2 by ring, pow_mul, huc, one_pow, inv_one]
  have hd : 5 ∣ d := by
    have h : η ^ d = (η⁻¹ ^ 4) ^ d := by
      have h' := h0.trans h4.symm
      rw [hua, huc, one_mul, one_mul, hc''] at h'
      simpa using h'
    have h5d : η ^ (5 * d) = 1 := by
      have h' : η ^ d = ((η ^ 4) ^ d)⁻¹ := by
        simpa [inv_pow, pow_mul] using h
      have h'' := congrArg (fun x => x * (η ^ 4) ^ d) h'
      rw [← pow_mul] at h''
      simp [inv_mul_cancel] at h''
      rw [← pow_add] at h''
      have hsum : d + 4 * d = 5 * d := by ring
      rw [hsum] at h''
      exact h''
    have hdvd : orderOf η ∣ 5 * d := orderOf_dvd_of_pow_eq_one h5d
    rw [hη25] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) hdvd
  exact ⟨ha, hb, hc, hd⟩

private theorem uc22s2112r34_deg5_four_le_pRank_of_commuting_order_five
    {G : Type} [Group G] [Finite G] {x0 x1 x2 x3 : G}
    (hx0 : x0 ^ 5 = 1) (hx1 : x1 ^ 5 = 1) (hx2 : x2 ^ 5 = 1) (hx3 : x3 ^ 5 = 1)
    (hc01 : Commute x0 x1) (hc02 : Commute x0 x2) (hc03 : Commute x0 x3)
    (hc12 : Commute x1 x2) (hc13 : Commute x1 x3) (hc23 : Commute x2 x3)
    (hind : ∀ a b c d : ℕ, x0 ^ a * x1 ^ b * x2 ^ c * x3 ^ d = 1 →
      5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let x : Fin 4 → G := ![x0, x1, x2, x3]
  have hxpow : ∀ i, x i ^ 5 = 1 := by
    intro i
    fin_cases i
    · simpa [x] using hx0
    · simpa [x] using hx1
    · simpa [x] using hx2
    · simpa [x] using hx3
  have hxcomm : ∀ i j, i ≠ j → Commute (x i) (x j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [x] using hc01
    · simpa [x] using hc02
    · simpa [x] using hc03
    · simpa [x] using hc01.symm
    · exact absurd rfl hij
    · simpa [x] using hc12
    · simpa [x] using hc13
    · simpa [x] using hc02.symm
    · simpa [x] using hc12.symm
    · exact absurd rfl hij
    · simpa [x] using hc23
    · simpa [x] using hc03.symm
    · simpa [x] using hc13.symm
    · simpa [x] using hc23.symm
    · exact absurd rfl hij
  let ϕ : ∀ i : Fin 4, Multiplicative (ZMod 5) →* G := fun i => {
    toFun := fun k => x i ^ (Multiplicative.toAdd k).val
    map_one' := by simp
    map_mul' := by
      intro a b
      rw [toAdd_mul, ZMod.val_add,
        ← pow_eq_pow_mod (a := x i) (m := (Multiplicative.toAdd a).val +
          (Multiplicative.toAdd b).val) (hxpow i), pow_add] }
  have hϕcomm : Pairwise fun i j : Fin 4 => ∀ a b : Multiplicative (ZMod 5),
      Commute (ϕ i a) (ϕ j b) := by
    intro i j hij a b
    exact (hxcomm i j hij).pow_pow _ _
  let F : (Fin 4 → Multiplicative (ZMod 5)) →* G := MonoidHom.noncommPiCoprod ϕ hϕcomm
  have hFapply : ∀ v : Fin 4 → Multiplicative (ZMod 5),
      F v = x 0 ^ (v 0).toAdd.val * x 1 ^ (v 1).toAdd.val *
        x 2 ^ (v 2).toAdd.val * x 3 ^ (v 3).toAdd.val := by
    intro v
    change (MonoidHom.noncommPiCoprod ϕ hϕcomm) v = _
    rw [MonoidHom.noncommPiCoprod_apply]
    exact uc22s2112r34_deg5_noncommProd_univ_four _ _
  have hF : Function.Injective F := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hv1 : F v = 1 := MonoidHom.mem_ker.mp hv
    rw [hFapply v] at hv1
    obtain ⟨ha, hb, hc, hd⟩ := hind _ _ _ _ hv1
    have h0 : (v 0).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt ha (ZMod.val_lt _)
    have h1 : (v 1).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt _)
    have h2 : (v 2).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hc (ZMod.val_lt _)
    have h3 : (v 3).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
    funext i
    fin_cases i
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h0)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h1)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h2)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).mp h3)
  have hcard : Nat.card (Fin 4 → Multiplicative (ZMod 5)) = 5 ^ 4 := by
    rw [Nat.card_pi]
    simp [Finset.prod_const]
  have hpowA : ∀ a : Fin 4 → Multiplicative (ZMod 5), a ^ 5 = 1 := by
    intro a
    funext i
    rw [Pi.pow_apply, ← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]
    rfl
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 5)
    (fun a b => mul_comm' a b) hpowA hcard F hF le_top

theorem four_le_pRank_of_lieModel_deg5 {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {p f : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) (hX : LieModel X t 5 p f)
    (h25 : (t = .PSL ∧ 25 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 25 ∣ p ^ f + 1)) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  rcases h25 with ⟨h, h25⟩ | ⟨h, h25⟩
  · rw [h] at hX
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hX' := hX.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hX'
    let _ := hKfield
    let _ := hKfinite
    have h25dvd : 25 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hKcard]
      exact h25
    obtain ⟨η, hη25⟩ := uc22s2112r34_deg5_exists_order_25 h25dvd
    let u : Kˣ := η ^ 5
    have huord : orderOf u = 5 := by
      dsimp [u]
      rw [orderOf_pow, hη25]
      norm_num
    have hu5 : u ^ 5 = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h'
      have : orderOf u = 1 := by rw [h']; exact orderOf_one
      omega
    have hE0 : uc22s2112r34_deg5_E0 u ∈ StatedSL 5 K := uc22s2112r34_deg5_E0_mem_statedSL hu5
    have hE1 : uc22s2112r34_deg5_E1 u ∈ StatedSL 5 K := uc22s2112r34_deg5_E1_mem_statedSL hu5
    have hE2 : uc22s2112r34_deg5_E2 u ∈ StatedSL 5 K := uc22s2112r34_deg5_E2_mem_statedSL hu5
    have hE3 : uc22s2112r34_deg5_E3 η ∈ StatedSL 5 K := uc22s2112r34_deg5_E3_mem_statedSL
    have hE0pow : (uc22s2112r34_deg5_E0 u) ^ 5 = 1 := uc22s2112r34_deg5_E0_pow hu5
    have hE1pow : (uc22s2112r34_deg5_E1 u) ^ 5 = 1 := uc22s2112r34_deg5_E1_pow hu5
    have hE2pow : (uc22s2112r34_deg5_E2 u) ^ 5 = 1 := uc22s2112r34_deg5_E2_pow hu5
    have hE3pow : (uc22s2112r34_deg5_E3 η) ^ 5 ∈ StatedScalars (Fin 5) K :=
      uc22s2112r34_deg5_E3_pow hη25
    let H := StatedSL 5 K
    let π : H →* StatedProj H := QuotientGroup.mk' _
    let x0 : StatedProj H := π ⟨uc22s2112r34_deg5_E0 u, hE0⟩
    let x1 : StatedProj H := π ⟨uc22s2112r34_deg5_E1 u, hE1⟩
    let x2 : StatedProj H := π ⟨uc22s2112r34_deg5_E2 u, hE2⟩
    let x3 : StatedProj H := π ⟨uc22s2112r34_deg5_E3 η, hE3⟩
    have hx0pow : x0 ^ 5 = 1 := by
      dsimp [x0]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE0pow
      rw [hsub, map_one]
    have hx1pow : x1 ^ 5 = 1 := by
      dsimp [x1]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE1pow
      rw [hsub, map_one]
    have hx2pow : x2 ^ 5 = 1 := by
      dsimp [x2]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE2pow
      rw [hsub, map_one]
    have hx3pow : x3 ^ 5 = 1 := by
      dsimp [x3]
      rw [← map_pow]
      have hmem : (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ 5 ∈
          (StatedScalars (Fin 5) K).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hE3pow
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hc01 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E1 u) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E1]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc02 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E2 u) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E2]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc03 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc12 : Commute (uc22s2112r34_deg5_E1 u) (uc22s2112r34_deg5_E2 u) := by
      rw [uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E2]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc13 : Commute (uc22s2112r34_deg5_E1 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc23 : Commute (uc22s2112r34_deg5_E2 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E2, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc01' : Commute x0 x1 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E1 u, hE1⟩ from Subtype.ext hc01.eq) π
    have hc02' : Commute x0 x2 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E2 u, hE2⟩ from Subtype.ext hc02.eq) π
    have hc03' : Commute x0 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc03.eq) π
    have hc12' : Commute x1 x2 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H)
        ⟨uc22s2112r34_deg5_E2 u, hE2⟩ from Subtype.ext hc12.eq) π
    have hc13' : Commute x1 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc13.eq) π
    have hc23' : Commute x2 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc23.eq) π
    have hind : ∀ a b c d : ℕ, x0 ^ a * x1 ^ b * x2 ^ c * x3 ^ d = 1 →
        5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
      intro a b c d hprod
      let g : H := (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ a *
        (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ b *
        (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ c *
        (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ d
      have hπg : π g = 1 := by
        have hmap : π g = π ((⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ a *
            (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ b *
            (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ c *
            (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ d) := rfl
        rw [hmap, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
        simpa [x0, x1, x2, x3] using hprod
      have hmem : g ∈ (StatedScalars (Fin 5) K).subgroupOf H := by
        change QuotientGroup.mk' _ g = 1 at hπg
        exact (QuotientGroup.eq_one_iff g).mp (by simpa [QuotientGroup.mk'_apply] using hπg)
      rw [Subgroup.mem_subgroupOf] at hmem
      have hdiag : (uc22s2112r34_deg5_E0 u) ^ a * (uc22s2112r34_deg5_E1 u) ^ b *
          (uc22s2112r34_deg5_E2 u) ^ c * (uc22s2112r34_deg5_E3 η) ^ d ∈
          StatedScalars (Fin 5) K := by
        simpa [g, Subgroup.coe_mul, Subgroup.coe_pow] using hmem
      exact uc22s2112r34_deg5_four_diag_independent u η huord hη25 rfl hdiag
    have hrank := uc22s2112r34_deg5_four_le_pRank_of_commuting_order_five
      (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
      hx0pow hx1pow hx2pow hx3pow hc01' hc02' hc03' hc12' hc13' hc23' hind
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) e] at hrank
    exact hrank
  · rw [h] at hX
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hX' := hX.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hX'
    let _ := hKfield
    let _ := hKfinite
    have hq0 : p ^ f ≠ 0 := pow_ne_zero f hp.pos.ne'
    have h25dvd : 25 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hKcard]
      have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
        have h1 : (p ^ f) ^ 2 - 1 = (p ^ f) ^ 2 - 1 ^ 2 := by norm_num
        rw [h1, Nat.sq_sub_sq]
        ring
      rw [hsq]
      exact dvd_mul_of_dvd_right h25 _
    obtain ⟨η, hη25⟩ := uc22s2112r34_deg5_exists_order_25 h25dvd
    let u : Kˣ := η ^ 5
    have huord : orderOf u = 5 := by
      dsimp [u]
      rw [orderOf_pow, hη25]
      norm_num
    have hu5 : u ^ 5 = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h'
      have : orderOf u = 1 := by rw [h']; exact orderOf_one
      omega
    have hη25' : η ^ 25 = 1 := by rw [← hη25]; exact pow_orderOf_eq_one η
    have hηq1 : η ^ (p ^ f + 1) = 1 := by
      obtain ⟨k, hk⟩ := h25
      rw [hk, pow_mul, hη25', one_pow]
    have huq1 : u ^ (p ^ f + 1) = 1 := by
      dsimp [u]
      rw [← pow_mul]
      obtain ⟨k, hk⟩ := h25
      rw [hk]
      have h5 : 5 * (25 * k) = 25 * (5 * k) := by ring
      rw [h5, pow_mul, hη25', one_pow]
    have hE0 : uc22s2112r34_deg5_E0 u ∈ StatedSU 5 (p ^ f) K :=
      uc22s2112r34_deg5_E0_mem_statedSU hq0 huq1
    have hE1 : uc22s2112r34_deg5_E1 u ∈ StatedSU 5 (p ^ f) K :=
      uc22s2112r34_deg5_E1_mem_statedSU hq0 huq1
    have hE2 : uc22s2112r34_deg5_E2 u ∈ StatedSU 5 (p ^ f) K :=
      uc22s2112r34_deg5_E2_mem_statedSU hq0 huq1
    have hE3 : uc22s2112r34_deg5_E3 η ∈ StatedSU 5 (p ^ f) K :=
      uc22s2112r34_deg5_E3_mem_statedSU hq0 hηq1
    have hE0pow : (uc22s2112r34_deg5_E0 u) ^ 5 = 1 := uc22s2112r34_deg5_E0_pow hu5
    have hE1pow : (uc22s2112r34_deg5_E1 u) ^ 5 = 1 := uc22s2112r34_deg5_E1_pow hu5
    have hE2pow : (uc22s2112r34_deg5_E2 u) ^ 5 = 1 := uc22s2112r34_deg5_E2_pow hu5
    have hE3pow : (uc22s2112r34_deg5_E3 η) ^ 5 ∈ StatedScalars (Fin 5) K :=
      uc22s2112r34_deg5_E3_pow hη25
    let H := StatedSU 5 (p ^ f) K
    let π : H →* StatedProj H := QuotientGroup.mk' _
    let x0 : StatedProj H := π ⟨uc22s2112r34_deg5_E0 u, hE0⟩
    let x1 : StatedProj H := π ⟨uc22s2112r34_deg5_E1 u, hE1⟩
    let x2 : StatedProj H := π ⟨uc22s2112r34_deg5_E2 u, hE2⟩
    let x3 : StatedProj H := π ⟨uc22s2112r34_deg5_E3 η, hE3⟩
    have hx0pow : x0 ^ 5 = 1 := by
      dsimp [x0]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE0pow
      rw [hsub, map_one]
    have hx1pow : x1 ^ 5 = 1 := by
      dsimp [x1]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE1pow
      rw [hsub, map_one]
    have hx2pow : x2 ^ 5 = 1 := by
      dsimp [x2]
      rw [← map_pow]
      have hsub : (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ 5 = 1 := by
        apply Subtype.ext
        exact hE2pow
      rw [hsub, map_one]
    have hx3pow : x3 ^ 5 = 1 := by
      dsimp [x3]
      rw [← map_pow]
      have hmem : (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ 5 ∈
          (StatedScalars (Fin 5) K).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hE3pow
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hc01 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E1 u) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E1]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc02 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E2 u) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E2]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc03 : Commute (uc22s2112r34_deg5_E0 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E0, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc12 : Commute (uc22s2112r34_deg5_E1 u) (uc22s2112r34_deg5_E2 u) := by
      rw [uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E2]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc13 : Commute (uc22s2112r34_deg5_E1 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E1, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc23 : Commute (uc22s2112r34_deg5_E2 u) (uc22s2112r34_deg5_E3 η) := by
      rw [uc22s2112r34_deg5_E2, uc22s2112r34_deg5_E3]
      exact (Commute.all _ _).map CFSG.SectionRank.ClassicalEven.torusDiag
    have hc01' : Commute x0 x1 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E1 u, hE1⟩ from Subtype.ext hc01.eq) π
    have hc02' : Commute x0 x2 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E2 u, hE2⟩ from Subtype.ext hc02.eq) π
    have hc03' : Commute x0 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc03.eq) π
    have hc12' : Commute x1 x2 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H)
        ⟨uc22s2112r34_deg5_E2 u, hE2⟩ from Subtype.ext hc12.eq) π
    have hc13' : Commute x1 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc13.eq) π
    have hc23' : Commute x2 x3 :=
      Commute.map (show Commute (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H)
        ⟨uc22s2112r34_deg5_E3 η, hE3⟩ from Subtype.ext hc23.eq) π
    have hind : ∀ a b c d : ℕ, x0 ^ a * x1 ^ b * x2 ^ c * x3 ^ d = 1 →
        5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
      intro a b c d hprod
      let g : H := (⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ a *
        (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ b *
        (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ c *
        (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ d
      have hπg : π g = 1 := by
        have hmap : π g = π ((⟨uc22s2112r34_deg5_E0 u, hE0⟩ : H) ^ a *
            (⟨uc22s2112r34_deg5_E1 u, hE1⟩ : H) ^ b *
            (⟨uc22s2112r34_deg5_E2 u, hE2⟩ : H) ^ c *
            (⟨uc22s2112r34_deg5_E3 η, hE3⟩ : H) ^ d) := rfl
        rw [hmap, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
        simpa [x0, x1, x2, x3] using hprod
      have hmem : g ∈ (StatedScalars (Fin 5) K).subgroupOf H := by
        change QuotientGroup.mk' _ g = 1 at hπg
        exact (QuotientGroup.eq_one_iff g).mp (by simpa [QuotientGroup.mk'_apply] using hπg)
      rw [Subgroup.mem_subgroupOf] at hmem
      have hdiag : (uc22s2112r34_deg5_E0 u) ^ a * (uc22s2112r34_deg5_E1 u) ^ b *
          (uc22s2112r34_deg5_E2 u) ^ c * (uc22s2112r34_deg5_E3 η) ^ d ∈
          StatedScalars (Fin 5) K := by
        simpa [g, Subgroup.coe_mul, Subgroup.coe_pow] using hmem
      exact uc22s2112r34_deg5_four_diag_independent u η huord hη25 rfl hdiag
    have hrank := uc22s2112r34_deg5_four_le_pRank_of_commuting_order_five
      (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
      hx0pow hx1pow hx2pow hx3pow hc01' hc02' hc03' hc12' hc13' hc23' hind
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) e] at hrank
    exact hrank

end CFSG.LocalAnalysis.UniquenessCase.UC22
