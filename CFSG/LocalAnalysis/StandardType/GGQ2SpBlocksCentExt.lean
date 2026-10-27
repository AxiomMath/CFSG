module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix
open CFSG.Open (StatedSp)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem tau_add (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u v : PlaneRaw.V m) : tau ζ m (u + v) = tau ζ m u * tau ζ m v := by
  have h : (fun i => Multiplicative.ofAdd ((u + v) i)) =
      (fun i => Multiplicative.ofAdd (u i)) * fun i => Multiplicative.ofAdd (v i) := by
    funext i
    rfl
  rw [tau, tau, tau, h, map_mul]

theorem tau_neg (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u : PlaneRaw.V m) : tau ζ m (-u) = (tau ζ m u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← tau_add, neg_add_cancel, tau_zero]

theorem tau_sub (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u v : PlaneRaw.V m) : tau ζ m (u - v) = tau ζ m u * (tau ζ m v)⁻¹ := by
  rw [sub_eq_add_neg, tau_add, tau_neg]

theorem tau_smul (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (c : ZMod 3) (v : PlaneRaw.V m) : tau ζ m (c • v) = tau ζ m v ^ c.val := by
  rw [← tau_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem tau_mul_comm (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u v : PlaneRaw.V m) : tau ζ m u * tau ζ m v = tau ζ m v * tau ζ m u := by
  rw [← tau_add, ← tau_add, add_comm]

theorem tau_injective {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) : Function.Injective (tau ζ m) := by
  intro u v h
  have h' : (fun i => Multiplicative.ofAdd (u i)) = fun i => Multiplicative.ofAdd (v i) :=
    TorC.spPlaneTorus_injective hζ m h
  funext i
  exact Multiplicative.ofAdd.injective (congrFun h' i)

theorem tau_single (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) {m : ℕ}
    (i : Fin m) (a : ZMod 3) :
    tau ζ m (Pi.single i a) = lam i (ζ (Multiplicative.ofAdd a)) := by
  have h : (fun k => Multiplicative.ofAdd ((Pi.single i a : PlaneRaw.V m) k)) =
      Pi.mulSingle i (Multiplicative.ofAdd a) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  rw [tau, h, spPlaneTorus_mulSingle]

theorem tau_eq_lam_mul_lam_mul (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    {m : ℕ} {i j : Fin m} (hij : i ≠ j) (u : PlaneRaw.V m) :
    tau ζ m u = lam i (ζ (Multiplicative.ofAdd (u i))) * lam j (ζ (Multiplicative.ofAdd (u j))) *
      tau ζ m (Function.update (Function.update u i 0) j 0) := by
  rw [← tau_single, ← tau_single, ← tau_add, ← tau_add]
  congr 1
  funext k
  simp only [Pi.add_apply, Pi.single_apply, Function.update_apply]
  by_cases hki : k = i
  · rw [hki]
    simp [hij]
  · by_cases hkj : k = j
    · rw [hkj]
      simp [Ne.symm hij]
    · simp [hki, hkj]

theorem mem_blockGroup_extension_iff {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    {m : ℕ} {e : PlaneRaw.V m} {g : ↥(StatedSp m K)} :
    g ∈ blockGroup ζ m (.extension e) ↔
      g ∈ levi m (PlaneRaw.Code.extSupport e) ∧ g * tau ζ m e = tau ζ m e * g := by
  show g ∈ levi m _ ⊓ Subgroup.centralizer _ ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem tau_mem_blockGroup_extension [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e v : PlaneRaw.V m} (hv : ∀ i, e i = 0 → v i = 0) :
    tau ζ m v ∈ blockGroup ζ m (.extension e) := by
  refine mem_blockGroup_extension_iff.mpr ⟨?_, tau_mul_comm ζ m v e⟩
  exact ycode_le_blockGroup ζ (.zero (PlaneRaw.Code.extSupport e))
    (tau_mem_ycode_zero hK hζ fun i hi => hv i (by simpa using hi))

private theorem zmod3_mul_self {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private theorem zmod3_mul_of_eq {a b : ZMod 3} (ha : a ≠ 0) (h : a = b) : a * b = 1 := by
  rw [← h]
  exact zmod3_mul_self ha

private theorem zmod3_mul_of_ne {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≠ b) :
    a * b = -1 := by
  revert a b
  decide

theorem sl2W_conj_zeta [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (a : ZMod 3) :
    sl2W * ζ (Multiplicative.ofAdd a) * sl2W⁻¹ = ζ (Multiplicative.ofAdd (-a)) := by
  by_cases ha : a = 0
  · rw [ha, neg_zero, ofAdd_zero, map_one, mul_one, mul_inv_cancel]
  · rw [sl2W_conj_eq_inv hK (zeta_pow_three a) (zeta_ne_one hζ ha), ofAdd_neg, map_inv]

@[expose] noncomputable def extSwap {m : ℕ} (e : PlaneRaw.V m) (i j : Fin m) (hij : i ≠ j) :
    ↥(StatedSp m K) :=
  if e i = e j then rho i j hij sl2W else lam i sl2W * lam j sl2W * rho i j hij sl2W

@[expose] def swapVec {m : ℕ} (e : PlaneRaw.V m) (i j : Fin m) (u : PlaneRaw.V m) :
    PlaneRaw.V m :=
  Function.update (Function.update u i (e i * e j * u j)) j (e i * e j * u i)

theorem swapVec_apply_fst {m : ℕ} (e : PlaneRaw.V m) {i j : Fin m} (hij : i ≠ j)
    (u : PlaneRaw.V m) : swapVec e i j u i = e i * e j * u j := by
  rw [swapVec, Function.update_of_ne hij, Function.update_self]

theorem swapVec_apply_snd {m : ℕ} (e : PlaneRaw.V m) (i j : Fin m) (u : PlaneRaw.V m) :
    swapVec e i j u j = e i * e j * u i := by
  rw [swapVec, Function.update_self]

theorem swapVec_apply_of_ne {m : ℕ} (e : PlaneRaw.V m) {i j k : Fin m} (hki : k ≠ i)
    (hkj : k ≠ j) (u : PlaneRaw.V m) : swapVec e i j u k = u k := by
  rw [swapVec, Function.update_of_ne hkj, Function.update_of_ne hki]

theorem swapVec_swapVec {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0)
    (hej : e j ≠ 0) (u : PlaneRaw.V m) : swapVec e i j (swapVec e i j u) = u := by
  funext k
  by_cases hki : k = i
  · rw [hki, swapVec_apply_fst e hij, swapVec_apply_snd]
    linear_combination (e j * e j * u i) * zmod3_mul_self hei + u i * zmod3_mul_self hej
  · by_cases hkj : k = j
    · rw [hkj, swapVec_apply_snd, swapVec_apply_fst e hij]
      linear_combination (e j * e j * u j) * zmod3_mul_self hei + u j * zmod3_mul_self hej
    · rw [swapVec_apply_of_ne e hki hkj, swapVec_apply_of_ne e hki hkj]

theorem swapVec_self {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0)
    (hej : e j ≠ 0) : swapVec e i j e = e := by
  funext k
  by_cases hki : k = i
  · rw [hki, swapVec_apply_fst e hij]
    linear_combination e i * zmod3_mul_self hej
  · by_cases hkj : k = j
    · rw [hkj, swapVec_apply_snd]
      linear_combination e j * zmod3_mul_self hei
    · rw [swapVec_apply_of_ne e hki hkj]

theorem swapVec_single {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) :
    swapVec e i j (Pi.single i (e i)) = Pi.single j (e j) := by
  funext k
  by_cases hki : k = i
  · rw [hki, swapVec_apply_fst e hij, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hij,
      mul_zero]
  · by_cases hkj : k = j
    · rw [hkj, swapVec_apply_snd, Pi.single_eq_same, Pi.single_eq_same]
      linear_combination e j * zmod3_mul_self hei
    · rw [swapVec_apply_of_ne e hki hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

theorem update_update_swapVec {m : ℕ} (e : PlaneRaw.V m) (i j : Fin m) (u : PlaneRaw.V m) :
    Function.update (Function.update (swapVec e i j u) i 0) j 0 =
      Function.update (Function.update u i 0) j 0 := by
  funext k
  simp only [swapVec, Function.update_apply]
  split_ifs <;> rfl

private theorem rho_conj_lam_fst {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (x : SpecialLinearGroup (Fin 2) K) :
    rho i j hij sl2W * lam i x * (rho i j hij sl2W)⁻¹ = lam j x := by
  have h := congrArg (fun φ => φ x) (conj_rho_sl2W_comp_lam_fst (k := K) hij)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem rho_conj_lam_snd {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (x : SpecialLinearGroup (Fin 2) K) :
    rho i j hij sl2W * lam j x * (rho i j hij sl2W)⁻¹ = lam i x := by
  have h := congrArg (fun φ => φ x) (conj_rho_sl2W_comp_lam_snd (k := K) hij)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem extSwap_conj_lam_fst [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) (hej : e j ≠ 0)
    (a : ZMod 3) :
    extSwap e i j hij * lam i (ζ (Multiplicative.ofAdd a)) * (extSwap e i j hij)⁻¹ =
      lam j (ζ (Multiplicative.ofAdd (e i * e j * a))) := by
  unfold extSwap
  split_ifs with h
  · rw [rho_conj_lam_fst, zmod3_mul_of_eq hei h, one_mul]
  · rw [zmod3_mul_of_ne hei hej h, neg_one_mul, ← sl2W_conj_zeta hK hζ]
    calc lam i sl2W * lam j sl2W * rho i j hij sl2W * lam i (ζ (Multiplicative.ofAdd a)) *
          (lam i sl2W * lam j sl2W * rho i j hij sl2W)⁻¹
        = lam i sl2W * (lam j sl2W * (rho i j hij sl2W * lam i (ζ (Multiplicative.ofAdd a)) *
            (rho i j hij sl2W)⁻¹) * (lam j sl2W)⁻¹) * (lam i sl2W)⁻¹ := by group
      _ = lam j (sl2W * ζ (Multiplicative.ofAdd a) * sl2W⁻¹) := by
          rw [rho_conj_lam_fst, ← map_inv (lam j), ← map_mul, ← map_mul,
            (commute_lam_lam hij _ _).eq, mul_inv_cancel_right]

theorem extSwap_conj_lam_snd [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) (hej : e j ≠ 0)
    (a : ZMod 3) :
    extSwap e i j hij * lam j (ζ (Multiplicative.ofAdd a)) * (extSwap e i j hij)⁻¹ =
      lam i (ζ (Multiplicative.ofAdd (e i * e j * a))) := by
  unfold extSwap
  split_ifs with h
  · rw [rho_conj_lam_snd, zmod3_mul_of_eq hei h, one_mul]
  · rw [zmod3_mul_of_ne hei hej h, neg_one_mul, ← sl2W_conj_zeta hK hζ]
    calc lam i sl2W * lam j sl2W * rho i j hij sl2W * lam j (ζ (Multiplicative.ofAdd a)) *
          (lam i sl2W * lam j sl2W * rho i j hij sl2W)⁻¹
        = lam i sl2W * (lam j sl2W * (rho i j hij sl2W * lam j (ζ (Multiplicative.ofAdd a)) *
            (rho i j hij sl2W)⁻¹) * (lam j sl2W)⁻¹) * (lam i sl2W)⁻¹ := by group
      _ = lam i (sl2W * ζ (Multiplicative.ofAdd a) * sl2W⁻¹) := by
          rw [rho_conj_lam_snd, (commute_lam_lam (Ne.symm hij) _ _).eq, mul_inv_cancel_right,
            ← map_inv (lam i), ← map_mul, ← map_mul]

theorem extSwap_mem_levi {m : ℕ} (e : PlaneRaw.V m) {S : Finset (Fin m)} {i j : Fin m}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    (extSwap e i j hij : ↥(StatedSp m K)) ∈ levi m S := by
  unfold extSwap
  split_ifs
  · exact rho_mem_levi hi hj hij _
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (lam_mem_levi hi _) (lam_mem_levi hj _))
      (rho_mem_levi hi hj hij _)

theorem extSwap_conj_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) (hej : e j ≠ 0)
    (u : PlaneRaw.V m) :
    extSwap e i j hij * tau ζ m u * (extSwap e i j hij)⁻¹ = tau ζ m (swapVec e i j u) := by
  have hσ : (extSwap e i j hij : ↥(StatedSp m K)) ∈ levi m {i, j} :=
    extSwap_mem_levi e (Finset.mem_insert_self i {j})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)) hij
  have h0 : ∀ k ∈ ({i, j} : Finset (Fin m)),
      Function.update (Function.update u i 0) j 0 k = 0 := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · rw [hk, Function.update_of_ne hij, Function.update_self]
    · rw [Finset.mem_singleton.mp hk, Function.update_self]
  have h3 := commute_tau_of_mem_levi (ζ := ζ) h0 hσ
  rw [tau_eq_lam_mul_lam_mul ζ hij u, tau_eq_lam_mul_lam_mul ζ hij (swapVec e i j u),
    update_update_swapVec, swapVec_apply_fst e hij, swapVec_apply_snd]
  calc extSwap e i j hij * (lam i (ζ (Multiplicative.ofAdd (u i))) *
        lam j (ζ (Multiplicative.ofAdd (u j))) *
        tau ζ m (Function.update (Function.update u i 0) j 0)) * (extSwap e i j hij)⁻¹
      = (extSwap e i j hij * lam i (ζ (Multiplicative.ofAdd (u i))) * (extSwap e i j hij)⁻¹) *
          (extSwap e i j hij * lam j (ζ (Multiplicative.ofAdd (u j))) * (extSwap e i j hij)⁻¹) *
          (extSwap e i j hij * tau ζ m (Function.update (Function.update u i 0) j 0) *
            (extSwap e i j hij)⁻¹) := by group
    _ = lam j (ζ (Multiplicative.ofAdd (e i * e j * u i))) *
          lam i (ζ (Multiplicative.ofAdd (e i * e j * u j))) *
          tau ζ m (Function.update (Function.update u i 0) j 0) := by
        rw [extSwap_conj_lam_fst hK hζ hij hei hej, extSwap_conj_lam_snd hK hζ hij hei hej, ← h3,
          mul_inv_cancel_right]
    _ = _ := by rw [(commute_lam_lam (Ne.symm hij) _ _).eq]

theorem extSwap_inv_conj_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) (hej : e j ≠ 0)
    (u : PlaneRaw.V m) :
    (extSwap e i j hij)⁻¹ * tau ζ m u * extSwap e i j hij = tau ζ m (swapVec e i j u) := by
  have h := extSwap_conj_tau hK hζ hij hei hej (swapVec e i j u)
  rw [swapVec_swapVec hij hei hej] at h
  rw [← h]
  group

theorem extSwap_mem_blockGroup [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hei : e i ≠ 0) (hej : e j ≠ 0) (hij : i ≠ j) :
    extSwap e i j hij ∈ blockGroup ζ m (.extension e) := by
  refine mem_blockGroup_extension_iff.mpr ⟨extSwap_mem_levi e
    ((PlaneRaw.mem_extSupport e i).mpr hei) ((PlaneRaw.mem_extSupport e j).mpr hej) hij, ?_⟩
  have h := extSwap_conj_tau hK hζ hij hei hej e
  rw [swapVec_self hij hei hej] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem tau_commute_ycode_extension_of
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {m : ℕ} {e u : PlaneRaw.V m}
    {i₀ : Fin m} (hi₀ : e i₀ ≠ 0) (hu : u ∈ PlaneRaw.centExt e) :
    ∀ g ∈ Ycode ζ m (.extension e), tau ζ m u * g = g * tau ζ m u := by
  intro g hg
  obtain ⟨hgL, hgC⟩ := mem_blockGroup_extension_iff.mp (ycode_le_blockGroup ζ (.extension e) hg)
  have hzero : ∀ i ∈ PlaneRaw.Code.extSupport e, (u - (e i₀ * u i₀) • e) i = 0 := by
    intro i hi
    have h := (PlaneRaw.mem_centExt e u).mp hu i hi i₀ ((PlaneRaw.mem_extSupport e i₀).mpr hi₀)
    have hsq := zmod3_mul_self ((PlaneRaw.mem_extSupport e i).mp hi)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination e i * h - u i * hsq
  have hdec : tau ζ m u = tau ζ m e ^ (e i₀ * u i₀).val * tau ζ m (u - (e i₀ * u i₀) • e) := by
    rw [← tau_smul, ← tau_add, add_sub_cancel]
  have h1 : Commute (tau ζ m e) g := hgC.symm
  have h2 : Commute (tau ζ m (u - (e i₀ * u i₀) • e)) g := commute_tau_of_mem_levi hzero hgL
  rw [hdec]
  exact (h1.pow_left _).mul_left h2

theorem centExt_of_tau_commute_ycode [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e u : PlaneRaw.V m} (h3 : 3 ≤ (PlaneRaw.Code.extSupport e).card)
    (h : ∀ g ∈ Ycode ζ m (.extension e), tau ζ m u * g = g * tau ζ m u) :
    u ∈ PlaneRaw.centExt e := by
  rw [PlaneRaw.mem_centExt]
  intro i hi j hj
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hk⟩ : (((PlaneRaw.Code.extSupport e).erase i).erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩),
      Finset.card_erase_of_mem hi]
    omega
  obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
  obtain ⟨hki, hkT⟩ := Finset.mem_erase.mp hk'
  have hei := (PlaneRaw.mem_extSupport e i).mp hi
  have hej := (PlaneRaw.mem_extSupport e j).mp hj
  have hek := (PlaneRaw.mem_extSupport e k).mp hkT
  have hjk : j ≠ k := Ne.symm hkj
  have hc : ⁅extSwap e i j hij, extSwap e j k hjk⁆ ∈ Ycode ζ m (.extension e) :=
    Subgroup.commutator_mem_commutator (extSwap_mem_blockGroup hK hζ hei hej hij)
      (extSwap_mem_blockGroup hK hζ hej hek hjk)
  have hconj : ⁅(extSwap (K := K) e i j hij), extSwap e j k hjk⁆ * tau ζ m u *
      ⁅(extSwap (K := K) e i j hij), extSwap e j k hjk⁆⁻¹ = tau ζ m u := by
    rw [← h _ hc, mul_inv_cancel_right]
  have hexp : ⁅(extSwap (K := K) e i j hij), extSwap e j k hjk⁆ * tau ζ m u *
      ⁅(extSwap (K := K) e i j hij), extSwap e j k hjk⁆⁻¹ =
      extSwap e i j hij * (extSwap e j k hjk * ((extSwap e i j hij)⁻¹ *
        ((extSwap e j k hjk)⁻¹ * tau ζ m u * extSwap e j k hjk) * extSwap e i j hij) *
        (extSwap e j k hjk)⁻¹) * (extSwap e i j hij)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hexp, extSwap_inv_conj_tau hK hζ hjk hej hek, extSwap_inv_conj_tau hK hζ hij hei hej,
    extSwap_conj_tau hK hζ hjk hej hek, extSwap_conj_tau hK hζ hij hei hej] at hconj
  have hv := congrFun (tau_injective hζ m hconj) i
  rw [swapVec_apply_fst e hij, swapVec_apply_fst e hjk, swapVec_apply_of_ne e hki hkj,
    swapVec_apply_snd] at hv
  linear_combination (-(e i)) * hv + (e j * u j * e j * e j * e k * e k) * zmod3_mul_self hei +
    (e j * u j * e k * e k) * zmod3_mul_self hej + (e j * u j) * zmod3_mul_self hek

theorem tau_sub_single_mem_ycode [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i j : Fin m} (hij : i ≠ j) (hei : e i ≠ 0) (hej : e j ≠ 0) :
    tau ζ m (Pi.single j (e j) - Pi.single i (e i)) ∈ Ycode ζ m (.extension e) := by
  have ht : tau ζ m (Pi.single i (e i)) ∈ blockGroup ζ m (.extension e) :=
    tau_mem_blockGroup_extension hK hζ fun k hk => by
      by_cases hki : k = i
      · rw [hki] at hk
        exact absurd hk hei
      · exact Pi.single_eq_of_ne hki _
  have hc := Subgroup.commutator_mem_commutator (extSwap_mem_blockGroup hK hζ hei hej hij) ht
  rw [commutatorElement_def, extSwap_conj_tau hK hζ hij hei hej, swapVec_single hij hei,
    ← tau_sub] at hc
  exact hc

theorem eq_sum_of_mem_insideExt {m : ℕ} {e u : PlaneRaw.V m} {i₀ : Fin m} (hi₀ : e i₀ ≠ 0)
    (hu : u ∈ PlaneRaw.insideExt e) :
    u = ∑ k ∈ (PlaneRaw.Code.extSupport e).erase i₀,
      (e k * u k) • (Pi.single k (e k) - Pi.single i₀ (e i₀)) := by
  obtain ⟨hsupp, hsum⟩ := (PlaneRaw.mem_insideExt e u).mp hu
  have hi₀T : i₀ ∈ PlaneRaw.Code.extSupport e := (PlaneRaw.mem_extSupport e i₀).mpr hi₀
  have hT : ∑ k ∈ PlaneRaw.Code.extSupport e, e k * u k = 0 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).trans hsum
    rw [PlaneRaw.mem_extSupport, not_not] at hk
    rw [hk, zero_mul]
  have herase := Finset.add_sum_erase (PlaneRaw.Code.extSupport e) (fun k => e k * u k) hi₀T
  rw [hT] at herase
  funext l
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  by_cases hl : l = i₀
  · rw [hl]
    rw [Finset.sum_congr rfl fun k hk => by
      rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk).symm, Pi.single_eq_same]]
    rw [← Finset.sum_mul]
    have hs : ∑ k ∈ (PlaneRaw.Code.extSupport e).erase i₀, e k * u k = -(e i₀ * u i₀) := by
      linear_combination herase
    rw [hs]
    linear_combination (-(u i₀)) * zmod3_mul_self hi₀
  · simp only [Pi.single_apply, hl, if_false, sub_zero]
    by_cases hlT : l ∈ PlaneRaw.Code.extSupport e
    · rw [Finset.sum_eq_single l]
      · rw [if_pos rfl]
        linear_combination (-(u l)) * zmod3_mul_self ((PlaneRaw.mem_extSupport e l).mp hlT)
      · intro k _ hkl
        rw [if_neg (Ne.symm hkl), mul_zero]
      · intro h
        exact absurd (Finset.mem_erase.mpr ⟨hl, hlT⟩) h
    · rw [Finset.sum_eq_zero]
      · exact hsupp l (by simpa using hlT)
      · intro k hk
        rw [if_neg, mul_zero]
        rintro rfl
        exact hlT (Finset.mem_of_mem_erase hk)

theorem tau_mem_ycode_extension_of [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e u : PlaneRaw.V m} {i₀ : Fin m} (hi₀ : e i₀ ≠ 0) (hu : u ∈ PlaneRaw.insideExt e) :
    tau ζ m u ∈ Ycode ζ m (.extension e) := by
  let W : AddSubgroup (PlaneRaw.V m) :=
    { carrier := {v | tau ζ m v ∈ Ycode ζ m (.extension e)}
      add_mem' := fun {a b} (ha : tau ζ m a ∈ Ycode ζ m (.extension e))
          (hb : tau ζ m b ∈ Ycode ζ m (.extension e)) => by
        show tau ζ m (a + b) ∈ Ycode ζ m (.extension e)
        rw [tau_add]
        exact Subgroup.mul_mem _ ha hb
      zero_mem' := by
        show tau ζ m 0 ∈ Ycode ζ m (.extension e)
        rw [tau_zero]
        exact Subgroup.one_mem _
      neg_mem' := fun {a} (ha : tau ζ m a ∈ Ycode ζ m (.extension e)) => by
        show tau ζ m (-a) ∈ Ycode ζ m (.extension e)
        rw [tau_neg]
        exact Subgroup.inv_mem _ ha }
  have hsmul : ∀ (c : ZMod 3) {v : PlaneRaw.V m}, v ∈ W → c • v ∈ W := fun c v hv => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact W.nsmul_mem hv _
  have hmem : u ∈ W := by
    rw [eq_sum_of_mem_insideExt hi₀ hu]
    refine W.sum_mem fun k hk => hsmul _ ?_
    obtain ⟨hki, hkT⟩ := Finset.mem_erase.mp hk
    exact tau_sub_single_mem_ycode hK hζ (Ne.symm hki) hi₀ ((PlaneRaw.mem_extSupport e k).mp hkT)
  exact hmem

@[expose] def planeBlock {m : ℕ} (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun s t => g (WitSpNs.coord s a) (WitSpNs.coord t b)

private theorem coord_zero {m : ℕ} (j : Fin m) : WitSpNs.coord 0 j = Sum.inl j := by
  simp [WitSpNs.coord]

private theorem coord_one {m : ℕ} (j : Fin m) : WitSpNs.coord 1 j = Sum.inr j := by
  simp [WitSpNs.coord]

theorem planeBlock_mul {m : ℕ} (g h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m) :
    planeBlock (g * h) a b = ∑ c, planeBlock g a c * planeBlock h c b := by
  ext s t
  rw [Matrix.sum_apply]
  simp only [planeBlock, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two, coord_zero,
    coord_one, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem planeBlock_planeMat {m : ℕ} (M : Fin m → Matrix (Fin 2) (Fin 2) K) (a b : Fin m) :
    planeBlock (WitSpNs.planeMat M) a b = if a = b then M a else 0 := by
  ext s t
  rw [planeBlock, Matrix.of_apply, WitSpNs.planeMat_apply, WitSpNs.plane_coord,
    WitSpNs.plane_coord, WitSpNs.side_coord, WitSpNs.side_coord]
  split_ifs with h
  · rw [h]
  · rfl

theorem planeBlock_one {m : ℕ} (a b : Fin m) :
    planeBlock (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = if a = b then 1 else 0 := by
  rw [← WitSpNs.planeMat_one, planeBlock_planeMat]

theorem planeBlock_mul_planeMat {m : ℕ} (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (M : Fin m → Matrix (Fin 2) (Fin 2) K) (a b : Fin m) :
    planeBlock (g * WitSpNs.planeMat M) a b = planeBlock g a b * M b := by
  rw [planeBlock_mul, Finset.sum_eq_single b]
  · rw [planeBlock_planeMat, if_pos rfl]
  · intro c _ hcb
    rw [planeBlock_planeMat, if_neg hcb, Matrix.mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem planeBlock_planeMat_mul {m : ℕ} (M : Fin m → Matrix (Fin 2) (Fin 2) K)
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m) :
    planeBlock (WitSpNs.planeMat M * g) a b = M a * planeBlock g a b := by
  rw [planeBlock_mul, Finset.sum_eq_single a]
  · rw [planeBlock_planeMat, if_pos rfl]
  · intro c _ hca
    rw [planeBlock_planeMat, if_neg (Ne.symm hca), Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem coe_apply_of_mem_levi {m : ℕ} {S : Finset (Fin m)} {g : ↥(StatedSp m K)}
    (hg : g ∈ levi m S) (x : Fin m ⊕ Fin m) {y : Fin m ⊕ Fin m} (hy : Sum.elim id id y ∉ S) :
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := by
  have h : ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      planeIdem m Sᶜ = planeIdem m Sᶜ := by
    rw [planeIdem_compl]
    exact hg
  have h' := congrFun (congrFun h x) y
  rw [planeIdem, Matrix.mul_diagonal, Matrix.diagonal_apply, if_pos (Finset.mem_compl.mpr hy),
    mul_one] at h'
  rw [h', Matrix.one_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy, hxy, if_pos (Finset.mem_compl.mpr hy)]
  · rw [if_neg hxy, if_neg hxy]

theorem planeBlock_eq_zero_of_mem_levi {m : ℕ} {S : Finset (Fin m)} {g : ↥(StatedSp m K)}
    (hg : g ∈ levi m S) {a c : Fin m} (hc : c ∉ S) (hac : a ≠ c) :
    planeBlock ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a c =
      0 := by
  ext s t
  have hne : WitSpNs.coord s a ≠ WitSpNs.coord t c := fun h =>
    hac (by simpa using congrArg WitSpNs.plane h)
  have hy : Sum.elim id id (WitSpNs.coord t c) ∉ S := by
    show WitSpNs.plane (WitSpNs.coord t c) ∉ S
    rw [WitSpNs.plane_coord]
    exact hc
  rw [planeBlock, Matrix.of_apply, coe_apply_of_mem_levi hg _ hy, Matrix.one_apply_ne hne]
  rfl

@[expose] noncomputable def normSL (x : ZMod 3) : SpecialLinearGroup (Fin 2) K :=
  if x = 1 then 1 else sl2W

theorem normSL_conj_zeta [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {x : ZMod 3} (hx : x ≠ 0) (a : ZMod 3) :
    normSL x * ζ (Multiplicative.ofAdd a) * (normSL x)⁻¹ = ζ (Multiplicative.ofAdd (x * a)) := by
  unfold normSL
  split_ifs with h
  · simp [h]
  · have hx' : x = -1 := by
      revert x
      decide
    rw [sl2W_conj_zeta hK hζ, hx', neg_one_mul]

theorem coe_normSL_conj_zeta [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {x : ZMod 3} (hx : x ≠ 0) (a : ZMod 3) :
    ((normSL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((ζ (Multiplicative.ofAdd a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (((normSL x)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd (x * a)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    normSL_conj_zeta hK hζ hx]

theorem coe_normSL_inv_mul (x : ZMod 3) :
    (((normSL x)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((normSL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_normSL_mul_inv (x : ZMod 3) :
    ((normSL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((normSL x)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] noncomputable def normBlock {m : ℕ} (e : PlaneRaw.V m)
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (a b : Fin m) : Matrix (Fin 2) (Fin 2) K :=
  ((normSL (e a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * planeBlock g a b *
    (((normSL (e b))⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

private theorem mul_conj_mul {A B N N' L R : Matrix (Fin 2) (Fin 2) K} (h : N' * N = 1) :
    L * (A * B) * R = L * A * N' * (N * B * R) := by
  rw [show A * B = A * (N' * N) * B by rw [h, Matrix.mul_one]]
  simp only [Matrix.mul_assoc]

theorem normBlock_mul {m : ℕ} (e : PlaneRaw.V m) {g : ↥(StatedSp m K)}
    (hg : g ∈ levi m (PlaneRaw.Code.extSupport e))
    (h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) {a : Fin m}
    (ha : a ∈ PlaneRaw.Code.extSupport e) (b : Fin m) :
    normBlock e (((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * h)
        a b =
      ∑ c ∈ PlaneRaw.Code.extSupport e,
        normBlock e ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a c *
          normBlock e h c b := by
  have hsum : planeBlock (((g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * h) a b =
      ∑ c ∈ PlaneRaw.Code.extSupport e,
        planeBlock ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a c *
          planeBlock h c b := by
    rw [planeBlock_mul]
    refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_).symm
    rw [planeBlock_eq_zero_of_mem_levi hg hc fun hac => hc (hac ▸ ha), Matrix.zero_mul]
  rw [normBlock, hsum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [normBlock, normBlock]
  exact mul_conj_mul (coe_normSL_inv_mul (e c))

theorem zeta_one_entries [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ) :
    ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
        1 ∧
      ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
        1 ∧
      ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have hsq := mul_self_add_self_eq_one hK (zeta_pow_three (ζ := ζ) 1)
    (zeta_ne_one hζ one_ne_zero)
  set A : Matrix (Fin 2) (Fin 2) K :=
    ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hA
  have hxx : ∀ x : K, x * x = x := fun x => by
    rcases eq_zero_or_eq_one hK x with hx | hx <;> rw [hx] <;> simp
  have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 + A 0 0 = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 + A 0 1 = 0 := by
    have := congrFun (congrFun hsq 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hbc : A 0 1 * A 1 0 = 1 := by
    rw [hxx, add_comm (A 0 0) _, add_assoc, CharTwo.add_self_eq_zero, add_zero] at h00
    exact h00
  have hb : A 0 1 = 1 := (eq_zero_or_eq_one hK _).resolve_left fun h0 => by
    rw [h0, zero_mul] at hbc
    exact zero_ne_one hbc
  have hc : A 1 0 = 1 := (eq_zero_or_eq_one hK _).resolve_left fun h0 => by
    rw [h0, mul_zero] at hbc
    exact zero_ne_one hbc
  refine ⟨hb, hc, ?_⟩
  rw [hb, mul_one, one_mul] at h01
  linear_combination h01 - (CharTwo.two_eq_zero : (2 : K) = 0)

abbrev zAlg (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Subalgebra K (Matrix (Fin 2) (Fin 2) K) :=
  Algebra.adjoin K
    {((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

@[reducible, expose] noncomputable def zAlgCommRing
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) : CommRing ↥(zAlg ζ) :=
  Algebra.adjoinCommRingOfComm K (Set.pairwise_singleton _ _)

attribute [local instance] zAlgCommRing

theorem mem_zAlg_of_commute [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X * ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        X) :
    X ∈ zAlg ζ := by
  obtain ⟨h01, h10, -⟩ := zeta_one_entries hK hζ
  set Z : Matrix (Fin 2) (Fin 2) K :=
    ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hZ
  have e00 := congrFun (congrFun hX 0) 0
  have e01 := congrFun (congrFun hX 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10] at e00 e01
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have q00 : X 0 0 =
      ((X 0 0 + X 0 1 * Z 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) + X 0 1 • Z) 0 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
    linear_combination (-(X 0 1 * Z 0 0)) * h2
  have q01 : X 0 1 =
      ((X 0 0 + X 0 1 * Z 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) + X 0 1 • Z) 0 1 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), h01]
    ring
  have q10 : X 1 0 =
      ((X 0 0 + X 0 1 * Z 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) + X 0 1 • Z) 1 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne (one_ne_zero : (1 : Fin 2) ≠ 0), h10]
    linear_combination (-1 : K) * e00
  have q11 : X 1 1 =
      ((X 0 0 + X 0 1 * Z 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) + X 0 1 • Z) 1 1 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
    linear_combination (-1 : K) * e01 - (X 0 1 * Z 0 0) * h2
  have hX' : X = (X 0 0 + X 0 1 * Z 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) + X 0 1 • Z := by
    ext i j
    fin_cases i <;> fin_cases j
    exacts [q00, q01, q10, q11]
  rw [hX']
  exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
    (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)

private theorem conj_commute {Na Na' Nb Nb' B Za Zb Z : Matrix (Fin 2) (Fin 2) K}
    (ha : Na' * Na = 1) (hb : Nb' * Nb = 1) (hZa : Na * Za * Na' = Z) (hZb : Nb * Zb * Nb' = Z)
    (hB : B * Zb = Za * B) : Na * B * Nb' * Z = Z * (Na * B * Nb') := by
  calc Na * B * Nb' * Z = Na * B * Nb' * (Nb * Zb * Nb') := by rw [hZb]
    _ = Na * B * (Nb' * Nb) * Zb * Nb' := by simp only [Matrix.mul_assoc]
    _ = Na * (B * Zb) * Nb' := by rw [hb, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Na * (Za * B) * Nb' := by rw [hB]
    _ = Na * Za * (Na' * Na) * B * Nb' := by rw [ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (Na * Za * Na') * (Na * B * Nb') := by simp only [Matrix.mul_assoc]
    _ = Z * (Na * B * Nb') := by rw [hZa]

theorem normBlock_commute [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {g : ↥(StatedSp m K)} (hg : g * tau ζ m e = tau ζ m e * g)
    {a b : Fin m} (ha : e a ≠ 0) (hb : e b ≠ 0) :
    normBlock e ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b *
        ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        normBlock e ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
          a b := by
  have hmat := coe_mul_comm_of_mul_comm hg
  rw [coe_tau] at hmat
  have hB := congrArg (fun X => planeBlock X a b) hmat
  simp only [planeBlock_mul_planeMat, planeBlock_planeMat_mul] at hB
  have hZa := coe_normSL_conj_zeta hK hζ ha (e a)
  have hZb := coe_normSL_conj_zeta hK hζ hb (e b)
  rw [zmod3_mul_self ha] at hZa
  rw [zmod3_mul_self hb] at hZb
  exact conj_commute (coe_normSL_inv_mul _) (coe_normSL_inv_mul _) hZa hZb hB

theorem zeta_mem_zAlg (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (x : Multiplicative (ZMod 3)) :
    ((ζ x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∈ zAlg ζ := by
  have hx : x = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd x).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [hx, map_pow, Matrix.SpecialLinearGroup.coe_pow]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _

@[expose] noncomputable def zetaC (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Multiplicative (ZMod 3) →* ↥(zAlg ζ) where
  toFun x := ⟨((ζ x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    zeta_mem_zAlg ζ x⟩
  map_one' := Subtype.ext (by
    show ((ζ 1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [map_one, Matrix.SpecialLinearGroup.coe_one])
  map_mul' x y := Subtype.ext (by
    show ((ζ (x * y) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ζ x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((ζ y : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul])

theorem zetaC_injective {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) : Function.Injective (zetaC ζ) := by
  intro x y h
  apply hζ
  apply Subtype.ext
  exact congrArg (fun z : ↥(zAlg ζ) => (z : Matrix (Fin 2) (Fin 2) K)) h

@[expose] noncomputable def blockMatC [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) (g : ↥(blockGroup ζ m (.extension e))) :
    Matrix ↥(PlaneRaw.Code.extSupport e) ↥(PlaneRaw.Code.extSupport e) ↥(zAlg ζ) :=
  Matrix.of fun a b => ⟨normBlock e (((g : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b,
    mem_zAlg_of_commute hK hζ (normBlock_commute hK hζ (mem_blockGroup_extension_iff.mp g.2).2
      ((PlaneRaw.mem_extSupport e a).mp a.2) ((PlaneRaw.mem_extSupport e b).mp b.2))⟩

theorem blockMatC_one [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) : blockMatC hK hζ e 1 = 1 := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  change normBlock e 1 a b = (((1 : Matrix ↥(PlaneRaw.Code.extSupport e)
    ↥(PlaneRaw.Code.extSupport e) ↥(zAlg ζ)) a b : ↥(zAlg ζ)) : Matrix (Fin 2) (Fin 2) K)
  rw [normBlock, planeBlock_one]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, if_pos rfl, Matrix.mul_one, coe_normSL_mul_inv]
    rfl
  · rw [Matrix.one_apply_ne hab, if_neg fun h => hab (Subtype.ext h), Matrix.mul_zero,
      Matrix.zero_mul]
    rfl

theorem blockMatC_mul [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) (g h : ↥(blockGroup ζ m (.extension e))) :
    blockMatC hK hζ e (g * h) = blockMatC hK hζ e g * blockMatC hK hζ e h := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  rw [Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]
  change normBlock e ((((g : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (((h : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) a b =
    ∑ c : ↥(PlaneRaw.Code.extSupport e), normBlock e (((g : ↥(StatedSp m K)) :
      GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a c *
        normBlock e (((h : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) c b
  rw [normBlock_mul e (mem_blockGroup_extension_iff.mp g.2).1 _ a.2, ← Finset.sum_coe_sort]

@[expose] noncomputable def detF4 [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) : ↥(blockGroup ζ m (.extension e)) →* ↥(zAlg ζ) where
  toFun g := (blockMatC hK hζ e g).det
  map_one' := by rw [blockMatC_one, Matrix.det_one]
  map_mul' g h := by rw [blockMatC_mul, Matrix.det_mul]

theorem detF4_apply [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) (g : ↥(blockGroup ζ m (.extension e))) :
    detF4 hK hζ e g = (blockMatC hK hζ e g).det :=
  rfl

theorem blockMatC_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e u : PlaneRaw.V m} (hu : tau ζ m u ∈ blockGroup ζ m (.extension e)) :
    blockMatC hK hζ e ⟨tau ζ m u, hu⟩ =
      Matrix.diagonal fun a : ↥(PlaneRaw.Code.extSupport e) =>
        zetaC ζ (Multiplicative.ofAdd (e a * u a)) := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  change normBlock e (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = _
  rw [normBlock, coe_tau, planeBlock_planeMat, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl,
      coe_normSL_conj_zeta hK hζ ((PlaneRaw.mem_extSupport e a).mp a.2)]
    rfl
  · rw [if_neg fun h => hab (Subtype.ext h), if_neg hab, Matrix.mul_zero, Matrix.zero_mul]
    rfl

theorem detF4_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e u : PlaneRaw.V m} (hu : tau ζ m u ∈ blockGroup ζ m (.extension e)) :
    detF4 hK hζ e ⟨tau ζ m u, hu⟩ =
      zetaC ζ (Multiplicative.ofAdd (∑ a : ↥(PlaneRaw.Code.extSupport e), e a * u a)) := by
  rw [detF4_apply, blockMatC_tau, Matrix.det_diagonal, ofAdd_sum, map_prod]

theorem detF4_eq_one_of_mem_ycode [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {g : ↥(StatedSp m K)} (hg : g ∈ Ycode ζ m (.extension e)) :
    detF4 hK hζ e ⟨g, ycode_le_blockGroup ζ _ hg⟩ = 1 := by
  have key : Ycode ζ m (.extension e) ≤
      (detF4 hK hζ e).ker.map (blockGroup ζ m (.extension e)).subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine ⟨⁅(⟨a, ha⟩ : ↥(blockGroup ζ m (.extension e))), ⟨b, hb⟩⁆, MonoidHom.mem_ker.mpr ?_,
      rfl⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    calc detF4 hK hζ e ⟨a, ha⟩ * detF4 hK hζ e ⟨b, hb⟩ * detF4 hK hζ e ⟨a, ha⟩⁻¹ *
          detF4 hK hζ e ⟨b, hb⟩⁻¹
        = detF4 hK hζ e (⟨a, ha⟩ * ⟨a, ha⟩⁻¹) * detF4 hK hζ e (⟨b, hb⟩ * ⟨b, hb⟩⁻¹) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, mul_one]
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (key hg)
  have hx' : x = ⟨g, ycode_le_blockGroup ζ _ hg⟩ := Subtype.ext hxg
  rw [← hx']
  exact hx

theorem sum_eq_zero_of_tau_mem_ycode [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e u : PlaneRaw.V m} (h : tau ζ m u ∈ Ycode ζ m (.extension e)) :
    ∑ i, e i * u i = 0 := by
  have h1 := detF4_eq_one_of_mem_ycode hK hζ h
  rw [detF4_tau] at h1
  have h2 : Multiplicative.ofAdd (∑ a : ↥(PlaneRaw.Code.extSupport e), e a * u a) = 1 :=
    zetaC_injective hζ (h1.trans (map_one _).symm)
  rw [ofAdd_eq_one, Finset.sum_coe_sort (PlaneRaw.Code.extSupport e) fun i => e i * u i] at h2
  rw [← h2]
  exact (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => by
    rw [PlaneRaw.mem_extSupport, not_not] at hk
    rw [hk, zero_mul]).symm

theorem tau_mem_ycode_extension_iff [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : PlaneRaw.admissible .symplectic (.extension e))
    (u : PlaneRaw.V m) :
    tau ζ m u ∈ Ycode ζ m (.extension e) ↔ u ∈ PlaneRaw.inside .symplectic (.extension e) := by
  have he' : 4 ≤ (PlaneRaw.Code.extSupport e).card := he.2
  change _ ↔ u ∈ PlaneRaw.insideExt e
  constructor
  · intro h
    rw [PlaneRaw.mem_insideExt]
    exact ⟨fun i hi => eq_zero_of_tau_mem_levi hK hζ
      (mem_blockGroup_extension_iff.mp (ycode_le_blockGroup ζ _ h)).1 i (by simpa using hi),
      sum_eq_zero_of_tau_mem_ycode hK hζ h⟩
  · intro h
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < (PlaneRaw.Code.extSupport e).card)
    exact tau_mem_ycode_extension_of hK hζ ((PlaneRaw.mem_extSupport e i₀).mp hi₀) h

theorem tau_commute_ycode_extension_iff [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : PlaneRaw.admissible .symplectic (.extension e))
    (u : PlaneRaw.V m) :
    (∀ g ∈ Ycode ζ m (.extension e), tau ζ m u * g = g * tau ζ m u) ↔
      u ∈ PlaneRaw.cent .symplectic (.extension e) := by
  have he' : 4 ≤ (PlaneRaw.Code.extSupport e).card := he.2
  change _ ↔ u ∈ PlaneRaw.centExt e
  constructor
  · exact centExt_of_tau_commute_ycode hK hζ (by omega)
  · intro h
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < (PlaneRaw.Code.extSupport e).card)
    exact tau_commute_ycode_extension_of ((PlaneRaw.mem_extSupport e i₀).mp hi₀) h

theorem spTauMemYcodeIff_holds : SpTauMemYcodeIff := by
  intro K _ _ _ ζ m hK hζ c hc u
  cases c with
  | zero S => exact tau_mem_ycode_zero_iff hK hζ S u
  | extension e => exact tau_mem_ycode_extension_iff hK hζ hc u

theorem spTauCommuteYcodeIff_holds : SpTauCommuteYcodeIff := by
  intro K _ _ _ ζ m hK hζ c hc u
  cases c with
  | zero S => exact tau_commute_ycode_zero_iff hK hζ hc u
  | extension e => exact tau_commute_ycode_extension_iff hK hζ hc u

end CFSG.StandardType.GGQ2Frame.SpBlocks

end
