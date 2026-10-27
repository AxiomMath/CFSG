module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.HSL3Bridge
public import CFSG.Quasithin.Background.HMultFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.ScalarSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MultSpace
public import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open scoped Matrix

private def colHom {m : ℕ} {K : Type} [Field K] :
    Multiplicative (Fin m × Fin 2 → K) →* Multiplicative (Fin m → K) where
  toFun v := Multiplicative.ofAdd fun j => Multiplicative.toAdd v (j, 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    simp
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext j
    simp

private theorem colHom_apply {m : ℕ} {K : Type} [Field K]
    (v : Multiplicative (Fin m × Fin 2 → K)) (j : Fin m) :
    (colHom v).toAdd j = v.toAdd (j, 0) := rfl

private theorem colHom_kronGL {m : ℕ} {K : Type} [Field K] (B : GL (Fin m) K)
    (v : Multiplicative (Fin m × Fin 2 → K)) :
    colHom (matAut (kronGL (Fin 2) m B) v) =
      Multiplicative.ofAdd ((B : Matrix (Fin m) (Fin m) K) *ᵥ (colHom v).toAdd) := by
  apply Multiplicative.toAdd.injective
  funext j
  rw [colHom_apply, toAdd_ofAdd]
  have hmat : (matAut (kronGL (Fin 2) m B) v).toAdd =
      (((kronGL (Fin 2) m B : GL (Fin m × Fin 2) K)) :
        Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) *ᵥ v.toAdd :=
    toAddMap_matAut (kronGL (Fin 2) m B) v.toAdd
  rw [hmat, kronGL_mulVec]
  rfl

variable {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ} {L₂ : Subgroup (MulAut W)}
  {π₂ : ↥(StatedSL 2 K) →* ↥L₂} {n : ℕ} {a : Fin n → ↥(StatedSL 2 K)}
  {col : W →* Multiplicative (Fin m → K)} {ψ : ↥L₂ →* GL (Fin m) K} {𝒮 : Set (Subgroup W)}

private def colSub (col : W →* Multiplicative (Fin m → K)) (J : Subgroup W) :
    AddSubgroup (Fin m → K) :=
  Subgroup.toAddSubgroup' (J.map col)

private theorem mem_colSub (col : W →* Multiplicative (Fin m → K)) (J : Subgroup W)
    (v : Fin m → K) : v ∈ colSub col J ↔ ∃ w ∈ J, (col w).toAdd = v := by
  rw [colSub, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    exact ⟨w, hw, by rw [hwv, toAdd_ofAdd]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, ofAdd_toAdd (col w)⟩

private theorem exists_colHom (e : W ≃* StdMod (Fin m × Fin 2) K) (ψ : ↥L₂ →* GL (Fin m) K)
    (he : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w)) :
    ∃ col : W →* Multiplicative (Fin m → K), Function.Surjective col ∧
      ∀ (y : ↥L₂) (w : W),
        (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd := by
  classical
  refine ⟨colHom.comp e.toMonoidHom, ?_, ?_⟩
  · intro v
    refine ⟨e.symm (Multiplicative.ofAdd fun p => if p.2 = 0 then v.toAdd p.1 else 0), ?_⟩
    apply Multiplicative.toAdd.injective
    funext j
    show (e (e.symm (Multiplicative.ofAdd fun p => if p.2 = 0 then v.toAdd p.1 else 0))).toAdd
        (j, 0) = v.toAdd j
    rw [MulEquiv.apply_symm_apply]
    simp
  · intro y w
    have h := colHom_kronGL (ψ y) (e w)
    rw [← he y w] at h
    exact congrArg Multiplicative.toAdd h

private theorem exists_col_prodAct
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd) :
    ∃ D : Matrix (Fin m) (Fin m) K,
      ∀ w : W, (col (prodAct π₂ a w)).toAdd = D *ᵥ (col w).toAdd := by
  classical
  refine ⟨∑ i, ((ψ (π₂ (a i)) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K), fun w => ?_⟩
  have h1 : col (prodAct π₂ a w) = ∏ i, col (((π₂ (a i) : ↥L₂) : MulAut W) w) := by
    rw [prodAct_apply, map_prod]
  rw [h1, toAdd_prod, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => col_act (π₂ (a i)) w

private theorem col_prodAct_rel (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (col_surj : Function.Surjective col)
    (hrel : ∀ v : W, prodAct π₂ a (prodAct π₂ a v) * prodAct π₂ a v * v = 1)
    (hcommL : ∀ x ∈ L₂, ∀ v : W, prodAct π₂ a (x v) = x (prodAct π₂ a v))
    {D : Matrix (Fin m) (Fin m) K}
    (hD : ∀ w : W, (col (prodAct π₂ a w)).toAdd = D *ᵥ (col w).toAdd) :
    D * D + D + 1 = 0 ∧
      ∀ y : ↥L₂, D * (ψ y : Matrix (Fin m) (Fin m) K) =
        (ψ y : Matrix (Fin m) (Fin m) K) * D := by
  constructor
  · refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    obtain ⟨w, hw⟩ := col_surj v
    rw [show v = (col w).toAdd from hw.symm]
    have h1 : col (prodAct π₂ a (prodAct π₂ a w) * prodAct π₂ a w * w) = 1 := by
      rw [hrel w, map_one]
    rw [map_mul, map_mul] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_mul, toAdd_mul, toAdd_one, hD (prodAct π₂ a w), hD w,
      Matrix.mulVec_mulVec] at h2
    rw [Matrix.zero_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    exact h2
  · intro y
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    obtain ⟨w, hw⟩ := col_surj v
    rw [show v = (col w).toAdd from hw.symm]
    have h := congrArg Multiplicative.toAdd (congrArg col (hcommL y y.2 w))
    rw [hD ((y : MulAut W) w), col_act y w, col_act y (prodAct π₂ a w), hD w,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    exact h

private theorem colSub_ker_eq_bot {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (hS : colSub col J ≠ ⊥) : J ⊓ col.ker = ⊥ := by
  have hker_stable : StableUnder L₂ (J ⊓ col.ker) := by
    intro y hy u hu
    refine ⟨(hirr J hJ).2.1 y hy u hu.1, ?_⟩
    have hucol : col u = 1 := hu.2
    apply Multiplicative.toAdd.injective
    rw [col_act ⟨y, hy⟩ u, hucol, toAdd_one, Matrix.mulVec_zero]
  rcases (hirr J hJ).2.2.2 (J ⊓ col.ker) hker_stable bot_le inf_le_left with h | h
  · exact h
  · exfalso
    apply hS
    have hle : J ≤ col.ker := h ▸ inf_le_right
    have h1 : J.map col = ⊥ := (Subgroup.map_eq_bot_iff J).mpr hle
    rw [show colSub col J = Subgroup.toAddSubgroup' (J.map col) from rfl, h1, OrderIso.map_bot]

private theorem colSub_card {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    (hK : Nat.card K = 2 ^ 2) (hS : colSub col J ≠ ⊥) : Nat.card ↥(colSub col J) = 16 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero 2 (by norm_num))
  have hker : J ⊓ col.ker = ⊥ := colSub_ker_eq_bot hJ hirr col_act hS
  have hinj : ∀ u v : ↥J, col (u : W) = col (v : W) → u = v := by
    intro u v huv
    have h1 : ((u : ↥J) : W) * (((v : ↥J) : W))⁻¹ ∈ J ⊓ col.ker := by
      refine ⟨J.mul_mem u.2 (J.inv_mem v.2), ?_⟩
      show col ((u : W) * (v : W)⁻¹) = 1
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    rw [hker] at h1
    have h2 : (u : W) = (v : W) := by
      have h3 := Subgroup.mem_bot.mp h1
      rwa [mul_inv_eq_one] at h3
    exact Subtype.ext h2
  have hf : Function.Bijective (fun u : ↥J =>
      (⟨col (u : W), Subgroup.mem_map_of_mem col u.2⟩ : ↥(J.map col))) := by
    refine ⟨fun u v huv => hinj u v (congrArg Subtype.val huv), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨w, hwJ, hwx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨w, hwJ⟩, Subtype.ext hwx⟩
  obtain ⟨eJ, -⟩ :=
    CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub (StatedSL 2 K) (hreal J hJ)
  have hcardJ : Nat.card ↥J = 16 := by
    rw [Nat.card_congr eJ.toEquiv, card_stdMod (ι := Fin 2) (K := K), hK, Fintype.card_fin]
    norm_num
  rw [show Nat.card ↥(colSub col J) = Nat.card ↥(J.map col) from rfl,
    (Nat.card_congr (_root_.Equiv.ofBijective _ hf)).symm, hcardJ]

private theorem colSub_smul_mem {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (y : ↥L₂) {v : Fin m → K} (hv : v ∈ colSub col J) :
    (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ colSub col J := by
  obtain ⟨w, hw, rfl⟩ := (mem_colSub col J v).mp hv
  rw [← col_act y w]
  exact (mem_colSub col J _).mpr
    ⟨(y : MulAut W) w, (hreal J hJ).2.2.2.1 ⟨y, y.2⟩ w hw, rfl⟩

private theorem colSub_D_mem {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    {D : Matrix (Fin m) (Fin m) K}
    (hD : ∀ w : W, (col (prodAct π₂ a w)).toAdd = D *ᵥ (col w).toAdd)
    {v : Fin m → K} (hv : v ∈ colSub col J) : D *ᵥ v ∈ colSub col J := by
  obtain ⟨w, hw, rfl⟩ := (mem_colSub col J v).mp hv
  rw [← hD w]
  exact (mem_colSub col J _).mpr ⟨prodAct π₂ a w, by
    rw [prodAct_apply]
    exact J.prod_mem fun i _ =>
      (hreal J hJ).2.2.2.1 ⟨π₂ (a i), (π₂ (a i)).2⟩ w hw, rfl⟩

private theorem colSub_irreducible {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd) :
    ∀ T : AddSubgroup (Fin m → K), T ≤ colSub col J →
      (∀ (y : ↥L₂) (v : Fin m → K),
        v ∈ T → (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) →
      T = ⊥ ∨ T = colSub col J := by
  intro T hTS hT
  have hmem : ∀ w : W, w ∈ J ⊓ T.toSubgroup.comap col ↔ w ∈ J ∧ (col w).toAdd ∈ T := by
    intro w
    rw [Subgroup.mem_inf, Subgroup.mem_comap, Multiplicative.mem_toSubgroup]
  have hstable : StableUnder L₂ (J ⊓ T.toSubgroup.comap col) := by
    intro y hy w hw
    rw [hmem] at hw ⊢
    refine ⟨(hreal J hJ).2.2.2.1 ⟨y, hy⟩ w hw.1, ?_⟩
    rw [col_act ⟨y, hy⟩ w]
    exact hT ⟨y, hy⟩ _ hw.2
  rcases (hirr J hJ).2.2.2 _ hstable bot_le inf_le_left with h | h
  · refine Or.inl (le_antisymm ?_ bot_le)
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_colSub col J v).mp (hTS hv)
    have hwJT : w ∈ J ⊓ T.toSubgroup.comap col := (hmem w).mpr ⟨hw, hv⟩
    rw [h] at hwJT
    rw [Subgroup.mem_bot.mp hwJT, map_one, toAdd_one]
    exact AddSubgroup.zero_mem _
  · refine Or.inr (le_antisymm hTS ?_)
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_colSub col J v).mp hv
    exact ((hmem w).mp (by rw [h]; exact hw)).2

private theorem colSub_faithful {J : Subgroup W} (hJ : J ∈ 𝒮)
    (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (hπ₂ : Function.Surjective π₂) (hS : colSub col J ≠ ⊥) (y : ↥L₂)
    (hfix : ∀ v ∈ colSub col J, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v = v) : y = 1 := by
  have hstab : StableUnder L₂ J := fun x hx u hu => (hreal J hJ).2.2.2.1 ⟨x, hx⟩ u hu
  have hfixJ : ∀ w : W, w ∈ J → (y : MulAut W) w = w := by
    intro w hw
    have h1 : col ((y : MulAut W) w) = col w := by
      apply Multiplicative.toAdd.injective
      rw [col_act y w, hfix (col w).toAdd ((mem_colSub col J _).mpr ⟨w, hw, rfl⟩)]
    have h3 : ((y : MulAut W) w) * w⁻¹ ∈ J ⊓ col.ker := by
      refine ⟨J.mul_mem (hstab y y.2 w hw) (J.inv_mem hw), ?_⟩
      show col ((y : MulAut W) w * w⁻¹) = 1
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [colSub_ker_eq_bot hJ hirr col_act hS] at h3
    have h4 := Subgroup.mem_bot.mp h3
    rwa [mul_inv_eq_one] at h4
  obtain ⟨γ, rfl⟩ := hπ₂ y
  obtain ⟨eJ, heJ⟩ :=
    CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub (StatedSL 2 K) (hreal J hJ)
  have htriv : ∀ v : Fin 2 → K,
      (((γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    intro v
    obtain ⟨u, rfl⟩ := eJ.surjective (Multiplicative.ofAdd v)
    have hmem : ((π₂ γ : ↥L₂) : MulAut W) (u : W) ∈ J := hstab (π₂ γ) (π₂ γ).2 u u.2
    have h1 := heJ γ u hmem
    have h2 : ((π₂ γ : ↥L₂) : MulAut W) (u : W) = (u : W) := hfixJ (u : W) u.2
    have hsub : (⟨((π₂ γ : ↥L₂) : MulAut W) (u : W), hmem⟩ : ↥J) = u := Subtype.ext h2
    rw [hsub] at h1
    have h3 : (eJ u).toAdd = (natAct (StatedSL 2 K) γ (eJ u)).toAdd := by
      rw [← congrArg Multiplicative.toAdd h1]
    have h4 : (natAct (StatedSL 2 K) γ (eJ u)).toAdd =
        (((γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (eJ u).toAdd :=
      toAddMap_natAut (StatedSL 2 K) γ (eJ u).toAdd
    exact (h3.trans h4).symm
  have hγ1 : γ = 1 := by
    refine Subtype.ext (Units.ext ?_)
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    simpa using htriv v
  rw [hγ1, map_one]

private theorem exists_planes
    (col_act : ∀ (y : ↥L₂) (w : W),
      (col ((y : MulAut W) w)).toAdd = (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ (col w).toAdd)
    (col_surj : Function.Surjective col) (hsup : ⨆ J ∈ 𝒮, J = ⊤)
    (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂)
    (hπ₂ : Function.Surjective π₂)
    (hK : Nat.card K = 2 ^ 2) {D : Matrix (Fin m) (Fin m) K}
    (hD : ∀ w : W, (col (prodAct π₂ a w)).toAdd = D *ᵥ (col w).toAdd) :
    ∃ 𝒮' : Set (AddSubgroup (Fin m → K)), (⨆ S ∈ 𝒮', S = ⊤) ∧
      (∀ S ∈ 𝒮', ∀ (y : ↥L₂) (v : Fin m → K),
        v ∈ S → (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S) ∧
      (∀ S ∈ 𝒮', ∀ v : Fin m → K, v ∈ S → D *ᵥ v ∈ S) ∧
      (∀ S ∈ 𝒮', ∀ T : AddSubgroup (Fin m → K), T ≤ S →
        (∀ (y : ↥L₂) (v : Fin m → K),
          v ∈ T → (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) →
        T = ⊥ ∨ T = S) ∧
      (∀ S ∈ 𝒮', Nat.card ↥S = 16) ∧
      (∀ S ∈ 𝒮', ∀ y : ↥L₂,
        (∀ v ∈ S, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → y = 1) := by
  classical
  refine ⟨{S | ∃ J ∈ 𝒮, S = colSub col J ∧ S ≠ ⊥}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hJsup : (⨆ J : 𝒮, ((J : Subgroup W))) = ⊤ := by
      rw [iSup_subtype'' 𝒮 (fun J : Subgroup W => J)]
      exact hsup
    have hmap : (⨆ J : 𝒮, ((J : Subgroup W).map col)) = ⊤ := by
      rw [← Subgroup.map_iSup, hJsup, Subgroup.map_top_of_surjective col col_surj]
    have h1 : (⨆ J ∈ 𝒮, colSub col J) ≤ ⨆ S ∈ {S | ∃ J ∈ 𝒮, S = colSub col J ∧ S ≠ ⊥}, S := by
      refine iSup₂_le fun J hJ => ?_
      by_cases hS : colSub col J = ⊥
      · rw [hS]
        exact bot_le
      · exact le_iSup₂_of_le (colSub col J) ⟨J, hJ, rfl, hS⟩ le_rfl
    have h2 : (⨆ S ∈ {S | ∃ J ∈ 𝒮, S = colSub col J ∧ S ≠ ⊥}, S) ≤ ⨆ J ∈ 𝒮, colSub col J := by
      refine iSup₂_le fun S hS => ?_
      obtain ⟨J, hJ, hSJ, -⟩ := hS
      rw [hSJ]
      exact le_iSup₂_of_le J hJ le_rfl
    have h4 : (⨆ J : 𝒮, colSub col (J : Subgroup W)) =
        Subgroup.toAddSubgroup' (⨆ J : 𝒮, ((J : Subgroup W).map col)) :=
      (OrderIso.map_iSup Subgroup.toAddSubgroup' (fun J : 𝒮 => ((J : Subgroup W).map col))).symm
    have h3 : (⨆ J ∈ 𝒮, colSub col J) = ⊤ := by
      rw [← iSup_subtype'' 𝒮 (fun J : Subgroup W => colSub col J), h4, hmap, OrderIso.map_top]
    rw [le_antisymm h2 h1, h3]
  · rintro S ⟨J, hJ, rfl, hS⟩
    exact colSub_smul_mem hJ hreal col_act
  · rintro S ⟨J, hJ, rfl, hS⟩
    exact fun v hv => colSub_D_mem hJ hreal hD hv
  · rintro S ⟨J, hJ, rfl, hS⟩
    exact colSub_irreducible hJ hirr hreal col_act
  · rintro S ⟨J, hJ, rfl, hS⟩
    exact colSub_card hJ hirr col_act hreal hK hS
  · rintro S ⟨J, hJ, rfl, hS⟩
    exact colSub_faithful hJ hirr hreal col_act hπ₂ hS

theorem exists_multSpace_decomp {W : Type} [CommGroup W] [Finite W] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 2) {L₂ : Subgroup (MulAut W)} {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K) (ψ : ↥L₂ →* GL (Fin m) K)
    (he : ∀ (y : ↥L₂) (w : W), e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    {π₂ : ↥(StatedSL 2 K) →* ↥L₂} (hπ₂ : Function.Surjective π₂) (𝒮 : Set (Subgroup W))
    (hsup : ⨆ J ∈ 𝒮, J = ⊤) (hirr : ∀ J ∈ 𝒮, IsIrrOn L₂ J ⊥)
    (hreal : ∀ J ∈ 𝒮, (FFModel.nat (StatedSL 2 K)).RealizesVia L₂ J ⊥ π₂) :
    ∃ (n : ℕ) (R : Fin n → Submodule K (Fin m → K)), iSupIndep R ∧ iSup R = ⊤ ∧
      (∀ i, Module.finrank K ↥(R i) = 2) ∧
      (∀ i (y : ↥L₂), ∀ v ∈ R i, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R i) ∧
      (∀ i (y : ↥L₂), (∀ v ∈ R i, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → y = 1) := by
  classical
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hK
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four
    (F := K) (by rw [hK]; norm_num)
  obtain ⟨a, ha⟩ := exists_sum_statedSL_two_eq_smul_one (K := K) hω
  obtain ⟨hrel, hcommL⟩ := prodAct_rel_of_iSup (StatedSL 2 K) hπ₂ 𝒮 hsup hreal hω ha
  obtain ⟨col, col_surj, col_act⟩ := exists_colHom (L₂ := L₂) e ψ he
  obtain ⟨D, hD⟩ := exists_col_prodAct (L₂ := L₂) (π₂ := π₂) (a := a) (col := col) col_act
  obtain ⟨hDrel, hDcomm⟩ := col_prodAct_rel (L₂ := L₂) (π₂ := π₂) (a := a) (col := col)
    (ψ := ψ) col_act col_surj hrel hcommL hD
  obtain ⟨𝒮', hsup', hinv, hDS, hirr', hcard, hfaith⟩ :=
    exists_planes (L₂ := L₂) (π₂ := π₂) (a := a) (col := col) (ψ := ψ) (𝒮 := 𝒮)
      col_act col_surj hsup hirr hreal hπ₂ hK hD
  exact exists_iSupIndep_finrank_two_of_iSup (G := ↥L₂) hK ψ D hDrel hDcomm 𝒮'
    hsup' hinv hDS hirr' hcard hfaith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
