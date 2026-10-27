module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesL44
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSymplectic
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowSp64
import CFSG.LieType.Universal.Symplectic
import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec21.TablesSp64

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover (embedSp embedSp_injective)
open CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (ω eω eω_add eω_zero eω_injective eω_ne_zero
  ω_pow_three orderOf_ω zpowers_sq map_top_mulEquiv)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def ext (v : Fin 3 → ZMod 3) : Fin 3 ⊕ Fin 3 → ZMod 3 := Sum.elim v (-v)

@[expose] def dg (x : Fin 3 ⊕ Fin 3 → ZMod 3) : Mat6 := diagonal fun i => eω (x i)

theorem eω_neg (a : ZMod 3) : eω (-a) = (((ω ^ a.val)⁻¹ : F4ˣ) : F4) := by
  have h0 : -a + a = 0 := neg_add_cancel a
  have h1 : eω (-a) * eω a = 1 := by rw [← eω_add, h0, eω_zero]
  have h2 : (((ω ^ a.val)⁻¹ : F4ˣ) : F4) * eω a = 1 := by
    change (((ω ^ a.val)⁻¹ : F4ˣ) : F4) * ((ω ^ a.val : F4ˣ) : F4) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact mul_right_cancel₀ (eω_ne_zero a) (h1.trans h2.symm)

@[expose] def δ : Multiplicative (Fin 3 → ZMod 3) →* Sp :=
  torusHom.comp (CFSG.RankThree.PartTwo.KFacts.KS21.DFT.powVec ω ω_pow_three)

theorem coe_δ (v : Fin 3 → ZMod 3) : mat (δ (Multiplicative.ofAdd v)) = dg (ext v) := by
  rw [mat, δ, MonoidHom.comp_apply, coe_torusHom, dg]
  congr 1
  funext x
  rcases x with i | i
  · rfl
  · change (((ω ^ (v i).val)⁻¹ : F4ˣ) : F4) = eω (-v i)
    rw [eω_neg]

theorem δ_injective : Function.Injective δ :=
  torusHom_injective.comp
    (CFSG.RankThree.PartTwo.KFacts.KS21.DFT.powVec_injective ω_pow_three orderOf_ω)

@[expose] def A0 : Subgroup Sp := δ.range

theorem isElemAbelian_A0 : IsElemAbelian 3 A0 := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    apply Subtype.ext
    change δ v * δ w = δ w * δ v
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, map_one]

theorem card_A0 : Nat.card A0 = 3 ^ 3 := by
  rw [A0, ← Nat.card_congr (MonoidHom.ofInjective δ_injective).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem exists_map_conj_eq_A0 {A' : Subgroup Sp} (hA' : IsElemAbelian 3 A')
    (hcard : Nat.card A' = 3 ^ 3) : ∃ x : Sp, A'.map (MulAut.conj x).toMonoidHom = A0 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_Sp
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  obtain ⟨z, hz⟩ := hfuse A' hA'
  have hT27 : Nat.card T ≤ 3 ^ 3 := maxEA_Sp.1 T hTe
  have hc : ∀ (X : Subgroup Sp) (u : Sp),
      Nat.card (X.map (MulAut.conj u).toMonoidHom) = Nat.card X :=
    fun X u => Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hyT : A0.map (MulAut.conj y).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hy (by rw [hc, card_A0]; exact hT27)
  have hzT : A'.map (MulAut.conj z).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hc, hcard]; exact hT27)
  refine ⟨y⁻¹ * z, ?_⟩
  rw [← map_conj_map_conj, hzT, ← hyT, map_conj_map_conj, inv_mul_cancel]
  ext g
  simp

abbrev Jm : Mat6 := fromBlocks 0 1 (-1) 0

theorem reindexGL_mem {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : Jm.submatrix π π = Jm)
    {g : GL (Fin 3 ⊕ Fin 3) F4} (hg : g ∈ Sp) : reindexGL π g ∈ Sp := by
  rw [mem_statedSp_iff] at hg ⊢
  change ((g : Mat6).submatrix π π)ᵀ * Jm * (g : Mat6).submatrix π π = Jm
  change (g : Mat6)ᵀ * Jm * (g : Mat6) = Jm at hg
  calc ((g : Mat6).submatrix π π)ᵀ * Jm * (g : Mat6).submatrix π π
      = (g : Mat6)ᵀ.submatrix π π * Jm.submatrix π π * (g : Mat6).submatrix π π := by
        rw [transpose_submatrix, hπ]
    _ = ((g : Mat6)ᵀ * Jm * (g : Mat6)).submatrix π π := by
        rw [submatrix_mul_equiv, submatrix_mul_equiv]
    _ = Jm := by rw [hg, hπ]

theorem Jm_symm {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : Jm.submatrix π π = Jm) :
    Jm.submatrix π.symm π.symm = Jm := by
  conv_lhs => rw [← hπ]
  rw [submatrix_submatrix]
  simp

@[expose] def reindexSp (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (hπ : Jm.submatrix π π = Jm) :
    Sp ≃* Sp where
  toFun g := ⟨reindexGL π g, reindexGL_mem hπ g.2⟩
  invFun g := ⟨reindexGL π.symm g, reindexGL_mem (Jm_symm hπ) g.2⟩
  left_inv g := Subtype.ext (Units.ext (by
    change ((mat g).submatrix π π).submatrix π.symm π.symm = mat g
    ext x y
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change ((mat g).submatrix π.symm π.symm).submatrix π π = mat g
    ext x y
    simp))
  map_mul' g h := Subtype.ext (map_mul (reindexGL π) (g : GL (Fin 3 ⊕ Fin 3) F4) h)

theorem mat_reindexSp (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (hπ : Jm.submatrix π π = Jm) (g : Sp) :
    mat (reindexSp π hπ g) = (mat g).submatrix π π := rfl

@[expose] def permE (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3 ⊕ Fin 3) := Equiv.sumCongr σ σ

theorem Jm_permE (σ : Equiv.Perm (Fin 3)) : Jm.submatrix (permE σ) (permE σ) = Jm := by
  ext (x | x) (y | y) <;> simp [permE, Matrix.one_apply, σ.injective.eq_iff]

@[expose] def flipF (s : Fin 3 → Bool) : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3
  | .inl i => if s i then .inr i else .inl i
  | .inr i => if s i then .inl i else .inr i

theorem flipF_flipF (s : Fin 3 → Bool) (x : Fin 3 ⊕ Fin 3) : flipF s (flipF s x) = x := by
  rcases x with i | i <;> by_cases h : s i <;> simp [flipF, h]

@[expose] def flipE (s : Fin 3 → Bool) : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  ⟨flipF s, flipF s, flipF_flipF s, flipF_flipF s⟩

theorem neg_one_F4 : (-1 : F4) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_eq_zero]

theorem Jm_flipE (s : Fin 3 → Bool) : Jm.submatrix (flipE s) (flipE s) = Jm := by
  have hneg : ∀ c : F4, -c = c := fun c => by rw [neg_eq_neg_one_mul, neg_one_F4, one_mul]
  ext (x | x) (y | y) <;> by_cases hx : s x <;> by_cases hy : s y <;>
    simp only [flipE, flipF, hx, hy, Equiv.coe_fn_mk, submatrix_apply, ite_true,
      Bool.false_eq_true, ite_false, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, hneg, Matrix.one_apply] <;>
    by_cases hxy : x = y <;> simp_all

theorem reindexSp_δ {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : Jm.submatrix π π = Jm)
    {v w : Fin 3 → ZMod 3} (h : ext v ∘ π = ext w) :
    reindexSp π hπ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd w) := by
  apply mat_injective
  rw [mat_reindexSp, coe_δ, coe_δ, dg, dg, submatrix_diagonal_equiv, ← h]
  rfl

theorem ext_comp_permE (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → ZMod 3) :
    ext v ∘ permE σ = ext (v ∘ σ) := by
  funext x
  rcases x with i | i <;> rfl

@[expose] def flipVec (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => if s i then -v i else v i

theorem ext_comp_flipE (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) :
    ext v ∘ flipE s = ext (flipVec s v) := by
  funext x
  rcases x with i | i <;> by_cases h : s i
  · simp only [ext, flipE, flipF, flipVec, h, Function.comp_apply, Equiv.coe_fn_mk, ite_true,
      Sum.elim_inr, Sum.elim_inl, Pi.neg_apply]
  · simp only [ext, flipE, flipF, flipVec, h, Function.comp_apply, Equiv.coe_fn_mk,
      Bool.false_eq_true, ite_false, Sum.elim_inl]
  · simp only [ext, flipE, flipF, flipVec, h, Function.comp_apply, Equiv.coe_fn_mk, ite_true,
      Sum.elim_inr, Sum.elim_inl, Pi.neg_apply]
    exact (neg_neg _).symm
  · simp only [ext, flipE, flipF, flipVec, h, Function.comp_apply, Equiv.coe_fn_mk,
      Bool.false_eq_true, ite_false, Sum.elim_inr, Pi.neg_apply]

theorem map_reindexSp_A0 {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : Jm.submatrix π π = Jm)
    (hext : ∀ v, ∃ w, ext v ∘ π = ext w) : A0.map (reindexSp π hπ).toMonoidHom = A0 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := hext (Multiplicative.toAdd v)
    exact ⟨_, (reindexSp_δ hπ hw).symm⟩
  · rw [Subgroup.card_map_of_injective (reindexSp π hπ).injective]

@[expose] def std : Fin 3 → (Fin 3 → ZMod 3) := ![![1, 0, 0], ![1, 1, 0], ![1, 1, 1]]

theorem exists_flip_perm_std : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ σ : Equiv.Perm (Fin 3),
    ∃ s : Fin 3 → Bool, ∃ i : Fin 3, flipVec s (v ∘ σ) = std i := by
  decide

theorem δ_pow_three (v : Fin 3 → ZMod 3) : δ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  rw [← map_pow]
  have : (Multiplicative.ofAdd v) ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  rw [this, map_one]

theorem orderThreeAt_of_std (h : ∀ i : Fin 3,
    OrderThreeAt (⊤ : Subgroup Sp) A0 (Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))))) :
    ∀ B : Subgroup Sp, B ≤ A0 → Nat.card B = 3 → OrderThreeAt (⊤ : Subgroup Sp) A0 B := by
  intro B hBA hB3
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun e => hb' (Subtype.ext e)
  obtain ⟨v, rfl⟩ := hBA hbB
  have hv : Multiplicative.toAdd v ≠ 0 := by
    intro h0
    apply hb1
    have : v = 1 := Multiplicative.toAdd.injective h0
    rw [this, map_one]
  obtain ⟨σ, s, i, hσ⟩ := exists_flip_perm_std _ hv
  have hBb := eq_zpowers_of_card_three hB3 hbB hb1
  set φ := (reindexSp (permE σ) (Jm_permE σ)).trans (reindexSp (flipE s) (Jm_flipE s))
  have hφ : φ (δ v) = δ (Multiplicative.ofAdd (std i)) := by
    change reindexSp (flipE s) (Jm_flipE s) (reindexSp (permE σ) (Jm_permE σ)
      (δ (Multiplicative.ofAdd (Multiplicative.toAdd v)))) = _
    rw [reindexSp_δ _ (ext_comp_permE σ _), reindexSp_δ _ (ext_comp_flipE s _), hσ]
  have hφA : A0.map φ.toMonoidHom = A0 := by
    have e : φ.toMonoidHom = (reindexSp (flipE s) (Jm_flipE s)).toMonoidHom.comp
        (reindexSp (permE σ) (Jm_permE σ)).toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, map_reindexSp_A0 _ (fun v => ⟨_, ext_comp_permE σ v⟩),
      map_reindexSp_A0 _ (fun v => ⟨_, ext_comp_flipE s v⟩)]
  have hmapB : B.map φ.toMonoidHom = Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))) := by
    rw [hBb, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hφ
  have hA : A0.map φ.symm.toMonoidHom = A0 := by
    have h1 := congrArg (Subgroup.map φ.symm.toMonoidHom) hφA
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Sp from by
      ext; simp, Subgroup.map_id, eq_comm] at h1
  have hB : (B.map φ.toMonoidHom).map φ.symm.toMonoidHom = B := by
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Sp from by
      ext; simp, Subgroup.map_id]
  have := (h i).map φ.symm
  rwa [map_top_mulEquiv, hA, ← hmapB, hB] at this

theorem mat_mul_inv (g : Sp) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_mul (g : Sp) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem isBlockDiag_of_mem_centralizer {v : Fin 3 → ZMod 3} {g : Sp}
    (hg : g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp)) :
    IsBlockDiag (ext v) (mat g) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h := congrArg mat hg
  rw [mat_mul, mat_mul, coe_δ, dg] at h
  exact IsBlockDiag.of_comp (t := ext v) eω_injective (isBlockDiag_of_commute h)

theorem mem_centralizer_of_isBlockDiag {v : Fin 3 → ZMod 3} {g : Sp}
    (hg : IsBlockDiag (ext v) (mat g)) :
    g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [mat_mul, mat_mul, coe_δ, dg]
  exact commute_of_isBlockDiag (hg.comp eω)

theorem mem_centralizer_of_constant {v w : Fin 3 → ZMod 3}
    (hw : ∀ i j, ext v i = ext v j → ext w i = ext w j) :
    δ (Multiplicative.ofAdd w) ∈ Subgroup.centralizer
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) : Set Sp) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  apply mat_injective
  rw [mat_mul, mat_mul, coe_δ, dg]
  exact commute_diagonal_of_isBlockDiag (s := fun i => eω (ext w i))
    (fun i j h => by rw [hw i j h]) (isBlockDiag_of_mem_centralizer hg)

theorem isIdOutside_δ {c : Set (Fin 3 ⊕ Fin 3)} {w : Fin 3 → ZMod 3}
    (hw : ∀ i, i ∉ c → ext w i = 0) : IsIdOutside c (mat (δ (Multiplicative.ofAdd w))) := by
  rw [coe_δ, dg]
  exact isIdOutside_diagonal fun i hi => by rw [hw i hi, eω_zero]

theorem layerCent_top_zpowers (b : Sp) :
    layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers b) =
      inSubgroup CFSG.layer (Subgroup.centralizer ({b} : Set Sp)) := by
  rw [layerCent, top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem layerCent_le_centralizer_δ (v : Fin 3 → ZMod 3) :
    layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) := by
  rw [layerCent_top_zpowers]
  exact Subgroup.map_subtype_le _

@[expose] def idOutsideSp (c : Set (Fin 3 ⊕ Fin 3)) : Subgroup Sp where
  carrier := {x | IsIdOutside c (mat x)}
  mul_mem' {x y} hx hy := by
    change IsIdOutside c (mat (x * y))
    rw [mat_mul]
    exact hx.mul hy
  one_mem' := fun _ _ _ => rfl
  inv_mem' {x} hx := hx.of_mul_eq_one (mat_mul_inv x) (mat_inv_mul x)

theorem centralizer_le_normalizer_idOutsideSp {v : Fin 3 → ZMod 3} {c : Set (Fin 3 ⊕ Fin 3)}
    (hc : ∀ i j, ext v i = ext v j → (i ∈ c ↔ j ∈ c)) :
    Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) ≤
      Subgroup.normalizer (idOutsideSp c : Set Sp) := by
  set C := Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp)
  have key : ∀ g ∈ C, ∀ s ∈ idOutsideSp c, g * s * g⁻¹ ∈ idOutsideSp c := by
    intro g hg s hs
    change IsIdOutside c (mat (g * s * g⁻¹))
    rw [mat_mul, mat_mul]
    exact IsIdOutside.conj_of_union hc (isBlockDiag_of_mem_centralizer hg)
      (isBlockDiag_of_mem_centralizer (C.inv_mem hg)) (mat_mul_inv g) hs
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key g hg s, fun h => ?_⟩
  have := key g⁻¹ (C.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem le_layerCent_of_normal {v : Fin 3 → ZMod 3} {S : Subgroup Sp}
    (hSC : S ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp))
    (hCS : Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) ≤
      Subgroup.normalizer (S : Set Sp)) (hq : CFSG.IsQuasisimple S) :
    S ≤ layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) := by
  rw [layerCent_top_zpowers]
  exact le_inSubgroup_layer_of_normal hSC hCS hq

theorem inner_of_witness {v : Fin 3 → ZMod 3} (u : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hu : ∀ w, δ (Multiplicative.ofAdd (u w)) ∈
      layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))))
    (hc : ∀ w i j, ext v i = ext v j → ext (w - u w) i = ext (w - u w) j) :
    ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))),
      y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup Sp)
        (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) : Subgroup Sp) : Set Sp) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨_, hu (Multiplicative.toAdd w), ?_⟩
  have e : (δ (Multiplicative.ofAdd (u (Multiplicative.toAdd w))))⁻¹ * δ w =
      δ (Multiplicative.ofAdd (Multiplicative.toAdd w - u (Multiplicative.toAdd w))) := by
    rw [← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    abel
  rw [e]
  exact Subgroup.centralizer_le (layerCent_le_centralizer_δ v)
    (mem_centralizer_of_constant (hc _))

theorem exists_eq_leviSp {x : Sp} (h12 : (mat x).toBlocks₁₂ = 0) (h21 : (mat x).toBlocks₂₁ = 0) :
    ∃ A : GL (Fin 3) F4, x = leviSp A ∧ (A : Matrix (Fin 3) (Fin 3) F4) = (mat x).toBlocks₁₁ := by
  set X₁ := (mat x).toBlocks₁₁
  set X₂ := (mat x).toBlocks₂₂
  have hX : mat x = fromBlocks X₁ 0 0 X₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (mat x)]
    rw [h12, h21]
  have hsym := mem_statedSp_iff.mp x.2
  change (mat x)ᵀ * Jm * mat x = Jm at hsym
  rw [hX, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hsym
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    transpose_zero, Matrix.mul_neg, Matrix.neg_mul] at hsym
  obtain ⟨-, h1, -, -⟩ := fromBlocks_inj.mp hsym
  have h1' : X₁ * X₂ᵀ = 1 := by
    have := congrArg transpose h1
    rw [transpose_mul, transpose_transpose, transpose_one] at this
    exact mul_eq_one_comm.mp this
  let A : GL (Fin 3) F4 := ⟨X₁, X₂ᵀ, h1', mul_eq_one_comm.mp h1'⟩
  refine ⟨A, mat_injective ?_, rfl⟩
  change mat x = (((leviSp A : Sp) : GL (Fin 3 ⊕ Fin 3) F4) : Mat6)
  rw [coe_leviSp, hX]
  rfl

theorem rho01_injective : Function.Injective (rho (k := F4) (r := 3) 0 1 (by decide)) := by
  intro g h hgh
  have e := congrArg (fun x : Sp => (mat x).toBlocks₁₁) hgh
  simp only [mat, coe_rho', toBlocks_fromBlocks₁₁] at e
  ext i j
  have := congrFun₂ e (if i = 0 then 0 else 1) (if j = 0 then 0 else 1)
  fin_cases i <;> fin_cases j <;> simpa [pairMat] using this

@[expose] def leviSL3 : SpecialLinearGroup (Fin 3) F4 →* Sp :=
  leviSp.comp SpecialLinearGroup.toGL

theorem leviSL3_injective : Function.Injective leviSL3 := by
  intro g h hgh
  have e := congrArg (fun x : Sp => (mat x).toBlocks₁₁) hgh
  simp only [leviSL3, MonoidHom.comp_apply, mat, coe_leviSp, toBlocks_fromBlocks₁₁] at e
  exact Subtype.ext e

abbrev bs (i : Fin 3) : Sp := δ (Multiplicative.ofAdd (std i))

abbrev Bs (i : Fin 3) : Subgroup Sp := Subgroup.zpowers (bs i)

theorem card_zpowers_δ {w : Fin 3 → ZMod 3} (hw : w ≠ 0) :
    Nat.card (Subgroup.zpowers (δ (Multiplicative.ofAdd w))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime (δ_pow_three w) fun h => hw ?_
  have h1 : δ (Multiplicative.ofAdd w) = δ 1 := by rw [h, map_one]
  exact Multiplicative.ofAdd.injective (δ_injective h1)

theorem δ_mem_A0 (w : Fin 3 → ZMod 3) : δ (Multiplicative.ofAdd w) ∈ A0 := ⟨_, rfl⟩

theorem zpowers_δ_le_A0 (w : Fin 3 → ZMod 3) :
    Subgroup.zpowers (δ (Multiplicative.ofAdd w)) ≤ A0 :=
  (Subgroup.zpowers_le).mpr (δ_mem_A0 w)

theorem δ_nsmul (n : ℕ) (w : Fin 3 → ZMod 3) :
    δ (Multiplicative.ofAdd (n • w)) = δ (Multiplicative.ofAdd w) ^ n := by
  rw [ofAdd_nsmul, map_pow]

theorem good_map (φ : Sp ≃* Sp) (hA : A0.map φ.toMonoidHom = A0) {X : Subgroup Sp}
    (h : A0 ≤ layerCent (⊤ : Subgroup Sp) X ⊔ X) :
    A0 ≤ layerCent (⊤ : Subgroup Sp) (X.map φ.toMonoidHom) ⊔ X.map φ.toMonoidHom := by
  rw [← hA, ← map_top_mulEquiv φ, ← map_layerCent, ← Subgroup.map_sup]
  exact Subgroup.map_mono h

theorem le_layerCent_of_iff {v : Fin 3 → ZMod 3} {κ : ZMod 3} {S : Subgroup Sp}
    (hS : ∀ x : Sp, x ∈ S ↔ IsIdOutside {i | ext v i = κ} (mat x))
    (hq : CFSG.IsQuasisimple S) :
    S ≤ layerCent (⊤ : Subgroup Sp) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) := by
  have hSeq : S = idOutsideSp {i | ext v i = κ} := by
    ext x
    exact hS x
  refine le_layerCent_of_normal (fun x hx => mem_centralizer_of_isBlockDiag
    ((hS x).mp hx).isBlockDiag) ?_ hq
  rw [hSeq]
  exact centralizer_le_normalizer_idOutsideSp fun i j e => by
    simp only [Set.mem_ofPred_eq, e]

theorem coordSet_succ : coordSet (Fin.succ : Fin 2 → Fin 3) = {i | ext (std 0) i = 0} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    revert a
    decide
  · intro h
    rcases x with i | i <;> fin_cases i
    · exact absurd h (by decide)
    · exact ⟨Sum.inl 0, rfl⟩
    · exact ⟨Sum.inl 1, rfl⟩
    · exact absurd h (by decide)
    · exact ⟨Sum.inr 0, rfl⟩
    · exact ⟨Sum.inr 1, rfl⟩

abbrev S4 : Subgroup Sp :=
  (embedSp (K := F4) (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)).range

theorem mem_S4_iff (x : Sp) : x ∈ S4 ↔ IsIdOutside {i | ext (std 0) i = 0} (mat x) := by
  rw [← coordSet_succ]
  exact mem_range_embedSp_iff _ x

theorem isQuasisimple_S4 : CFSG.IsQuasisimple S4 :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (embedSp_injective _))
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F4 (by norm_num)
      (Or.inl (Or.inr (by rw [card_F4]))))

theorem S4_le_Y0 : S4 ≤ layerCent (⊤ : Subgroup Sp) (Bs 0) :=
  le_layerCent_of_iff (κ := 0) mem_S4_iff isQuasisimple_S4

theorem decomp_b0 : ∀ w : Fin 3 → ZMod 3, w = ![0, w 1, w 2] + (w 0).val • std 0 := by
  decide

theorem supp_b0 : ∀ w : Fin 3 → ZMod 3, ∀ i : Fin 3 ⊕ Fin 3, ¬(ext (std 0) i = 0) →
    ext ![0, w 1, w 2] i = 0 := by
  decide

theorem good_b0 : A0 ≤ layerCent (⊤ : Subgroup Sp) (Bs 0) ⊔ Bs 0 := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨w, rfl⟩ : ∃ w' : Fin 3 → ZMod 3, Multiplicative.ofAdd w' = w :=
    ⟨Multiplicative.toAdd w, rfl⟩
  rw [decomp_b0 w, ofAdd_add, map_mul, δ_nsmul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (S4_le_Y0 ((mem_S4_iff _).mpr
    (isIdOutside_δ (supp_b0 w))))) (Subgroup.mem_sup_right (Subgroup.pow_mem _
      (Subgroup.mem_zpowers _) _))

theorem inner_b0 : ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup Sp) (Bs 0),
    y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup Sp) (Bs 0) : Subgroup Sp) :
      Set Sp) :=
  inner_of_witness (fun w => ![0, w 1, w 2])
    (fun w => S4_le_Y0 ((mem_S4_iff _).mpr (isIdOutside_δ (supp_b0 w)))) (by decide)

theorem coordSet_two : coordSet (fun _ : Fin 1 => (2 : Fin 3)) = {i | ext (std 1) i = 0} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    revert a
    decide
  · intro h
    rcases x with i | i <;> fin_cases i
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨Sum.inl 0, rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨Sum.inr 0, rfl⟩

theorem two_injective : Function.Injective (fun _ : Fin 1 => (2 : Fin 3)) :=
  fun a b _ => Subsingleton.elim a b

abbrev S2 : Subgroup Sp := (embedSp (K := F4) (fun _ : Fin 1 => (2 : Fin 3)) two_injective).range

theorem mem_S2_iff (x : Sp) : x ∈ S2 ↔ IsIdOutside {i | ext (std 1) i = 0} (mat x) := by
  rw [← coordSet_two]
  exact mem_range_embedSp_iff _ x

theorem isQuasisimple_S2 : CFSG.IsQuasisimple S2 :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (embedSp_injective _))
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 1 F4 le_rfl
      (Or.inl (Or.inr (by rw [card_F4]))))

theorem S2_le_Y1 : S2 ≤ layerCent (⊤ : Subgroup Sp) (Bs 1) :=
  le_layerCent_of_iff (κ := 0) mem_S2_iff isQuasisimple_S2

abbrev C1 : Subgroup Sp := Subgroup.centralizer ({bs 1} : Set Sp)

@[expose] def d2 : C1 →* F4 where
  toFun x := mat x (Sum.inl 0) (Sum.inl 0) * mat x (Sum.inl 1) (Sum.inl 1) -
    mat x (Sum.inl 0) (Sum.inl 1) * mat x (Sum.inl 1) (Sum.inl 0)
  map_one' := by simp [mat]
  map_mul' g h := by
    have hg := isBlockDiag_of_mem_centralizer g.2
    simp only [Subgroup.coe_mul, mat_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three]
    rw [hg (Sum.inl 0) (Sum.inl 2) (by decide), hg (Sum.inl 1) (Sum.inl 2) (by decide),
      hg (Sum.inl 0) (Sum.inr 0) (by decide), hg (Sum.inl 0) (Sum.inr 1) (by decide),
      hg (Sum.inl 0) (Sum.inr 2) (by decide), hg (Sum.inl 1) (Sum.inr 0) (by decide),
      hg (Sum.inl 1) (Sum.inr 1) (by decide), hg (Sum.inl 1) (Sum.inr 2) (by decide)]
    ring

abbrev c01 : Set (Fin 3 ⊕ Fin 3) := {i | ext (std 1) i ≠ 0}

abbrev Levi2 : Subgroup Sp := d2.toHomUnits.ker.map C1.subtype ⊓ idOutsideSp c01

theorem C1_le_normalizer_Levi2 : C1 ≤ Subgroup.normalizer (Levi2 : Set Sp) := by
  refine fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
  · have hle : d2.toHomUnits.ker.map C1.subtype ≤ C1 := Subgroup.map_subtype_le _
    have e : (d2.toHomUnits.ker.map C1.subtype).subgroupOf C1 = d2.toHomUnits.ker := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C1.subtype_injective]
    have : ((d2.toHomUnits.ker.map C1.subtype).subgroupOf C1).Normal := by
      rw [e]
      exact MonoidHom.normal_ker _
    exact Subgroup.le_normalizer_of_normal_subgroupOf hle hg
  · exact centralizer_le_normalizer_idOutsideSp (fun i j e => by
      simp only [Set.mem_ofPred_eq, e]) hg

theorem h01 : (0 : Fin 3) ≠ 1 := by decide

abbrev rho01 : SpecialLinearGroup (Fin 2) F4 →* Sp := rho (k := F4) (r := 3) 0 1 h01

theorem mat_rho01 (g : SpecialLinearGroup (Fin 2) F4) :
    mat (rho01 g) = fromBlocks (pairMat 0 1 (g : Matrix (Fin 2) (Fin 2) F4)) 0 0
      (pairMat 0 1 ((g⁻¹ : SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4)ᵀ) :=
  coe_rho' h01 g

theorem c01_eq : c01 = (Sum.elim id id) ⁻¹' ({0, 1} : Set (Fin 3)) := by
  ext x
  rcases x with i | i <;> fin_cases i <;> simp <;> decide

theorem rho01_mem_Levi2 (g : SpecialLinearGroup (Fin 2) F4) : rho01 g ∈ Levi2 := by
  have hbd : IsBlockDiag (ext (std 1)) (mat (rho01 g)) := by
    intro x y hxy
    rw [mat_rho01]
    rcases x with a | a <;> rcases y with b | b <;> fin_cases a <;> fin_cases b <;>
      first
      | exact absurd (by decide) hxy
      | simp [pairMat]
  have hC : rho01 g ∈ C1 := mem_centralizer_of_isBlockDiag hbd
  refine ⟨⟨⟨rho01 g, hC⟩, ?_, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    change mat (rho01 g) (Sum.inl 0) (Sum.inl 0) * mat (rho01 g) (Sum.inl 1) (Sum.inl 1) -
      mat (rho01 g) (Sum.inl 0) (Sum.inl 1) * mat (rho01 g) (Sum.inl 1) (Sum.inl 0) = 1
    rw [mat_rho01]
    have hg := g.2
    rw [det_fin_two] at hg
    simpa [pairMat] using hg
  · change IsIdOutside c01 (mat (rho01 g))
    rw [c01_eq]
    exact isSupp_rho h01 g

theorem Levi2_eq : Levi2 = rho01.range := by
  apply le_antisymm
  · rintro _ ⟨⟨⟨y, hyC⟩, hy, rfl⟩, hx⟩
    change IsIdOutside c01 (mat y) at hx
    have hbd := isBlockDiag_of_mem_centralizer hyC
    have hd : mat y (Sum.inl 0) (Sum.inl 0) * mat y (Sum.inl 1) (Sum.inl 1) -
        mat y (Sum.inl 0) (Sum.inl 1) * mat y (Sum.inl 1) (Sum.inl 0) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
      simpa [d2] using this
    have h12 : (mat y).toBlocks₁₂ = 0 := by
      ext a b
      rw [toBlocks₁₂, of_apply, Matrix.zero_apply]
      fin_cases a <;> fin_cases b <;>
        first
        | exact hbd _ _ (by decide)
        | (rw [hx _ _ (by decide)]; rfl)
    have h21 : (mat y).toBlocks₂₁ = 0 := by
      ext a b
      rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
      fin_cases a <;> fin_cases b <;>
        first
        | exact hbd _ _ (by decide)
        | (rw [hx _ _ (by decide)]; rfl)
    obtain ⟨A, hyA, hA⟩ := exists_eq_leviSp h12 h21
    set P : SpecialLinearGroup (Fin 2) F4 := ⟨!![mat y (Sum.inl 0) (Sum.inl 0),
      mat y (Sum.inl 0) (Sum.inl 1); mat y (Sum.inl 1) (Sum.inl 0),
      mat y (Sum.inl 1) (Sum.inl 1)], by rw [det_fin_two]; simpa using hd⟩ with hP
    refine ⟨P, ?_⟩
    change rho01 P = y
    rw [hyA]
    change leviSp (pairGL h01 P) = leviSp A
    congr 1
    apply Units.ext
    rw [coe_pairGL, hA]
    ext a b
    rw [toBlocks₁₁, of_apply]
    fin_cases a <;> fin_cases b <;>
      first
      | (rw [hx _ _ (by decide)]; simp [pairMat])
      | (simp [pairMat, hP])
  · rintro _ ⟨g, rfl⟩
    exact rho01_mem_Levi2 g

theorem isQuasisimple_Levi2 : CFSG.IsQuasisimple Levi2 := by
  rw [Levi2_eq]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective rho01_injective)
    CFSG.RankThree.PartTwo.Sec21.TablesL44.isQuasisimple_SL2

theorem Levi2_le_Y1 : Levi2 ≤ layerCent (⊤ : Subgroup Sp) (Bs 1) :=
  le_layerCent_of_normal (inf_le_left.trans (Subgroup.map_subtype_le _)) C1_le_normalizer_Levi2
    isQuasisimple_Levi2

theorem supp_Levi2 : ∀ a : ZMod 3, ∀ i : Fin 3 ⊕ Fin 3, i ∉ c01 → ext ![a, -a, 0] i = 0 := by
  decide

theorem supp_S2 : ∀ a : ZMod 3, ∀ i : Fin 3 ⊕ Fin 3, i ∉ {i | ext (std 1) i = 0} →
    ext ![0, 0, a] i = 0 := by
  decide

theorem δ_mem_centralizer (v w : Fin 3 → ZMod 3) :
    δ (Multiplicative.ofAdd w) ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul δ, ← map_mul δ, mul_comm]

theorem δ_mem_Levi2 (a : ZMod 3) : δ (Multiplicative.ofAdd ![a, -a, 0]) ∈ Levi2 := by
  refine ⟨⟨⟨_, δ_mem_centralizer _ _⟩, ?_, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    change mat (δ (Multiplicative.ofAdd ![a, -a, 0])) (Sum.inl 0) (Sum.inl 0) *
        mat (δ (Multiplicative.ofAdd ![a, -a, 0])) (Sum.inl 1) (Sum.inl 1) -
      mat (δ (Multiplicative.ofAdd ![a, -a, 0])) (Sum.inl 0) (Sum.inl 1) *
        mat (δ (Multiplicative.ofAdd ![a, -a, 0])) (Sum.inl 1) (Sum.inl 0) = 1
    rw [coe_δ, dg, diagonal_apply_eq, diagonal_apply_eq, diagonal_apply_ne _ (by decide),
      diagonal_apply_ne _ (by decide), mul_zero, sub_zero]
    change eω a * eω (-a) = 1
    have h0 : a + -a = 0 := add_neg_cancel a
    rw [← eω_add, h0, eω_zero]
  · exact isIdOutside_δ (supp_Levi2 a)

theorem δ_mem_S2 (a : ZMod 3) : δ (Multiplicative.ofAdd ![0, 0, a]) ∈ S2 := by
  rw [mem_S2_iff]
  exact isIdOutside_δ (supp_S2 a)

theorem inner_b1 : ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup Sp) (Bs 1),
    y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup Sp) (Bs 1) : Subgroup Sp) :
      Set Sp) := by
  refine inner_of_witness (fun w => ![2 * (w 0 - w 1), -(2 * (w 0 - w 1)), 0] + ![0, 0, w 2])
    (fun w => ?_) (by decide)
  rw [ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (Levi2_le_Y1 (δ_mem_Levi2 _)) (S2_le_Y1 (δ_mem_S2 _))

theorem decomp_b1 : ∀ w : Fin 3 → ZMod 3,
    w = ![w 0 - 2 * (w 0 + w 1), -(w 0 - 2 * (w 0 + w 1)), 0] + ![0, 0, w 2] +
      (2 * (w 0 + w 1)).val • std 1 := by
  decide

theorem good_b1 : A0 ≤ layerCent (⊤ : Subgroup Sp) (Bs 1) ⊔ Bs 1 := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨w, rfl⟩ : ∃ w' : Fin 3 → ZMod 3, Multiplicative.ofAdd w' = w :=
    ⟨Multiplicative.toAdd w, rfl⟩
  rw [decomp_b1 w, ofAdd_add, ofAdd_add, map_mul, map_mul, δ_nsmul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Levi2_le_Y1
    (δ_mem_Levi2 _))) (Subgroup.mem_sup_left (S2_le_Y1 (δ_mem_S2 _))))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))

abbrev C3 : Subgroup Sp := Subgroup.centralizer ({bs 2} : Set Sp)

theorem toBlocks₁₂_eq_zero {x : Sp} (hx : x ∈ C3) : (mat x).toBlocks₁₂ = 0 := by
  have hbd := isBlockDiag_of_mem_centralizer hx
  ext a b
  rw [toBlocks₁₂, of_apply, Matrix.zero_apply]
  exact hbd _ _ (by revert a b; decide)

theorem toBlocks₂₁_eq_zero {x : Sp} (hx : x ∈ C3) : (mat x).toBlocks₂₁ = 0 := by
  have hbd := isBlockDiag_of_mem_centralizer hx
  ext a b
  rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
  exact hbd _ _ (by revert a b; decide)

@[expose] def d3 : C3 →* F4 where
  toFun x := (mat x).toBlocks₁₁.det
  map_one' := by
    change ((1 : Mat6)).toBlocks₁₁.det = 1
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁, det_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, mat_mul]
    have e : (mat g * mat h).toBlocks₁₁ = (mat g).toBlocks₁₁ * (mat h).toBlocks₁₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks (mat g), ← fromBlocks_toBlocks (mat h)]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks₁₂_eq_zero g.2, Matrix.zero_mul,
        add_zero]
    rw [e, det_mul]

theorem range_leviSL3_eq : leviSL3.range = d3.toHomUnits.ker.map C3.subtype := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    have hbd : IsBlockDiag (ext (std 2)) (mat (leviSL3 A)) := by
      intro x y hxy
      change (((leviSp (SpecialLinearGroup.toGL A) : Sp) : GL (Fin 3 ⊕ Fin 3) F4) : Mat6) x y = 0
      rw [coe_leviSp]
      rcases x with a | a <;> rcases y with b | b
      · exact absurd (by revert a b; decide) hxy
      · rfl
      · rfl
      · exact absurd (by revert a b; decide) hxy
    refine ⟨⟨leviSL3 A, mem_centralizer_of_isBlockDiag hbd⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    change (mat (leviSL3 A)).toBlocks₁₁.det = 1
    change ((((leviSp (SpecialLinearGroup.toGL A) : Sp) : GL (Fin 3 ⊕ Fin 3) F4) :
      Mat6)).toBlocks₁₁.det = 1
    rw [coe_leviSp, toBlocks_fromBlocks₁₁]
    exact A.2
  · rintro _ ⟨⟨x, hxC⟩, hx, rfl⟩
    have hd : (mat x).toBlocks₁₁.det = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      simpa [d3] using this
    obtain ⟨A, hxA, hA⟩ := exists_eq_leviSp (toBlocks₁₂_eq_zero hxC) (toBlocks₂₁_eq_zero hxC)
    have hAd : (A : Matrix (Fin 3) (Fin 3) F4).det = 1 := by rw [hA]; exact hd
    refine ⟨(⟨(A : Matrix (Fin 3) (Fin 3) F4), hAd⟩ : SpecialLinearGroup (Fin 3) F4), ?_⟩
    change leviSL3 _ = x
    rw [hxA]
    change leviSp _ = leviSp A
    congr 1
    exact Units.ext rfl

theorem isQuasisimple_S3 : CFSG.IsQuasisimple leviSL3.range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective leviSL3_injective)
    CFSG.RankThree.PartTwo.Sec21.TablesL44.isQuasisimple_SL3

theorem S3_le_Y2 : leviSL3.range ≤ layerCent (⊤ : Subgroup Sp) (Bs 2) := by
  refine le_layerCent_of_normal ?_ ?_ isQuasisimple_S3
  · rw [range_leviSL3_eq]
    exact Subgroup.map_subtype_le _
  · rw [range_leviSL3_eq]
    have hle : d3.toHomUnits.ker.map C3.subtype ≤ C3 := Subgroup.map_subtype_le _
    have e : (d3.toHomUnits.ker.map C3.subtype).subgroupOf C3 = d3.toHomUnits.ker := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C3.subtype_injective]
    have : ((d3.toHomUnits.ker.map C3.subtype).subgroupOf C3).Normal := by
      rw [e]
      exact MonoidHom.normal_ker _
    exact fun g hg => Subgroup.le_normalizer_of_normal_subgroupOf hle hg

theorem Y2_le_S3 : layerCent (⊤ : Subgroup Sp) (Bs 2) ≤ leviSL3.range := by
  rw [layerCent_top_zpowers, range_leviSL3_eq]
  refine inSubgroup_layer_le_of_commutator_le ?_
  have e : (commutator C3).map C3.subtype = ⁅C3, C3⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← e]
  exact Subgroup.map_mono (Abelianization.commutator_subset_ker _)

theorem Y2_eq : layerCent (⊤ : Subgroup Sp) (Bs 2) = leviSL3.range :=
  le_antisymm Y2_le_S3 S3_le_Y2

abbrev X' : Subgroup Sp := Subgroup.zpowers (δ (Multiplicative.ofAdd ![1, 2, 0]))

theorem X'_eq : X' = (Bs 1).map
    (reindexSp (flipE ![false, true, false]) (Jm_flipE _)).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  change _ = Subgroup.zpowers (reindexSp (flipE ![false, true, false]) (Jm_flipE _) (bs 1))
  rw [reindexSp_δ _ (ext_comp_flipE _ _),
    show flipVec ![false, true, false] (std 1) = ![1, 2, 0] from by decide]

theorem good_X' : A0 ≤ layerCent (⊤ : Subgroup Sp) X' ⊔ X' := by
  rw [X'_eq]
  exact good_map _ (map_reindexSp_A0 _ (fun v => ⟨_, ext_comp_flipE _ v⟩)) good_b1

theorem X'_le_Y2 : X' ≤ layerCent (⊤ : Subgroup Sp) (Bs 2) ⊔ Bs 2 := by
  refine le_sup_of_le_left ((Subgroup.zpowers_le).mpr (S3_le_Y2 ?_))
  rw [range_leviSL3_eq]
  refine ⟨⟨_, δ_mem_centralizer _ _⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  change (mat (δ (Multiplicative.ofAdd ![1, 2, 0]))).toBlocks₁₁.det = 1
  rw [coe_δ, dg, toBlocks₁₁]
  have e : (of fun i j => (diagonal fun x => eω (ext ![1, 2, 0] x) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) (Sum.inl i) (Sum.inl j)) =
      diagonal fun i => eω (![1, 2, 0] i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [ext]
    · simp [h]
  rw [e, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [← eω_add, ← eω_add, show (1 : ZMod 3) + 2 + 0 = 0 from by decide, eω_zero]

theorem orderThreeAt_std (i : Fin 3) : OrderThreeAt (⊤ : Subgroup Sp) A0 (Bs i) := by
  fin_cases i
  · exact ⟨Or.inl inner_b0, Bs 0, Bs 0, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      le_sup_right, zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right, good_b0⟩
  · exact ⟨Or.inl inner_b1, Bs 1, Bs 1, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      le_sup_right, zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right, good_b1⟩
  · refine ⟨Or.inr ⟨(MulEquiv.subgroupCongr Y2_eq).trans
      (MonoidHom.ofInjective leviSL3_injective).symm⟩, Bs 2, X', zpowers_δ_le_A0 _,
      card_zpowers_δ (by decide), le_sup_right, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      X'_le_Y2, good_X'⟩

theorem orderThreeAt_A0 : ∀ B : Subgroup Sp, B ≤ A0 → Nat.card B = 3 →
    OrderThreeAt (⊤ : Subgroup Sp) A0 B :=
  orderThreeAt_of_std orderThreeAt_std

theorem terminalOrderThreeSp64 : TerminalOrderThreeSp64 := by
  intro G _ _ I A hAI hAe ⟨e⟩ hA B hBA hB3
  apply OrderThreeAt.of_subgroupOf hAI hBA
  set e' : I ≃* Sp := e.trans equivSp
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  set φ : I ≃* Sp := e'.trans (MulAut.conj x)
  have hφA : (A.subgroupOf I).map φ.toMonoidHom = A0 := by
    rw [← hx, Subgroup.map_map]
    rfl
  have hB' : (B.subgroupOf I).map φ.toMonoidHom ≤ A0 := by
    rw [← hφA]
    exact Subgroup.map_mono (fun x hx => hBA hx)
  have hcardB : Nat.card ((B.subgroupOf I).map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.trans hAI)).toEquiv, hB3]
  have h := (orderThreeAt_A0 _ hB' hcardB).map φ.symm
  have hsymm : ∀ X : Subgroup I, (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id I from by
      ext; simp, Subgroup.map_id]
  rwa [← hφA, hsymm, hsymm, show (⊤ : Subgroup Sp).map φ.symm.toMonoidHom = ⊤ from by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr φ.symm.surjective] at h

end CFSG.RankThree.PartTwo.Sec21.TablesSp64
