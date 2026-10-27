module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSp64
public import CFSG.RankThree.PartOne.KFCL.SpPerm
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.Foundations
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourCore
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (eω eω_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartOne.KFCL.Sp
open CFSG.ClassicalInvolution.Models.SymplecticPairs (par par_inl par_inr)
open scoped Matrix

private theorem ext_par (v : Fin 3 → ZMod 3) (a : Fin 3 ⊕ Fin 3) :
    ext v (par a) = -ext v a := by
  rcases a with i | i
  · rfl
  · show v i = - -v i
    exact (neg_neg (v i)).symm

private theorem exists_ext_comp_of_mem_Hp {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3)
    (v : Fin 3 → ZMod 3) : ∃ w, ext v ∘ τ = ext w := by
  refine ⟨fun i => ext v (τ (Sum.inl i)), ?_⟩
  funext a
  rcases a with i | i
  · rfl
  · change ext v (τ (Sum.inr i)) = - ext v (τ (Sum.inl i))
    have h := hτ (Sum.inl i)
    calc ext v (τ (Sum.inr i)) = ext v (τ (par (Sum.inl i))) := by rw [par_inl]
      _ = ext v (par (τ (Sum.inl i))) := by rw [h]
      _ = - ext v (τ (Sum.inl i)) := ext_par v _

private theorem mat_cj_eq_submatrix {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (x : Sp) :
    mat (cj hτ x) = (mat x).submatrix τ τ := by
  ext a b
  change (CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 F4) (cj hτ x) a b =
    (mat x).submatrix τ τ a b
  rw [mat_cj_apply (K := F4) (n := 3), Matrix.submatrix_apply]
  rfl

private theorem cj_δ {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (v : Fin 3 → ZMod 3) :
    ∃ w, cj hτ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd w) := by
  obtain ⟨w, hw⟩ := exists_ext_comp_of_mem_Hp hτ v
  refine ⟨w, ?_⟩
  apply mat_injective
  rw [mat_cj_eq_submatrix hτ, coe_δ, dg, Matrix.submatrix_diagonal_equiv, coe_δ, dg, ← hw]
  rfl

private theorem conj_permSp_eq_cj_inv {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (x : Sp) :
    permSp τ hτ * x * (permSp τ hτ)⁻¹ = cj ((Hp 3).inv_mem hτ) x := by
  rw [cj, ← permSp_inv hτ, inv_inv]

private theorem conj_permSp_mem_A0 {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) {x : Sp}
    (hx : x ∈ A0) : permSp τ hτ * x * (permSp τ hτ)⁻¹ ∈ A0 := by
  change x ∈ δ.range at hx
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [conj_permSp_eq_cj_inv hτ]
  obtain ⟨w, hw⟩ := cj_δ ((Hp 3).inv_mem hτ) (Multiplicative.toAdd v)
  refine ⟨Multiplicative.ofAdd w, ?_⟩
  rw [← hw, ofAdd_toAdd]

private theorem permSp_mem_normalizer_A0 {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    permSp τ hτ ∈ Subgroup.normalizer (A0 : Set Sp) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_permSp_mem_A0 hτ
  · intro hx
    have h := conj_permSp_mem_A0 ((Hp 3).inv_mem hτ) hx
    convert h using 1
    rw [← permSp_inv hτ]
    group

private theorem ext_single_eq_one_iff (i : Fin 3) (b : Fin 3 ⊕ Fin 3) :
    ext (Pi.single i (1 : ZMod 3)) b = 1 ↔ b = Sum.inl i := by
  rcases b with m | m <;> fin_cases i <;> fin_cases m <;> decide

private theorem ext_single_eq_neg_one_iff (i : Fin 3) (b : Fin 3 ⊕ Fin 3) :
    ext (Pi.single i (1 : ZMod 3)) b = -1 ↔ b = Sum.inr i := by
  rcases b with m | m <;> fin_cases i <;> fin_cases m <;> decide

private theorem mem_centralizer_permSp_eq_one {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3)
    (hcent : permSp (K := F4) τ hτ ∈ Subgroup.centralizer (A0 : Set Sp)) :
    permSp (K := F4) τ hτ = 1 := by
  have hfix : ∀ v : Fin 3 → ZMod 3, ext v ∘ τ = ext v := by
    intro v
    have h1 : cj hτ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd v) := by
      rw [cj]
      have hc := (Subgroup.mem_centralizer_iff.mp hcent) (δ (Multiplicative.ofAdd v)) (by
        exact ⟨Multiplicative.ofAdd v, rfl⟩)
      calc (permSp τ hτ)⁻¹ * δ (Multiplicative.ofAdd v) * permSp τ hτ
          = (permSp τ hτ)⁻¹ * (δ (Multiplicative.ofAdd v) * permSp τ hτ) := by rw [mul_assoc]
        _ = (permSp τ hτ)⁻¹ * (permSp τ hτ * δ (Multiplicative.ofAdd v)) := by rw [hc]
        _ = δ (Multiplicative.ofAdd v) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : (mat (δ (Multiplicative.ofAdd v))).submatrix τ τ =
        mat (δ (Multiplicative.ofAdd v)) := by
      rw [← mat_cj_eq_submatrix hτ (δ (Multiplicative.ofAdd v)), h1]
    funext a
    have h3 := congrFun₂ h2 a a
    simp only [Matrix.submatrix_apply, coe_δ, dg, Matrix.diagonal_apply_eq] at h3
    simpa only [Function.comp_apply] using eω_injective h3
  have hτ1 : τ = 1 := by
    ext a
    rcases a with i | i
    · have h := congrFun (hfix (Pi.single i (1 : ZMod 3))) (Sum.inl i)
      simp only [Function.comp_apply] at h
      have h' : ext (Pi.single i (1 : ZMod 3)) (Sum.inl i) = 1 := by
        simp [ext, Pi.single]
      rw [h'] at h
      exact (ext_single_eq_one_iff i (τ (Sum.inl i))).mp h
    · have h := congrFun (hfix (Pi.single i (1 : ZMod 3))) (Sum.inr i)
      simp only [Function.comp_apply] at h
      have h' : ext (Pi.single i (1 : ZMod 3)) (Sum.inr i) = -1 := by
        simp [ext, Pi.single]
      rw [h'] at h
      exact (ext_single_eq_neg_one_iff i (τ (Sum.inr i))).mp h
  cases hτ1
  exact permSp_one

private theorem permMatrix_injective :
    Function.Injective (fun ρ : Equiv.Perm (Fin 3 ⊕ Fin 3) => ρ.permMatrix F4) := by
  intro ρ ρ' hp
  beta_reduce at hp
  have hx : ∀ b, ρ' (ρ.symm b) = b := by
    intro b
    have hvec : ρ.permMatrix F4 *ᵥ (Pi.single b (1 : F4) : Fin 3 ⊕ Fin 3 → F4) =
        ρ'.permMatrix F4 *ᵥ (Pi.single b (1 : F4) : Fin 3 ⊕ Fin 3 → F4) := by rw [hp]
    rw [Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec] at hvec
    have h1 : (Pi.single b (1 : F4) : Fin 3 ⊕ Fin 3 → F4) (ρ' (ρ.symm b)) = 1 := by
      have := congrFun hvec (ρ.symm b)
      simpa [Function.comp_apply] using this.symm
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h1
    exact zero_ne_one h1
  ext a
  have h := hx (ρ a)
  simp only [Equiv.symm_apply_apply] at h
  exact h.symm

private theorem permMatrixHom_injective :
    Function.Injective (Matrix.permMatrixHom (n := Fin 3 ⊕ Fin 3) (R := F4)) := by
  intro σ τ h
  have h' : Equiv.Perm.permMatrix F4 σ⁻¹ = Equiv.Perm.permMatrix F4 τ⁻¹ := by
    rw [← Matrix.permMatrixHom_apply, ← Matrix.permMatrixHom_apply]
    exact h
  exact inv_injective (permMatrix_injective h')

private theorem permSpHom_injective : Function.Injective (permSpHom 3 F4) := by
  rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
  have hmat : Matrix.permMatrixHom (n := Fin 3 ⊕ Fin 3) (R := F4) τ =
      Matrix.permMatrixHom (n := Fin 3 ⊕ Fin 3) (R := F4) τ' := by
    have h1 := congrArg mat h
    change (CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 F4) (permSp τ hτ) =
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 F4) (permSp τ' hτ') at h1
    rw [mat_permSp, mat_permSp] at h1
    exact h1
  exact Subtype.ext (permMatrixHom_injective hmat)

private theorem permE_mem_Hp (σ : Equiv.Perm (Fin 3)) : permE σ ∈ Hp 3 := by
  rw [mem_Hp]
  intro a
  rcases a with i | i <;> rfl

private theorem flipE_mem_Hp (s : Fin 3 → Bool) : flipE s ∈ Hp 3 := by
  rw [mem_Hp]
  intro a
  rcases a with i | i <;> by_cases h : s i <;> simp [flipE, flipF, h, par]

private theorem sum_ite_inj {b b' : Bool} {j j' : Fin 3}
    (h : (if b then Sum.inr j else Sum.inl j) = (if b' then Sum.inr j' else Sum.inl j')) :
    j = j' ∧ b = b' := by
  cases b <;> cases b' <;> simp_all

private theorem card_le_Hp_three : 48 ≤ Nat.card ↥(Hp 3) := by
  let f : Equiv.Perm (Fin 3) × (Fin 3 → Bool) → ↥(Hp 3) := fun x =>
    ⟨flipE x.2 * permE x.1, (Hp 3).mul_mem (flipE_mem_Hp x.2) (permE_mem_Hp x.1)⟩
  have hinj : Function.Injective f := by
    rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
    have h' : flipE s * permE σ = flipE s' * permE σ' := congrArg Subtype.val h
    have hinl : ∀ i : Fin 3,
        (if s (σ i) then Sum.inr (σ i) else Sum.inl (σ i)) =
        (if s' (σ' i) then Sum.inr (σ' i) else Sum.inl (σ' i)) := by
      intro i
      have := congrArg (fun τ : Equiv.Perm (Fin 3 ⊕ Fin 3) => τ (Sum.inl i)) h'
      simpa [Equiv.Perm.mul_apply, flipE, flipF, permE, Equiv.sumCongr_apply] using this
    have hσ : σ = σ' := Equiv.Perm.ext (fun i => (sum_ite_inj (hinl i)).1)
    have hs : s = s' := by
      funext j
      obtain ⟨i, rfl⟩ := σ.surjective j
      have := (sum_ite_inj (hinl i)).2
      simpa [hσ] using this
    exact Prod.ext hσ hs
  haveI : Fintype ↥(Hp 3) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at h
  norm_num at h
  rwa [Nat.card_eq_fintype_card]

private theorem card_le_spWeyl : 48 ≤ Nat.card (spWeyl 3 F4) := by
  have h := card_le_Hp_three
  have he : Nat.card ↥(Hp 3) = Nat.card (spWeyl 3 F4) :=
    Nat.card_congr (MonoidHom.ofInjective permSpHom_injective).toEquiv
  rwa [he] at h

private theorem exists_weyl_A0 :
    ∃ W₀ : Subgroup Sp, W₀ ≤ Subgroup.normalizer (A0 : Set Sp) ∧
      (∀ w ∈ W₀, w ∈ Subgroup.centralizer (A0 : Set Sp) → w = 1) ∧
      48 ≤ Nat.card W₀ := by
  refine ⟨spWeyl 3 F4, ?_, ?_, card_le_spWeyl⟩
  · intro w hw
    rw [mem_spWeyl_iff] at hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    exact permSp_mem_normalizer_A0 hτ
  · intro w hw hcent
    rw [mem_spWeyl_iff] at hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    exact mem_centralizer_permSp_eq_one hτ hcent

private theorem map_mem_normalizer {G : Type} [Group G] (φ : G ≃* G) {A : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    φ w ∈ Subgroup.normalizer ((A.map φ.toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hw ⊢
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨w * a * w⁻¹, (hw a).mp ha, ?_⟩
    simp
  · rintro ⟨a, ha, haeq⟩
    refine ⟨w⁻¹ * a * w, (hw (w⁻¹ * a * w)).mpr ?_, ?_⟩
    · rw [show w * (w⁻¹ * a * w) * w⁻¹ = a by group]; exact ha
    · change φ (w⁻¹ * a * w) = y
      change φ a = φ w * y * (φ w)⁻¹ at haeq
      have h1 : φ (w⁻¹ * a * w) = (φ w)⁻¹ * φ a * φ w := by simp
      rw [h1, haeq]
      group

private theorem card_eq_three_cube_of_selfCentralizing {E : Subgroup Sp}
    (hE : IsElemAbelian 3 E)
    (hself : ∀ g : Sp, g ∈ Subgroup.centralizer (E : Set Sp) → g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 3 ^ 3 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_Sp
  have hT27 : Nat.card T ≤ 3 ^ 3 := maxEA_Sp.1 T hTe
  obtain ⟨z, hz⟩ := hfuse E hE
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  have hc : ∀ (X : Subgroup Sp) (u : Sp),
      Nat.card (X.map (MulAut.conj u).toMonoidHom) = Nat.card X :=
    fun X u => Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hselfz : ∀ g : Sp,
      g ∈ Subgroup.centralizer ((E.map (MulAut.conj z).toMonoidHom : Subgroup Sp) : Set Sp) →
      g ^ 3 = 1 → g ∈ E.map (MulAut.conj z).toMonoidHom := by
    intro g hg hg3
    refine ⟨z⁻¹ * g * z, ?_, ?_⟩
    · refine hself (z⁻¹ * g * z) ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        have hge : z * e * z⁻¹ ∈ E.map (MulAut.conj z).toMonoidHom := ⟨e, he, rfl⟩
        have hcomm := (Subgroup.mem_centralizer_iff.mp hg) (z * e * z⁻¹) hge
        calc e * (z⁻¹ * g * z) = z⁻¹ * ((z * e * z⁻¹) * g) * z := by group
          _ = z⁻¹ * (g * (z * e * z⁻¹)) * z := by rw [hcomm]
          _ = (z⁻¹ * g * z) * e := by group
      · calc (z⁻¹ * g * z) ^ 3 = ((MulAut.conj z⁻¹) g) ^ 3 := by
              rw [MulAut.conj_apply, inv_inv]
          _ = (MulAut.conj z⁻¹) (g ^ 3) := (map_pow (MulAut.conj z⁻¹) g 3).symm
          _ = z⁻¹ * g ^ 3 * z := by rw [MulAut.conj_apply, inv_inv]
          _ = 1 := by rw [hg3]; group
    · show z * (z⁻¹ * g * z) * z⁻¹ = g
      group
  have hTle : T ≤ E.map (MulAut.conj z).toMonoidHom := by
    intro t ht
    exact hselfz t (by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (hTe.1.is_comm.comm ⟨e, hz he⟩ ⟨t, ht⟩)) (hTe.2 t ht)
  have hET : E.map (MulAut.conj z).toMonoidHom = T := le_antisymm hz hTle
  have hge : 3 ^ 3 ≤ Nat.card T := by
    have h1 := Subgroup.card_le_of_le hy
    rw [hc A0 y, card_A0] at h1
    exact h1
  have hcardT : Nat.card T = 3 ^ 3 := le_antisymm hT27 hge
  rw [← hc E z, hET, hcardT]

theorem ggB48_sp_six_four_weyl (E : Subgroup ↥(StatedSp 3 (GaloisField 2 2)))
    (hE : IsElemAbelian 3 E)
    (hself : ∀ g : ↥(StatedSp 3 (GaloisField 2 2)), g ∈ Subgroup.centralizer (E : Set _) →
      g ^ 3 = 1 → g ∈ E) :
    ∃ W : Subgroup ↥(StatedSp 3 (GaloisField 2 2)), W ≤ Subgroup.normalizer (E : Set _) ∧
      (∀ w ∈ W, w ∈ Subgroup.centralizer (E : Set _) → w = 1) ∧ 48 ≤ Nat.card W := by
  have hcardE : Nat.card E = 3 ^ 3 := card_eq_three_cube_of_selfCentralizing hE hself
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hE hcardE
  obtain ⟨W₀, hW₀norm, hW₀disj, hW₀card⟩ := exists_weyl_A0
  have hEeq : (A0.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup Sp) = E := by
    refine Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective ?_
    rw [Subgroup.map_map, hx]
    have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
        MonoidHom.id Sp :=
      MonoidHom.ext (fun g => by
        change (MulAut.conj x) ((MulAut.conj x⁻¹) g) = g
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group)
    rw [hcomp, Subgroup.map_id]
  refine ⟨W₀.map (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← hEeq]
    intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    exact map_mem_normalizer (MulAut.conj x⁻¹) (hW₀norm hw₀)
  · rw [← hEeq]
    rintro w ⟨w₀, hw₀, rfl⟩ hcent
    have hw₀cent : w₀ ∈ Subgroup.centralizer (A0 : Set Sp) := by
      rw [Subgroup.mem_centralizer_iff] at hcent ⊢
      intro a ha
      have hE' : (MulAut.conj x⁻¹) a ∈ (A0.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup Sp) :=
        ⟨a, ha, rfl⟩
      have h := hcent ((MulAut.conj x⁻¹) a) hE'
      exact (MulAut.conj x⁻¹).injective (by simpa [map_mul] using h)
    rw [hW₀disj w₀ hw₀ hw₀cent, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hW₀card

end CFSG.StandardType

end
