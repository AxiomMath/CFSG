module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux5
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrame
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G}

private theorem sylow_conj_of_card_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X P₁ P₂ : Subgroup G} (hP₁ : P₁ ≤ X) (hP₂ : P₂ ≤ X)
    (hP₁g : IsPGroup p P₁) (hP₂g : IsPGroup p P₂) (hcard : Nat.card P₁ = Nat.card P₂)
    (hindex : ¬ p ∣ (P₁.subgroupOf X).index) :
    ∃ z ∈ X, P₂.map (MulAut.conj z).toMonoidHom = P₁ := by
  have h₁ : IsPGroup p (P₁.subgroupOf X) := hP₁g.comap_subtype
  have h₂ : IsPGroup p (P₂.subgroupOf X) := hP₂g.comap_subtype
  have hc₁ : Nat.card (P₁.subgroupOf X) = Nat.card P₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁).toEquiv
  have hc₂ : Nat.card (P₂.subgroupOf X) = Nat.card P₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₂).toEquiv
  have hindex₂ : ¬ p ∣ (P₂.subgroupOf X).index := by
    have e₁ := (P₁.subgroupOf X).card_mul_index
    have e₂ := (P₂.subgroupOf X).card_mul_index
    rw [hc₁, hcard] at e₁
    rw [hc₂] at e₂
    have hpos : 0 < Nat.card P₂ := Nat.card_pos
    have : (P₂.subgroupOf X).index = (P₁.subgroupOf X).index :=
      Nat.eq_of_mul_eq_mul_left hpos (e₂.trans e₁.symm)
    rwa [this]
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq X (h₂.toSylow hindex₂) (h₁.toSylow hindex)
  refine ⟨z, z.2, ?_⟩
  have hz' : MulAut.conj z • P₂.subgroupOf X = P₁.subgroupOf X := by
    have := congrArg (fun S : Sylow p X => (S : Subgroup X)) hz
    simpa [Sylow.coe_subgroup_smul] using this
  have hle : P₂.map (MulAut.conj (z : G)).toMonoidHom ≤ P₁ := by
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MulAut.conj z • (⟨g, hP₂ hg⟩ : X) ∈ MulAut.conj z • P₂.subgroupOf X :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (by simpa [Subgroup.mem_subgroupOf] using hg)
    rw [hz', Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.conj_apply] using hmem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective P₂ _ (MulAut.conj (z : G)).injective).toEquiv).le

@[expose] noncomputable def e6QTwoSixNormAction
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    ↥(Subgroup.normalizer (L : Set G)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  (MulAut.congr θ).toMonoidHom.comp
    ((e6QTwoQuotCenterAutHom L).comp (Subgroup.normalizerMonoidHom L))

theorem e6QTwoSixNormAction_apply
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (g : ↥(Subgroup.normalizer (L : Set G))) :
    e6QTwoSixNormAction θ g =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L
        (Subgroup.normalizerMonoidHom L g)) := rfl

private theorem e6QTwoSixNormAction_mk
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (g : ↥(Subgroup.normalizer (L : Set G))) (l : L) :
    e6QTwoSixNormAction θ g (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L)
        (Subgroup.normalizerMonoidHom L g l)) := by
  rw [e6QTwoSixNormAction_apply, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk]

theorem e6QTwoSixNormAction_of_mem_L
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (g : ↥L) :
    e6QTwoSixNormAction θ ⟨g, Subgroup.le_normalizer g.2⟩ =
      e6QTwoSixConjOnQuot θ g := by
  ext q
  obtain ⟨q', rfl⟩ := θ.surjective q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q'
  rw [e6QTwoSixNormAction_mk, e6QTwoSixConjOnQuot_mk]
  have h : (Subgroup.normalizerMonoidHom L ⟨g, Subgroup.le_normalizer g.2⟩) l =
      g * l * g⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [h]

theorem e6QTwoSixNormAction_of_mem_Bs
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) :
    e6QTwoSixNormAction θ ⟨b, hNL b.2⟩ = e6QTwoSixFrameAction hNL θ b := by
  ext q
  obtain ⟨q', rfl⟩ := θ.surjective q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q'
  rw [e6QTwoSixNormAction_mk, e6QTwoSixFrameAction_apply]
  have h : (Subgroup.normalizerMonoidHom L ⟨b, hNL b.2⟩) l =
      ⟨(b : G) * (l : G) * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩ := by
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [h]

private def e6QTwoSixDiagSet (K : Type) [Field K] : Type :=
  {σ : Fin 6 → Kˣ // σ (0 : Fin 6) = 1}

private noncomputable def e6QTwoSixDiagSetEquiv (K : Type) [Field K] :
    e6QTwoSixDiagSet K ≃ (Fin 5 → Kˣ) where
  toFun σ := fun i => σ.1 (Fin.succAbove (0 : Fin 6) i)
  invFun τ := ⟨Fin.insertNth (0 : Fin 6) 1 τ, by simp⟩
  left_inv σ := by
    apply Subtype.ext
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [σ.2]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      simp
  right_inv τ := by
    funext i
    simp

private theorem e6QTwoSix_card_diagSet
    (hK : Nat.card K = 4) :
    Nat.card (e6QTwoSixDiagSet K) = 3 ^ 5 := by
  rw [Nat.card_congr (e6QTwoSixDiagSetEquiv K), Nat.card_pi]
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunits]

theorem e6QTwoSixFrameAct_of_mem_range
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (he : e ∈ (e6QTwoSixFrameAction hNL θ).range) :
    ∃ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ := by
  classical
  let DiagSet := {σ : Fin 6 → Kˣ // σ (0 : Fin 6) = 1}
  have hDiagCard : Nat.card DiagSet = 3 ^ 5 := e6QTwoSix_card_diagSet hK
  let F : DiagSet → (e6QTwoSixFrameAction hNL θ).range := fun σ =>
    ⟨e6QTwoSixFrameAction hNL θ
        (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))),
      MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  have hF_inj : Function.Injective F := by
    intro σ σ' h
    have hβ : e6QTwoSixFrameAction hNL θ
        (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))) =
        e6QTwoSixFrameAction hNL θ
          (Classical.choose (hfull σ'.1 σ'.2 (fun k =>
            USixTwo.cube_unit_eq_one hK (σ'.1 k)))) := by
      simpa [F] using congrArg Subtype.val h
    have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ
          (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))))
        σ.1 :=
      Classical.choose_spec (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))
    have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ
          (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))))
        σ'.1 := by
      rw [hβ]
      exact Classical.choose_spec (hfull σ'.1 σ'.2 (fun k =>
        USixTwo.cube_unit_eq_one hK (σ'.1 k)))
    have heq : σ.1 = σ'.1 := e6QTwoSixFrameAct_inj hK σ.2 σ'.2
      (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k))
      (fun k => USixTwo.cube_unit_eq_one hK (σ'.1 k)) h1 h2
    exact Subtype.ext heq
  have hF_bij : Function.Bijective F :=
    hF_inj.bijective_of_nat_card_le (by rw [hDiagCard, hrange5])
  obtain ⟨σ, hσ⟩ := hF_bij.2 ⟨e, he⟩
  refine ⟨σ.1, σ.2, fun k => USixTwo.cube_unit_eq_one hK (σ.1 k), ?_⟩
  have hval : e = (F σ).val := (congrArg Subtype.val hσ).symm
  rw [hval]
  exact Classical.choose_spec (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))

theorem e6QTwoSix_conj_mem_sup
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) (τ : Equiv.Perm (Fin 6)) (b : Bs) :
    (e6QTwoSixPermPre hK hQ θ τ : G) * (b : G) * (e6QTwoSixPermPre hK hQ θ τ : G)⁻¹ ∈
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  let n : ↥L := e6QTwoSixPermPre hK hQ θ τ
  let β := e6QTwoSixFrameAction hNL θ
  let w := e6QTwoSixFramePerm hK hQ τ
  have hnL : (n : G) ∈ L := n.2
  have hgN : (n : G) * (b : G) * (n : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hnL) (hNL b.2))
      ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hnL))
  have hbL : (n : G) * (b : G) * (n : G)⁻¹ * (b : G)⁻¹ ∈ L := by
    have h1 : (b : G) * (n : G)⁻¹ * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL b.2) ((n : G)⁻¹)).mp (L.inv_mem hnL)
    have h2 : (n : G) * ((b : G) * (n : G)⁻¹ * (b : G)⁻¹) ∈ L := L.mul_mem hnL h1
    convert h2 using 1
    group
  have hgSup : (n : G) * (b : G) * (n : G)⁻¹ ∈ L ⊔ Bs := by
    have h_eq : (n : G) * (b : G) * (n : G)⁻¹ =
        ((n : G) * (b : G) * (n : G)⁻¹ * (b : G)⁻¹) * (b : G) := by group
    rw [h_eq]
    exact (L ⊔ Bs).mul_mem (Subgroup.mem_sup_left hbL) (Subgroup.mem_sup_right b.2)
  obtain ⟨σ, hσ0, hσ3, hσfr⟩ :=
    e6QTwoSixFrameAct_of_mem_range hK hNL θ hfull hrange5 ⟨b, rfl⟩
  have hperm : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (w * β b * w⁻¹) (σ ∘ ⇑τ.symm) := e6QTwoSixFrameAct_perm hK hσfr τ
  let c0 : Kˣ := ((σ ∘ ⇑τ.symm) (0 : Fin 6))⁻¹
  have hperm' : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (w * β b * w⁻¹) (fun k => c0 * (σ ∘ ⇑τ.symm) k) :=
    TableBUD.FrameAct.smul hperm c0
  have h0' : (fun k => c0 * (σ ∘ ⇑τ.symm) k) (0 : Fin 6) = 1 := by
    show c0 * (σ (τ.symm 0)) = 1
    exact inv_mul_cancel _
  have h3' : ∀ k, (c0 * (σ ∘ ⇑τ.symm) k) ^ 3 = 1 := by
    intro k
    rw [mul_pow]
    simp only [Function.comp_apply]
    rw [hσ3 (τ.symm k), mul_one]
    exact USixTwo.cube_unit_eq_one hK c0
  obtain ⟨b', hb'⟩ := hfull (fun k => c0 * (σ ∘ ⇑τ.symm) k) h0' h3'
  have hb'eq : β b' = w * β b * w⁻¹ :=
    TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
      (hσ := fun k => e6QTwoSixPowThreeVal hK h3' k) hb' hperm'
  have hL_n : e6QTwoSixNormAction θ ⟨n, Subgroup.le_normalizer hnL⟩ = w :=
    (e6QTwoSixNormAction_of_mem_L θ n).trans (e6QTwoSixConjOnQuot_permPre hK hQ θ τ)
  have hB_b : e6QTwoSixNormAction θ ⟨b, hNL b.2⟩ = β b :=
    e6QTwoSixNormAction_of_mem_Bs θ hNL b
  have hg_eq : (⟨(n : G) * (b : G) * (n : G)⁻¹, hgN⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨n, Subgroup.le_normalizer hnL⟩ * ⟨b, hNL b.2⟩ *
        ⟨n, Subgroup.le_normalizer hnL⟩⁻¹ := Subtype.ext rfl
  have hact : e6QTwoSixNormAction θ ⟨(n : G) * (b : G) * (n : G)⁻¹, hgN⟩ =
      w * β b * w⁻¹ := by
    rw [hg_eq, map_mul, map_mul, map_inv, hL_n, hB_b]
  let c : G := (b' : G)⁻¹ * ((n : G) * (b : G) * (n : G)⁻¹)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem (hNL (Bs.inv_mem b'.2)) hgN
  have hc_act : e6QTwoSixNormAction θ ⟨c, hcN⟩ = 1 := by
    have hc_eq : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨b', hNL b'.2⟩⁻¹ * ⟨(n : G) * (b : G) * (n : G)⁻¹, hgN⟩ := Subtype.ext rfl
    rw [hc_eq, map_mul, map_inv, e6QTwoSixNormAction_of_mem_Bs θ hNL b', hact, hb'eq]
    group
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    have hφ : e6QTwoQuotCenterAutHom L (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩) = 1 := by
      apply (MulAut.congr θ).injective
      change e6QTwoSixNormAction θ ⟨c, hcN⟩ = (MulAut.congr θ) 1
      rw [hc_act, map_one]
    have hψ : Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ = 1 := by
      apply e6QTwoQuotCenterAutHom_injective hperf
      rw [hφ, map_one]
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hψ
    simp only [MulAut.one_apply] at h
    have h3 : ((Subgroup.normalizerMonoidHom L ⟨c, hcN⟩) ⟨l, hl⟩ : G) = c * l * c⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨c, hcN⟩ ⟨l, hl⟩
    have h4 : c * l * c⁻¹ = l := by
      rw [← h3]
      exact congrArg Subtype.val h
    calc l * c = (c * l * c⁻¹) * c := by rw [h4]
      _ = c * l := by group
  have hcSup : c ∈ L ⊔ Bs := by
    change (b' : G)⁻¹ * ((n : G) * (b : G) * (n : G)⁻¹) ∈ L ⊔ Bs
    exact (L ⊔ Bs).mul_mem (Subgroup.mem_sup_right (Bs.inv_mem b'.2)) hgSup
  have hcX : c ∈ Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) :=
    e6QTwoSix_C0_le_sup_Z hK θ hperf hBs hcard hx hx1 hBL hstar hNL hI hLx
      (Subgroup.mem_inf.mpr ⟨hcC, hcSup⟩)
  have hg_eq2 : (n : G) * (b : G) * (n : G)⁻¹ = (b' : G) * c := by
    change (n : G) * (b : G) * (n : G)⁻¹ =
      (b' : G) * ((b' : G)⁻¹ * ((n : G) * (b : G) * (n : G)⁻¹))
    group
  rw [hg_eq2]
  exact (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).mul_mem
    (Subgroup.mem_sup_left b'.2) hcX

theorem e6QTwoSix_normalizes_sup
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) (τ : Equiv.Perm (Fin 6)) :
    (e6QTwoSixPermPre hK hQ θ τ : G) ∈
      Subgroup.normalizer
        (((Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))) : Subgroup G) : Set G) := by
  classical
  let n : ↥L := e6QTwoSixPermPre hK hQ θ τ
  have hLN : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) :=
    e6QTwoSixNormalizesCenter (Bs := L) (hNL := Subgroup.le_normalizer)
  have hnZ : (n : G) ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) := hLN n.2
  have hle : (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (n : G)).toMonoidHom ≤
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro - ⟨y, hy, rfl⟩
      exact e6QTwoSix_conj_mem_sup hK θ hNL hfull hrange5 hperf hBs hcard hx hx1 hBL hstar
        hI hLx τ ⟨y, hy⟩
    · rintro - ⟨z, hz, rfl⟩
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hnZ z).mp hz)
  have hcard : Nat.card ↥((Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (n : G)).toMonoidHom) =
      Nat.card ↥(Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))) :=
    Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective
  have hEq : (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (n : G)).toMonoidHom =
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem e6QTwoSix_exists_sylow_conj
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) (τ : Equiv.Perm (Fin 6)) :
    ∃ z ∈ Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)),
      (Bs.map (MulAut.conj (e6QTwoSixPermPre hK hQ θ τ : G))).map
        (MulAut.conj z).toMonoidHom = Bs := by
  classical
  let n : ↥L := e6QTwoSixPermPre hK hQ θ τ
  let X : Subgroup G := Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))
  have hNX : (n : G) ∈ Subgroup.normalizer (X : Set G) := by
    dsimp only [n, X]
    exact e6QTwoSix_normalizes_sup hK θ hNL hfull hrange5 hperf hBs hcard hx hx1 hBL hstar
      hI hLx τ
  have hXmap : X.map (MulAut.conj (n : G)).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hNX
  have hP₁ : Bs ≤ X := le_sup_left
  have hP₂ : Bs.map (MulAut.conj (n : G)).toMonoidHom ≤ X := by
    calc Bs.map (MulAut.conj (n : G)).toMonoidHom
        ≤ X.map (MulAut.conj (n : G)).toMonoidHom := Subgroup.map_mono le_sup_left
      _ = X := hXmap
  have hP₁g : IsPGroup 3 Bs :=
    CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian hBs
  have hP₂g : IsPGroup 3 (Bs.map (MulAut.conj (n : G)).toMonoidHom) := hP₁g.map _
  have hcard' : Nat.card Bs = Nat.card ↥(Bs.map (MulAut.conj (n : G)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective).symm
  have hindex : ¬ 3 ∣ (Bs.subgroupOf X).index :=
    e6QTwoSixSylowIndex hK θ hperf hBs hx hBL hstar hNL
  obtain ⟨z, hzX, hz⟩ :=
    sylow_conj_of_card_eq (p := 3) hP₁ hP₂ hP₁g hP₂g hcard' hindex
  exact ⟨z, hzX, hz⟩

end CFSG.StandardType.E6QTwo

end
