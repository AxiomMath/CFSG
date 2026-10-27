module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc
public import CFSG.LieType.HighestRoot.CentG2
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
import CFSG.RankThree.PartTwo.Sec16.KS16ProofGTwo

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

namespace KS11Lie2Proof

@[expose] def HasType424 (H : Type) [Group H] : Prop :=
  ∃ L ∈ thetaComponents 3 H, IsType424 (L ⧸ aschbacherSolvableCore 3 L)

theorem HasType424.of_mulEquiv {H H' : Type} [Group H] [Group H'] [Finite H] (e : H ≃* H')
    (h : HasType424 H) : HasType424 H' := by
  obtain ⟨L, hL, hT⟩ := h
  refine ⟨L.map e.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three e hL, ?_⟩
  set φ := L.equivMapOfInjective e.toMonoidHom e.injective
  exact isType424_of_mulEquiv
    (QuotientGroup.congr _ _ φ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three φ)).symm hT

theorem hasType424_of_mem {G : Type} [Group G] [Finite G] {H J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn H) (hT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    HasType424 H := by
  obtain ⟨L, hL, rfl⟩ := hJ
  refine ⟨L, hL, ?_⟩
  set φ := L.equivMapOfInjective H.subtype H.subtype_injective
  exact isType424_of_mulEquiv
    (QuotientGroup.congr _ _ φ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three φ)) hT

theorem fixSub_congr {Z C : Type} [Group Z] [Group C] (e : Z ≃* C) (α : MulAut Z) :
    Item426.fixSub (MulAut.congr e α) = (Item426.fixSub α).map e.toMonoidHom := by
  ext c
  constructor
  · intro hc
    refine ⟨e.symm c, ?_, by simp⟩
    have h1 : e (α (e.symm c)) = c := hc
    change α (e.symm c) = e.symm c
    have h2 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  · rintro ⟨z, hz, rfl⟩
    have hz' : α z = z := hz
    change e (α (e.symm (e z))) = e z
    rw [MulEquiv.symm_apply_apply, hz']

@[expose] noncomputable def fixSubCongr {Z C : Type} [Group Z] [Group C] (e : Z ≃* C)
    (α : MulAut Z) : Item426.fixSub α ≃* Item426.fixSub (MulAut.congr e α) :=
  ((Item426.fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (fixSub_congr e α).symm)

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem not_hasType424_of_simple (N : Subgroup Γ) [IsSimpleGroup N]
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N) {x y : Γ} (hxN : x ∈ N) (hyN : y ∈ N)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hcx : Commute ⁅x, y⁆ x)
    (hcy : Commute ⁅x, y⁆ y) (hyx : y ∉ Subgroup.zpowers x) : ¬ HasType424 Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩
  have hLN : L ≤ N := by
    have h1 : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  have hsn : (L.subgroupOf N).IsSubnormal := hLsn.subgroupOf
  rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · exfalso
    have hLb : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      have h2 : (⟨l, hLN hl⟩ : N) ∈ L.subgroupOf N := hl
      rw [h, Subgroup.mem_bot] at h2
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h2
    subst hLb
    obtain ⟨-, -, u, v, huv⟩ := hLq
    exact huv (Subsingleton.elim _ _)
  · have hNL : N ≤ L := by
      intro n hn
      have h2 : (⟨n, hn⟩ : N) ∈ L.subgroupOf N := by rw [h]; trivial
      exact h2
    have hxL : x ∈ L := hNL hxN
    have hyL : y ∈ L := hNL hyN
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    set xb := π ⟨x, hxL⟩ with hxb
    set yb := π ⟨y, hyL⟩ with hyb
    have hcube := Sec16.KS1622GTwoProof.pow_three_eq_one_of_mem_closure hx3 hy3 hcx hcy
    have hxb1 : xb ≠ 1 := by
      intro h1
      rw [hxb, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
        (Subtype.ext (by simpa using hx3))
      exact hx1 (congrArg Subtype.val h2)
    have hxb3 : xb ^ 3 = 1 := by
      rw [hxb, ← map_pow]
      have : (⟨x, hxL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hyb3 : yb ^ 3 = 1 := by
      rw [hyb, ← map_pow]
      have : (⟨y, hyL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have hP : IsPGroup 3 (Subgroup.closure ({xb, yb} : Set (L ⧸ aschbacherSolvableCore 3 L))) := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      have hle : Subgroup.closure ({xb, yb} : Set (L ⧸ aschbacherSolvableCore 3 L)) ≤
          (Subgroup.closure ({⟨x, hxL⟩, ⟨y, hyL⟩} : Set L)).map π := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact ⟨_, Subgroup.subset_closure (by simp), rfl⟩
        · exact ⟨_, Subgroup.subset_closure (by simp), rfl⟩
      obtain ⟨w, hw, hwg⟩ := hle g.2
      have hw' : (w : Γ) ∈ Subgroup.closure ({x, y} : Set Γ) := by
        have hmap : (Subgroup.closure ({⟨x, hxL⟩, ⟨y, hyL⟩} : Set L)).map L.subtype ≤
            Subgroup.closure ({x, y} : Set Γ) := by
          rw [MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨u, hu, rfl⟩
          rcases hu with rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
        exact hmap ⟨w, hw, rfl⟩
      rw [← hwg, ← map_pow]
      have : w ^ 3 = 1 := Subtype.ext (by simpa using hcube _ hw')
      rw [this, map_one]
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have hSc : IsCyclic S := KS11LieProof.isCyclic_sylow_three_of_isType424 hT hLq S
    have hxS : xb ∈ S := hS (Subgroup.subset_closure (by simp))
    have hyS : yb ∈ S := hS (Subgroup.subset_closure (by simp))
    have hyb1 : yb ≠ 1 := by
      intro h1
      apply hyx
      rw [hyb, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
        (Subtype.ext (by simpa using hy3))
      have h3 : y = 1 := congrArg Subtype.val h2
      rw [h3]
      exact Subgroup.one_mem _
    have hox : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb1
    have hoy : orderOf yb = 3 := orderOf_eq_prime hyb3 hyb1
    have hzS : (Subgroup.zpowers (⟨xb, hxS⟩ : S)) = Subgroup.zpowers ⟨yb, hyS⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk, hox, hoy]
    have hyx' : (⟨yb, hyS⟩ : S) ∈ Subgroup.zpowers ⟨xb, hxS⟩ := by
      rw [hzS]
      exact Subgroup.mem_zpowers _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyx'
    have hi' : xb ^ i = yb := congrArg Subtype.val hi
    apply hyx
    have hθ : (⟨y, hyL⟩ : L) * ((⟨x, hxL⟩ : L) ^ i)⁻¹ ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, map_zpow, ← hπ,
        ← hxb, ← hyb, hi', mul_inv_cancel]
    have hmem : y * (x ^ i)⁻¹ ∈ Subgroup.closure ({x, y} : Set Γ) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
    have h3 : ((⟨y, hyL⟩ : L) * ((⟨x, hxL⟩ : L) ^ i)⁻¹) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hcube _ hmem)
    have h4 := congrArg Subtype.val (eq_one_of_mem_theta_of_pow_eq_one hθ h3)
    have h5 : y * (x ^ i)⁻¹ = 1 := by simpa using h4
    rw [mul_inv_eq_one] at h5
    rw [h5]
    exact Subgroup.zpow_mem_zpowers x i

section E9

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

@[expose] def sl2Three (k : Type) [Field k] : SL2 k :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

theorem sl2Three_pow_three (k : Type) [Field k] : sl2Three k ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  simp only [sl2Three]
  rw [pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp

theorem sl2Three_ne_smul {k : Type} [Field k] (l : k) :
    (sl2Three k : Matrix (Fin 2) (Fin 2) k) ≠ l • (1 : Matrix (Fin 2) (Fin 2) k) := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  simp [sl2Three] at h1

theorem sl2Three_mul_uSL_ne {k : Type} [Field k] {l : k} (hl : l ^ 2 = 1) :
    ((sl2Three k * uSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) ≠
      l • ((uSL 1 * sl2Three k : SL2 k) : Matrix (Fin 2) (Fin 2) k) := by
  intro h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  simp only [sl2Three, uSL, Matrix.mul_fin_two] at h
  have h1 := congrFun (congrFun h 0) 0
  simp at h1
  rw [h1] at hl
  norm_num at hl

theorem simpleRootSL2_eq_one
    {τ : Tag} {k : Type} [Field k] (i : Fin τ.rank) {A : SL2 k}
    (hA : simpleRootSL2 τ k i A = 1) :
    ∃ l : kˣ, (l : k) ^ 2 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) k) = (l : k) • 1 :=
  (exceptional_ordinary_rank_one_central_image τ k i).choose_spec.2.2.2.2.2.1 A
    (MonoidHom.mem_ker.2 hA)

theorem g2_root_even_s_check : ∀ j < (Tag.rootCertificate .G2).roots.length,
    (Tag.rootCertificate .G2).root j g2s % 2 = 0 → (Tag.rootCertificate .G2).root j g2s ≠ 0 →
      (Tag.rootCertificate .G2).root j = g2δ ∨ (Tag.rootCertificate .G2).root j = -g2δ := by
  decide

theorem g2_not_isRoot_comb' {α β : Fin (Tag.rank .G2) → ℤ}
    (h : ((α = g2δ ∨ α = -g2δ) ∧ (β = g2e0 ∨ β = -g2e0)) ∨
      ((α = g2e0 ∨ α = -g2e0) ∧ (β = g2δ ∨ β = -g2δ)))
    {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : ¬ IsRoot .G2 (x • α + y • β) := by
  intro hr
  obtain ⟨j, hj, hv⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)).1 hr
  have c0 : ∀ {v w : Fin (Tag.rank .G2) → ℤ}, v = w → v g2l = w g2l := fun h => h ▸ rfl
  have c1 : ∀ {v w : Fin (Tag.rank .G2) → ℤ}, v = w → v g2s = w g2s := fun h => h ▸ rfl
  have hs := c1 hv
  have hl := c0 hv
  rcases h with ⟨hα | hα, hβ | hβ⟩ | ⟨hα | hα, hβ | hβ⟩ <;> subst hα hβ <;>
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply] at hs hl
    simp only [nsmul_eq_mul, mul_neg, g2δ_l, g2δ_s, g2e0_l, g2e0_s] at hs hl
    have h2 := g2_root_even_s_check j hj (by omega) (by omega)
    rcases h2 with h2 | h2
    · have h3 := c0 h2
      have h4 := c1 h2
      simp only [g2δ_l, g2δ_s] at h3 h4
      omega
    · have h3 := c0 h2
      have h4 := c1 h2
      simp only [Pi.neg_apply, g2δ_l, g2δ_s] at h3 h4
      omega


theorem g2_commute' {k : Type} [Field k] {x y : ModGL .G2 k}
    (hx : x ∈ rootSubgroup .G2 k g2e0 ⊔ rootSubgroup .G2 k (-g2e0))
    (hy : y ∈ rootSubgroup .G2 k g2δ ⊔ rootSubgroup .G2 k (-g2δ)) : Commute x y := by
  have hroot : ∀ v, v = g2e0 ∨ v = -g2e0 ∨ v = g2δ ∨ v = -g2δ → IsRoot .G2 v := by
    rintro v (rfl | rfl | rfl | rfl)
    exacts [isRoot_single _ _, IsRoot.neg (isRoot_single _ _), isRoot_g2δ,
      IsRoot.neg isRoot_g2δ]
  have key : ∀ {α β : Fin (Tag.rank .G2) → ℤ}, (α = g2δ ∨ α = -g2δ) → (β = g2e0 ∨ β = -g2e0) →
      ∀ u ∈ rootSubgroup .G2 k α, ∀ v ∈ rootSubgroup .G2 k β, Commute u v := by
    intro α β hα hβ u hu v hv
    have hα' := hroot α (by rcases hα with h | h <;> simp [h])
    have hβ' := hroot β (by rcases hβ with h | h <;> simp [h])
    have hne : α ≠ β ∧ α ≠ -β := by
      rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> exact ⟨by decide, by decide⟩
    exact commute_of_forall_not_isRoot hα' hβ' hne.1 hne.2
      (fun a b ha hb => g2_not_isRoot_comb' (Or.inl ⟨hα, hβ⟩) ha hb) hu hv
  have hδ : ∀ {β : Fin (Tag.rank .G2) → ℤ}, (β = g2δ ∨ β = -g2δ) →
      ∀ u ∈ rootSubgroup .G2 k β, Commute x u := fun {β} hβ u hu =>
    (commute_of_mem_sup (fun v hv => key hβ (Or.inl rfl) u hu v hv)
      (fun v hv => key hβ (Or.inr rfl) u hu v hv) hx).symm
  exact commute_of_mem_sup (hδ (Or.inl rfl)) (hδ (Or.inr rfl)) hy

theorem g2_exists_e9 (k : Type) [Field k] :
    ∃ u v : adjointGroup .G2 k, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  set n := canonicalRep (coxeterSystem .G2) k (simple .G2 g2s * simple .G2 g2l) with hn
  set ρ₁ := simpleRootSL2 .G2 k g2l with hρ₁
  set ρ₂ := simpleRootSL2 .G2 k g2s with hρ₂
  set M := sl2Three k with hM
  have hu₀Q : ρ₁ M ∈ rootSubgroup .G2 k g2e0 ⊔ rootSubgroup .G2 k (-g2e0) := by
    rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
    exact ⟨M, rfl⟩
  have hQ₂ : ∀ A, MulAut.conj n (ρ₂ A) ∈ rootSubgroup .G2 k g2δ ⊔ rootSubgroup .G2 k (-g2δ) := by
    intro A
    rw [← map_conj_canonicalRep_closure_xUnit_yUnit g2_w_smul, ← range_simpleRootSL2]
    exact ⟨ρ₂ A, ⟨A, rfl⟩, rfl⟩
  have hnA : n ∈ adjointGroup .G2 k := canonicalRep_mem_adjointGroup _ k _
  have hu₀A : ρ₁ M ∈ adjointGroup .G2 k := simpleRootSL2_mem_adjointGroup _ M
  have hv₀A : MulAut.conj n (ρ₂ M) ∈ adjointGroup .G2 k :=
    mul_mem (mul_mem hnA (simpleRootSL2_mem_adjointGroup _ M)) (inv_mem hnA)
  refine ⟨⟨ρ₁ M, hu₀A⟩, ⟨MulAut.conj n (ρ₂ M), hv₀A⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : ρ₁ M = 1 := congrArg Subtype.val h
    obtain ⟨l, -, hl⟩ := simpleRootSL2_eq_one g2l h1
    exact sl2Three_ne_smul (l : k) hl
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hM, sl2Three_pow_three, map_one]
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ← map_pow, hM, sl2Three_pow_three, map_one, map_one]
  · exact Subtype.ext (g2_commute' hu₀Q (hQ₂ M)).eq
  · intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hv₀ : MulAut.conj n (ρ₂ M) = ρ₁ M ^ i := by
      have h1 := congrArg Subtype.val hi
      simp only [Subgroup.coe_zpow] at h1
      exact h1.symm
    have hvQ₁ : MulAut.conj n (ρ₂ M) ∈ rootSubgroup .G2 k g2e0 ⊔ rootSubgroup .G2 k (-g2e0) := by
      rw [hv₀]
      exact zpow_mem hu₀Q i
    have hc := (g2_commute' hvQ₁ (hQ₂ (uSL 1))).eq
    have hc' : ρ₂ M * ρ₂ (uSL 1) = ρ₂ (uSL 1) * ρ₂ M :=
      (MulAut.conj n).injective (by rw [map_mul, map_mul]; exact hc)
    have h1 : ρ₂ (M * uSL 1 * (uSL 1 * M)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc', mul_inv_cancel]
    obtain ⟨l, hl2, hl⟩ := simpleRootSL2_eq_one g2s h1
    apply sl2Three_mul_uSL_ne hl2
    have h2 : M * uSL 1 = (M * uSL 1 * (uSL 1 * M)⁻¹) * (uSL 1 * M) := by group
    rw [hM] at h2 hl
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, hl, Matrix.smul_mul, Matrix.one_mul]

theorem isSimpleGroup_g2
    {k : Type} [Field k] [Finite k] (hk : 3 ≤ Nat.card k) :
    IsSimpleGroup (adjointGroup .G2 k) :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k hk)
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot.symm))

end E9

section FieldFixed

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

noncomputable abbrev fixIncl :
    Item426.fixSub (KFacts.g2FieldHom K σ) →* ModGL Tag.G2 K :=
  (adjointGroup Tag.G2 K).subtype.comp (Item426.fixSub (KFacts.g2FieldHom K σ)).subtype

omit [Finite K] in
theorem fixIncl_injective : Function.Injective (fixIncl σ) :=
  (adjointGroup Tag.G2 K).subtype_injective.comp
    (Item426.fixSub (KFacts.g2FieldHom K σ)).subtype_injective

omit [Finite K] in
theorem fixIncl_mem (h : Item426.fixSub (KFacts.g2FieldHom K σ)) :
    fixIncl σ h ∈ entrywiseFixedGroup Tag.G2 σ := by
  refine ⟨(h : adjointGroup Tag.G2 K).2, ?_⟩
  change Units.map (entrywiseHom σ.toRingHom) ((h : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
    ((h : adjointGroup Tag.G2 K) : ModGL Tag.G2 K)
  rw [← KFacts.coe_g2FieldHom]
  exact congrArg Subtype.val h.2

omit [Finite K] in
theorem fixedFieldImage_le_range : fixedFieldImage Tag.G2 σ ≤ (fixIncl σ).range := by
  intro g hg
  obtain ⟨hgC, hgσ⟩ := fixedFieldImage_le hg
  have hfix : KFacts.g2FieldHom K σ ⟨g, hgC⟩ = ⟨g, hgC⟩ :=
    Subtype.ext (by rw [KFacts.coe_g2FieldHom]; exact hgσ)
  exact ⟨⟨⟨g, hgC⟩, hfix⟩, rfl⟩

@[expose] noncomputable def fixN : Subgroup (Item426.fixSub (KFacts.g2FieldHom K σ)) :=
  (fixedFieldImage Tag.G2 σ).comap (fixIncl σ)

theorem commutator_mem_fixN (a b : Item426.fixSub (KFacts.g2FieldHom K σ)) :
    a * b * a⁻¹ * b⁻¹ ∈ fixN σ := by
  obtain ⟨-, -, -, -, -, -, hab⟩ := Chevalley_coordinate_field_fixed_normal_subgroup Tag.G2 K σ
  set E := entrywiseFixedGroup Tag.G2 σ
  set a' : E := ⟨fixIncl σ b⁻¹, fixIncl_mem σ _⟩
  set b' : E := ⟨fixIncl σ a⁻¹, fixIncl_mem σ _⟩
  have h1 := hab (QuotientGroup.mk a') (QuotientGroup.mk b')
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 : ((a' * b')⁻¹ * (b' * a') : E) = fixIncl σ (a * b * a⁻¹ * b⁻¹) := by
    simp only [a', b', mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      inv_inv]
    group
  change fixIncl σ (a * b * a⁻¹ * b⁻¹) ∈ fixedFieldImage Tag.G2 σ
  rw [← h2]
  exact h1

@[expose] noncomputable def fixNEquiv : fixN σ ≃* adjointGroup Tag.G2 (fixSubfield σ) :=
  (((fixN σ).equivMapOfInjective (fixIncl σ) (fixIncl_injective σ)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (fixedFieldImage_le_range σ)))).trans
    ((adjointGroup Tag.G2 (fixSubfield σ)).equivMapOfInjective
      (baseChangeGL (fixSubfield σ).subtype) (baseChangeGL_injective _)).symm

theorem not_hasType424_fixSub
    (hk : 3 ≤ Nat.card (fixSubfield σ)) :
    ¬ HasType424 (Item426.fixSub (KFacts.g2FieldHom K σ)) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : IsSimpleGroup (adjointGroup Tag.G2 (fixSubfield σ)) := isSimpleGroup_g2 hk
  have : IsSimpleGroup (fixN σ) := MulEquiv.isSimpleGroup (fixNEquiv σ)
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := g2_exists_e9 (fixSubfield σ)
  set x := (fixNEquiv σ).symm u with hx
  set y := (fixNEquiv σ).symm v with hy
  have hx1 : (x : Item426.fixSub (KFacts.g2FieldHom K σ)) ≠ 1 := by
    intro h
    apply hu1
    have h1 : x = 1 := Subtype.ext h
    rw [hx, MulEquiv.symm_apply_eq, map_one] at h1
    exact h1
  have hx3 : (x : Item426.fixSub (KFacts.g2FieldHom K σ)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx, ← map_pow, hu3, map_one, Subgroup.coe_one]
  have hy3 : (y : Item426.fixSub (KFacts.g2FieldHom K σ)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hy, ← map_pow, hv3, map_one, Subgroup.coe_one]
  have hxy : (x : Item426.fixSub (KFacts.g2FieldHom K σ)) * y = y * x := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hx, hy, ← map_mul, ← map_mul, huv]
  have hc : ⁅(x : Item426.fixSub (KFacts.g2FieldHom K σ)),
      (y : Item426.fixSub (KFacts.g2FieldHom K σ))⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hxy
  refine not_hasType424_of_simple (fixN σ) (commutator_mem_fixN σ) x.2 y.2 hx1 hx3 hy3
    (by rw [hc]; exact Commute.one_left _) (by rw [hc]; exact Commute.one_left _) ?_
  intro hmem
  apply hvu
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : x ^ i = y := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hi)
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [hx, hy, ← map_zpow, MulEquiv.symm_apply_eq, MulEquiv.apply_symm_apply] at h1
  exact h1

end FieldFixed

section Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem mul_mul_inv_eq_congr {C : Type} [Group C] (β σ : MulAut C) :
    β * σ * β⁻¹ = MulAut.congr β σ := by
  ext x
  rfl

theorem three_le_card_fixSubfield {K : Type} [Field K] [Finite K] [CharP K 3] (σ : K ≃+* K) :
    3 ≤ Nat.card (fixSubfield σ) := by
  let f : Fin 3 → fixSubfield σ := fun i => ((i : ℕ) : fixSubfield σ)
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : ((i : ℕ) : K) = ((j : ℕ) : K) := by
      have := congrArg Subtype.val hij
      simpa [f] using this
    rw [CharP.natCast_eq_natCast K 3, Nat.ModEq, Nat.mod_eq_of_lt i.2,
      Nat.mod_eq_of_lt j.2] at h1
    exact Fin.ext h1
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem conj_mul_mul_inv_eq_congr {C : Type} [Group C] (k : C) (σ : MulAut C) :
    MulAut.conj k * σ * (MulAut.conj k)⁻¹ = MulAut.congr (MulAut.conj k) σ := by
  ext x
  rfl



theorem not_hasType424_outer_g2 {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8) {α : MulAut (adjointGroup Tag.G2 K)}
    (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α) : ¬ HasType424 (Item426.fixSub α) := by
  obtain ⟨σ, hσ3, k, rfl⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα3 hout
  have hcard : Nat.card (fixSubfield σ) ^ 3 = Nat.card K := by
    have h := KFacts.card_fixSubfield_pow σ
    rwa [hσ3] at h
  have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
    have h1 : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
    by_contra h
    have h2 : Nat.card (fixSubfield σ) = 2 := by omega
    rw [h2] at hcard
    exact hK8 (by rw [← hcard]; norm_num)
  intro h
  rw [conj_mul_mul_inv_eq_congr] at h
  exact not_hasType424_fixSub σ hk3 (h.of_mulEquiv (fixSubCongr (MulAut.conj k) _).symm)

theorem not_hasType424_conj_field_three {K : Type} [Field K] [Finite K] [CharP K 3] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (3 * m)) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 3 ^ m)
    (hσ3 : σ ^ 3 = 1) {g : adjointGroup Tag.G2 K}
    (hα3 : (MulAut.conj g * KFacts.g2FieldHom K σ) ^ 3 = 1) :
    ¬ HasType424 (Item426.fixSub (MulAut.conj g * KFacts.g2FieldHom K σ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Φ := KFacts.g2FieldHom K σ with hΦ
  have hN : g * Φ g * Φ (Φ g) = 1 := by
    rw [KFacts.conj_mul_pow_three, ← map_pow, hσ3, map_one, mul_one] at hα3
    have hz : g * Φ g * Φ (Φ g) ∈ Subgroup.center (adjointGroup Tag.G2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.G2 K) => φ y) hα3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * (g * Φ g * Φ (Φ g)) = g * Φ g * Φ (Φ g) * y * (g * Φ g * Φ (Φ g))⁻¹ *
            (g * Φ g * Φ (Φ g)) := by rw [h1]
        _ = g * Φ g * Φ (Φ g) * y := by group
    rw [center_adjointGroup_eq_bot] at hz
    exact hz
  obtain ⟨β, hβ⟩ := KFacts.exists_conj_mul_eq_of_norm_eq_one (p := 3) hm hK hσ
    (fun h => KFacts.coe_g2FieldHom σ h) hN
  intro h
  rw [hβ, mul_mul_inv_eq_congr] at h
  exact not_hasType424_fixSub σ (three_le_card_fixSubfield σ)
    (h.of_mulEquiv (fixSubCongr β Φ).symm)

theorem not_hasType424_outer_g2_three {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) {α : MulAut (adjointGroup Tag.G2 K)}
    (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α) : ¬ HasType424 (Item426.fixSub α) := by
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := ‹CharP K 3›
  obtain ⟨hord, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  let φ : MulAut (adjointGroup Tag.G2 K) := CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K
  have hord' : orderOf φ = 2 * f := hord
  have hdvd : ∀ (j : ℕ) (h : adjointGroup Tag.G2 K), φ ^ j = MulAut.conj h → 2 * f ∣ j :=
    fun j h hj => G2_two_mul_dvd_of_pow_eq_conj hf hK hj
  obtain ⟨⟨g₀, k⟩, hgk, -⟩ := hNF α
  let g : adjointGroup Tag.G2 K := g₀
  have hgk' : α = MulAut.conj g * φ ^ (k : ℕ) := hgk
  have h3k : 2 * f ∣ 3 * (k : ℕ) := by
    have h1 : (MulAut.conj g * φ ^ (k : ℕ)) ^ 3 = 1 := hgk' ▸ hα3
    rw [KFacts.conj_mul_pow_three, ← pow_mul] at h1
    refine hdvd _ (g * (φ ^ (k : ℕ)) g * (φ ^ (k : ℕ)) ((φ ^ (k : ℕ)) g))⁻¹ ?_
    rw [map_inv, mul_comm 3]
    exact eq_inv_of_mul_eq_one_right h1
  have hk : ¬ 2 * f ∣ (k : ℕ) := by
    rintro ⟨t, ht⟩
    apply hout
    refine ⟨g, ?_⟩
    rw [hgk', ht, pow_mul, ← hord', pow_orderOf_eq_one, one_pow, mul_one]
  have hkl : (k : ℕ) < 2 * f := k.2
  obtain ⟨t, ht⟩ := h3k
  have hk0 : 0 < (k : ℕ) := Nat.pos_of_ne_zero fun h => hk (by rw [h]; exact dvd_zero _)
  have ht12 : t = 1 ∨ t = 2 := by
    rcases t with _ | _ | _ | t
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have : 2 * f * (t + 1 + 1 + 1) ≥ 2 * f * 3 := Nat.mul_le_mul_left _ (by omega)
      omega
  obtain ⟨m, hfm, hkm⟩ : ∃ m, f = 3 * m ∧ ((k : ℕ) = 2 * m ∨ (k : ℕ) = 4 * m) := by
    rcases ht12 with rfl | rfl
    · exact ⟨(k : ℕ) / 2, by omega, Or.inl (by omega)⟩
    · exact ⟨(k : ℕ) / 4, by omega, Or.inr (by omega)⟩
  have hm : 1 ≤ m := by omega
  have hK' : Nat.card K = 3 ^ (3 * m) := by rw [hK, hfm]
  obtain ⟨fr, hfr, hfro, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three hf hK
  set σ := fr ^ m with hσdef
  have hσ : ∀ c, σ c = c ^ 3 ^ m := ringAut_pow_apply_of_frobenius hfr m
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef, ← pow_mul, mul_comm, ← hfm, ← hfro, pow_orderOf_eq_one]
  have hΦ : φ ^ (2 * m) = KFacts.g2FieldHom K σ :=
    (finiteExceptionalAut_pow_two_mul CFSG.LieType.Ree.ReeTag.G2 m).trans
      (exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.G2 hσ).symm
  rcases hkm with hkm | hkm
  ·
    have hα : α = MulAut.conj g * KFacts.g2FieldHom K σ := by rw [hgk', hkm, hΦ]
    rw [hα] at hα3 ⊢
    exact not_hasType424_conj_field_three hm hK' hσ hσ3 hα3
  ·
    set Φ := KFacts.g2FieldHom K σ with hΦdef
    have hΦ3 : Φ ^ 3 = 1 := by rw [hΦdef, ← map_pow, hσ3, map_one]
    have hα : α = MulAut.conj g * Φ ^ 2 := by
      rw [hgk', hkm, show 4 * m = 2 * m * 2 by ring, pow_mul, hΦ]
    have hinv : α⁻¹ = MulAut.conj (Φ g⁻¹) * Φ := by
      have hΦ2 : (Φ ^ 2)⁻¹ = Φ := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ, hΦ3]
      rw [hα, mul_inv_rev, hΦ2, ← KFacts.mul_mulAutConj_mul_inv, map_inv, inv_mul_cancel_right]
    have hinv3 : (MulAut.conj (Φ g⁻¹) * Φ) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    have hfix : Item426.fixSub α = Item426.fixSub α⁻¹ := by
      ext x
      constructor
      · intro hx
        have hx' : α x = x := hx
        change α⁻¹ x = x
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hx']
      · intro hx
        have hx' : α⁻¹ x = x := hx
        change α x = x
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq] at hx'
        exact hx'.symm
    intro h
    rw [hfix, hinv] at h
    exact not_hasType424_conj_field_three hm hK' hσ hσ3 hinv3 h

end Descent

end KS11Lie2Proof

@[expose] def NoOuterType424G2Eight : Prop :=
  NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.card = 8 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

section Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem noOuterType424G2_of_eight (h8 : NoOuterType424G2Eight) : NoOuterType424G2 := by
  intro Z _ _ hZ α J hα3 hin hJ hJT
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  by_cases hq8 : q.card = 8
  · exact h8 Z ⟨X, inferInstance, ⟨q, hq, hq8, ⟨f⟩⟩, ⟨e⟩⟩ α J hα3 hin hJ hJT
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  have hq3 : 3 ≤ q.card := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rwa [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let E : Z ≃* adjointGroup Tag.G2 K :=
    ((e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans b.symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
  have hT := (KS11Lie2Proof.hasType424_of_mem hJ hJT).of_mulEquiv
    (KS11Lie2Proof.fixSubCongr E α)
  have hα3' : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hout : ¬ KFacts.IsInnerAut (MulAut.congr E α) := by
    rintro ⟨c, hc⟩
    apply hin
    refine ⟨E.symm c, ?_⟩
    have h1 := congrArg (MulAut.congr E.symm) hc
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at h1
    rw [h1]
    ext z
    simp
  by_cases hp3 : q.p = 3
  · have : CharP K 3 := CharP.congr q.p hp3
    have hK3 : Nat.card K = 3 ^ q.exponent := by
      rw [hK, TauCeti.PrimePower.card_def, hp3]
    exact KS11Lie2Proof.not_hasType424_outer_g2_three q.exponent_pos hK3 hα3' hout hT
  · have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K q.p]
      exact hp3
    have hq3' : q.card ≠ 3 := by
      intro h
      rw [TauCeti.PrimePower.card_def] at h
      have h1 : q.p ∣ 3 := by
        rw [← h]
        exact dvd_pow_self _ q.exponent_pos.ne'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp h1)
    have hK4 : 4 ≤ Nat.card K := by omega
    have hK8 : Nat.card K ≠ 8 := by rw [hK]; exact hq8
    exact KS11Lie2Proof.not_hasType424_outer_g2 hK3 hK4 hK8 hα3' hout hT

end Assembly

end CFSG.RankThree.PartTwo.Sec11
