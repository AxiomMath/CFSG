module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Lab

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat CFSG.Quasithin.OperatorJH
open scoped MatrixGroups Matrix Pointwise

namespace L4316

variable {G : Type} [Group G] {F : Type} [Field F]

@[expose] def qSub (Q : Subgroup G) (β₂ : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (W : AddSubgroup (Fin 2 → Fin 3 → F)) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ Q, Multiplicative.toAdd (β₂ ⟨x, hx⟩) ∈ W}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Q.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, Q.mul_mem ha hb⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, toAdd_mul]
    exact W.add_mem ha' hb'
  one_mem' := ⟨Q.one_mem, by
    have e : (⟨1, Q.one_mem⟩ : ↥Q) = 1 := rfl
    rw [e, map_one, toAdd_one]
    exact W.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Q.inv_mem ha, ?_⟩
    have e : (⟨a⁻¹, Q.inv_mem ha⟩ : ↥Q) = (⟨a, ha⟩ : ↥Q)⁻¹ := rfl
    rw [e, map_inv, toAdd_inv]
    exact W.neg_mem ha'

theorem qSub_le (Q : Subgroup G) (β₂ : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (W : AddSubgroup (Fin 2 → Fin 3 → F)) : qSub Q β₂ W ≤ Q := fun _ hx => hx.1

theorem qSub_mono {Q : Subgroup G} {β₂ : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    {W W' : AddSubgroup (Fin 2 → Fin 3 → F)} (h : W ≤ W') : qSub Q β₂ W ≤ qSub Q β₂ W' :=
  fun _ ⟨hx, hx'⟩ => ⟨hx, h hx'⟩

@[expose] def wSub₁ (F : Type) [Field F] : AddSubgroup (Fin 2 → Fin 3 → F) where
  carrier := {v | v 0 0 = 0 ∧ v 1 = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by simp [ha, hb], by rw [Pi.add_apply, ha', hb', add_zero]⟩
  zero_mem' := ⟨rfl, rfl⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by simp [ha], by rw [Pi.neg_apply, ha', neg_zero]⟩

@[expose] def wSub₂ (F : Type) [Field F] : AddSubgroup (Fin 2 → Fin 3 → F) where
  carrier := {v | v 1 = 0}
  add_mem' := by
    rintro a b ha hb
    change a 1 + b 1 = 0
    rw [show a 1 = 0 from ha, show b 1 = 0 from hb, add_zero]
  zero_mem' := rfl
  neg_mem' := by
    rintro a ha
    change -(a 1) = 0
    rw [show a 1 = 0 from ha, neg_zero]

@[expose] def wSub₃ (F : Type) [Field F] : AddSubgroup (Fin 2 → Fin 3 → F) where
  carrier := {v | v 1 0 = 0}
  add_mem' := by
    rintro a b ha hb
    change a 1 0 + b 1 0 = 0
    rw [show a 1 0 = 0 from ha, show b 1 0 = 0 from hb, add_zero]
  zero_mem' := rfl
  neg_mem' := by
    rintro a ha
    change -(a 1 0) = 0
    rw [show a 1 0 = 0 from ha, neg_zero]

theorem wSub₁_le_wSub₂ : wSub₁ F ≤ wSub₂ F := fun _ hv => hv.2

theorem wSub₂_le_wSub₃ : wSub₂ F ≤ wSub₃ F := fun v (hv : v 1 = 0) => by
  change v 1 0 = 0
  rw [hv]
  rfl

theorem map_mem_wSub {A : Matrix (Fin 3) (Fin 3) F} (h00 : A 0 0 = 1) (h01 : A 0 1 = 0)
    (h02 : A 0 2 = 0) {v : Fin 2 → Fin 3 → F} :
    (v ∈ wSub₁ F → (fun i => A *ᵥ v i) ∈ wSub₁ F) ∧
      (v ∈ wSub₂ F → (fun i => A *ᵥ v i) ∈ wSub₂ F) ∧
      (v ∈ wSub₃ F → (fun i => A *ᵥ v i) ∈ wSub₃ F) := by
  have hrow : ∀ w : Fin 3 → F, (A *ᵥ w) 0 = w 0 := fun w => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h01, h02]
  refine ⟨fun hv => ⟨?_, ?_⟩, fun hv => ?_, fun hv => ?_⟩
  · change (A *ᵥ v 0) 0 = 0
    rw [hrow, hv.1]
  · change A *ᵥ v 1 = 0
    rw [hv.2, Matrix.mulVec_zero]
  · change A *ᵥ v 1 = 0
    rw [show v 1 = 0 from hv, Matrix.mulVec_zero]
  · change (A *ᵥ v 1) 0 = 0
    rw [hrow, show v 1 0 = 0 from hv]

theorem smul_mem_wSub (c : F) {v : Fin 2 → Fin 3 → F} :
    (v ∈ wSub₁ F → (fun i => Matrix.scalar (Fin 3) c *ᵥ v i) ∈ wSub₁ F) ∧
      (v ∈ wSub₂ F → (fun i => Matrix.scalar (Fin 3) c *ᵥ v i) ∈ wSub₂ F) ∧
      (v ∈ wSub₃ F → (fun i => Matrix.scalar (Fin 3) c *ᵥ v i) ∈ wSub₃ F) := by
  have hs : ∀ w : Fin 3 → F, Matrix.scalar (Fin 3) c *ᵥ w = c • w := fun w => by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    simp
  refine ⟨fun hv => ⟨?_, ?_⟩, fun hv => ?_, fun hv => ?_⟩
  · change (Matrix.scalar (Fin 3) c *ᵥ v 0) 0 = 0
    rw [hs, Pi.smul_apply, hv.1, smul_zero]
  · change Matrix.scalar (Fin 3) c *ᵥ v 1 = 0
    rw [hv.2, Matrix.mulVec_zero]
  · change Matrix.scalar (Fin 3) c *ᵥ v 1 = 0
    rw [show v 1 = 0 from hv, Matrix.mulVec_zero]
  · change (Matrix.scalar (Fin 3) c *ᵥ v 1) 0 = 0
    rw [hs, Pi.smul_apply, show v 1 0 = 0 from hv, smul_zero]

theorem le_normalizer_qSub_self [Finite G] (Q : Subgroup G)
    (β₂ : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)) (W : AddSubgroup (Fin 2 → Fin 3 → F)) :
    Q ≤ Subgroup.normalizer ((qSub Q β₂ W : Subgroup G) : Set G) := by
  intro q hq
  refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxQ, hxW⟩ := hx
  have hqx : q * x * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hxQ) (Q.inv_mem hq)
  refine ⟨hqx, ?_⟩
  have e : (⟨q * x * q⁻¹, hqx⟩ : ↥Q) = ⟨q, hq⟩ * ⟨x, hxQ⟩ * (⟨q, hq⟩ : ↥Q)⁻¹ := rfl
  rw [e, map_mul β₂, map_mul β₂, map_inv β₂, toAdd_mul, toAdd_mul, toAdd_inv, add_comm,
    ← add_assoc, neg_add_cancel, zero_add]
  exact hxW

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem moduleAct_K₂ {k : G} (hk : k ∈ K₂) :
    moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 0 0 = 1 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 0 1 = 0 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 0 2 = 0 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 1 1 =
        (s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 1 2 =
        -(s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 2 1 =
        -(s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
      moduleAct true (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) 2 2 =
        (s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have hk' : k⁻¹ ∈ K₂ := K₂.inv_mem hk
  have hinv : ((((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) =
      ((α ⟨k⁻¹, s.K₂_le_K hk'⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) := by
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  obtain ⟨h00, h10, h20⟩ := s.α_entries hk'
  have hlev := s.levi_coe ⟨k⁻¹, hk'⟩
  have hl : s.levi ⟨k⁻¹, hk'⟩ = (s.levi ⟨k, hk⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [hl, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] at hlev
  have e : ∀ i j : Fin 2, (((α ⟨k⁻¹, s.K₂_le_K hk'⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i.succ j.succ =
        (!![(s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 1 1,
          -(s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 0 1;
          -(s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 1 0,
          (s.levi ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) 0 0] : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    exact (congrFun (congrFun hlev i) j).symm
  simp only [moduleAct, ↓reduceIte, hinv, Matrix.transpose_apply]
  refine ⟨h00, h10, h20, ?_, ?_, ?_, ?_⟩
  · simpa using e 0 0
  · simpa using e 1 0
  · simpa using e 0 1
  · simpa using e 1 1

theorem moduleAct_zpow_y (hm : m = 2) (j : ℤ) (hj : y ^ j ∈ K) :
    moduleAct true (((α ⟨y ^ j, hj⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) =
      Matrix.scalar (Fin 3) (((μ ^ j)⁻¹ : Fˣ) : F) := by
  have hinv : ((((α ⟨y ^ j, hj⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) =
      ((α ⟨y ^ (-j), Subgroup.zpow_mem _ s.y_mem (-j)⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) := by
    rw [← Subgroup.coe_inv, ← map_inv]
    congr 2
    exact Subtype.ext (zpow_neg y j).symm
  simp only [moduleAct, ↓reduceIte, hinv]
  rw [s.coe_α_zpow_y hm (-j), zpow_neg, Matrix.scalar_apply, Matrix.diagonal_transpose]

variable {β₂ : ↥(q4311 I K) →* Multiplicative (Fin 2 → Fin 3 → F)}
  (hβ₂a : ∀ (a : ↥K) (u v : ↥(q4311 I K)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
    Multiplicative.toAdd (β₂ v) i =
      (moduleAct true ((α a : ↥(StatedSL 3 F)) : GL (Fin 3) F)) *ᵥ
        Multiplicative.toAdd (β₂ u) i)
include hβ₂a

theorem le_normalizer_qSub (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    {W : AddSubgroup (Fin 2 → Fin 3 → F)}
    (hW : ∀ (A : Matrix (Fin 3) (Fin 3) F), A 0 0 = 1 → A 0 1 = 0 → A 0 2 = 0 →
      ∀ v ∈ W, (fun i => A *ᵥ v i) ∈ W)
    (hWs : ∀ c : F, ∀ v ∈ W, (fun i => Matrix.scalar (Fin 3) c *ᵥ v i) ∈ W) :
    K₂ ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer ((L4316.qSub (q4311 I K) β₂ W : Subgroup G) : Set G) := by
  have hQN := s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39
  have key : ∀ g (hg : g ∈ K), (∀ v ∈ W, (fun i =>
      moduleAct true (((α ⟨g, hg⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) *ᵥ v i) ∈ W) →
      g ∈ Subgroup.normalizer ((L4316.qSub (q4311 I K) β₂ W : Subgroup G) : Set G) := by
    intro g hg hA
    refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨hxQ, hxW⟩ := hx
    have hgx : g * x * g⁻¹ ∈ q4311 I K := (Subgroup.mem_normalizer_iff.mp (hQN hg) x).mp hxQ
    refine ⟨hgx, ?_⟩
    have h1 : Multiplicative.toAdd (β₂ ⟨_, hgx⟩) = fun i =>
        moduleAct true (((α ⟨g, hg⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) *ᵥ
          Multiplicative.toAdd (β₂ ⟨x, hxQ⟩) i := by
      funext i
      exact hβ₂a ⟨g, hg⟩ ⟨x, hxQ⟩ ⟨_, hgx⟩ rfl i
    rw [h1]
    exact hA _ hxW
  refine _root_.sup_le (fun k hk => ?_) (Subgroup.zpowers_le.mpr ?_)
  · obtain ⟨h00, h01, h02, -⟩ := s.moduleAct_K₂ hk
    exact key k (s.K₂_le_K hk) fun v hv => hW _ h00 h01 h02 v hv
  · have hyK : y ^ (1 : ℤ) ∈ K := Subgroup.zpow_mem _ s.y_mem 1
    have := key (y ^ (1 : ℤ)) hyK fun v hv => by
      rw [s.moduleAct_zpow_y hm 1 hyK]
      exact hWs _ v hv
    simpa using this

theorem natEig_Q₁ (hm : m = 2) (j : ℤ) (hβ₂s : Function.Surjective β₂)
    (hβ₂k : β₂.ker = (u4311 I K).subgroupOf (q4311 I K)) :
    IsNatEigSection K₂ (y ^ j) s.leviS (u4311 I K)
      (L4316.qSub (q4311 I K) β₂ (L4316.wSub₁ F)) (((μ ^ j)⁻¹ : Fˣ) : F) := by
  classical
  set Q₁ := L4316.qSub (q4311 I K) β₂ (L4316.wSub₁ F) with hQ₁
  have hle : Q₁ ≤ q4311 I K := L4316.qSub_le _ _ _
  let pr : (Fin 2 → Fin 3 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => ![-(v 0 2), v 0 1]
      map_zero' := by ext i; fin_cases i <;> simp
      map_add' := fun v w => by ext i; fin_cases i <;> simp [add_comm] }
  have hval : ∀ x : ↥Q₁, Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x) =
        ![-(Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 0 2),
          Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 0 1] := fun x => rfl
  refine ⟨(AddMonoidHom.toMultiplicative pr).comp (β₂.comp (Subgroup.inclusion hle)),
    fun w => ?_, fun x => ?_, fun k x x' hx => ?_, fun x x' hx => ?_⟩
  · set w' := Multiplicative.toAdd w with hw'
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (Pi.single (0 : Fin 2) ![0, w' 1, -(w' 0)]))
    have hqQ₁ : (q : G) ∈ Q₁ := ⟨q.2, by
      rw [show (⟨(q : G), q.2⟩ : ↥(q4311 I K)) = q from rfl, hq, toAdd_ofAdd]
      exact ⟨by simp, by simp⟩⟩
    refine ⟨⟨q, hqQ₁⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hval, show Subgroup.inclusion hle ⟨(q : G), hqQ₁⟩ = q from rfl, hq, toAdd_ofAdd, ← hw']
    ext i
    fin_cases i <;> simp
  · have hW : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) ∈ L4316.wSub₁ F := x.2.2
    have hv0 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 0 0 = 0 := hW.1
    have hv1 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 = 0 := hW.2
    have hU : (x : G) ∈ u4311 I K ↔ Subgroup.inclusion hle x ∈ β₂.ker := by
      rw [hβ₂k, Subgroup.mem_subgroupOf]
      rfl
    rw [hU, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [hval, toAdd_one] at h1
      have ha := congrFun h1 0
      have hb := congrFun h1 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero] at ha hb
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      ext i l
      fin_cases i
      · fin_cases l
        · exact hv0
        · exact hb
        · exact ha
      · simp [hv1]
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hval, h, toAdd_one, toAdd_one]
      ext i
      fin_cases i <;> simp
  · have hW : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) ∈ L4316.wSub₁ F := x.2.2
    have hv0 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 0 0 = 0 := hW.1
    have h1 := hβ₂a ⟨k, s.K₂_le_K k.2⟩ (Subgroup.inclusion hle x) (Subgroup.inclusion hle x')
      hx 0
    obtain ⟨-, -, -, h11, h12, h21, h22⟩ := s.moduleAct_K₂ k.2
    change Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x') =
        ((Matrix.SpecialLinearGroup.toGL (s.levi k) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
            (β₂.comp (Subgroup.inclusion hle))) x)
    rw [hval, hval, h1, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h11, h12, h21, h22,
        hv0]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h11, h12, h21, h22,
        hv0]
      ring
  · have hjK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
    have h1 := hβ₂a ⟨y ^ j, hjK⟩ (Subgroup.inclusion hle x) (Subgroup.inclusion hle x') hx 0
    rw [s.moduleAct_zpow_y hm j hjK] at h1
    change Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x') = (((μ ^ j)⁻¹ : Fˣ) : F) •
        Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
          (β₂.comp (Subgroup.inclusion hle))) x)
    rw [hval, hval, h1]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem natEig_Q₃ (hm : m = 2) (j : ℤ) (hβ₂s : Function.Surjective β₂) :
    IsNatEigSection K₂ (y ^ j) s.leviS (L4316.qSub (q4311 I K) β₂ (L4316.wSub₂ F))
      (L4316.qSub (q4311 I K) β₂ (L4316.wSub₃ F)) (((μ ^ j)⁻¹ : Fˣ) : F) := by
  classical
  set Q₃ := L4316.qSub (q4311 I K) β₂ (L4316.wSub₃ F) with hQ₃
  have hle : Q₃ ≤ q4311 I K := L4316.qSub_le _ _ _
  let pr : (Fin 2 → Fin 3 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => ![-(v 1 2), v 1 1]
      map_zero' := by ext i; fin_cases i <;> simp
      map_add' := fun v w => by ext i; fin_cases i <;> simp [add_comm] }
  have hval : ∀ x : ↥Q₃, Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x) =
        ![-(Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 2),
          Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 1] := fun x => rfl
  refine ⟨(AddMonoidHom.toMultiplicative pr).comp (β₂.comp (Subgroup.inclusion hle)),
    fun w => ?_, fun x => ?_, fun k x x' hx => ?_, fun x x' hx => ?_⟩
  · set w' := Multiplicative.toAdd w with hw'
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (Pi.single (1 : Fin 2) ![0, w' 1, -(w' 0)]))
    have hqQ₃ : (q : G) ∈ Q₃ := ⟨q.2, by
      rw [show (⟨(q : G), q.2⟩ : ↥(q4311 I K)) = q from rfl, hq, toAdd_ofAdd]
      change (Pi.single (1 : Fin 2) ![0, w' 1, -(w' 0)] : Fin 2 → Fin 3 → F) 1 0 = 0
      simp⟩
    refine ⟨⟨q, hqQ₃⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hval, show Subgroup.inclusion hle ⟨(q : G), hqQ₃⟩ = q from rfl, hq, toAdd_ofAdd, ← hw']
    ext i
    fin_cases i <;> simp
  · have hW : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) ∈ L4316.wSub₃ F := x.2.2
    have hv0 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 0 = 0 := hW
    constructor
    · intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [hval, toAdd_one] at h1
      have ha := congrFun h1 0
      have hb := congrFun h1 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero] at ha hb
      refine ⟨hle x.2, ?_⟩
      change Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 = 0
      ext l
      fin_cases l
      · exact hv0
      · exact hb
      · exact ha
    · intro h
      have h1 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 = 0 := h.2
      apply Multiplicative.toAdd.injective
      rw [hval, toAdd_one, h1]
      ext i
      fin_cases i <;> simp
  · have hW : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) ∈ L4316.wSub₃ F := x.2.2
    have hv0 : Multiplicative.toAdd (β₂ (Subgroup.inclusion hle x)) 1 0 = 0 := hW
    have h1 := hβ₂a ⟨k, s.K₂_le_K k.2⟩ (Subgroup.inclusion hle x) (Subgroup.inclusion hle x')
      hx 1
    obtain ⟨-, -, -, h11, h12, h21, h22⟩ := s.moduleAct_K₂ k.2
    change Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x') =
        ((Matrix.SpecialLinearGroup.toGL (s.levi k) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
            (β₂.comp (Subgroup.inclusion hle))) x)
    rw [hval, hval, h1, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h11, h12, h21, h22,
        hv0]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h11, h12, h21, h22,
        hv0]
      ring
  · have hjK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
    have h1 := hβ₂a ⟨y ^ j, hjK⟩ (Subgroup.inclusion hle x) (Subgroup.inclusion hle x') hx 1
    rw [s.moduleAct_zpow_y hm j hjK] at h1
    change Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
      (β₂.comp (Subgroup.inclusion hle))) x') = (((μ ^ j)⁻¹ : Fˣ) : F) •
        Multiplicative.toAdd (((AddMonoidHom.toMultiplicative pr).comp
          (β₂.comp (Subgroup.inclusion hle))) x)
    rw [hval, hval, h1]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem comm_mem_qSub {Wa Wb : AddSubgroup (Fin 2 → Fin 3 → F)}
    (hWW : ∀ (A : Matrix (Fin 3) (Fin 3) F), A 0 0 = 1 → A 0 1 = 0 → A 0 2 = 0 →
      ∀ v ∈ Wa, (fun i => A *ᵥ v i) - v ∈ Wb)
    (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {k : G} (hk : k ∈ K₂) {x : G}
    (hx : x ∈ L4316.qSub (q4311 I K) β₂ Wa) :
    k * x * k⁻¹ * x⁻¹ ∈ L4316.qSub (q4311 I K) β₂ Wb := by
  obtain ⟨hxQ, hxW⟩ := hx
  have hkK := s.K₂_le_K hk
  have hQN := s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39
  have hkx : k * x * k⁻¹ ∈ q4311 I K := (Subgroup.mem_normalizer_iff.mp (hQN hkK) x).mp hxQ
  have hmem : k * x * k⁻¹ * x⁻¹ ∈ q4311 I K := (q4311 I K).mul_mem hkx ((q4311 I K).inv_mem hxQ)
  refine ⟨hmem, ?_⟩
  have e : (⟨k * x * k⁻¹ * x⁻¹, hmem⟩ : ↥(q4311 I K)) = ⟨_, hkx⟩ * (⟨x, hxQ⟩ : ↥(q4311 I K))⁻¹ :=
    rfl
  have h1 : Multiplicative.toAdd (β₂ ⟨_, hkx⟩) = fun i =>
      moduleAct true (((α ⟨k, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) *ᵥ
        Multiplicative.toAdd (β₂ ⟨x, hxQ⟩) i := by
    funext i
    exact hβ₂a ⟨k, hkK⟩ ⟨x, hxQ⟩ ⟨_, hkx⟩ rfl i
  rw [e, map_mul β₂, map_inv β₂, toAdd_mul, toAdd_inv, h1, ← sub_eq_add_neg]
  obtain ⟨h00, h01, h02, -⟩ := s.moduleAct_K₂ hk
  exact hWW _ h00 h01 h02 _ hxW

end Setting4315

namespace L4316

variable {G : Type} [Group G] {Y K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F]
  {α₀ : ↥K →* ↥(StatedSL n F)}

theorem lt_of_natEig {C₁ C₂ : Subgroup G} {a : F} (h : IsNatEigSection K x α₀ C₁ C₂ a)
    (hle : C₁ ≤ C₂) (hn : 2 ≤ n) (hα : Function.Surjective α₀)
    (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) : C₁ < C₂ := by
  refine lt_of_le_of_ne hle fun heq => h.not_centralized hn hα hKC fun k hk c hc => ?_
  rw [heq]
  have h1 : k * c * k⁻¹ ∈ C₂ := (Subgroup.mem_normalizer_iff.mp (hKC hk) c).mp hc
  exact C₂.mul_mem h1 (C₂.inv_mem hc)

theorem le_normalizer_bot (A : Subgroup G) :
    A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro h1
    calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end L4316

namespace Setting4315

variable {G : Type} [Group G] [Finite G]
variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem exists_labSeries_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) (j : ℤ) :
    ∃ l : List (Subgroup G × Option F),
      IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (y ^ j) s.leviS ⊥ l R₂ ∧
        labMultiset l = ({((μ ^ j : Fˣ) : F), ((μ ^ j : Fˣ) : F)⁻¹, ((μ ^ j : Fˣ) : F)⁻¹, 1} :
          Multiset F) := by
  classical
  obtain ⟨-, -, β₂, hβ₂s, hβ₂k, hβ₂a⟩ := s.dualQ
  set Y := K₂ ⊔ Subgroup.zpowers y with hY
  set Q₁ := L4316.qSub (q4311 I K) β₂ (L4316.wSub₁ F) with hQ₁
  set Q₂ := L4316.qSub (q4311 I K) β₂ (L4316.wSub₂ F) with hQ₂
  set Q₃ := L4316.qSub (q4311 I K) β₂ (L4316.wSub₃ F) with hQ₃
  have hKY : K₂ ≤ Y := le_sup_left
  have hYZ : Y ≤ Subgroup.normalizer (ZS : Set G) := _root_.sup_le
    ((s.K₂_le_KZ.trans s.KZ_cent).trans (Subgroup.centralizer_le_normalizer _))
    s.Y_le_normalizer_ZS
  have hYU := s.le_normalizer_U
  have hYQ := s.le_normalizer_Q h135 hR hC h37 h38 h39
  have hYQi : ∀ {W : AddSubgroup (Fin 2 → Fin 3 → F)},
      (∀ (A : Matrix (Fin 3) (Fin 3) F), A 0 0 = 1 → A 0 1 = 0 → A 0 2 = 0 →
        ∀ v ∈ W, (fun i => A *ᵥ v i) ∈ W) →
      (∀ c : F, ∀ v ∈ W, (fun i => Matrix.scalar (Fin 3) c *ᵥ v i) ∈ W) →
      Y ≤ Subgroup.normalizer ((L4316.qSub (q4311 I K) β₂ W : Subgroup G) : Set G) :=
    fun hW hWs => s.le_normalizer_qSub hβ₂a h135 hR hC h37 h38 h39 hm hW hWs
  have hY₁ : Y ≤ Subgroup.normalizer (Q₁ : Set G) :=
    hYQi (fun A h0 h1 h2 v hv => (L4316.map_mem_wSub h0 h1 h2).1 hv)
      (fun c v hv => (L4316.smul_mem_wSub c).1 hv)
  have hY₂ : Y ≤ Subgroup.normalizer (Q₂ : Set G) :=
    hYQi (fun A h0 h1 h2 v hv => (L4316.map_mem_wSub h0 h1 h2).2.1 hv)
      (fun c v hv => (L4316.smul_mem_wSub c).2.1 hv)
  have hY₃ : Y ≤ Subgroup.normalizer (Q₃ : Set G) :=
    hYQi (fun A h0 h1 h2 v hv => (L4316.map_mem_wSub h0 h1 h2).2.2 hv)
      (fun c v hv => (L4316.smul_mem_wSub c).2.2 hv)
  have hQN : ∀ W, q4311 I K ≤
      Subgroup.normalizer ((L4316.qSub (q4311 I K) β₂ W : Subgroup G) : Set G) :=
    fun W => L4316.le_normalizer_qSub_self (q4311 I K) β₂ W
  have hQU : q4311 I K ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) :=
    (s.q4311_le_K).trans s.K_U
  have hUQ₁ : u4311 I K ≤ Q₁ := fun u hu => ⟨hu.1, by
    have h1 : (⟨u, hu.1⟩ : ↥(q4311 I K)) ∈ β₂.ker := by
      rw [hβ₂k, Subgroup.mem_subgroupOf]
      exact hu
    rw [MonoidHom.mem_ker.mp h1, toAdd_one]
    exact (L4316.wSub₁ F).zero_mem⟩
  have hQ₁₂ : Q₁ ≤ Q₂ := L4316.qSub_mono L4316.wSub₁_le_wSub₂
  have hQ₂₃ : Q₂ ≤ Q₃ := L4316.qSub_mono L4316.wSub₂_le_wSub₃
  have hQ₃Q : Q₃ ≤ q4311 I K := L4316.qSub_le _ _ _
  obtain ⟨l₀, hl₀, hl₀n⟩ := L4316.exists_isLabSeries_central (Y := Y) (x := y ^ j)
    (α₀ := s.leviS) bot_le (L4316.le_normalizer_bot ZS) (L4316.le_normalizer_bot Y) hYZ
    (fun k hk z hz => by
      have hc := Subgroup.mem_centralizer_iff.mp (s.KZ_cent (s.K₂_le_KZ hk)) z hz
      rw [Subgroup.mem_bot, ← hc, mul_inv_cancel_right, mul_inv_cancel])
  have hfU := s.isLabFactor_U hm j
  have hn1 := s.natEig_Q₁ hβ₂a hm j hβ₂s hβ₂k
  have hfQ₁ : IsLabFactor Y K₂ (y ^ j) s.leviS (u4311 I K) Q₁ (some (((μ ^ j)⁻¹ : Fˣ) : F)) :=
    L4316.isLabFactor_of_natEig hn1 (L4316.lt_of_natEig hn1 hUQ₁ le_rfl s.leviS_surjective
      (hKY.trans hY₁)) (hQ₁.symm ▸ (L4316.qSub_le _ _ _).trans hQU) hYU hY₁ hKY le_rfl
      s.leviS_surjective
  obtain ⟨l₂, hl₂, hl₂n⟩ := L4316.exists_isLabSeries_central (Y := Y) (x := y ^ j)
    (α₀ := s.leviS) hQ₁₂ ((L4316.qSub_le _ _ _).trans (hQN _)) hY₁ hY₂
    (fun k hk x hx => s.comm_mem_qSub hβ₂a (Wa := L4316.wSub₂ F) (Wb := L4316.wSub₁ F)
      (fun A h0 h1 h2 v hv => ⟨by
        change (A *ᵥ v 0) 0 - v 0 0 = 0
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2], by
        change A *ᵥ v 1 - v 1 = 0
        rw [show v 1 = 0 from hv, Matrix.mulVec_zero, sub_zero]⟩)
      h135 hR hC h37 h38 h39 hk hx)
  have hn3 := s.natEig_Q₃ hβ₂a hm j hβ₂s
  have hfQ₃ : IsLabFactor Y K₂ (y ^ j) s.leviS Q₂ Q₃ (some (((μ ^ j)⁻¹ : Fˣ) : F)) :=
    L4316.isLabFactor_of_natEig hn3 (L4316.lt_of_natEig hn3 hQ₂₃ le_rfl s.leviS_surjective
      (hKY.trans hY₃)) ((L4316.qSub_le _ _ _).trans (hQN _)) hY₂ hY₃ hKY le_rfl
      s.leviS_surjective
  obtain ⟨l₄, hl₄, hl₄n⟩ := L4316.exists_isLabSeries_central (Y := Y) (x := y ^ j)
    (α₀ := s.leviS) hQ₃Q (hQN _) hY₃ hYQ
    (fun k hk x hx => s.comm_mem_qSub hβ₂a (Wa := ⊤) (Wb := L4316.wSub₃ F)
      (fun A h0 h1 h2 v _ => by
        change (A *ᵥ v 1) 0 - v 1 0 = 0
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2])
      h135 hR hC h37 h38 h39 hk ⟨hx, AddSubgroup.mem_top _⟩)
  have hfR := s.isLabFactor_R₂ h135 hR hC h37 h38 h39 hm j
  refine ⟨l₀ ++ [(u4311 I K, some ((μ ^ j : Fˣ) : F))] ++ [(Q₁, some (((μ ^ j)⁻¹ : Fˣ) : F))] ++
    l₂ ++ [(Q₃, some (((μ ^ j)⁻¹ : Fˣ) : F))] ++ l₄ ++ [(R₂, some 1)], ?_, ?_⟩
  · exact (((((hl₀.append (isLabSeries_singleton hfU)).append (isLabSeries_singleton hfQ₁)).append
      hl₂).append (isLabSeries_singleton hfQ₃)).append hl₄).append (isLabSeries_singleton hfR)
  · simp only [labMultiset_append, labMultiset_eq_zero_of_forall hl₀n,
      labMultiset_eq_zero_of_forall hl₂n, labMultiset_eq_zero_of_forall hl₄n, labMultiset_cons,
      labMultiset_nil, Option.elim, zero_add, add_zero, Units.val_inv_eq_inv_val]
    simp [Multiset.insert_eq_cons, Multiset.singleton_add, Multiset.cons_add]

end Setting4315

end CFSG.Quasithin.H13.Ch4
