module

public import CFSG.Quasithin.Vol2.Ch3Sec3CZCore
public import CFSG.Quasithin.Background.S1549DL3F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace CZL32

@[expose] def e1 : L3.Vec := ![1, 0, 0]

@[expose] def e2 : L3.Vec := ![0, 1, 0]

@[expose] def P12 : Finset L3.Vec := {0, e1, e2, e1 + e2}

@[expose] def bSub : Subgroup L3.Γ := L3.ptSub e1 ⊓ L3.stabSub P12

theorem mem_bSub {g : L3.Γ} :
    g ∈ bSub ↔ L3.act g e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12 := Iff.rfl

theorem card_bSub_filter : (Finset.univ.filter fun g : L3.Γ =>
    L3.act g e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12).card = 8 := by
  decide +kernel

theorem card_bSub : Nat.card bSub = 8 := by
  rw [← card_bSub_filter, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_bSub])

theorem bSub_le_ptSub : bSub ≤ L3.ptSub e1 := inf_le_left

theorem isPGroup_bSub : IsPGroup 2 ↥bSub :=
  IsPGroup.of_card (n := 3) (by rw [card_bSub]; rfl)

theorem not_two_dvd_index_bSub : ¬ 2 ∣ bSub.index := by
  have := Subgroup.card_mul_index bSub
  rw [card_bSub, card_L3Γ] at this
  omega

theorem card_ptSub_filter :
    (Finset.univ.filter fun g : L3.Γ => L3.act g e1 = e1).card = 24 := by
  decide +kernel

theorem card_ptSub : Nat.card (L3.ptSub e1) = 24 := by
  rw [← card_ptSub_filter, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [L3.mem_ptSub])

theorem add_mem_pair : ∀ x y : L3.Vec, x ∈ ({0, e1} : Finset L3.Vec) →
    y ∈ ({0, e1} : Finset L3.Vec) → x + y ∈ ({0, e1} : Finset L3.Vec) := by
  decide +kernel

theorem neg_mem_pair : ∀ x : L3.Vec, x ∈ ({0, e1} : Finset L3.Vec) →
    -x ∈ ({0, e1} : Finset L3.Vec) := by
  decide +kernel

@[expose] def rSub : Subgroup L3.Γ where
  carrier := {g | ∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)}
  one_mem' := fun v => by simp [L3.act_one]
  mul_mem' := fun {a b} ha hb v => by
    have e : L3.act (a * b) v - v = (L3.act a (L3.act b v) - L3.act b v) + (L3.act b v - v) := by
      rw [L3.act_mul]
      abel
    rw [e]
    exact add_mem_pair _ _ (ha (L3.act b v)) (hb v)
  inv_mem' := fun {a} ha v => by
    have h1 := ha (L3.act a⁻¹ v)
    rw [L3.act_act_inv] at h1
    have e : L3.act a⁻¹ v - v = -(v - L3.act a⁻¹ v) := by abel
    rw [e]
    exact neg_mem_pair _ h1

theorem mem_rSub {g : L3.Γ} : g ∈ rSub ↔ ∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec) :=
  Iff.rfl

theorem card_rSub_filter : (Finset.univ.filter fun g : L3.Γ =>
    ∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)).card = 4 := by
  decide +kernel

theorem card_rSub : Nat.card rSub = 4 := by
  rw [← card_rSub_filter, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_rSub])

theorem rSub_check : ∀ g : L3.Γ, (∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)) →
    L3.act g e1 = e1 ∧ g * g = 1 := by
  decide +kernel

theorem rSub_le_ptSub : rSub ≤ L3.ptSub e1 := fun g hg => (rSub_check g hg).1

theorem sq_eq_one_of_mem_rSub {g : L3.Γ} (hg : g ∈ rSub) : g * g = 1 := (rSub_check g hg).2

theorem act_mem_pair {g : L3.Γ} (hg : g ∈ L3.ptSub e1) {x : L3.Vec}
    (hx : x ∈ ({0, e1} : Finset L3.Vec)) : L3.act g x ∈ ({0, e1} : Finset L3.Vec) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl (L3.act_zero g)
  · exact Or.inr hg

theorem ptSub_le_normalizer : L3.ptSub e1 ≤ Subgroup.normalizer (rSub : Set L3.Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_rSub, mem_rSub]
  constructor
  · intro hx v
    have e : L3.act (g * x * g⁻¹) v - v =
        L3.act g (L3.act x (L3.act g⁻¹ v) - L3.act g⁻¹ v) := by
      simp only [L3.act_sub, L3.act_mul, L3.act_act_inv]
    rw [e]
    exact act_mem_pair hg (hx _)
  · intro hx v
    have hg' : g⁻¹ ∈ L3.ptSub e1 := (L3.ptSub e1).inv_mem hg
    have e : L3.act x v - v =
        L3.act g⁻¹ (L3.act (g * x * g⁻¹) (L3.act g v) - L3.act g v) := by
      simp only [L3.act_sub, L3.act_mul, L3.act_inv_act]
    rw [e]
    exact act_mem_pair hg' (hx _)

@[expose] def aW : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def bW : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

theorem aW_mem : aW ∈ L3.ptSub e1 := by
  rw [L3.mem_ptSub]
  decide +kernel

theorem bW_mem : bW ∈ L3.ptSub e1 := by
  rw [L3.mem_ptSub]
  decide +kernel

theorem comm_not_mem : (bW * aW)⁻¹ * (aW * bW) ∉ rSub := by
  rw [mem_rSub]
  decide +kernel

@[expose] def b1 : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def b2 : L3.Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

theorem b1_mem : b1 ∈ bSub := by
  rw [mem_bSub]
  decide +kernel

theorem b2_mem : b2 ∈ bSub := by
  rw [mem_bSub]
  decide +kernel

theorem fix_B : ∀ v : L3.Vec, L3.act b1 v = v → L3.act b2 v = v → v = 0 ∨ v = e1 := by
  decide +kernel

theorem zmod2_eq_one : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem matrix_ext {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v, Matrix.mulVec A v = Matrix.mulVec B v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

section Rho3

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def conjU (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) : ↥(blockU L) :=
  ⟨(g : G) * u * (g : G)⁻¹, Mod32.conj_mem_blockU g.2 u⟩

theorem coe_conjU (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    (conjU g u : G) = (g : G) * u * (g : G)⁻¹ := rfl

variable (β : ↥(blockU L) →* Multiplicative L3.Vec) (hβs : Function.Surjective β)
  (hβk : β.ker = (blockZ L).subgroupOf (blockU L))

noncomputable def lin (g : ↥(Subgroup.normalizer (L : Set G))) (v : L3.Vec) : L3.Vec :=
  Multiplicative.toAdd (β (conjU g (Classical.choose (hβs (Multiplicative.ofAdd v)))))

include hβs in
theorem exists_beta (v : L3.Vec) : ∃ u, Multiplicative.toAdd (β u) = v :=
  ⟨_, congrArg Multiplicative.toAdd (Classical.choose_spec (hβs (Multiplicative.ofAdd v)))⟩

include hβk in
theorem lin_beta (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    lin β hβs g (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (conjU g u)) := by
  unfold lin
  set u' := Classical.choose (hβs (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) with hu'
  have h1 : β u' = β u :=
    Classical.choose_spec (hβs (Multiplicative.ofAdd (Multiplicative.toAdd (β u))))
  have h2 : u'⁻¹ * u ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1]
    exact inv_mul_cancel _
  rw [hβk, Subgroup.mem_subgroupOf] at h2
  have h3 : (conjU g u')⁻¹ * conjU g u ∈ β.ker := by
    rw [hβk, Subgroup.mem_subgroupOf]
    have e : (((conjU g u')⁻¹ * conjU g u : ↥(blockU L)) : G) =
        (g : G) * ((u'⁻¹ * u : ↥(blockU L)) : G) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjU]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ g.2) _).mp h2
  rw [MonoidHom.mem_ker, map_mul, map_inv] at h3
  rw [inv_mul_eq_one.mp h3]

include hβk in
theorem lin_add (g : ↥(Subgroup.normalizer (L : Set G))) (v w : L3.Vec) :
    lin β hβs g (v + w) = lin β hβs g v + lin β hβs g w := by
  obtain ⟨u, rfl⟩ := exists_beta β hβs v
  obtain ⟨u', rfl⟩ := exists_beta β hβs w
  rw [← toAdd_mul, ← map_mul β, lin_beta β hβs hβk, lin_beta β hβs hβk, lin_beta β hβs hβk,
    ← toAdd_mul, ← map_mul β]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_conjU]
  group

include hβk in
theorem lin_mul (g h : ↥(Subgroup.normalizer (L : Set G))) (v : L3.Vec) :
    lin β hβs (g * h) v = lin β hβs g (lin β hβs h v) := by
  obtain ⟨u, rfl⟩ := exists_beta β hβs v
  rw [lin_beta β hβs hβk, lin_beta β hβs hβk, lin_beta β hβs hβk]
  congr 2
  apply Subtype.ext
  simp only [coe_conjU, Subgroup.coe_mul]
  group

include hβk in
theorem lin_one (v : L3.Vec) : lin β hβs 1 v = v := by
  obtain ⟨u, rfl⟩ := exists_beta β hβs v
  rw [lin_beta β hβs hβk]
  congr 2
  apply Subtype.ext
  simp [coe_conjU]

include hβk in
theorem lin_zero (g : ↥(Subgroup.normalizer (L : Set G))) : lin β hβs g 0 = 0 := by
  have h := lin_beta β hβs hβk g 1
  have e : conjU g (1 : ↥(blockU L)) = 1 := Subtype.ext (by simp [coe_conjU])
  rw [e, map_one] at h
  exact h

include hβk in
theorem lin_smul (g : ↥(Subgroup.normalizer (L : Set G))) (c : ZMod 2) (v : L3.Vec) :
    lin β hβs g (c • v) = c • lin β hβs g v := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, lin_zero β hβs hβk]
  · rw [one_smul, one_smul]

noncomputable def linMap (g : ↥(Subgroup.normalizer (L : Set G))) :
    L3.Vec →ₗ[ZMod 2] L3.Vec where
  toFun := lin β hβs g
  map_add' := lin_add β hβs hβk g
  map_smul' := lin_smul β hβs hβk g

noncomputable def mat (g : ↥(Subgroup.normalizer (L : Set G))) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  LinearMap.toMatrix' (linMap β hβs hβk g)

theorem mat_mulVec (g : ↥(Subgroup.normalizer (L : Set G))) (v : L3.Vec) :
    Matrix.mulVec (mat β hβs hβk g) v = lin β hβs g v := by
  rw [mat, LinearMap.toMatrix'_mulVec]
  rfl

theorem mat_mul (g h : ↥(Subgroup.normalizer (L : Set G))) :
    mat β hβs hβk (g * h) = mat β hβs hβk g * mat β hβs hβk h :=
  matrix_ext fun v => by
    rw [← Matrix.mulVec_mulVec, mat_mulVec, mat_mulVec, mat_mulVec, lin_mul β hβs hβk]

theorem mat_one : mat β hβs hβk 1 = 1 :=
  matrix_ext fun v => by rw [mat_mulVec, lin_one β hβs hβk, Matrix.one_mulVec]

theorem det_mat (g : ↥(Subgroup.normalizer (L : Set G))) : (mat β hβs hβk g).det = 1 := by
  have h : mat β hβs hβk g * mat β hβs hβk g⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact zmod2_eq_one _ _ h2

noncomputable def rho3 : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ where
  toFun g := ⟨mat β hβs hβk g, det_mat β hβs hβk g⟩
  map_one' := Subtype.ext (mat_one β hβs hβk)
  map_mul' g h := Subtype.ext (mat_mul β hβs hβk g h)

theorem act_rho3 (g : ↥(Subgroup.normalizer (L : Set G))) (v : L3.Vec) :
    L3.act (rho3 β hβs hβk g) v = lin β hβs g v :=
  mat_mulVec β hβs hβk g v

theorem rho3_equiv (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L))
    (h : (u' : G) = g * u * g⁻¹) :
    Multiplicative.toAdd (β u') = L3.act (rho3 β hβs hβk g) (Multiplicative.toAdd (β u)) := by
  rw [act_rho3, lin_beta β hβs hβk]
  congr 2
  exact Subtype.ext h

theorem rho3_of_mem {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u)))
    (ℓ : ↥L) :
    (rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((α ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  apply matrix_ext
  intro v
  obtain ⟨u, rfl⟩ := exists_beta β hβs v
  rw [← hβe ℓ u (conjU ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ u) rfl]
  exact (act_rho3 β hβs hβk _ _).trans (lin_beta β hβs hβk _ u)

theorem rho3_surj {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hαs : Function.Surjective α)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u)))
    (γ : L3.Γ) : ∃ ℓ, ∃ hℓ : ℓ ∈ L, rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ := by
  obtain ⟨ℓ, hℓ⟩ := hαs ⟨Matrix.SpecialLinearGroup.toGL γ, Subgroup.subset_closure γ.2⟩
  refine ⟨ℓ, ℓ.2, Subtype.ext ?_⟩
  rw [rho3_of_mem β hβs hβk hβe ℓ, hℓ]
  rfl

theorem rho3_ker {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u)))
    (ℓ : ↥L) (h1 : rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1) :
    ℓ ∈ CFSG.pCore 2 ↥L := by
  rw [← hαk, MonoidHom.mem_ker]
  have h4 := rho3_of_mem β hβs hβk hβe ℓ
  rw [h1] at h4
  apply Subtype.ext
  apply Units.ext
  exact h4.symm

end Rho3

variable {G : Type} [Group G]

theorem mem_qL_of_ker [Finite G] {Γ' : Type} [Group Γ'] {T L : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ') (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T)
    (hL : ∀ ℓ : ↥L, ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1 → ℓ ∈ CFSG.pCore 2 ↥L)
    {g : G} (hg : g ∈ L ⊔ T) (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (h1 : ρ ⟨g, hgN⟩ = 1) : g ∈ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  let ρ' : ↥(L ⊔ T) →* Γ' := ρ.comp (Subgroup.inclusion hLTN)
  have hK2 : IsPGroup 2 ↥(ρ'.ker.map (L ⊔ T).subtype) := by
    rintro ⟨_, ⟨k', hk', rfl⟩⟩
    obtain ⟨ℓ, hℓ, t, ht, hkt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp k'.2
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hstep : ∀ n : ℕ, ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨ℓ', hℓ', e⟩ := ih
        refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) ℓ).mp hℓ
        · rw [pow_succ, e]
          group
    obtain ⟨ℓ', hℓ', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkL : (k' : G) ^ 2 ^ a ∈ L := by
      rw [hkt, e]
      exact hℓ'
    have h3 : ρ ⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ = 1 := by
      have e2 : (⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ :
          ↥(Subgroup.normalizer (L : Set G))) = (Subgroup.inclusion hLTN k') ^ 2 ^ a :=
        Subtype.ext (by simp)
      have hk1 : ρ (Subgroup.inclusion hLTN k') = 1 := hk'
      rw [e2, map_pow, hk1, one_pow]
    have hker := hL ⟨_, hkL⟩ h3
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hker⟩
    have h4 : ((k' : G) ^ 2 ^ a) ^ 2 ^ b = 1 :=
      congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hb
    refine ⟨a + b, Subtype.ext ?_⟩
    show (k' : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact h4
  have hgK : g ∈ ρ'.ker.map (L ⊔ T).subtype := ⟨⟨g, hg⟩, h1, rfl⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _)
    (by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective]
      infer_instance) hK2 hgK

theorem mem_image_bSub {T L : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ)
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) (hTidx : ¬ 2 ∣ T.index)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ bSub)
    (hH : Function.Surjective (ρ.comp (Subgroup.inclusion hLTN))) {x : L3.Γ} (hx : x ∈ bSub) :
    ∃ t, ∃ ht : t ∈ T, ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ = x := by
  set f := ρ.comp (Subgroup.inclusion hLTN) with hf
  set I := (T.subgroupOf (L ⊔ T)).map f with hI
  have hle : I ≤ bSub := by
    rintro _ ⟨y, hy, rfl⟩
    exact hρT y hy
  have hodd : ¬ 2 ∣ I.index := by
    have h1 := Subgroup.index_map_dvd (T.subgroupOf (L ⊔ T)) hH
    exact fun h3 => hTidx ((h3.trans h1).trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hmul := Subgroup.card_mul_index I
  rw [card_L3Γ] at hmul
  have hdvd : Nat.card I ∣ 8 := by
    rw [← card_bSub]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨c, hc⟩ : ∃ c, Nat.card I = c := ⟨_, rfl⟩
  rw [hc] at hmul hdvd
  have hc8 : c ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hc8' : c = 8 := by interval_cases c <;> omega
  have hIeq : I = bSub := Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc8', card_bSub])
  rw [← hIeq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, hyx⟩

theorem exists_rho_cZ [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hLn : IsLnBlock L 3)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ,
      (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ bSub) ∧
      (∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
        g ∈ qL L T) ∧
      oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
        oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) (L3.ptSub e1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, α, hαs, hαk, β, hβs, hβk, hβe⟩ := id hLn
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hρα := rho3_of_mem β hβs hβk hβe
  obtain ⟨σ, hσ⟩ : ∃ σ : L3.Γ,
      ∀ t (ht : t ∈ T), σ * rho3 β hβs hβk ⟨t, hTL ht⟩ * σ⁻¹ ∈ bSub := by
    let f : ↥T →* L3.Γ := (rho3 β hβs hβk).comp (Subgroup.inclusion hTL)
    have hf : IsPGroup 2 ↥f.range := hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    let P : Sylow 2 L3.Γ := isPGroup_bSub.toSylow not_two_dvd_index_bSub
    obtain ⟨Q, hQ⟩ := hf.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L3.Γ Q P
    refine ⟨g, fun t ht => ?_⟩
    have h1 : f ⟨t, ht⟩ ∈ (Q : Subgroup L3.Γ) := hQ ⟨⟨t, ht⟩, rfl⟩
    have h2 : g * f ⟨t, ht⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 _) : Subgroup L3.Γ) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hg] at h2
    exact h2
  let ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ :=
    (MulAut.conj σ).toMonoidHom.comp (rho3 β hβs hβk)
  have hρapp : ∀ g, ρ g = σ * rho3 β hβs hβk g * σ⁻¹ := fun _ => rfl
  let β' : ↥(blockU L) →* Multiplicative L3.Vec :=
    (AddMonoidHom.toMultiplicative (AddMonoidHom.mk' (L3.act σ) (L3.act_add σ))).comp β
  have hβ' : ∀ u, Multiplicative.toAdd (β' u) = L3.act σ (Multiplicative.toAdd (β u)) :=
    fun _ => rfl
  have hβk' : β'.ker = (blockZ L).subgroupOf (blockU L) := by
    rw [← hβk]
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : L3.act σ (Multiplicative.toAdd (β u)) = 0 := by
        rw [← hβ', h1]
        rfl
      have h3 := congrArg (L3.act σ⁻¹) h2
      rw [L3.act_inv_act, L3.act_zero] at h3
      exact Multiplicative.toAdd.injective h3
    · intro h1
      apply Multiplicative.toAdd.injective
      rw [hβ', h1]
      exact L3.act_zero σ
  have hβe' : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β' u') = L3.act (ρ g) (Multiplicative.toAdd (β' u)) := by
    intro g u u' hu
    rw [hβ', hβ', rho3_equiv β hβs hβk g u u' hu, hρapp, L3.act_mul, L3.act_inv_act,
      L3.act_mul]
  have hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ := by
    intro γ
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨Matrix.SpecialLinearGroup.toGL (σ⁻¹ * γ * σ),
      Subgroup.subset_closure (σ⁻¹ * γ * σ).2⟩
    refine ⟨ℓ, ℓ.2, ?_⟩
    have e : rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = σ⁻¹ * γ * σ := by
      apply Subtype.ext
      rw [hρα ℓ, hℓ]
      rfl
    rw [hρapp, e]
    group
  have hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T := by
    intro g hg hgN h1
    refine mem_qL_of_ker ρ hTL hT2 (fun ℓ hℓ1 => ?_) hg hgN h1
    rw [← hαk, MonoidHom.mem_ker]
    have h2 : rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1 := by
      have h3 : σ * rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ * σ⁻¹ = 1 := hℓ1
      calc rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ =
            σ⁻¹ * (σ * rho3 β hβs hβk ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ * σ⁻¹) * σ := by group
        _ = 1 := by rw [h3]; group
    have h4 := hρα ℓ
    rw [h2] at h4
    apply Subtype.ext
    apply Units.ext
    exact h4.symm
  have hH : Function.Surjective (ρ.comp (Subgroup.inclusion hLTN)) := by
    intro γ
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  obtain ⟨t₁, ht₁, e₁⟩ := mem_image_bSub ρ hLTN hTidx (fun t ht => hσ t ht) hH b1_mem
  obtain ⟨t₂, ht₂, e₂⟩ := mem_image_bSub ρ hLTN hTidx (fun t ht => hσ t ht) hH b2_mem
  refine ⟨ρ, hσ, hρL, hK, ?_⟩
  refine CZCore.cZ_core (w₀ := e1) (p := L3.ptSub e1) h38 h39 h hshort hTL ρ β' hβk' L3.act
    L3.act_zero hβe'
    (fun v hv => ?_) (fun x hx => hx) (fun x hx => hx)
  apply fix_B
  · rw [← e₁]
    exact hv t₁ ht₁
  · rw [← e₂]
    exact hv t₂ ht₂

theorem xs3_l32 [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLn : IsLnBlock L 3) :
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3)) := by
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  obtain ⟨ρ, hρT, hρL, hK, hX⟩ := exists_rho_cZ h38 h39 h hLn hTL
  have htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have h6 : Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ L3.ptSub e1) =
      6 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ rSub) := by
    rw [htop, top_inf_eq, top_inf_eq, card_ptSub, card_rSub]
  obtain ⟨ℓa, hℓa, ea⟩ := hρL aW
  obtain ⟨ℓb, hℓb, eb⟩ := hρL bW
  obtain ⟨-, -, hXT, ⟨e⟩, -, -⟩ := parabolic_gen ρ hLTN hT2 hTidx
    (fun g hg h1 => hK g hg (hLTN hg) h1) (fun t ht => bSub_le_ptSub (hρT t ht)) rSub_le_ptSub
    ptSub_le_normalizer (fun x hx => sq_eq_one_of_mem_rSub hx) h6 hℓa hℓb
    (by rw [ea]; exact aW_mem) (by rw [eb]; exact bW_mem) (by rw [ea, eb]; exact comm_not_mem)
  exact nonempty_quot_pCore_congr (by rw [hX, hXT]) ⟨e⟩

end CZL32

end CFSG.Quasithin.H13
