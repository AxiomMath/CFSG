module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L I H K : Subgroup G}

private theorem g2_mem_sup_iff_of_le_normalizer {s t : Subgroup G}
    (hst : s ≤ Subgroup.normalizer (t : Set G)) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, (y₂⁻¹ * z₁ * y₂) * z₂,
        t.mul_mem ((Subgroup.mem_normalizer_iff''.mp (hst hy₂) z₁).mp hz₁) hz₂,
        by simp [mul_assoc]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨y⁻¹, s.inv_mem hy, y * z⁻¹ * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hst hy) z⁻¹).mp (t.inv_mem hz), by simp [mul_assoc]⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

private theorem g2_le_normalizer_of_comm {s t : Subgroup G}
    (hst : ∀ x ∈ s, ∀ y ∈ t, x * y = y * x) : s ≤ Subgroup.normalizer (t : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hst x hx h hh, mul_inv_cancel_right]
    exact hh
  · intro hk
    have hk' : x * (x * h * x⁻¹) = (x * h * x⁻¹) * x := hst x hx _ hk
    have e : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [hk']
        _ = x * h * x⁻¹ := by group
    rw [e]
    exact hk

private theorem g2_eq_of_mul_eq_mul {V₁ V₂ : Subgroup G} (hdisj : V₁ ⊓ V₂ = ⊥) {a b a' b' : G}
    (ha : a ∈ V₁) (hb : b ∈ V₂) (ha' : a' ∈ V₁) (hb' : b' ∈ V₂) (h : a' * b' = a * b) :
    a' = a ∧ b' = b := by
  have e : a⁻¹ * a' = b * b'⁻¹ := by
    calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
      _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
      _ = b * b'⁻¹ := by group
  have h1 : a⁻¹ * a' = 1 := by
    have hmem : a⁻¹ * a' ∈ V₁ ⊓ V₂ :=
      ⟨V₁.mul_mem (V₁.inv_mem ha) ha', by rw [e]; exact V₂.mul_mem hb (V₂.inv_mem hb')⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact hmem
  refine ⟨(inv_mul_eq_one.mp h1).symm, ?_⟩
  have h2 : b * b'⁻¹ = 1 := by rw [← e, h1]
  exact (mul_inv_eq_one.mp h2).symm

private theorem g2_conj_eq_of_comm {V₁ V₂ : Subgroup G} (hdisj : V₁ ⊓ V₂ = ⊥) {z a b : G}
    (ha : a ∈ V₁) (hb : b ∈ V₂) (hza : z * a * z⁻¹ ∈ V₁) (hzb : z * b * z⁻¹ ∈ V₂)
    (h : z * (a * b) = a * b * z) : z * a * z⁻¹ = a ∧ z * b * z⁻¹ = b := by
  have key : (z * a * z⁻¹) * (z * b * z⁻¹) = a * b := by
    calc (z * a * z⁻¹) * (z * b * z⁻¹) = z * (a * b) * z⁻¹ := by group
      _ = a * b := by rw [h]; group
  exact g2_eq_of_mul_eq_mul hdisj ha hb hza hzb key

private theorem g2_two_eq_zero {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : (2 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero F
  rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h
  exact (pow_eq_zero_iff'.mp h).1

private noncomputable def g2Up (F : Type) [Field F] : ↥(StatedSL 2 F) :=
  ⟨⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure
      (show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 by simp [Matrix.det_fin_two_of])⟩

private noncomputable def g2Lo (F : Type) [Field F] : ↥(StatedSL 2 F) :=
  ⟨⟨!![1, 0; 1, 1], !![1, 0; -1, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure
      (show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 by simp [Matrix.det_fin_two_of])⟩

private theorem g2Up_val (F : Type) [Field F] :
    (((g2Up F : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl

private theorem g2Lo_val (F : Type) [Field F] :
    (((g2Lo F : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl

private theorem g2Up_mul_self {F : Type} [Field F] (h2 : (2 : F) = 0) :
    g2Up F * g2Up F = 1 := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  apply Subtype.ext
  apply Units.ext
  show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]

private theorem g2Lo_mul_self {F : Type} [Field F] (h2 : (2 : F) = 0) :
    g2Lo F * g2Lo F = 1 := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  apply Subtype.ext
  apply Units.ext
  show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]

private theorem g2_vec_eq_zero {F : Type} [Field F] (w : Fin 2 → F)
    (h1 : w = Matrix.mulVec (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) w)
    (h2 : w = Matrix.mulVec (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) w) : w = 0 := by
  have e1 : w 1 = 0 := by
    have h := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have e0 : w 0 = 0 := by
    have h := congrFun h2 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  funext i
  fin_cases i <;> simp [e0, e1]

private theorem g2_exists_lift {LH R : Subgroup G} (hR : R ≤ Subgroup.normalizer (LH : Set G))
    {F : Type} [Field F] (α : ↥(LH ⊔ R) →* ↥(StatedSL 2 F)) (hα : Function.Surjective α)
    (hker : α.ker = R.subgroupOf (LH ⊔ R)) {g : ↥(StatedSL 2 F)} (hg : g * g = 1) :
    ∃ z ∈ LH, z * z ∈ R ∧ ∃ hz : z ∈ LH ⊔ R, α ⟨z, hz⟩ = g := by
  obtain ⟨x, hx⟩ := hα g
  have hxA : (x : G) ∈ R ⊔ LH := by rw [sup_comm]; exact x.2
  obtain ⟨y, hy, z, hz, hyz⟩ := (g2_mem_sup_iff_of_le_normalizer hR).mp hxA
  have hyA : y ∈ LH ⊔ R := Subgroup.mem_sup_right hy
  have hzA : z ∈ LH ⊔ R := Subgroup.mem_sup_left hz
  have hy0 : (⟨y, hyA⟩ : ↥(LH ⊔ R)) ∈ α.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hy
  have hxeq : x = (⟨y, hyA⟩ : ↥(LH ⊔ R)) * ⟨z, hzA⟩ := Subtype.ext hyz.symm
  have hαz : α ⟨z, hzA⟩ = g := by
    have h1 : α x = α ⟨y, hyA⟩ * α ⟨z, hzA⟩ := by rw [hxeq, map_mul]
    rw [hx, MonoidHom.mem_ker.mp hy0, one_mul] at h1
    exact h1.symm
  refine ⟨z, hz, ?_, hzA, hαz⟩
  have hzz : α (⟨z, hzA⟩ * ⟨z, hzA⟩) = 1 := by rw [map_mul, hαz, hg]
  have hmem : (⟨z, hzA⟩ * ⟨z, hzA⟩ : ↥(LH ⊔ R)) ∈ α.ker := MonoidHom.mem_ker.mpr hzz
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  exact hmem

private theorem g2_mem_Z_of_fix {LH R V₁ Z : Subgroup G} {F : Type} [Field F] (h2 : (2 : F) = 0)
    (hR : R ≤ Subgroup.normalizer (LH : Set G))
    (h : IsNaturalSection (LH ⊔ R) V₁ Z (R.subgroupOf (LH ⊔ R)) (StatedSL 2 F))
    {x : G} (hx : x ∈ V₁) (hfix : ∀ z ∈ LH, z * z ∈ R → z * x * z⁻¹ = x) : x ∈ Z := by
  obtain ⟨-, α, hαs, hαk, β, -, hβk, hcomp⟩ := h
  have fixv : ∀ g : ↥(StatedSL 2 F), g * g = 1 →
      Multiplicative.toAdd (β ⟨x, hx⟩) =
        Matrix.mulVec ((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          (Multiplicative.toAdd (β ⟨x, hx⟩)) := by
    intro g hg
    obtain ⟨z, hzLH, hzz, hz, hαz⟩ := g2_exists_lift hR α hαs hαk hg
    have key := hcomp ⟨z, hz⟩ ⟨x, hx⟩ ⟨x, hx⟩ (hfix z hzLH hzz).symm
    rw [hαz] at key
    exact key
  have e1 := fixv (g2Up F) (g2Up_mul_self h2)
  have e2 := fixv (g2Lo F) (g2Lo_mul_self h2)
  rw [g2Up_val] at e1
  rw [g2Lo_val] at e2
  have hw : Multiplicative.toAdd (β ⟨x, hx⟩) = 0 := g2_vec_eq_zero _ e1 e2
  have hβ1 : β ⟨x, hx⟩ = 1 := toAdd_eq_zero.mp hw
  have hmem : (⟨x, hx⟩ : ↥V₁) ∈ β.ker := MonoidHom.mem_ker.mpr hβ1
  rw [hβk, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem card_of_naturalSection_two {A V₁ Z : Subgroup G} {N : Subgroup ↥A} {F : Type} [Field F]
    [Fintype F] (h : IsNaturalSection A V₁ Z N (StatedSL 2 F)) (hZ : Z = ⊥) :
    Nat.card ↥V₁ = Fintype.card F ^ 2 := by
  obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩), Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_V_of_sum (c : Conf4212 G T M L I H K) {F : Type} [Field F] [Fintype F]
    {V₁ V₂ : Subgroup G} (hV : ⁅reducedAggregate (L ⊔ T), L⁆ = V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ = ⊥)
    (h₁ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₁
      (V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F))
    (h₂ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₂
      (V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F))
    (hVL : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = Fintype.card F ^ 4 := by
  have hVC : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hVL
  have hV1 : V₁ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
    rw [hV]
    exact le_sup_left
  have hV2 : V₂ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
    rw [hV]
    exact le_sup_right
  have hcomm : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x := fun x hx y hy =>
    c.V_comm x (hV1 hx) y (hV2 hy)
  have hZ1 : V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
        Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := ⟨hV1 hx.1, hx.2⟩
    rw [hVC] at hx'
    exact hx'
  have hZ2 : V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
        Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := ⟨hV2 hx.1, hx.2⟩
    rw [hVC] at hx'
    exact hx'
  have hcard1 := card_of_naturalSection_two h₁ hZ1
  have hcard2 := card_of_naturalSection_two h₂ hZ2
  have hnorm : V₁ ≤ Subgroup.normalizer (V₂ : Set G) := g2_le_normalizer_of_comm hcomm
  let f : ↥V₁ × ↥V₂ → ↥⁅reducedAggregate (L ⊔ T), L⁆ := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mul_mem _ (hV1 p.1.2) (hV2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ hab
      have hab' : a₁ * b₁ = a₂ * b₂ := congrArg Subtype.val hab
      obtain ⟨rfl, rfl⟩ := g2_eq_of_mul_eq_mul hdisj ha₂ hb₂ ha₁ hb₁ hab'
      rfl
    · rintro ⟨v, hv⟩
      have hvV : v ∈ V₁ ⊔ V₂ := by
        rw [← hV]
        exact hv
      obtain ⟨a, ha, b, hb, hab⟩ := (g2_mem_sup_iff_of_le_normalizer hnorm).mp hvV
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext hab⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hcard1, hcard2]
  ring

theorem cv_of_sum (c : Conf4212 G T M L I H K) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n)
    {V₁ V₂ : Subgroup G} (hV : ⁅reducedAggregate (L ⊔ T), L⁆ = V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ = ⊥)
    (h₁ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₁
      (V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F))
    (h₂ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₂
      (V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F))
    (hVL : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ v ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
      (∀ t ∈ perfectCore (L ⊓ H), t * t ∈ pCoreOf 2 I → t * v = v * t) → v = 1 := by
  intro v hv hcomm
  have h2 : (2 : F) = 0 := g2_two_eq_zero hF
  have hVC : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hVL
  have hV1 : V₁ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
    rw [hV]
    exact le_sup_left
  have hV2 : V₂ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
    rw [hV]
    exact le_sup_right
  have hcomm12 : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x := fun x hx y hy =>
    c.V_comm x (hV1 hx) y (hV2 hy)
  have hRHM : pCoreOf 2 I ≤ H ⊓ M :=
    le_inf ((pCoreOf_le 2 I).trans c.inH.1) ((pCoreOf_le 2 I).trans c.I_le)
  have hR : pCoreOf 2 I ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
    hRHM.trans c.LH_normal
  have hnorm : V₁ ≤ Subgroup.normalizer (V₂ : Set G) := g2_le_normalizer_of_comm hcomm12
  have hvV : v ∈ V₁ ⊔ V₂ := by
    rw [← hV]
    exact hv
  obtain ⟨a, ha, b, hb, rfl⟩ := (g2_mem_sup_iff_of_le_normalizer hnorm).mp hvV
  have hconj : ∀ z ∈ perfectCore (L ⊓ H), z * z ∈ pCoreOf 2 I →
      z * a * z⁻¹ = a ∧ z * b * z⁻¹ = b := by
    intro z hz hzz
    have hzA : z ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_left hz
    have hza : z * a * z⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (h₁.1 hzA) a).mp ha
    have hzb : z * b * z⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (h₂.1 hzA) b).mp hb
    exact g2_conj_eq_of_comm hdisj ha hb hza hzb (hcomm z hz hzz)
  have hfix_a : ∀ z ∈ perfectCore (L ⊓ H), z * z ∈ pCoreOf 2 I → z * a * z⁻¹ = a :=
    fun z hz hzz => (hconj z hz hzz).1
  have hfix_b : ∀ z ∈ perfectCore (L ⊓ H), z * z ∈ pCoreOf 2 I → z * b * z⁻¹ = b :=
    fun z hz hzz => (hconj z hz hzz).2
  have ha1 : a = 1 := by
    have hZa := g2_mem_Z_of_fix h2 hR h₁ ha hfix_a
    have hx' : a ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
        Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := ⟨hV1 ha, hZa.2⟩
    rw [hVC, Subgroup.mem_bot] at hx'
    exact hx'
  have hb1 : b = 1 := by
    have hZb := g2_mem_Z_of_fix h2 hR h₂ hb hfix_b
    have hx' : b ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
        Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := ⟨hV2 hb, hZb.2⟩
    rw [hVC, Subgroup.mem_bot] at hx'
    exact hx'
  rw [ha1, hb1, mul_one]

end CFSG.Quasithin.H13.Ch4.CentK
