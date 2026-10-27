module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL3Core
public import CFSG.Quasithin.EmptyFaithful.R3c10Bnd

public section

namespace CFSG.Quasithin.R3c10.L3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2.L3Core
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
open Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem hei_conj_x (a b c a' : F) :
    hei a' 0 0 * hei a b c * (hei a' 0 0)⁻¹ * (hei a b c)⁻¹ = hei 0 0 (a' * b) := by
  rw [hei_inv, hei_inv, hei_mul, hei_mul, hei_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine hei_congr ?_ ?_ ?_
  · linear_combination (a' + a) * h2
  · linear_combination b * h2
  · linear_combination (c + a * b) * h2

theorem mem_centerOf_iff (z : projectiveSL 3 F) :
    z ∈ centerOf (projUnitriangular 3 F) ↔ ∃ c : F, z = hei 0 0 c := by
  constructor
  · rintro ⟨hzU, hzC⟩
    obtain ⟨a, b, c, rfl⟩ := exists_hei hzU
    have h1 := Subgroup.mem_centralizer_iff.mp hzC (hei 0 1 0) (hei_mem 0 1 0)
    have h2 := hei_conj_y a b c 1
    have h3 := hei_conj_x a b c 1
    rw [h1] at h2
    have h4 : hei 0 0 (a * 1) = 1 := by rw [← h2]; group
    have h5 := Subgroup.mem_centralizer_iff.mp hzC (hei 1 0 0) (hei_mem 1 0 0)
    rw [h5] at h3
    have h6 : hei 0 0 (1 * b) = 1 := by rw [← h3]; group
    rw [← hei_zero] at h4 h6
    have ha : a = 0 := by simpa using (hei_inj h4).2.2
    have hb : b = 0 := by simpa using (hei_inj h6).2.2
    exact ⟨c, hei_congr ha hb rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨hei_mem 0 0 c, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    obtain ⟨a, b, c', rfl⟩ := exists_hei (SetLike.mem_coe.mp hu)
    rw [hei_mul, hei_mul]
    exact hei_congr (by simp [add_comm]) (by simp [add_comm]) (by simp [add_comm])

theorem le_centerOf_of_normal_card_four [Finite F] (hq : 4 ≤ Nat.card F)
    {V : Subgroup (projectiveSL 3 F)} (hVU : V ≤ projUnitriangular 3 F)
    (hVn : ∀ g ∈ projUnitriangular 3 F, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hV4 : Nat.card V = 4) :
    V ≤ centerOf (projUnitriangular 3 F) := by
  intro v hv
  rw [mem_centerOf_iff]
  obtain ⟨a, b, c, rfl⟩ := exists_hei (hVU hv)
  have hroot : (a ≠ 0 ∨ b ≠ 0) → ∀ t : F, hei 0 0 t ∈ V := by
    intro hab t
    rcases hab with ha | hb
    · have h1 := V.mul_mem (hVn (hei 0 (a⁻¹ * t) 0) (hei_mem _ _ _) _ hv) (V.inv_mem hv)
      rw [hei_conj_y, mul_inv_cancel_left₀ ha] at h1
      exact h1
    · have h1 := V.mul_mem (hVn (hei (t * b⁻¹) 0 0) (hei_mem _ _ _) _ hv) (V.inv_mem hv)
      rw [hei_conj_x, inv_mul_cancel_right₀ hb] at h1
      exact h1
  by_contra hne
  push Not at hne
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hne c (hei_congr h.1 h.2 rfl)
  have hmem : ∀ t : F, hei 0 0 t ∈ V := hroot hab
  let f : F → V := fun t => ⟨hei 0 0 t, hmem t⟩
  have hf : Function.Injective f := fun t t' h => (hei_inj (congrArg Subtype.val h)).2.2
  have hcard : Nat.card V ≤ Nat.card F := by rw [hV4]; exact hq
  have hbij := hf.bijective_of_nat_card_le hcard
  obtain ⟨t, ht⟩ := hbij.2 ⟨hei a b c, hv⟩
  exact hne t (congrArg Subtype.val ht).symm

theorem isPGroup_projUnitriangular [Finite F] : IsPGroup 2 ↥(projUnitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  rw [← hS]
  exact S.isPGroup'

theorem centerOf_le_of_normalized [Finite F] {E : Subgroup (projectiveSL 3 F)}
    (hEU : E ≤ projUnitriangular 3 F) (hE1 : E ≠ ⊥)
    (hU : ∀ g ∈ projUnitriangular 3 F, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hT : ∀ (s : Fin 3 → F) (hs : s 0 * s 1 * s 2 = 1), ∀ e ∈ E,
      proj 3 F (diagSL s hs) * e * (proj 3 F (diagSL s hs))⁻¹ ∈ E) :
    centerOf (projUnitriangular 3 F) ≤ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(projUnitriangular 3 F) := (isPGroup_projUnitriangular).isNilpotent
  have hEn : (E.subgroupOf (projUnitriangular 3 F)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hU g g.2 x hx
  have hE1' : E.subgroupOf (projUnitriangular 3 F) ≠ ⊥ := by
    intro hb
    apply hE1
    rw [eq_bot_iff]
    intro e he
    have : (⟨e, hEU he⟩ : ↥(projUnitriangular 3 F)) ∈ E.subgroupOf (projUnitriangular 3 F) :=
      Subgroup.mem_subgroupOf.mpr he
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hE1'
  obtain ⟨⟨⟨x, hxU⟩, hxmem⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  have hxE : x ∈ E := Subgroup.mem_subgroupOf.mp hxmem.1
  have hxZ : x ∈ centerOf (projUnitriangular 3 F) :=
    ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun t ht => by
      have := Subgroup.mem_center_iff.mp hxmem.2 ⟨t, ht⟩
      exact congrArg Subtype.val this⟩
  obtain ⟨c₀, rfl⟩ := (mem_centerOf_iff x).mp hxZ
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (Subtype.ext hei_zero))
  intro z hz
  obtain ⟨c, rfl⟩ := (mem_centerOf_iff z).mp hz
  by_cases hc : c = 0
  · rw [hc, hei_zero]
    exact E.one_mem
  · set l : F := c * c₀⁻¹ with hl
    have hl0 : l ≠ 0 := mul_ne_zero hc (inv_ne_zero hc₀)
    have hs : (![l, l⁻¹, 1] : Fin 3 → F) 0 * (![l, l⁻¹, 1] : Fin 3 → F) 1 *
        (![l, l⁻¹, 1] : Fin 3 → F) 2 = 1 := by
      simp [hl0]
    have h1 := hT ![l, l⁻¹, 1] hs _ hxE
    rw [torus_conj_hei] at h1
    have e : hei ((![l, l⁻¹, 1] : Fin 3 → F) 0 * ((![l, l⁻¹, 1] : Fin 3 → F) 1)⁻¹ * 0)
        ((![l, l⁻¹, 1] : Fin 3 → F) 1 * ((![l, l⁻¹, 1] : Fin 3 → F) 2)⁻¹ * 0)
        ((![l, l⁻¹, 1] : Fin 3 → F) 0 * ((![l, l⁻¹, 1] : Fin 3 → F) 2)⁻¹ * c₀) = hei 0 0 c := by
      refine hei_congr (by simp) (by simp) ?_
      simp [hl, mul_assoc, inv_mul_cancel₀ hc₀]
    rwa [e] at h1

theorem normalizer_le_of_le_centerOf [Finite F] {V : Subgroup (projectiveSL 3 F)}
    (hVZ : V ≤ centerOf (projUnitriangular 3 F)) (hV1 : V ≠ ⊥) :
    Subgroup.normalizer (V : Set (projectiveSL 3 F)) ≤
      Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  obtain ⟨c₀, hc₀eq⟩ := (mem_centerOf_iff _).mp (hVZ v₀.2)
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hv₀1
    exact Subtype.ext (by rw [hc₀eq]; exact hei_zero)
  intro g hg
  have hgv : g * (v₀ : projectiveSL 3 F) * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg v₀).mp v₀.2
  obtain ⟨c', hc'⟩ := (mem_centerOf_iff _).mp (hVZ hgv)
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    apply hv₀1
    have h1 : g * (v₀ : projectiveSL 3 F) * g⁻¹ = 1 := by rw [hc']; exact hei_zero
    have h2 : (v₀ : projectiveSL 3 F) = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    exact Subtype.ext h2
  obtain ⟨A, rfl⟩ := proj_surjective 3 F g
  have hv₀P : (v₀ : projectiveSL 3 F) = proj 3 F (wMat c₀) := by
    rw [hc₀eq, hei_zero_zero]
    rfl
  have hgP : proj 3 F A * (v₀ : projectiveSL 3 F) * (proj 3 F A)⁻¹ = proj 3 F (wMat c') := by
    rw [hc', hei_zero_zero]
    rfl
  have hproj : proj 3 F (A * wMat c₀) = proj 3 F (wMat c' * A) := by
    rw [map_mul, map_mul, ← hgP, hv₀P]
    group
  set s : SpecialLinearGroup (Fin 3) F := (A * wMat c₀)⁻¹ * (wMat c' * A) with hsdef
  have hs : s ∈ scalars 3 F := proj_eq_proj_iff.mp hproj
  obtain ⟨z, -, hz⟩ := mem_scalars.mp hs
  have hmat : wMat c' * A = (A * wMat c₀) * s := by rw [hsdef]; group
  have hM : (wMat c' : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (wMat c₀ : Matrix (Fin 3) (Fin 3) F) *
        (s : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) hmat
    simpa [SpecialLinearGroup.coe_mul] using this
  rw [hz] at hM
  have e10 := congrFun (congrFun hM 1) 0
  have e20 := congrFun (congrFun hM 2) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e21 := congrFun (congrFun hM 2) 1
  have e12 := congrFun (congrFun hM 1) 2
  have e22 := congrFun (congrFun hM 2) 2
  have e01 := congrFun (congrFun hM 0) 1
  simp [wMat, wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply] at e10 e20 e11 e21 e12 e22 e01
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.2
  have hz1 : (z : F) = 1 := by
    by_contra hne
    have hne' : (1 - (z : F)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have a10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
      have : (A : Matrix (Fin 3) (Fin 3) F) 1 0 * (1 - (z : F)) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne'
    have a20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
      have : (A : Matrix (Fin 3) (Fin 3) F) 2 0 * (1 - (z : F)) = 0 := by linear_combination e20
      exact (mul_eq_zero.mp this).resolve_right hne'
    have a11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = 0 := by
      have : (A : Matrix (Fin 3) (Fin 3) F) 1 1 * (1 - (z : F)) = 0 := by linear_combination e11
      exact (mul_eq_zero.mp this).resolve_right hne'
    have a21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
      have : (A : Matrix (Fin 3) (Fin 3) F) 2 1 * (1 - (z : F)) = 0 := by linear_combination e21
      exact (mul_eq_zero.mp this).resolve_right hne'
    rw [Matrix.det_fin_three] at hdet
    simp [a10, a20, a11, a21] at hdet
  rw [hz1] at e12 e22 e01
  have a10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    have : (A : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ = 0 := by linear_combination -e12
    exact (mul_eq_zero.mp this).resolve_right hc₀
  have a20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    have : (A : Matrix (Fin 3) (Fin 3) F) 2 0 * c₀ = 0 := by linear_combination -e22
    exact (mul_eq_zero.mp this).resolve_right hc₀
  have a21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    have : c' * (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left hc'0
  have hAup : A ∈ upperTriangular 3 F := by
    rw [mem_upperTriangular]
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | simpa using a10 | simpa using a20 | simpa using a21
  rw [normalizer_projUnitriangular (K := F) (n := 3) 2]
  exact Subgroup.mem_map_of_mem _ hAup

end CFSG.Quasithin.R3c10.L3

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section SylowGood

variable {Y Y' : Type} [Group Y] [Group Y']

structure SylowGood (T : Subgroup Y) : Prop where
  monolith : ∃ Zc : Subgroup Y, Zc ≠ ⊥ ∧ ∀ E : Subgroup Y, E ≤ T → E ≠ ⊥ →
    Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (E : Set Y) → Zc ≤ E
  four : ∀ V : Subgroup Y, V ≤ T → Nat.card V = 4 → T ≤ Subgroup.normalizer (V : Set Y) →
    Subgroup.normalizer (V : Set Y) ≤ Subgroup.normalizer (T : Set Y)

theorem SylowGood.map {T : Subgroup Y} (e : Y ≃* Y') (h : SylowGood T) :
    SylowGood (T.map e.toMonoidHom) := by
  have hmem : ∀ (H : Subgroup Y) (x : Y), e x ∈ H.map e.toMonoidHom ↔ x ∈ H := fun H x => by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hnorm : ∀ (H : Subgroup Y) (x : Y), e x ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup Y') : Set Y') ↔
      x ∈ Subgroup.normalizer (H : Set Y) := fun H x => by
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hx y
      have := hx (e y)
      rw [hmem, show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by simp, hmem] at this
      exact this
    · intro hx y'
      obtain ⟨y, rfl⟩ := e.surjective y'
      rw [hmem, show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by simp, hmem]
      exact hx y
  refine ⟨?_, ?_⟩
  · obtain ⟨Zc, hZ1, hZ⟩ := h.monolith
    refine ⟨Zc.map e.toMonoidHom, ?_, fun E' hE'T hE'1 hN => ?_⟩
    · intro hb
      apply hZ1
      rw [eq_bot_iff]
      intro z hz
      have : e z ∈ Zc.map e.toMonoidHom := ⟨z, hz, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (by simpa using this)
    · set E : Subgroup Y := E'.comap e.toMonoidHom with hE
      have hEmem : ∀ x, x ∈ E ↔ e x ∈ E' := fun x => Iff.rfl
      have hET : E ≤ T := fun x hx => (hmem T x).mp (hE'T ((hEmem x).mp hx))
      have hE1 : E ≠ ⊥ := by
        intro hb
        apply hE'1
        rw [eq_bot_iff]
        intro y' hy'
        obtain ⟨y, rfl⟩ := e.surjective y'
        have : y ∈ E := (hEmem y).mpr hy'
        rw [hb, Subgroup.mem_bot] at this
        rw [this]
        simp
      have hNE : Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (E : Set Y) := by
        intro n hn
        have h1 := hN ((hnorm T n).mpr hn)
        rw [Subgroup.mem_normalizer_iff] at h1 ⊢
        intro y
        have := h1 (e y)
        rw [show e n * e y * (e n)⁻¹ = e (n * y * n⁻¹) by simp] at this
        exact this
      have hZE := hZ E hET hE1 hNE
      rintro _ ⟨z, hz, rfl⟩
      exact (hEmem z).mp (hZE hz)
  · intro V' hV'T hV'4 hTV'
    set V : Subgroup Y := V'.comap e.toMonoidHom with hV
    have hVmem : ∀ x, x ∈ V ↔ e x ∈ V' := fun x => Iff.rfl
    have hVT : V ≤ T := fun x hx => (hmem T x).mp (hV'T ((hVmem x).mp hx))
    have hV4 : Nat.card V = 4 := by
      have : V.map e.toMonoidHom = V' := by
        ext y'
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (hVmem y).mp hy
        · intro hy'
          obtain ⟨y, rfl⟩ := e.surjective y'
          exact ⟨y, (hVmem y).mpr hy', rfl⟩
      rw [← hV'4, ← this]
      exact Nat.card_congr (V.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    have hTV : T ≤ Subgroup.normalizer (V : Set Y) := by
      intro t ht
      have h1 := hTV' ((hmem T t).mpr ht)
      rw [Subgroup.mem_normalizer_iff] at h1 ⊢
      intro y
      have := h1 (e y)
      rw [show e t * e y * (e t)⁻¹ = e (t * y * t⁻¹) by simp] at this
      exact this
    have h4 := h.four V hVT hV4 hTV
    intro n' hn'
    obtain ⟨n, rfl⟩ := e.surjective n'
    have hnV : n ∈ Subgroup.normalizer (V : Set Y) := by
      rw [Subgroup.mem_normalizer_iff] at hn' ⊢
      intro y
      have := hn' (e y)
      rw [show e n * e y * (e n)⁻¹ = e (n * y * n⁻¹) by simp] at this
      exact this
    exact (hnorm T n).mpr (h4 hnV)

theorem SylowGood.of_map {T : Subgroup Y} (e : Y ≃* Y') (h : SylowGood (T.map e.toMonoidHom)) :
    SylowGood T := by
  have := h.map e.symm
  have e2 : (T.map e.toMonoidHom).map e.symm.toMonoidHom = T := by
    rw [Subgroup.map_map]
    ext x
    simp
  rwa [e2] at this

end SylowGood

section PSL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.QuasithinUnique.Lin2.L3Core

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sylowGood_projUnitriangular (hq : 4 ≤ Nat.card F) :
    SylowGood (projUnitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨centerOf (projUnitriangular 3 F), ?_, fun E hEU hE1 hN => ?_⟩, ?_⟩
  · intro hb
    have hmem : hei 0 0 (1 : F) ∈ centerOf (projUnitriangular 3 F) := (L3.mem_centerOf_iff _).mpr ⟨1, rfl⟩
    rw [hb, Subgroup.mem_bot, ← hei_zero] at hmem
    have := (hei_inj hmem).2.2
    exact one_ne_zero this
  · refine L3.centerOf_le_of_normalized hEU hE1 (fun g hg e he => ?_) (fun s hs e he => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.le_normalizer hg)) e).mp he
    · exact (Subgroup.mem_normalizer_iff.mp (hN (torus_mem_normalizer s hs)) e).mp he
  · intro V hVU hV4 hUV
    refine L3.normalizer_le_of_le_centerOf (L3.le_centerOf_of_normal_card_four hq hVU
      (fun g hg v hv => (Subgroup.mem_normalizer_iff.mp (hUV hg) v).mp hv) hV4) ?_
    intro hb
    rw [hb, Subgroup.card_bot] at hV4
    omega

end PSL3

section Transport

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {X : Type} [Group X]

theorem sylowGood_psl3 {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f X) :
    ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowGood T := by
  obtain ⟨⟨hp, hf', -⟩, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  intro T hT
  have hq : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  apply SylowGood.of_map e'
  have hT' : IsSylowTwoOf (T.map e'.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map e'.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := e'.toMonoidHom) e'.bijective]
    exact hi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have h0 : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top h0 hT'
  rw [← hg]
  exact (sylowGood_projUnitriangular hq).map (MulAut.conj g)

theorem borelData_psl3 [Finite X] {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f X) : BorelData X :=
  ⟨R3c8.borelPkg_psl3 hf h, fun T hT => (sylowGood_psl3 hf h T hT).monolith⟩

end Transport

section Par

variable {G : Type} [Group G] [Finite G]

theorem l3_par {L Q V : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hX : IsPSL 3 2 f (↥L ⧸ Subgroup.center ↥L))
    (hV4 : Nat.card V = 4) (hVZ : ∀ x ∈ V, x ∈ centerOf L → x = 1) (hVQ : V ≤ Q)
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) :
    ∀ H : Subgroup G, Q ≤ H → H ≤ L → H ≤ Subgroup.normalizer (V : Set G) →
      H ≤ Subgroup.normalizer (Q : Set G) ∨ L ≤ H := by
  classical
  intro H hQH hHL hHV
  left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : Q ≤ L := hQ.1
  have hVL : V ≤ L := hVQ.trans hPL
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set P' : Subgroup ↥L := Q.subgroupOf L with hP'
  set T : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hTsyl : IsSylowTwoOf T ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hGood := sylowGood_psl3 hf hX T hTsyl
  set Vbar : Subgroup (↥L ⧸ Z) := (V.subgroupOf L).map π with hVbar
  have hinj : ∀ x : ↥L, x ∈ V.subgroupOf L → π x = 1 → x = 1 := by
    intro x hx h1
    have hxZ : x ∈ Z := by rw [← hker]; exact h1
    have : (x : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hxZ
    exact Subtype.ext (hVZ _ (Subgroup.mem_subgroupOf.mp hx) this)
  have hV4' : Nat.card Vbar = 4 := by
    have hinj' : Function.Injective (π.domRestrict (V.subgroupOf L)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hinj x.1 x.2 hx)
    rw [hVbar, ← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv, hV4]
  have hVT : Vbar ≤ T := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hVQ (Subgroup.mem_subgroupOf.mp hx))
  have hnormV : ∀ l : ↥L, (l : G) ∈ Subgroup.normalizer (V : Set G) →
      π l ∈ Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := by
    intro l hlV
    have hlV' : l ∈ Subgroup.normalizer ((V.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hVL l).mpr hlV
    refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
    obtain ⟨a, ha, rfl⟩ := hvbar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlV' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  have hTV : T ≤ Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := by
    rw [hT]
    rintro _ ⟨p, hp, rfl⟩
    exact hnormV p (hQV (Subgroup.mem_subgroupOf.mp hp))
  have h4 := hGood.four Vbar hVT hV4' hTV
  intro g hg
  have hgL : g ∈ L := hHL hg
  have hmem : π ⟨g, hgL⟩ ∈ Subgroup.normalizer ((Tsyl : Subgroup (↥L ⧸ Z)) : Set (↥L ⧸ Z)) :=
    h4 (hnormV ⟨g, hgL⟩ (hHV hg))
  have h1 : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.normalizer (P' : Set ↥L) := by
    rw [← hNcomap]
    exact hmem
  exact (SBc2.mem_normalizer_subgroupOf_iff hPL ⟨g, hgL⟩).mp h1

end Par

end CFSG.Quasithin.R3c10

