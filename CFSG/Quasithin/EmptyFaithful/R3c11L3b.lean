module

public import CFSG.Quasithin.EmptyFaithful.R3c11L3

public section

namespace CFSG.Quasithin.R3c11.L3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2.L3Core
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
open Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem card_centerOf : Nat.card (centerOf (projUnitriangular 3 F)) = Nat.card F := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun c : F => (⟨hei 0 0 c, (R3c10.L3.mem_centerOf_iff _).mpr ⟨c, rfl⟩⟩ :
      ↥(centerOf (projUnitriangular 3 F)))) ⟨fun c c' h => ?_, fun z => ?_⟩)
  · exact (hei_inj (congrArg Subtype.val h)).2.2
  · obtain ⟨c, hc⟩ := (R3c10.L3.mem_centerOf_iff _).mp z.2
    exact ⟨c, Subtype.ext hc.symm⟩

omit [CharP F 2] in
theorem proj_mem_projUnitriangular_of_diag {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ upperTriangular 3 F)
    (h1 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0)
    (h2 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    proj 3 F A ∈ projUnitriangular 3 F := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.2
  have hA' : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := mem_upperTriangular_iff_isUpperTriangular.mp hA
  rw [Matrix.det_of_isUpperTriangular hA', Fin.prod_univ_three, h1, h2] at hdet
  set a : F := (A : Matrix (Fin 3) (Fin 3) F) 0 0 with ha
  have ha3 : a ^ 3 = 1 := by linear_combination hdet
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha3
    norm_num at ha3
  let c : Fˣ := Units.mk0 a ha0
  have hc : c ^ 3 = 1 := Units.ext (by simpa [c] using ha3)
  have hc' : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc, inv_one]
  let z : SpecialLinearGroup (Fin 3) F := scalarElement c hc
  let z' : SpecialLinearGroup (Fin 3) F := scalarElement c⁻¹ hc'
  let u : SpecialLinearGroup (Fin 3) F := z' * A
  have hz : proj 3 F z = 1 := proj_eq_one_iff.mpr (scalarElement_mem_scalars c hc)
  have hzz' : z * z' = 1 := by
    apply Subtype.ext
    change (scalar (Fin 3) (c : F)) * (scalar (Fin 3) ((c⁻¹ : Fˣ) : F)) = 1
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hAeq : A = z * u := by
    have : z * u = (z * z') * A := by simp only [u, mul_assoc]
    rw [this, hzz', one_mul]
  have hu : u ∈ unitriangular 3 F := by
    rw [mem_unitriangular]
    have hentry : ∀ i j, (u : Matrix (Fin 3) (Fin 3) F) i j =
        ((c⁻¹ : Fˣ) : F) * (A : Matrix (Fin 3) (Fin 3) F) i j := by
      intro i j
      have e : (u : Matrix (Fin 3) (Fin 3) F) =
          scalar (Fin 3) ((c⁻¹ : Fˣ) : F) * (A : Matrix (Fin 3) (Fin 3) F) := rfl
      rw [e, Matrix.scalar_apply, Matrix.diagonal_mul]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hentry, hA i j hij, mul_zero]
    · rw [hentry]
      fin_cases i <;> simp [c, h1, h2, ← ha, inv_mul_cancel₀ ha0]
  refine ⟨u, hu, ?_⟩
  calc proj 3 F u = proj 3 F z * proj 3 F u := by rw [hz, one_mul]
    _ = proj 3 F (z * u) := (map_mul _ _ _).symm
    _ = proj 3 F A := by rw [← hAeq]

theorem cent_le_of_card_four [Finite F] (hF : Nat.card F = 4) :
    ∀ g ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)),
      (∀ z ∈ centerOf (projUnitriangular 3 F), g * z = z * g) → g ∈ projUnitriangular 3 F := by
  classical
  intro g hg hcent
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular (K := F) (n := 3) 2] at hg
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
  have hw : hei 0 0 (1 : F) ∈ centerOf (projUnitriangular 3 F) :=
    (R3c10.L3.mem_centerOf_iff _).mpr ⟨1, rfl⟩
  have h1 := hcent _ hw
  rw [hei_zero_zero] at h1
  have hproj : proj 3 F (A * wMat (1 : F)) = proj 3 F (wMat (1 : F) * A) := by
    rw [map_mul, map_mul]
    exact h1
  set s : SpecialLinearGroup (Fin 3) F := (A * wMat (1 : F))⁻¹ * (wMat (1 : F) * A) with hsdef
  have hs : s ∈ scalars 3 F := proj_eq_proj_iff.mp hproj
  obtain ⟨z, -, hz⟩ := mem_scalars.mp hs
  have hmat : wMat (1 : F) * A = (A * wMat (1 : F)) * s := by rw [hsdef]; group
  have hM : (wMat (1 : F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (wMat (1 : F) : Matrix (Fin 3) (Fin 3) F) *
        (s : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F)) hmat
    simpa [SpecialLinearGroup.coe_mul] using this
  rw [hz] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e02 := congrFun (congrFun hM 0) 2
  simp [wMat, wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply] at e00 e02
  have hAu : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hA
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.2
  rw [Matrix.det_of_isUpperTriangular hAu, Fin.prod_univ_three] at hdet
  have a20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hA 2 0 (by decide)
  have h00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hz1 : (z : F) = 1 := by
    rw [a20, add_zero] at e00
    have : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * ((z : F) - 1) = 0 := by linear_combination -e00
    have := (mul_eq_zero.mp this).resolve_left h00
    linear_combination this
  rw [hz1] at e02
  have h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    linear_combination e02
  have hcube : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 3 = 1 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.pow_card_sub_one_eq_one ((A : Matrix (Fin 3) (Fin 3) F) 0 0) h00
    rw [← Nat.card_eq_fintype_card, hF] at h
    simpa using h
  have h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    rw [h22] at hdet
    have h2 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 0 0 *
        ((A : Matrix (Fin 3) (Fin 3) F) 1 1 - (A : Matrix (Fin 3) (Fin 3) F) 0 0) = 0 := by
      linear_combination hdet - hcube
    have := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero h00 h00)
    linear_combination this
  exact proj_mem_projUnitriangular_of_diag hA h11 h22

end CFSG.Quasithin.R3c11.L3

namespace CFSG.Quasithin.R3c11

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section SylowGoodCl

variable {Y Y' : Type} [Group Y] [Group Y']

structure SylowGoodCl (T : Subgroup Y) : Prop where
  vcen : ∀ V : Subgroup Y, V ≤ T → Nat.card V = 4 → T ≤ Subgroup.normalizer (V : Set Y) →
    V ≤ centerOf T
  cenle : ∀ E : Subgroup Y, E ≤ T → E ≠ ⊥ →
    Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (E : Set Y) → centerOf T ≤ E
  cent : Nat.card (centerOf T) = 4 → ∀ g ∈ Subgroup.normalizer (T : Set Y),
    (∀ z ∈ centerOf T, g * z = z * g) → g ∈ T

theorem mem_map_equiv_iff (e : Y ≃* Y') (H : Subgroup Y) (x : Y) :
    e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_normalizer_map_equiv_iff (e : Y ≃* Y') (H : Subgroup Y) (x : Y) :
    e x ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup Y') : Set Y') ↔
      x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    have := hx (e y)
    rw [mem_map_equiv_iff, show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by simp,
      mem_map_equiv_iff] at this
    exact this
  · intro hx y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    rw [mem_map_equiv_iff, show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by simp, mem_map_equiv_iff]
    exact hx y

theorem centerOf_map (e : Y ≃* Y') (T : Subgroup Y) :
    centerOf (T.map e.toMonoidHom) = (centerOf T).map e.toMonoidHom := by
  ext y'
  obtain ⟨y, rfl⟩ := e.surjective y'
  rw [mem_map_equiv_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_map_equiv_iff e T y).mp h1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp h2 (e t) ((mem_map_equiv_iff e T t).mpr ht)
    exact e.injective (by simpa using this)
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_map_equiv_iff e T y).mpr h1, Subgroup.mem_centralizer_iff.mpr fun t' ht' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := ht'
    have := Subgroup.mem_centralizer_iff.mp h2 t ht
    simpa using congrArg e this

theorem SylowGoodCl.map {T : Subgroup Y} (e : Y ≃* Y') (h : SylowGoodCl T) :
    SylowGoodCl (T.map e.toMonoidHom) := by
  have hc := centerOf_map e T
  refine ⟨?_, ?_, ?_⟩
  · intro V' hV'T hV'4 hTV'
    set V : Subgroup Y := V'.comap e.toMonoidHom with hV
    have hVmem : ∀ x, x ∈ V ↔ e x ∈ V' := fun x => Iff.rfl
    have hVT : V ≤ T := fun x hx => (mem_map_equiv_iff e T x).mp (hV'T ((hVmem x).mp hx))
    have hVeq : V.map e.toMonoidHom = V' := by
      ext y'
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hVmem y).mp hy
      · intro hy'
        obtain ⟨y, rfl⟩ := e.surjective y'
        exact ⟨y, (hVmem y).mpr hy', rfl⟩
    have hV4 : Nat.card V = 4 := by
      rw [← hV'4, ← hVeq]
      exact Nat.card_congr (V.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    have hTV : T ≤ Subgroup.normalizer (V : Set Y) := by
      intro t ht
      have h1 := hTV' ((mem_map_equiv_iff e T t).mpr ht)
      rw [← hVeq] at h1
      exact (mem_normalizer_map_equiv_iff e V t).mp h1
    have := h.vcen V hVT hV4 hTV
    rw [hc, ← hVeq]
    exact Subgroup.map_mono this
  · intro E' hE'T hE'1 hN
    set E : Subgroup Y := E'.comap e.toMonoidHom with hE
    have hEmem : ∀ x, x ∈ E ↔ e x ∈ E' := fun x => Iff.rfl
    have hEeq : E.map e.toMonoidHom = E' := by
      ext y'
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hEmem y).mp hy
      · intro hy'
        obtain ⟨y, rfl⟩ := e.surjective y'
        exact ⟨y, (hEmem y).mpr hy', rfl⟩
    have hET : E ≤ T := fun x hx => (mem_map_equiv_iff e T x).mp (hE'T ((hEmem x).mp hx))
    have hE1 : E ≠ ⊥ := by
      intro hb
      apply hE'1
      rw [← hEeq, hb, Subgroup.map_bot]
    have hNE : Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (E : Set Y) := by
      intro n hn
      have h1 := hN ((mem_normalizer_map_equiv_iff e T n).mpr hn)
      rw [← hEeq] at h1
      exact (mem_normalizer_map_equiv_iff e E n).mp h1
    rw [hc, ← hEeq]
    exact Subgroup.map_mono (h.cenle E hET hE1 hNE)
  · intro hcard g' hg' hcomm
    obtain ⟨g, rfl⟩ := e.surjective g'
    have hg : g ∈ Subgroup.normalizer (T : Set Y) := (mem_normalizer_map_equiv_iff e T g).mp hg'
    have hcard' : Nat.card (centerOf T) = 4 := by
      rw [hc] at hcard
      rw [← hcard]
      exact (Nat.card_congr ((centerOf T).equivMapOfInjective e.toMonoidHom e.injective).toEquiv)
    have := h.cent hcard' g hg (fun z hz => by
      have := hcomm (e z) (by rw [hc]; exact (mem_map_equiv_iff e (centerOf T) z).mpr hz)
      exact e.injective (by simpa using this))
    exact (mem_map_equiv_iff e T g).mpr this

theorem SylowGoodCl.of_map {T : Subgroup Y} (e : Y ≃* Y') (h : SylowGoodCl (T.map e.toMonoidHom)) :
    SylowGoodCl T := by
  have := h.map e.symm
  have e2 : (T.map e.toMonoidHom).map e.symm.toMonoidHom = T := by
    rw [Subgroup.map_map]
    ext x
    simp
  rwa [e2] at this

end SylowGoodCl

section PSL3Cl

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.QuasithinUnique.Lin2.L3Core

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sylowGoodCl_projUnitriangular (hq : 4 ≤ Nat.card F) :
    SylowGoodCl (projUnitriangular 3 F) := by
  refine ⟨fun V hVU hV4 hUV => R3c10.L3.le_centerOf_of_normal_card_four hq hVU
      (fun g hg v hv => (Subgroup.mem_normalizer_iff.mp (hUV hg) v).mp hv) hV4,
    fun E hEU hE1 hN => ?_, fun hcard => ?_⟩
  · refine R3c10.L3.centerOf_le_of_normalized hEU hE1 (fun g hg e he => ?_) (fun s hs e he => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.le_normalizer hg)) e).mp he
    · exact (Subgroup.mem_normalizer_iff.mp (hN (torus_mem_normalizer s hs)) e).mp he
  · refine L3.cent_le_of_card_four ?_
    rw [← L3.card_centerOf]
    exact hcard

end PSL3Cl

section TransportCl

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {X : Type} [Group X]

theorem sylowGoodCl_psl3 {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f X) :
    ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowGoodCl T := by
  obtain ⟨⟨hp, hf', -⟩, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  intro T hT
  have hq : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  apply SylowGoodCl.of_map e'
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
  exact (sylowGoodCl_projUnitriangular hq).map (MulAut.conj g)

end TransportCl

end CFSG.Quasithin.R3c11
