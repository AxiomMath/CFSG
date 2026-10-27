module

public import CFSG.LocalAnalysis.StandardType.GGTWPat2W
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWPat1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nS2_preReflection_conj {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ha hb : V) (αa αb : Module.Dual (ZMod p) V)
    (hbb : αb hb = 2) (v : V) :
    Module.preReflection hb αb (Module.preReflection ha αa (Module.preReflection hb αb v)) =
      v - (αa - αa hb • αb) v • (ha - αb ha • hb) := by
  have hkey := Module.preReflection_preReflection (R := ZMod p) (M := V) (x := hb) (y := ha)
    (f := αb) (g := αa) hbb
  simp only [Module.preReflection_apply, Module.Dual.eval_apply] at hkey
  have hcomp : Module.preReflection hb αb ∘ₗ Module.preReflection ha αa ∘ₗ
      Module.preReflection hb αb =
      Module.preReflection (ha - αb ha • hb) (αa - αa hb • αb) := hkey.symm
  calc Module.preReflection hb αb (Module.preReflection ha αa (Module.preReflection hb αb v))
      = (Module.preReflection hb αb ∘ₗ Module.preReflection ha αa ∘ₗ
          Module.preReflection hb αb) v := by
          simp only [LinearMap.comp_apply]
    _ = Module.preReflection (ha - αb ha • hb) (αa - αa hb • αb) v := by rw [hcomp]
    _ = v - (αa - αa hb • αb) v • (ha - αb ha • hb) := Module.preReflection_apply _ _ _

theorem ggTWUp_false_twoW {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hcells : GGTWDCells1 p N) {Bs : Subgroup G}
    {pos : GGTWPos} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa]
    [DecidableEq Λa] {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {e : Fin (N - 1) ≃ Λ}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV : V}
    (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 2)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hform : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod p) V = N)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hex : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) : False := by
  classical
  haveI : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; rcases hN with h | h | h | h | h <;> omega)
  let eJ : {c : Fin (N - 1) // ggTWInJ N pos c.val} ≃ {i : Λ // i ≠ b₁ ∧ i ≠ b₂} :=
    { toFun := fun c => ⟨e c.1, (hJpos c.1).1 c.2⟩
      invFun := fun i => ⟨e.symm i.1, (hJpos (e.symm i.1)).2 (by simpa using i.2)⟩
      left_inv := by intro c; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }
  let ee : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ≃
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) := Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) :=
    MK.reindex ee.symm
  let CK' : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hWK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK ee.symm
  have hCK' : GGIntCartan MK' CK' := by
    have h := GGIntCartan.reindex (e := ee.symm) hCK
    simpa [CK', MK', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using h
  have hcast : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      ((CK' (Sum.inl i) (Sum.inl j) : ℤ) : ZMod p) =
        ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
    intro i j
    have h1 := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at h1
    have h2 := hF.pair i.1 j.1
    have hval : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp [CK', ee, Matrix.submatrix_apply]
    rw [hval, ← h1]
    rw [show (eJ i).1 = e i.1 from rfl, show (eJ j).1 = e j.1 from rfl]
    exact h2
  have hJ' : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK' (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hCK'.1 (Sum.inl i)]
      simp [CartanMatrix.A]
    · have hne : Sum.inl i ≠
          (Sum.inl j : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)) :=
        fun h => hij (by injection h)
      have hpair : (CK' (Sum.inl i) (Sum.inl j) = 0 ∧ CK' (Sum.inl j) (Sum.inl i) = 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) = -1 ∧ CK' (Sum.inl j) (Sum.inl i) = -1) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 2 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 3 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) := by
        rcases hCK'.2 (Sum.inl i) (Sum.inl j) hne with
          ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hb : CartanMatrix.A (N - 1) i.1 j.1 = 0 ∨
          CartanMatrix.A (N - 1) i.1 j.1 = -1 := by
        rcases l05nDP4_cartanA_mem (N - 1) i.1 j.1 with h2 | hm1 | h0
        · exact absurd (l05nDP4_cartanA_eq_two h2) hij'
        · exact Or.inr hm1
        · exact Or.inl h0
      have h1c := hcast i j
      have h2c : ((CK' (Sum.inl j) (Sum.inl i) : ℤ) : ZMod p) =
          ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
        rw [hcast j i, CFSG.ClassicalInvolution.ModelFacts.cartanA_symm (N - 1) j.1 i.1]
      exact (ggTW_cast_cartan_pair hp hpair hb h1c h2c).1
  have hvalJ : ∀ (c : Fin (N - 1)) (hc : ggTWInJ N pos c.val), (eJ ⟨c, hc⟩).1 = e c :=
    fun c hc => rfl
  obtain ⟨a, hwa⟩ := hex
  rcases ggTW_pattern2W hN pos hcard hWK' hCK' hJ' a with
    ⟨c0, m, n, hpat, hrow⟩ | ⟨hzeroa, b, c0, m, n, _hbne, hpatb, hpatc, hrowb⟩
  ·
    have hαa : α (Sum.inr a) (h (Sum.inr a)) = 2 := by
      have hpk := hpairK (Sum.inr a) (Sum.inr a)
      simp only [Sum.map_inr, id_eq] at hpk
      rw [hpk, hCK.1 (Sum.inr a)]
      norm_num
    have hpair : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
        α (Sum.inr a) (h (Sum.inl (e c))) = (if c = c0 then (m : ZMod p) else 0) ∧
          α (Sum.inl (e c)) (h (Sum.inr a)) = (if c = c0 then (n : ZMod p) else 0) := by
      intro c hc
      have hrowc := hrow ⟨c, hc⟩
      constructor
      · have hpk := hpairK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩))
        simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk
        have hck : CK' (Sum.inr a) (Sum.inl ⟨c, hc⟩) =
            CK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩)) := by
          simp [CK', ee, Matrix.submatrix_apply]
        rw [hpk, ← hck, hrowc.1]
        split_ifs <;> simp
      · have hpk := hpairK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a)
        simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk
        have hck : CK' (Sum.inl ⟨c, hc⟩) (Sum.inr a) =
            CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a) := by
          simp [CK', ee, Matrix.submatrix_apply]
        rw [hpk, ← hck, hrowc.2]
        split_ifs <;> simp
    have hsub : ∀ x, x ∈ Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := p) ι (φ (Sum.inr a))} →
        x ∈ Subgroup.closure (Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o))) := by
      rintro x (hx | hx)
      · obtain ⟨i, rfl⟩ := hx
        exact Subgroup.subset_closure ⟨Sum.inl (e i), rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
    have hntA : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := p) ι (φ (Sum.inr a))}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
      fun g hg => hnt g ((Subgroup.closure_le _).mpr hsub hg)
    exact ggTWD_false_one hcells hF hdim
      (fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))) (fun i v => hform (Sum.inl (e i)) v)
      (ggLin (p := p) ι (φ (Sum.inr a))) (h (Sum.inr a)) (α (Sum.inr a))
      (fun v => hform (Sum.inr a) v) hαa hwa pos c0 m n hpat hpair hntA
  · by_cases hwb : α (Sum.inr b) xV = 0
    ·
      let Cab : ℤ := CK (Sum.inr a) (Sum.inr b)
      let Cba : ℤ := CK (Sum.inr b) (Sum.inr a)
      have hCab : CK' (Sum.inr a) (Sum.inr b) = CK (Sum.inr a) (Sum.inr b) := by
        simp [CK', ee, Matrix.submatrix_apply]
      have hCba : CK' (Sum.inr b) (Sum.inr a) = CK (Sum.inr b) (Sum.inr a) := by
        simp [CK', ee, Matrix.submatrix_apply]
      let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ (Sum.inr b) * φ (Sum.inr a) * φ (Sum.inr b))
      let ha' : V := h (Sum.inr a) - (Cba : ZMod p) • h (Sum.inr b)
      let αa' : Module.Dual (ZMod p) V := α (Sum.inr a) - (Cab : ZMod p) • α (Sum.inr b)
      have hbb : α (Sum.inr b) (h (Sum.inr b)) = 2 := by
        have hpk := hpairK (Sum.inr b) (Sum.inr b)
        simp only [Sum.map_inr, id_eq] at hpk
        rw [hpk, hCK.1 (Sum.inr b)]
        norm_num
      have haa : α (Sum.inr a) (h (Sum.inr a)) = 2 := by
        have hpk := hpairK (Sum.inr a) (Sum.inr a)
        simp only [Sum.map_inr, id_eq] at hpk
        rw [hpk, hCK.1 (Sum.inr a)]
        norm_num
      have hab : α (Sum.inr a) (h (Sum.inr b)) = (Cab : ZMod p) := by
        have hpk := hpairK (Sum.inr a) (Sum.inr b)
        simp only [Sum.map_inr, id_eq] at hpk
        simpa only [Cab] using hpk
      have hba : α (Sum.inr b) (h (Sum.inr a)) = (Cba : ZMod p) := by
        have hpk := hpairK (Sum.inr b) (Sum.inr a)
        simp only [Sum.map_inr, id_eq] at hpk
        simpa only [Cba] using hpk
      have hra : ∀ v, ra v = v - αa' v • ha' := by
        intro v
        have hra_def : ra = ggLin (p := p) ι (φ (Sum.inr b)) * ggLin (p := p) ι (φ (Sum.inr a)) *
            ggLin (p := p) ι (φ (Sum.inr b)) := by
          simp [ra, map_mul]
        have hb_pre : ∀ w, Module.preReflection (h (Sum.inr b)) (α (Sum.inr b)) w =
            ggLin (p := p) ι (φ (Sum.inr b)) w := by
          intro w
          rw [Module.preReflection_apply]
          exact (hform (Sum.inr b) w).symm
        have ha_pre : ∀ w, Module.preReflection (h (Sum.inr a)) (α (Sum.inr a)) w =
            ggLin (p := p) ι (φ (Sum.inr a)) w := by
          intro w
          rw [Module.preReflection_apply]
          exact (hform (Sum.inr a) w).symm
        calc ra v
            = (ggLin (p := p) ι (φ (Sum.inr b)) * ggLin (p := p) ι (φ (Sum.inr a)) *
                ggLin (p := p) ι (φ (Sum.inr b))) v := by rw [hra_def]
          _ = ggLin (p := p) ι (φ (Sum.inr b)) (ggLin (p := p) ι (φ (Sum.inr a))
                (ggLin (p := p) ι (φ (Sum.inr b)) v)) := by
                simp only [LinearEquiv.mul_apply]
          _ = Module.preReflection (h (Sum.inr b)) (α (Sum.inr b))
                (Module.preReflection (h (Sum.inr a)) (α (Sum.inr a))
                  (Module.preReflection (h (Sum.inr b)) (α (Sum.inr b)) v)) := by
                rw [hb_pre, ha_pre, hb_pre]
          _ = v - (α (Sum.inr a) - α (Sum.inr a) (h (Sum.inr b)) • α (Sum.inr b)) v •
                (h (Sum.inr a) - α (Sum.inr b) (h (Sum.inr a)) • h (Sum.inr b)) :=
                l05nS2_preReflection_conj (h (Sum.inr a)) (h (Sum.inr b))
                  (α (Sum.inr a)) (α (Sum.inr b)) hbb v
          _ = v - αa' v • ha' := by
                rw [hab, hba]
      have hαa : αa' ha' = 2 := by
        have hgoal : αa' ha' = (α (Sum.inr a) - (Cab : ZMod p) • α (Sum.inr b))
            (h (Sum.inr a) - (Cba : ZMod p) • h (Sum.inr b)) := by
          simp only [αa', ha']
        rw [hgoal]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_smul]
        rw [haa, hab, hba, hbb]
        ring
      have hw : αa' xV ≠ 0 := by
        have hxe : αa' xV = α (Sum.inr a) xV := by
          simp only [αa', LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hwb,
            mul_zero, sub_zero]
        rwa [hxe]
      have hpair : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
          αa' (h (Sum.inl (e c))) =
              (if c = c0 then ((-Cab * m : ℤ) : ZMod p) else 0) ∧
            α (Sum.inl (e c)) ha' =
              (if c = c0 then ((-Cba * n : ℤ) : ZMod p) else 0) := by
        intro c hc
        have hrowc := hrowb ⟨c, hc⟩
        have hzeroc := hzeroa ⟨c, hc⟩
        constructor
        · have hpk_a := hpairK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩))
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk_a
          have hck_a : CK' (Sum.inr a) (Sum.inl ⟨c, hc⟩) =
              CK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩)) := by
            simp [CK', ee, Matrix.submatrix_apply]
          have hpk_b := hpairK (Sum.inr b) (Sum.inl (eJ ⟨c, hc⟩))
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk_b
          have hck_b : CK' (Sum.inr b) (Sum.inl ⟨c, hc⟩) =
              CK (Sum.inr b) (Sum.inl (eJ ⟨c, hc⟩)) := by
            simp [CK', ee, Matrix.submatrix_apply]
          have hgoal : αa' (h (Sum.inl (e c))) =
              α (Sum.inr a) (h (Sum.inl (e c))) -
                (Cab : ZMod p) * α (Sum.inr b) (h (Sum.inl (e c))) := by
            simp only [αa', LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hgoal, hpk_a, ← hck_a, hzeroc.1, hpk_b, ← hck_b, hrowc.1]
          by_cases hcc : c = c0
          · rw [if_pos hcc, if_pos hcc]; push_cast; ring
          · rw [if_neg hcc, if_neg hcc]; ring
        · have hpk_a := hpairK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a)
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk_a
          have hck_a : CK' (Sum.inl ⟨c, hc⟩) (Sum.inr a) =
              CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a) := by
            simp [CK', ee, Matrix.submatrix_apply]
          have hpk_b := hpairK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr b)
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk_b
          have hck_b : CK' (Sum.inl ⟨c, hc⟩) (Sum.inr b) =
              CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr b) := by
            simp [CK', ee, Matrix.submatrix_apply]
          have hgoal : α (Sum.inl (e c)) ha' =
              α (Sum.inl (e c)) (h (Sum.inr a)) -
                (Cba : ZMod p) * α (Sum.inl (e c)) (h (Sum.inr b)) := by
            simp only [ha', map_sub, map_smul, smul_eq_mul]
          rw [hgoal, hpk_a, ← hck_a, hzeroc.2, hpk_b, ← hck_b, hrowc.2]
          by_cases hcc : c = c0
          · rw [if_pos hcc, if_pos hcc]; push_cast; ring
          · rw [if_neg hcc, if_neg hcc]; ring
      have hsub : ∀ x, x ∈ Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ra} →
          x ∈ Subgroup.closure (Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o))) := by
        rintro x (hx | hx)
        · obtain ⟨i, rfl⟩ := hx
          exact Subgroup.subset_closure ⟨Sum.inl (e i), rfl⟩
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          have hb : ggLin (p := p) ι (φ (Sum.inr b)) ∈
              Subgroup.closure (Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o))) :=
            Subgroup.subset_closure ⟨Sum.inr b, rfl⟩
          have ha : ggLin (p := p) ι (φ (Sum.inr a)) ∈
              Subgroup.closure (Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o))) :=
            Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
          have hra_eq : ra = ggLin (p := p) ι (φ (Sum.inr b)) * ggLin (p := p) ι (φ (Sum.inr a)) *
              ggLin (p := p) ι (φ (Sum.inr b)) := by
            simp [ra, map_mul]
          rw [hra_eq]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb ha) hb
      have hntB : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
            ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ra}),
          ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
        fun g hg => hnt g ((Subgroup.closure_le _).mpr hsub hg)
      exact ggTWD_false_one hcells hF hdim
        (fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))) (fun i v => hform (Sum.inl (e i)) v)
        ra ha' αa' hra hαa hw pos c0 (-Cab * m) (-Cba * n)
        (by simpa only [Cab, Cba, hCab, hCba] using hpatc) hpair hntB
    ·
      have hαa : α (Sum.inr b) (h (Sum.inr b)) = 2 := by
        have hpk := hpairK (Sum.inr b) (Sum.inr b)
        simp only [Sum.map_inr, id_eq] at hpk
        rw [hpk, hCK.1 (Sum.inr b)]
        norm_num
      have hpair : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
          α (Sum.inr b) (h (Sum.inl (e c))) = (if c = c0 then (m : ZMod p) else 0) ∧
            α (Sum.inl (e c)) (h (Sum.inr b)) = (if c = c0 then (n : ZMod p) else 0) := by
        intro c hc
        have hrowc := hrowb ⟨c, hc⟩
        constructor
        · have hpk := hpairK (Sum.inr b) (Sum.inl (eJ ⟨c, hc⟩))
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk
          have hck : CK' (Sum.inr b) (Sum.inl ⟨c, hc⟩) =
              CK (Sum.inr b) (Sum.inl (eJ ⟨c, hc⟩)) := by
            simp [CK', ee, Matrix.submatrix_apply]
          rw [hpk, ← hck, hrowc.1]
          split_ifs <;> simp
        · have hpk := hpairK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr b)
          simp only [Sum.map_inr, Sum.map_inl, id_eq, hvalJ c hc] at hpk
          have hck : CK' (Sum.inl ⟨c, hc⟩) (Sum.inr b) =
              CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr b) := by
            simp [CK', ee, Matrix.submatrix_apply]
          rw [hpk, ← hck, hrowc.2]
          split_ifs <;> simp
      have hsub : ∀ x, x ∈ Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪
          {ggLin (p := p) ι (φ (Sum.inr b))} →
          x ∈ Subgroup.closure (Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o))) := by
        rintro x (hx | hx)
        · obtain ⟨i, rfl⟩ := hx
          exact Subgroup.subset_closure ⟨Sum.inl (e i), rfl⟩
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact Subgroup.subset_closure ⟨Sum.inr b, rfl⟩
      have hntA : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
            ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := p) ι (φ (Sum.inr b))}),
          ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
        fun g hg => hnt g ((Subgroup.closure_le _).mpr hsub hg)
      exact ggTWD_false_one hcells hF hdim
        (fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))) (fun i v => hform (Sum.inl (e i)) v)
        (ggLin (p := p) ι (φ (Sum.inr b))) (h (Sum.inr b)) (α (Sum.inr b))
        (fun v => hform (Sum.inr b) v) hαa hwb pos c0 m n hpatb hpair hntA

end CFSG.StandardType

end
