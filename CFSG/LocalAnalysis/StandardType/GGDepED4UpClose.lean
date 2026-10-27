module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGDepED4Check
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def l05nEC_eJ {Λ : Type} (b₁ b₂ : Λ) (e : Fin 6 ≃ Λ)
    (hb₁ : b₁ = e 0) (hb₂ : b₂ = e 5) :
    {c : Fin 6 // GGDepED4In c} ≃ {i : Λ // i ≠ b₁ ∧ i ≠ b₂} where
  toFun c := ⟨e c.1, by
    have hc : c.1 ≠ 0 ∧ c.1 ≠ 5 := c.2
    exact ⟨fun hh => hc.1 (e.injective (by rw [hh, hb₁])),
      fun hh => hc.2 (e.injective (by rw [hh, hb₂]))⟩⟩
  invFun i := ⟨e.symm i.1, by
    exact ⟨fun hh => i.2.1 (by
        have h : i.1 = e 0 := by simpa using congrArg e hh
        exact h.trans hb₁.symm),
      fun hh => i.2.2 (by
        have h : i.1 = e 5 := by simpa using congrArg e hh
        exact h.trans hb₂.symm)⟩⟩
  left_inv c := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp

theorem ggDepED4Up_false_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (h : GGDepED4UpCfg p 1 Bs L J K) : False := by
  classical
  obtain ⟨Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α, xV,
    hcore, hdim⟩ := h
  obtain ⟨hb₁, hb₂, hcardk, hWMK, hCK, _hk2, hφeq, hF, hpairK, hntCore, hex, _hAuto,
    _hJauto⟩ := hcore
  have hp3 : p = 3 := hF.p3
  subst hp3
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcardk).1
  obtain ⟨a⟩ := (Nat.card_eq_one_iff_unique.mp hcardk).2
  let eJ := l05nEC_eJ b₁ b₂ e hb₁ hb₂
  let F : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ≃ Option {c : Fin 6 // GGDepED4In c} :=
    { toFun := fun o => match o with
        | Sum.inl i => some (eJ.symm i)
        | Sum.inr _ => none
      invFun := fun o => match o with
        | some c => Sum.inl (eJ c)
        | none => Sum.inr a
      left_inv := by
        rintro (i | x)
        · show Sum.inl (eJ (eJ.symm i)) = Sum.inl i
          rw [Equiv.apply_symm_apply]
        · show Sum.inr a = Sum.inr x
          rw [Subsingleton.elim a x]
      right_inv := by
        rintro (_ | c)
        · rfl
        · show some (eJ.symm (eJ c)) = some c
          rw [Equiv.symm_apply_apply] }
  let MK' : CoxeterMatrix (Option {c : Fin 6 // GGDepED4In c}) := MK.reindex F
  let CK' : Matrix (Option {c : Fin 6 // GGDepED4In c})
      (Option {c : Fin 6 // GGDepED4In c}) ℤ := Matrix.reindex F F CK
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK F
  have hCK' : GGIntCartan MK' CK' := GGIntCartan.reindex F hCK
  have hF_none : F.symm none = Sum.inr a := rfl
  have hF_some : ∀ c : {c : Fin 6 // GGDepED4In c},
      F.symm (some c) = Sum.inl (eJ c) := fun c => rfl
  have hJ' : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK' (some i) (some j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at hpk
    have hck : CK' (some i) (some j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply, hF_some i, hF_some j]
    have hgoal : α (Sum.inl (eJ i).1) (h (Sum.inl (eJ j).1)) =
        (CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) : ZMod 3) := hpk
    rw [hck, ← hgoal]
    exact hF.pair i.1 j.1
  obtain ⟨c0, hleaf, hbonds⟩ := ggDepED4_pattern1 hWMK' hCK' hJ'
  let hE : Fin 6 → V := fun i => h (Sum.inl (e i))
  let αE : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let rE : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))
  let raE : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (φ (Sum.inr a))
  let haE : V := h (Sum.inr a)
  let αaE : Module.Dual (ZMod 3) V := α (Sum.inr a)
  have hrE : ∀ i v, rE i v = v - αE i v • hE i := fun i v => hφeq (Sum.inl (e i)) v
  have hraE : ∀ v, raE v = v - αaE v • haE := fun v => hφeq (Sum.inr a) v
  have hαa : αaE haE = 2 := by
    have hpk := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpk
    have hgoal : αaE haE = (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := hpk
    rw [hgoal, hCK.1 (Sum.inr a)]
    norm_num
  have hw : αaE xV ≠ 0 := by
    obtain ⟨a', ha'⟩ := hex
    rw [Subsingleton.elim a' a] at ha'
    exact ha'
  have hpair : ∀ c : Fin 6, GGDepED4In c →
      αaE (hE c) = (if c = c0 then (-1 : ZMod 3) else 0) ∧
        αE c haE = (if c = c0 then (-1 : ZMod 3) else 0) := by
    intro c hc
    have hb := hbonds ⟨c, hc⟩
    constructor
    · have hck : CK' none (some ⟨c, hc⟩) = CK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩)) := by
        simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply, hF_none, hF_some]
      have hCKval : CK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩)) =
          (if c = c0 then (-1 : ℤ) else 0) := by
        rw [← hck, hb.1]
      have hpk := hpairK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αaE (hE c) = (CK (Sum.inr a) (Sum.inl (eJ ⟨c, hc⟩)) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
    · have hck : CK' (some ⟨c, hc⟩) none = CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a) := by
        simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply, hF_none, hF_some]
      have hCKval : CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a) =
          (if c = c0 then (-1 : ℤ) else 0) := by
        rw [← hck, hb.2]
      have hpk := hpairK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αE c haE = (CK (Sum.inl (eJ ⟨c, hc⟩)) (Sum.inr a) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
  have hsub : Set.range rE ∪ {raE} ⊆ Set.range (fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) := by
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨Sum.inl (e i), rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨Sum.inr a, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range rE ∪ {raE}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hntCore g (Subgroup.closure_mono hsub hg)
  exact ggDepED4_false_one ggDepED4_cells1 (h := hE) (α := αE) (x := xV)
    hF hdim rE hrE raE haE αaE hraE hαa hw c0 hleaf hpair hnt

theorem ggDepED4Up_false_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (h : GGDepED4UpCfg p 2 Bs L J K) : False := by
  classical
  obtain ⟨Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α, xV,
    hcore, hdim⟩ := h
  obtain ⟨hb₁, hb₂, hcardk, hWMK, hCK, hk2, hφeq, hF, hpairK, hntCore, hex, _hAuto,
    _hJauto⟩ := hcore
  have hp3 : p = 3 := hF.p3
  subst hp3
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  let eJ := l05nEC_eJ b₁ b₂ e hb₁ hb₂
  let ee : ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) :=
    Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := MK.reindex ee.symm
  let CK' : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)
      ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK ee.symm
  have hCK' : GGIntCartan MK' CK' := by
    have hh := GGIntCartan.reindex (e := ee.symm) hCK
    simpa [MK', CK', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using hh
  have hE' : ∃ eK : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa),
      MK' = CoxeterMatrix.E₆.reindex eK := by
    obtain ⟨eK, heK⟩ := hk2 rfl
    exact ⟨eK.trans ee.symm, by
      show MK.reindex ee.symm = CoxeterMatrix.E₆.reindex (eK.trans ee.symm)
      rw [heK, l05nBL_reindex_trans]⟩
  have hJ' : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK' (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at hpk
    have hck : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
    have hgoal : α (Sum.inl (eJ i).1) (h (Sum.inl (eJ j).1)) =
        (CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) : ZMod 3) := hpk
    rw [hck, ← hgoal]
    exact hF.pair i.1 j.1
  obtain ⟨a₁, a₂, c, c', hane, hleafc, hleafc', _hcc', hpairJ, _h12, _h21, _h11, _h22⟩ :=
    ggDepED4_pattern2 hcardk hWMK' hCK' hE' hJ'
  let hE : Fin 6 → V := fun i => h (Sum.inl (e i))
  let αE : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let rE : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))
  let ra1E : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (φ (Sum.inr a₁))
  let ra2E : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (φ (Sum.inr a₂))
  let ha1E : V := h (Sum.inr a₁)
  let ha2E : V := h (Sum.inr a₂)
  let αa1E : Module.Dual (ZMod 3) V := α (Sum.inr a₁)
  let αa2E : Module.Dual (ZMod 3) V := α (Sum.inr a₂)
  have hrE : ∀ i v, rE i v = v - αE i v • hE i := fun i v => hφeq (Sum.inl (e i)) v
  have hra1E : ∀ v, ra1E v = v - αa1E v • ha1E := fun v => hφeq (Sum.inr a₁) v
  have hra2E : ∀ v, ra2E v = v - αa2E v • ha2E := fun v => hφeq (Sum.inr a₂) v
  have hαa1 : αa1E ha1E = 2 := by
    have hpk := hpairK (Sum.inr a₁) (Sum.inr a₁)
    simp only [Sum.map_inr, id_eq] at hpk
    have hgoal : αa1E ha1E = (CK (Sum.inr a₁) (Sum.inr a₁) : ZMod 3) := hpk
    rw [hgoal, hCK.1 (Sum.inr a₁)]
    norm_num
  have hαa2 : αa2E ha2E = 2 := by
    have hpk := hpairK (Sum.inr a₂) (Sum.inr a₂)
    simp only [Sum.map_inr, id_eq] at hpk
    have hgoal : αa2E ha2E = (CK (Sum.inr a₂) (Sum.inr a₂) : ZMod 3) := hpk
    rw [hgoal, hCK.1 (Sum.inr a₂)]
    norm_num
  have hall : ∀ b : Λa, b = a₁ ∨ b = a₂ := by
    obtain ⟨y, _hy_ne, hy_all⟩ := (Nat.card_eq_two_iff' a₁).mp hcardk
    have hy_eq : y = a₂ := (hy_all a₂ (Ne.symm hane)).symm
    intro b
    by_cases hb' : b = a₁
    · exact Or.inl hb'
    · right
      rw [← hy_eq]
      exact hy_all b hb'
  have hw : αa1E xV ≠ 0 ∨ αa2E xV ≠ 0 := by
    obtain ⟨b, hb'⟩ := hex
    rcases hall b with hb1 | hb2
    · left
      have h : αa1E xV = α (Sum.inr b) xV := by rw [hb1]
      rw [h]; exact hb'
    · right
      have h : αa2E xV = α (Sum.inr b) xV := by rw [hb2]
      rw [h]; exact hb'
  have hpair1 : ∀ j : Fin 6, GGDepED4In j →
      αa1E (hE j) = (if j = c then (-1 : ZMod 3) else 0) ∧
        αE j ha1E = (if j = c then (-1 : ZMod 3) else 0) := by
    intro j hj
    have hb := hpairJ ⟨j, hj⟩
    constructor
    · have hck : CK' (Sum.inr a₁) (Sum.inl ⟨j, hj⟩) =
          CK (Sum.inr a₁) (Sum.inl (eJ ⟨j, hj⟩)) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
      have hCKval : CK (Sum.inr a₁) (Sum.inl (eJ ⟨j, hj⟩)) =
          (if j = c then (-1 : ℤ) else 0) := by
        rw [← hck, hb.1]
      have hpk := hpairK (Sum.inr a₁) (Sum.inl (eJ ⟨j, hj⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αa1E (hE j) = (CK (Sum.inr a₁) (Sum.inl (eJ ⟨j, hj⟩)) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
    · have hck : CK' (Sum.inl ⟨j, hj⟩) (Sum.inr a₁) =
          CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₁) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
      have hCKval : CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₁) =
          (if j = c then (-1 : ℤ) else 0) := by
        rw [← hck, hb.2.1]
      have hpk := hpairK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₁)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αE j ha1E = (CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₁) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
  have hpair2 : ∀ j : Fin 6, GGDepED4In j →
      αa2E (hE j) = (if j = c' then (-1 : ZMod 3) else 0) ∧
        αE j ha2E = (if j = c' then (-1 : ZMod 3) else 0) := by
    intro j hj
    have hb := hpairJ ⟨j, hj⟩
    constructor
    · have hck : CK' (Sum.inr a₂) (Sum.inl ⟨j, hj⟩) =
          CK (Sum.inr a₂) (Sum.inl (eJ ⟨j, hj⟩)) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
      have hCKval : CK (Sum.inr a₂) (Sum.inl (eJ ⟨j, hj⟩)) =
          (if j = c' then (-1 : ℤ) else 0) := by
        rw [← hck, hb.2.2.1]
      have hpk := hpairK (Sum.inr a₂) (Sum.inl (eJ ⟨j, hj⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αa2E (hE j) = (CK (Sum.inr a₂) (Sum.inl (eJ ⟨j, hj⟩)) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
    · have hck : CK' (Sum.inl ⟨j, hj⟩) (Sum.inr a₂) =
          CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₂) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
      have hCKval : CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₂) =
          (if j = c' then (-1 : ℤ) else 0) := by
        rw [← hck, hb.2.2.2]
      have hpk := hpairK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₂)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αE j ha2E = (CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a₂) : ZMod 3) := hpk
      rw [hgoal, hCKval]
      split_ifs <;> simp
  have hsub : Set.range rE ∪ {ra1E, ra2E} ⊆
      Set.range (fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) := by
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨Sum.inl (e i), rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact ⟨Sum.inr a₁, rfl⟩
      · rw [hx]
        exact ⟨Sum.inr a₂, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range rE ∪ {ra1E, ra2E}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hntCore g (Subgroup.closure_mono hsub hg)
  exact ggDepED4_false_two ggDepED4_cells1 (h := hE) (α := αE) (x := xV)
    hF hdim rE hrE ra1E ra2E ha1E ha2E αa1E αa2E hra1E hra2E hαa1 hαa2 hw c c' hleafc hleafc'
    hpair1 hpair2 hnt

end CFSG.StandardType

end
