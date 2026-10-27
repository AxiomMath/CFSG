module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTWPatV
public import CFSG.LocalAnalysis.StandardType.GGTWDWeyl36

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWUp_false_one {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hcells : GGTWDCells1 p N)
    {Bs L J K : Subgroup G} (h : GGTWUpCfg p N 1 Bs L J K) : False := by
  classical
  obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, hh, α, xV,
    hcore, hdim⟩ := h
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  obtain ⟨hb, hcardk, hJpos, hWMK, hCK, _hk2, hφeq, hF, hpairK, hntCore, hex, _hAuto,
    _hJauto⟩ := hcore
  haveI : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; rcases hN with h | h | h | h | h <;> omega)
  obtain ⟨a, c0, m, n, hpat, hpair, hαa⟩ :=
    ggTW_pat1_V (p := p) (N := N) hp hpN hN (pos := pos) (V := V) (Λ := Λ) (b₁ := b₁)
      (b₂ := b₂) (Λa := Λa) (MK := MK) (CK := CK) (e := e) (h := hh) (α := α) (xV := xV)
      hb hcardk hJpos hWMK hCK hF hpairK
  haveI : Subsingleton Λa :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have hw : α (Sum.inr a) xV ≠ 0 := by
    obtain ⟨a', ha'⟩ := hex
    rwa [Subsingleton.elim a' a] at ha'
  have hr : ∀ (i : Fin (N - 1)) (v : V), ggLin (p := p) ι (φ (Sum.inl (e i))) v =
      v - α (Sum.inl (e i)) v • hh (Sum.inl (e i)) := fun i v => hφeq (Sum.inl (e i)) v
  have hra : ∀ v, ggLin (p := p) ι (φ (Sum.inr a)) v =
      v - α (Sum.inr a) v • hh (Sum.inr a) := fun v => hφeq (Sum.inr a) v
  have hsub : Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪
      {ggLin (p := p) ι (φ (Sum.inr a))} ⊆
      Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) := by
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨Sum.inl (e i), rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨Sum.inr a, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := p) ι (φ (Sum.inr a))}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hntCore g (Subgroup.closure_mono hsub hg)
  exact ggTWD_false_one hcells (V := V) hF hdim
    (fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))) hr
    (ggLin (p := p) ι (φ (Sum.inr a))) (hh (Sum.inr a)) (α (Sum.inr a)) hra hαa hw
    pos c0 m n hpat hpair hnt

theorem ggTWUp_false_two {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hcells : GGTWDCells2 p N)
    {Bs L J K : Subgroup G} (h : GGTWUpCfg p N 2 Bs L J K) : False := by
  classical
  obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, hh, α, xV,
    hcore, hdim⟩ := h
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  obtain ⟨hb, hcardk, hJpos, hWMK, hCK, hk2, hφeq, hF, hpairK, hntCore, hex, _hAuto,
    _hJauto⟩ := hcore
  haveI : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; rcases hN with h | h | h | h | h <;> omega)
  obtain ⟨a₁, a₂, c, c₂, hane, hpat, hpair, h12, h21, h11, h22⟩ :=
    ggTW_pat2_V (p := p) (N := N) hp hpN hN (pos := pos) (V := V) (Λ := Λ) (b₁ := b₁)
      (b₂ := b₂) (Λa := Λa) (MK := MK) (CK := CK) (e := e) (h := hh) (α := α) (xV := xV)
      hb hcardk hJpos hWMK hCK (hk2 rfl) hF hpairK
  have hall : ∀ b : Λa, b = a₁ ∨ b = a₂ := by
    obtain ⟨y, _hy_ne, hy_all⟩ := (Nat.card_eq_two_iff' a₁).mp hcardk
    have hy_eq : y = a₂ := (hy_all a₂ (Ne.symm hane)).symm
    intro b
    by_cases hb' : b = a₁
    · exact Or.inl hb'
    · right
      rw [← hy_eq]
      exact hy_all b hb'
  have hw : α (Sum.inr a₁) xV ≠ 0 ∨ α (Sum.inr a₂) xV ≠ 0 := by
    obtain ⟨b, hb'⟩ := hex
    rcases hall b with hb1 | hb2
    · left
      rw [hb1] at hb'
      exact hb'
    · right
      rw [hb2] at hb'
      exact hb'
  have hr : ∀ (i : Fin (N - 1)) (v : V), ggLin (p := p) ι (φ (Sum.inl (e i))) v =
      v - α (Sum.inl (e i)) v • hh (Sum.inl (e i)) := fun i v => hφeq (Sum.inl (e i)) v
  have hra1 : ∀ v, ggLin (p := p) ι (φ (Sum.inr a₁)) v =
      v - α (Sum.inr a₁) v • hh (Sum.inr a₁) := fun v => hφeq (Sum.inr a₁) v
  have hra2 : ∀ v, ggLin (p := p) ι (φ (Sum.inr a₂)) v =
      v - α (Sum.inr a₂) v • hh (Sum.inr a₂) := fun v => hφeq (Sum.inr a₂) v
  have hsub : Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪
      {ggLin (p := p) ι (φ (Sum.inr a₁)), ggLin (p := p) ι (φ (Sum.inr a₂))} ⊆
      Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) := by
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨Sum.inl (e i), rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact ⟨Sum.inr a₁, rfl⟩
      · rw [hx]
        exact ⟨Sum.inr a₂, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := p) ι (φ (Sum.inr a₁)), ggLin (p := p) ι (φ (Sum.inr a₂))}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hntCore g (Subgroup.closure_mono hsub hg)
  exact ggTWD_false_two hcells (V := V) hF hdim
    (fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))) hr
    (ggLin (p := p) ι (φ (Sum.inr a₁))) (ggLin (p := p) ι (φ (Sum.inr a₂)))
    (hh (Sum.inr a₁)) (hh (Sum.inr a₂)) (α (Sum.inr a₁)) (α (Sum.inr a₂))
    hra1 hra2 hw pos c c₂ hpat ⟨hpair, h12, h21, h11, h22⟩ hnt

theorem ggTWUp_weyl36_one
    (hcells : GGTWDCells36Orb) {G : Type} [Group G] [Finite G] {Bs L J K : Subgroup G}
    (h : GGTWUpCfg 3 6 1 Bs L J K) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, hh, α, xV,
    hcore, hdim⟩ := h
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  obtain ⟨hb, hcardk, hJpos, hWMK, hCK, _hk2, hφeq, hF, hpairK, hntCore, hex, hAuto,
    _hJauto⟩ := hcore
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨a, c0, m, n, hpat, hpair, hαa⟩ :=
    ggTW_pat1_V (p := 3) (N := 6) (by norm_num) (by norm_num) (by decide) (pos := pos) (V := V)
      (Λ := Λ) (b₁ := b₁) (b₂ := b₂) (Λa := Λa) (MK := MK) (CK := CK) (e := e) (h := hh)
      (α := α) (xV := xV) hb hcardk hJpos hWMK hCK hF hpairK
  haveI : Subsingleton Λa :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have hw : α (Sum.inr a) xV ≠ 0 := by
    obtain ⟨a', ha'⟩ := hex
    rwa [Subsingleton.elim a' a] at ha'
  have hr : ∀ (i : Fin (6 - 1)) (v : V), ggLin (p := 3) ι (φ (Sum.inl (e i))) v =
      v - α (Sum.inl (e i)) v • hh (Sum.inl (e i)) := fun i v => hφeq (Sum.inl (e i)) v
  have hra : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a)) v =
      v - α (Sum.inr a) v • hh (Sum.inr a) := fun v => hφeq (Sum.inr a) v
  have hrange : Set.range (fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) =
      Set.range (fun i : Fin (6 - 1) => ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := 3) ι (φ (Sum.inr a))} := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      rcases o with l | b
      · exact Or.inl ⟨e.symm l, by simp⟩
      · right
        simp [Subsingleton.elim b a]
    · rintro (⟨i, rfl⟩ | hx)
      · exact ⟨Sum.inl (e i), rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨Sum.inr a, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (6 - 1) =>
        ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := 3) ι (φ (Sum.inr a))}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    rw [← hrange]
    exact hntCore
  have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range (fun i : Fin (6 - 1) => ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := 3) ι (φ (Sum.inr a))}) := by
    rw [hAuto, MonoidHom.map_closure]
    refine congrArg Subgroup.closure ?_
    rw [← Set.range_comp]
    exact hrange
  exact ggTWD_weyl_one_36 hcells (V := V) ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) hF hdim
    (fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))) hr
    (ggLin (p := 3) ι (φ (Sum.inr a))) (hh (Sum.inr a)) (α (Sum.inr a)) hra hαa hw hA
    pos c0 m n hpat hpair hnt

theorem ggTWUp_weyl36_two
    (hcells : GGTWDCells36Orb) {G : Type} [Group G] [Finite G] {Bs L J K : Subgroup G}
    (h : GGTWUpCfg 3 6 2 Bs L J K) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, hh, α, xV,
    hcore, hdim⟩ := h
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  obtain ⟨hb, hcardk, hJpos, hWMK, hCK, hk2, hφeq, hF, hpairK, hntCore, hex, hAuto,
    _hJauto⟩ := hcore
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨a₁, a₂, c, c₂, hane, hpat, hpair, h12, h21, h11, h22⟩ :=
    ggTW_pat2_V (p := 3) (N := 6) (by norm_num) (by norm_num) (by decide) (pos := pos) (V := V)
      (Λ := Λ) (b₁ := b₁) (b₂ := b₂) (Λa := Λa) (MK := MK) (CK := CK) (e := e) (h := hh)
      (α := α) (xV := xV) hb hcardk hJpos hWMK hCK (hk2 rfl) hF hpairK
  have hall : ∀ b : Λa, b = a₁ ∨ b = a₂ := by
    obtain ⟨y, _hy_ne, hy_all⟩ := (Nat.card_eq_two_iff' a₁).mp hcardk
    have hy_eq : y = a₂ := (hy_all a₂ (Ne.symm hane)).symm
    intro b
    by_cases hb' : b = a₁
    · exact Or.inl hb'
    · right
      rw [← hy_eq]
      exact hy_all b hb'
  have hw : α (Sum.inr a₁) xV ≠ 0 ∨ α (Sum.inr a₂) xV ≠ 0 := by
    obtain ⟨b, hb'⟩ := hex
    rcases hall b with hb1 | hb2
    · left
      rw [hb1] at hb'
      exact hb'
    · right
      rw [hb2] at hb'
      exact hb'
  have hr : ∀ (i : Fin (6 - 1)) (v : V), ggLin (p := 3) ι (φ (Sum.inl (e i))) v =
      v - α (Sum.inl (e i)) v • hh (Sum.inl (e i)) := fun i v => hφeq (Sum.inl (e i)) v
  have hra1 : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a₁)) v =
      v - α (Sum.inr a₁) v • hh (Sum.inr a₁) := fun v => hφeq (Sum.inr a₁) v
  have hra2 : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a₂)) v =
      v - α (Sum.inr a₂) v • hh (Sum.inr a₂) := fun v => hφeq (Sum.inr a₂) v
  have hrange : Set.range (fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) =
      Set.range (fun i : Fin (6 - 1) => ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := 3) ι (φ (Sum.inr a₁)), ggLin (p := 3) ι (φ (Sum.inr a₂))} := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      rcases o with l | b
      · exact Or.inl ⟨e.symm l, by simp⟩
      · rcases hall b with hb | hb
        · right
          simp [hb]
        · right
          simp [hb]
    · rintro (⟨i, rfl⟩ | hx)
      · exact ⟨Sum.inl (e i), rfl⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact ⟨Sum.inr a₁, rfl⟩
        · rw [hx]
          exact ⟨Sum.inr a₂, rfl⟩
  have hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (6 - 1) =>
        ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := 3) ι (φ (Sum.inr a₁)), ggLin (p := 3) ι (φ (Sum.inr a₂))}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    rw [← hrange]
    exact hntCore
  have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range (fun i : Fin (6 - 1) => ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪
        {ggLin (p := 3) ι (φ (Sum.inr a₁)), ggLin (p := 3) ι (φ (Sum.inr a₂))}) := by
    rw [hAuto, MonoidHom.map_closure]
    refine congrArg Subgroup.closure ?_
    rw [← Set.range_comp]
    exact hrange
  exact ggTWD_weyl_two_36 hcells (V := V) ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) hF hdim
    (fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))) hr
    (ggLin (p := 3) ι (φ (Sum.inr a₁))) (ggLin (p := 3) ι (φ (Sum.inr a₂)))
    (hh (Sum.inr a₁)) (hh (Sum.inr a₂)) (α (Sum.inr a₁)) (α (Sum.inr a₂))
    hra1 hra2 hw hA pos c c₂ hpat ⟨hpair, h12, h21, h11, h22⟩ hnt

end CFSG.StandardType

end
