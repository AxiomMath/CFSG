module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix

private def matAddEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (g : GL ι K) : AddAut (ι → K) where
  toFun v := (g : Matrix ι ι K) *ᵥ v
  invFun v := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
  map_add' _ _ := Matrix.mulVec_add _ _ _
  left_inv v := by simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv v := by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

@[simp] private lemma matAddEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (g : GL ι K) (v : ι → K) :
    matAddEquiv g v = (g : Matrix ι ι K) *ᵥ v :=
  rfl

private def actHom {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (X : Subgroup (GL ι K)) : X →* Multiplicative (AddAut (ι → K)) where
  toFun g := Multiplicative.ofAdd (matAddEquiv (g : GL ι K))
  map_one' := by
    refine congrArg Multiplicative.ofAdd (AddEquiv.ext fun v => ?_)
    simp
  map_mul' g h := by
    refine congrArg Multiplicative.ofAdd (AddEquiv.ext fun v => ?_)
    simp [Matrix.mulVec_mulVec]

private lemma mulVec_mem_iSup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {ι' : Sort*} (X : Subgroup (GL ι K)) {F : ι' → AddSubgroup (ι → K)}
    (hF : ∀ i, ∀ A ∈ X, ∀ v ∈ F i, (A : Matrix ι ι K) *ᵥ v ∈ F i) :
    ∀ A ∈ X, ∀ v ∈ ⨆ i, F i, (A : Matrix ι ι K) *ᵥ v ∈ ⨆ i, F i := by
  intro A hA v hv
  refine AddSubgroup.iSup_induction F
    (C := fun v => (A : Matrix ι ι K) *ᵥ v ∈ ⨆ i, F i) hv ?_ ?_ ?_
  · intro i x hx
    exact AddSubgroup.mem_iSup_of_mem i (hF i A hA x hx)
  · simp
  · intro x y hx hy
    show (A : Matrix ι ι K) *ᵥ (x + y) ∈ ⨆ i, F i
    rw [Matrix.mulVec_add]
    exact AddSubgroup.add_mem _ hx hy

private lemma exists_ne_zero_of_ne_bot' {V : Type*} [AddCommGroup V] {H : AddSubgroup V}
    (h : H ≠ ⊥) : ∃ x ∈ H, x ≠ 0 := by
  obtain ⟨⟨x, hx⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp h
  exact ⟨x, hx, fun h' => hx0 (Subtype.ext h')⟩

private def scaleSub (K : Type) [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (W₀ : AddSubgroup V) (c : Kˣ) : AddSubgroup V where
  carrier := {v | (c : K)⁻¹ • v ∈ W₀}
  add_mem' := fun {a b} ha hb => by
    have ha' : (c : K)⁻¹ • a ∈ W₀ := ha
    have hb' : (c : K)⁻¹ • b ∈ W₀ := hb
    show (c : K)⁻¹ • (a + b) ∈ W₀
    rw [smul_add]
    exact W₀.add_mem ha' hb'
  zero_mem' := by
    show (c : K)⁻¹ • (0 : V) ∈ W₀
    rw [smul_zero]
    exact W₀.zero_mem
  neg_mem' := fun {a} ha => by
    have ha' : (c : K)⁻¹ • a ∈ W₀ := ha
    show (c : K)⁻¹ • (-a) ∈ W₀
    rw [smul_neg]
    exact W₀.neg_mem ha'

private lemma scaleSub_ne_bot {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {W₀ : AddSubgroup V} (hW₀ : W₀ ≠ ⊥) (c : Kˣ) : scaleSub K W₀ c ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_ne_bot' hW₀
  intro h
  have hmem : (c : K) • w ∈ scaleSub K W₀ c := by
    show (c : K)⁻¹ • ((c : K) • w) ∈ W₀
    rw [inv_smul_smul₀ (Units.ne_zero c)]
    exact hw
  rw [h, AddSubgroup.mem_bot, smul_eq_zero] at hmem
  exact hmem.elim (Units.ne_zero c) hw0

private lemma scaleSub_inv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} {W₀ : AddSubgroup (ι → K)}
    (hW₀ : ∀ A ∈ X, ∀ v ∈ W₀, (A : Matrix ι ι K) *ᵥ v ∈ W₀) (c : Kˣ) :
    ∀ A ∈ X, ∀ v ∈ scaleSub K W₀ c, (A : Matrix ι ι K) *ᵥ v ∈ scaleSub K W₀ c := by
  intro A hA v hv
  have hv' : (c : K)⁻¹ • v ∈ W₀ := hv
  show (c : K)⁻¹ • ((A : Matrix ι ι K) *ᵥ v) ∈ W₀
  rw [← Matrix.mulVec_smul]
  exact hW₀ A hA _ hv'

private lemma scaleSub_simple {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} {W₀ : AddSubgroup (ι → K)}
    (hmin : ∀ T : AddSubgroup (ι → K), T ≤ W₀ →
      (∀ A ∈ X, ∀ v ∈ T, (A : Matrix ι ι K) *ᵥ v ∈ T) → T = ⊥ ∨ T = W₀)
    (c : Kˣ) (T : AddSubgroup (ι → K)) (hT : T ≤ scaleSub K W₀ c)
    (hTinv : ∀ A ∈ X, ∀ v ∈ T, (A : Matrix ι ι K) *ᵥ v ∈ T) :
    T = ⊥ ∨ T = scaleSub K W₀ c := by
  have hc : (c : K) ≠ 0 := Units.ne_zero c
  let T' : AddSubgroup (ι → K) :=
    { carrier := {u | (c : K) • u ∈ T}
      add_mem' := fun {a b} ha hb => by
        have ha' : (c : K) • a ∈ T := ha
        have hb' : (c : K) • b ∈ T := hb
        show (c : K) • (a + b) ∈ T
        rw [smul_add]
        exact T.add_mem ha' hb'
      zero_mem' := by
        show (c : K) • (0 : ι → K) ∈ T
        rw [smul_zero]
        exact T.zero_mem
      neg_mem' := fun {a} ha => by
        have ha' : (c : K) • a ∈ T := ha
        show (c : K) • (-a) ∈ T
        rw [smul_neg]
        exact T.neg_mem ha' }
  have hT'le : T' ≤ W₀ := by
    intro u hu
    have hu' : (c : K) • u ∈ T := hu
    have h1 : (c : K)⁻¹ • ((c : K) • u) ∈ W₀ := hT hu'
    rwa [inv_smul_smul₀ hc] at h1
  have hT'inv : ∀ A ∈ X, ∀ v ∈ T', (A : Matrix ι ι K) *ᵥ v ∈ T' := by
    intro A hA v hv
    have hv' : (c : K) • v ∈ T := hv
    show (c : K) • ((A : Matrix ι ι K) *ᵥ v) ∈ T
    rw [← Matrix.mulVec_smul]
    exact hTinv A hA _ hv'
  rcases hmin T' hT'le hT'inv with h' | h'
  · left
    rw [eq_bot_iff]
    intro t ht
    have hu : (c : K)⁻¹ • t ∈ T' := by
      show (c : K) • ((c : K)⁻¹ • t) ∈ T
      rw [smul_inv_smul₀ hc]
      exact ht
    rw [h', AddSubgroup.mem_bot] at hu
    rw [AddSubgroup.mem_bot, ← smul_inv_smul₀ hc t, hu, smul_zero]
  · right
    apply le_antisymm hT
    intro v hv
    have hu : (c : K)⁻¹ • v ∈ T' := by
      rw [h']
      exact hv
    have hu' : (c : K) • ((c : K)⁻¹ • v) ∈ T := hu
    rwa [smul_inv_smul₀ hc] at hu'

private lemma scaleSub_iSup_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} (hirr : NatIrred X) {W₀ : AddSubgroup (ι → K)} (hW₀ : W₀ ≠ ⊥)
    (hW₀inv : ∀ A ∈ X, ∀ v ∈ W₀, (A : Matrix ι ι K) *ᵥ v ∈ W₀) :
    (⨆ c : Kˣ, scaleSub K W₀ c) = ⊤ := by
  have hsmul : ∀ v ∈ ⨆ c : Kˣ, scaleSub K W₀ c, ∀ a : K,
      a • v ∈ ⨆ c : Kˣ, scaleSub K W₀ c := by
    intro v hv
    refine AddSubgroup.iSup_induction (fun c : Kˣ => scaleSub K W₀ c)
      (C := fun v => ∀ a : K, a • v ∈ ⨆ c : Kˣ, scaleSub K W₀ c) hv ?_ ?_ ?_
    · intro d v hv a
      by_cases ha : a = 0
      · rw [ha, zero_smul]
        exact AddSubgroup.zero_mem _
      · have hmem : a • v ∈ scaleSub K W₀ (Units.mk0 a ha * d) := by
          show ((Units.mk0 a ha * d : Kˣ) : K)⁻¹ • (a • v) ∈ W₀
          rw [Units.val_mul, Units.val_mk0, smul_smul, _root_.mul_inv_rev, mul_assoc,
            inv_mul_cancel₀ ha, mul_one]
          exact hv
        exact AddSubgroup.mem_iSup_of_mem (Units.mk0 a ha * d) hmem
    · intro a
      rw [smul_zero]
      exact AddSubgroup.zero_mem _
    · intro x y hx hy a
      rw [smul_add]
      exact AddSubgroup.add_mem _ (hx a) (hy a)
  have hUinv : ∀ A ∈ X, ∀ v ∈ ⨆ c : Kˣ, scaleSub K W₀ c,
      (A : Matrix ι ι K) *ᵥ v ∈ ⨆ c : Kˣ, scaleSub K W₀ c :=
    mulVec_mem_iSup X (fun c A hA v hv => scaleSub_inv hW₀inv c A hA v hv)
  let Us : Submodule K (ι → K) :=
    { carrier := {v | v ∈ ⨆ c : Kˣ, scaleSub K W₀ c}
      add_mem' := fun {a b} ha hb => by
        have ha' : a ∈ ⨆ c : Kˣ, scaleSub K W₀ c := ha
        have hb' : b ∈ ⨆ c : Kˣ, scaleSub K W₀ c := hb
        show a + b ∈ ⨆ c : Kˣ, scaleSub K W₀ c
        exact AddSubgroup.add_mem _ ha' hb'
      zero_mem' := by
        show (0 : ι → K) ∈ ⨆ c : Kˣ, scaleSub K W₀ c
        exact AddSubgroup.zero_mem _
      smul_mem' := fun a {x} hx => hsmul x hx a }
  rcases hirr Us (fun A hA v hv => hUinv A hA v hv) with hbot | htop
  · exfalso
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_ne_bot' hW₀
    have hw1 : w ∈ scaleSub K W₀ 1 := by
      show ((1 : Kˣ) : K)⁻¹ • w ∈ W₀
      rw [Units.val_one, inv_one, one_smul]
      exact hw
    have hwU : w ∈ Us := AddSubgroup.mem_iSup_of_mem (1 : Kˣ) hw1
    rw [hbot, Submodule.mem_bot] at hwU
    exact hw0 hwU
  · rw [eq_top_iff]
    intro v _
    have hvUs : v ∈ Us := by
      rw [htop]
      exact Submodule.mem_top
    exact hvUs

private lemma comm_of_decomp {V : Type*} [AddCommGroup V] (p : V →+ V) (M : V → V)
    (A B : AddSubgroup V) (hcov : A ⊔ B = ⊤) (hpA : ∀ a ∈ A, p a = a)
    (hpB : ∀ b ∈ B, p b = 0) (hM : ∀ x y, M (x + y) = M x + M y)
    (hMA : ∀ a ∈ A, M a ∈ A) (hMB : ∀ b ∈ B, M b ∈ B) (v : V) :
    p (M v) = M (p v) := by
  have hv : v ∈ A ⊔ B := by
    rw [hcov]
    exact AddSubgroup.mem_top v
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hv
  have hpv : p (a + b) = a := by
    rw [map_add, hpA a ha, hpB b hb, add_zero]
  rw [hpv, hM, map_add, hpA _ (hMA a ha), hpB _ (hMB b hb), add_zero]

private lemma exists_proj {V : Type*} [AddCommGroup V] (A B : AddSubgroup V)
    (hdisj : Disjoint A B) (hcov : A ⊔ B = ⊤) :
    ∃ p : V →+ V, (∀ a ∈ A, p a = a) ∧ (∀ b ∈ B, p b = 0) := by
  have hAB : Disjoint (AddSubgroup.toIntSubmodule A) (AddSubgroup.toIntSubmodule B) := by
    rw [Submodule.disjoint_def]
    intro x hxA hxB
    have hx : x ∈ A ⊓ B := AddSubgroup.mem_inf.mpr ⟨hxA, hxB⟩
    rw [disjoint_iff.mp hdisj, AddSubgroup.mem_bot] at hx
    exact hx
  have hco : Codisjoint (AddSubgroup.toIntSubmodule A) (AddSubgroup.toIntSubmodule B) := by
    rw [codisjoint_iff, ← map_sup AddSubgroup.toIntSubmodule A B, hcov, map_top]
  have hcompl : IsCompl (AddSubgroup.toIntSubmodule A) (AddSubgroup.toIntSubmodule B) :=
    ⟨hAB, hco⟩
  have hr : IsCompl (LinearMap.range (AddSubgroup.toIntSubmodule A).subtype)
      (AddSubgroup.toIntSubmodule B) := by
    rw [Submodule.range_subtype]
    exact hcompl
  have hi := Submodule.injective_subtype (AddSubgroup.toIntSubmodule A)
  refine ⟨((AddSubgroup.toIntSubmodule A).subtype.comp
    (LinearMap.linearProjOfIsCompl _ _ hi hr)).toAddMonoidHom, ?_, ?_⟩
  · intro a ha
    have h1 := LinearMap.linearProjOfIsCompl_apply_left _ _ hi hr ⟨a, ha⟩
    have h2 : LinearMap.linearProjOfIsCompl _ _ hi hr a = ⟨a, ha⟩ := h1
    show (AddSubgroup.toIntSubmodule A).subtype (LinearMap.linearProjOfIsCompl _ _ hi hr a) = a
    rw [h2]
    rfl
  · intro b hb
    have h1 := LinearMap.linearProjOfIsCompl_apply_right' _ _ hi hr b hb
    show (AddSubgroup.toIntSubmodule A).subtype (LinearMap.linearProjOfIsCompl _ _ hi hr b) = 0
    rw [h1, map_zero]

private lemma core_two_summands {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} (hcomm : AddCommutantScalar X)
    {J : Type*} {F : J → AddSubgroup (ι → K)} (hind : iSupIndep F) (hsup : ⨆ j, F j = ⊤)
    (hinv : ∀ j, ∀ A ∈ X, ∀ v ∈ F j, (A : Matrix ι ι K) *ᵥ v ∈ F j)
    (hne : ∀ j, F j ≠ ⊥) {j₀ j₁ : J} (h01 : j₀ ≠ j₁) : False := by
  have hdisj : Disjoint (F j₀) (⨆ (j : J) (_ : j ≠ j₀), F j) :=
    hind.disjoint_biSup (x := j₀) (y := {j | j ≠ j₀}) (by simp)
  have hcov : F j₀ ⊔ (⨆ (j : J) (_ : j ≠ j₀), F j) = ⊤ :=
    (iSup_split_single F j₀).symm.trans hsup
  have hBinv : ∀ A ∈ X, ∀ v ∈ ⨆ (j : J) (_ : j ≠ j₀), F j,
      (A : Matrix ι ι K) *ᵥ v ∈ ⨆ (j : J) (_ : j ≠ j₀), F j :=
    mulVec_mem_iSup X (F := fun j : J => ⨆ (_ : j ≠ j₀), F j)
      (fun j => mulVec_mem_iSup X (F := fun _ : j ≠ j₀ => F j) (fun _ => hinv j))
  obtain ⟨p, hpA, hpB⟩ := exists_proj (F j₀) (⨆ (j : J) (_ : j ≠ j₀), F j) hdisj hcov
  have hpc : ∀ A ∈ X, ∀ v, p ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ p v := by
    intro A hA v
    exact comm_of_decomp p (fun w => (A : Matrix ι ι K) *ᵥ w) (F j₀)
      (⨆ (j : J) (_ : j ≠ j₀), F j) hcov hpA hpB (fun x y => Matrix.mulVec_add _ _ _)
      (fun a ha => hinv j₀ A hA a ha) (fun b hb => hBinv A hA b hb) v
  obtain ⟨c, hc⟩ := hcomm p hpc
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_ne_bot' (hne j₀)
  have hj1 : F j₁ ≤ ⨆ (j : J) (_ : j ≠ j₀), F j :=
    le_iSup₂ (f := fun j (_ : j ≠ j₀) => F j) j₁ h01.symm
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_ne_bot' (hne j₁)
  have hbB : b ∈ ⨆ (j : J) (_ : j ≠ j₀), F j := hj1 hb
  have e1 : c • a = a := (hc a).symm.trans (hpA a ha)
  have e2 : c • b = 0 := (hc b).symm.trans (hpB b hbB)
  have hc0 : c = 0 := (smul_eq_zero.mp e2).resolve_right hb0
  apply ha0
  rw [hc0, zero_smul] at e1
  exact e1.symm

theorem eq_top_of_addInvariant {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {X : Subgroup (GL ι K)} (hirr : NatIrred X) (hcomm : AddCommutantScalar X)
    {W : AddSubgroup (ι → K)} (hW0 : W ≠ ⊥)
    (hWinv : ∀ A ∈ X, ∀ v ∈ W, (A : Matrix ι ι K) *ᵥ v ∈ W) : W = ⊤ := by
  have hfin : Finite (AddSubgroup (ι → K)) :=
    Finite.of_injective (fun L : AddSubgroup (ι → K) => (L : Set (ι → K)))
      SetLike.coe_injective
  obtain ⟨W₀, ⟨hW₀0, hW₀W, hW₀inv⟩, hW₀min⟩ :=
    (Set.toFinite {T : AddSubgroup (ι → K) | T ≠ ⊥ ∧ T ≤ W ∧
      ∀ A ∈ X, ∀ v ∈ T, (A : Matrix ι ι K) *ᵥ v ∈ T}).exists_minimal
      ⟨W, hW0, le_rfl, hWinv⟩
  have hmin : ∀ T : AddSubgroup (ι → K), T ≤ W₀ →
      (∀ A ∈ X, ∀ v ∈ T, (A : Matrix ι ι K) *ᵥ v ∈ T) → T = ⊥ ∨ T = W₀ := by
    intro T hTW hTinv
    by_cases hT : T = ⊥
    · exact Or.inl hT
    · exact Or.inr (le_antisymm hTW (hW₀min ⟨hT, hTW.trans hW₀W, hTinv⟩ hTW))
  have hsum : (⨆ c : Kˣ, scaleSub K W₀ c) = ⊤ := scaleSub_iSup_eq_top hirr hW₀0 hW₀inv
  obtain ⟨J, -, hJind, hJsup⟩ := exists_iSupIndep_of_simple (actHom X) (scaleSub K W₀)
    (fun c h v hv => scaleSub_inv hW₀inv c h.1 h.2 v hv)
    (fun c => ⟨scaleSub_ne_bot hW₀0 c, fun T hT hTinv =>
      scaleSub_simple hmin c T hT (fun A hA v hv => hTinv ⟨A, hA⟩ v hv)⟩)
  have hJtop : (⨆ j : J, scaleSub K W₀ (j : Kˣ)) = ⊤ := hJsup.trans hsum
  have hcore : ∀ j₀ j₁ : J, j₀ = j₁ := by
    intro j₀ j₁
    by_contra h
    exact core_two_summands hcomm (F := fun j : J => scaleSub K W₀ (j : Kˣ)) hJind hJtop
      (fun j A hA v hv => scaleSub_inv hW₀inv (j : Kˣ) A hA v hv)
      (fun j => scaleSub_ne_bot hW₀0 (j : Kˣ)) h
  have hJne : Nonempty J := by
    by_contra hcon
    have hempty : IsEmpty J := not_nonempty_iff.mp hcon
    have hbot : (⨆ j : J, scaleSub K W₀ (j : Kˣ)) = ⊥ := iSup_of_empty _
    obtain ⟨w, _, hw0⟩ := exists_ne_zero_of_ne_bot' hW₀0
    have hw' : w ∈ (⨆ j : J, scaleSub K W₀ (j : Kˣ)) := by
      rw [hJtop]
      exact AddSubgroup.mem_top w
    rw [hbot, AddSubgroup.mem_bot] at hw'
    exact hw0 hw'
  obtain ⟨j₀⟩ := hJne
  have hle : (⨆ j : J, scaleSub K W₀ (j : Kˣ)) ≤ scaleSub K W₀ (j₀ : Kˣ) := by
    refine iSup_le fun j => ?_
    exact le_of_eq (congrArg (fun k : J => scaleSub K W₀ (k : Kˣ)) (hcore j j₀))
  have htop : scaleSub K W₀ (j₀ : Kˣ) = ⊤ := by
    apply top_le_iff.mp
    rw [← hJtop]
    exact hle
  have hW₀top : W₀ = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hmem : ((j₀ : Kˣ) : K) • w ∈ scaleSub K W₀ (j₀ : Kˣ) := by
      rw [htop]
      exact AddSubgroup.mem_top _
    have hmem' : ((j₀ : Kˣ) : K)⁻¹ • (((j₀ : Kˣ) : K) • w) ∈ W₀ := hmem
    rwa [inv_smul_smul₀ (Units.ne_zero _)] at hmem'
  rw [hW₀top] at hW₀W
  exact top_le_iff.mp hW₀W

end CFSG.RankThree.GF2n.Stroth80
