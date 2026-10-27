module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114SL3
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.Point

open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique CFSG.Quasithin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def fixVecs {Γ : Subgroup (GL ι F)} (U : Subgroup ↥Γ) : Set (ι → F) :=
  {x | ∀ u ∈ U, (((u : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x = x}

@[expose] def vecStab (Γ : Subgroup (GL ι F)) (W : Set (ι → F)) : Subgroup ↥Γ where
  carrier := {g | ∀ x, (((g : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x ∈ W ↔ x ∈ W}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro g h hg hh x
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hg, hh]
  inv_mem' := by
    intro g hg x
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [← hg]
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one, one_mulVec]

theorem mem_vecStab {Γ : Subgroup (GL ι F)} {W : Set (ι → F)} {g : ↥Γ} :
    g ∈ vecStab Γ W ↔ ∀ x, (((g : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x ∈ W ↔ x ∈ W :=
  Iff.rfl

@[expose] def PointProp (Γ : Subgroup (GL ι F)) : Prop :=
  ∀ U : Subgroup ↥Γ, IsSylowTwoOf U ⊤ →
    IsCoatom (vecStab Γ (fixVecs U)) ∧
      Subgroup.normalizer (U : Set ↥Γ) ≤ vecStab Γ (fixVecs U)

theorem mem_fixVecs_map_conj {Γ : Subgroup (GL ι F)} (U : Subgroup ↥Γ) (g : ↥Γ) (x : ι → F) :
    x ∈ fixVecs (U.map (MulAut.conj g).toMonoidHom) ↔
      (((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x ∈ fixVecs U := by
  have key : ∀ u : ↥Γ, (((g * u * g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x = x ↔
      (((u : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ ((((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x) =
        (((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x := by
    intro u
    have hg : ∀ y z : ι → F, (((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ y =
        (((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ z → y = z := by
      intro y z h
      have := congrArg (fun w => (((g : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ w) h
      simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, one_mulVec] at this
      exact this
    constructor
    · intro h
      conv_rhs => rw [← h]
      simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul]
      congr 3
      group
    · intro h
      apply hg
      rw [← h]
      simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul]
      congr 3
      group
  constructor
  · intro hx u hu
    exact (key u).mp (hx _ ⟨u, hu, rfl⟩)
  · rintro hx _ ⟨u, hu, rfl⟩
    exact (key u).mpr (hx u hu)

theorem vecStab_fixVecs_map_conj {Γ : Subgroup (GL ι F)} (U : Subgroup ↥Γ) (g : ↥Γ) :
    vecStab Γ (fixVecs (U.map (MulAut.conj g).toMonoidHom)) =
      (vecStab Γ (fixVecs U)).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_vecStab, Subgroup.mem_map_equiv, mem_vecStab]
  simp only [mem_fixVecs_map_conj]
  have e : (MulAut.conj g).symm h = g⁻¹ * h * g := by
    simp [MulAut.conj_symm_apply]
  rw [e]
  constructor
  · intro H y
    have := H ((((g : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ y)
    simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, one_mulVec] at this ⊢
    convert this using 4
    group
  · intro H y
    have := H ((((g⁻¹ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ y)
    simp only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul] at this ⊢
    convert this using 4
    group

theorem pointProp_of {Γ : Subgroup (GL ι F)} [Finite ↥Γ] {U₀ : Subgroup ↥Γ}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hco : IsCoatom (vecStab Γ (fixVecs U₀)))
    (hN : Subgroup.normalizer (U₀ : Set ↥Γ) ≤ vecStab Γ (fixVecs U₀)) : PointProp Γ := by
  intro U hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have toSyl : ∀ {V : Subgroup ↥Γ}, IsSylowTwoOf V ⊤ → ∃ P : Sylow 2 ↥Γ, (P : Subgroup ↥Γ) = V := by
    intro V hV
    have hi : ¬ 2 ∣ V.index := by
      have := hV.2.2
      change ¬ 2 ∣ V.relIndex ⊤ at this
      rwa [Subgroup.relIndex_top_right] at this
    exact ⟨hV.2.1.toSylow hi, rfl⟩
  obtain ⟨P₀, hP₀⟩ := toSyl hU₀
  obtain ⟨P, hP⟩ := toSyl hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ P₀ P
  have hUeq : U = U₀.map (MulAut.conj g).toMonoidHom := by
    rw [← hP, ← hg, Sylow.coe_subgroup_smul, ← hP₀]
    rfl
  subst hUeq
  rw [vecStab_fixVecs_map_conj]
  refine ⟨(OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) _).mpr hco, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hN

section Coord

variable {V : Type*} [CommGroup V] {Γ : Subgroup (GL ι F)} {A : Subgroup (MulAut V)}
  {π : ↥Γ →* ↥A} {Z : Subgroup V}

theorem exists_coord (hR : (FFModel.nat Γ).RealizesVia A ⊤ Z π) :
    ∃ f : V →* Multiplicative (ι → F), Function.Surjective f ∧ (∀ v, f v = 1 ↔ v ∈ Z) ∧
      ∀ (γ : ↥Γ) (v : V), Multiplicative.toAdd (f (((π γ : ↥A) : MulAut V) v)) =
        (((γ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ Multiplicative.toAdd (f v) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβ1, hβint⟩ := hR
  have hker : (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec ≤
      (FFModel.nat Γ).sec.subtype.ker := by
    intro m hm
    have hm' : (m : (FFModel.nat Γ).Amb) ∈ (FFModel.nat Γ).ker := hm
    rw [MonoidHom.mem_ker]
    exact hm'
  let g : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec →*
      (FFModel.nat Γ).Amb :=
    QuotientGroup.lift ((FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec)
      (FFModel.nat Γ).sec.subtype hker
  have hg : ∀ m : ↥(FFModel.nat Γ).sec, g (QuotientGroup.mk m) = m := fun m => rfl
  have hginj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [hg, hg] at hxy
        exact congrArg _ (Subtype.ext hxy)
  have hmem : ∀ a : (FFModel.nat Γ).Amb, a ∈ (FFModel.nat Γ).sec := fun a => Subgroup.mem_top a
  let f : V →* Multiplicative (ι → F) :=
    (g.comp β).comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom
  have hf : ∀ v : V, f v = g (β ⟨v, Subgroup.mem_top v⟩) := fun v => rfl
  have hβf : ∀ v : V, β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨f v, hmem _⟩ := by
    intro v
    apply hginj
    rw [hg, ← hf]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨a, hmem a⟩)
    refine ⟨u, ?_⟩
    rw [hf]
    have : (⟨(u : V), Subgroup.mem_top (u : V)⟩ : ↥(⊤ : Subgroup V)) = u := rfl
    rw [this, hu, hg]
  · intro v
    rw [hf, ← hβ1 ⟨v, Subgroup.mem_top v⟩]
    constructor
    · intro h
      apply hginj
      rw [h, map_one]
      rfl
    · intro h
      rw [h, map_one]
      rfl
  · intro γ v
    have h1 := hβint γ ⟨v, Subgroup.mem_top v⟩ ⟨f v, hmem _⟩ (Subgroup.mem_top _)
      (hmem _) (hβf v)
    have h2 : f (((π γ : ↥A) : MulAut V) v) = (FFModel.nat Γ).act γ (f v) := by
      have := congrArg g h1
      rw [hg] at this
      exact this
    rw [h2]
    rfl

end Coord

section Transport

variable {V : Type*} [CommGroup V]

@[expose] def wSet (S : Subgroup (MulAut V)) (Z : Subgroup V) : Set V :=
  {v | ∀ s ∈ S, s v * v⁻¹ ∈ Z}

@[expose] def stabSet (A : Subgroup (MulAut V)) (W : Set V) : Subgroup ↥A where
  carrier := {a | ∀ v, ((a : ↥A) : MulAut V) v ∈ W ↔ v ∈ W}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro a b ha hb v
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Subgroup.coe_mul, MulAut.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha v
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [← ha]
    rw [InvMemClass.coe_inv, MulAut.apply_inv_self]

theorem mem_stabSet {A : Subgroup (MulAut V)} {W : Set V} {a : ↥A} :
    a ∈ stabSet A W ↔ ∀ v, ((a : ↥A) : MulAut V) v ∈ W ↔ v ∈ W :=
  Iff.rfl

variable {Γ : Subgroup (GL ι F)} {A : Subgroup (MulAut V)} {π : ↥Γ →* ↥A} {Z : Subgroup V}

theorem isCoatom_stabSet (hR : (FFModel.nat Γ).RealizesVia A ⊤ Z π) (hP : PointProp Γ)
    {S : Subgroup ↥A} (hS : IsSylowTwoOf S ⊤) :
    IsCoatom (stabSet A (wSet (S.map A.subtype) Z)) ∧
      Subgroup.normalizer (S : Set ↥A) ≤ stabSet A (wSet (S.map A.subtype) Z) := by
  have hπs : Function.Surjective π := hR.1
  obtain ⟨f, hfs, hf1, hfint⟩ := exists_coord hR
  have hfeq : ∀ x y : V, x * y⁻¹ ∈ Z ↔ f x = f y := by
    intro x y
    rw [← hf1, map_mul, map_inv, mul_inv_eq_one]
  have hcov : ∀ x : ι → F, ∃ v : V, Multiplicative.toAdd (f v) = x := by
    intro x
    obtain ⟨v, hv⟩ := hfs (Multiplicative.ofAdd x)
    exact ⟨v, by rw [hv]; rfl⟩
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hfix : ∀ x : ι → F, (((γ : ↥Γ) : GL ι F) : Matrix ι ι F) *ᵥ x = x := by
      intro x
      obtain ⟨v, rfl⟩ := hcov x
      rw [← hfint, hγ]
      rfl
    have hM : (((γ : ↥Γ) : GL ι F) : Matrix ι ι F) = 1 := by
      ext i j
      have := congrFun (hfix (Pi.single j 1)) i
      rw [mulVec_single_one, Matrix.col_apply] at this
      rw [this, Matrix.one_apply, Pi.single_apply]
    exact Subtype.ext (Units.ext (by rw [hM]; rfl))
  set e : ↥Γ ≃* ↥A := MulEquiv.ofBijective π ⟨hπi, hπs⟩ with he
  set U : Subgroup ↥Γ := S.comap π with hU
  have hUe : U = S.map e.symm.toMonoidHom := by
    ext γ
    rw [hU, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    rfl
  have hUS : IsSylowTwoOf U ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨le_top, ?_, ?_⟩
    · rw [hUe]
      exact hS.2.1.map _
    · have h := hS.2.2
      change ¬ 2 ∣ S.relIndex ⊤ at h
      change ¬ 2 ∣ U.relIndex ⊤
      rw [Subgroup.relIndex_top_right] at h ⊢
      rwa [hUe, Subgroup.index_map_of_bijective e.symm.bijective]
  have hW : ∀ v : V, v ∈ wSet (S.map A.subtype) Z ↔
      Multiplicative.toAdd (f v) ∈ fixVecs U := by
    intro v
    constructor
    · intro hv γ hγ
      have h1 := hv _ ⟨π γ, hγ, rfl⟩
      rw [hfeq] at h1
      rw [← hfint, Subgroup.coe_subtype] at *
      rw [h1]
    · rintro hv _ ⟨s, hs, rfl⟩
      obtain ⟨γ, rfl⟩ := hπs s
      rw [Subgroup.coe_subtype, hfeq]
      have h1 := hv γ hs
      rw [← hfint] at h1
      exact congrArg Multiplicative.ofAdd h1
  have hkey : ∀ γ : ↥Γ, π γ ∈ stabSet A (wSet (S.map A.subtype) Z) ↔
      γ ∈ vecStab Γ (fixVecs U) := by
    intro γ
    rw [mem_stabSet, mem_vecStab]
    constructor
    · intro H x
      obtain ⟨v, rfl⟩ := hcov x
      rw [← hfint, ← hW, ← hW]
      exact H v
    · intro H v
      rw [hW, hW, hfint]
      exact H _
  have hmap : stabSet A (wSet (S.map A.subtype) Z) =
      (vecStab Γ (fixVecs U)).map e.toMonoidHom := by
    ext a
    obtain ⟨γ, rfl⟩ := hπs a
    rw [hkey, Subgroup.mem_map_equiv]
    have : e.symm (π γ) = γ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
  obtain ⟨hco, hN⟩ := hP U hUS
  refine ⟨?_, ?_⟩
  · rw [hmap]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).mpr hco
  · intro a ha
    obtain ⟨γ, rfl⟩ := hπs a
    rw [hkey]
    apply hN
    have h1 : S.map e.symm.toMonoidHom ≤ Subgroup.normalizer ((S.map e.symm.toMonoidHom :
        Subgroup ↥Γ) : Set ↥Γ) := Subgroup.le_normalizer
    rw [← hUe] at h1
    have h2 : e.symm (π γ) ∈ Subgroup.normalizer (U : Set ↥Γ) := by
      rw [hUe, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨π γ, ha, rfl⟩
    have : e.symm (π γ) = γ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rwa [this] at h2

end Transport

section SL3

open CFSG.Quasithin.H13.SL3

theorem fixVecs_unitri :
    fixVecs ((unitri F).subgroupOf (StatedSL 3 F)) = {x : Fin 3 → F | x 1 = 0 ∧ x 2 = 0} := by
  ext x
  constructor
  · intro hx
    have h1 := hx ⟨u1 F, u1_mem_statedSL⟩ (Subgroup.mem_subgroupOf.mpr u1_mem_unitri)
    have h2 := hx ⟨u2 F, u2_mem_statedSL⟩ (Subgroup.mem_subgroupOf.mpr u2_mem_unitri)
    have a := congrFun h1 0
    have b := congrFun h2 1
    simp only [coe_u1, coe_u2] at a b
    simp [mU1, mU2, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a b
    exact ⟨a, b⟩
  · rintro ⟨h1, h2⟩ u hu
    obtain ⟨u00, -, -, u10, u20, -⟩ := (Subgroup.mem_subgroupOf.mp hu : IsUnitri _)
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, u00, u10, u20]

theorem vecStab_line :
    vecStab (StatedSL 3 F) {x : Fin 3 → F | x 1 = 0 ∧ x 2 = 0} =
      (lineStab F).subgroupOf (StatedSL 3 F) := by
  have hfwd : ∀ g : GL (Fin 3) F, g ∈ lineStab F → ∀ x : Fin 3 → F, x 1 = 0 → x 2 = 0 →
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 1 = 0 ∧
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = 0 := by
    intro g hg x hx1 hx2
    obtain ⟨g10, g20⟩ := hg
    constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx1, hx2, g10, g20]
  ext g
  rw [mem_vecStab, Subgroup.mem_subgroupOf]
  constructor
  · intro H
    have h0 : (Pi.single (0 : Fin 3) (1 : F) : Fin 3 → F) ∈
        {x : Fin 3 → F | x 1 = 0 ∧ x 2 = 0} := by
      simp
    have := (H _).mpr h0
    rw [mulVec_single_one] at this
    exact this
  · intro hg x
    constructor
    · intro hx
      have hinv := (lineStab F).inv_mem hg
      have := hfwd _ hinv _ hx.1 hx.2
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hx
      exact hfwd _ hg x hx.1 hx.2

theorem isCoatom_lineStab : IsCoatom ((lineStab F).subgroupOf (StatedSL 3 F)) := by
  refine ⟨fun h => ?_, fun Q hQ => ?_⟩
  · have : (⟨wSL F, wSL_mem_statedSL⟩ : ↥(StatedSL 3 F)) ∈ (lineStab F).subgroupOf (StatedSL 3 F) :=
      by rw [h]; trivial
    exact wSL_notMem_lineStab (Subgroup.mem_subgroupOf.mp this)
  · obtain ⟨q, hqQ, hq⟩ := IsConcreteLE.exists_of_lt hQ
    have hle := statedSL_le_of_lineStab_lt (H := Q.map (StatedSL 3 F).subtype)
      (Subgroup.map_subtype_le Q)
      (fun g hg => ⟨⟨g, hg.1⟩, hQ.le (Subgroup.mem_subgroupOf.mpr hg.2), rfl⟩)
      ⟨q, hqQ, rfl⟩ (fun h => hq (Subgroup.mem_subgroupOf.mpr h))
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem normalizer_unitri_le :
    Subgroup.normalizer (((unitri F).subgroupOf (StatedSL 3 F) : Subgroup ↥(StatedSL 3 F)) :
      Set ↥(StatedSL 3 F)) ≤ (lineStab F).subgroupOf (StatedSL 3 F) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have hc : ∀ u : ↥(StatedSL 3 F), (u : GL (Fin 3) F) ∈ unitri F →
      (g : GL (Fin 3) F)⁻¹ * u * g ∈ lineStab F := by
    intro u hu
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) u).mp
      (Subgroup.mem_subgroupOf.mpr hu)
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact unitri_le_lineStab h1
  exact mem_lineStab_of_conj (hc ⟨u1 F, u1_mem_statedSL⟩ u1_mem_unitri)
    (hc ⟨u2 F, u2_mem_statedSL⟩ u2_mem_unitri)

theorem pointProp_sl3 [Finite F] {m : ℕ} (hm : 1 ≤ m) (hq : Nat.card F = 2 ^ m) :
    PointProp (StatedSL 3 F) := by
  have : Fintype F := Fintype.ofFinite F
  have hU : IsSylowTwoOf ((unitri F).subgroupOf (StatedSL 3 F)) ⊤ := by
    refine ⟨le_top, isPGroup_unitri hq, ?_⟩
    change ¬ 2 ∣ ((unitri F).subgroupOf (StatedSL 3 F)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact not_two_dvd_index_unitri hm hq
  refine pointProp_of hU ?_ ?_
  · rw [fixVecs_unitri, vecStab_line]
    exact isCoatom_lineStab
  · rw [fixVecs_unitri, vecStab_line]
    exact normalizer_unitri_le

end SL3

section Sp4

open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher

theorem fixVecs_unipotent :
    fixVecs (unipotent 2 F) = ((isoFlag 2 F 1 : Submodule F (Fin 2 ⊕ Fin 2 → F)) :
      Set (Fin 2 ⊕ Fin 2 → F)) := by
  ext x
  rw [SetLike.mem_coe, mem_isoFlag]
  constructor
  · intro hx
    have hC1 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![1, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    have hC2 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    have hA : IsUnitriangular (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) := by
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> simp
    obtain ⟨g1, hg1, hg1e⟩ := exists_mem_unipotent (r := 2) (K := F) isUnitriangular_one hC1
    obtain ⟨g2, hg2, hg2e⟩ := exists_mem_unipotent (r := 2) (K := F) isUnitriangular_one hC2
    obtain ⟨g3, hg3, hg3e⟩ := exists_mem_unipotent (r := 2) (K := F) hA (transpose_zero)
    have e1 := congrFun (hx g1 hg1) (Sum.inl 0)
    have e2 := congrFun (hx g2 hg2) (Sum.inl 1)
    have e3 := congrFun (hx g3 hg3) (Sum.inl 0)
    rw [hg1e] at e1
    rw [hg2e] at e2
    rw [hg3e] at e3
    simp [blockMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2 e3
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact e1
      · exact e2
    · fin_cases j
      · simp at hj
      · exact e3
  · rintro ⟨hz, hy⟩ g hg
    obtain ⟨A, C, hA, -, hge⟩ := mem_unipotent.mp hg
    rw [hge]
    have hz' : (x ∘ Sum.inr : Fin 2 → F) = 0 := funext fun j => hz j
    have hy1 : x (Sum.inl 1) = 0 := hy 1 (by simp)
    have hA10 : A 1 0 = 0 := hA.1 (by decide)
    have hA00 : A 0 0 = 1 := hA.2 0
    ext i
    rcases i with i | i
    · simp only [blockMat, fromBlocks_mulVec, hz', mulVec_zero, add_zero, Sum.elim_inl]
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hy1, hA10, hA00]
    · simp only [blockMat, fromBlocks_mulVec, hz', mulVec_zero, zero_mulVec, add_zero,
        Sum.elim_inr]
      exact (hz i).symm

theorem vecStab_isoFlag :
    vecStab (StatedSp 2 F) ((isoFlag 2 F 1 : Submodule F (Fin 2 ⊕ Fin 2 → F)) :
      Set (Fin 2 ⊕ Fin 2 → F)) = stabilizer 2 F (flag 2 F 1) := by
  have hflag : flag 2 F 1 = isoFlag 2 F 1 := by
    rw [flag, ite_eq_left (by norm_num : (1 : ℕ) ≤ 2)]
  rw [hflag]
  ext g
  rw [mem_vecStab, mem_stabilizer]
  constructor
  · intro H
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (H v).mpr hv
    · intro w hw
      refine ⟨(((g⁻¹ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w, ?_, ?_⟩
      · apply (H _).mp
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
        exact hw
      · rw [mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul,
          mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  · intro H x
    constructor
    · intro hx
      rw [← H] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [mulVecLin_apply] at hyx
      have hinj : Function.Injective ((((g : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec) := by
        intro a b hab
        have := congrArg ((((g⁻¹ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec) hab
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul] using this
      rw [← hinj hyx]
      exact hy
    · intro hx
      rw [← H]
      exact ⟨x, hx, rfl⟩

theorem pointProp_sp4 [Finite F] [CharP F 2] : PointProp (StatedSp 2 F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsSylowTwoOf (unipotent 2 F) ⊤ := by
    refine ⟨le_top, hP ▸ P.isPGroup', ?_⟩
    change ¬ 2 ∣ (unipotent 2 F).relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← hP]
    exact P.not_dvd_index
  refine pointProp_of hU ?_ ?_
  · rw [fixVecs_unipotent, vecStab_isoFlag]
    exact ⟨stabilizer_flag_ne_top (by norm_num) (by norm_num), fun Q hQ =>
      ((eq_of_stabilizer_flag_le (by norm_num) Q hQ.le).resolve_left hQ.ne')⟩
  · rw [fixVecs_unipotent, vecStab_isoFlag, normalizer_unipotent]
    exact borelSubgroup_le_stabilizer_flag (by norm_num)

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecB.Point
