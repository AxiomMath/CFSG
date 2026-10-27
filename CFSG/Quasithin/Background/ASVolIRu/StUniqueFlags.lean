module

public import CFSG.Quasithin.Recognition.RuTypeDefs
import CFSG.Quasithin.Recognition.RuTypeSL3

public section

namespace CFSG.Quasithin.RuType.StUnique

open scoped MatrixGroups Matrix

abbrev Vec : Type := Fin 3 → ZMod 2

def IsFlag (x : Vec × Vec) : Prop := x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.2 ⬝ᵥ x.1 = 0

instance : DecidablePred IsFlag := fun x =>
  inferInstanceAs (Decidable (x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.2 ⬝ᵥ x.1 = 0))

abbrev Flag : Type := {x : Vec × Vec // IsFlag x}

theorem card_flag : Fintype.card Flag = 21 := by decide +kernel

def flagAct (g : SL(3, ZMod 2)) (x : Vec × Vec) : Vec × Vec :=
  ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x.1,
    x.2 ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))

theorem flagAct_one (x : Vec × Vec) : flagAct 1 x = x := by
  simp [flagAct]

theorem flagAct_mul (g h : SL(3, ZMod 2)) (x : Vec × Vec) :
    flagAct (g * h) x = flagAct g (flagAct h x) := by
  simp [flagAct, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, mul_inv_rev]

theorem flagAct_inv_flagAct (g : SL(3, ZMod 2)) (x : Vec × Vec) :
    flagAct g⁻¹ (flagAct g x) = x := by
  rw [← flagAct_mul, inv_mul_cancel, flagAct_one]

theorem isFlag_flagAct (g : SL(3, ZMod 2)) {x : Vec × Vec} (hx : IsFlag x) :
    IsFlag (flagAct g x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have e := flagAct_inv_flagAct g x
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, ?_⟩
  · rw [← e]
    show ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (flagAct g x).1 = 0
    rw [h, Matrix.mulVec_zero]
  · rw [← e]
    show (flagAct g x).2 ᵥ* ((g⁻¹⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
    rw [h, Matrix.zero_vecMul]
  · show (x.2 ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x.1) = 0
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact h3

instance : MulAction SL(3, ZMod 2) Flag where
  smul g x := ⟨flagAct g x.1, isFlag_flagAct g x.2⟩
  one_smul x := Subtype.ext (flagAct_one x.1)
  mul_smul g h x := Subtype.ext (flagAct_mul g h x.1)

theorem smul_fst (g : SL(3, ZMod 2)) (x : Flag) :
    (g • x).1.1 = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x.1.1 := by
  show (flagAct g x.1).1 = _
  simp [flagAct]

theorem smul_snd (g : SL(3, ZMod 2)) (x : Flag) :
    (g • x).1.2 = x.1.2 ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  show (flagAct g x.1).2 = _
  simp [flagAct]

def x₀ : Flag := ⟨(![1, 0, 0], ![0, 0, 1]), by decide⟩

theorem flag_transitive : ∀ x : Flag, ∃ g : SL(3, ZMod 2), g • x₀ = x := by
  decide +kernel

instance : MulAction.IsPretransitive SL(3, ZMod 2) Flag where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := flag_transitive x
    obtain ⟨h, hh⟩ := flag_transitive y
    exact ⟨h * g⁻¹, by rw [← hg, ← hh, mul_smul, inv_smul_smul]⟩

theorem card_stabilizer : Nat.card (MulAction.stabilizer SL(3, ZMod 2) x₀) = 8 := by
  have hF : Nat.card Flag = 21 := by rw [Nat.card_eq_fintype_card, card_flag]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer SL(3, ZMod 2) x₀)
  rw [MulAction.index_stabilizer_of_transitive, SL3.card_SL3, hF] at h1
  omega

abbrev FlagMod : Type := Flag → ZMod 2

def modAct (g : SL(3, ZMod 2)) (f : FlagMod) : FlagMod := fun x => f (g⁻¹ • x)

theorem modAct_apply (g : SL(3, ZMod 2)) (f : FlagMod) (x : Flag) :
    modAct g f x = f (g⁻¹ • x) := by
  simp [modAct]

def modActHom (g : SL(3, ZMod 2)) : FlagMod →ₗ[ZMod 2] FlagMod where
  toFun := modAct g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem modActHom_apply (g : SL(3, ZMod 2)) (f : FlagMod) : modActHom g f = modAct g f := by
  unfold modActHom
  rfl

def betaMap : Matrix (Fin 3) (Fin 3) (ZMod 2) →ₗ[ZMod 2] FlagMod where
  toFun A x := x.1.2 ⬝ᵥ (A *ᵥ x.1.1)
  map_add' A B := by
    funext x
    simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by
    funext x
    simp [Matrix.smul_mulVec, dotProduct_smul]

theorem betaMap_stAct (g : SL(3, ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    betaMap (stAct g A) = modAct g (betaMap A) := by
  funext x
  show x.1.2 ⬝ᵥ ((stAct g A) *ᵥ x.1.1) = (x.1.2 ᵥ* (((g⁻¹)⁻¹ : SL(3, ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ (A *ᵥ (((g⁻¹ : SL(3, ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x.1.1))
  rw [inv_inv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [stAct, Matrix.mul_assoc]

def pointVec (p : Vec) : FlagMod := fun x => if x.1.1 = p then 1 else 0

def lineVec (ℓ : Vec) : FlagMod := fun x => if x.1.2 = ℓ then 1 else 0

theorem inv_mulVec_eq_iff (g : SL(3, ZMod 2)) (p q : Vec) :
    ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ q = p ↔
      q = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ p := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem vecMul_eq_iff (g : SL(3, ZMod 2)) (l l' : Vec) :
    l' ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = l ↔
      l' = l ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  constructor
  · rintro rfl
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  · rintro rfl
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem mulVec_ne_zero (g : SL(3, ZMod 2)) {p : Vec} (hp : p ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ p ≠ 0 := by
  intro h
  apply hp
  have h2 := (inv_mulVec_eq_iff g p ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ p)).mpr rfl
  rw [h, Matrix.mulVec_zero] at h2
  exact h2.symm

theorem vecMul_ne_zero (g : SL(3, ZMod 2)) {l : Vec} (hl : l ≠ 0) :
    l ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 := by
  intro h
  apply hl
  have h2 := (vecMul_eq_iff g l
    (l ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).mpr rfl
  rw [h, Matrix.zero_vecMul] at h2
  exact h2.symm

theorem modAct_pointVec (g : SL(3, ZMod 2)) (p : Vec) :
    modAct g (pointVec p) = pointVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ p) := by
  funext x
  simp only [modAct, pointVec, smul_fst, inv_mulVec_eq_iff]

theorem modAct_lineVec (g : SL(3, ZMod 2)) (l : Vec) :
    modAct g (lineVec l) =
      lineVec (l ᵥ* ((g⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  funext x
  simp only [modAct, lineVec, smul_snd, inv_inv, vecMul_eq_iff]

abbrev NZ : Type := {v : Vec // v ≠ 0}

theorem card_NZ : Fintype.card NZ = 7 := by decide +kernel

def pointSpan : Submodule (ZMod 2) FlagMod :=
  Submodule.span (ZMod 2) (Set.range fun p : NZ => pointVec p.1)

def lineSpan : Submodule (ZMod 2) FlagMod :=
  Submodule.span (ZMod 2) (Set.range fun l : NZ => lineVec l.1)

theorem pointSpan_eq :
    pointSpan = Submodule.span (ZMod 2) (Set.range fun p : NZ => pointVec p.1) := by
  rw [pointSpan]

theorem lineSpan_eq :
    lineSpan = Submodule.span (ZMod 2) (Set.range fun l : NZ => lineVec l.1) := by
  rw [lineSpan]

theorem pointVec_mem {p : Vec} (hp : p ≠ 0) : pointVec p ∈ pointSpan :=
  Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩

theorem lineVec_mem {l : Vec} (hl : l ≠ 0) : lineVec l ∈ lineSpan :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem modAct_mem_pointSpan (g : SL(3, ZMod 2)) {f : FlagMod} (hf : f ∈ pointSpan) :
    modAct g f ∈ pointSpan := by
  have h : pointSpan ≤ pointSpan.comap (modActHom g) := by
    rw [pointSpan, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, modActHom_apply, modAct_pointVec]
    exact pointVec_mem (mulVec_ne_zero g p.2)
  exact h hf

theorem modAct_mem_lineSpan (g : SL(3, ZMod 2)) {f : FlagMod} (hf : f ∈ lineSpan) :
    modAct g f ∈ lineSpan := by
  have h : lineSpan ≤ lineSpan.comap (modActHom g) := by
    rw [lineSpan, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, modActHom_apply, modAct_lineVec]
    exact lineVec_mem (vecMul_ne_zero g l.2)
  exact h hf

def slSub : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) (ZMod 2) (ZMod 2))

theorem mem_slSub {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} : A ∈ slSub ↔ A.trace = 0 := by
  simp [slSub, LinearMap.mem_ker]

theorem card_slSub : Nat.card slSub = 2 ^ 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun A => mem_slSub), Nat.card_eq_fintype_card,
    SL3.card_traceZero]
  norm_num

theorem stAct_mem_slSub (g : SL(3, ZMod 2)) {A : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA : A ∈ slSub) : stAct g A ∈ slSub :=
  mem_slSub.mpr (by rw [SL3.trace_stAct]; exact mem_slSub.mp hA)

def decompSpan : Submodule (ZMod 2) FlagMod :=
  Submodule.map betaMap slSub ⊔ pointSpan ⊔ lineSpan

theorem decompSpan_invariant (g : SL(3, ZMod 2)) {f : FlagMod} (hf : f ∈ decompSpan) :
    modAct g f ∈ decompSpan := by
  have h : decompSpan ≤ decompSpan.comap (modActHom g) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨A, hA, rfl⟩
      rw [Submodule.mem_comap, modActHom_apply, ← betaMap_stAct]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨stAct g A, stAct_mem_slSub g hA, rfl⟩)
    · intro f hf
      rw [Submodule.mem_comap, modActHom_apply]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (modAct_mem_pointSpan g hf))
    · intro f hf
      rw [Submodule.mem_comap, modActHom_apply]
      exact Submodule.mem_sup_right (modAct_mem_lineSpan g hf)
  exact h hf

theorem single_x₀_eq : (Pi.single x₀ 1 : FlagMod) =
    betaMap !![0, 0, 1; 0, 0, 0; 0, 0, 0] +
      (pointVec ![0, 0, 1] + pointVec ![0, 1, 1] + pointVec ![1, 0, 0] + pointVec ![1, 0, 1] +
        pointVec ![1, 1, 1]) + (lineVec ![0, 1, 0] + lineVec ![0, 1, 1]) := by
  have h : (Pi.single x₀ 1 : FlagMod) = fun y => if y = x₀ then 1 else 0 := by
    funext y
    simp [Pi.single_apply]
  rw [h]
  funext y
  revert y
  decide +kernel

theorem single_x₀_mem : (Pi.single x₀ 1 : FlagMod) ∈ decompSpan := by
  rw [single_x₀_eq]
  have hs : (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ slSub := by
    rw [mem_slSub]
    decide
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, hs, rfl⟩)
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (pointVec_mem ?_) (pointVec_mem ?_)) (pointVec_mem ?_))
      (pointVec_mem ?_)) (pointVec_mem ?_) <;> decide
  · refine Submodule.mem_sup_right (Submodule.add_mem _ (lineVec_mem ?_) (lineVec_mem ?_)) <;>
      decide

theorem decompSpan_eq_top : decompSpan = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ x, f x • (Pi.single x (1 : ZMod 2) : FlagMod) := by
    funext y
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hf]
  refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
  obtain ⟨g, rfl⟩ := flag_transitive x
  have h : (Pi.single (g • x₀) (1 : ZMod 2) : FlagMod) = modAct g (Pi.single x₀ 1) := by
    funext y
    simp only [modAct, Pi.single_apply, inv_smul_eq_iff]
  rw [h]
  exact decompSpan_invariant g single_x₀_mem

theorem flagMod_decomp (f : FlagMod) :
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 ∧
      ∃ e₁ ∈ pointSpan, ∃ e₂ ∈ lineSpan, f = betaMap A + e₁ + e₂ := by
  have hf : f ∈ decompSpan := by
    rw [decompSpan_eq_top]
    trivial
  obtain ⟨u, hu, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨v, hv, e₁, he₁, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨A, hA, rfl⟩ := hv
  exact ⟨A, mem_slSub.mp hA, e₁, he₁, e₂, he₂, rfl⟩

end CFSG.Quasithin.RuType.StUnique
