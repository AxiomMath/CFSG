module

public import CFSG.Quasithin.Vol2.KGFactRankSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.KGRank

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

@[expose] def boolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun l => [false :: l, true :: l]

theorem mem_boolLists : ∀ l : List Bool, l ∈ boolLists l.length
  | [] => by simp [boolLists]
  | b :: l => by
    simp only [List.length_cons, boolLists, List.mem_flatMap]
    exact ⟨l, mem_boolLists l, by cases b <;> simp⟩

@[expose] def utB : List Bool → Fin 5 → Fin 5 → Bool
  | [a01, a02, a03, a04, a12, a13, a14, a23, a24, a34] =>
    ![![true, a01, a02, a03, a04], ![false, true, a12, a13, a14], ![false, false, true, a23, a24],
      ![false, false, false, true, a34], ![false, false, false, false, true]]
  | _ => fun _ _ => false

@[expose] def xorsum (B : Fin 5 → Fin 5 → Bool) (i j : Fin 5) : Bool :=
  (B i 0 && B 0 j) ^^ (B i 1 && B 1 j) ^^ (B i 2 && B 2 j) ^^ (B i 3 && B 3 j) ^^ (B i 4 && B 4 j)

@[expose] def sqOKB (B : Fin 5 → Fin 5 → Bool) : Bool :=
  (List.finRange 5).all fun i => (List.finRange 5).all fun j => xorsum B i j == decide (i = j)

theorem card_sqOK : ((boolLists 10).filter fun l => sqOKB (utB l)).length = 192 := by
  decide +kernel

@[expose] def bitF2 (a : ZMod 2) : Bool := decide (a = 1)

theorem bitF2_add (a b : ZMod 2) : bitF2 (a + b) = (bitF2 a ^^ bitF2 b) := by
  revert a b; decide

theorem bitF2_mul (a b : ZMod 2) : bitF2 (a * b) = (bitF2 a && bitF2 b) := by
  revert a b; decide

theorem bitF2_injective : Function.Injective bitF2 := by
  intro a b; revert a b; decide

@[expose] def code (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : List Bool :=
  [bitF2 (g 0 1), bitF2 (g 0 2), bitF2 (g 0 3), bitF2 (g 0 4), bitF2 (g 1 2), bitF2 (g 1 3),
    bitF2 (g 1 4), bitF2 (g 2 3), bitF2 (g 2 4), bitF2 (g 3 4)]

theorem utB_code {g : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hl : ∀ i j : Fin 5, j < i → g i j = 0)
    (hd : ∀ i : Fin 5, g i i = 1) : utB (code g) = fun i j => bitF2 (g i j) := by
  have h0 : bitF2 0 = false := rfl
  have h1 : bitF2 1 = true := rfl
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [utB, code, hd, h0, h1, hl _ _ (show (0 : Fin 5) < 1 by decide),
      hl _ _ (show (0 : Fin 5) < 2 by decide), hl _ _ (show (0 : Fin 5) < 3 by decide),
      hl _ _ (show (0 : Fin 5) < 4 by decide), hl _ _ (show (1 : Fin 5) < 2 by decide),
      hl _ _ (show (1 : Fin 5) < 3 by decide), hl _ _ (show (1 : Fin 5) < 4 by decide),
      hl _ _ (show (2 : Fin 5) < 3 by decide), hl _ _ (show (2 : Fin 5) < 4 by decide),
      hl _ _ (show (3 : Fin 5) < 4 by decide)]

theorem sqOKB_of_mul_self {g : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : g * g = 1) :
    sqOKB (fun i j => bitF2 (g i j)) = true := by
  simp only [sqOKB, List.all_eq_true, beq_iff_eq]
  intro i _ j _
  have h1 : bitF2 ((g * g) i j) = decide (i = j) := by
    rw [h, Matrix.one_apply]
    split_ifs with hij <;> simp [bitF2, hij]
  rw [← h1, Matrix.mul_apply, Fin.sum_univ_five, bitF2_add, bitF2_add, bitF2_add, bitF2_add,
    bitF2_mul, bitF2_mul, bitF2_mul, bitF2_mul, bitF2_mul]
  rfl

theorem card_le_of_sq_eq_one {E : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hEU : E ≤ unitriangular 5 (ZMod 2)) (h2 : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 192 := by
  classical
  set L := (boolLists 10).filter fun l => sqOKB (utB l) with hL
  have hmem : ∀ x : E, code (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∈ L.toFinset := by
    intro x
    obtain ⟨hl, hd⟩ := mem_unitriangular.mp (hEU x.2)
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨mem_boolLists _, ?_⟩
    rw [utB_code hl hd]
    apply sqOKB_of_mul_self
    have hx := h2 x x.2
    rw [sq] at hx
    have := congrArg (fun y : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (y : Matrix (Fin 5) (Fin 5) (ZMod 2))) hx
    simpa using this
  let f : E → L.toFinset := fun x => ⟨code (x : Matrix (Fin 5) (Fin 5) (ZMod 2)), hmem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hc : code (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        code (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) := congrArg Subtype.val hxy
    obtain ⟨hxl, hxd⟩ := mem_unitriangular.mp (hEU x.2)
    obtain ⟨hyl, hyd⟩ := mem_unitriangular.mp (hEU y.2)
    have h1 := congrArg utB hc
    rw [utB_code hxl hxd, utB_code hyl hyd] at h1
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact bitF2_injective (congrFun (congrFun h1 i) j)
  calc Nat.card E ≤ Nat.card L.toFinset := Nat.card_le_card_of_injective f hf
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le L
    _ = 192 := card_sqOK

theorem eq_one_of_ne_zero_of_card_two' {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {a : K} (ha : a ≠ 0) : a = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hu : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have := Fintype.card_le_one_iff.mp hu.le (Units.mk0 a ha) 1
  exact congrArg Units.val this

theorem elemAbelianLt_sl52 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ElemAbelianLt (SpecialLinearGroup (Fin 5) F) (2 ^ 8) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) le_rfl (by rw [hF, pow_one])
  let σ : F ≃+* ZMod 2 := (ZMod.ringEquiv F hF').symm
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 5) (by norm_num)
  refine elemAbelianLt_of_le_sylow (isSylowTwoOf_top_of_sylow P₀) fun E hEP hE => ?_
  rw [hP₀] at hEP
  let ψ : SpecialLinearGroup (Fin 5) F →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    SpecialLinearGroup.map σ.toRingHom
  have hψ : Function.Injective ψ := by
    intro x y hxy
    ext i j
    have := congrArg (fun z : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (z : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j) hxy
    exact σ.injective (by simpa [ψ] using this)
  have hEU : E.map ψ ≤ unitriangular 5 (ZMod 2) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hl, hd⟩ := mem_unitriangular.mp (hEP hx)
    refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp [ψ, hl i j hij]
    · simp [ψ, hd i]
  have h2 : ∀ y ∈ E.map ψ, y ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hc := card_le_of_sq_eq_one hEU h2
  rw [Subgroup.card_map_of_injective hψ] at hc
  omega

theorem elemAbelianLt_psl52 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1) :
    ElemAbelianLt X (2 ^ 8) := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hX
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have hsc : scalars 5 F = ⊥ := by
    rw [eq_bot_iff]
    rintro A ⟨c, -, hA⟩
    have hc : (c : F) = 1 := eq_one_of_ne_zero_of_card_two' hF2 c.ne_zero
    rw [Subgroup.mem_bot]
    ext a b
    rw [hA, hc]
    simp
  have hinj : Function.Injective (proj 5 F) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, hsc]
  let ψ : SpecialLinearGroup (Fin 5) F ≃* projectiveSL 5 F :=
    MulEquiv.ofBijective (proj 5 F) ⟨hinj, proj_surjective 5 F⟩
  let φ : X ≃* SpecialLinearGroup (Fin 5) F :=
    (e₀.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 5 F).symm).trans ψ.symm
  exact ElemAbelianLt.of_mulEquiv φ (elemAbelianLt_sl52 hF2)

end CFSG.Quasithin.H13.KGRank
