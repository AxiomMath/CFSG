module

public import CFSG.Quasithin.Vol2.Ch11SecBK4W
public import CFSG.Quasithin.H13.NQCatParabolicSL3
public import CFSG.Quasithin.Vol2.Ch11SecBK4S
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usl)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (upperTriangular unitriangular)
open scoped IsMulCommutative MatrixGroups Pointwise

namespace BK4

variable {K : Type} [Field K]

variable (K) in
@[expose] def flag3 (i : ℕ) : Submodule K (Fin 3 → K) where
  carrier := {x | ∀ j : Fin 3, i ≤ j.val → x j = 0}
  add_mem' := fun {a b} ha hb j hj => by
    show a j + b j = 0
    rw [ha j hj, hb j hj, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c x hx j hj => by
    show c • x j = 0
    rw [hx j hj, smul_zero]

theorem mem_flag3 {i : ℕ} {x : Fin 3 → K} :
    x ∈ flag3 K i ↔ ∀ j : Fin 3, i ≤ j.val → x j = 0 :=
  Iff.rfl

theorem flag3_zero : flag3 K 0 = ⊥ :=
  eq_bot_iff.mpr fun _ hx => (Submodule.mem_bot K).mpr (funext fun j => hx j (Nat.zero_le _))

theorem flag3_top {i : ℕ} (hi : 3 ≤ i) : flag3 K i = ⊤ :=
  eq_top_iff.mpr fun _ _ j hj => absurd (lt_of_lt_of_le j.2 hi) (not_lt.mpr hj)

theorem flag3_one : flag3 K 1 = KGNat.stdLine K := by
  ext x
  rw [mem_flag3, KGNat.mem_stdLine]
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact h1
    · exact h2

theorem flag3_two : flag3 K 2 = KGNat.stdPlane K := by
  ext x
  rw [mem_flag3, KGNat.mem_stdPlane]
  constructor
  · intro h
    exact h 2 (by decide)
  · intro h2 j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h2

theorem hstep_flag3 : ∀ i < 3, ∃ e ∈ flag3 K (i + 1), e ∉ flag3 K i ∧
    ∀ y ∈ flag3 K (i + 1), ∃ c : K, y - c • e ∈ flag3 K i := by
  intro i hi
  set k : Fin 3 := ⟨i, hi⟩ with hk
  refine ⟨Pi.single k 1, fun j hj => ?_, fun h => ?_, fun y hy => ⟨y k, fun j hj => ?_⟩⟩
  · have hjk : j ≠ k := fun h => by
      have : j.val = i := by rw [h]
      omega
    simp [hjk]
  · have := h k (le_refl _)
    simp at this
  · by_cases hjk : j = k
    · subst hjk
      simp
    · have hj' : i + 1 ≤ j.val := by
        have : j.val ≠ i := fun h => hjk (Fin.ext h)
        omega
      simp [hjk, hy j hj']

theorem mulVec_mem_flag3 {b : SL(3, K)} (hb : b ∈ upperTriangular 3 K) {i : ℕ}
    {x : Fin 3 → K} (hx : x ∈ flag3 K i) : (b : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ flag3 K i := by
  intro j hj
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k j with h | h
  · rw [hb j k h, zero_mul]
  · rw [hx k (le_trans hj (show j.val ≤ k.val from h)), mul_zero]

omit [Field K] in
theorem exists_finset_card_four [Finite K] (h4 : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact ⟨s, hs⟩

theorem mapsTo_sl3 [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : SL(3, K)} (hg : ∀ x : MulAut W, x ∈ P ↔
      ∃ u ∈ Usl K, x = ((KGNat.rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {A : Subgroup (MulAut W)} (hAH : A ≤ H) (hPA : P ≤ A) (hA : Group.IsSolvable A)
    {a : MulAut W} (ha : a ∈ A) (i : ℕ) (w : W) (hw : f w ∈ KGNat.gmap g (flag3 K i)) :
    f (a w) ∈ KGNat.gmap g (flag3 K i) := by
  let φ : SL(3, K) →* MulAut W :=
    H.subtype.comp ((KGNat.rho3 π).comp (MulAut.conj g).toMonoidHom)
  have hφ : ∀ b, φ b = ((KGNat.rho3 π (g * b * g⁻¹) : ↥H) : MulAut W) := fun b => rfl
  have hφinj : Function.Injective φ := H.subtype_injective.comp
    ((KGNat.rho3_bijective hf).1.comp (MulAut.conj g).injective)
  have hU : unitriangular 3 K ≤ A.comap φ := by
    rw [← SecS.C11P9A.usl_eq_unitriangular]
    intro u hu
    rw [Subgroup.mem_comap, hφ]
    exact hPA ((hg _).mpr ⟨u, hu, rfl⟩)
  have hB : Group.IsSolvable ↥(A.comap φ) := by
    have := hA
    refine Group.isSolvable_of_isSolvable_injective (f := φ.subgroupComap A) fun x y h => ?_
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (hφinj h1)
  have hBU := H13.NQCat.SL3.le_upperTriangular_of_isSolvable hK4 hU hB
  obtain ⟨b', hb'⟩ := (KGNat.rho3_bijective hf).2 ⟨a, hAH ha⟩
  have hb : g⁻¹ * b' * g ∈ A.comap φ := by
    rw [Subgroup.mem_comap, hφ, show g * (g⁻¹ * b' * g) * g⁻¹ = b' by group, hb']
    exact ha
  have e1 : a w = ((KGNat.rho3 π b' : ↥H) : MulAut W) w := by rw [hb']
  rw [e1, hf.act3, KGNat.mem_gmap, show b' = g * (g⁻¹ * b' * g) * g⁻¹ by group,
    KGNat.conj_mulVec]
  exact mulVec_mem_flag3 (hBU hb) (KGNat.mem_gmap.mp hw)

variable {G : Type} [Group G] {L V T D : Subgroup G}

theorem cartanPower_sl3 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L V)} {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDL : D ≤ L) (hD : IsElemAbelian p D) (hDT : (D : Set G) * T = T * D) {t : G}
    (ht : t ∈ T) (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := KGNat.exists_sylow_eq_conj_Usl hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL')
  have hK4 := exists_finset_card_four (four_le_of_card hK hn)
  have hΨΦ : ∀ x, Matrix.toLin' ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
      (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K) x) = x := fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec]
  have hΦΨ : ∀ x, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)
      (Matrix.toLin' ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) x) = x := fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec]
  refine cartanPower_of_flag hf hLV (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT)
    (x₀ := ![1, 0, 0]) (fun h => one_ne_zero (congrFun h 0))
    (fun x hxV hxL hx => mem_centralizer_of_sl3 hLV hVL hf hxV hxL hx) hTS.2.1 hTV hTL
    (m := 3) (fun i => KGNat.gmap g (flag3 K i)) ?_ ?_ (hstep_map _ _ hΨΦ hΦΨ hstep_flag3) ?_
    ?_ ?_ hDL hp hp2 hD hDT ht htD
  · show KGNat.gmap g (flag3 K 0) = ⊥
    rw [flag3_zero, KGNat.gmap, Submodule.map_bot]
  · intro i hi
    show KGNat.gmap g (flag3 K i) = ⊤
    rw [flag3_top hi]
    exact eq_top_iff.mpr fun x _ => KGNat.mem_gmap.mpr Submodule.mem_top
  · intro i hi0 hi3
    show SecA.IsFlagW _ _ _ _ i (hf.pre (KGNat.gmap g (flag3 K i)).toAddSubgroup)
    interval_cases i
    · rw [flag3_one]
      exact KGNat.isFlagW_pre hW hf hg (fun a b c x hx => KGNat.uMat_mem_stdLine a b c hx)
        (by rw [KGNat.card_stdLine, pow_one])
    · rw [flag3_two]
      exact KGNat.isFlagW_pre hW hf hg (fun a b c x hx => KGNat.uMat_mem_stdPlane a b c hx)
        KGNat.card_stdPlane
  · intro i hi0 hi3 U hU
    show U = hf.pre (KGNat.gmap g (flag3 K i)).toAddSubgroup
    obtain ⟨S, hS, hcard, rfl⟩ := KGNat.exists_eq_pre_of_isFlagW hW hf hg hU
    interval_cases i
    · rw [(KGNat.eq_std_of_stable hS).1 (by rw [hcard, pow_one]), flag3_one]
    · rw [(KGNat.eq_std_of_stable hS).2.1 hcard, flag3_two]
  · intro A hAH hPA hA a ha i w hw
    exact mapsTo_sl3 hK4 hf hg hAH hPA hA ha i w hw

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
