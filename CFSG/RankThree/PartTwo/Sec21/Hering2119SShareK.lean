module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SStep2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

theorem item2119EndShareTWeak_holds :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
      (U₀ : Subgroup G) (a : G) (X : Subgroup G),
      Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
        ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
          Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
          ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
            (∀ e ∈ A, e ∉ Subgroup.zpowers d →
              CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
            IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
            (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
            (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
              CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
              Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
            ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
              CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
              ∃ t : G, t ∈ y2128Of (Lf e) (F e) (q2127Of A d F) ∧
                t ∈ Subgroup.centralizer ({e} : Set G) ∧ (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧
                ∀ x ∈ CFSG.Open.thompsonSubgroup P, t * x * t⁻¹ = x⁻¹ := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e he hed P hP
  have hL' := hL e he hed P hP
  have hAbs := Hering2119S.lineAbs_of_config hE hLf h26 hF h27 hQ hQX h28 he hed hL'
  obtain ⟨hDe, hD81, -, -⟩ := hL'
  have hDc : ∀ x ∈ CFSG.Open.thompsonSubgroup P, ∀ y ∈ CFSG.Open.thompsonSubgroup P,
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD : Hering2119S.IsElem3 (CFSG.Open.thompsonSubgroup P) := ⟨hDc, fun x hx => hDe.2 x hx⟩
  haveI : Fact (Hering2119S.IsElem3 (CFSG.Open.thompsonSubgroup P)) := ⟨hD⟩
  obtain ⟨S, aN, bN, hS2, hSY, hSe, haS, hbS, hQ0, -⟩ := Hering2119S.quat_of_line _ hD81 hAbs
  have hsq := Hering2119S.sq_on_D (CFSG.Open.thompsonSubgroup P) aN hQ0.II
  obtain ⟨k, hk⟩ := hS2 ⟨(aN : G), haS⟩
  refine ⟨(aN : G) * (aN : G), (Subgroup.mul_mem _ (hSY haS) (hSY haS)), ?_, ⟨k, ?_⟩, ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.mp (hSe haS)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (aN : G) * (aN : G) * e = (aN : G) * ((aN : G) * e) := by rw [mul_assoc]
        _ = (aN : G) * (e * (aN : G)) := by rw [h]
        _ = ((aN : G) * e) * (aN : G) := by rw [mul_assoc]
        _ = (e * (aN : G)) * (aN : G) := by rw [h]
        _ = e * ((aN : G) * (aN : G)) := by rw [mul_assoc])
  · have h1 : (aN : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [(Commute.refl (aN : G)).mul_pow, h1, one_mul]
  · intro x hx
    have := hsq x hx
    rw [← this]
    group

end CFSG.RankThree.PartTwo.Sec21

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

abbrev V4 := Fin 4 → F3

abbrev M4 := Matrix (Fin 4) (Fin 4) F3

@[expose] def omega4 (x y : V4) : F3 := x 0 * y 2 - x 2 * y 0 + x 1 * y 3 - x 3 * y 1

@[expose] def inA (v : V4) : Prop := v 2 = 0 ∧ v 3 = 0

instance (v : V4) : Decidable (inA v) := by unfold inA; infer_instance

@[expose] def lineVec : Fin 4 → V4 :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0]]

@[expose] def InF (a : V4) (X : M4) (v : V4) : Prop :=
  ∃ c : F3, ∃ h : V4, X.mulVec h = h ∧ omega4 a h = 0 ∧ v = c • a + h

instance (a : V4) (X : M4) (v : V4) : Decidable (InF a X v) := by unfold InF; infer_instance

@[expose] def InH (a : V4) (X : M4) (v : V4) : Prop := X.mulVec v = v ∧ omega4 a v = 0

instance (a : V4) (X : M4) (v : V4) : Decidable (InH a X v) := by unfold InH; infer_instance

structure IsItem (a : V4) (X T : M4) : Prop where
  symp : ∀ x y, omega4 (X.mulVec x) (X.mulVec y) = omega4 x y
  ne_one : X ≠ 1
  cube : X * X * X = 1
  noFix : ∀ v, inA v → v ≠ 0 → X.mulVec v ≠ v
  presF : ∀ v, InF a X v → InF a X (X.mulVec v)
  sq : T * T = 1
  mult : ∀ x y, omega4 (T.mulVec x) (T.mulVec y) = -omega4 x y
  fixa : T.mulVec a = a
  neg : ∀ v, X.mulVec v = v → T.mulVec v = -v

@[expose] def BadVec (a : V4) (X : M4) (v : V4) : Prop :=
  (inA v ∧ v ≠ 0) ∨ (InF a X v ∧ ¬ InH a X v)

instance (a : V4) (X : M4) (v : V4) : Decidable (BadVec a X v) := by unfold BadVec; infer_instance

def Compat (X T : Fin 4 → M4) : Prop :=
  ∀ g ∈ Submonoid.closure (Set.range X ∪ Set.range T), g ≠ 1 → g * g * g = 1 →
    ∀ i v, BadVec (lineVec i) (X i) v → g.mulVec v ≠ v

@[expose] def SameCyc (A B : M4) : Prop := B = A ∨ B = A * A

def ConclK (X : Fin 4 → M4) : Prop :=
  (∀ i j v, X i *ᵥ v = v ↔ X j *ᵥ v = v) ∧ ∃ σ : Equiv.Perm (Fin 4),
    SameCyc (X (σ 0)) (X (σ 1)) ∧ SameCyc (X (σ 2)) (X (σ 3)) ∧ ¬ SameCyc (X (σ 0)) (X (σ 2))

@[expose] def Item2119EndShareK : Prop :=
  ∀ X T : Fin 4 → M4, (∀ i, IsItem (lineVec i) (X i) (T i)) → Compat X T → ConclK X

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
