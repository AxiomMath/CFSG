module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

section Vocabulary

variable {G : Type*} [Group G]

@[expose] def yI (Y₁ : Subgroup G) (w : G) (i : ℕ) : Subgroup G :=
  Y₁.map (MulAut.conj (w ^ (i - 1))).toMonoidHom

@[expose] def cQuot (Y₀ : Subgroup G) : Subgroup G :=
  Subgroup.closure
    (sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀ (CFSG.Open.pCoreOf 2 Y₀))

theorem coe_cQuot (Y₀ : Subgroup G) :
    (cQuot Y₀ : Set G) =
      sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀ (CFSG.Open.pCoreOf 2 Y₀) := by
  set N := Subgroup.normalizer (Y₀ : Set G)
  set O := CFSG.Open.pCoreOf 2 Y₀
  have hNO : N ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  let K : Subgroup G :=
    { carrier := sectionCentralizer N Y₀ O
      mul_mem' := by
        rintro z₁ z₂ ⟨h₁N, h₁⟩ ⟨h₂N, h₂⟩
        refine ⟨N.mul_mem h₁N h₂N, fun y hy => ?_⟩
        have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
            z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹ * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNO h₁N) _).mp (h₂ y hy)) (h₁ y hy)
      one_mem' := ⟨N.one_mem, fun y _ => by simp⟩
      inv_mem' := by
        rintro z ⟨hzN, hz⟩
        refine ⟨N.inv_mem hzN, fun y hy => ?_⟩
        have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ Y₀ :=
          (Subgroup.mem_normalizer_iff.mp (N.inv_mem hzN) y).mp hy
        have h1 := O.inv_mem (hz _ hy')
        have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ =
            z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by group
        rwa [e] at h1 }
  have hK : cQuot Y₀ = K :=
    le_antisymm (Subgroup.closure_le K |>.mpr le_rfl) Subgroup.subset_closure
  rw [hK]
  rfl

@[expose] def omegaOneAt (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ x ^ p = 1}

@[expose] def omegaOneZ (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ X ∧ z ∈ Subgroup.centralizer (X : Set G) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haX, haC, hap⟩ ⟨hbX, hbC, hbp⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haX
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haX, haC, hap⟩
    exact ⟨X.inv_mem haX, Subgroup.inv_mem _ haC, by rw [inv_pow, hap, inv_one]⟩

end Vocabulary

section Quot

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def imgY0 (A Y₀ : Subgroup G) [(kerAO2 A Y₀).Normal] (X : Subgroup G) :
    Subgroup (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀) :=
  (X.subgroupOf (A ⊔ Y₀)).map (QuotientGroup.mk' (kerAO2 A Y₀))

@[expose] noncomputable def alphaY0 (A Y₀ : Subgroup G) [(kerAO2 A Y₀).Normal] (a : G)
    (ha : a ∈ A) : ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
  QuotientGroup.mk' (kerAO2 A Y₀) ⟨a, Subgroup.mem_sup_left ha⟩

@[expose] noncomputable def oTwoCY0 (A Y₀ : Subgroup G) [(kerAO2 A Y₀).Normal]
    (x : ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀) : Subgroup (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀) :=
  CFSG.Open.pCoreOf 2 (imgY0 A Y₀ Y₀ ⊓ Subgroup.centralizer {x})

theorem Sec17Std.le_normalizer_y0 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : A ≤ Subgroup.normalizer (Y₀ : Set G) :=
  h.mem_y0Star.prop.1.1.2

end Quot

structure Sec17Y1 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L Y₀ Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G) : Prop extends Sec17Std G A c L Y₀ where
  mem_y1Star : Y₁ ∈ scriptY1Star A (lB A)
  not_le_M : ¬ Y₁ ≤ Subgroup.normalizer (Y₀ : Set G)
  mem_qStar_two : S ∈ scriptQPiStar A (lB A) Y₁ (piOf 2)
  inf_L_mem_qStar_two : S ⊓ L ∈ scriptQPiStar A (lB A) L (piOf 2)
  y1_isSolvable : Group.IsSolvable ↥Y₁
  p_prime : p.Prime
  three_lt_p : 3 < p
  mem_qStar_p : P ∈ scriptQPiStar A (lB A) Y₁ (piOf p)
  commutator_not_le_M : ¬ ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (Y₀ : Set G)

structure Sec17W (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L Y₀ Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G) (w : G) (Q : Subgroup G) : Prop
    extends Sec17Y1 G A c L Y₀ Y₁ S p P where
  w_mem : w ∈ Subgroup.normalizer (A : Set G) ⊓ L
  w_not_mem : w ∉ A
  orderOf_w : orderOf w = 3
  le_Q : P ≤ Q
  mem_qStar_G : Q ∈ scriptQPiStar A (lB A) ⊤ (piOf p)

structure Sec17WQ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L Y₀ Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G) (w : G) (Q : Subgroup G) : Prop
    extends Sec17W G A c L Y₀ Y₁ S p P w Q where
  w_normalizes_Q : w ∈ Subgroup.normalizer (Q : Set G)

structure Sec17S (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L Y₀ Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G) (w : G) (Q : Subgroup G) (s : G) : Prop
    extends Sec17WQ G A c L Y₀ Y₁ S p P w Q where
  s_mem_W : s ∈ Subgroup.normalizer (A : Set G)
  s_inverts_c : s * c * s⁻¹ = c⁻¹
  s_normalizes_Aw : s ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G)
  s_normalizes_Q : s ∈ Subgroup.normalizer (Q : Set G)
  s_normalizes_y1 : s ∈ Subgroup.normalizer (Y₁ : Set G)

structure Sec17Data (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L Y₀ Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G) (w : G) (Q : Subgroup G) (s d r : G) : Prop
    extends Sec17S G A c L Y₀ Y₁ S p P w Q s where
  d_mem : d ∈ A ⊓ L
  d_ne_one : d ≠ 1
  d_threeCentral : IsThreeCentralIn L d
  r_normalizes_Q : r ∈ Subgroup.normalizer (Q : Set G)
  r_origin : ∃ x ∈ xA A, x * r ∈ L ⊓ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) :
    Set G) ∧ (x * r) * d * (x * r)⁻¹ = d⁻¹

@[expose] def Para1714 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      ∃ (Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P

@[expose] def Para1722 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ∃ (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q

@[expose] def Para1724 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      Sec4.autIn (Subgroup.normalizer (Q : Set G)) A = wStar A ∧
        ∃ w' : G, Sec17WQ G A c L Y₀ Y₁ S p P w' Q

@[expose] def Para1725 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17WQ G A c L Y₀ Y₁ S p P w Q →
      ∃ (Y₁' S' P' : Subgroup G) (s : G), Sec17S G A c L Y₀ Y₁' S' p P' w Q s

@[expose] def Para1726 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G) (s : G), Sec17S G A c L Y₀ Y₁ S p P w Q s →
      ∃ d r : G, Sec17Data G A c L Y₀ Y₁ S p P w Q s d r

end CFSG.RankThree.PartTwo.Sec17
