module

public import CFSG.RankThree.PartTwo.Sec15.Item1512
public import CFSG.RankThree.PartTwo.Sec15.Item153

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Concl1514 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L Y : Subgroup G) : Prop :=
  (Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L ∧
      omegaA A = {Subgroup.zpowers c} ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) ∨
    (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
      WStarS4 A ∧ TransOmegaThree A c ∧
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)))) ∨
    ((∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Assembly.RankThreeEven.projSU 3 5 1)) ∧
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∧
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ omegaA A = {Subgroup.zpowers c} ∧
      (∀ Y₀ ∈ scriptY0Star A LB, ¬ L ≤ Y₀) ∧ IsSimpleGroup ↥L ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer (L : Set G))))

omit [Finite G] in
theorem item1514_iff {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G} {L : Subgroup G} :
    Item1514 A LB c L ↔ ∀ Y ∈ scriptY0Star A LB, MeetsY4 A LB L Y → Concl1514 A LB c L Y :=
  Iff.rfl

@[expose] noncomputable def Concl1515 (A : Subgroup G) (c : G) (L Y : Subgroup G) : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e ∧
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
    Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y ∧
    (∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧ IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∧
    omegaA A = {Subgroup.zpowers c}

@[expose] def Step1515 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y ∈ scriptY0Star A LB, MeetsY4 A LB L Y → ¬ Concl1514 A LB c L Y → Concl1515 A c L Y

structure Ctx1514 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L Y : Subgroup G) :
    Prop where
  mem_y0Star : Y ∈ scriptY0Star A LB
  meets : MeetsY4 A LB L Y
  not_concl : ¬ Concl1514 A LB c L Y
  concl1515 : Concl1515 A c L Y

@[expose] def Step1516 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y →
    ∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer (Y : Set G)) (piOf 2),
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
        scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)

@[expose] def Step1517 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y →
    (∀ Y' ∈ scriptY2 A, ¬ L ≤ Y') ∧ IsSimpleGroup ↥L ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer (L : Set G)))

@[expose] def Step1518 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p = 2

@[expose] def sign1519 (m r : ℕ) : ZMod r :=
  if 2 ^ m % 3 = 1 then 1 else -1

@[expose] def IsChoice1519 (m r : ℕ) : Prop :=
  r.Prime ∧ (2 : ZMod r) ^ m = sign1519 m r ∧
    ((∃ k : ℕ, m = 2 * k ∧ m % 4 = 2 ∧ (2 : ZMod r) ^ k = 1 ∧
        ∀ i : ℕ, i ∣ k → i < k → (2 : ZMod r) ^ i ≠ 1) ∨
      (m % 4 ≠ 2 ∧ ∀ i : ℕ, i ∣ m → i < m → (2 : ZMod r) ^ i ≠ sign1519 m r))

@[expose] def Data1519 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (L : Subgroup G) (p : ℕ)
    (P : Subgroup G) : Prop :=
  p.Prime ∧ 3 < p ∧
    (∃ m : ℕ, 1 ≤ m ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m ∧
      IsChoice1519 m p) ∧
    CFSG.Assembly.IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
    P ∈ scriptQPi A LB L (piOf p) ∧
    ∀ Y₀ ∈ scriptY0 A LB, ∀ R ∈ scriptQPi A LB (Subgroup.normalizer (Y₀ : Set G)) (piOf p),
      (R : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀)

@[expose] def Step1519 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y → ∃ (p : ℕ) (P : Subgroup G), Data1519 A LB L p P

@[expose] noncomputable def Step1520 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ Y, Ctx1514 A LB c L Y → ∀ (p : ℕ) (P : Subgroup G), Data1519 A LB L p P →
    ∀ X ∈ scriptY2 A, P ≤ X →
      P ≤ inSubgroup CFSG.solvableRadical (pPrimeCoreOf 3 (delta A LB X))

@[expose] def Step1521 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y → ∀ (p : ℕ) (P : Subgroup G), Data1519 A LB L p P →
    ∀ X ∈ scriptY2 A, ¬ P ≤ X

@[expose] def Step1522 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  ∀ Y, Ctx1514 A LB c L Y → ∀ (p : ℕ) (P : Subgroup G), Data1519 A LB L p P →
    ∃ X ∈ scriptY2 A, P ≤ X

omit [Finite G] in
theorem rank3II_15_14_of_steps {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L : Subgroup G} (h1515 : Step1515 A LB c L) (h1519 : Step1519 A LB c L)
    (h1521 : Step1521 A LB c L) (h1522 : Step1522 A LB c L) : Item1514 A LB c L := by
  intro Y hY hYL
  by_contra hce
  have hctx : Ctx1514 A LB c L Y := ⟨hY, hYL, hce, h1515 Y hY hYL hce⟩
  obtain ⟨p, P, hP⟩ := h1519 Y hctx
  obtain ⟨X, hX, hPX⟩ := h1522 Y hctx p P hP
  exact h1521 Y hctx p P hP X hX hPX

theorem normalizer_le_of_omegaA_eq {A : Subgroup G} {c : G}
    (h : omegaA A = {Subgroup.zpowers c}) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro w hw
  have hc : Subgroup.zpowers c ∈ omegaA A := h ▸ Set.mem_singleton _
  have hcw : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
    (map_conj_mem_omegaA_iff hw).mpr hc
  rw [h, Set.mem_singleton_iff] at hcw
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcw

theorem rank3II_15_16_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A)) (h149 : Item149 A (lB A))
    (h1411 : Item1411_1 A (lB A)) (hloc : Claim1411Local A (lB A)) :
    Step1516 A (lB A) c L := by
  intro Y hctx S hS
  obtain ⟨-, -, -, -, -, -, -, -, hΩ⟩ := hctx.concl1515
  have hWH := normalizer_le_of_omegaA_eq hΩ
  have hY0 : Y ∈ scriptY0 A (lB A) := hctx.mem_y0Star.prop
  have hYY : Y ∈ scriptY A := hY0.1.1
  have hNY : Subgroup.normalizer (Y : Set G) ∈ scriptY A :=
    normalizer_mem_scriptY h.isSimpleGroup hYY (ne_bot_of_mem_scriptY0 hY0)
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hNX : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hNY
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G))
      (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S', -, hS'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  have hS'G : S' ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := ((h153 Y hctx.mem_y0Star).2.1 S' hS').1
  have hS'Y : S' ≤ Subgroup.normalizer (Y : Set G) := hobs Y hctx.mem_y0Star S' hS'
  have hS'NY : S' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) := by
    refine ⟨⟨⟨hS'.prop.1.1, hS'Y⟩, hS'.prop.2⟩, fun T hT hle => ?_⟩
    exact hS'.2 ⟨⟨hT.1.1, hT.1.2.trans hNX⟩, hT.2⟩ hle
  obtain ⟨w, hw, rfl⟩ := hloc.1 _ hNY S' hS'NY S hS
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hSG : S'.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
    Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G))
      (fun Q hQ v hv => map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hv hQ) hS'G hwA
  exact inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hWH h1411 hSG

theorem claim153Obs_of_normal {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) (hn : Claim153Normal A (lB A)) :
    Claim153Obs A (lB A) := by
  intro Y hY S hS
  rw [← normalizer_x_eq_of_normal h h149 hn hY]
  exact hS.prop.1.2

end CFSG.RankThree.PartTwo.Sec15
