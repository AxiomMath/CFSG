module

public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.EmptyFaithful.S153MAR
public import CFSG.Quasithin.EmptyFaithful.LRed4Alt
public import CFSG.Quasithin.Background.FLcPerf
public import CFSG.Quasithin.EmptyFaithful.S153D0Star
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec
open scoped commutatorElement IsMulCommutative

structure Env4 {G : Type} [Group G] [Finite G] (L S R Yp Y₁ Y₂ Vp : Subgroup G) : Prop where
  Vp_elem : IsElemAbelian 2 Vp
  L_N : L ≤ Subgroup.normalizer (Vp : Set G)
  S_N : S ≤ Subgroup.normalizer (Vp : Set G)
  R_L : R ≤ Subgroup.normalizer (L : Set G)
  S_L : S ≤ Subgroup.normalizer (L : Set G)
  R_two : IsPGroup 2 ↥R
  red : IsTwoReducedIn (L ⊔ R) Vp
  ff : @IsFFModule ↥Vp (commGroupOfElemAbelian Vp_elem) (autOn (L ⊔ R) Vp)
  quasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  sqtk : SQTKGroup ↥L
  nt : ¬ L ≤ Subgroup.centralizer (Vp : Set G)
  quot4 : IsLnTwoQuot L 4
  sylow : IsSylowTwoOf (S ⊓ L) L
  Y₁_Yp : Y₁ ≤ Yp
  Y₂_Yp : Y₂ ≤ Yp
  Yp_L : Yp ≤ L
  Yp_Y : Yp ≤ Y₁ ⊔ Y₂
  Y₁_S : ∀ s ∈ S, ∀ y ∈ Y₁, s * y * s⁻¹ ∈ Y₁
  Y₂_S : ∀ s ∈ S, ∀ y ∈ Y₂, s * y * s⁻¹ ∈ Y₂
  Y₁_card : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3
  Y₂_card : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3
  Yp_nine : 9 ∣ Nat.card ↥Yp
section Lambda

variable {G : Type} [Group G] [Finite G] {L S R Yp Y₁ Y₂ Vp : Subgroup G}

theorem Env4.LR_L (E : Env4 L S R Yp Y₁ Y₂ Vp) : L ⊔ R ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer E.R_L

theorem Env4.O2 (E : Env4 L S R Yp Y₁ Y₂ Vp) : pCoreOf 2 (autOn (L ⊔ R) Vp) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot E.red

theorem Env4.O2L (E : Env4 L S R Yp Y₁ Y₂ Vp) : pCoreOf 2 (autOn L Vp) = ⊥ :=
  pCoreOf_autOn_L_eq_bot1527d le_sup_left E.LR_L E.O2

theorem Env4.psl (E : Env4 L S R Yp Y₁ Y₂ Vp) : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := E.quot4
  exact LRed4.isPSL_two_of_statedSL' (by norm_num) e

theorem Env4.simple (E : Env4 L S R Yp Y₁ Y₂ Vp) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 E.psl).2

theorem Env4.kerP (E : Env4 L S R Yp Y₁ Y₂ Vp) : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (Vp : Set G)) :=
  isPGroup_ker_of_simple E.L_N E.simple E.O2L E.nt

theorem Env4.equiv (E : Env4 L S R Yp Y₁ Y₂ Vp) :
    Nonempty (↥(autOn L Vp) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) :=
  autOn_equiv_quotient1527d E.L_N E.O2L E.kerP

theorem Env4.equiv4 (E : Env4 L S R Yp Y₁ Y₂ Vp) :
    Nonempty (↥(autOn L Vp) ≃* ↥(StatedSL 4 (ZMod 2))) := by
  obtain ⟨e⟩ := E.equiv
  obtain ⟨e'⟩ := E.quot4
  exact ⟨e.trans e'⟩

theorem Env4.card_Λ (E : Env4 L S R Yp Y₁ Y₂ Vp) : Nat.card ↥(autOn L Vp) = 20160 := by
  obtain ⟨e⟩ := E.equiv4
  rw [Nat.card_congr e.toEquiv]
  exact card_statedSL_four_zmod1527d

theorem Env4.Λne (E : Env4 L S R Yp Y₁ Y₂ Vp) : autOn L Vp ≠ ⊥ := fun h =>
  E.nt (S153D.le_centralizer_of_autOn_eq_bot E.L_N h)

end Lambda
section B51

variable {G : Type} [Group G] [Finite G] {L S R Yp Y₁ Y₂ Vp : Subgroup G}

theorem Env4.qsΛ (E : Env4 L S R Yp Y₁ Y₂ Vp) : CFSG.IsQuasisimple ↥(autOn L Vp) :=
  isQuasisimple_autOn E.L_N E.quasi E.O2L E.nt

theorem Env4.sqtkΛ (E : Env4 L S R Yp Y₁ Y₂ Vp) : SQTKGroup ↥(autOn L Vp) :=
  sqtkGroup_autOn E.L_N E.sqtk E.kerP

theorem Env4.two_pow (E : Env4 L S R Yp Y₁ Y₂ Vp) :
    ∀ x ∈ autOn (L ⊔ R) Vp, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn L Vp :=
  autOn_two_of E.L_N fun y hy => by
    obtain ⟨e, he⟩ := InternalSec.two_of_sup E.R_two E.R_L y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩

theorem Env4.b51 (E : Env4 L S R Yp Y₁ Y₂ Vp) :
    @B51Hyp ↥Vp (commGroupOfElemAbelian E.Vp_elem) _
      (@ffJ ↥Vp (commGroupOfElemAbelian E.Vp_elem) (autOn (L ⊔ R) Vp)) (autOn L Vp) := by
  let _ : CommGroup ↥Vp := commGroupOfElemAbelian E.Vp_elem
  have hV2 : ∀ v : ↥Vp, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using E.Vp_elem.2 v v.2)
  exact (S153M.le_ffJ_of_ffModule hV2 (autOn_le_autOn_of_le le_sup_left) (autOn_normal_of E.LR_L)
    E.two_pow E.qsΛ E.sqtkΛ E.O2 E.ff).2

end B51
section Transport

variable {G : Type} [Group G] [Finite G]

theorem card_form_autOn {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G))) {a : ℕ} (h : Nat.card ↥A = 2 ^ a * 3) :
    ∃ b : ℕ, Nat.card ↥(autOn A V) = 2 ^ b * 3 := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 hC
  have h2 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
  rw [inf_of_le_left inf_le_left, h, hj, ← card_autOn_eq_relIndex hA] at h2
  have hdvd : 2 ^ j ∣ 2 ^ a * 3 := ⟨_, by rw [← h2]; ring⟩
  have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  have hja : j ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hdvd)
  refine ⟨a - j, Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) j : 0 < 2 ^ j) ?_⟩
  rw [h2, mul_assoc, mul_comm 3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hja]

theorem nine_dvd_autOn {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G))) (h : 9 ∣ Nat.card ↥A) :
    9 ∣ Nat.card ↥(autOn A V) := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 hC
  have h2 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
  rw [inf_of_le_left inf_le_left, hj, ← card_autOn_eq_relIndex hA] at h2
  rw [← h2] at h
  exact (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h

end Transport
section MSTransport

variable {G : Type} [Group G] [Finite G] {L S R Yp Y₁ Y₂ Vp : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_centralizer_aux {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc⟩

theorem Env4.ker_le (E : Env4 L S R Yp Y₁ Y₂ Vp) : L ⊓ Subgroup.centralizer (Vp : Set G) ≤ S ⊓ L := by
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (Vp : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      mem_normalizer_centralizer_aux (E.L_N hg)⟩
  exact (le_pCoreOf_of_le_normalizer inf_le_left hnorm E.kerP).trans
    (pCoreOf_le_of_isSylowTwoOf E.sylow)

end MSTransport

end CFSG.Quasithin.A38c10
