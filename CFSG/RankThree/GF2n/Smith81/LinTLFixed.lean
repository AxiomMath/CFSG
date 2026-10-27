module

public import CFSG.RankThree.GF2n.Smith81.LinTLCentralizer
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem isPGroup_LB_two (hc : Ctx M Q Z B) : IsPGroup 2 (LB M Q B) := by
  intro l
  have h2 : (l : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB l.2
  obtain ⟨k, hk⟩ := CFSG.RankThree.GF2n.Smith81.isPGroup_Q' hc.hyp ⟨_, h2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_succ', pow_mul]
  exact this

theorem Ctx.inf_QB_inf_eq_of_fixed (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V)
    (hVn : LB M Q B ≤ Subgroup.normalizer (V : Set G)) (hBV : (B ⊔ Z) ⊓ V = Z)
    (h3 : ∀ y ∈ Q ⊓ QB B, (∀ l ∈ LB M Q B, ⁅y, l⁆ ∈ Z) → y ∈ B ⊔ Z) :
    Q ⊓ QB B ⊓ V = Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = Q ⊓ QB B ⊓ V := ⟨_, rfl⟩
  rw [← hS]
  have hmemS : ∀ g : G, g ∈ S ↔ g ∈ Q ∧ g ∈ QB B ∧ g ∈ V := by
    intro g
    simp only [hS, Subgroup.mem_inf, and_assoc]
  have hSQ : S ≤ Q := fun g hg => ((hmemS g).mp hg).1
  have hSD : S ≤ QB B := fun g hg => ((hmemS g).mp hg).2.1
  have hSV : S ≤ V := fun g hg => ((hmemS g).mp hg).2.2
  have hZS : Z ≤ S := fun z hz => (hmemS z).mpr ⟨hc.Z_le_Q hz, hc.Z_le_QB.1 hz, hZV hz⟩
  refine le_antisymm ?_ hZS
  by_contra hSZ
  have hconjQ : ∀ x ∈ Q, ∀ h ∈ S, x * h * x⁻¹ ∈ S := by
    intro x hx h hh
    obtain ⟨hhQ, hhD, hhV⟩ := (hmemS h).mp hh
    have hxL : x ∈ LB M Q B := Subgroup.mem_sup_left hx
    refine (hmemS _).mpr ⟨Q.mul_mem (Q.mul_mem hx hhQ) (Q.inv_mem hx), ?_, ?_⟩
    · have hcomm : ⁅x, h⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx hhQ
      have e : x * h * x⁻¹ = ⁅x, h⁆ * h := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (QB B).mul_mem (hc.Z_le_QB.1 hcomm) hhD
    · exact (Subgroup.mem_normalizer_iff.mp (hVn hxL) h).mp hhV
  have hconjM : ∀ s ∈ QB B ⊓ M, ∀ h ∈ S, s * h * s⁻¹ ∈ S := by
    intro s hs h hh
    obtain ⟨hhQ, hhD, hhV⟩ := (hmemS h).mp hh
    have hsD : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
    have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
    have hsL : s ∈ LB M Q B := Subgroup.mem_sup_right hs
    refine (hmemS _).mpr ⟨?_, (QB B).mul_mem ((QB B).mul_mem hsD hhD) ((QB B).inv_mem hsD), ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) h).mp hhQ
    · exact (Subgroup.mem_normalizer_iff.mp (hVn hsL) h).mp hhV
  have hnQ : Q ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjQ x hx h hh, fun hh => ?_⟩
    have h' := hconjQ x⁻¹ (Q.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at h'
  have hnM : QB B ⊓ M ≤ Subgroup.normalizer (S : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjM s hs h hh, fun hh => ?_⟩
    have h' := hconjM s⁻¹ ((QB B ⊓ M).inv_mem hs) _ hh
    have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
    rwa [e] at h'
  have hnL : LB M Q B ≤ Subgroup.normalizer (S : Set G) := by
    unfold LB
    exact sup_le hnQ hnM
  have hL2 : IsPGroup 2 (LB M Q B) := isPGroup_LB_two hc
  have hS2 : IsPGroup 2 S := (CFSG.RankThree.GF2n.Smith81.isPGroup_Q' hc.hyp).to_le hSQ
  let f : ↥(LB M Q B) → ↥S → ↥S := fun l x =>
    ⟨(l : G) * x * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hnL l.2) x).mp x.2⟩
  have hf : ∀ (l : ↥(LB M Q B)) (a b : ↥S), a⁻¹ * b ∈ Z.subgroupOf S →
      (f l a)⁻¹ * f l b ∈ Z.subgroupOf S := by
    intro l a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    have hab' : (a : G)⁻¹ * (b : G) ∈ Z := by simpa using hab
    have e : (((f l a)⁻¹ * f l b : ↥S) : G) = (l : G) * ((a : G)⁻¹ * (b : G)) * (l : G)⁻¹ := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, hc.LB_centralizes_Z l.2 _ hab']
    exact hab'
  letI act : MulAction ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S) :=
    { smul := fun l => Quotient.map' (f l) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        exact hf l a b hab)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp [f]))
      mul_smul := fun l₁ l₂ q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)) }
  have hsmul : ∀ (l : ↥(LB M Q B)) (x : ↥S),
      (l • (x : ↥S ⧸ Z.subgroupOf S)) = ((f l x : ↥S) : ↥S ⧸ Z.subgroupOf S) :=
    fun l x => rfl
  have hidx : 2 ∣ Nat.card (↥S ⧸ Z.subgroupOf S) := by
    rw [← Subgroup.index]
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hdvd : (Z.subgroupOf S).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · exfalso
      rw [pow_zero, Subgroup.index_eq_one] at hj
      apply hSZ
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥S) ∈ Z.subgroupOf S := by
        rw [hj]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    · rw [hj, pow_succ]
      exact dvd_mul_left _ _
  have hmod := hL2.card_modEq_card_fixedPoints (↥S ⧸ Z.subgroupOf S)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hidx))
  have h1fix : ((1 : ↥S) : ↥S ⧸ Z.subgroupOf S) ∈
      MulAction.fixedPoints ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S) := by
    intro l
    rw [hsmul]
    exact congrArg _ (Subtype.ext (by simp [f]))
  obtain ⟨q, hqfix, hq1⟩ : ∃ q ∈ MulAction.fixedPoints ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S),
      q ≠ ((1 : ↥S) : ↥S ⧸ Z.subgroupOf S) := by
    by_contra hcon
    push Not at hcon
    have hsub : (MulAction.fixedPoints ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S)).Subsingleton :=
      fun a ha b hb => (hcon a ha).trans (hcon b hb).symm
    have hcard : Nat.card (MulAction.fixedPoints ↥(LB M Q B) (↥S ⧸ Z.subgroupOf S)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨hsub.coe_sort, ⟨⟨_, h1fix⟩⟩⟩
    omega
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyZ : (y : G) ∉ Z := fun h => hq1 (by
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using h)
  have hyQ : (y : G) ∈ Q := hSQ y.2
  have hcomm : ∀ l ∈ LB M Q B, ⁅(y : G), l⁆ ∈ Z := by
    intro l hl
    have h := hqfix ⟨l, hl⟩
    rw [hsmul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have hw : (((f ⟨l, hl⟩ y)⁻¹ * y : ↥S) : G) = (l * (y : G) * l⁻¹)⁻¹ * (y : G) := rfl
    rw [hw] at h
    have e : ⁅(y : G), l⁆ = (y : G) * ((l * (y : G) * l⁻¹)⁻¹ * (y : G)) * (y : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hc.conj_Z_of_mem_Q hyQ h]
    exact h
  have hyB : (y : G) ∈ B ⊔ Z :=
    h3 (y : G) (Subgroup.mem_inf.mpr ⟨hyQ, hSD y.2⟩) hcomm
  have hyBZ : (y : G) ∈ (B ⊔ Z) ⊓ V := Subgroup.mem_inf.mpr ⟨hyB, hSV y.2⟩
  rw [hBV] at hyBZ
  exact hyZ hyBZ

theorem Ctx.inf_QB_inf_eq_of_sup_inf (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V)
    (hVn : LB M Q B ≤ Subgroup.normalizer (V : Set G)) (hBV : (B ⊔ Z) ⊓ V = Z) :
    Q ⊓ QB B ⊓ V = Z :=
  hc.inf_QB_inf_eq_of_fixed hZV hVn hBV fun _ hy hyc => hc.mem_sup_of_comm_LB_mem_Z' hy hyc

end CFSG.RankThree.GF2n.Stroth80
