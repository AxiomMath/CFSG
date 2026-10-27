module

public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountTools

public section

namespace CFSG.Quasithin.H13.Case4Count

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open CFSG.Quasithin.H13.L3321 (RData SL4)
open CFSG.Quasithin.CubicCount CFSG.Quasithin.SevenL4Model
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Data (G : Type) [Group G] [Finite G] (T L R : Subgroup G) (α : ↥L →* SL4) : Prop where
  TL : T ≤ Subgroup.normalizer (L : Set G)
  T2 : IsPGroup 2 ↥T
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  RT : R ≤ T
  QR : qL L T ≤ R
  mul : ∀ r ∈ R, ∃ l ∈ L, ∃ c ∈ qL L T, r = l * c
  RQ1 : ∀ l : ↥L, (l : G) ∈ R → α l ∈ FLc.QI 4 {1}
  RQ3 : ∀ l : ↥L, (l : G) ∈ R → α l ∈ FLc.QI 4 {3}
  RY1 : R ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 {1}) : Set G)
  RY3 : R ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 {3}) : Set G)

namespace Data

variable {T L R : Subgroup G} {α : ↥L →* SL4}

theorem exists_levi_one (hR : Data G T L R α) :
    ∃ ψ : ↥(liftCore α (FLc.QI 4 {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1})) ∧
      ∀ y : ↥(liftCore α (FLc.QI 4 {1})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 1 3 (by norm_num)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hk2 : IsPGroup 2 ↥α.ker := by
    rw [hR.ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨ψ, hψs, hψk, hψe⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hR.surj hk2
    (I := {1}) (a := 1) (m := 3) (by norm_num) le_rfl (Or.inr rfl) (Or.inl rfl) hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk, hψe⟩

theorem exists_levi_three (hR : Data G T L R α) :
    ∃ ψ : ↥(liftCore α (FLc.QI 4 {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧ ∀ y : ↥(liftCore α (FLc.QI 4 {3})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 0 3 (by norm_num)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hk2 : IsPGroup 2 ↥α.ker := by
    rw [hR.ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨ψ, hψs, -, hψe⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hR.surj hk2
    (I := {3}) (a := 0) (m := 3) (by norm_num) le_rfl (Or.inl rfl) (Or.inr rfl) hno
  exact ⟨ψ, hψs, hψe⟩

theorem mem_rad1_of_le (hR : Data G T L R α) {N : Subgroup G}
    (hNQ : N ≤ liftPre α (FLc.QI 4 {1})) (hN2 : IsPGroup 2 N)
    (hYN : liftCore α (FLc.QI 4 {1}) ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N) :
    ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ rad1 := by
  obtain ⟨ψ, hψs, -, hψe⟩ := hR.exists_levi_one
  have hYH : liftCore α (FLc.QI 4 {1}) ≤ liftPre α (FLc.QI 4 {1}) := perfectCore_le _
  have hYs : ∀ s, ∃ y : ↥(liftPre α (FLc.QI 4 {1})),
      (y : G) ∈ liftCore α (FLc.QI 4 {1}) ∧ (blk1.comp (liftPreHom α (FLc.QI 4 {1}))) y = s := by
    intro s
    obtain ⟨y, hy⟩ := hψs ((FLc.slEquivGLt 3).symm s)
    refine ⟨⟨y, hYH y.2⟩, y.2, Units.ext ?_⟩
    rw [← slEquivGLt_symm_val s, ← hy, hψe y]
    rfl
  have h1 := eq_one_of_normal_two _ hYs hNQ hN2 hYN ⟨x, hNQ hx⟩ hx
  obtain ⟨hxL, hxQ⟩ := mem_liftPre_iff.mp (hNQ hx)
  refine ⟨hxL, mem_rad1_of_blk hxQ ?_⟩
  exact congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1

theorem mem_rad3_of_le (hR : Data G T L R α) {N : Subgroup G}
    (hNQ : N ≤ liftPre α (FLc.QI 4 {3})) (hN2 : IsPGroup 2 N)
    (hYN : liftCore α (FLc.QI 4 {3}) ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N) :
    ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ rad3 := by
  obtain ⟨ψ, hψs, hψe⟩ := hR.exists_levi_three
  have hYH : liftCore α (FLc.QI 4 {3}) ≤ liftPre α (FLc.QI 4 {3}) := perfectCore_le _
  have hYs : ∀ s, ∃ y : ↥(liftPre α (FLc.QI 4 {3})),
      (y : G) ∈ liftCore α (FLc.QI 4 {3}) ∧ (blk3.comp (liftPreHom α (FLc.QI 4 {3}))) y = s := by
    intro s
    obtain ⟨y, hy⟩ := hψs ((FLc.slEquivGLt 3).symm s)
    refine ⟨⟨y, hYH y.2⟩, y.2, Units.ext ?_⟩
    rw [← slEquivGLt_symm_val s, ← hy, hψe y]
    rfl
  have h1 := eq_one_of_normal_two _ hYs hNQ hN2 hYN ⟨x, hNQ hx⟩ hx
  obtain ⟨hxL, hxQ⟩ := mem_liftPre_iff.mp (hNQ hx)
  refine ⟨hxL, mem_rad3_of_blk hxQ ?_⟩
  exact congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1

omit [Finite G] in
theorem inf_le_liftPre {I : Set ℕ} (hRQ : ∀ l : ↥L, (l : G) ∈ R → α l ∈ FLc.QI 4 I)
    (hRY : R ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G)) :
    (liftCore α (FLc.QI 4 I) ⊔ R) ⊓ L ≤ liftPre α (FLc.QI 4 I) := by
  rintro x ⟨hxYR, hxL⟩
  have hx' : x ∈ (liftCore α (FLc.QI 4 I) : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRY]
    exact hxYR
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  have hyP : y ∈ liftPre α (FLc.QI 4 I) := perfectCore_le _ hy
  obtain ⟨hyL, hyQ⟩ := mem_liftPre_iff.mp hyP
  have hrL : r ∈ L := by
    have := L.mul_mem (L.inv_mem hyL) hxL
    simpa using this
  refine mem_liftPre_iff.mpr ⟨hxL, ?_⟩
  have e : (⟨y * r, hxL⟩ : ↥L) = ⟨y, hyL⟩ * ⟨r, hrL⟩ := rfl
  rw [e, map_mul]
  exact (FLc.QI 4 I).mul_mem hyQ (hRQ ⟨r, hrL⟩ hr)

theorem kills_of_rad (hR : Data G T L R α) {I : Set ℕ}
    (hRY : R ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G)) {P : Subgroup G}
    (hAP : qL L T ≤ P) (hPY : P ≤ liftCore α (FLc.QI 4 I) ⊔ R) {Rad : Subgroup SL4}
    (hrad : ∀ x ∈ P ⊓ L, ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ Rad) {g : G} (hgL : g ∈ L) {b : Bool}
    (hkill : ∀ r ∈ Rad, cubAct b (α ⟨g, hgL⟩) r = 1) : Kills b g (qL L T) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  have hm' : m ∈ (liftCore α (FLc.QI 4 I) : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRY]
    exact hPY hm
  obtain ⟨y, hy, r, hr, rfl⟩ := hm'
  obtain ⟨l, hl, c, hc, rfl⟩ := hR.mul r hr
  have hyL : y ∈ L := liftCore_le α _ hy
  have hl'L : y * l ∈ L := L.mul_mem hyL hl
  have hl'P : y * l ∈ P := by
    have e : y * (l * c) * c⁻¹ = y * l := by group
    rw [← e]
    exact P.mul_mem hm (P.inv_mem (hAP hc))
  obtain ⟨hl'L', hrl⟩ := hrad _ ⟨hl'P, hl'L⟩
  have hcL : cubAct b g (y * l) ∈ L := cubAct_mem (Subgroup.le_normalizer hgL) hl'L b
  have hcα : α ⟨cubAct b g (y * l), hcL⟩ = 1 := by
    rw [cubAct_hom α b hgL hl'L hcL]
    exact hkill _ hrl
  have hOq : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hR.TL))
  have hcO : cubAct b g (y * l) ∈ qL L T := by
    have hk : (⟨cubAct b g (y * l), hcL⟩ : ↥L) ∈ α.ker := hcα
    rw [hR.ker, Lem3328.mem_pCore_iff] at hk
    exact hOq hk
  have hAL : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hLTA : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hgLT : g ∈ L ⊔ T := Subgroup.mem_sup_left hgL
  have h1 := cubAct_mul_mem hAL hLTA (hLTA hgLT) (Subgroup.le_normalizer hgLT)
    (Subgroup.mem_sup_left hl'L) hc b
  show cubAct b g (y * (l * c)) ∈ qL L T
  have e : y * (l * c) = y * l * c := by group
  rw [e]
  have h2 := (qL L T).mul_mem h1 hcO
  rwa [inv_mul_cancel_right] at h2

theorem kills_rad1 (hR : Data G T L R α) {P : Subgroup G} (hAP : qL L T ≤ P)
    (hPY : P ≤ liftCore α (FLc.QI 4 {1}) ⊔ R)
    (hYP : liftCore α (FLc.QI 4 {1}) ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 P)
    {g : G} (hgL : g ∈ L) (hg : α ⟨g, hgL⟩ = x1) : Kills true g (qL L T) P := by
  refine hR.kills_of_rad hR.RY1 hAP hPY (Rad := rad1) (fun x hx => ?_) hgL (fun r hr => ?_)
  · refine hR.mem_rad1_of_le ((inf_le_inf_right L hPY).trans (inf_le_liftPre hR.RQ1 hR.RY1))
      (hP2.to_le inf_le_left) (fun y hy => OperatorJH.mem_normalizer_inf_of (hYP hy)
        (Subgroup.le_normalizer (liftCore_le α _ hy))) hx
  · rw [hg]
    exact cubAct_x1_rad1 r hr

theorem kills_rad3 (hR : Data G T L R α) {P : Subgroup G} (hAP : qL L T ≤ P)
    (hPY : P ≤ liftCore α (FLc.QI 4 {3}) ⊔ R)
    (hYP : liftCore α (FLc.QI 4 {3}) ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 P)
    {h : G} (hhL : h ∈ L) (hh : α ⟨h, hhL⟩ = x3) : Kills false h (qL L T) P := by
  refine hR.kills_of_rad hR.RY3 hAP hPY (Rad := rad3) (fun x hx => ?_) hhL (fun r hr => ?_)
  · refine hR.mem_rad3_of_le ((inf_le_inf_right L hPY).trans (inf_le_liftPre hR.RQ3 hR.RY3))
      (hP2.to_le inf_le_left) (fun y hy => OperatorJH.mem_normalizer_inf_of (hYP hy)
        (Subgroup.le_normalizer (liftCore_le α _ hy))) hx
  · rw [hh]
    exact cubAct_x3_rad3 r hr

theorem card_Q_ge_one (hR : Data G T L R α) :
    8 * Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1})) ⊓
      pCoreOf 2 L) ≤
      Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1}))) := by
  obtain ⟨ψ, -, hψk', hψe⟩ := hR.exists_levi_one
  have hRY := hR.RY1
  have htr : ∀ {j c : Fin 4} (hj : 1 ≤ (j : ℕ)) (hc : 1 ≤ (c : ℕ)) (hcj : c ≠ j)
      (h0j : (0 : Fin 4) ≠ j), SpecialLinearGroup.transvection h0j (1 : ZMod 2) ∈
        (α.comp (Subgroup.inclusion (L3321.FData.Q_le_L hRY))).range := by
    intro j c hj hc hcj h0j
    have h0c : (0 : Fin 4) ≠ c := fun e => by rw [← e] at hc; simp at hc
    obtain ⟨x, hx, hxe⟩ := L3318.exists_mem_liftCore hR.surj
      (L3318.transvection_mem_perfectCore_one (K := ZMod 2) (n := 4) le_rfl rfl hc h0c)
    obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hR.surj
      (L3318.transvection_mem_perfectCore_levi_one (K := ZMod 2) (n := 4) le_rfl hc hj hcj)
    have hψx : ψ ⟨x, hx⟩ = 1 := by
      apply Subtype.ext
      rw [hψe, hxe, SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one]
      ext a b
      rw [blkAt_apply, Matrix.add_apply, Matrix.single_apply]
      have hne : ¬ ((0 : Fin 4) = ⟨1 + (a : ℕ), by omega⟩ ∧ c = ⟨1 + (b : ℕ), by omega⟩) := by
        rintro ⟨e, -⟩
        have := congrArg Fin.val e
        simp only [Fin.val_zero] at this
        omega
      rw [ite_eq_right hne, add_zero, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]
    have hxO := L3321.FData.mem_pCoreOf_of_levi hRY hψk' hx hψx
    obtain ⟨hq, hqL, hqe⟩ := L3321.FData.comm_mem_Q (α := α) (liftCore_le α _) hx hxO hy
    refine ⟨⟨⁅x, y⁆, hq⟩, ?_⟩
    show α ⟨⁅x, y⁆, _⟩ = _
    rw [hqe, hxe, hye, SpecialLinearGroup.commutatorElement_transvection h0c hcj h0j, mul_one]
  refine L3321.card_ge_of_inj hR.ker (L3321.FData.Q_le_L hRY)
    (fun c => ⟨L3321.radM1 c, L3321.det_radM1 c⟩)
    (fun c c' h => L3321.radM1_inj c c' (congrArg Subtype.val h)) fun c => ?_
  exact L3321.radM1_mem (htr (c := 2) (by decide) (by decide) (by decide) _)
    (htr (c := 1) (by decide) (by decide) (by decide) _)
    (htr (c := 1) (by decide) (by decide) (by decide) _) c

end Data

end CFSG.Quasithin.H13.Case4Count
