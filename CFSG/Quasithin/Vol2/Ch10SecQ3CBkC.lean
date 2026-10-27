module

public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_blockQ_iff {X : Subgroup G} (x : X) :
    (x : G) ∈ blockQ X ↔ x ∈ CFSG.pCore 2 ↥X := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    assumption
  · intro hx
    exact ⟨x, by assumption, rfl⟩

theorem commutator_zpowers_le {A : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) : ⁅A, Subgroup.zpowers b⁆ ≤ A :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hb)

theorem eq_of_two_pow_mul_odd {a b m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ a * m = 2 ^ b * m') : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := congrArg (padicValNat 2) h
  rwa [padicValNat.mul (pow_ne_zero _ two_ne_zero) hm.pos.ne',
    padicValNat.mul (pow_ne_zero _ two_ne_zero) hm'.pos.ne', padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd hm'.not_two_dvd_nat, add_zero, add_zero] at h1

theorem eq_top_of_isPGroup_quot [Finite G] {X : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (N : Subgroup X) [N.Normal] (h : IsPGroup 2 (↥X ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hNt
  have : Nontrivial (↥X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNt
  have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isNilpotent (↥X ⧸ N) h.isNilpotent

section Counting

variable {X : Subgroup G} {F : Type} [Field F] {n : ℕ}

theorem card_eq_mul (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = CFSG.pCore 2 ↥X) {A : Subgroup G} (hA : A ≤ X) :
    Nat.card A = Nat.card ((A.subgroupOf X).map α) * Nat.card ↥(A ⊓ blockQ X) := by
  set A' := A.subgroupOf X with hA'
  set g := α.comp A'.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hg, MonoidHom.range_comp,
    Subgroup.range_subtype] at h1
  have h2 : (α.comp A'.subtype).ker = α.ker.subgroupOf A' := rfl
  have h3 : Nat.card (α.ker.subgroupOf A') = Nat.card ↥(A ⊓ blockQ X) := by
    rw [hαk]
    exact Nat.card_congr
      { toFun := fun z => ⟨((z : ↥A') : G), (z : ↥A').2, (mem_blockQ_iff _).mpr z.2⟩
        invFun := fun w => ⟨⟨⟨w, hA w.2.1⟩, w.2.1⟩,
          (mem_blockQ_iff (X := X) ⟨(w : G), hA w.2.1⟩).mp w.2.2⟩
        left_inv := fun z => rfl
        right_inv := fun w => rfl }
  rw [h2, h3] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv).symm

theorem card_map_sylow [Fintype F] (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    {P : Subgroup G} (hP : IsSylowTwoOf P X) : Nat.card ((P.subgroupOf X).map α) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' := P.subgroupOf X with hP'
  have hP'2 : IsPGroup 2 P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hP'i : ¬ 2 ∣ P'.index := hP.2.2
  obtain ⟨a, ha⟩ := (hP'2.map α).exists_card_eq
  have hi : ¬ 2 ∣ (P'.map α).index := fun h => hP'i (h.trans (Subgroup.index_map_dvd _ hαs))
  have hcard := Subgroup.card_mul_index (P'.map α)
  rw [SecA.card_SL_two_pow (by rw [Nat.card_eq_fintype_card, hF]), ha] at hcard
  have hodd : Odd (4 ^ n - 1) := by
    have h4 : Even (4 ^ n) := (by decide : Even 4).pow_of_ne_zero (by omega)
    have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    exact Nat.Even.sub_odd h1 h4 odd_one
  rw [ha, eq_of_two_pow_mul_odd (Nat.odd_iff.mpr (by omega)) hodd hcard]

theorem map_le_map_commutator [Fintype F] [CharP F 2]
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    {b : G} (hb : b ∈ X) (hsq : α ⟨b, hb⟩ ^ 2 ≠ 1) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hbP : b ∈ Subgroup.normalizer (P : Set G)) :
    (P.subgroupOf X).map α ≤ (⁅P, Subgroup.zpowers b⁆.subgroupOf X).map α := by
  set P'' := (P.subgroupOf X).map α with hP''
  set β := α ⟨b, hb⟩ with hβ
  have hbN : (⟨b, hb⟩ : ↥X) ∈ Subgroup.normalizer ((P.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    Subgroup.mem_normalizer_iff.mpr fun h => Subgroup.mem_normalizer_iff.mp hbP h
  have hβN : β ∈ Subgroup.normalizer (P'' : Set _) := Subgroup.le_normalizer_map α ⟨_, hbN, rfl⟩
  have hP''2 : IsPGroup 2 P'' := (hP2.comap_of_injective X.subtype X.subtype_injective).map α
  have h1 := le_commutator_of_fix (le_refl P'') hβN fun x hx hxb => by
    obtain ⟨k, hk⟩ := hP''2 ⟨x, hx⟩
    exact eq_one_of_commute_of_pow β x hsq hxb.symm (congrArg Subtype.val hk)
  refine h1.trans ?_
  rw [Subgroup.commutator_le]
  rintro _ ⟨p, hp, rfl⟩ y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨⁅p, ⟨b, hb⟩ ^ k⁆, ?_, by rw [map_commutatorElement, map_zpow]⟩
  change ⁅(p : G), b ^ k⁆ ∈ ⁅P, Subgroup.zpowers b⁆
  exact Subgroup.commutator_mem_commutator hp (Subgroup.zpow_mem_zpowers b k)

theorem card_commutator_le [Finite G] [Fintype F] [CharP F 2] (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n)
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥X) {b : G} (hb : b ∈ X) (hsq : α ⟨b, hb⟩ ^ 2 ≠ 1)
    {P : Subgroup G} (hP : IsSylowTwoOf P X) (hbP : b ∈ Subgroup.normalizer (P : Set G)) :
    2 ^ n * Nat.card ↥(⁅blockQ X, Subgroup.zpowers b⁆ : Subgroup G) ≤
      Nat.card ↥(⁅P, Subgroup.zpowers b⁆ : Subgroup G) := by
  have hCP : ⁅P, Subgroup.zpowers b⁆ ≤ P := commutator_zpowers_le hbP
  rw [card_eq_mul α hαk (hCP.trans hP.1)]
  refine Nat.mul_le_mul ?_ ?_
  · rw [← card_map_sylow hn hF α hαs hP]
    exact Subgroup.card_le_of_le (map_le_map_commutator α hb hsq hP.2.1 hbP)
  · apply Subgroup.card_le_of_le
    exact le_inf (Subgroup.commutator_mono (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP) le_rfl)
      (commutator_zpowers_le (C1.le_normalizer_blockQ X hb))

theorem sq_ne_one (hn : 2 ≤ n) (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = CFSG.pCore 2 ↥X) {b : G} (hb : b ∈ X) (hbo : orderOf b = 2 ^ n - 1) :
    α ⟨b, hb⟩ ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hob : orderOf (⟨b, hb⟩ : ↥X) = 2 ^ n - 1 := by rw [Subgroup.orderOf_mk, hbo]
  have hodd : Odd (orderOf (⟨b, hb⟩ : ↥X)) := by
    rw [hob]
    exact Nat.Even.sub_odd (by omega) ((by decide : Even 2).pow_of_ne_zero (by omega)) odd_one
  have hk : IsPGroup 2 α.ker := hαk ▸ CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hord := orderOf_map_eq_of_odd α hk hodd
  intro h
  have h2 := orderOf_dvd_of_pow_eq_one h
  rw [hord, hob] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem mem_blockQ_of_commute [CharP F 2] (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = CFSG.pCore 2 ↥X) {b : G} (hb : b ∈ X) (hsq : α ⟨b, hb⟩ ^ 2 ≠ 1) {x : G}
    (hx : x ∈ X) {k : ℕ} (hxk : x ^ 2 ^ k = 1) (hxb : x * b = b * x) : x ∈ blockQ X := by
  have h1 : α ⟨x, hx⟩ = 1 := by
    refine eq_one_of_commute_of_pow (α ⟨b, hb⟩) (α ⟨x, hx⟩) hsq ?_ (k := k) ?_
    · rw [← map_mul, ← map_mul]
      exact congrArg α (Subtype.ext hxb.symm)
    · rw [← map_pow]
      have : (⟨x, hx⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
      rw [this, map_one]
  have h2 : (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := hαk ▸ h1
  exact (mem_blockQ_iff ⟨x, hx⟩).mpr h2

theorem blockU_le_of_commutator [Finite G] [Fintype F] (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hperf : ⁅X, X⁆ = X)
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥X) {b : G} (hb : b ∈ X) (hb1 : α ⟨b, hb⟩ ≠ 1)
    {V : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ⁅blockQ X, Subgroup.zpowers b⁆ ≤ V) : blockU X ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G :=
    { carrier := {y | y ∈ X ∧ ∀ x ∈ blockQ X, x * y * x⁻¹ * y⁻¹ ∈ V}
      one_mem' := ⟨X.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨X.mul_mem hy hz, fun x hx => ?_⟩
        have e : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
            (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [e]
        exact V.mul_mem (hy' x hx) ((Subgroup.mem_normalizer_iff.mp (hXV hy) _).mp (hz' x hx))
      inv_mem' := by
        rintro y ⟨hy, hy'⟩
        refine ⟨X.inv_mem hy, fun x hx => ?_⟩
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hXV (X.inv_mem hy)) _).mp
          (V.inv_mem (hy' x hx)) }
  set N' := N.subgroupOf X with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun y hy g => ⟨X.mul_mem (X.mul_mem g.2 hy.1) (X.inv_mem g.2), fun x hx => ?_⟩⟩
    have hx' : (g : G)⁻¹ * x * g ∈ blockQ X := by
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ X (X.inv_mem g.2)) x).mp hx
      simpa using this
    have e : x * ((g : G) * y * (g : G)⁻¹) * x⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ =
        (g : G) * (((g : G)⁻¹ * x * g) * y * ((g : G)⁻¹ * x * g)⁻¹ * (y : G)⁻¹) * (g : G)⁻¹ := by
      group
    change x * ((g : G) * y * (g : G)⁻¹) * x⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈ V
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXV g.2) _).mp (hy.2 _ hx')
  have hbN : (⟨b, hb⟩ : ↥X) ∈ N' := ⟨hb, fun x hx => by
    have := hcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers b))
    rwa [commutatorElement_def] at this⟩
  have hαN : N'.map α = ⊤ := by
    have := Ch11.SecA.isSimpleGroup_SL2 (K := F) hn (by rw [Nat.card_eq_fintype_card, hF])
    have : (N'.map α).Normal := hN'n.map α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map α) with h | h
    · exact absurd (h ▸ Subgroup.mem_map_of_mem α hbN) (by rwa [Subgroup.mem_bot])
    · exact h
  have h2 : IsPGroup 2 (↥X ⧸ N') := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, hmy⟩ : α y ∈ N'.map α := hαN ▸ Subgroup.mem_top _
    have hk : m⁻¹ * y ∈ CFSG.pCore 2 ↥X := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hmy, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨_, hk⟩
    refine ⟨k, ?_⟩
    have e : (QuotientGroup.mk y : ↥X ⧸ N') = QuotientGroup.mk (m⁻¹ * y) := by
      rw [QuotientGroup.eq]
      have : (m⁻¹ * y)⁻¹ * y = y⁻¹ * m * y := by group
      rw [← QuotientGroup.eq, QuotientGroup.eq_iff_div_mem]
      have hmem : y * (m⁻¹ * y)⁻¹ = y * y⁻¹ * m := by group
      simpa [div_eq_mul_inv, hmem] using hm
    rw [e, ← QuotientGroup.mk_pow, show (m⁻¹ * y) ^ 2 ^ k = 1 from congrArg Subtype.val hk',
      QuotientGroup.mk_one]
  have htop : N' = ⊤ := eq_top_of_isPGroup_quot hperf N' h2
  rw [blockU, Subgroup.commutator_le]
  intro x hx y hy
  have : (⟨y, hy⟩ : ↥X) ∈ N' := htop ▸ Subgroup.mem_top _
  rw [commutatorElement_def]
  exact this.2 x hx

end Counting


end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
