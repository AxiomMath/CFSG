module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GR
public import CFSG.Quasithin.Background.SevenL4Model

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

theorem eq_one_of_central4 {z : SL4} (hz : ∀ g : SL4, g * z = z * g) : z = 1 := by
  obtain ⟨r, hr, hrz⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp (Subgroup.mem_center_iff.mpr hz)
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    revert hr
    generalize r = s
    revert s
    decide
  apply Subtype.ext
  rw [← hrz, hr1, map_one]
  rfl

omit [Finite G] in
theorem mem_pCoreOf_of_central {L : Subgroup G} {α : ↥L →* SL4} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) {c : G} (hc : c ∈ L)
    (hcen : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) : c ∈ pCoreOf 2 L := by
  have hker : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ pCoreOf 2 L := fun l => by
    rw [← MonoidHom.mem_ker, hαk, Lem3328.mem_pCore_iff]
  have hcomm : ∀ x : ↥L, α x * α ⟨c, hc⟩ = α ⟨c, hc⟩ * α x := by
    intro x
    have hmem : c * x * c⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hc x.2) (L.inv_mem hc)) (L.inv_mem x.2)
    have h2 := (hker ⟨_, hmem⟩).mpr (hcen x x.2)
    have e : (⟨_, hmem⟩ : ↥L) = ⟨c, hc⟩ * x * (⟨c, hc⟩)⁻¹ * x⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc α x * α ⟨c, hc⟩ =
          (α ⟨c, hc⟩ * α x * (α ⟨c, hc⟩)⁻¹ * (α x)⁻¹)⁻¹ * (α ⟨c, hc⟩ * α x) := by group
      _ = α ⟨c, hc⟩ * α x := by rw [h2, inv_one, one_mul]
  have h1 : α ⟨c, hc⟩ = 1 := eq_one_of_central4 fun g => by
    obtain ⟨x, rfl⟩ := hαs g
    exact hcomm x
  exact (hker _).mp h1

theorem mem_qL_of_central {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT2 : IsPGroup 2 T) {α : ↥L →* SL4} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) {c : G} (hc : c ∈ L ⊔ T)
    (hcen : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) : c ∈ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hNO : ∀ g ∈ Subgroup.normalizer (L : Set G),
      g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg
  let K : Subgroup G :=
    { carrier := {g | g ∈ L ⊔ T ∧ ∀ x ∈ L, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 L}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(L ⊔ T).mul_mem ha hb, fun x hx => ?_⟩
        have hbx : b * x * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLTN hb) x).mp hx
        have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ pCoreOf 2 L :=
          (Subgroup.mem_normalizer_iff.mp (hNO a (hLTN ha)) _).mp (hb' x hx)
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 L).mul_mem h1 (ha' x hx)
      one_mem' := ⟨(L ⊔ T).one_mem, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(L ⊔ T).inv_mem ha, fun x hx => ?_⟩
        have hy : a⁻¹ * x * a⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hLTN ((L ⊔ T).inv_mem ha)) x).mp hx
        have h1 := (pCoreOf 2 L).inv_mem (ha' _ hy)
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
            (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by group
        rw [e]
        exact h1 }
  have hKLT : K ≤ L ⊔ T := fun g hg => hg.1
  have hnorm : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    refine OperatorJH.mem_normalizer_of_conj_mem_of fun k ⟨hk, hk'⟩ => ⟨?_, fun x hx => ?_⟩
    · exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hk) ((L ⊔ T).inv_mem hg)
    · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hLTN ((L ⊔ T).inv_mem hg)) x).mp hx
      have h2 : g * (k * (g⁻¹ * x * g⁻¹⁻¹) * k⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp (hNO g (hLTN hg)) _).mp (hk' _ hx')
      have e : g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ * x⁻¹ =
          g * (k * (g⁻¹ * x * g⁻¹⁻¹) * k⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
      rw [e]
      exact h2
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨k, hkLT, hkc⟩
    have hk' : k ∈ (L : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
      exact hkLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hk'
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hstep : ∀ n : ℕ, ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨l', hl', e⟩ := ih
        refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) l).mp hl
        · rw [pow_succ, e]
          group
    obtain ⟨l', hl', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkK : (l * t) ^ 2 ^ a ∈ K := K.pow_mem ⟨hkLT, hkc⟩ _
    have hO : l' ∈ pCoreOf 2 L := by
      refine mem_pCoreOf_of_central hαs hαk hl' fun x hx => ?_
      have := hkK.2 x hx
      rwa [e] at this
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hO⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : l' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, e, hb']
  have hKQ : K ≤ qL L T :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKLT hnorm hK2
  exact hKQ ⟨hc, hcen⟩

theorem exists_mul {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α) {r : G}
    (hr : r ∈ R) : ∃ l ∈ L, ∃ c ∈ qL L T, r = l * c := by
  obtain ⟨y, -, hy⟩ := hR.conj r hr
  have hrT : r ∈ T := hR.RT hr
  refine ⟨y, y.2, (y : G)⁻¹ * r, ?_, by group⟩
  refine mem_qL_of_central hR.TL hR.hyp.sylow.1 hR.surj hR.ker
    ((L ⊔ T).mul_mem (Subgroup.mem_sup_left (L.inv_mem y.2)) (Subgroup.mem_sup_right hrT))
    fun x hx => ?_
  have hrx : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hR.TL hrT) x).mp hx
  have hmem : (y : G)⁻¹ * r * x * ((y : G)⁻¹ * r)⁻¹ * x⁻¹ ∈ L := by
    have e : (y : G)⁻¹ * r * x * ((y : G)⁻¹ * r)⁻¹ * x⁻¹ = (y : G)⁻¹ * (r * x * r⁻¹) * y * x⁻¹ := by
      group
    rw [e]
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem y.2) hrx) y.2) (L.inv_mem hx)
  have h1 : α ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥L) = y⁻¹ * ⟨r * x * r⁻¹, hrx⟩ * y * (⟨x, hx⟩ : ↥L)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hy ⟨x, hx⟩ hrx]
    group
  have h2 : (⟨_, hmem⟩ : ↥L) ∈ α.ker := h1
  rw [hR.ker, Lem3328.mem_pCore_iff] at h2
  exact h2

omit [Finite G] in
theorem cubAct_hom {L : Subgroup G} {H : Type} [Group H] (f : ↥L →* H) (b : Bool) {g y : G}
    (hg : g ∈ L) (hy : y ∈ L) (hc : cubAct b g y ∈ L) :
    f ⟨cubAct b g y, hc⟩ = cubAct b (f ⟨g, hg⟩) (f ⟨y, hy⟩) := by
  have e : (⟨cubAct b g y, hc⟩ : ↥L) = cubAct b ⟨g, hg⟩ ⟨y, hy⟩ :=
    Subtype.ext (by simp [cubAct])
  rw [e]
  simp only [cubAct, map_mul, map_pow, map_inv]

theorem pow_eight_pow {M : Type} [Monoid M] {x : M} (h : x ^ 7 = 1) (c : ℕ) : x ^ 8 ^ c = x := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, pow_mul, ih, pow_succ, h, one_mul]

@[expose] noncomputable def blk1 : ↥(FLc.QI 4 {1}) →* GL (Fin 3) (ZMod 2) :=
  (blkMon (FLc.QI 4 {1}) 1 3 (by norm_num)
    (blockLeft_of_stabilizer fun _ hg => (mem_flagStabilizer.mp hg) 1 rfl)
    (blockRight_top _ (by norm_num))).toHomUnits

@[expose] noncomputable def blk3 : ↥(FLc.QI 4 {3}) →* GL (Fin 3) (ZMod 2) :=
  (blkMon (FLc.QI 4 {3}) 0 3 (by norm_num) (blockLeft_zero _ 3)
    (blockRight_of_stabilizer fun _ hg => (mem_flagStabilizer.mp hg) 3 rfl)).toHomUnits

theorem exists_levi_three {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α) :
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

omit [Finite G] in
theorem mem_liftPre_iff {L : Subgroup G} {α : ↥L →* SL4} {Q : Subgroup SL4} {x : G} :
    x ∈ liftPre α Q ↔ ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ Q := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hxL, hx⟩
    exact ⟨⟨x, hxL⟩, hx, rfl⟩

@[expose] noncomputable def liftPreHom {L : Subgroup G} (α : ↥L →* SL4) (Q : Subgroup SL4) :
    ↥(liftPre α Q) →* ↥Q where
  toFun x := ⟨α ⟨x, (mem_liftPre_iff.mp x.2).1⟩, (mem_liftPre_iff.mp x.2).2⟩
  map_one' := Subtype.ext (map_one α)
  map_mul' x y := Subtype.ext (map_mul α ⟨x, (mem_liftPre_iff.mp x.2).1⟩
    ⟨y, (mem_liftPre_iff.mp y.2).1⟩)

omit [Finite G] in
theorem eq_one_of_normal_two {H : Subgroup G} (φ : ↥H →* GL (Fin 3) (ZMod 2)) {Y N : Subgroup G}
    (hYs : ∀ s, ∃ y : ↥H, (y : G) ∈ Y ∧ φ y = s) (hNH : N ≤ H) (hN2 : IsPGroup 2 N)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (n : ↥H) (hn : (n : G) ∈ N) : φ n = 1 := by
  set B := (N.subgroupOf H).map φ with hBdef
  have hB2 : IsPGroup 2 ↥B := (hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm).map φ
  have hBn : B.Normal := ⟨fun b hb s => by
    obtain ⟨m, hm, rfl⟩ := hb
    obtain ⟨y, hyY, rfl⟩ := hYs s
    have hm' : (m : G) ∈ N := Subgroup.mem_subgroupOf.mp hm
    refine ⟨y * m * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hYN hyY) m).mp hm'⟩
  have hB : B = ⊥ := CFSG.Quasithin.FFC.eq_bot_of_normal_isPGroup hB2
  have hmem : φ n ∈ B := ⟨n, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  rw [hB] at hmem
  exact Subgroup.mem_bot.mp hmem

omit [Finite G] in
theorem slEquivGLt_symm_val (s : GL (Fin 3) (ZMod 2)) :
    (((FLc.slEquivGLt 3).symm s : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  conv_rhs => rw [← (FLc.slEquivGLt 3).apply_symm_apply s]
  rfl

theorem mem_rad1_of_le {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    {N : Subgroup G} (hNQ : N ≤ liftPre α (FLc.QI 4 {1})) (hN2 : IsPGroup 2 N)
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

theorem mem_rad3_of_le {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    {N : Subgroup G} (hNQ : N ≤ liftPre α (FLc.QI 4 {3})) (hN2 : IsPGroup 2 N)
    (hYN : liftCore α (FLc.QI 4 {3}) ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N) :
    ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ rad3 := by
  obtain ⟨ψ, hψs, hψe⟩ := exists_levi_three hR
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

theorem inf_le_liftPre {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    (I : Set ℕ) : (liftCore α (FLc.QI 4 I) ⊔ R) ⊓ L ≤ liftPre α (FLc.QI 4 I) := by
  rintro x ⟨hxYR, hxL⟩
  have hx' : x ∈ (liftCore α (FLc.QI 4 I) : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hR.le_normalizer_Y I)]
    exact hxYR
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  have hyP : y ∈ liftPre α (FLc.QI 4 I) := perfectCore_le _ hy
  obtain ⟨hyL, hyQ⟩ := mem_liftPre_iff.mp hyP
  have hrL : r ∈ L := by
    have := L.mul_mem (L.inv_mem hyL) hxL
    simpa using this
  have hrQ : α ⟨r, hrL⟩ ∈ FLc.QI 4 I :=
    FLc.Ut_le_QI 4 I (hR.mem_Ut ⟨r, hrL⟩ hr)
  refine mem_liftPre_iff.mpr ⟨hxL, ?_⟩
  have e : (⟨y * r, hxL⟩ : ↥L) = ⟨y, hyL⟩ * ⟨r, hrL⟩ := rfl
  rw [e, map_mul]
  exact (FLc.QI 4 I).mul_mem hyQ hrQ

theorem kills_of_rad {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    {I : Set ℕ} {P : Subgroup G} (hAP : qL L T ≤ P)
    (hPY : P ≤ liftCore α (FLc.QI 4 I) ⊔ R) {Rad : Subgroup SL4}
    (hrad : ∀ x ∈ P ⊓ L, ∃ hxL : x ∈ L, α ⟨x, hxL⟩ ∈ Rad) {g : G} (hgL : g ∈ L) {b : Bool}
    (hkill : ∀ r ∈ Rad, cubAct b (α ⟨g, hgL⟩) r = 1) : Kills b g (qL L T) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  have hm' : m ∈ (liftCore α (FLc.QI 4 I) : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hR.le_normalizer_Y I)]
    exact hPY hm
  obtain ⟨y, hy, r, hr, rfl⟩ := hm'
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul hR hr
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

theorem kills_rad1 {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    {P : Subgroup G} (hAP : qL L T ≤ P) (hPY : P ≤ liftCore α (FLc.QI 4 {1}) ⊔ R)
    (hYP : liftCore α (FLc.QI 4 {1}) ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 P)
    {g : G} (hgL : g ∈ L) (hg : α ⟨g, hgL⟩ = x1) : Kills true g (qL L T) P := by
  refine kills_of_rad hR hAP hPY (Rad := rad1) (fun x hx => ?_) hgL (fun r hr => ?_)
  · refine mem_rad1_of_le hR ((inf_le_inf_right L hPY).trans (inf_le_liftPre hR {1}))
      (hP2.to_le inf_le_left) (fun y hy => OperatorJH.mem_normalizer_inf_of (hYP hy)
        (Subgroup.le_normalizer (liftCore_le α _ hy))) hx
  · rw [hg]
    exact cubAct_x1_rad1 r hr

theorem kills_rad3 {T M L D R : Subgroup G} {α : ↥L →* SL4} (hR : RData G T M L D R α)
    {P : Subgroup G} (hAP : qL L T ≤ P) (hPY : P ≤ liftCore α (FLc.QI 4 {3}) ⊔ R)
    (hYP : liftCore α (FLc.QI 4 {3}) ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 P)
    {h : G} (hhL : h ∈ L) (hh : α ⟨h, hhL⟩ = x3) : Kills false h (qL L T) P := by
  refine kills_of_rad hR hAP hPY (Rad := rad3) (fun x hx => ?_) hhL (fun r hr => ?_)
  · refine mem_rad3_of_le hR ((inf_le_inf_right L hPY).trans (inf_le_liftPre hR {3}))
      (hP2.to_le inf_le_left) (fun y hy => OperatorJH.mem_normalizer_inf_of (hYP hy)
        (Subgroup.le_normalizer (liftCore_le α _ hy))) hx
  · rw [hh]
    exact cubAct_x3_rad3 r hr

theorem x1_mem_perfectCore : x1 ∈ perfectCore (FLc.QI 4 {1}) := by
  rw [x1_eq_prod]
  refine Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_) ?_ <;>
  exact L3318.transvection_mem_perfectCore_levi_one (K := ZMod 2) (n := 4) le_rfl (by decide)
    (by decide) _

theorem x3_mem_perfectCore : x3 ∈ perfectCore (FLc.QI 4 {3}) := by
  have hno : ∀ c' ∈ ({3} : Set ℕ), ¬ (0 < c' ∧ c' < 0 + 3) := by
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    omega
  have hT : ∀ {a c : Fin 4} (ha : (a : ℕ) < 3) (hc : (c : ℕ) < 3) (hac : a ≠ c),
      SpecialLinearGroup.transvection hac (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {3}) := by
    intro a c ha hc hac
    rw [L3318.transvection_eq_liftT (by norm_num) ha hc hac]
    exact Ln2.liftT_mem_perfectCore (by norm_num) le_rfl hno _
  rw [x3_eq_prod]
  refine Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_) ?_ <;>
  exact hT (by decide) (by decide) _

theorem exists_x1 {L : Subgroup G} {α : ↥L →* SL4} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ∃ g ∈ liftCore α (FLc.QI 4 {1}), ∃ hgL : g ∈ L, α ⟨g, hgL⟩ = x1 ∧ g ^ 7 = 1 := by
  obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hαs x1_mem_perfectCore
  have hyL := liftCore_le α _ hy
  have h7 : (⟨y, hyL⟩ : ↥L) ^ 7 ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_pow, hye, x1_pow_seven]
  rw [hαk] at h7
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup ⟨_, h7⟩
  have hc' : y ^ (7 * 2 ^ c) = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hc
    simpa [pow_mul] using this
  refine ⟨y ^ 8 ^ c, (liftCore α _).pow_mem hy _, L.pow_mem hyL _, ?_, ?_⟩
  · have e : (⟨y ^ 8 ^ c, L.pow_mem hyL _⟩ : ↥L) = ⟨y, hyL⟩ ^ 8 ^ c := rfl
    rw [e, map_pow, hye, pow_eight_pow x1_pow_seven]
  · rw [← pow_mul, show 8 ^ c * 7 = 7 * 2 ^ c * 4 ^ c by
      rw [show (8 : ℕ) = 2 * 4 from rfl, mul_pow]; ring, pow_mul, hc', one_pow]

theorem mem_liftCore_of_pow_seven {L : Subgroup G} {α : ↥L →* SL4}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) {Q : Subgroup SL4} {h : G}
    (hhL : h ∈ L) (hhQ : α ⟨h, hhL⟩ ∈ perfectCore Q) (hh7 : h ^ 7 = 1) : h ∈ liftCore α Q := by
  obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hαs hhQ
  have hyL := liftCore_le α Q hy
  have huL : y⁻¹ * h ∈ L := L.mul_mem (L.inv_mem hyL) hhL
  have hu1 : α ⟨y⁻¹ * h, huL⟩ = 1 := by
    have e : (⟨y⁻¹ * h, huL⟩ : ↥L) = (⟨y, hyL⟩ : ↥L)⁻¹ * ⟨h, hhL⟩ := rfl
    rw [e, map_mul, map_inv, hye, inv_mul_cancel]
  have huP : y⁻¹ * h ∈ liftPre α Q :=
    mem_liftPre_iff.mpr ⟨huL, by rw [hu1]; exact Q.one_mem⟩
  have huN : y⁻¹ * h ∈ Subgroup.normalizer (liftCore α Q : Set G) :=
    L3316.mem_normalizer_perfectCore (Subgroup.le_normalizer huP)
  have hk : (⟨y⁻¹ * h, huL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk]
    exact hu1
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup ⟨_, hk⟩
  have huc : (y⁻¹ * h) ^ 2 ^ c = 1 := by
    simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hc
  have hstep : ∀ n : ℕ, (y * (y⁻¹ * h)) ^ n * ((y⁻¹ * h) ^ n)⁻¹ ∈ liftCore α Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (y * (y⁻¹ * h)) ^ (n + 1) * ((y⁻¹ * h) ^ (n + 1))⁻¹ =
          ((y * (y⁻¹ * h)) ^ n * ((y⁻¹ * h) ^ n)⁻¹) *
            ((y⁻¹ * h) ^ n * y * ((y⁻¹ * h) ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact (liftCore α Q).mul_mem ih ((Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (liftCore α Q : Set G)).pow_mem huN n) y).mp hy)
  have h2 : h ^ 2 ^ c ∈ liftCore α Q := by
    have := hstep (2 ^ c)
    rwa [huc, inv_one, mul_one, mul_inv_cancel_left] at this
  have h8 : h = (h ^ 2 ^ c) ^ 4 ^ c := by
    rw [← pow_mul, ← mul_pow, show (2 * 4 : ℕ) = 8 from rfl, pow_eight_pow hh7]
  rw [h8]
  exact (liftCore α Q).pow_mem h2 _

end CFSG.Quasithin.H13.Case4Count
