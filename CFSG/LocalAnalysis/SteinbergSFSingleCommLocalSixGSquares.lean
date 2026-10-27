module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixE
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Matrix Polynomial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)

namespace LocalSixE

theorem pow_three_eq_zero_of_isNilpotent {F : Type} [Field F]
    {N : Matrix (Fin 3) (Fin 3) F} (hN : IsNilpotent N) : N ^ 3 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h2 : N.charpoly = X ^ 3 := by
    have := h1.eq_zero
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.1 this
  have h3 := Matrix.aeval_self_charpoly N
  rw [h2, map_pow, aeval_X] at h3
  exact h3

theorem pow_four_eq_one_of_GL_three {F : Type} [Field F] [CharP F 2] {x : GL (Fin 3) F} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) - 1 with hNdef
  have hNk : N ^ 2 ^ k = 0 := by
    rw [hNdef, sub_pow_char_pow_of_commute _ _ (Commute.one_right _), one_pow,
      ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  have hN3 : N ^ 3 = 0 := pow_three_eq_zero_of_isNilpotent ⟨_, hNk⟩
  apply Units.ext
  have h4 : N ^ 2 ^ 2 = 0 := by
    rw [show (2 : ℕ) ^ 2 = 3 + 1 by norm_num, pow_succ, hN3, zero_mul]
  have h5 : (x : Matrix (Fin 3) (Fin 3) F) = N + 1 := by rw [hNdef, sub_add_cancel]
  rw [Units.val_pow_eq_pow_val, h5, show (4 : ℕ) = 2 ^ 2 by norm_num,
    add_pow_char_pow_of_commute _ _ (Commute.one_right _), h4, zero_add, one_pow, Units.val_one]

theorem pow_four_eq_one_of_statedProj {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (GL (Fin 3) F)} (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) F).det = 1)
    {y : StatedProj H} {k : ℕ} (hy : y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ^ 2 ^ k ∈ (StatedScalars (Fin 3) F).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy]
  have hz3 : ((x : GL (Fin 3) F) ^ 2 ^ k) ^ 3 = 1 := by
    rw [mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    have hdetc : ((x ^ 2 ^ k : H) : GL (Fin 3) F).val.det = 1 := hdet _ (x ^ 2 ^ k).2
    rw [← SubmonoidClass.coe_pow, ← hc]
    rw [← hc] at hdetc
    have hc3 : c ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : Matrix (Fin 3) (Fin 3) F) =
          Matrix.scalar (Fin 3) (c : F) := rfl
      rw [this, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdetc
      exact hdetc
    rw [← map_pow, hc3, map_one]
  have h12 : x ^ 12 = 1 := by
    have h1 : ((x : GL (Fin 3) F) ^ 3) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact hz3
    have h2 := pow_four_eq_one_of_GL_three h1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, show (12 : ℕ) = 3 * 4 by norm_num, pow_mul]
    exact h2
  have hy12 : (x : StatedProj H) ^ 12 = 1 := by rw [← QuotientGroup.mk_pow, h12]; rfl
  have hd1 : orderOf (x : StatedProj H) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy
  have hd2 : orderOf (x : StatedProj H) ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one hy12
  have hcop : Nat.Coprime (orderOf (x : StatedProj H)) 3 :=
    Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left _ (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right hd2)


theorem det_eq_one_of_mem_statedSL {n : ℕ} {F : Type} [Field F] {A : GL (Fin n) F}
    (hA : A ∈ StatedSL n F) : (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem det_eq_one_of_mem_statedSU {n q : ℕ} {F : Type} [Field F] {A : GL (Fin n) F}
    (hA : A ∈ StatedSU n q F) : (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem pow_four_eq_one_of_classicalModel {D : Type} [Group D] {m : ℕ}
    (hD : StatedClassicalModel D .PSL 3 2 m ∨ StatedClassicalModel D .PSU 3 2 m) {y : D} {k : ℕ}
    (hy : y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  rcases hD with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩
  · have : CharP F 2 := PrincipalLayers.charP_two_of_card hF
    have h1 : e y ^ 2 ^ k = 1 := by rw [← map_pow, hy, map_one]
    have h2 := pow_four_eq_one_of_statedProj (fun A hA => det_eq_one_of_mem_statedSL hA) h1
    rw [← map_pow, map_eq_one_iff e e.injective] at h2
    exact h2
  · have : CharP F 2 := PrincipalLayers.charP_two_of_card (m := 2 * m) (by rw [hF, ← pow_mul,
      mul_comm])
    have h1 : e y ^ 2 ^ k = 1 := by rw [← map_pow, hy, map_one]
    have h2 := pow_four_eq_one_of_statedProj (fun A hA => det_eq_one_of_mem_statedSU hA) h1
    rw [← map_pow, map_eq_one_iff e e.injective] at h2
    exact h2


theorem mem_of_sq_eq_one {G : Type*} [Group G] [Finite G] {W U : Subgroup G}
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hU : closure {x | ∃ w ∈ W, x = w * w} = U)
    (h4 : ∀ w ∈ W, w ^ 4 = 1) (hcard : Nat.card W = Nat.card U * Nat.card U) {w : G}
    (hw : w ∈ W) (hw2 : w * w = 1) : w ∈ U := by
  let sq : ↥W →* ↥W :=
    { toFun := fun x => x * x
      map_one' := by simp
      map_mul' := fun x y => Subtype.ext (by
        change (x : G) * y * (x * y) = x * x * (y * y)
        have hxy := hWc x x.2 y y.2
        calc (x : G) * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hxy]
          _ = x * x * (y * y) := by group) }
  have hsq : ∀ x : W, ((sq x : W) : G) = x * x := fun _ => rfl
  have hrange : sq.range.map W.subtype = U := by
    rw [← hU]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact subset_closure ⟨x, x.2, rfl⟩
    · rw [closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨sq ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  have hcardR : Nat.card sq.range = Nat.card U := by
    rw [← hrange, card_map_of_injective W.subtype_injective]
  have hcardK : Nat.card sq.ker = Nat.card U := by
    have h1 := card_eq_card_quotient_mul_card_subgroup sq.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange sq).toEquiv, hcardR, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
  have hUK : U ≤ sq.ker.map W.subtype := by
    rw [← hrange]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨sq x, ?_, rfl⟩
    change sq x ∈ sq.ker
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hsq, hsq, OneMemClass.coe_one]
    have := h4 x x.2
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 by norm_num, pow_add, pow_add, pow_add, pow_one] at this
    rw [← this]
    group
  have hUeq : U = sq.ker.map W.subtype :=
    Subgroup.eq_of_le_of_card_ge hUK (by
      rw [card_map_of_injective W.subtype_injective, hcardK])
  rw [hUeq]
  refine ⟨⟨w, hw⟩, ?_, rfl⟩
  change (⟨w, hw⟩ : W) ∈ sq.ker
  rw [MonoidHom.mem_ker]
  exact Subtype.ext hw2




end LocalSixE

namespace PrincipalLayers.AxisData

open PrincipalLayers CFSG.RankThree.PartOne.KCRootAxis

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))

theorem pow_four_eq_one_of_model
    (h : AxisData F K n S J Y V U t hk) {m : ℕ}
    (hm : StatedClassicalModel ↥𝐃 .PSL 3 2 m ∨ StatedClassicalModel ↥𝐃 .PSU 3 2 m) :
    ∀ v ∈ V, v ^ 4 = 1 := by
  intro v hv
  obtain ⟨k, hk'⟩ := h.V_pgroup ⟨v, hv⟩
  have hvk : v ^ 2 ^ k = 1 := congrArg Subtype.val hk'
  have hθD := h.map_V_le (mem_map_of_mem θ hv)
  have hy : (⟨_, hθD⟩ : ↥𝐃) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← map_pow, hvk, map_one, OneMemClass.coe_one]
  have hy4 := LocalSixE.pow_four_eq_one_of_classicalModel hm hy
  have hθ4 : θ (v ^ 4) = θ 1 := by
    rw [map_pow, map_one]
    have := congrArg Subtype.val hy4
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  exact h.injOn_V (pow_mem hv 4) (one_mem _) hθ4

end PrincipalLayers.AxisData

namespace LocalSixE

section Squares

open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic FullCenterTorus
  FullCenterWeyl SingleComm NextCores RootStandard TorusLayer PrincipalLayers
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}
set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇𝐭[" k "]" => centralizer (𝐉[k] : Set G)
set_option quotPrecheck false in
local notation "𝐘[" k "]" => closure {x : G | ∃ g ∈ 𝐇𝐭[k], ∃ s ∈ 𝐒[k], x = g⁻¹ * s * g}
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)


theorem sq_V_mem_U (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector
      fun D _ => CFSG.Blueprint.Catalog D)
    [IsSimpleGroup G] (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ v ∈ 𝐕[i, i], v * v ∈ 𝐔[i] := by
  obtain ⟨htH, _, hd⟩ := axisData h i hne hbot hKP hnab i
  obtain ⟨hWV, hWc, hUW, hWU, hW1, hV3⟩ := nontrivial_data h i hne hbot
  have hK : Nat.card K = 2 ^ n := hd.card_K
  have hV3' : Nat.card (𝐕[i, i].subgroupOf 𝐇𝐭[i]) = (2 ^ n) ^ 3 := hV3.trans (by rw [hK])
  have hc := hd.nontrivialAxisConclusion hWV hWc hUW hWU hW1 hV3'
  have hVC : 𝐕[i, i].subgroupOf 𝐇𝐭[i] ⊓ centralizer ({⟨t, htH⟩} : Set ↥𝐇𝐭[i]) ≤
      𝐔[i].subgroupOf 𝐇𝐭[i] := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at hx1 ⊢
    have hxt : (x : G) ∈ 𝐂 := by
      rw [mem_centralizer_singleton_iff] at hx2 ⊢
      exact congrArg Subtype.val hx2
    rw [← V_inf_C h i hne hbot]
    exact mem_inf.2 ⟨hx1, hxt⟩
  obtain ⟨-, -, hm, -⟩ := hd.nontrivialModel hSel hVC hV3' hc
  have h4' := hd.pow_four_eq_one_of_model hm
  have h4 : ∀ v ∈ 𝐕[i, i], v ^ 4 = 1 := fun v hv =>
    congrArg Subtype.val (h4' ⟨v, (mem_inf.1 hv).2⟩ (mem_subgroupOf.2 hv))
  obtain ⟨hWc', lam, -, huniq, -, hlamne⟩ := square_map h i
  have hl : (1 : K) = lam := huniq 1 (W_sq_eq' h i hne hbot)
  obtain ⟨hclW, -, -, -⟩ := hlamne (hl ▸ one_ne_zero)
  have hWcard : Nat.card 𝐖[i] = Nat.card 𝐔[i] * Nat.card 𝐔[i] := by
    rw [card_W h i, card_U φ i, sq]
  intro v hv
  have hv2W : v * v ∈ 𝐖[i] := closure_sq_V_le h i hne hbot (subset_closure ⟨v, hv, rfl⟩)
  refine mem_of_sq_eq_one hWc' hclW (fun w hw => h4 w (W_le_V h i hne hbot i hw)) hWcard hv2W ?_
  have := h4 v hv
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 by norm_num, pow_add, pow_add, pow_add, pow_one] at this
  rw [← this]
  group


theorem sq_M_mem_U (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector
      fun D _ => CFSG.Blueprint.Catalog D)
    [IsSimpleGroup G] (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i] := by
  intro x hx
  rw [← V_sup_W_swap h i hne hbot] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute fun x hx y hy =>
    V_comm_W_swap h i hne hbot hx hy).mp hx
  have hab : a * b = b * a := V_comm_W_swap h i hne hbot ha hb
  have e : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
  rw [e, sq_W_swap h i hne hbot hb, mul_one]
  exact sq_V_mem_U hSel h i hne hbot hKP hnab a ha

end Squares

end LocalSixE

end CFSG.LocalAnalysis.SymplecticFourStandard
