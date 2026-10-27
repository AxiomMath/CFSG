module

public import CFSG.Quasithin.Vol2.Ch11SecBK4A
public import CFSG.Quasithin.Vol2.Ch11SecBK7A
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

section Kinds

variable [IsMulCommutative ↥V]

theorem kindSL3_of_isCoord [Finite K] (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L V)} {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) : KindSL3 L V n :=
  ⟨K, inferInstance, inferInstance, hK,
    ⟨(MulEquiv.ofBijective π ⟨hf.injective_nat, hf.onto⟩).symm.trans
      (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩

theorem kindSp4_of_isCoord [Finite K] (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSp 2 K) →* ↥(autOn L V)} {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) : KindSp4 L V n :=
  ⟨K, inferInstance, inferInstance, hK,
    ⟨(MulEquiv.ofBijective π ⟨hf.injective_nat, hf.onto⟩).symm⟩⟩

theorem kindG2_of_isCoord [Finite K] [CharP K 2] (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) : KindG2 L V n := by
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  have hb : Function.Bijective π := by
    have h1 := (G2Q8.rhoG_bijective hf hc0 hc1).comp
      (MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1)).bijective
    exact h1
  exact ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hb).symm⟩⟩

end Kinds

theorem mem_centralizer_of_conjV_eq_one {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (h : SecA.conjV V x hxV = 1) : x ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun τ : MulAut ↥V => ((τ ⟨v, hv⟩ : ↥V) : G)) h
  simp only [SecA.conjV_apply_coe, MulAut.one_apply] at h1
  calc v * x = x * v * x⁻¹ * x := by rw [h1]
    _ = x * v := by group

variable [IsMulCommutative ↥V]

theorem commV_autOn_top (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) :
    commV (autOn L V) = ⊤ := by
  rw [Ch10.SecA.commV_autOn_eq hLV, hVL, Subgroup.subgroupOf_self]

theorem cV_le_fixV : (Subgroup.centralizer (L : Set G)).subgroupOf V ≤ fixV (autOn L V) :=
  fun z hz h hh => SecA.autOn_fixes_cV h hh z hz

theorem mem_centralizer_of_sl3 (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L V)} {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : ∀ v, f (SecA.conjV V x hxV v) = f v) : x ∈ Subgroup.centralizer (V : Set G) := by
  refine mem_centralizer_of_conjV_eq_one hxV (KGNat.eq_one_of_commV (commV_autOn_top hLV hVL)
    (KGNat.commute_of_trivial_mod hf (fun _ hh => G2Q8.conjV_mul_conjV_inv_mem hxL hxV hh) hx)
    fun w => cV_le_fixV ((hf.ker _).mp ?_))
  rw [hf.map_mul_inv, hx, sub_self]

theorem mem_centralizer_of_sp4 (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    {π : ↥(StatedSp 2 K) →* ↥(autOn L V)} {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : ∀ v, f (SecA.conjV V x hxV v) = f v) : x ∈ Subgroup.centralizer (V : Set G) :=
  mem_centralizer_of_conjV_eq_one hxV (K7.eq_one_of_modZ hf
    (fun h hh z hz => SecA.autOn_fixes_cV h hh z hz) (commV_autOn_top hLV hVL)
    (fun _ hh => G2Q8.conjV_mul_conjV_inv_mem hxL hxV hh) hx)

theorem mem_centralizer_of_g2 [CharP K 2] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ = V) {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)}
    {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hx : ∀ v, f (SecA.conjV V x hxV v) = f v) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  refine mem_centralizer_of_conjV_eq_one hxV (KGNat.eq_one_of_commV (commV_autOn_top hLV hVL)
    (G2Q8.commute_of_trivial_modG hf hc0 hc1
      (fun _ hh => G2Q8.conjV_mul_conjV_inv_mem hxL hxV hh) hx)
    fun w => cV_le_fixV ((hf.ker _).mp ?_))
  rw [hf.map_mul_inv, hx, sub_self]

omit [IsMulCommutative ↥V] in
theorem mem_fixV_zpowers {W : Type*} [CommGroup W] {τ : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers τ) ↔ τ w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem inf_centralizer_subgroupOf {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V =
      fixV (Subgroup.zpowers (SecA.conjV V x hxV)) := by
  ext v
  rw [Subgroup.mem_subgroupOf, mem_fixV_zpowers, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, h x rfl, mul_inv_cancel_right]
  · intro h
    refine ⟨v.2, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 := congrArg Subtype.val h
    rw [SecA.conjV_apply_coe] at h1
    calc y * (v : G) = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [h1]

theorem mQuot_inf_centralizer {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) =
      rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  rw [E3.mQuot_eq_rkIdx, inf_centralizer_subgroupOf]

omit [IsMulCommutative ↥V] in
theorem index_eq_two_pow [Finite G] (hV : IsElemAbelian 2 V) (C : Subgroup ↥V) :
    C.index = 2 ^ rkIdx C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥V := fun w => ⟨1, Subtype.ext (by simpa using hV.2 w w.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ C.index_dvd_card)
  rw [rkIdx, hj, padicValNat.prime_pow]

section Coord

variable {D : FFModel} {M : Type} [AddCommGroup M] [Module K M] {LM : KGNat.LinModel D K M}
  {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : D.Gam →* ↥H} {f : ↥V → M}

theorem le_rkIdx_add [Finite G] (hV : IsElemAbelian 2 V) (hf : KGNat.IsCoord LM H Z π f)
    {T : M →+ M} {C : Subgroup ↥V} (hC : ∀ w ∈ C, T (f w) = f w) {a b : ℕ} (hM : Nat.card M = 2 ^ a)
    (hT : Nat.card {x : M // T x = x} ≤ 2 ^ b) : a ≤ rkIdx C + b := by
  have h1 := BK4.card_le_index_mul hf hC
  rw [hM, index_eq_two_pow hV C] at h1
  have h2 : 2 ^ a ≤ 2 ^ (rkIdx C + b) := by
    rw [pow_add]
    exact h1.trans (Nat.mul_le_mul_left _ hT)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem mem_of_rkIdx_add_le [Finite G] (hV : IsElemAbelian 2 V)
    (hf : KGNat.IsCoord LM H Z π f) {T : M →+ M} {C : Subgroup ↥V}
    (hC : ∀ w ∈ C, T (f w) = f w) {a b : ℕ} (hM : Nat.card M = 2 ^ a)
    (hT : Nat.card {x : M // T x = x} ≤ 2 ^ b) (hle : rkIdx C + b ≤ a) {w : ↥V}
    (hw : T (f w) = f w) : w ∈ C := by
  refine BK4.mem_of_index_mul_le hf hC ?_ hw
  rw [hM, index_eq_two_pow hV C]
  calc 2 ^ rkIdx C * Nat.card {x : M // T x = x} ≤ 2 ^ rkIdx C * 2 ^ b :=
        Nat.mul_le_mul_left _ hT
    _ = 2 ^ (rkIdx C + b) := (pow_add _ _ _).symm
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hle

omit [IsMulCommutative ↥V] in
theorem index_preFix_mul {W : Type*} [CommGroup W] [Finite W] {H' : Subgroup (MulAut W)}
    {Z' : Subgroup W} {π' : D.Gam →* ↥H'} {f' : W → M} (hf : KGNat.IsCoord LM H' Z' π' f')
    (T : M →+ M) : (BK4.preFix hf T).index * Nat.card {x : M // T x = x} = Nat.card M := by
  have h1 := Subgroup.card_mul_index (BK4.preFix hf T)
  rw [BK4.card_preFix, BK4.card_eq_mul hf] at h1
  have hZ : 0 < Nat.card Z' := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hZ ?_
  rw [← h1]
  ring

theorem rkIdx_add_le [Finite G] (hV : IsElemAbelian 2 V) (hf : KGNat.IsCoord LM H Z π f)
    {T : M →+ M} {C : Subgroup ↥V} (hC : BK4.preFix hf T ≤ C) {a b : ℕ}
    (hM : Nat.card M = 2 ^ a) (hT : 2 ^ b ≤ Nat.card {x : M // T x = x}) : rkIdx C + b ≤ a := by
  have h1 := index_preFix_mul hf T
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hC)
  rw [index_eq_two_pow hV C] at h2
  have h3 : 2 ^ (rkIdx C + b) ≤ 2 ^ a := by
    rw [pow_add, ← hM, ← h1]
    exact Nat.mul_le_mul h2 hT
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

end Coord

omit [IsMulCommutative ↥V] in
theorem mParam_eq [Finite G] (hV : IsElemAbelian 2 V) {X : Subgroup G} {m : ℕ}
    (hlow : ∀ t ∈ autI hV X, orderOf t = 2 → m ≤ rkIdx (fixV (Subgroup.zpowers t)))
    (hup : ∃ t ∈ autI hV X, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) = m) :
    E3.mParam (autI hV X) = m := by
  obtain ⟨t, ht, ht2, htm⟩ := hup
  have heven : Even (Nat.card (autI hV X)) := by
    have h1 := orderOf_dvd_natCard (⟨t, ht⟩ : ↥(autI hV X))
    rw [Subgroup.orderOf_mk, ht2] at h1
    exact even_iff_two_dvd.mpr h1
  rw [E3.mParam, ite_eq_left_iff.mpr (fun h => absurd heven h)]
  refine le_antisymm (Nat.sInf_le ⟨t, ht, ht2, htm.symm⟩) (le_csInf ⟨_, t, ht, ht2, rfl⟩ ?_)
  rintro k ⟨s, hs, hs2, rfl⟩
  exact hlow s hs hs2

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
