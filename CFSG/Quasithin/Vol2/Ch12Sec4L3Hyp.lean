module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

namespace L3Hyp

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_fixV_zpowers {a : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite V] in
theorem smul_eq_self_iff {f : MulAut V} {U : Subgroup V} : f • U = U ↔ f ∈ stabSub U := by
  constructor
  · intro h u
    constructor
    · intro hu
      have h1 : f • u ∈ f • U := by
        rw [h]
        rw [MulAut.smul_def]
        exact hu
      exact Subgroup.smul_mem_pointwise_smul_iff.1 h1
    · intro hu
      have h1 := Subgroup.smul_mem_pointwise_smul u f U hu
      rw [h, MulAut.smul_def] at h1
      exact h1
  · intro h
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulAut.smul_def]
      exact (h y).2 hy
    · intro hx
      refine ⟨f⁻¹ x, (h (f⁻¹ x)).1 (by rw [MulAut.apply_inv_self]; exact hx), ?_⟩
      rw [MulAut.smul_def, MulAut.apply_inv_self]

theorem card_complements_le (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 4) {z : V} :
    Nat.card {U : Subgroup V // U.index = 2 ∧ z ∉ U} ≤ 8 := by
  classical
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hV2, ofMul_one]
  let φ : {U : Subgroup V // U.index = 2 ∧ z ∉ U} → (Additive V →ₗ[ZMod 2] ZMod 2) := fun U =>
    AddMonoidHom.toZModLinearMap 2
      ({ toFun := fun w => if Additive.toMul w ∈ U.1 then 0 else 1
         map_zero' := by simp [U.1.one_mem]
         map_add' := fun x y => by
          have h := Subgroup.mul_mem_iff_of_index_two U.2.1 (a := Additive.toMul x)
            (b := Additive.toMul y)
          rw [toMul_add]
          by_cases hx : Additive.toMul x ∈ U.1 <;> by_cases hy : Additive.toMul y ∈ U.1 <;>
            simp_all [show (1 : ZMod 2) + 1 = 0 from rfl] } : Additive V →+ ZMod 2)
  have hφ : ∀ U w, φ U w = if Additive.toMul w ∈ U.1 then 0 else 1 := fun _ _ => rfl
  have hφz : ∀ U, φ U (Additive.ofMul z) = 1 := fun U => by
    rw [hφ, toMul_ofMul, ite_eq_right U.2.2]
  have hφinj : Function.Injective φ := by
    intro U U' h
    apply Subtype.ext
    ext v
    have h1 := LinearMap.congr_fun h (Additive.ofMul v)
    rw [hφ, hφ, toMul_ofMul] at h1
    by_cases hv : v ∈ U.1 <;> by_cases hv' : v ∈ U'.1 <;> simp_all
  rcases isEmpty_or_nonempty {U : Subgroup V // U.index = 2 ∧ z ∉ U} with hE | hne
  · rw [Nat.card_of_isEmpty]
    norm_num
  obtain ⟨U₀⟩ := hne
  have : Finite (Additive V →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f : Additive V →ₗ[ZMod 2] ZMod 2 => (f : Additive V → ZMod 2))
      DFunLike.coe_injective
  set ev := LinearMap.applyₗ (R := ZMod 2) (M₂ := ZMod 2) (Additive.ofMul z) with hev
  have hfin : Module.finrank (ZMod 2) (Additive V) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive V) = 2 ^ 4 := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hdual : Module.finrank (ZMod 2) (Additive V →ₗ[ZMod 2] ZMod 2) = 4 := by
    rw [Module.finrank_linearMap, hfin, Module.finrank_self, mul_one]
  have hsurj : Function.Surjective ev := by
    intro c
    refine ⟨c • φ U₀, ?_⟩
    rw [hev, LinearMap.applyₗ_apply_apply, LinearMap.smul_apply, hφz, smul_eq_mul, mul_one]
  have hrange : Module.finrank (ZMod 2) (LinearMap.range ev) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker ev) = 3 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ev
    rw [hrange, hdual] at h1
    omega
  have hcardker : Nat.card ↥(LinearMap.ker ev) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hker, Nat.card_zmod]
    norm_num
  let ψ : {U : Subgroup V // U.index = 2 ∧ z ∉ U} → ↥(LinearMap.ker ev) := fun U =>
    ⟨φ U - φ U₀, by
      rw [LinearMap.mem_ker, hev, LinearMap.applyₗ_apply_apply, LinearMap.sub_apply, hφz, hφz,
        sub_self]⟩
  have hψinj : Function.Injective ψ := by
    intro U U' h
    have h1 := congrArg Subtype.val h
    exact hφinj (sub_left_injective h1)
  calc Nat.card {U : Subgroup V // U.index = 2 ∧ z ∉ U}
      ≤ Nat.card ↥(LinearMap.ker ev) := Nat.card_le_card_of_injective ψ hψinj
    _ = 8 := hcardker

theorem not_mem_stabSub_of_invol {a : MulAut V} {U : Subgroup V} {z : V}
    (hfix : Nat.card (fixV (Subgroup.zpowers a)) = 4)
    (hcomm : commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a))
    (hza : z ∈ fixV (Subgroup.zpowers a)) (hzU : z ∉ U) (hU : Nat.card U = 8)
    (ha : a ∈ stabSub U) : False := by
  have hUF : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) ≤ 2 := by
    have hne : U ⊓ fixV (Subgroup.zpowers a) ≠ fixV (Subgroup.zpowers a) := fun h => hzU (by
      rw [← h] at hza
      exact hza.1)
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le
      (inf_le_right : U ⊓ fixV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers a))
    have hk1 : k ≠ 1 := fun h1 => hne
      (Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hk, h1, mul_one])))
    rw [hfix] at hk
    have hk0 : k ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hk
      norm_num at hk
    have h2 : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) * 2 ≤ 4 := by
      rw [hk]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  let f : ↥U →* V :=
    { toFun := fun u => a u * (u : V)⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hrange : f.range ≤ U ⊓ fixV (Subgroup.zpowers a) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨U.mul_mem ((ha u).2 u.2) (U.inv_mem u.2), ?_⟩
    rw [← hcomm]
    exact Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, u, rfl⟩
  have hker : Nat.card f.ker ≤ Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) := by
    refine Nat.card_le_card_of_injective
      (fun u => ⟨((u : ↥U) : V), (u : ↥U).2, mem_fixV_zpowers.2 ?_⟩) ?_
    · exact mul_inv_eq_one.1 u.2
    · intro u v h
      have h1 : (((u : ↥U) : V)) = ((v : ↥U) : V) :=
        congrArg (fun w : ↥(U ⊓ fixV (Subgroup.zpowers a)) => (w : V)) h
      exact Subtype.ext (Subtype.ext h1)
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) :=
    Subgroup.card_le_of_le hrange
  have h3 : Nat.card f.ker * Nat.card f.range ≤ 2 * 2 :=
    Nat.mul_le_mul (hker.trans hUF) (h2.trans hUF)
  rw [h1, hU] at h3
  norm_num at h3

end L3Hyp

open L3Hyp

theorem l3HyperplaneFact1248 : L3HyperplaneFact1248 := by
  intro V _ _ hV2 hcard X hs hX hcomm hfix U hU hnot
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnat := binaryNaturalSL_of_card_sixteen hV2 hcard hs hX hcomm hfix
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card V = 16 := by rw [hcard]; norm_num
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcomm h16
  obtain ⟨-, -, -, hinv⟩ := B4_8_2 hV2 h16 hnat hind
  obtain ⟨z, hzX, hzU⟩ : ∃ z ∈ fixV X, z ∉ U := by
    by_contra h
    push Not at h
    exact hnot h
  have hUcard : Nat.card U = 8 := by
    have h1 := U.card_mul_index
    rw [hU, h16] at h1
    omega
  have hodd : ∀ U' : Subgroup V, Nat.card U' = 8 → z ∉ U' → ∀ a ∈ X, a ∈ stabSub U' →
      a ^ 2 = 1 → a = 1 := by
    intro U' hU' hzU' a haX ha ha2
    by_contra ha1
    obtain ⟨hc, hrk⟩ := hinv a haX ha1 ha2
    have hF : Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
      rw [card_eq_two_pow hV2, hrk]
      norm_num
    exact not_mem_stabSub_of_invol hF hc
      (fun g hg => hzX g ((Subgroup.zpowers_le.2 haX) hg)) hzU' hU' ha
  let _ : MulAction ↥X (Subgroup V) := MulAction.compHom (Subgroup V) X.subtype
  have hsmul : ∀ (g : ↥X) (W : Subgroup V), g • W = (g : MulAut V) • W := fun _ _ => rfl
  have horb : Nat.card (MulAction.orbit ↥X U) ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun W : MulAction.orbit ↥X U => (⟨W.1, ?_, ?_⟩ : {U' : Subgroup V // U'.index = 2 ∧
        z ∉ U'})) ?_) (card_complements_le hV2 hcard)
    · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 W.2
      rw [← hg, hsmul]
      have h1 := ((g : MulAut V) • U).card_mul_index
      rw [← Nat.card_congr (Subgroup.equivSMul (g : MulAut V) U).toEquiv, hUcard, h16] at h1
      omega
    · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 W.2
      rw [← hg, hsmul]
      intro hz
      obtain ⟨y, hy, hyz⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz
      rw [MulAut.smul_def] at hyz
      have hgz : (g : MulAut V) z = z := hzX g g.2
      have hyz' : y = z := (g : MulAut V).injective (hyz.trans hgz.symm)
      exact hzU (hyz' ▸ hy)
    · intro W W' h
      have h1 : (W : Subgroup V) = W' :=
        congrArg (fun x : {U' : Subgroup V // U'.index = 2 ∧ z ∉ U'} => x.1) h
      exact Subtype.ext h1
  have hstab : Nat.card (MulAction.stabilizer ↥X U) = Nat.card ↥(X ⊓ stabSub U) := by
    have h1 : MulAction.stabilizer ↥X U = (X ⊓ stabSub U).subgroupOf X := by
      ext g
      rw [MulAction.mem_stabilizer_iff, hsmul, smul_eq_self_iff, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hos : Nat.card (MulAction.orbit ↥X U) * Nat.card (MulAction.stabilizer ↥X U) =
      Nat.card ↥X := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥X U), mul_comm]
    exact (MulAction.stabilizer ↥X U).card_mul_index
  rw [hstab, hX] at hos
  have hodd' : ¬ 2 ∣ Nat.card ↥(X ⊓ stabSub U) := by
    intro h2
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ stabSub U)) 2 h2
    have ha1 : (a : MulAut V) ≠ 1 := fun h => by
      have : a = 1 := Subtype.ext h
      rw [this, orderOf_one] at ha
      norm_num at ha
    have ha2 : (a : MulAut V) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at ha
      rw [← ha, pow_orderOf_eq_one]
    exact ha1 (hodd U hUcard hzU a a.2.1 a.2.2 ha2)
  have : Nonempty (MulAction.orbit ↥X U) := ⟨⟨U, MulAction.mem_orbit_self U⟩⟩
  have horb1 : 0 < Nat.card (MulAction.orbit ↥X U) := Nat.card_pos
  have h21 : Nat.card ↥(X ⊓ stabSub U) = 21 := by
    generalize Nat.card (MulAction.orbit ↥X U) = o at hos horb horb1
    interval_cases o <;> omega
  have hNX : X ⊓ stabSub U < X := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    rw [h, hX] at h21
    norm_num at h21
  refine ⟨⟨hNX, fun K hK hKX => ?_⟩, ?_, ?_⟩
  · by_contra hKne
    have hd1 : 21 ∣ Nat.card K := h21 ▸ Subgroup.card_dvd_of_le hK.le
    have hd2 : Nat.card K ∣ 168 := hX ▸ Subgroup.card_dvd_of_le hKX
    have hlt : 21 < Nat.card K := h21 ▸ Subgroup.card_lt_of_lt hK
    have hne : Nat.card K ≠ 168 := fun h =>
      hKne (Subgroup.eq_of_le_of_card_ge hKX (le_of_eq (by rw [h, hX])))
    set K' := K.subgroupOf X with hK'
    have hcK' : Nat.card K' = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have hidx := K'.card_mul_index
    rw [hcK', hX] at hidx
    obtain ⟨m, hm⟩ := hd1
    obtain ⟨r, hr⟩ := hd2
    have hm8 : m ≤ 8 := by
      rw [hm, mul_assoc] at hr
      have h8 : m * r = 8 := by linarith
      exact Nat.le_of_dvd (by norm_num) (Dvd.intro r h8)
    have hcases : K'.index = 2 ∨ K'.index = 4 := by
      rw [hm] at hidx hlt hne
      interval_cases m <;> omega
    have hcore := IsSimpleGroup.eq_bot_or_eq_top_of_normal K'.normalCore
    rcases hcore with h | h
    · have h1 := K'.index_normalCore_dvd_factorial_index
      rw [h, Subgroup.index_bot, hX] at h1
      rcases hcases with h2 | h2 <;> rw [h2] at h1 <;> norm_num [Nat.factorial] at h1
    · have h1 : K' = ⊤ := eq_top_iff.2 (h ▸ K'.normalCore_le)
      rw [h1, Subgroup.index_top] at hidx
      omega
  ·
    have h1 := Subgroup.relIndex_mul_card (X ⊓ stabSub U) X
    rw [inf_eq_left.2 inf_le_left, h21, hX] at h1
    omega
  ·
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ stabSub U)) 3
      (by rw [h21]; norm_num)
    have hy3 : orderOf (y : MulAut V) = 3 := by rw [Subgroup.orderOf_coe, hy]
    refine ⟨Subgroup.zpowers (y : MulAut V), Subgroup.zpowers_le.2 y.2,
      by rw [Nat.card_zpowers, hy3], fun hle => ?_⟩
    have hyU : (y : MulAut V) ∈ centSub U := hle (Subgroup.mem_zpowers _)
    have hyz : (y : MulAut V) z = z := hzX y y.2.1
    have hy1 : (y : MulAut V) = 1 := by
      ext v
      rw [MulAut.one_apply]
      by_cases hv : v ∈ U
      · exact hyU v hv
      · have hzv : z⁻¹ * v ∈ U := by
          have hz' : z⁻¹ ∉ U := fun h => hzU (by simpa using h)
          exact (Subgroup.mul_mem_iff_of_index_two hU).2 (iff_of_false hz' hv)
        have h1 := hyU _ hzv
        rw [map_mul, map_inv, hyz] at h1
        calc (y : MulAut V) v = z * (z⁻¹ * (y : MulAut V) v) := by group
          _ = z * (z⁻¹ * v) := by rw [h1]
          _ = v := by group
    rw [hy1, orderOf_one] at hy3
    norm_num at hy3

theorem lemma12_4_8_of_g2
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h614 : ASInputs.AS_E_6_14) (hG2 : G2HyperplaneFact1248)
    (hchar : CharTwo1248) : Lemma12_4_8 :=
  lemma12_4_8_of h331 h1222 h323 hpre h3228 h614 l3HyperplaneFact1248 hG2 hchar

end CFSG.Quasithin.H13
