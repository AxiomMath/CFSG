module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Steps

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_commutator_of_isPGroup {p : ℕ} (hp : p.Prime) {T N : Subgroup G}
    (hT : IsPGroup p T) (hNT : N ≤ T) (h : T ≤ N ⊔ ⁅T, T⁆) : T ≤ N := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p ↥T) := ⟨hT⟩
  set H : Subgroup ↥T := N.subgroupOf T with hH
  have hmap : (H ⊔ _root_.commutator ↥T).map T.subtype = N ⊔ ⁅T, T⁆ := by
    rw [Subgroup.map_sup, hH, Subgroup.map_subgroupOf_eq_of_le hNT, _root_.commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : H ⊔ _root_.commutator ↥T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ (H ⊔ _root_.commutator ↥T).map T.subtype := hmap ▸ h x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  have htop' : H ⊔ frattini ↥T = ⊤ :=
    eq_top_iff.mpr (htop.symm.le.trans
      (sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := p)) _))
  have hHtop : H = ⊤ := CFSG.lemma_1_7_a (p := p) H htop'
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥T) ∈ H := hHtop ▸ Subgroup.mem_top _
  exact hmem

omit [Finite G] in
theorem pow_three_of_mem_zpowers {a : G} (ha3 : a ^ 3 = 1) :
    ∀ x ∈ Subgroup.zpowers a, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]

theorem fpf_of_eq_commutator {U : Subgroup G} {a : G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) (ha3 : a ^ 3 = 1) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hUa : U = ⁅U, Subgroup.zpowers a⁆) : ∀ u ∈ U, a * u * a⁻¹ = u → u = 1 := by
  have hmem : U ∈ fourGroupsMinus (Subgroup.zpowers a) :=
    ⟨mem_fourGroups_iff.mpr ⟨Subgroup.zpowers_le.mpr haU, hU, hU4⟩, hUa⟩
  obtain ⟨b, hb, hfpf⟩ :=
    HeadProof.exists_fpf_of_fourGroupsMinus (pow_three_of_mem_zpowers ha3) hmem
  intro u hu hau
  apply hfpf u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : Commute a u := by
    change a * u = u * a
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [hau]
  rw [(hc.zpow_left k).eq]
  group

theorem fourGroup_facts {U : Subgroup G} {a : G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) (ha3 : a ^ 3 = 1) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hUa : U = ⁅U, Subgroup.zpowers a⁆) {v : G} (hv : v ∈ U) (hv1 : v ≠ 1) :
    a * v * a⁻¹ ∈ U ∧ a * v * a⁻¹ ≠ 1 ∧
      (∀ u ∈ U, u = 1 ∨ u = v ∨ u = a * v * a⁻¹ ∨ u = v * (a * v * a⁻¹)) ∧
      v * v = 1 ∧ (a * v * a⁻¹) * (a * v * a⁻¹) = 1 ∧
      v * (a * v * a⁻¹) = (a * v * a⁻¹) * v ∧ v * (a * v * a⁻¹) ≠ 1 ∧
      a⁻¹ * v * a = v * (a * v * a⁻¹) ∧
      a * (a * v * a⁻¹) * a⁻¹ = v * (a * v * a⁻¹) := by
  have hfpf := fpf_of_eq_commutator hU hU4 ha3 haU hUa
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU2 : ∀ x ∈ U, x * x = 1 := fun x hx => by rw [← sq]; exact hU.2 x hx
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hU2 x hx)
  set w := a * v * a⁻¹ with hw
  have hwU : w ∈ U := (Subgroup.mem_normalizer_iff.mp haU v).mp hv
  have hw1 : w ≠ 1 := fun h => hv1 (by
    have : v = a⁻¹ * w * a := by rw [hw]; group
    rw [this, h]
    group)
  have hvw : v ≠ w := fun h => hv1 (hfpf v hv h.symm)
  have hvwU : v * w ∈ U := U.mul_mem hv hwU
  have hvw1 : v * w ≠ 1 := fun h => hvw (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, hinv w hwU])
  have hvwv : v * w ≠ v := fun h => hw1 (by
    have := congrArg (v⁻¹ * ·) h
    simpa using this)
  have hvww : v * w ≠ w := fun h => hv1 (by
    have := congrArg (· * w⁻¹) h
    simpa using this)
  have hall : ∀ u ∈ U, u = 1 ∨ u = v ∨ u = w ∨ u = v * w :=
    HeadProof.mem_of_card_four hU4 U.one_mem hv hwU hvwU (Ne.symm hv1) (Ne.symm hw1)
      (Ne.symm hvw1) hvw (Ne.symm hvwv) (Ne.symm hvww)
  have ha2 : a * a = a⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_three', ha3]
  have hinvconj : a⁻¹ * v * a = v * w := by
    have hmemU : a⁻¹ * v * a ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem haU) v).mp hv
      simpa [mul_assoc] using this
    rcases hall _ hmemU with h | h | h | h
    · exact absurd (by rw [show v = a * (a⁻¹ * v * a) * a⁻¹ by group, h]; group) hv1
    · exact absurd (hfpf v hv (by
        calc a * v * a⁻¹ = a * (a⁻¹ * v * a) * a⁻¹ := by rw [h]
          _ = v := by group)) hv1
    ·
      exfalso
      rw [hw] at h
      have h2 : v = a⁻¹ * v * a := by
        calc v = a * (a⁻¹ * v * a) * a⁻¹ := by group
          _ = a * (a * v * a⁻¹) * a⁻¹ := by rw [h]
          _ = (a * a) * v * (a * a)⁻¹ := by group
          _ = a⁻¹ * v * a := by rw [ha2, inv_inv]
      exact hv1 (hfpf v hv (by
        calc a * v * a⁻¹ = a * (a⁻¹ * v * a) * a⁻¹ := by rw [← h2]
          _ = v := by group))
    · exact h
  have hconjw : a * w * a⁻¹ = v * w := by
    have h1 : a * w * a⁻¹ = a⁻¹ * v * a := by
      have ha2' : a⁻¹ * a⁻¹ = a := by
        rw [← mul_inv_rev, ha2, inv_inv]
      calc a * w * a⁻¹ = (a * a) * v * (a⁻¹ * a⁻¹) := by rw [hw]; group
        _ = a⁻¹ * v * a := by rw [ha2, ha2']
    rw [h1, hinvconj]
  exact ⟨hwU, hw1, hall, hU2 v hv, hU2 w hwU, hUc v hv w hwU, hvw1, hinvconj, hconjw⟩

section Ab

variable (Z : Subgroup G)

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G))
    (z : Z) : g * (z : G) * g⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp hg z).mp z.2

noncomputable def conjAb {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) :
    Abelianization Z →* Abelianization Z :=
  Abelianization.map (Z.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom

variable {Z}

omit [Finite G] in
theorem conjAb_of {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) (z : Z) :
    conjAb Z hg (Abelianization.of z) =
      Abelianization.of ⟨g * (z : G) * g⁻¹, conj_mem_of_mem_normalizer Z hg z⟩ := by
  rw [conjAb, Abelianization.map_of]
  congr 1

omit [Finite G] in
theorem exists_of_eq (x : Abelianization Z) : ∃ z : Z, Abelianization.of z = x :=
  QuotientGroup.mk_surjective x

omit [Finite G] in
theorem conjAb_mul_apply {g h : G} (hg : g ∈ Subgroup.normalizer (Z : Set G))
    (hh : h ∈ Subgroup.normalizer (Z : Set G)) (x : Abelianization Z) :
    conjAb Z (mul_mem hg hh) x = conjAb Z hg (conjAb Z hh x) := by
  obtain ⟨z, rfl⟩ := exists_of_eq x
  rw [conjAb_of, conjAb_of, conjAb_of]
  congr 1
  exact Subtype.ext (by simp only [mul_inv_rev]; group)

omit [Finite G] in
theorem conjAb_congr {g h : G} (hgh : g = h) (hg : g ∈ Subgroup.normalizer (Z : Set G))
    (hh : h ∈ Subgroup.normalizer (Z : Set G)) (x : Abelianization Z) :
    conjAb Z hg x = conjAb Z hh x := by
  subst hgh
  rfl

omit [Finite G] in
theorem conjAb_one_apply (h1 : (1 : G) ∈ Subgroup.normalizer (Z : Set G))
    (x : Abelianization Z) : conjAb Z h1 x = x := by
  obtain ⟨z, rfl⟩ := exists_of_eq x
  rw [conjAb_of]
  congr 1
  exact Subtype.ext (by simp)

omit [Finite G] in
theorem conjAb_eq_comp {g g' g'' : G} (hgg : g = g' * g'')
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) (hg' : g' ∈ Subgroup.normalizer (Z : Set G))
    (hg'' : g'' ∈ Subgroup.normalizer (Z : Set G)) (x : Abelianization Z) :
    conjAb Z hg x = conjAb Z hg' (conjAb Z hg'' x) := by
  rw [conjAb_congr hgg hg (mul_mem hg' hg''), conjAb_mul_apply]

omit [Finite G] in
theorem conjAb_comm_rel {g h g' h' : G} (hrel : g * h = h' * g')
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) (hh : h ∈ Subgroup.normalizer (Z : Set G))
    (hg' : g' ∈ Subgroup.normalizer (Z : Set G)) (hh' : h' ∈ Subgroup.normalizer (Z : Set G))
    (x : Abelianization Z) : conjAb Z hg (conjAb Z hh x) = conjAb Z hh' (conjAb Z hg' x) := by
  rw [← conjAb_eq_comp rfl (mul_mem hg hh), ← conjAb_eq_comp rfl (mul_mem hh' hg'),
    conjAb_congr hrel]

omit [Finite G] in
theorem eq_one_of_sq_eq_one_of_odd (hZ : Odd (Nat.card Z)) {x : Abelianization Z}
    (hx : x * x = 1) : x = 1 := by
  have hdvd : Nat.card (Abelianization Z) ∣ Nat.card Z := by
    change Nat.card (Z ⧸ _root_.commutator Z) ∣ Nat.card Z
    exact Subgroup.card_quotient_dvd_card _
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
  have h2 : orderOf x ∣ Nat.card Z := (orderOf_dvd_natCard x).trans hdvd
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card Z) := Nat.dvd_gcd h1 h2
  have hg : Nat.gcd 2 (Nat.card Z) = 1 :=
    (Nat.coprime_comm.mp (Nat.Coprime.symm (Nat.coprime_two_left.mpr hZ)))
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

end Ab

omit [Finite G] in
theorem norm_eq_one {Z U : Subgroup G} (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hZU : Z = ⁅Z, U⁆) {v w : G} (hv : v ∈ U) (hw : w ∈ U)
    (hall : ∀ u ∈ U, u = 1 ∨ u = v ∨ u = w ∨ u = v * w) (hvv : v * v = 1) (hww : w * w = 1)
    (hvw : v * w = w * v) (x : Abelianization Z) :
    x * conjAb Z (hUZ hv) x * conjAb Z (hUZ hw) x * conjAb Z (hUZ (U.mul_mem hv hw)) x = 1 := by
  set σv := conjAb Z (hUZ hv) with hσv
  set σw := conjAb Z (hUZ hw) with hσw
  set σvw := conjAb Z (hUZ (U.mul_mem hv hw)) with hσvw
  set ν : Abelianization Z →* Abelianization Z := MonoidHom.id _ * σv * σw * σvw with hν
  have hνapp : ∀ y, ν y = y * σv y * σw y * σvw y := fun y => rfl
  have h1 : (1 : G) ∈ Subgroup.normalizer (Z : Set G) := one_mem _
  have hvv' : ∀ y, σv (σv y) = y := fun y => by
    rw [hσv, ← conjAb_eq_comp (g := 1) hvv.symm h1, conjAb_one_apply]
  have hww' : ∀ y, σw (σw y) = y := fun y => by
    rw [hσw, ← conjAb_eq_comp (g := 1) hww.symm h1, conjAb_one_apply]
  have hvw1 : ∀ y, σv (σw y) = σvw y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp rfl]
  have hwv1 : ∀ y, σw (σv y) = σvw y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp hvw]
  have hvvw : ∀ y, σv (σvw y) = σw y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp (g := w) (by rw [← mul_assoc, hvv, one_mul])]
  have hwvw : ∀ y, σw (σvw y) = σv y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp (g := v)
      (by rw [hvw, ← mul_assoc, hww, one_mul])]
  have hvwv : ∀ y, σvw (σv y) = σw y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp (g := w) (by rw [hvw, mul_assoc, hvv, mul_one])]
  have hvww : ∀ y, σvw (σw y) = σv y := fun y => by
    rw [hσv, hσw, hσvw, ← conjAb_eq_comp (g := v) (by rw [mul_assoc, hww, mul_one])]
  have hvwvw : ∀ y, σvw (σvw y) = y := fun y => by
    rw [hσvw, ← conjAb_eq_comp (g := 1)
      (by rw [show v * w * (v * w) = v * (w * v) * w by group, ← hvw,
        show v * (v * w) * w = (v * v) * (w * w) by group, hvv, hww, one_mul]) h1,
      conjAb_one_apply]
  have hinvar : ∀ u (hu : u ∈ U) y, ν (conjAb Z (hUZ hu) y) = ν y := by
    intro u hu y
    rcases hall u hu with rfl | rfl | rfl | rfl
    · rw [conjAb_one_apply]
    · rw [hνapp, hνapp, ← hσv, hvv', hwv1, hvwv]
      simp only [mul_comm, mul_left_comm]
    · rw [hνapp, hνapp, ← hσw, hvw1, hww', hvww]
      simp only [mul_comm, mul_left_comm]
    · rw [hνapp, hνapp, ← hσvw, hvvw, hwvw, hvwvw]
      simp only [mul_comm, mul_left_comm]
  set W : Subgroup G := ((ν.comp Abelianization.of).ker).map Z.subtype with hW
  have hcomm : ⁅Z, U⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro z hz u hu
    have hcz : ⁅z, u⁆ = z * (u * z⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    have hmem : ⁅z, u⁆ ∈ Z := by
      rw [hcz]
      exact mul_mem hz ((Subgroup.mem_normalizer_iff.mp (hUZ hu) _).mp (inv_mem hz))
    refine ⟨⟨⁅z, u⁆, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hsplit : Abelianization.of (⟨⁅z, u⁆, hmem⟩ : Z) =
        Abelianization.of (⟨z, hz⟩ : Z) * (conjAb Z (hUZ hu) (Abelianization.of ⟨z, hz⟩))⁻¹ := by
      rw [conjAb_of, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcz]; group)
    rw [hsplit, map_mul, map_inv, hinvar u hu, mul_inv_cancel]
  obtain ⟨z, rfl⟩ := exists_of_eq x
  have hz : (z : G) ∈ W := hZU.le.trans hcomm z.2
  obtain ⟨z', hz', hzz'⟩ := hz
  obtain rfl : z' = z := Subtype.ext hzz'
  exact hz'

theorem exists_lift_of_conjAb_eq {Z : Subgroup G} {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hZ : IsPGroup p Z) {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) (hg3 : g ^ 3 = 1)
    {x : Abelianization Z} (hx : conjAb Z hg x = x) :
    ∃ t : Z, g * (t : G) * g⁻¹ = t ∧ Abelianization.of t = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  set A := Subgroup.zpowers g with hAdef
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := Subgroup.zpowers_le.mpr hg
  have hA3 : IsPGroup 3 A := Proof171.isPGroup_zpowers_of_pow_three hg3
  set α : A →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hAZ) with hα
  have hαapp : ∀ (b : A) (z : Z), ((α b z : Z) : G) = (b : G) * z * (b : G)⁻¹ := fun b z =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Z ⟨b, hAZ b.2⟩ z
  set N : Subgroup Z := _root_.commutator Z with hNdef
  have hNα : ∀ b : A, ∀ n ∈ N, α b n ∈ N := fun b n hn => by
    have hchar : N.Characteristic := inferInstance
    exact (Subgroup.characteristic_iff_map_le.mp hchar ((α b) : Z ≃* Z))
      (Subgroup.mem_map_of_mem _ hn)
  have hcop : ¬ 3 ∣ Nat.card N := by
    intro h3
    have hdvd : Nat.card N ∣ Nat.card Z := by
      rw [← Nat.card_congr (Subgroup.topEquiv (G := Z)).toEquiv]
      exact Subgroup.card_dvd_of_le le_top
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
    have : 3 ∣ p ^ n := hn ▸ h3.trans hdvd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow this)).symm
  have hgen : ∀ q : Z ⧸ N, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα
      ⟨g, Subgroup.mem_zpowers g⟩ q = conjAb Z hg q := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    change _ = conjAb Z hg (Abelianization.of z)
    rw [conjAb_of]
    change ((α ⟨g, Subgroup.mem_zpowers g⟩ z : Z) : Z ⧸ N) = _
    congr 1
  set x' : Z ⧸ N := x with hx'
  have hfix : x' ∈ {q : Z ⧸ N |
      ∀ b : A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα b q = q} := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hb : b = (⟨g, Subgroup.mem_zpowers g⟩ : A) ^ k := Subtype.ext (by simp [hk])
    have hstab : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα
        ⟨g, Subgroup.mem_zpowers g⟩ ∈ MulAction.stabilizer (MulAut (Z ⧸ N)) x' := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hgen]
      exact hx
    have hk' := zpow_mem hstab k
    rw [← map_zpow, ← hb, MulAction.mem_stabilizer_iff, MulAut.smul_def] at hk'
    exact hk'
  rw [CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hNα hcop] at hfix
  obtain ⟨t, ht, htx⟩ := hfix
  refine ⟨t, ?_, htx⟩
  have := congrArg Subtype.val (ht ⟨g, Subgroup.mem_zpowers g⟩)
  rw [hαapp] at this
  exact this

theorem sq_mem_of_mem_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {Z U : Subgroup G} {a : G} (hZ : IsPGroup p Z) (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) (ha3 : a ^ 3 = 1) (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (haZ : a ∈ Subgroup.normalizer (Z : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hUa : U = ⁅U, Subgroup.zpowers a⁆) (hZU : Z = ⁅Z, U⁆) {v : G} (hv : v ∈ U) (hv1 : v ≠ 1)
    {y : G} (hyZ : y ∈ Z) (hyv : v * y * v⁻¹ = y) :
    y * y ∈ (⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1),
      Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G)) ⊔ ⁅Z, Z⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hwU, hw1, hall, hvv, hww, hvw, hvw1, hinvconj, hconjw⟩ :=
    fourGroup_facts hU hU4 ha3 haU hUa hv hv1
  set w := a * v * a⁻¹ with hwdef
  have hodd : Odd (Nat.card Z) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  set T := ⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1), Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G)
    with hTdef
  have hvwU : v * w ∈ U := U.mul_mem hv hwU
  have hvN := hUZ hv
  have hwN := hUZ hwU
  have hvwN := hUZ hvwU
  set σv := conjAb Z hvN with hσv
  set σw := conjAb Z hwN with hσw
  set σvw := conjAb Z hvwN with hσvw
  set σa := conjAb Z haZ with hσa
  have hν := norm_eq_one hUZ hZU hv hwU hall hvv hww hvw
  set yb : Abelianization Z := Abelianization.of ⟨y, hyZ⟩ with hyb
  have hσvy : σv yb = yb := by
    rw [hσv, hyb, conjAb_of]
    congr 1
    exact Subtype.ext hyv
  have hwvw : ∀ x, σvw x = σw (σv x) := fun x => by
    rw [hσvw, hσw, hσv, ← conjAb_eq_comp hvw]
  have hσwy : σw yb = yb⁻¹ := by
    have h := hν yb
    rw [← hσv, ← hσw, ← hσvw, hσvy, hwvw, hσvy] at h
    have h' : (yb * σw yb) * (yb * σw yb) = 1 := by
      rw [← h]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    exact eq_inv_of_mul_eq_one_right (eq_one_of_sq_eq_one_of_odd hodd h')
  have hσvwy : σvw yb = yb⁻¹ := by rw [hwvw, hσvy, hσwy]
  set t := yb * σa yb * σa (σa yb) with htdef
  have h1N : (1 : G) ∈ Subgroup.normalizer (Z : Set G) := one_mem _
  have hσa3 : ∀ x, σa (σa (σa x)) = x := fun x => by
    rw [hσa, ← conjAb_eq_comp rfl (mul_mem haZ haZ) haZ haZ,
      ← conjAb_eq_comp rfl (mul_mem (mul_mem haZ haZ) haZ) (mul_mem haZ haZ) haZ,
      conjAb_congr (show a * a * a = 1 by rw [← pow_three', ha3]) _ h1N, conjAb_one_apply]
  have hσat : σa t = t := by
    rw [htdef, map_mul, map_mul, hσa3]
    simp only [mul_comm, mul_left_comm]
  have hva : ∀ x, σv (σa x) = σa (σvw x) := fun x =>
    conjAb_comm_rel (by rw [← hinvconj]; group) hvN haZ hvwN haZ x
  have hvwa : ∀ x, σvw (σa x) = σa (σw x) := fun x =>
    conjAb_comm_rel (by rw [← hconjw]; group) hvwN haZ hwN haZ x
  have hσvt : σv t = yb * (σa yb)⁻¹ * (σa (σa yb))⁻¹ := by
    rw [htdef, map_mul, map_mul, hσvy, hva, hσvwy, map_inv, hva, hvwa, hσwy, map_inv, map_inv]
  have htt : t * σv t = yb * yb := by
    rw [hσvt, htdef, mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_mul_mul_comm,
      mul_inv_cancel, mul_one]
  have hνt := hν t
  rw [← hσv, ← hσw, ← hσvw] at hνt
  have hyy : yb * yb = (σw t * σvw t)⁻¹ := by
    rw [← htt, eq_inv_iff_mul_eq_one, ← hνt]
    simp only [mul_assoc]
  have hconj3 : ∀ u : G, (u * a * u⁻¹) ^ 3 = 1 := fun u => by
    rw [conj_pow, ha3, mul_one, mul_inv_cancel]
  have hlift : ∀ u (hu : u ∈ U), u ≠ 1 → ∃ s : Z, s.1 ∈ T ∧
      Abelianization.of s = conjAb Z (hUZ hu) t := by
    intro u hu hu1
    have hguN : u * a * u⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
      mul_mem (mul_mem (hUZ hu) haZ) (inv_mem (hUZ hu))
    have hfix : conjAb Z hguN (conjAb Z (hUZ hu) t) = conjAb Z (hUZ hu) t := by
      rw [conjAb_comm_rel (show u * a * u⁻¹ * u = u * a by group) hguN (hUZ hu) haZ (hUZ hu),
        ← hσa, hσat]
    obtain ⟨s, hs, hst⟩ := exists_lift_of_conjAb_eq hp hp3 hZ hguN (hconj3 u) hfix
    have hle : Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G) ≤ T :=
      le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le hu1 le_rfl))
    refine ⟨s, hle ⟨s.2, ?_⟩, hst⟩
    show (s : G) ∈ Subgroup.centralizer ({u * a * u⁻¹} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (s : G) * (u * a * u⁻¹) = u * a * u⁻¹ * s * (u * a * u⁻¹)⁻¹ * (u * a * u⁻¹) := by
          rw [hs]
      _ = u * a * u⁻¹ * s := by group
  obtain ⟨s₁, hs₁T, hs₁⟩ := hlift w hwU hw1
  obtain ⟨s₂, hs₂T, hs₂⟩ := hlift (v * w) hvwU hvw1
  have hker : (⟨y, hyZ⟩ : Z) * ⟨y, hyZ⟩ * (s₁ * s₂) ∈ _root_.commutator Z := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_mul, map_mul, ← hyb, hs₁, hs₂,
      ← hσw, ← hσvw, hyy, inv_mul_cancel]
  have hmap : (_root_.commutator Z).map Z.subtype = ⁅Z, Z⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : y * y * (s₁ * s₂ : G) ∈ ⁅Z, Z⁆ := by
    rw [← hmap]
    exact ⟨_, hker, rfl⟩
  have hs : ((s₁ * s₂ : Z) : G) ∈ T := by
    rw [Subgroup.coe_mul]
    exact mul_mem hs₁T hs₂T
  have heq : y * y = y * y * (s₁ * s₂ : G) * ((s₁ * s₂ : Z) : G)⁻¹ := by
    rw [Subgroup.coe_mul]
    group
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left (inv_mem hs))

theorem le_iSup_inf_centralizer_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {Z U : Subgroup G} {a : G} (hZ : IsPGroup p Z) (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) (ha3 : a ^ 3 = 1) (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (haZ : a ∈ Subgroup.normalizer (Z : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hUa : U = ⁅U, Subgroup.zpowers a⁆) (hZU : Z = ⁅Z, U⁆) :
    Z ≤ ⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1), Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set T := ⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1), Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G)
    with hTdef
  have hTZ : T ≤ Z := iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hcop : Nat.Coprime 2 (Nat.card Z) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  refine le_of_le_sup_commutator_of_isPGroup hp hZ hTZ ?_
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_two hU (by rw [hU4]; norm_num) hUZ hcop
    fun v hv hv1 => ?_
  intro y hy
  have hyv : v * y * v⁻¹ = y := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hy.2, mul_inv_cancel_right]
  have hsq := sq_mem_of_mem_centralizer hp hp2 hp3 hZ hU hU4 ha3 hUZ haZ haU hUa hZU hv hv1 hy.1
    hyv
  obtain ⟨n, hn⟩ := hZ ⟨y, hy.1⟩
  have hyn : y ^ p ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine Proof171.mem_of_pow_mem_of_coprime (a := 2) (b := p ^ n)
    (Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))) ?_ hyn
  rw [sq]
  exact hsq

end CFSG.RankThree.PartTwo.Sec17.Proof171Steps
