module

public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.Quasithin.Background.A318PSp4
public import CFSG.Quasithin.Background.A318PG2
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace A6E9

theorem mul_pow_three_of_central {G : Type*} [Group G] {s t : G}
    (hk : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center G) (ht : t ^ 3 ∈ Subgroup.center G) :
    (s * t) ^ 3 = s ^ 3 * t ^ 3 := by
  set c := (s * t * s⁻¹ * t⁻¹)⁻¹ with hcdef
  have hc : ∀ x : G, x * c = c * x := fun x =>
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hk) x
  have htc : ∀ x : G, x * t ^ 3 = t ^ 3 * x := fun x => Subgroup.mem_center_iff.mp ht x
  have hcomm : ∀ x y : G, x * (c * y) = c * (x * y) := fun x y => by
    rw [← mul_assoc, hc x, mul_assoc]
  have hts : t * s = c * (s * t) := by rw [hcdef]; group
  have hst : s * t * s⁻¹ = c⁻¹ * t := by rw [hcdef]; group
  have hc3 : c ^ 3 = 1 := by
    have h1 : s * t ^ 3 * s⁻¹ = (c⁻¹ * t) ^ 3 := by rw [← hst, conj_pow]
    have h2 : (c⁻¹ * t) ^ 3 = c⁻¹ ^ 3 * t ^ 3 :=
      Commute.mul_pow (Commute.inv_left (hc t).symm) 3
    have h3 : s * t ^ 3 * s⁻¹ = t ^ 3 := by rw [htc s]; group
    have h4 : c⁻¹ ^ 3 * t ^ 3 = t ^ 3 := by rw [← h2, ← h1, h3]
    have h5 : c⁻¹ ^ 3 = 1 := by
      calc c⁻¹ ^ 3 = c⁻¹ ^ 3 * t ^ 3 * (t ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4]; group
    rw [inv_pow] at h5
    exact inv_eq_one.mp h5
  calc (s * t) ^ 3 = s * (t * s) * (t * s) * t := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = s * (c * (s * t)) * (c * (s * t)) * t := by rw [hts]
    _ = c * c * (s * s * (t * s) * t * t) := by
        simp only [mul_assoc, hcomm]
    _ = c * c * (s * s * (c * (s * t)) * t * t) := by rw [hts]
    _ = c ^ 3 * (s ^ 3 * t ^ 3) := by
        simp only [mul_assoc, hcomm, pow_succ, pow_zero, one_mul]
    _ = s ^ 3 * t ^ 3 := by rw [hc3, one_mul]

theorem exists_nine_of_quotient {Q : Type} [Group Q] [Finite Q] {Z : Subgroup Q} [Z.Normal]
    (hZ : Z ≤ Subgroup.center Q) {E : Subgroup (Q ⧸ Z)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) : ∃ F : Subgroup Q, IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' Z with hπ
  set P := E.comap π with hP
  have hEc := hE.1
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Q := by
    intro x hx y hy
    apply hZ
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    have hxy : π x * π y = π y * π x :=
      setLike_mul_comm (show π x ∈ E from hx) (show π y ∈ E from hy)
    rw [← hπ, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
    group
  have hP3 : ∀ x ∈ P, x ^ 3 ∈ Z := by
    intro x hx
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_pow]
    exact hE.2 _ hx
  let f : ↥P →* ↥P :=
    { toFun := fun x => x ^ 3
      map_one' := one_pow 3
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
        exact mul_pow_three_of_central (hPc x x.2 y y.2) (hZ (hP3 y y.2))) }
  have hf : ∀ x : ↥P, f x = x ^ 3 := fun _ => rfl
  have hZP : Z ≤ P := fun z hz => by
    show π z ∈ E
    have : π z = 1 := by
      rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']; exact hz
    rw [this]; exact E.one_mem
  have hidx : P.index = E.index :=
    Subgroup.index_comap_of_surjective E (QuotientGroup.mk'_surjective Z)
  have h1 := P.card_mul_index
  have h2 := E.card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hEi : 0 < E.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hcardP : Nat.card P = 9 * Nat.card Z := by
    rw [hidx] at h1
    have : Nat.card P * E.index = 9 * Nat.card Z * E.index := by
      rw [h1, h3, ← h2, hcard]; ring
    exact Nat.eq_of_mul_eq_mul_right hEi this
  have hrange : Nat.card f.range ≤ Nat.card Z := by
    have hle : f.range ≤ Z.subgroupOf P := by
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_subgroupOf, hf, SubgroupClass.coe_pow]
      exact hP3 x x.2
    calc Nat.card f.range ≤ Nat.card (Z.subgroupOf P) := Subgroup.card_le_of_le hle
      _ = Nat.card Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hker : 9 ≤ Nat.card f.ker := by
    have hk := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hcardP] at hk
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have : 9 * Nat.card f.range ≤ Nat.card f.range * Nat.card f.ker := by
      rw [← hk]; exact Nat.mul_le_mul_left 9 hrange
    rw [mul_comm (Nat.card f.range)] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have hpg : IsPGroup 3 ↥f.ker := fun g => ⟨1, Subtype.ext (by
    have := g.2
    rw [MonoidHom.mem_ker, hf] at this
    simpa using this)⟩
  obtain ⟨H, -, hH⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card Nat.prime_three hpg
    (H := ⊤) (n := 2) (by rw [Subgroup.card_top]; norm_num; exact hker)
  refine ⟨(H.map f.ker.subtype).map P.subtype, ?_, ?_⟩
  · have hHc : IsMulCommutative ↥H := IsPGroup.isMulCommutative_of_card_eq_prime_sq hH
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
      obtain ⟨a'', ha'', rfl⟩ := Subgroup.mem_map.1 ha'
      obtain ⟨b'', hb'', rfl⟩ := Subgroup.mem_map.1 hb'
      have h0 : a'' * b'' = b'' * a'' := setLike_mul_comm ha'' hb''
      have h := congrArg (fun z : ↥f.ker => ((z : ↥P) : Q)) h0
      simp only [Subgroup.coe_mul] at h
      show (a : Q) * b = b * a
      rw [← ha, ← hb]
      exact h
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.1 hy
      have := z.2
      rw [MonoidHom.mem_ker, hf] at this
      simpa using congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective f.ker.subtype_injective, hH]
    norm_num

theorem isElemAbelian_three_of_forall {G : Type*} [Group G] {E : Subgroup G}
    (hc : ∀ a b : E, a * b = b * a) (h3 : ∀ x ∈ E, x ^ 3 = 1) : IsElemAbelian 3 E :=
  ⟨⟨⟨hc⟩⟩, h3⟩

theorem exists_nine_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ F : Subgroup X, IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  obtain ⟨E, hE, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
    have := hE.1
    have h1 : a' * b' = b' * a' := setLike_mul_comm ha' hb'
    show (a : X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, h1]
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x' hx', map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h := Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := m)
  rw [one_pow] at h
  rw [← two_mul, pow_mul]
  simpa using h

theorem exists_cube_root {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have hu : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hu
  refine ⟨g, ?_, ?_⟩
  · have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa using congrArg Units.val this
  · intro h1
    have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)

theorem exists_nine_sp4 {X : Type} [Group X] {n : ℕ} (h : IsPSp4 2 n X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨E, hE9, hEel, -⟩ := A318P.exists_nine_sp4 (K := K) (RingEquiv.refl K)
  exact exists_nine_of_mulEquiv e ⟨E, hEel, hE9⟩

theorem exists_nine_g2
    {X : Type} [Group X] {n : ℕ} (h : IsG2 2 n X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  let ψ : X ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
        QuotientGroup.quotientBot)
  obtain ⟨E, hE9, hEel, -⟩ := A318P.exists_nine_g2 (K := K) (RingEquiv.refl K)
  exact exists_nine_of_mulEquiv ψ ⟨E, hEel, hE9⟩

theorem exists_nine_psl3 {X : Type} [Group X] {n : ℕ} (hn : Even n) (h : IsPSL 3 2 n X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root (K := K) (by rw [hK]; exact three_dvd_two_pow_sub_one hn)
  let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 K))
  obtain ⟨E, hE9, hEc, hE3, -⟩ := A318P.exists_nine_projectiveSL hω hω1 (RingEquiv.refl K) rfl
  exact exists_nine_of_mulEquiv e' ⟨E, isElemAbelian_three_of_forall hEc hE3, hE9⟩

theorem exists_nine_psu3 {X : Type} [Group X] {n : ℕ} (hn : Odd n) (h : IsPSU 3 2 n X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨⟨-, hn1, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hKU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
  have h3 : 3 ∣ 2 ^ n + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow 2 1 hn
    simpa using this
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK, ← pow_mul, mul_comm, pow_mul]
    have h := Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := n)
    rw [one_pow] at h
    simpa using h
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root h3K
  let e' : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hKU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hKU (by norm_num)).symm
  obtain ⟨E, hE9, hEc, hE3, -⟩ := A318P.exists_nine_psu hKU h3 hω hω1 (RingEquiv.refl K) rfl
  exact exists_nine_of_mulEquiv e' ⟨E, isElemAbelian_three_of_forall hEc hE3, hE9⟩

theorem exists_nine_of_rank_two
    {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (h : IsPSp4 2 n (Q ⧸ Subgroup.center Q) ∨ IsG2 2 n (Q ⧸ Subgroup.center Q) ∨
      (Even n ∧ IsPSL 3 2 n (Q ⧸ Subgroup.center Q)) ∨
      (Odd n ∧ IsPSU 3 2 n (Q ⧸ Subgroup.center Q))) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hq : ∃ E : Subgroup (Q ⧸ Subgroup.center Q), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    rcases h with h | h | ⟨hn, h⟩ | ⟨hn, h⟩
    · exact exists_nine_sp4 h
    · exact exists_nine_g2 h
    · exact exists_nine_psl3 hn h
    · exact exists_nine_psu3 hn h
  obtain ⟨E, hE, hcard⟩ := hq
  exact exists_nine_of_quotient le_rfl hE hcard

end A6E9

end CFSG.Quasithin.H13.A6
