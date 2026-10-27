module

import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_pow_three_pow_eq_one148 {N : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N))
    {x : G} (hx : x ∈ N) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have h2 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3 : Nat.Coprime (orderOf x) (Nat.card N) :=
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k hN)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h1)

omit [Finite G] in
theorem isPGroup_three_of_pow148 {B : Subgroup G} (hB : ∀ b ∈ B, b ^ 3 = 1) : IsPGroup 3 B :=
  fun b => ⟨1, Subtype.ext (by simpa using hB b b.2)⟩

theorem exists_commute_mem_coset148 {B N : Subgroup G} (hB3 : IsPGroup 3 B)
    (hN3 : Nat.Coprime 3 (Nat.card N)) (hBN : B ≤ Subgroup.normalizer (N : Set G)) {k : G}
    (hk : ∀ b ∈ B, k⁻¹ * (b * k * b⁻¹) ∈ N) :
    ∃ y : G, k⁻¹ * y ∈ N ∧ ∀ b ∈ B, b * y = y * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3' : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
  set α : B →* MulAut G := MulAut.conj.comp B.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB3 α N
    hN3' k).2 (by
      intro a x hx
      change k⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ N
      have h1 := hk a a.2
      have h2 : (a : G) * (k⁻¹ * x) * (a : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hBN a.2) _).mp hx
      have h3 := N.mul_mem h1 h2
      rwa [show k⁻¹ * ((a : G) * k * (a : G)⁻¹) * ((a : G) * (k⁻¹ * x) * (a : G)⁻¹) =
        k⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  refine ⟨y, hy, fun b hb => ?_⟩
  have h := hyfix ⟨b, hb⟩
  change b * y * b⁻¹ = y at h
  calc b * y = b * y * b⁻¹ * b := by group
    _ = y * b := by rw [h]

theorem exists_pow_three_part148 {y : G} :
    ∃ m k : ℕ, m % 3 = 1 ∧ (y ^ m) ^ 3 ^ k = 1 := by
  set n := orderOf y with hn
  have hn0 : n ≠ 0 := (orderOf_pos y).ne'
  set c := n / 3 ^ n.factorization 3 with hc
  have hcop : Nat.Coprime 3 c := Nat.coprime_ordCompl Nat.prime_three hn0
  have hc3 : c % 3 = 1 ∨ c % 3 = 2 := by
    have h0 : c % 3 ≠ 0 := by
      intro h
      have : 3 ∣ c := Nat.dvd_of_mod_eq_zero h
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop this) (by norm_num)
    omega
  refine ⟨c * c, n.factorization 3, ?_, ?_⟩
  · rcases hc3 with h | h <;> simp [Nat.mul_mod, h]
  · have hnc : 3 ^ n.factorization 3 * c = n := Nat.ordProj_mul_ordCompl_eq_self n 3
    rw [← pow_mul, show c * c * 3 ^ n.factorization 3 = n * c by
      calc c * c * 3 ^ n.factorization 3 = (3 ^ n.factorization 3 * c) * c := by ring
        _ = n * c := by rw [hnc], pow_mul, hn, pow_orderOf_eq_one, one_pow]

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem mem_img148_iff {X : Subgroup G} {x : ↥(Y ⊔ A) ⧸ ker148 A Y} :
    x ∈ img148 A Y X ↔ ∃ (g : G) (hg : g ∈ Y ⊔ A), g ∈ X ∧
      QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ = x := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, m.2, hm, rfl⟩
  · rintro ⟨g, hg, hgX, rfl⟩
    exact ⟨⟨g, hg⟩, hgX, rfl⟩

omit [Finite G] in
theorem mk'_ker148_eq_iff {g h : ↥(Y ⊔ A)} :
    QuotientGroup.mk' (ker148 A Y) g = QuotientGroup.mk' (ker148 A Y) h ↔
      (g : G)⁻¹ * h ∈ pPrimeCoreOf 3 Y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  simp [ker148, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem mk'_ker148_eq_one_iff {g : ↥(Y ⊔ A)} :
    QuotientGroup.mk' (ker148 A Y) g = 1 ↔ (g : G) ∈ pPrimeCoreOf 3 Y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  simp [ker148, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem alpha148_eq_mk' {a : G} (ha : a ∈ A) :
    alpha148 A Y a ha = QuotientGroup.mk' (ker148 A Y) ⟨a, Subgroup.mem_sup_right ha⟩ :=
  rfl

omit [Finite G] in
theorem alpha148_mem_img148 {a : G} (ha : a ∈ A) : alpha148 A Y a ha ∈ img148 A Y A :=
  mem_img148_iff.mpr ⟨a, Subgroup.mem_sup_right ha, ha, rfl⟩

omit [Finite G] in
theorem alpha148_mul {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    alpha148 A Y (a * b) (A.mul_mem ha hb) = alpha148 A Y a ha * alpha148 A Y b hb := by
  rw [alpha148_eq_mk', alpha148_eq_mk', alpha148_eq_mk', ← map_mul]
  rfl

omit [Finite G] in
theorem alpha148_pow {a : G} (ha : a ∈ A) (k : ℕ) :
    alpha148 A Y (a ^ k) (A.pow_mem ha k) = alpha148 A Y a ha ^ k := by
  rw [alpha148_eq_mk', alpha148_eq_mk', ← map_pow]
  rfl

omit [Finite G] in
theorem alpha148_inv {a : G} (ha : a ∈ A) :
    alpha148 A Y a⁻¹ (A.inv_mem ha) = (alpha148 A Y a ha)⁻¹ := by
  rw [alpha148_eq_mk', alpha148_eq_mk', ← map_inv]
  rfl

theorem alpha148_injective (hA3 : ∀ a ∈ A, a ^ 3 = 1) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : alpha148 A Y a ha = alpha148 A Y b hb) : a = b := by
  rw [alpha148_eq_mk', alpha148_eq_mk', mk'_ker148_eq_iff] at h
  have h1 : a⁻¹ * b = 1 := eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h
    (k := 1) (by rw [pow_one]; exact hA3 _ (A.mul_mem (A.inv_mem ha) hb))
  calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
    _ = b := by group

omit [Finite G] in
theorem img148_le_normalizer {S X : Subgroup G} (hSX : S ≤ Subgroup.normalizer (X : Set G)) :
    img148 A Y S ≤ Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  refine le_trans ?_ (Subgroup.le_normalizer_map (QuotientGroup.mk' (ker148 A Y)))
  refine Subgroup.map_mono fun m hm => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hmX := Subgroup.mem_normalizer_iff.mp (hSX (Subgroup.mem_subgroupOf.mp hm)) x
  simpa using hmX

omit [Finite G] in
theorem img148_sup {X X' : Subgroup G} (hX : X ≤ Y ⊔ A) (hX' : X' ≤ Y ⊔ A) :
    img148 A Y (X ⊔ X') = img148 A Y X ⊔ img148 A Y X' := by
  unfold img148
  rw [Subgroup.subgroupOf_sup hX hX', Subgroup.map_sup]

omit [Finite G] in
theorem img148_mono {X X' : Subgroup G} (h : X ≤ X') : img148 A Y X ≤ img148 A Y X' :=
  Subgroup.map_mono fun _ hm => h hm

omit [Finite G] in
theorem card_map_eq_of_ker148 {M Q : Type*} [Group M] [Group Q] {f : M →* Q} {S : Subgroup M}
    (h : ∀ x ∈ S, f x = 1 → x = 1) : Nat.card (S.map f) = Nat.card S := by
  have hinj : Function.Injective (f.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (h x x.2 hx)
  rw [← Subgroup.range_subtype S, ← MonoidHom.range_comp, Subgroup.range_subtype]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem img148_isE27 (hA : Late.IsE27 A) :
    CFSG.Assembly.IsElemAbelian 3 (img148 A Y A) ∧ Nat.card (img148 A Y A) = 27 := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, haA, rfl⟩ := mem_img148_iff.mp hx
    obtain ⟨b, hb, hbA, rfl⟩ := mem_img148_iff.mp hy
    apply Subtype.ext
    change QuotientGroup.mk' (ker148 A Y) ⟨a, ha⟩ * QuotientGroup.mk' (ker148 A Y) ⟨b, hb⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨b, hb⟩ * QuotientGroup.mk' (ker148 A Y) ⟨a, ha⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc a haA b hbA)
  · intro x hx
    obtain ⟨a, ha, haA, rfl⟩ := mem_img148_iff.mp hx
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a haA)
    rw [this, map_one]
  · rw [← hA.2]
    unfold img148
    rw [card_map_eq_of_ker148 fun x hx h1 => ?_]
    · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    · rw [mk'_ker148_eq_one_iff] at h1
      exact Subtype.ext (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1
        (k := 1) (by rw [pow_one]; exact hA3 _ (Subgroup.mem_subgroupOf.mp hx)))

theorem exists_alpha148_eq_of_mem_img148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {U : Subgroup G} (hUM : U ≤ Y ⊔ A)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) {x : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hx : x ∈ img148 A Y U)
    (hxA : ∀ (a : G) (ha : a ∈ A), alpha148 A Y a ha * x = x * alpha148 A Y a ha)
    (hx3 : x ^ 3 = 1) : ∃ (u : G) (hu : u ∈ A), u ∈ U ∧ alpha148 A Y u hu = x := by
  obtain ⟨j, hjM, hjU, rfl⟩ := mem_img148_iff.mp hx
  set N := pPrimeCoreOf 3 Y with hNdef
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hk : ∀ b ∈ A, j⁻¹ * (b * j * b⁻¹) ∈ N ⊓ U := by
    intro b hb
    refine ⟨?_, U.mul_mem (U.inv_mem hjU) ((Subgroup.mem_normalizer_iff.mp (hAU hb) j).mp hjU)⟩
    have hbjM : b * j * b⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem (Subgroup.mem_sup_right hb) hjM)
        ((Y ⊔ A).inv_mem (Subgroup.mem_sup_right hb))
    have h1 : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨b * j * b⁻¹, hbjM⟩ := by
      have e1 : QuotientGroup.mk' (ker148 A Y) ⟨b * j * b⁻¹, hbjM⟩ =
          alpha148 A Y b hb * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
            (alpha148 A Y b hb)⁻¹ := by
        rw [alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1, hxA b hb, mul_assoc, mul_inv_cancel, mul_one]
    exact mk'_ker148_eq_iff.mp h1
  have hNU3 : Nat.Coprime 3 (Nat.card ↥(N ⊓ U)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 Y)
  have hANU : A ≤ Subgroup.normalizer ((N ⊓ U : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAN ha, hAU ha⟩
  obtain ⟨y, hy, hyA⟩ := exists_commute_mem_coset148 (isPGroup_three_of_pow148 hA3) hNU3 hANU hk
  have hyU : y ∈ U := by
    have := U.mul_mem hjU hy.2
    rwa [mul_inv_cancel_left] at this
  have hyM : y ∈ Y ⊔ A := hUM hyU
  obtain ⟨m, k, hm, hv⟩ := exists_pow_three_part148 (y := y)
  have hvU : y ^ m ∈ U := U.pow_mem hyU m
  have hvM : y ^ m ∈ Y ⊔ A := hUM hvU
  have hαy : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ := mk'_ker148_eq_iff.mpr hy.1
  have hαv : QuotientGroup.mk' (ker148 A Y) ⟨y ^ m, hvM⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ := by
    have e1 : QuotientGroup.mk' (ker148 A Y) ⟨y ^ m, hvM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ ^ m := by
      rw [← map_pow]
      rfl
    rw [e1, ← hαy, ← Nat.div_add_mod m 3, hm, pow_add, pow_mul, hx3, one_pow, one_mul, pow_one]
  have hv3 : (y ^ m) ^ 3 = 1 := by
    have hv3M : (y ^ m) ^ 3 ∈ Y ⊔ A := (Y ⊔ A).pow_mem hvM 3
    have h1 : (y ^ m) ^ 3 ∈ N := by
      have : QuotientGroup.mk' (ker148 A Y) ⟨(y ^ m) ^ 3, hv3M⟩ = 1 := by
        rw [show (⟨(y ^ m) ^ 3, hv3M⟩ : ↥(Y ⊔ A)) = ⟨y ^ m, hvM⟩ ^ 3 from rfl, map_pow, hαv,
          hx3]
      exact mk'_ker148_eq_one_iff.mp this
    refine eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1 (k := k) ?_
    rw [← pow_mul, show 3 * 3 ^ k = 3 ^ k * 3 by ring, pow_mul, hv, one_pow]
  have hvA : ∀ a ∈ A, a * y ^ m = y ^ m * a := fun a ha => (Commute.pow_right (hyA a ha) m).eq
  have hvAm : y ^ m ∈ A :=
    Sec4.mem_of_maximal_of_commute ⟨hAF.1, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩ hv3 hvA
  exact ⟨y ^ m, hvAm, hvU, hαv⟩

theorem mem_img148_of_commute (hAF : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hxA : x ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hx3 : x ^ 3 = 1) : x ∈ img148 A Y A := by
  have hxA' : ∀ (a : G) (ha : a ∈ A), alpha148 A Y a ha * x = x * alpha148 A Y a ha :=
    fun a ha => Subgroup.mem_centralizer_iff.mp hxA _ (alpha148_mem_img148 ha)
  have hx : x ∈ img148 A Y (Y ⊔ A) := by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) x
    exact mem_img148_iff.mpr ⟨m, m.2, m.2, rfl⟩
  obtain ⟨u, hu, -, rfl⟩ := exists_alpha148_eq_of_mem_img148 hAF hAY le_rfl
    (le_sup_right.trans Subgroup.le_normalizer) hx hxA' hx3
  exact alpha148_mem_img148 hu

end Quot

@[expose] def InnerOn148 {Γ : Type*} [Group Γ] (X : Subgroup Γ) (g : Γ) : Prop :=
  ∃ x ∈ X, ∀ y ∈ X, g * y * g⁻¹ = x * y * x⁻¹

section Decomp

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem eq_zpowers_sup_inf_of_innerOn (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e : G} (he : e ∈ A)
    (hZ : Subgroup.center ↥(img148 A Y J) = ⊥)
    (hC : Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ⊆ (Subgroup.zpowers e : Set G))
    (hin : ∀ (a : G) (ha : a ∈ A), ∃ k : ℕ,
      InnerOn148 (img148 A Y J) (alpha148 A Y a ha * alpha148 A Y e he ^ k)) :
    A = Subgroup.zpowers e ⊔ (A ⊓ J) := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJn : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  refine le_antisymm (fun a ha => ?_) (sup_le (Subgroup.zpowers_le.mpr he) inf_le_left)
  obtain ⟨k, x, hxJ, hxc⟩ := hin a ha
  set a' := a * e ^ k with ha'def
  have ha' : a' ∈ A := A.mul_mem ha (A.pow_mem he k)
  have hαa' : alpha148 A Y a' ha' = alpha148 A Y a ha * alpha148 A Y e he ^ k := by
    rw [alpha148_mul ha (A.pow_mem he k), alpha148_pow he]
  rw [← hαa'] at hxc
  have hcen : ∀ z ∈ img148 A Y J, (∀ y ∈ img148 A Y J, z * y * z⁻¹ = y) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := hzc w w.2
      change (w : _) * z = z * w
      calc (w : _) * z = z * w * z⁻¹ * z := by rw [this]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hxA : ∀ (b : G) (hb : b ∈ A), alpha148 A Y b hb * x = x * alpha148 A Y b hb := by
    intro b hb
    set β := alpha148 A Y b hb
    have hβ : β ∈ img148 A Y A := alpha148_mem_img148 hb
    have hβa : β * alpha148 A Y a' ha' = alpha148 A Y a' ha' * β := by
      rw [← alpha148_mul hb ha', ← alpha148_mul ha' hb]
      congr 1
      exact hAc b hb a' ha'
    have hz : β * x * β⁻¹ ∈ img148 A Y J :=
      (Subgroup.mem_normalizer_iff.mp (hJn hβ) x).mp hxJ
    have hzx : x⁻¹ * (β * x * β⁻¹) = 1 := by
      refine hcen _ ((img148 A Y J).mul_mem ((img148 A Y J).inv_mem hxJ) hz) fun y hy => ?_
      have hy' : β⁻¹ * y * β ∈ img148 A Y J := by
        have := (Subgroup.mem_normalizer_iff.mp (hJn ((img148 A Y A).inv_mem hβ)) y).mp hy
        rwa [inv_inv] at this
      have h1 := hxc _ hy'
      have h2 := hxc y hy
      calc x⁻¹ * (β * x * β⁻¹) * y * (x⁻¹ * (β * x * β⁻¹))⁻¹
          = x⁻¹ * (β * (x * (β⁻¹ * y * β) * x⁻¹) * β⁻¹) * x := by group
        _ = x⁻¹ * (β * (alpha148 A Y a' ha' * (β⁻¹ * y * β) * (alpha148 A Y a' ha')⁻¹) * β⁻¹)
              * x := by rw [h1]
        _ = x⁻¹ * ((β * alpha148 A Y a' ha') * β⁻¹ * y * β * (β * alpha148 A Y a' ha')⁻¹)
              * x := by group
        _ = x⁻¹ * ((alpha148 A Y a' ha' * β) * β⁻¹ * y * β * (alpha148 A Y a' ha' * β)⁻¹)
              * x := by rw [hβa]
        _ = x⁻¹ * (alpha148 A Y a' ha' * y * (alpha148 A Y a' ha')⁻¹) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
        _ = y := by group
    have : β * x * β⁻¹ = x := by
      calc β * x * β⁻¹ = x * (x⁻¹ * (β * x * β⁻¹)) := by group
        _ = x := by rw [hzx, mul_one]
    calc β * x = β * x * β⁻¹ * β := by group
      _ = x * β := by rw [this]
  have hx3 : x ^ 3 = 1 := by
    refine hcen _ ((img148 A Y J).pow_mem hxJ 3) fun y hy => ?_
    have ha3 : alpha148 A Y a' ha' ^ 3 = 1 := by
      rw [← alpha148_pow ha']
      simp only [hA3 a' ha']
      rfl
    have hy1 : x * y * x⁻¹ ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem hxJ hy) ((img148 A Y J).inv_mem hxJ)
    have hy2 : x * (x * y * x⁻¹) * x⁻¹ ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem hxJ hy1) ((img148 A Y J).inv_mem hxJ)
    set α' := alpha148 A Y a' ha'
    calc x ^ 3 * y * (x ^ 3)⁻¹ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by
          rw [pow_three]; group
      _ = α' * (α' * (α' * y * α'⁻¹) * α'⁻¹) * α'⁻¹ := by
          rw [hxc y hy, hxc _ hy1, hxc _ hy2]
      _ = α' ^ 3 * y * (α' ^ 3)⁻¹ := by rw [pow_three]; group
      _ = y := by rw [ha3]; group
  obtain ⟨u, huA, huJ, hu⟩ := exists_alpha148_eq_of_mem_img148 hAF hAY hJM hAJ hxJ hxA hx3
  have hcent : a' * u⁻¹ ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
    refine ⟨A.mul_mem ha' (A.inv_mem huA), fun g hg => ?_⟩
    have hgM : g ∈ Y ⊔ A := hJM hg
    set gb := QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩
    have hgb : gb ∈ img148 A Y J := mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩
    have hmem : (a' * u⁻¹) * g * (a' * u⁻¹)⁻¹ * g⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem (Subgroup.mem_sup_right
        (A.mul_mem ha' (A.inv_mem huA))) hgM) ((Y ⊔ A).inv_mem (Subgroup.mem_sup_right
        (A.mul_mem ha' (A.inv_mem huA))))) ((Y ⊔ A).inv_mem hgM)
    refine (mk'_ker148_eq_one_iff (g := ⟨_, hmem⟩)).mp ?_
    have e1 : QuotientGroup.mk' (ker148 A Y) ⟨_, hmem⟩ =
        (alpha148 A Y a' ha' * x⁻¹) * gb * (alpha148 A Y a' ha' * x⁻¹)⁻¹ * gb⁻¹ := by
      rw [← hu, ← alpha148_inv huA, ← alpha148_mul ha' (A.inv_mem huA), alpha148_eq_mk']
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hxg : x⁻¹ * gb * x ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem ((img148 A Y J).inv_mem hxJ) hgb) hxJ
    rw [e1]
    calc (alpha148 A Y a' ha' * x⁻¹) * gb * (alpha148 A Y a' ha' * x⁻¹)⁻¹ * gb⁻¹
        = alpha148 A Y a' ha' * (x⁻¹ * gb * x) * (alpha148 A Y a' ha')⁻¹ * gb⁻¹ := by group
      _ = x * (x⁻¹ * gb * x) * x⁻¹ * gb⁻¹ := by rw [hxc _ hxg]
      _ = 1 := by group
  have hzp : a' * u⁻¹ ∈ Subgroup.zpowers e := hC hcent
  have hmemA : a = (a' * u⁻¹) * u * (e ^ k)⁻¹ := by rw [ha'def]; group
  rw [hmemA]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hzp)
    (Subgroup.mem_sup_right ⟨huA, huJ⟩)) (Subgroup.mem_sup_left ?_)
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) k)

end Decomp

end CFSG.RankThree.PartTwo.Sec14
