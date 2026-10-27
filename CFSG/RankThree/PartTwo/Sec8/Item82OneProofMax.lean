module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec8.Outer
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82OneProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts

section General

variable {G : Type*} [Group G]

theorem isElemAbelian_sup_zpowers {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {y : G} (hy3 : y ^ 3 = 1) (hyA : ∀ x ∈ A, x * y = y * x) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) := by
  have hcomm : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hle : A ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hyA x hx).symm k)).eq
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    exact hyA x hx
  have hpair : ∀ z ∈ A ⊔ Subgroup.zpowers y, ∃ x ∈ A, ∃ k : ℤ, z = x * y ^ k := by
    intro z hz
    rw [sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) A hyN] at hz
    obtain ⟨w, hw, x, hx, rfl⟩ := hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨x, hx, k, ((Commute.zpow_left (hyA x hx).symm k)).eq⟩
  have hcomm' : ∀ z ∈ A ⊔ Subgroup.zpowers y, ∀ z' ∈ A ⊔ Subgroup.zpowers y, z * z' = z' * z := by
    intro z hz z' hz'
    obtain ⟨x, hx, k, rfl⟩ := hpair z hz
    obtain ⟨x', hx', k', rfl⟩ := hpair z' hz'
    have h1 : Commute x x' := hcomm x hx x' hx'
    have h2 : Commute x (y ^ k') := (Commute.zpow_right (hyA x hx) k')
    have h3 : Commute (y ^ k) x' := (Commute.zpow_left (hyA x' hx').symm k)
    have h4 : Commute (y ^ k) (y ^ k') := Commute.zpow_zpow_self y k k'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  refine ⟨⟨⟨fun z z' => Subtype.ext (hcomm' z z.2 z' z'.2)⟩⟩, fun z hz => ?_⟩
  obtain ⟨x, hx, k, rfl⟩ := hpair z hz
  have hc : Commute x (y ^ k) := Commute.zpow_right (hyA x hx) k
  rw [hc.mul_pow, hA.2 x hx, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hy3, one_zpow]

theorem mem_zpowers_pow_of_not_three_dvd {x : G} (hx3 : x ^ 3 = 1) {r : ℕ} (hr : ¬ 3 ∣ r) :
    x ∈ Subgroup.zpowers (x ^ r) := by
  have hr' : r % 3 = 1 ∨ r % 3 = 2 := by omega
  have hxr : x ^ r = x ^ (r % 3) := by
    conv_lhs => rw [← Nat.div_add_mod r 3, pow_add, pow_mul, hx3, one_pow, one_mul]
  rcases hr' with h | h
  · rw [hxr, h, pow_one]
    exact Subgroup.mem_zpowers x
  · rw [hxr, h]
    have : x = (x ^ 2) ^ (2 : ℤ) := by
      rw [zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨2, this.symm⟩

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun σ : MulAut G => σ g) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * x = x * g * x⁻¹ * x := by rw [h1]
    _ = x * g := by group

end General

section AutA

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {L : Subgroup G}

theorem pow_three_of_mem_autThetaQuot (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ : β ∈ autThetaQuot A L) : β ^ 3 = 1 := by
  obtain ⟨g, hN, hgA, rfl⟩ := mem_autThetaQuot_iff.mp hβ
  have h1 : (⟨g, hN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hAe.2 g hgA)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem commute_of_mem_autThetaQuot (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    {β γ : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ : β ∈ autThetaQuot A L)
    (hγ : γ ∈ autThetaQuot A L) : Commute β γ := by
  obtain ⟨g, hN, hgA, rfl⟩ := mem_autThetaQuot_iff.mp hβ
  obtain ⟨g', hN', hgA', rfl⟩ := mem_autThetaQuot_iff.mp hγ
  have hgg : g * g' = g' * g := congrArg Subtype.val (hAe.1.is_comm.comm ⟨g, hgA⟩ ⟨g', hgA'⟩)
  have h1 : (⟨g, hN⟩ : Subgroup.normalizer (L : Set G)) * ⟨g', hN'⟩ = ⟨g', hN'⟩ * ⟨g, hN⟩ :=
    Subtype.ext hgg
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, h1, map_mul, map_mul]

end AutA



variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem card_autThetaQuot_eq_nine (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) : Nat.card (autThetaQuot A L) = 9 := by
  have hAe := h.mem_partTwoF.1
  have hset := Sec13.sectionCentralizer_eq_inf hAN
  rw [h.sectionCentralizer_eq] at hset
  have heq : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hset.symm
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 c h.mem_A) h.ne_one
  have hmul := Sec13.card_inf_mul_card_autThetaQuot hAN
  rw [heq, hc3, h27] at hmul
  omega

theorem exists_inner_generator (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ x : L ⧸ aschbacherSolvableCore 3 L, MulAut.conj x ∈ autThetaQuot A L ∧
      MulAut.conj x ≠ 1 ∧
      (∀ β ∈ autThetaQuot A L, IsInnerAut β → β ∈ Subgroup.zpowers (MulAut.conj x)) ∧
      ∀ β ∈ autThetaQuot A L, ∃ k < 3,
        thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) ^ k * β ∈
          Subgroup.zpowers (MulAut.conj x) := by
  have hAe := h.mem_partTwoF.1
  set Γ := autThetaQuot A L with hΓ
  set Inn := (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
    MulAut (L ⧸ aschbacherSolvableCore 3 L)).range with hInn
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ Γ := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have hτout : ¬ IsInnerAut τ := h.not_isInnerAut_induced
  have h9 := card_autThetaQuot_eq_nine h h27 hAN
  have hk : ∀ β ∈ Γ, ∃ k < 3, τ ^ k * β ∈ Inn := fun β hβ =>
    hcyc τ β (commute_of_mem_autThetaQuot hAe hτΓ hβ) (pow_three_of_mem_autThetaQuot hAe hτΓ)
      (pow_three_of_mem_autThetaQuot hAe hβ) hτout
  have hle3 := card_le_three_mul_card_inf_of_forall_pow_mul_mem hτΓ hk
  rw [h9] at hle3
  have hdvd : Nat.card (Γ ⊓ Inn : Subgroup _) ∣ 9 := h9 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne9 : Nat.card (Γ ⊓ Inn : Subgroup _) ≠ 9 := by
    intro h9'
    have hEq : Γ ⊓ Inn = Γ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, h9'])
    have hτI : τ ∈ Γ ⊓ Inn := by rw [hEq]; exact hτΓ
    exact hτout hτI.2
  have hI3 : Nat.card (Γ ⊓ Inn : Subgroup _) = 3 := by
    have hpos : 0 < Nat.card (Γ ⊓ Inn : Subgroup _) := Nat.card_pos
    have hle : Nat.card (Γ ⊓ Inn : Subgroup _) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hI : Nat.card (Γ ⊓ Inn : Subgroup _) <;> simp_all
  obtain ⟨⟨ι, hιI⟩, hι1⟩ : ∃ ι : (Γ ⊓ Inn : Subgroup _), ι ≠ 1 := by
    have : Nontrivial (Γ ⊓ Inn : Subgroup _) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hI3]; norm_num)
    exact exists_ne 1
  have hι1' : ι ≠ 1 := fun h1 => hι1 (Subtype.ext h1)
  obtain ⟨x, rfl⟩ := hιI.2
  have hzp : Subgroup.zpowers (MulAut.conj x) = Γ ⊓ Inn := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hιI
    · rw [hI3, Nat.card_zpowers,
        orderOf_eq_prime (pow_three_of_mem_autThetaQuot hAe hιI.1) hι1']
  refine ⟨x, hιI.1, hι1', fun β hβ hβi => ?_, fun β hβ => ?_⟩
  · rw [hzp]
    exact ⟨hβ, hβi⟩
  · obtain ⟨k, hk3, hkI⟩ := hk β hβ
    refine ⟨k, hk3, ?_⟩
    rw [hzp]
    exact ⟨mul_mem (pow_mem hτΓ k) hβ, hkI⟩

theorem false_of_not_three_dvd (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (h3 : ¬ 3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) : False := by
  obtain ⟨x, hxΓ, hx1, -, -⟩ := exists_inner_generator h h27 hAN hcyc
  have ho : orderOf (MulAut.conj x) = 3 :=
    orderOf_eq_prime (pow_three_of_mem_autThetaQuot h.mem_partTwoF.1 hxΓ) hx1
  have h1 : orderOf (MulAut.conj x) ∣ orderOf x := orderOf_map_dvd _ x
  rw [ho] at h1
  exact h3 (h1.trans (orderOf_dvd_natCard x))

theorem false_of_e9Closed (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hE9 : E9Closed (barCentralizer (Subgroup.zpowers a) L)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨x, hxΓ, hx1, hinner, hkpow⟩ := exists_inner_generator h h27 hAN hcyc
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ autThetaQuot A L := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, pow_three_of_mem_autThetaQuot hAe hxΓ, map_one])
  have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have hτx : τ x = x := by
    apply hinj
    rw [← mul_mulAutConj_mul_inv, (commute_of_mem_autThetaQuot hAe hτΓ hxΓ).eq,
      mul_inv_cancel_right]
  have hbar : barCentralizer (Subgroup.zpowers a) L = autFix τ :=
    barCentralizer_zpowers_eq_autFix (hAN h.a_mem)
  have hxC : x ∈ barCentralizer (Subgroup.zpowers a) L := by
    rw [hbar]
    exact hτx
  obtain ⟨⟨y, hyC⟩, hy3, hxy, hyx⟩ := hE9 ⟨x, hxC⟩ (Subtype.ext hx3)
    (fun h1 => hx1' (congrArg Subtype.val h1))
  have hy3' : y ^ 3 = 1 := congrArg Subtype.val hy3
  have hxy' : x * y = y * x := congrArg Subtype.val hxy
  have hyx' : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
  have hτy : τ y = y := by
    rw [hbar] at hyC
    exact hyC
  have hτpow : ∀ m : ℕ, (τ ^ m) y = y := by
    intro m
    induction m with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hτy, ih]
  have hfix : ∀ β ∈ autThetaQuot A L, β y = y := by
    intro β hβ
    obtain ⟨k, -, hkI⟩ := hkpow β hβ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkI
    have hxyj : MulAut.conj x ^ j • y = y := by
      rw [← map_zpow]
      change x ^ j * y * (x ^ j)⁻¹ = y
      rw [(Commute.zpow_left (show Commute x y from hxy') j).eq, mul_inv_cancel_right]
    have hτk : (τ ^ k)⁻¹ y = y := by
      calc (τ ^ k)⁻¹ y = (τ ^ k)⁻¹ ((τ ^ k) y) := by rw [hτpow k]
        _ = y := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    calc β y = (τ ^ k)⁻¹ ((τ ^ k * β) y) := by
          rw [MulAut.mul_apply, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      _ = (τ ^ k)⁻¹ (MulAut.conj x ^ j • y) := by rw [← hj]; rfl
      _ = y := by rw [hxyj, hτk]
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  set φ : A →* MulAut L := (compAction L).comp (Subgroup.inclusion hAN) with hφ
  have hφN : ∀ g, ∀ n ∈ aschbacherSolvableCore 3 L, φ g n ∈ aschbacherSolvableCore 3 L := by
    intro g n hn
    have hmap := map_aschbacherSolvableCore (φ g)
    rw [← hmap]
    exact ⟨n, hn, rfl⟩
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    not_three_dvd_card_aschbacherSolvableCore L
  obtain ⟨y₀, hy₀def⟩ := QuotientGroup.mk_surjective y
  have hy₀ : ∀ g, ((φ g y₀ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      (y₀ : L ⧸ aschbacherSolvableCore 3 L) := by
    intro g
    have hg : thetaQuotMulAut L (φ g) ∈ autThetaQuot A L :=
      mem_autThetaQuot_iff.mpr ⟨g, hAN g.2, g.2, rfl⟩
    have h1 := hfix _ hg
    rw [← hy₀def] at h1
    exact h1
  obtain ⟨y₁, hy₁, hy₁A⟩ :=
    exists_fixed_of_coprime hA3 φ (aschbacherSolvableCore 3 L) hN3 hφN y₀ hy₀
  set r := Nat.card (aschbacherSolvableCore 3 L) with hr
  set y₂ : L := y₁ ^ r with hy₂
  have hy₁3 : y₁ ^ 3 ∈ aschbacherSolvableCore 3 L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy₁, hy₀def]
    exact hy3'
  have hy₂3 : y₂ ^ 3 = 1 := by
    rw [hy₂, ← pow_mul, mul_comm, pow_mul]
    have := pow_card_eq_one' (x := (⟨y₁ ^ 3, hy₁3⟩ : aschbacherSolvableCore 3 L))
    exact congrArg Subtype.val this
  have hy₂bar : ((y₂ : L) : L ⧸ aschbacherSolvableCore 3 L) = y ^ r := by
    rw [hy₂, QuotientGroup.mk_pow, hy₁, hy₀def]
  have hy₂A : ∀ g ∈ A, g * (y₂ : G) = (y₂ : G) * g := by
    intro g hg
    have h1 : φ ⟨g, hg⟩ y₂ = y₂ := by rw [hy₂, map_pow, hy₁A]
    have h2 : g * (y₂ : G) * g⁻¹ = y₂ := congrArg Subtype.val h1
    calc g * (y₂ : G) = g * (y₂ : G) * g⁻¹ * g := by group
      _ = y₂ * g := by rw [h2]
  have hy₂notA : (y₂ : G) ∉ A := by
    intro hyA
    have hN' : (y₂ : G) ∈ Subgroup.normalizer (L : Set G) := hAN hyA
    have hconj : thetaQuotMulAut L (compAction L ⟨y₂, hN'⟩) =
        MulAut.conj ((y₂ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
      thetaQuotMulAut_compAction_eq_conj y₂.2 hN'
    have hmem : thetaQuotMulAut L (compAction L ⟨y₂, hN'⟩) ∈ autThetaQuot A L :=
      mem_autThetaQuot_iff.mpr ⟨y₂, hN', hyA, rfl⟩
    have hz := hinner _ hmem (by rw [hconj]; exact ⟨_, rfl⟩)
    rw [hconj] at hz
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← map_zpow] at hj
    have hj' := hinj hj
    apply hyx'
    have hmem' : y ^ r ∈ Subgroup.zpowers x := by
      rw [← hy₂bar, ← hj']
      exact Subgroup.zpow_mem_zpowers x j
    exact Subgroup.zpowers_le.mpr hmem' (mem_zpowers_pow_of_not_three_dvd hy3' hN3)
  have hB := isElemAbelian_sup_zpowers hAe (by simpa using congrArg Subtype.val hy₂3) hy₂A
  have hBA := h.mem_partTwoF.2.1 _ hB le_sup_left
  exact hy₂notA (hBA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (y₂ : G)))

end CFSG.RankThree.PartTwo.Sec8.Item82OneProof
