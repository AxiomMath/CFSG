module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.NPrime
public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.L3YC

section Split

variable {Γ : Type*} [Group Γ]

theorem exists_two_three_split {P : Subgroup Γ} {g : Γ} {m : ℕ} (hP : IsPGroup 2 ↥P)
    (hg : g ^ 3 ^ m ∈ P) :
    ∃ g₂ ∈ P, ∃ g₃ ∈ Subgroup.zpowers g, g = g₂ * g₃ ∧ g₃ ^ 3 ^ m = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g ^ 3 ^ m, hg⟩
  have hk' : (g ^ 3 ^ m) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨g ^ (((3 ^ m : ℕ) : ℤ) * b), ?_, g ^ (a * ((2 ^ k : ℕ) : ℤ)), ?_, ?_, ?_⟩
  · rw [zpow_mul, zpow_natCast]
    exact P.zpow_mem hg b
  · exact Subgroup.zpow_mem_zpowers g _
  · rw [← zpow_add]
    have : ((3 ^ m : ℕ) : ℤ) * b + a * ((2 ^ k : ℕ) : ℤ) = 1 := by
      push_cast at hab ⊢
      linarith
    rw [this, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have h : a * ((2 ^ k : ℕ) : ℤ) * ((3 ^ m : ℕ) : ℤ) = ((3 ^ m * 2 ^ k : ℕ) : ℤ) * a := by
      push_cast; ring
    rw [h, zpow_mul, zpow_natCast, pow_mul, hk', one_zpow]

end Split

section Fixed

variable {G : Type} [Group G]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mat2_cube_fix : ∀ (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (v : Fin 2 → ZMod 2),
    A * A * A = 1 → v ≠ 0 → A.mulVec v = v → A = 1 := by
  decide +kernel

theorem centralizes_of_fixes [Finite G] {V : Subgroup G} (hV4 : Nat.card V = 4)
    (hsq : ∀ a ∈ V, a * a = 1) {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) {m : ℕ}
    (hgm : g ^ 3 ^ m = 1) {c : G} (hc : c ∈ V) (hc1 : c ≠ 1) (hgc : g * c * g⁻¹ = c) :
    ∀ x ∈ V, g * x * g⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 2)
    (W := ↥V) (comm_of_sq_one hsq)
    (fun a => by rw [pow_two]; exact Subtype.ext (hsq _ a.2)) (by rw [hV4]; norm_num)
  have hA := card_mulAut_of_card_four hV4 hsq
  have h1 : actAut hg ^ 3 ^ m = 1 := by
    rw [actAut_pow, actAut_eq_one_iff]
    intro x _
    rw [hgm]
    group
  have h3 : actAut hg ^ 3 = 1 :=
    pow_three_eq_one_of_odd hA (Odd.pow (by decide : Odd 3)) h1
  set A := CFSG.SectionRank.Ccomm.elemAutEquivGL e (actAut hg) with hAdef
  have hA3 : A ^ 3 = 1 := by rw [hAdef, ← map_pow, h3, map_one]
  have hA3' : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) * A * A = 1 := by
    have := congrArg (fun u : GL (Fin 2) (ZMod 2) => (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) hA3
    simpa [pow_three', Units.val_mul] using this
  have hv : Multiplicative.toAdd (e ⟨c, hc⟩) ≠ 0 := by
    intro h
    have : e ⟨c, hc⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h
    have h' : (⟨c, hc⟩ : ↥V) = 1 := e.injective (by rw [this, map_one])
    exact hc1 (congrArg Subtype.val h')
  have hfix : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (e ⟨c, hc⟩)) =
      Multiplicative.toAdd (e ⟨c, hc⟩) := by
    rw [hAdef, CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec]
    congr 2
    exact Subtype.ext hgc
  have hA1 : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := mat2_cube_fix _ _ hA3' hv hfix
  have hAone : A = 1 := Units.ext hA1
  have : actAut hg = 1 := by
    apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
    rw [← hAdef, hAone, map_one]
  exact (actAut_eq_one_iff hg).mp this

end Fixed

section Inner

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_modO2Surj_of_isLnTwoQuot {L : Subgroup G} (hq : IsLnTwoQuot L 3) :
    ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α := by
  obtain ⟨e⟩ := hq
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite G] in
theorem center_trivial_of_isLnTwoQuot {L : Subgroup G} (hq : IsLnTwoQuot L 3) :
    ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L := by
  obtain ⟨α, hα⟩ := exists_modO2Surj_of_isLnTwoQuot hq
  exact center_trivial_of_modO2Surj (F := ZMod 2) (by simp) hα

theorem exists_inner_of_three_power {L : Subgroup G} (hq : IsLnTwoQuot L 3) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hxm : x ^ 3 ^ m = 1) :
    ∃ l ∈ L, l⁻¹ * x ∈ N0 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hq
  have hOI : OddInner (↥L ⧸ CFSG.pCore 2 ↥L) :=
    oddInner_sl32.of_mulEquiv
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).trans e.symm)
  set ex : MulAut ↥L := L.normalizerMonoidHom ⟨x, hx⟩ with hex
  let φ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) ex (CFSG.pCore_map_iso 2 ex)
  have hφ : ∀ (j : ℕ) (y : ↥L), (φ ^ j) (QuotientGroup.mk y) = QuotientGroup.mk ((ex ^ j) y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
      have : φ (QuotientGroup.mk y) = QuotientGroup.mk (ex y) := rfl
      rw [this, ih]
  have hex1 : ex ^ 3 ^ m = 1 := by
    rw [hex, ← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 ^ m = 1 :=
      Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  have hφ1 : φ ^ 3 ^ m = 1 := by
    ext y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hex1]
    rfl
  have hodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hφ1)
  obtain ⟨k, hk⟩ := hOI φ hodd
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective k
  have hconj : ∀ y : ↥L, (ex y)⁻¹ * (l₀ * y * l₀⁻¹) ∈ CFSG.pCore 2 ↥L := by
    intro y
    have h1 : φ (QuotientGroup.mk y) = (MulAut.conj (QuotientGroup.mk l₀ : ↥L ⧸ CFSG.pCore 2 ↥L))
        (QuotientGroup.mk y) := by rw [← hk]
    have h2 : QuotientGroup.mk (s := CFSG.pCore 2 ↥L) (ex y) =
        QuotientGroup.mk (s := CFSG.pCore 2 ↥L) (l₀ * y * l₀⁻¹) := by
      have := h1
      simp only [MulAut.conj_apply] at this
      exact this
    exact QuotientGroup.eq.mp h2
  refine ⟨(l₀ : G), l₀.2, ?_⟩
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer l₀.2)) hx, ?_⟩
  intro y hy
  set y' : ↥L := ⟨y, hy⟩ with hy'
  have hp := hconj y'
  have hnormal : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hq' : y' * (l₀⁻¹ * ((ex y')⁻¹ * (l₀ * y' * l₀⁻¹))⁻¹ * l₀⁻¹⁻¹) * y'⁻¹ ∈
      CFSG.pCore 2 ↥L :=
    hnormal.conj_mem _ (hnormal.conj_mem _ ((CFSG.pCore 2 ↥L).inv_mem hp) l₀⁻¹) y'
  refine ⟨_, by exact hq', ?_⟩
  have hexy : ((ex y' : ↥L) : G) = x * y * x⁻¹ := rfl
  have hyy : ((y' : ↥L) : G) = y := rfl
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, hexy,
    hyy]
  group

theorem exists_decomp_of_three_power {L : Subgroup G} (hq : IsLnTwoQuot L 3) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hxm : x ^ 3 ^ m = 1) :
    ∃ l ∈ L, ∃ n ∈ N0 L, x = l * n ∧ n ^ 3 ^ m = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l₀, hl₀, hn⟩ := exists_inner_of_three_power hq hx hxm
  set n₀ : G := l₀⁻¹ * x with hn₀
  have hnL : n₀ ^ 3 ^ m ∈ L := by
    set N' := Subgroup.normalizer (L : Set G) with hN'
    have hnorm : (L.subgroupOf N').Normal := Subgroup.normal_in_normalizer
    have hab : QuotientGroup.mk' (L.subgroupOf N') ⟨n₀, hn.1⟩ =
        QuotientGroup.mk' (L.subgroupOf N') ⟨x, hx⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have h1 : x⁻¹ * l₀ * x ∈ L := (Subgroup.mem_normalizer_iff''.mp hx l₀).mp hl₀
      simpa [hn₀, mul_assoc] using h1
    have h2 : (QuotientGroup.mk' (L.subgroupOf N') ⟨n₀, hn.1⟩) ^ 3 ^ m = 1 := by
      rw [hab, ← map_pow]
      have : (⟨x, hx⟩ : ↥N') ^ 3 ^ m = 1 := Subtype.ext (by simpa using hxm)
      rw [this, map_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hnN : n₀ ^ 3 ^ m ∈ N0 L := pow_mem hn _
  have hzP : n₀ ^ 3 ^ m ∈ pCoreOf 2 L :=
    center_trivial_of_isLnTwoQuot hq _ hnL (fun a ha => hnN.2 a ha)
  obtain ⟨n₂, hn₂, n₃, hn₃, hsplit, hn₃pow⟩ :=
    exists_two_three_split (pCoreOf_isPGroup 2 L) hzP
  have hn₃N : n₃ ∈ N0 L := (Subgroup.zpowers_le.mpr hn) hn₃
  refine ⟨l₀ * n₂, L.mul_mem hl₀ (pCoreOf_le 2 L hn₂), n₃, hn₃N, ?_, hn₃pow⟩
  have : x = l₀ * n₀ := by rw [hn₀]; group
  rw [this, hsplit, mul_assoc]

end Inner

end Stellmacher.L3YC

end CFSG.Quasithin
