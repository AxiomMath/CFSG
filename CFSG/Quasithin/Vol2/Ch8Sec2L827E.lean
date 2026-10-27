module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828D
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210C
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section L827E

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_two_827 {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) {b : G} (hb : b ∈ X) {k : ℕ} (hbk : b ^ 2 ^ k = 1) :
    b ∈ pCoreOf 2 X := by
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hz : ((Nat.gcd p (2 ^ k) : ℕ) : ℤ) =
      p * Nat.gcdA p (2 ^ k) + 2 ^ k * Nat.gcdB p (2 ^ k) := by
    have := Nat.gcd_eq_gcd_ab p (2 ^ k)
    push_cast at this ⊢
    exact this
  rw [hcop.gcd_eq_one, Nat.cast_one] at hz
  have e : b = (b ^ p) ^ Nat.gcdA p (2 ^ k) := by
    calc b = b ^ (1 : ℤ) := (zpow_one b).symm
      _ = b ^ ((p : ℤ) * Nat.gcdA p (2 ^ k) + ((2 ^ k : ℕ) : ℤ) * Nat.gcdB p (2 ^ k)) := by
          rw [hz]; push_cast; ring_nf
      _ = (b ^ p) ^ Nat.gcdA p (2 ^ k) * (b ^ 2 ^ k) ^ Nat.gcdB p (2 ^ k) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (b ^ p) ^ Nat.gcdA p (2 ^ k) := by rw [hbk, one_zpow, mul_one]
  rw [e]
  exact zpow_mem (hXp b hb) _

omit [Finite G] in
theorem eq_one_of_odd_of_two_827 {H : Type*} [Group H] {g : H} {m k : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hgk : g ^ 2 ^ k = 1) : g = 1 := by
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
  have h1 : orderOf g ∣ Nat.gcd m (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgm) (orderOf_dvd_of_pow_eq_one hgk)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem mem_of_odd_two_827 {C : Subgroup G} {y : G}
    (h1 : ∀ k : ℕ, Odd (orderOf (y ^ k)) → y ^ k ∈ C)
    (h2 : ∀ k a : ℕ, (y ^ k) ^ 2 ^ a = 1 → y ^ k ∈ C) : y ∈ C := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hy1 : y ^ 2 ^ a ∈ C := by
    refine h1 _ (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_))
    rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hy2 : y ^ m ∈ C := by
    refine h2 m a ?_
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hz : ((Nat.gcd (2 ^ a) m : ℕ) : ℤ) =
      2 ^ a * Nat.gcdA (2 ^ a) m + m * Nat.gcdB (2 ^ a) m := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) m
    push_cast at this ⊢
    exact this
  rw [hcop.gcd_eq_one, Nat.cast_one] at hz
  have e : y = (y ^ 2 ^ a) ^ Nat.gcdA (2 ^ a) m * (y ^ m) ^ Nat.gcdB (2 ^ a) m := by
    calc y = y ^ (1 : ℤ) := (zpow_one y).symm
      _ = y ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m) := by
          rw [hz]; push_cast; ring_nf
      _ = _ := by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [e]
  exact C.mul_mem (zpow_mem hy1 _) (zpow_mem hy2 _)

theorem commutator_le_pCoreOf_827 {B X V P : Subgroup G} (hBp : ⁅B, B⁆ = B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥(autOn B V) ⧸ CFSG.pCore 2 ↥(autOn B V)))
    (hP : IsPGroup 2 ↥P) (hCB : ⁅B ⊓ Subgroup.centralizer (V : Set G), B⁆ ≤ P)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXp : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X)
    (hXs : Group.IsSolvable ↥X) : ⁅B, X⁆ ≤ pCoreOf 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_82 (W := ↥V)
  set O := pCoreOf 2 X with hOdef
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    hBX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hconjX : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X := fun b hb x hx =>
    (Subgroup.mem_normalizer_iff.mp (hBX hb) x).mp hx
  have hconjOB : ∀ b ∈ B, ∀ o ∈ O, b * o * b⁻¹ ∈ O := fun b hb o ho =>
    (Subgroup.mem_normalizer_iff.mp (hBO hb) o).mp ho
  have hconjOX : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.mp (hXO hx) o).mp ho
  set Q := ⁅X, B⁆ with hQdef
  have hQX : Q ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hBX
  have hQB : Q ≤ B := Subgroup.le_normalizer_iff_commutator_le_right.mp hXB
  set R := ⁅Q, B⁆ with hRdef
  have hRX : R ≤ X := (Subgroup.commutator_mono hQX le_rfl).trans hQX
  set Λ := autOn B V with hΛdef
  set φ := actHom82 hBV with hφdef
  have hφs : Function.Surjective φ := actHom82_surjective hBV
  have hΛp : ⁅Λ, Λ⁆ = Λ := by
    have hr : Λ = (Λ.subtype.comp φ).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφs, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hBp' : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hBp
    rw [hr, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hΛns : ¬ Group.IsSolvable ↥Λ := by
    intro hs
    have hqs : Group.IsSolvable (↥Λ ⧸ CFSG.pCore 2 ↥Λ) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have := hq.1
    exact Group.IsPerfect.not_isSolvable _ hqs
  set S := (X ⊓ B).subgroupOf B with hSdef
  have hSn : S.Normal := by
    refine ⟨fun s hs b => ?_⟩
    rw [hSdef, Subgroup.mem_subgroupOf] at hs ⊢
    refine ⟨?_, (b * s * b⁻¹).2⟩
    exact hconjX b b.2 s hs.1
  set D := S.map φ with hDdef
  have hDn : D.Normal := hSn.map φ hφs
  have hDne : D ≠ ⊤ := by
    intro htop
    apply hΛns
    have hSs : Group.IsSolvable ↥S := by
      let ι : ↥S →* ↥X :=
        { toFun := fun s => ⟨((s : ↥B) : G), (Subgroup.mem_subgroupOf.mp s.2).1⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := ι) fun s t hst => ?_
      have h := congrArg (fun z : ↥X => (z : G)) hst
      exact Subtype.ext (Subtype.ext h)
    have hDs : Group.IsSolvable ↥D := by
      rw [hDdef]
      exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective S)
    have hsurj : Function.Surjective (D.subtype) := by
      intro l
      exact ⟨⟨l, htop ▸ Subgroup.mem_top l⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj
  have hZ := map_le_center_828 hq hΛp hDn hDne
  have hSB : ∀ s ∈ X ⊓ B, ∀ b ∈ B, ∃ hsb : ⁅s, b⁆ ∈ B,
      φ ⟨⁅s, b⁆, hsb⟩ ∈ CFSG.pCore 2 ↥Λ := by
    intro s hs b hb
    refine ⟨B.mul_mem (B.mul_mem (B.mul_mem hs.2 hb) (B.inv_mem hs.2)) (B.inv_mem hb), ?_⟩
    have he : (⟨⁅s, b⁆, B.mul_mem (B.mul_mem (B.mul_mem hs.2 hb) (B.inv_mem hs.2))
        (B.inv_mem hb)⟩ : ↥B) = ⁅(⟨s, hs.2⟩ : ↥B), (⟨b, hb⟩ : ↥B)⁆ := rfl
    rw [he, map_commutatorElement, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
      map_commutatorElement]
    have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥Λ) (φ ⟨s, hs.2⟩) ∈
        Subgroup.center (↥Λ ⧸ CFSG.pCore 2 ↥Λ) :=
      hZ ⟨φ ⟨s, hs.2⟩, ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, rfl⟩
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hc _).symm
  have hA : ∀ y ∈ R, Odd (orderOf y) → ∀ b ∈ B, ⁅y, b⁆ ∈ O := by
    intro y hy hyo b hb
    have hRS : R ≤ ((CFSG.pCore 2 ↥Λ).comap φ).map B.subtype := by
      rw [hRdef, Subgroup.commutator_le]
      intro q hq c hc
      obtain ⟨hqc, hmem⟩ := hSB q ⟨hQX hq, hQB hq⟩ c hc
      exact ⟨⟨⁅q, c⁆, hqc⟩, hmem, rfl⟩
    obtain ⟨y', hy', rfl⟩ := hRS hy
    have hy1 : φ y' = 1 := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Λ)) ⟨φ y', hy'⟩
      refine eq_one_of_odd_of_two_827 (m := orderOf y') ?_ ?_ (k := k) ?_
      · rwa [← Subgroup.orderOf_coe]
      · rw [← map_pow, pow_orderOf_eq_one, map_one]
      · exact congrArg Subtype.val hk
    have hyC : (y' : G) ∈ Subgroup.centralizer (V : Set G) :=
      (mem_ker_actHom82 hBV y').mp hy1
    have hyb : ⁅(y' : G), b⁆ ∈ P := hCB (Subgroup.commutator_mem_commutator ⟨y'.2, hyC⟩ hb)
    obtain ⟨k, hk⟩ := hP ⟨_, hyb⟩
    have hybX : ⁅(y' : G), b⁆ ∈ X := by
      have e : ⁅(y' : G), b⁆ = (y' : G) * (b * (y' : G)⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact X.mul_mem (hRX hy) (hconjX b hb _ (X.inv_mem (hRX hy)))
    exact mem_pCoreOf_of_two_827 hp hp2 hXp hybX (k := k) (congrArg Subtype.val hk)
  let C : Subgroup G :=
    { carrier := {y | y ∈ X ∧ ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ O}
      one_mem' := ⟨X.one_mem, fun b _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨X.mul_mem hy₁ hy₂, fun b hb => ?_⟩
        have e : y₁ * y₂ * b * (y₁ * y₂)⁻¹ * b⁻¹ =
            y₁ * (y₂ * b * y₂⁻¹ * b⁻¹) * y₁⁻¹ * (y₁ * b * y₁⁻¹ * b⁻¹) := by group
        rw [e]
        exact O.mul_mem (hconjOX y₁ hy₁ _ (h₂ b hb)) (h₁ b hb)
      inv_mem' := by
        rintro y ⟨hy, h⟩
        refine ⟨X.inv_mem hy, fun b hb => ?_⟩
        have e : y⁻¹ * b * y⁻¹⁻¹ * b⁻¹ = y⁻¹ * (y * b * y⁻¹ * b⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hconjOX y⁻¹ (X.inv_mem hy) _ (O.inv_mem (h b hb)) }
  have hOC : ∀ o ∈ O, o ∈ C := by
    intro o ho
    refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 X ho, fun b hb => ?_⟩
    have e : o * b * o⁻¹ * b⁻¹ = o * (b * o⁻¹ * b⁻¹) := by group
    rw [e]
    exact O.mul_mem ho (hconjOB b hb _ (O.inv_mem ho))
  have hRC : R ≤ C := by
    intro y hy
    refine mem_of_odd_two_827 (fun k hk => ?_) (fun k a hka => ?_)
    · refine ⟨hRX (R.pow_mem hy k), fun b hb => ?_⟩
      have := hA _ (R.pow_mem hy k) hk b hb
      rwa [commutatorElement_def] at this
    · exact hOC _ (mem_pCoreOf_of_two_827 hp hp2 hXp (hRX (R.pow_mem hy k)) hka)
  have hRB : ⁅R, B⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro y hy b hb
    rw [commutatorElement_def]
    exact (hRC hy).2 b hb
  have hQO : ⁅Q, B⁆ ≤ O := by
    have h := CFSG.RankThree.PartTwo.Sec6.three_subgroups_mod (X := B) (Y := Q) (Z := B) (N := O)
      hBO (hQX.trans hXO) hBO (by rw [Subgroup.commutator_comm B Q]; exact hRB) hRB
    rw [hBp, Subgroup.commutator_comm] at h
    exact h
  have h := CFSG.RankThree.PartTwo.Sec6.three_subgroups_mod (X := B) (Y := X) (Z := B) (N := O)
    hBO hXO hBO (by rw [Subgroup.commutator_comm B X]; exact hQO) hQO
  rw [hBp] at h
  exact h

end L827E

end CFSG.Quasithin.H13
