module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionInflate
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFrattiniGeneratorBound

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG Subgroup
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutator_mem_centralizer_of_prime_card {q : ℕ} (hq : q.Prime) {Z : Subgroup G}
    [Z.Normal] (hZ : Nat.card Z = q) (g h : G) :
    ⁅g, h⁆ ∈ Subgroup.centralizer (Z : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨z0, hz0⟩ := IsCyclic.exists_generator (α := Z)
  have hcomm : ∀ a b : MulAut ↥Z, a * b = b * a := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hz0 (a z0))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hz0 (b z0))
    have hz : (a * b) z0 = (b * a) z0 := by
      calc (a * b) z0 = a (b z0) := rfl
        _ = a (z0 ^ j) := by rw [hj]
        _ = (a z0) ^ j := map_zpow a z0 j
        _ = (z0 ^ i) ^ j := by rw [hi]
        _ = z0 ^ (i * j) := (zpow_mul z0 i j).symm
        _ = z0 ^ (j * i) := by rw [mul_comm]
        _ = (z0 ^ j) ^ i := zpow_mul z0 j i
        _ = (b z0) ^ i := by rw [hj]
        _ = b (z0 ^ i) := (map_zpow b z0 i).symm
        _ = b (a z0) := by rw [hi]
        _ = (b * a) z0 := rfl
    ext x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hz0 x)
    rw [map_zpow (a * b), map_zpow (b * a), hz]
  have h1 : MulAut.conjNormal (H := Z) ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h2 := congrArg (fun f : MulAut ↥Z => ((f ⟨z, hz⟩ : ↥Z) : G)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc z * ⁅g, h⁆ = (⁅g, h⁆ * z * ⁅g, h⁆⁻¹) * ⁅g, h⁆ := by rw [h2]
    _ = ⁅g, h⁆ * z := by group

theorem le_centralizer_of_commutator_eq {q : ℕ} (hq : q.Prime) {R A Z : Subgroup G}
    [Z.Normal] (hZ : Nat.card Z = q) (hRA : ⁅R, A⁆ = R) :
    R ≤ Subgroup.centralizer (Z : Set G) := by
  rw [← hRA]
  exact Subgroup.commutator_le.2 fun r _ a _ => commutator_mem_centralizer_of_prime_card hq hZ r a

theorem commutator_commutator_sup_eq_bot {X Y : Subgroup G} [X.Normal] [Y.Normal]
    (hXY : ⁅X, Y⁆ = ⊥) (hX : ⁅⁅X, X⁆, X⁆ = ⊥) (hY : ⁅⁅Y, Y⁆, Y⁆ = ⊥) :
    ⁅⁅X ⊔ Y, X ⊔ Y⁆, X ⊔ Y⁆ = ⊥ := by
  have hYX : ⁅Y, X⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hXY
  have h1 : ⁅X ⊔ Y, X ⊔ Y⁆ = ⁅X, X⁆ ⊔ ⁅Y, Y⁆ := by
    rw [Subgroup.commutator_sup_right X Y (X ⊔ Y), Subgroup.commutator_sup_left X X Y,
      Subgroup.commutator_sup_left Y X Y, hXY, hYX, sup_bot_eq, bot_sup_eq]
  have e1 : ⁅⁅X, X⁆, Y⁆ = ⊥ :=
    le_bot_iff.1 (hXY ▸ Subgroup.commutator_mono (Subgroup.commutator_le_right X X) le_rfl)
  have e2 : ⁅⁅Y, Y⁆, X⁆ = ⊥ :=
    le_bot_iff.1 (hYX ▸ Subgroup.commutator_mono (Subgroup.commutator_le_right Y Y) le_rfl)
  rw [h1, Subgroup.commutator_sup_right (⁅X, X⁆) (⁅Y, Y⁆) (X ⊔ Y),
    Subgroup.commutator_sup_left (⁅X, X⁆) X Y, Subgroup.commutator_sup_left (⁅Y, Y⁆) X Y,
    hX, hY, e1, e2]
  simp

end Commutators

theorem le_centralizer_of_critical (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction)
    {G : Type} [Group G] [Finite G] {q : ℕ} {A R Q D : Subgroup G} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hA : Nat.card A = 5)
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32)
    (ha : ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
      ⁅a, r⁆ ∉ inSubgroup Subgroup.center R)
    [hQn : Q.Normal] (hQp : IsPGroup q Q) (hDQ : D ≤ Q) [hDn : D.Normal]
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) (hDcard : Nat.card D = q ^ 5)
    (hZne : D ⊓ Subgroup.centralizer (D : Set G) ≠ ⊥)
    (hRZ : R ≤ Subgroup.centralizer ((D ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G))
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    R ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set C : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCn : C.Normal := inferInstance
  have hCq : IsPGroup q C := hQp.to_le inf_le_left
  have hZC : D ⊓ Subgroup.centralizer (D : Set G) ≤ C := fun z hz => ⟨hDQ hz.1, hz.2⟩
  have hCnt : Nontrivial ↥C :=
    (Subgroup.nontrivial_iff_ne_bot C).2 (ne_bot_of_le_ne_bot hZne hZC)
  obtain ⟨W, hWchar, hWne, hWcomm, hWexp, hWpg⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hCq
  have : W.Characteristic := hWchar
  set W' : Subgroup G := W.map C.subtype with hW'
  have hW'n : W'.Normal :=
    CFSG.LocalAnalysis.GorensteinLyons.map_subtype_normal_of_characteristic C W
  have hW'C : W' ≤ C := Subgroup.map_subtype_le W
  have hW'Q : W' ≤ Q := hW'C.trans inf_le_left
  have hDW' : ∀ k ∈ D, ∀ l ∈ W', k * l = l * k := fun k hk l hl =>
    Subgroup.mem_centralizer_iff.1 (hW'C hl).2 k hk
  have hDW'bot : ⁅D, W'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hDW' k hk l hl).symm
  have hW'exp : ∀ x ∈ W', x ^ q = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    simpa using congrArg Subtype.val (hWexp w hw)
  have hW'cl : ⁅⁅W', W'⁆, W'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ⁅W, (⊤ : Subgroup ↥C)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b)
    have h2 : ⁅a, b⁆ ∈ Subgroup.centralizer (W : Set ↥C) := (hWcomm h1).2
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 h2 u hu)
  have hXexp : ∀ x ∈ D ⊔ W', x ^ q = 1 := by
    intro x hx
    obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hDW' hx
    rw [(show Commute k l from hDW' k hk l hl).mul_pow, hDexp k hk, hW'exp l hl, one_mul]
  have hXcl : ⁅⁅D ⊔ W', D ⊔ W'⁆, D ⊔ W'⁆ = ⊥ :=
    commutator_commutator_sup_eq_bot hDW'bot hDcl hW'cl
  have hXQ : D ⊔ W' ≤ Q := sup_le hDQ hW'Q
  have hDX : D ≤ D ⊔ W' := le_sup_left
  have hRX : R ⊓ Subgroup.centralizer ((D ⊔ W' : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hRD]
    exact inf_le_inf_left R (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDX))
  have hrankX : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥((D ⊔ W') ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2 := fun r hr hr1 =>
    (OddCore37.pRank_le_of_le hq (inf_le_inf_right _ hXQ)).trans (hrank r hr hr1)
  obtain ⟨-, -, hshape⟩ := fixedRankTwo_of_order_five hET32 hq hq2 hq5 hA hAR hR hR32 ha
    (sup_le (le_normalizer_of_forall fun _ _ y hy => (inferInstance : (D ⊔ W').Normal).conj_mem
        y hy _)
      (le_normalizer_of_forall fun _ _ y hy => (inferInstance : (D ⊔ W').Normal).conj_mem
        y hy _))
    (hQp.to_le hXQ) hXexp hXcl hRX hrankX
  have hXD : D ⊔ W' = D := by
    have hcard := OddCore37.isQDShape_card hshape
    have hle : Nat.card D ≤ Nat.card ↥(D ⊔ W') := Subgroup.card_le_of_le hDX
    rcases hcard with h | h
    · exfalso
      rw [h, hDcard] at hle
      have := Nat.pow_lt_pow_right hq.one_lt (show 4 < 5 by norm_num)
      omega
    · exact (Subgroup.eq_of_le_of_card_ge hDX (by rw [h, hDcard])).symm
  have hW'D : W' ≤ D := hXD ▸ le_sup_right
  have hRW' : ∀ r ∈ R, ∀ w ∈ W', r * w * r⁻¹ = w := by
    intro r hr w hw
    have hwZ : w ∈ D ⊓ Subgroup.centralizer (D : Set G) := ⟨hW'D hw, (hW'C hw).2⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hRZ hr) w hwZ
    calc r * w * r⁻¹ = w * r * r⁻¹ := by rw [← h1]
      _ = w := by group
  have hRC : ∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ = c := by
    intro r hr c hc
    set σ : MulAut ↥C := MulAut.conjNormal (H := C) r with hσ
    have hσfix : σ ∈ fixingSubgroup (MulAut ↥C) (W : Set ↥C) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      rw [MulAut.smul_def, hσ, MulAut.conjNormal_apply]
      exact hRW' r hr y ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hWpg ⟨σ, hσfix⟩
    have hk' : σ ^ q ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨m, hm⟩ := hR.1 ⟨r, hr⟩
    have hm' : σ ^ 2 ^ m = 1 := by
      have h1 : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
      rw [hσ, ← map_pow, h1, map_one]
    have hcop : Nat.Coprime (q ^ k) (2 ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have h3 := pow_gcd_eq_one.2 ⟨hk', hm'⟩
    rw [hcop, pow_one] at h3
    have h4 := congrArg (fun f : MulAut ↥C => ((f ⟨c, hc⟩ : ↥C) : G)) h3
    simpa [hσ, MulAut.conjNormal_apply] using h4
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  calc c * r = (r * c * r⁻¹) * r := by rw [hRC r hr c hc]
    _ = r * c := by group

end CFSG.RankThree.PartOne.Torsion37
