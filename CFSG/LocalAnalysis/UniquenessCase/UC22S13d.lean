module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.Milestones.ASVolI.A3Aut.L2
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal equivalence)

theorem uc22s13d_conjNormal_eq_one_iff {Q : Type*} [Group Q] {J : Subgroup Q} [J.Normal]
    {q : Q} : MulAut.conjNormal (H := J) q = 1 ↔ q ∈ centralizer (J : Set Q) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro j hj
    have h1 : q * j * q⁻¹ = j := by
      simpa using congrArg (fun f : MulAut ↥J => (f ⟨j, hj⟩ : Q)) h
    calc j * q = q * j * q⁻¹ * q := by rw [h1]
      _ = q * j := inv_mul_cancel_right _ _
  · intro h
    refine MulEquiv.ext fun j => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have h1 : (j : Q) * q = q * j := mem_centralizer_iff.1 h j j.2
    calc q * j * q⁻¹ = j * q * q⁻¹ := by rw [h1]
      _ = j := mul_inv_cancel_right _ _

theorem uc22s13d_commutator_le_centralizer {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q)
    [J.Normal] (hOut : ∀ σ τ : MulAut ↥J, ∃ y : ↥J, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y)
    {x : Q} (hxJ : x ∈ J)
    (hC : ∀ a ∈ J, ∀ b ∈ J, a * x = x * a → b * x = x * b → a * b = b * a) :
    ⁅⁅centralizer ({x} : Set Q), centralizer ({x} : Set Q)⁆,
        ⁅centralizer ({x} : Set Q), centralizer ({x} : Set Q)⁆⁆ ≤
      centralizer (J : Set Q) := by
  set C := centralizer ({x} : Set Q)
  have hQ := PartTwo.s13_commutator_le_sup_centralizer J hOut
  have h1 : ⁅C, C⁆ ≤ (J ⊓ C) ⊔ centralizer (J : Set Q) := by
    rw [commutator_le]
    intro c₁ hc₁ c₂ hc₂
    have hmem : ⁅c₁, c₂⁆ ∈ J ⊔ centralizer (J : Set Q) := hQ (by
      rw [commutator_def]
      exact commutator_mem_commutator (mem_top c₁) (mem_top c₂))
    obtain ⟨j, hj, z, hz, hjz⟩ := mem_sup_of_normal_left.1 hmem
    have hcC : ⁅c₁, c₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
    have hzC : z ∈ C := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hz x hxJ).symm
    have hjC : j ∈ C := by
      have hj' : j = ⁅c₁, c₂⁆ * z⁻¹ := by rw [← hjz, mul_inv_cancel_right]
      rw [hj']
      exact C.mul_mem hcC (C.inv_mem hzC)
    rw [← hjz]
    exact mul_mem_sup ⟨hj, hjC⟩ hz
  have h2 : ⁅(J ⊓ C) ⊔ centralizer (J : Set Q), (J ⊓ C) ⊔ centralizer (J : Set Q)⁆ ≤
      centralizer (J : Set Q) := by
    rw [commutator_le]
    intro s₁ hs₁ s₂ hs₂
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := mem_sup_of_normal_right.1 hs₁
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := mem_sup_of_normal_right.1 hs₂
    rw [← uc22s13d_conjNormal_eq_one_iff (J := J)]
    have hz₁' := uc22s13d_conjNormal_eq_one_iff.2 hz₁
    have hz₂' := uc22s13d_conjNormal_eq_one_iff.2 hz₂
    have hj : ⁅j₁, j₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (hC j₁ hj₁.1 j₂ hj₂.1 (mem_centralizer_singleton_iff.1 hj₁.2)
        (mem_centralizer_singleton_iff.1 hj₂.2))
    calc MulAut.conjNormal (H := J) ⁅j₁ * z₁, j₂ * z₂⁆ =
        ⁅MulAut.conjNormal (H := J) j₁ * MulAut.conjNormal (H := J) z₁,
          MulAut.conjNormal (H := J) j₂ * MulAut.conjNormal (H := J) z₂⁆ := by
          rw [map_commutatorElement, map_mul, map_mul]
      _ = MulAut.conjNormal (H := J) ⁅j₁, j₂⁆ := by
          rw [hz₁', hz₂', mul_one, mul_one, map_commutatorElement]
      _ = 1 := by rw [hj, map_one]
  exact (commutator_mono h1 h1).trans h2

theorem uc22s13d_mem_centralizer_of_two {Q : Type*} [Group Q] (J : Subgroup Q) [J.Normal]
    (hZ : ∀ z ∈ J, (∀ j ∈ J, z * j = j * z) → z = 1)
    (hInn : ∀ β : MulAut ↥J, ∀ k : ℕ, β ^ (2 ^ k) = 1 →
      β ∈ (MulAut.conj : ↥J →* MulAut ↥J).range)
    {x : Q} (hxJ : x ∈ J) (hC2 : ∀ a ∈ J, a * x = x * a → ∀ k : ℕ, a ^ (2 ^ k) = 1 → a = 1)
    {t : Q} (htx : t * x = x * t) {k : ℕ} (htk : t ^ (2 ^ k) = 1) :
    t ∈ centralizer (J : Set Q) := by
  rw [← uc22s13d_conjNormal_eq_one_iff (J := J)]
  have hβ : MulAut.conjNormal (H := J) t ^ (2 ^ k) = 1 := by rw [← map_pow, htk, map_one]
  obtain ⟨j₀, hj₀⟩ := hInn _ k hβ
  have hj₀x : (j₀ : Q) * x = x * j₀ := by
    have h1 := congrArg (fun f : MulAut ↥J => (f ⟨x, hxJ⟩ : Q)) hj₀
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    have h2 : t * x * t⁻¹ = x := by rw [htx, mul_inv_cancel_right]
    rw [h2] at h1
    calc (j₀ : Q) * x = (j₀ : Q) * x * (j₀ : Q)⁻¹ * j₀ := (inv_mul_cancel_right _ _).symm
      _ = x * j₀ := by rw [h1]
  have hj₀k : (j₀ : Q) ^ (2 ^ k) = 1 := by
    refine hZ _ (J.pow_mem j₀.2 _) fun j hj => ?_
    have h1 : MulAut.conj (j₀ ^ (2 ^ k)) = 1 := by rw [map_pow, hj₀, hβ]
    have h2 := congrArg (fun f : MulAut ↥J => (f ⟨j, hj⟩ : Q)) h1
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow,
      MulAut.one_apply] at h2
    calc (j₀ : Q) ^ (2 ^ k) * j =
        (j₀ : Q) ^ (2 ^ k) * j * ((j₀ : Q) ^ (2 ^ k))⁻¹ * (j₀ : Q) ^ (2 ^ k) :=
          (inv_mul_cancel_right _ _).symm
      _ = j * (j₀ : Q) ^ (2 ^ k) := by rw [h2]
  have hj₀1 : j₀ = 1 := Subtype.ext (hC2 _ j₀.2 hj₀x k hj₀k)
  rw [← hj₀, hj₀1, map_one]

theorem uc22s13d_center {Q : Type*} [Group Q] {J : Subgroup Q} (hs : IsSimpleGroup ↥J)
    (hna : ∃ a b : ↥J, a * b ≠ b * a) : ∀ z ∈ J, (∀ j ∈ J, z * j = j * z) → z = 1 := by
  intro z hz hzc
  have hc : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center ↥J := by rw [h]; exact mem_top a
      exact absurd ((mem_center_iff.1 ha b).symm) hab
  have hzc' : (⟨z, hz⟩ : ↥J) ∈ Subgroup.center ↥J :=
    mem_center_iff.2 fun j => Subtype.ext (hzc j j.2).symm
  rw [hc, mem_bot] at hzc'
  exact congrArg Subtype.val hzc'

theorem uc22s13d_out_mem_of_mem_sup {Y H : Type*} [Group Y] [Group H] (φ : H →* MulAut Y)
    (hI : (MulAut.conj : Y →* MulAut Y).range ⊓ φ.range = ⊥) {m : ℕ}
    (hm : Nat.Coprime m (Nat.card H)) {α : MulAut Y}
    (hmem : α ∈ (MulAut.conj : Y →* MulAut Y).range ⊔ φ.range) (hα : α ^ m = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  haveI : (MulAut.conj : Y →* MulAut Y).range.Normal := inner_normal Y
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨y, hy, z, ⟨h, rfl⟩, rfl⟩ := Set.mem_mul.1 hmem
  have h1 : φ h ^ m ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have h2 := congrArg (QuotientGroup.mk (s := (MulAut.conj : Y →* MulAut Y).range)) hα
    rwa [QuotientGroup.mk_pow, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul,
      QuotientGroup.mk_one] at h2
  have h3 : φ h ^ m = 1 := by
    have h4 : φ h ^ m ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ φ.range :=
      ⟨h1, h ^ m, map_pow φ h m⟩
    rwa [hI, Subgroup.mem_bot] at h4
  have h5 : orderOf (φ h) ∣ Nat.card H := (orderOf_map_dvd φ h).trans (orderOf_dvd_natCard h)
  rw [orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hm (orderOf_dvd_of_pow_eq_one h3) h5),
    mul_one]
  exact hy

theorem uc22s13d_out_mem_of_card_dvd {X : Type*} [Group X] {m m' : ℕ}
    (hm : Nat.card (Outer X) ∣ m') (hcop : Nat.Coprime m m') {α : MulAut X} (hα : α ^ m = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  set a : Outer X := (α : MulAut X ⧸ inner X) with ha
  have h1 : orderOf a ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [ha, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf a ∣ m' := (orderOf_dvd_natCard a).trans hm
  exact (QuotientGroup.eq_one_iff α).1
    (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

theorem uc22s13d_out_mem_of_isPGroup {X : Type*} [Group X] (hP : IsPGroup 2 (Outer X)) {m : ℕ}
    (hm : Odd m) {α : MulAut X} (hα : α ^ m = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  set a : Outer X := (α : MulAut X ⧸ inner X) with ha
  obtain ⟨k, hk⟩ := hP a
  have h1 : orderOf a ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [ha, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).symm h1 h2))

theorem uc22s13d_inner_of_two {T : Type} [Group T] {n : ℕ}
    (hT : IsL2 T n ∨ IsSz T n) (hn : Odd n) (β : MulAut T) {k : ℕ} (hβ : β ^ (2 ^ k) = 1) :
    β ∈ (MulAut.conj : T →* MulAut T).range := by
  have hcop : ∀ m : ℕ, Odd m → Nat.Coprime (2 ^ k) m := fun m hm =>
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  rcases hT with hL2 | hSz
  · obtain ⟨-, F, _, _, hF, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hL2
    refine uc22p2214_out_mem_of_congr e (uc22s13d_out_mem_of_mem_sup
      (CFSG.GorensteinWalter.psl2FieldAut F) CFSG.ASVolI.burnsideAut_psl2_inn_inf_field ?_
      (CFSG.ASVolI.burnsideAut_psl2_aut_mem _) (by rw [← map_pow, hβ, map_one]))
    rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF).1]
    exact hcop n hn
  · obtain ⟨-, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hSz
    refine uc22s13d_out_mem_of_card_dvd ?_ (hcop _ hn) hβ
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2

theorem uc22s13d_cent {T : Type} [Group T] {n : ℕ}
    (hT : IsL2 T n ∨ IsSz T n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    {x : T} (hx : orderOf x = r) :
    (∀ a b : T, a * x = x * a → b * x = x * b → a * b = b * a) ∧
      ∀ a : T, a * x = x * a → ∀ k : ℕ, a ^ (2 ^ k) = 1 → a = 1 := by
  rcases hT with hL2 | hSz
  · obtain ⟨hn2, F, _, _, hF, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hL2
    have hx1 : e x ≠ 1 := by
      intro h
      rw [(map_eq_one_iff e e.injective).1 h, orderOf_one] at hx
      exact hr.one_lt.ne hx
    have hxo : Odd (orderOf (e x)) := by
      rw [MulEquiv.orderOf_eq, hx]
      exact hr.odd_of_ne_two hr2
    obtain ⟨hcyc, hcard, -⟩ :=
      CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer n hn2 hF
        (e x) hx1 hxo
    have hmem : ∀ a : T, a * x = x * a → e a ∈ centralizer ({e x} : Set _) := by
      intro a ha
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ha]
    have heven : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    have hodd : Odd (Nat.card (centralizer ({e x} : Set _))) := by
      rcases hcard with h | h <;> rw [h, hF]
      · exact Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
      · exact heven.add_odd odd_one
    refine ⟨fun a b ha hb => e.injective ?_, fun a ha k hak => e.injective ?_⟩
    · haveI := hcyc
      have h1 := IsMulCommutative.is_comm.comm (⟨e a, hmem a ha⟩ : centralizer ({e x} : Set _))
        ⟨e b, hmem b hb⟩
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
    · have h1 : orderOf (e a) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hak, map_one])
      have h2 : orderOf (e a) ∣ Nat.card (centralizer ({e x} : Set _)) := by
        have h3 := orderOf_dvd_natCard (⟨e a, hmem a ha⟩ : centralizer ({e x} : Set _))
        rwa [Subgroup.orderOf_mk] at h3
      rw [orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)) h1 h2), map_one]
  · obtain ⟨-, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hSz
    have hxo : orderOf (e x) = r := by rw [MulEquiv.orderOf_eq, hx]
    obtain ⟨⟨g, hg⟩, hcomm⟩ :=
      (CFSG.LieType.Ree.suzuki_split_torus_odd_prime_centralizers hK).2 r hr hr2 hrn (e x) hxo
    have hmem : ∀ b : T, b * x = x * b → e b ∈ centralizer ({e x} : Set _) := by
      intro b hb
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hb]
    have hcard : Nat.card (centralizer ({e x} : Set _)) = 2 ^ (2 * a + 1) - 1 := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact (CFSG.LieType.Ree.suzuki_borel_structure hK).2.2.1
    have hodd : Odd (Nat.card (centralizer ({e x} : Set _))) := by
      rw [hcard]
      exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two) odd_one
    refine ⟨fun b c hb hc => e.injective ?_, fun b hb k hbk => e.injective ?_⟩
    · rw [map_mul, map_mul]
      exact hcomm _ (hmem b hb) _ (hmem c hc)
    · have h1 : orderOf (e b) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hbk, map_one])
      have h2 : orderOf (e b) ∣ Nat.card (centralizer ({e x} : Set _)) := by
        have h3 := orderOf_dvd_natCard (⟨e b, hmem b hb⟩ : centralizer ({e x} : Set _))
        rwa [Subgroup.orderOf_mk] at h3
      rw [orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)) h1 h2), map_one]

theorem uc22s13d_exists_odd_prime {F : Type*} [Group F] [Finite F] [Nontrivial F]
    [Group.IsPerfect F] : ∃ z : F, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf z = q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, hqd, hq2⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card F ∧ q ≠ 2 := by
    by_contra h
    push_neg at h
    have hcard : Nat.card F = 2 ^ (Nat.card F).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdd => h _ hd hdd
    exact Group.IsPerfect.not_isNilpotent F (IsPGroup.of_card hcard).isNilpotent
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqd
  exact ⟨z, q, hq, hq2, hz⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
