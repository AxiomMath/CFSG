module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec11.Item116Coords
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_pow_mul_pow_of_mem_sup {c d x : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hx : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = c ^ i * d ^ j := by
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcd
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  rw [sup_comm] at hx
  have hx' : x ∈ ((Subgroup.zpowers c : Set G) * (Subgroup.zpowers d : Set G)) := by
    rw [← hcoe]
    exact hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨((m : ℤ) : ZMod 3).val, ((n : ℤ) : ZMod 3).val, ZMod.val_lt _, ZMod.val_lt _, ?_⟩
  rw [← Sec11.zpow_eq_pow_val hc3, ← Sec11.zpow_eq_pow_val hd3]

theorem zpowers_eq_mul_pow_of_mem_sup {c d b : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hb : b ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c)
    (hbD : b ∉ Subgroup.zpowers d) :
    ∃ k : ℕ, k < 3 ∧ Subgroup.zpowers b = Subgroup.zpowers (c * d ^ k) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_sup hcd hc3 hd3 hb
  have hcom : Commute c d := hcd
  interval_cases i
  · exact absurd (by rw [pow_zero, one_mul]; exact Subgroup.npow_mem_zpowers d j) hbD
  · exact ⟨j, hj, by rw [pow_one]⟩
  ·
    refine ⟨(2 * j) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    have hsq : (c ^ 2 * d ^ j) ^ 2 = c * d ^ ((2 * j) % 3) := by
      rw [(hcom.pow_pow 2 j).mul_pow, ← pow_mul, ← pow_mul,
        Sec11.pow_eq_pow_mod_three hc3 (2 * 2), Sec11.pow_eq_pow_mod_three hd3 (j * 2),
        mul_comm j 2]
      norm_num
    have h3 : (c ^ 2 * d ^ j) ^ 3 = 1 := by
      rw [(hcom.pow_pow 2 j).mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 3, pow_mul, hc3,
        mul_comm j 3, pow_mul, hd3, one_pow, one_pow, one_mul]
    rw [← hsq]
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers _ 2))
    rw [Subgroup.zpowers_le]
    have h4 : ((c ^ 2 * d ^ j) ^ 2) ^ 2 = c ^ 2 * d ^ j := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    have h5 := Subgroup.npow_mem_zpowers ((c ^ 2 * d ^ j) ^ 2) 2
    rwa [h4] at h5

theorem conj_mul_pow_of_inv {c d t : G} (hd3 : d ^ 3 = 1) (htc : t * c * t⁻¹ = c)
    (htd : t * d * t⁻¹ = d⁻¹) (k : ℕ) : t * (c * d ^ k) * t⁻¹ = c * d ^ (2 * k) := by
  have h1 : t * (c * d ^ k) * t⁻¹ = (t * c * t⁻¹) * (t * d * t⁻¹) ^ k := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow]
  rw [h1, htc, htd]
  congr 1
  have hdinv : d⁻¹ = d ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hd3]
  rw [hdinv, ← pow_mul]

theorem exists_conj_eq_zpowers {c d x t b : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hcD : c ∉ Subgroup.zpowers d)
    (hx : x ∈ Subgroup.normalizer
        ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hxH : x ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (htc : t * c * t⁻¹ = c) (htd : t * d * t⁻¹ = d⁻¹)
    (hb : b ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c) (hbD : b ∉ Subgroup.zpowers d) :
    ∃ u ∈ Subgroup.normalizer
        ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G),
      Subgroup.zpowers b = Subgroup.zpowers (u * c * u⁻¹) := by
  obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.mp hx
  have htD : (Subgroup.zpowers d).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * d * t⁻¹) = _
    rw [htd, Subgroup.zpowers_inv]
  have htC : (Subgroup.zpowers c).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * c * t⁻¹) = _
    rw [htc]
  have htU : t ∈ Subgroup.normalizer
      ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr htD⟩
    have h := congrArg₂ (· ⊔ ·) htD htC
    rwa [← Subgroup.map_sup] at h
  have hcB : c ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c :=
    (le_sup_right : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hxcB : x * c * x⁻¹ ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hxB c).mp hcB
  have hxcD : x * c * x⁻¹ ∉ Subgroup.zpowers d := by
    intro h
    apply hcD
    have := (Subgroup.mem_normalizer_iff.mp hxD c).mpr h
    exact this
  obtain ⟨k₀, hk₀, hk₀eq⟩ := zpowers_eq_mul_pow_of_mem_sup hcd hc3 hd3 hxcB hxcD
  have hk₀0 : k₀ ≠ 0 := by
    rintro rfl
    apply hxH
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * c * x⁻¹) = _
    rw [hk₀eq, pow_zero, mul_one]
  obtain ⟨k, hk, hkeq⟩ := zpowers_eq_mul_pow_of_mem_sup hcd hc3 hd3 hb hbD
  have htx : Subgroup.zpowers ((t * x) * c * (t * x)⁻¹) = Subgroup.zpowers (c * d ^ (2 * k₀)) := by
    have h1 : (t * x) * c * (t * x)⁻¹ = t * (x * c * x⁻¹) * t⁻¹ := by group
    rw [h1, ← conj_mul_pow_of_inv hd3 htc htd k₀]
    have h2 := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hk₀eq
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hd2 : ∀ m : ℕ, d ^ m = d ^ (m % 3) := Sec11.pow_eq_pow_mod_three hd3
  interval_cases k
  · exact ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩,
      by rw [hkeq, pow_zero, mul_one, one_mul, inv_one, mul_one]⟩
  · interval_cases k₀
    · exact absurd rfl hk₀0
    · exact ⟨x, hx, hkeq.trans hk₀eq.symm⟩
    · refine ⟨t * x, Subgroup.mul_mem _ htU hx, ?_⟩
      rw [htx, hkeq, hd2 (2 * 2)]
  · interval_cases k₀
    · exact absurd rfl hk₀0
    · refine ⟨t * x, Subgroup.mul_mem _ htU hx, ?_⟩
      rw [htx, hkeq]
    · exact ⟨x, hx, hkeq.trans hk₀eq.symm⟩

theorem isPGroup_three_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem pPrimeCoreOf_le_centralizer_of_isSimpleGroup [Finite G] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (hsimp : IsSimpleGroup ↥L) (h3 : 3 ∣ Nat.card L) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨L', hL', hLeq⟩ := hL
  subst hLeq
  have hUn : (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G))).Normal := inferInstance
  have e : ↥L' ≃* ↥(L'.map (Subgroup.centralizer ({c} : Set G)).subtype) :=
    L'.equivMapOfInjective _ (Subgroup.subtype_injective _)
  have h3' : 3 ∣ Nat.card L' := by rwa [Nat.card_congr e.toEquiv]
  have hsimp' : IsSimpleGroup ↥L' := e.isSimpleGroup
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hL'
      hUn.isSubnormal with hle | ⟨-, hcomm⟩
  · exfalso
    have hcop : Nat.Coprime 3
        (Nat.card (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G)))) :=
      CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
      (h3'.trans (Subgroup.card_dvd_of_le hle))
  ·
    have hθ : aschbacherSolvableCore 3 ↥L' = ⊥ := by
      obtain ⟨hsolv, -⟩ := solvable_prime_complement_core_characterization
        (H := ↥L') Nat.prime_three
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L') with h | h
      · exact h
      · exfalso
        have hperf : Group.IsPerfect ↥L' := hL'.1
        have : Group.IsSolvable ↥L' := by
          rw [h] at hsolv
          exact Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.topEquiv).symm.toMonoidHom) (MulEquiv.injective _)
        exact Group.IsPerfect.not_isSolvable ↥L' this
    have hbot : ⁅L', CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({c} : Set G))⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine hcomm.trans ?_
      rw [inSubgroup, hθ, Subgroup.map_bot]
    have hbotG : ⁅L'.map (Subgroup.centralizer ({c} : Set G)).subtype,
        pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G))⁆ = ⊥ := by
      rw [pPrimeCoreOf, ← Subgroup.map_commutator, hbot, Subgroup.map_bot]
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbotG
    exact hbotG

theorem card_pPrimeCoreOf_centralizer_eq {b c u : G}
    (h : Subgroup.zpowers b = Subgroup.zpowers (u * c * u⁻¹)) :
    Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) =
      Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G))) := by
  rw [centralizer_singleton_eq_of_zpowers_eq h]
  have h1 := map_pPrimeCoreOf 3 (MulAut.conj u) (Subgroup.centralizer ({c} : Set G))
  rw [map_centralizer_singleton] at h1
  change Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({(MulAut.conj u) c} : Set G))) = _
  rw [← h1, Subgroup.card_map_of_injective (MulAut.conj u).injective]

theorem exists_conj_le_inf_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {Q A : Subgroup G}
    (hQ : IsPGroup p Q) (hAQ : A ≤ Q) {y : G} (hyQ : A.map (MulAut.conj y).toMonoidHom ≤ Q)
    (hne : A.map (MulAut.conj y).toMonoidHom ≠ A) :
    ∃ z : G, (z = y ∨ z ∈ Q) ∧
      A.map (MulAut.conj z).toMonoidHom ≤ Q ⊓ Subgroup.normalizer (A : Set G) ∧
      A.map (MulAut.conj z).toMonoidHom ≠ A := by
  by_cases hN : A.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (A : Set G)
  · exact ⟨y, Or.inl rfl, le_inf hyQ hN, hne⟩
  set T := A ⊔ A.map (MulAut.conj y).toMonoidHom with hT
  have hTQ : T ≤ Q := sup_le hAQ hyQ
  have hTp : IsPGroup p ↥T := hQ.to_le hTQ
  have : Group.IsNilpotent ↥T := hTp.isNilpotent
  set H : Subgroup ↥T := (Subgroup.normalizer (A : Set G)).subgroupOf T with hH
  have hHt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hN
    intro x hx
    have hxT : x ∈ T := (le_sup_right : _ ≤ T) hx
    have : (⟨x, hxT⟩ : ↥T) ∈ H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hlt := Group.normalizerCondition_of_isNilpotent H hHt
  obtain ⟨z, hzN, hzH⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨z, Or.inr (hTQ z.2), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have haT : a ∈ T := (le_sup_left : A ≤ T) ha
    have haH : (⟨a, haT⟩ : ↥T) ∈ H :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer ha)
    have hmem := (Subgroup.mem_normalizer_iff.mp hzN ⟨a, haT⟩).mp haH
    have hval : ((z * ⟨a, haT⟩ * z⁻¹ : ↥T) : G) = (MulAut.conj (z : G)).toMonoidHom a := by
      simp [MulAut.conj_apply]
    rw [← hval]
    exact ⟨hTQ (z * ⟨a, haT⟩ * z⁻¹).2, Subgroup.mem_subgroupOf.mp hmem⟩
  · intro heq
    exact hzH (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq))

theorem mul_inv_mem_of_fixes [Finite G] {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hB : IsHyperplane A B) {σ : MulAut ↥A} {k : ℕ} (hσ : σ ^ (3 ^ k) = 1)
    (hfix : ∀ x : ↥A, (x : G) ∈ B → σ x = x) (a : ↥A) : ((σ a * a⁻¹ : ↥A) : G) ∈ B := by
  have hcomm : ∀ x y : ↥A, x * y = y * x := fun x y => hA.1.is_comm.comm x y
  have h3 : ∀ x : ↥A, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hA.2 x x.2)
  by_contra hn
  have haB : (a : G) ∉ B := by
    intro h
    apply hn
    rw [hfix a h, mul_inv_cancel]
    exact B.one_mem
  have hAa : A = Subgroup.zpowers (a : G) ⊔ B :=
    le_antisymm (le_zpowers_sup_of_not_mem hB a.2 haB)
      (sup_le (Subgroup.zpowers_le.mpr a.2) hB.1)
  have hdec : ∀ x : ↥A, ∃ j : ℕ, ∃ b : ↥A, (b : G) ∈ B ∧ x = a ^ j * b := by
    intro x
    obtain ⟨j, -, b, hb, hxb⟩ := exists_pow_mul_of_mem hA a.2 hAa x.2
    refine ⟨j, ⟨b, hB.1 hb⟩, hb, Subtype.ext ?_⟩
    rw [hxb]
    simp
  obtain ⟨i, hi, b, hb, hσa⟩ := exists_pow_mul_of_mem hA a.2 hAa (σ a).2
  set b' : ↥A := ⟨b, hB.1 hb⟩ with hb'
  have hσa' : σ a = a ^ i * b' := Subtype.ext (by rw [hσa]; simp [hb'])
  interval_cases i
  ·
    apply haB
    have h1 : σ a = σ b' := by rw [hσa', pow_zero, one_mul, hfix b' hb]
    rw [σ.injective h1]
    exact hb
  · apply hn
    rw [hσa', pow_one, hcomm a b', mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  ·
    have hσ2a : (σ ^ 2) a = a := by
      rw [pow_two, MulAut.mul_apply, hσa', map_mul, map_pow, hσa', hfix b' hb]
      calc (a ^ 2 * b') ^ 2 * b' = a ^ 4 * b' ^ 3 := by
            rw [(Commute.mul_pow (hcomm (a ^ 2) b') 2), ← pow_mul, pow_succ b' 2, mul_assoc]
        _ = a := by
            rw [h3 b', mul_one, show 4 = 3 + 1 by norm_num, pow_succ, h3 a, one_mul]
    have hσ2 : σ ^ 2 = 1 := by
      ext x
      obtain ⟨j, c, hc, rfl⟩ := hdec x
      rw [map_mul, map_pow, hσ2a, pow_two, MulAut.mul_apply, hfix c hc, hfix c hc]
      rfl
    have hodd : 3 ^ k = 2 * (3 ^ k / 2) + 1 := by
      have h2 : 3 ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
      omega
    have hσ1 : σ = 1 := by
      rw [hodd, pow_succ, pow_mul, hσ2, one_pow, one_mul] at hσ
      exact hσ
    apply hn
    rw [hσ1, MulAut.one_apply, mul_inv_cancel]
    exact B.one_mem

theorem le_normalizer_of_hyperplane_le [Finite G] {A E B : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hB : IsHyperplane A B) (hBE : B ≤ E) (hEA : E ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer (E : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ E, a * y * a⁻¹ ∈ E := by
    intro a ha y hy
    set σ := A.normalizerMonoidHom ⟨y, hEA hy⟩ with hσ
    have hσ3 : σ ^ (3 ^ 1) = 1 := by
      rw [pow_one, hσ, ← map_pow]
      have : (⟨y, hEA hy⟩ : Subgroup.normalizer (A : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hE.2 y hy)
      rw [this, map_one]
    have hfix : ∀ x : ↥A, (x : G) ∈ B → σ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hσ, normalizerMonoidHom_apply_val]
      have hxy : (x : G) * y = y * x :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hBE hx⟩ ⟨y, hy⟩)
      rw [← hxy, mul_inv_cancel_right]
    have hmem := mul_inv_mem_of_fixes hA hB hσ3 hfix ⟨a, ha⟩
    rw [Subgroup.coe_mul, hσ, normalizerMonoidHom_apply_val, Subgroup.coe_inv] at hmem
    have heq : a * y * a⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ * y := by group
    rw [heq]
    exact E.mul_mem (E.inv_mem (hBE hmem)) hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key a ha y
  · intro hy
    have h1 := key a⁻¹ (A.inv_mem ha) _ hy
    simpa [mul_assoc] using h1

end CFSG.RankThree.PartTwo.Sec16.Proof1613
