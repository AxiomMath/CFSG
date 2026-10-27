module

public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofModel
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofLift
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.L3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem exists_rank_three_centralizer {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hnq : ¬ IsQuasisimple X) (hO2 : CFSG.pCore 2 X = ⊥)
    (hO : IsQuasisimple (X ⧸ CFSG.oddCore X))
    (hbar : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X)) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hL : Sec4.IsoLThreePi (X ⧸ aschbacherSolvableCore 3 X) p e) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ ∃ t : X, orderOf t = 2 ∧
      ∃ P : Subgroup X, P ≤ Subgroup.centralizer {t} ∧ 3 ≤ CFSG.pRank r P := by
  classical
  set θ := aschbacherSolvableCore 3 X with hθdef
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθs : Group.IsSolvable θ := hθ.1
  have hθ3 : ¬ 3 ∣ Nat.card θ := hθ.2.2.1
  obtain ⟨hsimp, hZbar, -, -⟩ := typeFacts135_isoLThreePi he hbar hL
  have : IsSimpleGroup (X ⧸ θ) := hsimp
  set π : X →* X ⧸ θ := QuotientGroup.mk' θ with hπ
  have hπker : ∀ x : X, π x = 1 ↔ x ∈ θ := fun x => QuotientGroup.eq_one_iff x
  obtain ⟨X₁, X₂, N₁, N₂, h12, h13, h23, h9, hF1, hF2, hN1, hN2, hC⟩ :=
    exists_heis_data_of_isoLThreePi he hL
  set B : Subgroup (X ⧸ θ) := Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ with hB
  have hBel : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_zpowers_sup h13 h23 h12
  have hX₁1 : X₁ ≠ 1 := by
    intro h
    have hle : B ≤ Subgroup.zpowers X₂ := by
      rw [hB, h, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
    have h3 : Nat.card (Subgroup.zpowers X₂) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) h23
    have h9' : Nat.card B = 9 := h9
    have := (Subgroup.card_le_of_le hle).trans h3
    omega
  obtain ⟨S, -, hSel, -, hSB⟩ := exists_elemAbelian_map_eq (M := ⊤) hBel (by
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact le_top)
  have hX₁S : X₁ ∈ S.map π := by
    rw [hSB]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)
  have hX₂S : X₂ ∈ S.map π := by
    rw [hSB]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
  obtain ⟨y₁, hy₁S, hy₁⟩ := hX₁S
  obtain ⟨y₂, hy₂S, hy₂⟩ := hX₂S
  have hy12 : y₁ * y₂ = y₂ * y₁ := mul_comm_of_mem hSel.1 hy₁S hy₂S
  have hy13 : y₁ ^ 3 = 1 := hSel.2 y₁ hy₁S
  have hy23 : y₂ ^ 3 = 1 := hSel.2 y₂ hy₂S
  set E : Subgroup X := Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ with hE
  have hES : E ≤ S := sup_le (Subgroup.zpowers_le.mpr hy₁S) (Subgroup.zpowers_le.mpr hy₂S)
  have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hSel.2 g g.2)⟩
  have hEp : IsPGroup 3 E := hSp.to_le hES
  have hEB : E.map π = B := by
    rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hy₁, hy₂]
  have hinj : Set.InjOn π E := injOn_mk_of_isPGroup Nat.prime_three hEp
  have hE9 : Nat.card E = 9 := by
    rw [← card_map_eq_of_injOn π hinj, hEB, h9]
  have hy₁E : y₁ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  have hy₂E : y₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  have hNB : ∀ n : X ⧸ θ, n * X₁ * n⁻¹ ∈ B → n * X₂ * n⁻¹ ∈ B →
      ∃ m ∈ Subgroup.normalizer (E : Set X), π m = n := by
    intro n hn1 hn2
    have hn : n ∈ Subgroup.normalizer ((E.map π : Subgroup (X ⧸ θ)) : Set (X ⧸ θ)) := by
      rw [hEB]
      exact mem_normalizer_sup_of_conj h12 hn1 hn2
    rw [normalizer_map_mk_eq hEp] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    exact ⟨m, hm, hmn⟩
  have hX₁B : X₁ ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)
  have hX₂B : X₂ ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
  obtain ⟨m₁, hm₁N, hm₁⟩ := hNB N₁ (by rw [hF1]; exact B.inv_mem hX₂B) (by rw [hF2]; exact hX₁B)
  obtain ⟨m₂, hm₂N, hm₂⟩ := hNB N₂
    (by rw [hN1]; exact B.mul_mem (B.inv_mem hX₂B) (B.inv_mem hX₁B))
    (by rw [hN2]; exact B.mul_mem (B.mul_mem hX₁B hX₂B) hX₁B)
  have hconjE : ∀ {m y : X}, m ∈ Subgroup.normalizer (E : Set X) → y ∈ E → m * y * m⁻¹ ∈ E :=
    fun hm hy => (Subgroup.mem_normalizer_iff.mp hm _).mp hy
  have hrel : ∀ {m y z : X}, m ∈ Subgroup.normalizer (E : Set X) → y ∈ E → z ∈ E →
      π m * π y * (π m)⁻¹ = π z → m * y * m⁻¹ = z := by
    intro m y z hm hy hz h
    refine hinj (hconjE hm hy) hz ?_
    rw [map_mul, map_mul, map_inv]
    exact h
  have hG1 : m₁ * y₁ * m₁⁻¹ = y₂⁻¹ :=
    hrel hm₁N hy₁E (E.inv_mem hy₂E) (by rw [hm₁, hy₁, hF1, map_inv, hy₂])
  have hG2 : m₁ * y₂ * m₁⁻¹ = y₁ := hrel hm₁N hy₂E hy₁E (by rw [hm₁, hy₂, hF2, hy₁])
  have hG3 : m₂ * y₁ * m₂⁻¹ = y₂⁻¹ * y₁⁻¹ :=
    hrel hm₂N hy₁E (E.mul_mem (E.inv_mem hy₂E) (E.inv_mem hy₁E))
      (by rw [hm₂, hy₁, hN1, map_mul, map_inv, map_inv, hy₁, hy₂])
  have hG4 : m₂ * y₂ * m₂⁻¹ = y₁ * y₂ * y₁ :=
    hrel hm₂N hy₂E (E.mul_mem (E.mul_mem hy₁E hy₂E) hy₁E)
      (by rw [hm₂, hy₂, hN2, map_mul, map_mul, hy₁, hy₂])
  have htr : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (E : Set X), n * x * n⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨n, hn, hny⟩ := Sec4.transitive_of_q8 (M := ⊤) hy12 hy13 hy23 hG1 hG2 hG3 hG4
      (Subgroup.mem_top _) (Subgroup.mem_top _) x hx hx1 y hy hy1
    exact ⟨n, (Subgroup.mem_inf.mp hn).2, hny⟩
  have hOθ : CFSG.oddCore X ≤ θ := oddCore_le_of_isQuasisimple hθs hO
  have hZO := center_quotient_oddCore_eq_map hθs hZbar hO hOθ
  have hZ : ∀ T : Subgroup X, IsPGroup 2 T → ∀ k ∈ T, k * y₁ = y₁ * k → k * y₂ = y₂ * k →
      ∀ s ∈ T, k * s = s * k := by
    intro T hT k hk hk1 hk2 s hs
    have h3 : (π k) ^ 3 = 1 := hC (π k) (by rw [← hy₁, ← map_mul, ← map_mul, hk1])
      (by rw [← hy₂, ← map_mul, ← map_mul, hk2])
    obtain ⟨n, hn⟩ := hT ⟨k, hk⟩
    have hkn : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hkθ : k ∈ θ := by
      rw [← hπker]
      have hd1 : orderOf (π k) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hd2 : orderOf (π k) ∣ 2 ^ n :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hkn, map_one])
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by norm_num)) hd1 hd2)
    have hcen : QuotientGroup.mk' (CFSG.oddCore X) k ∈
        Subgroup.center (X ⧸ CFSG.oddCore X) := by
      rw [hZO]
      exact ⟨k, hkθ, rfl⟩
    have hw : (k * s)⁻¹ * (s * k) ∈ CFSG.oddCore X := by
      have h := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk' (CFSG.oddCore X) s)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h
      have h' := Subgroup.inv_mem _ h
      simpa using h'
    have hwT : (k * s)⁻¹ * (s * k) ∈ T := T.mul_mem (T.inv_mem (T.mul_mem hk hs)) (T.mul_mem hs hk)
    obtain ⟨m, hm⟩ := hT ⟨_, hwT⟩
    have hwm : ((k * s)⁻¹ * (s * k)) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hd1 : orderOf ((k * s)⁻¹ * (s * k)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hwm
    have hd2 : orderOf ((k * s)⁻¹ * (s * k)) ∣ Nat.card (CFSG.oddCore X) := by
      rw [← Subgroup.orderOf_mk _ hw]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ m) (Nat.card (CFSG.oddCore X)) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (CFSG.ABGDGroups.odd_card_oddCore X))
    have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    rw [inv_mul_eq_one] at h1
    exact h1
  obtain ⟨t, ht2, ht₁, ht₂⟩ := exists_involution_of_q8 hy12 hy13 hy23 hG1 hG2 hG3 hG4 hZ
  have hy₁θ : y₁ ∉ θ := fun h => hX₁1 (by rw [← hy₁]; exact (hπker y₁).mpr h)
  obtain ⟨r, hr, z, hz, hzy⟩ := exists_pCore_not_commute hθs hnq hy₁θ
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzy (by rw [one_mul, mul_one])
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [hO2, Subgroup.mem_bot] at hz
    exact hz1 hz
  have hr3 : r ≠ 3 := by
    rintro rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hsol : Group.IsSolvable (CFSG.pCore 3 X) := by
      have := (CFSG.pCore_isPGroup (p := 3) (G := X)).isNilpotent
      infer_instance
    have hle : CFSG.pCore 3 X ≤ θ :=
      Sec4.Census.le_of_isSolvable_of_normal inferInstance hsol
    have hzθ : z ∈ θ := hle hz
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 3 (CFSG.pCore 3 X)) ⟨z, hz⟩
    have hzn : z ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd1 : orderOf z ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hzn
    have hd2 : orderOf z ∣ Nat.card θ := by
      rw [← Subgroup.orderOf_mk _ hzθ]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ n) (Nat.card θ) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    exact hz1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2))
  have hr3' : 3 < r := by
    have := hr.two_le
    omega
  have : Fact r.Prime := ⟨hr⟩
  have hPne : CFSG.pCore r X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hz
    exact hz1 hz
  obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt hr2 hPne
  have hne : ∃ e ∈ E, ∃ y ∈ CFSG.pCore r X, e * y * e⁻¹ ≠ y := by
    refine ⟨y₁, hy₁E, z, hz, fun h => hzy ?_⟩
    calc z * y₁ = y₁ * z * y₁⁻¹ * y₁ := by rw [h]
      _ = y₁ * z := by group
  have hrank := three_le_pRank_inf_centralizer hr2 hr3 hD hy12 hy13 hy23 hE9 ht2 ht₁ ht₂ htr
    hne
  have ht1 : t ≠ 1 := by
    rintro rfl
    have hy1 : y₁ = y₁⁻¹ := by simpa using ht₁
    have hy1' : y₁ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hy1]; exact mul_inv_cancel y₁
    have : y₁ = 1 := by
      calc y₁ = y₁ ^ 3 * (y₁ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hy13, hy1', inv_one, one_mul]
    exact hy₁θ (this ▸ θ.one_mem)
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  exact ⟨r, hr, hr3', t, hto, D ⊓ Subgroup.centralizer {t}, inf_le_right, hrank⟩

end CFSG.RankThree.PartTwo.Sec13.L3Proof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item135SimpleL3 : Item135SimpleL3 := by
  intro G _ _ A c L hD hnq hO2 _hm hO hL3
  obtain ⟨p, e, hp, -, he, hL⟩ := hL3
  have hLc := hD.mem_thetaComponentsAt
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hnq' : ¬ IsQuasisimple L := fun hq => hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientBot (G := L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO2).symm) hq)
  obtain ⟨r, hr, hr3, t, ht, P, hPt, hP⟩ :=
    L3Proof.exists_rank_three_centralizer hnq' hO2 hO hbar he hL
  have hcomm : ∀ h ∈ P.map L.subtype, h * (t : G) = (t : G) * h := by
    rintro _ ⟨x, hx, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hPt hx)
    exact congrArg Subtype.val h
  have hloc := Sec4.Census.pRank_le_localRank_of_centralizes hr (by omega)
    (H := P.map L.subtype) (t := (t : G)) (by rw [Subgroup.orderOf_coe]; exact ht) hcomm
  have hrank : CFSG.pRank r (P.map L.subtype) = CFSG.pRank r P :=
    pRank_congr_mulEquiv hr.one_lt (P.equivMapOfInjective _ L.subtype_injective).symm
  have hlt := hD.localRank_lt r hr hr3
  omega

end CFSG.RankThree.PartTwo.Sec13
