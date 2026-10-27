module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartOne.K1327.Trick
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec13.Item13GL
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

namespace Proof15Res4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_le_closure {V : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) :
    ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.closure {x | ∃ v ∈ V, x = ⁅v, c⁆} := by
  rw [Subgroup.commutator_le]
  intro v hv g hg
  rcases eq_of_mem_zpowers_of_pow_three hc3 hg with rfl | rfl | rfl
  · rw [commutatorElement_one_right]
    exact one_mem _
  · exact Subgroup.subset_closure ⟨v, hv, rfl⟩
  · have e : ⁅v, c ^ 2⁆ = ⁅v, c⁆ * ⁅c * v * c⁻¹, c⁆ := by
      simp only [commutatorElement_def, pow_two]
      group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨v, hv, rfl⟩)
      (Subgroup.subset_closure ⟨c * v * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcV v).mp hv, rfl⟩)

theorem mem_commutator_of_fixed {R : Type*} [Group R] [Finite R] (φ : R →* R)
    (hgen : Subgroup.closure {x | ∃ r : R, x = r * (φ r)⁻¹} = ⊤) {r : R} (hr : φ r = r) :
    r ∈ commutator R := by
  set Ψ : R →* Abelianization R := Abelianization.of / Abelianization.of.comp φ with hΨ
  have hΨapp : ∀ s : R, Ψ s = Abelianization.of (s * (φ s)⁻¹) := fun s => by
    simp [hΨ, div_eq_mul_inv]
  have hsurj : Function.Surjective Ψ := by
    intro m
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective m
    have hy : y ∈ Subgroup.closure {x | ∃ r : R, x = r * (φ r)⁻¹} := hgen ▸ Subgroup.mem_top y
    have key : Abelianization.of y ∈ Ψ.range := by
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        exact ⟨s, hΨapp s⟩
      | one => rw [map_one]; exact one_mem _
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      | inv x _ hx => rw [map_inv]; exact inv_mem hx
    obtain ⟨s, hs⟩ := key
    exact ⟨s, hs⟩
  set ψ : Abelianization R →* Abelianization R := Abelianization.lift Ψ with hψ
  have hψs : Function.Surjective ψ := by
    intro m
    obtain ⟨s, hs⟩ := hsurj m
    exact ⟨Abelianization.of s, by rw [hψ, Abelianization.lift_apply_of, hs]⟩
  have hψi : Function.Injective ψ := Finite.injective_iff_surjective.mpr hψs
  have h1 : ψ (Abelianization.of r) = 1 := by
    rw [hψ, Abelianization.lift_apply_of, hΨapp, hr, mul_inv_cancel, map_one]
  have h2 : Abelianization.of r = 1 := hψi (h1.trans ψ.map_one.symm)
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact h2

theorem inf_centralizer_le_map_commutator {V : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) (hVc : ⁅V, Subgroup.zpowers c⁆ = V) :
    V ⊓ Subgroup.centralizer ({c} : Set G) ≤ (commutator ↥V).map V.subtype := by
  set φ : ↥V →* ↥V := (V.normalizerMonoidHom ⟨c, hcV⟩).toMonoidHom with hφ
  have hφapp : ∀ v : ↥V, ((φ v : ↥V) : G) = c * v * c⁻¹ := fun v => rfl
  have hgen : Subgroup.closure {x | ∃ r : ↥V, x = r * (φ r)⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hrV : (r : G) ∈ Subgroup.closure {x | ∃ v ∈ V, x = ⁅v, c⁆} := by
      have := (commutator_zpowers_le_closure hc3 hcV) (hVc.symm ▸ r.2 : (r : G) ∈ ⁅V, _⁆)
      exact this
    have himg : Subgroup.closure {x | ∃ v ∈ V, x = ⁅v, c⁆} =
        (Subgroup.closure {x | ∃ r : ↥V, x = r * (φ r)⁻¹}).map V.subtype := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, hv⟩ * (φ ⟨v, hv⟩)⁻¹, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
        simp [hφapp, commutatorElement_def, mul_assoc]
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        refine ⟨s, s.2, ?_⟩
        simp [hφapp, commutatorElement_def, mul_assoc]
    rw [himg] at hrV
    obtain ⟨s, hs, hsr⟩ := hrV
    have : s = r := Subtype.ext hsr
    exact this ▸ hs
  intro v hv
  have hfix : φ ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := by
    apply Subtype.ext
    rw [hφapp]
    have hcv : c * v = v * c := (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm
    simp [hcv]
  exact ⟨⟨v, hv.1⟩, mem_commutator_of_fixed φ hgen hfix, rfl⟩

omit [Finite G] in
theorem centralizer_sq_eq {x : G} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc x = x ^ 3 * x := by rw [hx, one_mul]
        _ = x ^ (2 * 2) := by rw [← pow_succ]
    rw [e]
    exact (Commute.pow_right h 2).eq
  · intro h
    exact (Commute.pow_right h 2).eq

theorem le_sup_of_generation {V : Subgroup G} {c d : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hc1 : c ≠ 1) (hdc : d ∉ Subgroup.zpowers c)
    (hcV : c ∈ Subgroup.normalizer (V : Set G)) (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hV3 : ¬ 3 ∣ Nat.card V)
    (h1 : V ⊓ Subgroup.centralizer ({c * d} : Set G) ≤ Subgroup.centralizer ({d} : Set G))
    (h2 : V ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) ≤ Subgroup.centralizer ({d} : Set G)) :
    V ≤ (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ (V ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hB
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute c d from hcd) m n)).eq
  obtain ⟨hcard, hset⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers c) (Subgroup.zpowers d)
      hcomm
  have hc3' : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc3 hc1
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ one_mem _)
  have hd3' : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hd3 hd1
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers d = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers d : Subgroup G) ∣ 3 :=
      hd3' ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hd3'])
      exact hdc (heq ▸ Subgroup.mem_zpowers d |>.1)
  rw [hinf, Subgroup.card_bot, mul_one, hc3', hd3'] at hcard
  have hBc : B = Subgroup.closure ({c, d} : Set G) := by
    rw [hB, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hBab : CFSG.Open.IsElemAbelian 3 B := by
    have hpair : ({c, d} : Set G).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hcd
      · exact hcd.symm
      · exact Commute.refl _
    have hC : IsMulCommutative ↥B := hBc ▸ Subgroup.isMulCommutative_closure hpair
    refine ⟨hC, fun x hx => ?_⟩
    have hx' : x ∈ ((B : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [(Commute.zpow_zpow (show Commute c d from hcd) m n).mul_pow, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m, mul_comm n, zpow_mul, zpow_mul,
      zpow_natCast, zpow_natCast, hc3, hd3, one_zpow, one_zpow, one_mul]
  have hBV : B ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcV) (Subgroup.zpowers_le.mpr hdV)
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers Nat.prime_three hBab
    (by rw [hcard]; norm_num) hBV hV3
  refine hgen.trans (iSup_le fun b => ?_)
  have hbB : (b.val : G) ∈ ((B : Subgroup G) : Set G) := b.val.2
  rw [hset] at hbB
  obtain ⟨u, hu, v, hv, huv⟩ := hbB
  have hb1 : (b.val : G) ≠ 1 := fun h => b.2 (Subtype.ext h)
  set J := (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ (V ⊓ Subgroup.centralizer ({d} : Set G))
  have hcJ : V ⊓ Subgroup.centralizer ({c} : Set G) ≤ J := le_sup_left
  have hdJ : V ⊓ Subgroup.centralizer ({d} : Set G) ≤ J := le_sup_right
  have hcdJ : V ⊓ Subgroup.centralizer ({c * d} : Set G) ≤ J :=
    fun x hx => hdJ ⟨hx.1, h1 hx⟩
  have hcd'J : V ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) ≤ J :=
    fun x hx => hdJ ⟨hx.1, h2 hx⟩
  have hd2 : d ^ 2 = d⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hd3]
  have hsq : ∀ x : G, x ^ 3 = 1 → V ⊓ Subgroup.centralizer ({x} : Set G) ≤ J →
      V ⊓ Subgroup.centralizer ({x ^ 2} : Set G) ≤ J := by
    intro x hx hle
    rw [centralizer_sq_eq hx]
    exact hle
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [(show Commute c d from hcd).mul_pow, hc3, hd3, one_mul]
  have hcdi3 : (c * d⁻¹) ^ 3 = 1 := by
    rw [(show Commute c d⁻¹ from (Commute.inv_right hcd)).mul_pow, hc3, inv_pow, hd3,
      inv_one, one_mul]
  have huv' : u * v = (b.val : G) := huv
  change V ⊓ Subgroup.centralizer ({(b.val : G)} : Set G) ≤ J
  rw [← huv']
  have hb1' : u * v ≠ 1 := huv' ▸ hb1
  rcases eq_of_mem_zpowers_of_pow_three hc3 hu with hu' | hu' | hu' <;>
    rcases eq_of_mem_zpowers_of_pow_three hd3 hv with hv' | hv' | hv' <;>
    rw [hu', hv'] at hb1' ⊢
  · exact absurd (mul_one 1) hb1'
  · rw [one_mul]; exact hdJ
  · rw [one_mul]; exact hsq d hd3 hdJ
  · rw [mul_one]; exact hcJ
  · exact hcdJ
  · rw [hd2]; exact hcd'J
  · rw [mul_one]; exact hsq c hc3 hcJ
  ·
    have e : c ^ 2 * d = (c * d⁻¹) ^ 2 := by
      rw [(show Commute c d⁻¹ from (Commute.inv_right hcd)).mul_pow, inv_pow, hd2, inv_inv]
    rw [e]
    exact hsq _ hcdi3 hcd'J
  ·
    have e : c ^ 2 * d ^ 2 = (c * d) ^ 2 := ((show Commute c d from hcd).mul_pow 2).symm
    rw [e]
    exact hsq _ hcd3 hcdJ

omit [Finite G] in
theorem mem_normalizer_commutator {Q : Subgroup G} {c g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgc : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    g ∈ Subgroup.normalizer ((⁅Q, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp hgQ,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgc]

theorem passage1515 : Passage1515 := by
  intro G _ _ Q hQ c d hcd hc3 hd3 hcQ hdQ h1 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQc : Subgroup.zpowers c ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr hcQ
  have hle : ⁅Q, Subgroup.zpowers c⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq g hg
    rw [commutatorElement_def]
    have h1 : g * q⁻¹ * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQc hg) q⁻¹).mp (inv_mem hq)
    have e : q * g * q⁻¹ * g⁻¹ = q * (g * q⁻¹ * g⁻¹) := by group
    rw [e]
    exact mul_mem hq h1
  by_cases hc1 : c = 1
  · subst hc1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    exact bot_le
  by_cases hdc : d ∈ Subgroup.zpowers c
  ·
    have hcen1 : ∀ x : G, x ∈ Subgroup.centralizer ({(1 : G)} : Set G) := fun x =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
    rcases eq_of_mem_zpowers_of_pow_three hc3 hdc with hd' | hd' | hd'
    · intro x _
      rw [hd']
      exact hcen1 x
    · have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
        h2 ⟨hx, by rw [hd', mul_inv_cancel]; exact hcen1 x⟩
      exact hle.trans hQd
    · have e : c * c ^ 2 = 1 := by rw [← hc3]; group
      have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
        h1 ⟨hx, by rw [hd', e]; exact hcen1 x⟩
      exact hle.trans hQd
  set V := ⁅Q, Subgroup.zpowers c⁆ with hV
  have hV2 : IsPGroup 2 V := hQ.to_le hle
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hVc : ⁅V, Subgroup.zpowers c⁆ = V :=
    CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime Q (Subgroup.zpowers c) hcop hQc
  have hcc : c ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hdc' : d ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_ (Subgroup.mem_zpowers d)
    exact Sec14.centralizer_singleton_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr hcd.symm)
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_commutator hcQ hcc
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_commutator hdQ hdc'
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hgen := le_sup_of_generation hcd hc3 hd3 hc1 hdc hcV hdV hV3
    (fun x hx => h1 ⟨hle hx.1, hx.2⟩) (fun x hx => h2 ⟨hle hx.1, hx.2⟩)
  have hcomm := inf_centralizer_le_map_commutator hc3 hcV hVc
  have : Fact (IsPGroup 2 ↥V) := ⟨hV2⟩
  set Hd := (Subgroup.centralizer ({d} : Set G)).subgroupOf V with hHd
  have htop : Hd ⊔ frattini ↥V = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hr : (r : G) ∈ (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        (V ⊓ Subgroup.centralizer ({d} : Set G)) := hgen r.2
    have hmap : (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        (V ⊓ Subgroup.centralizer ({d} : Set G)) ≤ (frattini ↥V ⊔ Hd).map V.subtype := by
      rw [Subgroup.map_sup]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨y, hy, rfl⟩ := hcomm hx
        exact Subgroup.mem_sup_left ⟨y, CFSG.commutator_le_frattini_of_isPGroup (p := 2) hy,
          rfl⟩
      · exact Subgroup.mem_sup_right ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hmap hr
    have : s = r := Subtype.ext hsr
    rw [sup_comm]
    exact this ▸ hs
  have hHd : Hd = ⊤ := frattini_nongenerating htop
  intro x hx
  have : (⟨x, hx⟩ : ↥V) ∈ Hd := hHd ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Proof15Res4

end CFSG.RankThree.PartTwo.Sec15
