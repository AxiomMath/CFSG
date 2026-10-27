module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianBasis
import CFSG.GroupTheory.Extraspecial2PG
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G]

open QuaternionGroup in
private theorem quaternion_table :
    (∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = a 2) ∧
    (∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = a 2) ∧
    (∀ q : QuaternionGroup 2, q * a 2 = a 2 * q) ∧
    (∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, q * r = r * q) → q = 1 ∨ q = a 2) ∧
    (∀ q r : QuaternionGroup 2, ⁅q, r⁆ = 1 ∨ ⁅q, r⁆ = a 2) ∧
    a 2 ≠ (1 : QuaternionGroup 2) ∧ a 2 * a 2 = (1 : QuaternionGroup 2) ∧
    a 1 * a 1 = (a 2 : QuaternionGroup 2) ∧ xa 0 * xa 0 = (a 2 : QuaternionGroup 2) ∧
    xa 0 * a 1 = (a 1 * xa 0 * a 2 : QuaternionGroup 2) ∧
    xa 0 * a 1 * (xa 0 * a 1) = (a 2 : QuaternionGroup 2) ∧
    ⁅(a 1 : QuaternionGroup 2), (xa 0 : QuaternionGroup 2)⁆ = a 2 := by
  decide

private theorem quaternion_facts {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2) :
    ∃ c ∈ Q, c ≠ 1 ∧ c * c = 1 ∧
      (∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = c) ∧
      (∀ q ∈ Q, q * q = 1 ∨ q * q = c) ∧
      (∀ q ∈ Q, q * c = c * q) ∧
      (∀ q ∈ Q, (∀ r ∈ Q, q * r = r * q) → q = 1 ∨ q = c) ∧
      (∀ q ∈ Q, ∀ r ∈ Q, ⁅q, r⁆ = 1 ∨ ⁅q, r⁆ = c) ∧
      ∃ i ∈ Q, ∃ j ∈ Q, i * i = c ∧ j * j = c ∧ j * i = i * j * c ∧ j * i * (j * i) = c ∧
        ⁅i, j⁆ = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := quaternion_table
  let f : QuaternionGroup 2 →* G := Q.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.symm.injective
  have hfQ : ∀ r, f r ∈ Q := fun r => (e.symm r).2
  have hsurj : ∀ q ∈ Q, ∃ r, f r = q := fun q hq => ⟨e ⟨q, hq⟩, by simp [f]⟩
  refine ⟨f (QuaternionGroup.a 2), hfQ _, fun h => h6 (hf (h.trans (map_one f).symm)),
    by rw [← map_mul, h7, map_one], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hqq
    obtain ⟨r, rfl⟩ := hsurj q hq
    rw [← map_mul, ← map_one f] at hqq
    rcases h1 r (hf hqq) with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  · intro q hq
    obtain ⟨r, rfl⟩ := hsurj q hq
    rcases h2 r with h | h
    · left
      rw [← map_mul, h, map_one]
    · right
      rw [← map_mul, h]
  · intro q hq
    obtain ⟨r, rfl⟩ := hsurj q hq
    rw [← map_mul, ← map_mul, h3 r]
  · intro q hq hc
    obtain ⟨r, rfl⟩ := hsurj q hq
    have hr : ∀ s, r * s = s * r := fun s => hf (by rw [map_mul, map_mul]; exact hc (f s) (hfQ s))
    rcases h4 r hr with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  · intro q hq r hr
    obtain ⟨s, rfl⟩ := hsurj q hq
    obtain ⟨t, rfl⟩ := hsurj r hr
    rw [← map_commutatorElement]
    rcases h5 s t with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  · refine ⟨f (QuaternionGroup.a 1), hfQ _, f (QuaternionGroup.xa 0), hfQ _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, h8]
    · rw [← map_mul, h9]
    · rw [← map_mul, ← map_mul, ← map_mul, h10]
    · rw [← map_mul, ← map_mul, h11]
    · rw [← map_commutatorElement, h12]

private theorem card_eq_eight_of_quaternion {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2) :
    Nat.card Q = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem ne_one_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) : z ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hz
  exact absurd hz (by norm_num)

private theorem quaternion_facts_of_mem {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2) {z : G}
    (hz : orderOf z = 2) (hzQ : z ∈ Q) :
    (∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z) ∧ (∀ q ∈ Q, q * q = 1 ∨ q * q = z) ∧
      (∀ q ∈ Q, (∀ r ∈ Q, q * r = r * q) → q = 1 ∨ q = z) ∧
      (∀ q ∈ Q, ∀ r ∈ Q, ⁅q, r⁆ = 1 ∨ ⁅q, r⁆ = z) ∧
      ∃ i ∈ Q, ∃ j ∈ Q, i * i = z ∧ j * j = z ∧ j * i = i * j * z ∧ j * i * (j * i) = z := by
  obtain ⟨c, -, -, -, hinv, hsq, -, hcen, hcom, i, hi, j, hj, hii, hjj, hji, hjiji, -⟩ :=
    quaternion_facts e
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hzc : z = c := (hinv z hzQ hzz).resolve_left (ne_one_of_orderOf_eq_two hz)
  subst hzc
  exact ⟨hinv, hsq, hcen, hcom, i, hi, j, hj, hii, hjj, hji, hjiji⟩

private theorem eq_one_or_eq_of_mem_zpowers {z c : G} (hz : orderOf z = 2)
    (hc : c ∈ Subgroup.zpowers z) : c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← zpow_mod_orderOf, hz, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

private theorem mul_self_eq_one_of_mem_zpowers {z c : G} (hz : orderOf z = 2)
    (hc : c ∈ Subgroup.zpowers z) : c * c = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers hz hc with h | h
  · rw [h, one_mul]
  · rw [h, ← pow_two, ← hz, pow_orderOf_eq_one]

private theorem commute_of_mem_zpowers {z c a : G} (hc : c ∈ Subgroup.zpowers z)
    (ha : a * z = z * a) : a * c = c * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact (Commute.zpow_right ha k).eq

variable [Finite G]

private theorem nonempty_quaternion_of_three_action {E : Subgroup G} (hcard : Nat.card E = 8)
    (hnab : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) {σ : G} (hσ : orderOf σ = 3)
    (hN : σ ∈ Subgroup.normalizer (E : Set G)) (hact : ∃ e ∈ E, σ * e * σ⁻¹ ≠ e) :
    Nonempty (↥E ≃* QuaternionGroup 2) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  rcases CFSG.OddStandard.SmallF3.HarrisU33.Outside.order8_nonabelian (G := ↥E) hcard
      ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩ with hD | hQ
  · exfalso
    obtain ⟨eD⟩ := hD
    let x : ↥(Subgroup.normalizer (E : Set G)) := ⟨σ, hN⟩
    let c : MulAut ↥E := E.normalizerMonoidHom x
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa [x] using hσ3)
    have hc3 : c ^ 3 = 1 := by
      change (E.normalizerMonoidHom x) ^ 3 = 1
      rw [← map_pow, hx3, map_one]
    have hcne : c ≠ 1 := by
      intro hc1
      obtain ⟨e, he, hne⟩ := hact
      apply hne
      have h : c ⟨e, he⟩ = ⟨e, he⟩ := by rw [hc1]; rfl
      simpa [c, Subgroup.normalizerMonoidHom_apply_apply_coe] using congrArg Subtype.val h
    have hcord : orderOf c = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hcne
      · exact h
    have hAut : IsPGroup 2 (MulAut ↥E) :=
      (CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) le_rfl).of_equiv
        (MulAut.congr eD).symm
    obtain ⟨k, hk⟩ := hAut.exists_orderOf_dvd_pow c
    rw [hcord] at hk
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hk) (by norm_num)
  · exact hQ

private theorem mul_mem_of_mem_sup_zpowers {N : Subgroup G} {g x : G}
    (hn : g ∈ Subgroup.normalizer (N : Set G)) (hsq : g * g ∈ N) (hg : g ∉ N)
    (hx : x ∈ N ⊔ Subgroup.zpowers g) (hxN : x ∉ N) : x * g ∈ N := by
  have hcard := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hn hsq hg
  have h1 := Subgroup.relIndex_mul_card N (N ⊔ Subgroup.zpowers g)
  rw [inf_eq_left.mpr le_sup_left, hcard] at h1
  have h2 : N.relIndex (N ⊔ Subgroup.zpowers g) = 2 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hgM : g ∈ N ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨g, hgM⟩)
  simp only [Subgroup.mem_subgroupOf] at h3
  exact h3.mpr (iff_of_false hxN hg)

private theorem card_le_mul_card_inf_centralizer {Y : Subgroup G} {z x : G}
    (hz : ∀ a ∈ Y, a * z = z * a) (hx : ∀ a ∈ Y, ⁅a, x⁆ ∈ Subgroup.zpowers z) :
    Nat.card Y ≤ Nat.card (Subgroup.zpowers z) *
      Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  let φ : Y →* Subgroup.zpowers z :=
    { toFun := fun g => ⟨⁅(g : G), x⁆, hx _ g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g₁ g₂ => Subtype.ext (by
        show ⁅(g₁ : G) * g₂, x⁆ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆
        have hc : (g₁ : G) * ⁅(g₂ : G), x⁆ = ⁅(g₂ : G), x⁆ * g₁ :=
          commute_of_mem_zpowers (hx _ g₂.2) (hz _ g₁.2)
        have hab : ⁅(g₂ : G), x⁆ * ⁅(g₁ : G), x⁆ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆ := by
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hx _ g₁.2)
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hx _ g₂.2)
          rw [← hi, ← hj]
          exact (Commute.zpow_zpow_self z j i).eq
        calc ⁅(g₁ : G) * g₂, x⁆ = (g₁ : G) * ⁅(g₂ : G), x⁆ * (g₁ : G)⁻¹ * ⁅(g₁ : G), x⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅(g₂ : G), x⁆ * ⁅(g₁ : G), x⁆ := by rw [hc]; group
          _ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆ := hab) }
  have hker : φ.ker = (Subgroup.centralizer ({x} : Set G)).subgroupOf Y := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      ← commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_card_group _
  have h3 : Nat.card φ.ker = Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

private theorem mem_normalizer_sup_zpowers {a b g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b).comap (MulAut.conj g).toMonoidHom :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact hle hx

private theorem extraspecial_facts {P : Subgroup G} (hP : IsExtraspecial2 P) :
    ∃ z : G, orderOf z = 2 ∧ ⁅P, P⁆ = Subgroup.zpowers z ∧ z ∈ P ∧
      (∀ a ∈ P, a * z = z * a) ∧ (∀ a ∈ P, a * a ∈ Subgroup.zpowers z) ∧
      (∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ Subgroup.zpowers z) ∧
      (∀ b ∈ P, (∀ a ∈ P, b * a = a * b) → b ∈ Subgroup.zpowers z) := by
  obtain ⟨z, hD, hz⟩ := CFSG.GroupTheory.exists_zpowers_eq_of_card_eq_prime Nat.prime_two hP.2.2
  have hDc : ⁅P, P⁆ = (Subgroup.center P).map P.subtype := hP.2.1
  have hzD : z ∈ (Subgroup.center P).map P.subtype := by
    rw [← hDc, hD]
    exact Subgroup.mem_zpowers z
  refine ⟨z, hz, hD, Subgroup.map_subtype_le _ hzD, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨w, hw, hwz⟩ := hzD
    rw [← hwz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨a, ha⟩)
  · intro a ha
    rw [← hD, hDc]
    exact CFSG.IsExtraspecial2.mul_self_mem_center_map hP ha
  · intro a ha b hb
    rw [← hD]
    exact Subgroup.commutator_mem_commutator ha hb
  · intro b hb hcb
    rw [← hD, hDc]
    exact ⟨⟨b, hb⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcb g g.2).symm, rfl⟩

private theorem conj_eq_of_mem_derived {P : Subgroup G} (hP : IsExtraspecial2 P) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) {c : G} (hc : c ∈ ⁅P, P⁆) : g * c * g⁻¹ = c := by
  obtain ⟨z, hz, hD, hzP, hzc, -, -, hcen⟩ := extraspecial_facts hP
  rw [hD] at hc
  have hgz : g * z * g⁻¹ = z := by
    have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
      refine hcen _ ((Subgroup.mem_normalizer_iff.mp hg z).mp hzP) fun a ha => ?_
      have ha' : g⁻¹ * a * g ∈ P := (Subgroup.mem_normalizer_iff''.mp hg a).mp ha
      have h := hzc _ ha'
      calc g * z * g⁻¹ * a = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by rw [← h]
        _ = a * (g * z * g⁻¹) := by group
    rcases eq_one_or_eq_of_mem_zpowers hz hmem with h | h
    · exfalso
      apply ne_one_of_orderOf_eq_two hz
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  rcases eq_one_or_eq_of_mem_zpowers hz hc with h | h
  · rw [h]
    group
  · rw [h]
    exact hgz

private theorem mul_conj_mul_conj_mem {P : Subgroup G} (hP : IsExtraspecial2 P) {σ : G}
    (hσ : orderOf σ = 3) (hσP : σ ∈ Subgroup.normalizer (P : Set G))
    (hfix : ∀ x ∈ P, σ * x * σ⁻¹ = x → x ∈ ⁅P, P⁆) {x : G} (hx : x ∈ P) :
    x * (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹) ∈ ⁅P, P⁆ := by
  obtain ⟨z, hz, hD, -, -, -, hcomm, -⟩ := extraspecial_facts hP
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_zpowers hz (Subgroup.mem_zpowers z)
  have hσz : σ * z * σ⁻¹ = z :=
    conj_eq_of_mem_derived hP hσP (by rw [hD]; exact Subgroup.mem_zpowers z)
  have hσ3 : σ * (σ * σ) = 1 := by rw [← pow_three, ← hσ]; exact pow_orderOf_eq_one σ
  have hy : σ * x * σ⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hσP x).mp hx
  have hw : σ * (σ * x * σ⁻¹) * σ⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hσP _).mp hy
  obtain ⟨t, ht⟩ : ∃ t, x * (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹) = t := ⟨_, rfl⟩
  rw [ht]
  have htP : t ∈ P := ht ▸ P.mul_mem (P.mul_mem hx hy) hw
  have hkey : σ * t * σ⁻¹ = t * ⁅t⁻¹, x⁻¹⁆ := by
    have h3 : σ * (σ * (σ * x * σ⁻¹) * σ⁻¹) * σ⁻¹ = x := by
      calc σ * (σ * (σ * x * σ⁻¹) * σ⁻¹) * σ⁻¹ = σ * (σ * σ) * x * (σ * (σ * σ))⁻¹ := by group
        _ = x := by rw [hσ3]; group
    rw [← ht]
    calc σ * (x * (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹)) * σ⁻¹
        = (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹) *
          (σ * (σ * (σ * x * σ⁻¹) * σ⁻¹) * σ⁻¹) := by group
      _ = (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹) * x := by rw [h3]
      _ = x * (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹) *
          ⁅(x * (σ * x * σ⁻¹) * (σ * (σ * x * σ⁻¹) * σ⁻¹))⁻¹, x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
  have hc : ⁅t⁻¹, x⁻¹⁆ ∈ Subgroup.zpowers z := hcomm _ (P.inv_mem htP) _ (P.inv_mem hx)
  rcases eq_one_or_eq_of_mem_zpowers hz hc with h | h
  · exact hfix t htP (by rw [hkey, h, mul_one])
  · exfalso
    rw [h] at hkey
    have h2 : σ * (σ * t * σ⁻¹) * σ⁻¹ = t := by
      calc σ * (σ * t * σ⁻¹) * σ⁻¹ = σ * (t * z) * σ⁻¹ := by rw [hkey]
        _ = (σ * t * σ⁻¹) * (σ * z * σ⁻¹) := by group
        _ = t * z * z := by rw [hkey, hσz]
        _ = t := by rw [mul_assoc, hzz, mul_one]
    have h3 : σ * (σ * (σ * t * σ⁻¹) * σ⁻¹) * σ⁻¹ = t := by
      calc σ * (σ * (σ * t * σ⁻¹) * σ⁻¹) * σ⁻¹ = σ * (σ * σ) * t * (σ * (σ * σ))⁻¹ := by group
        _ = t := by rw [hσ3]; group
    rw [h2, hkey] at h3
    exact ne_one_of_orderOf_eq_two hz (mul_eq_left.mp h3)

theorem exists_quaternion_pair_of_fixedPointFree {P : Subgroup G} (hP : IsExtraspecial2 P)
    (hP32 : Nat.card P = 32) {σ : G} (hσ : orderOf σ = 3)
    (hσP : σ ∈ Subgroup.normalizer (P : Set G))
    (hfix : ∀ x ∈ P, σ * x * σ⁻¹ = x → x ∈ ⁅P, P⁆) :
    ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ P ∧ Q₂ ≤ P ∧ Q₁ ⊔ Q₂ = P ∧ Q₁ ⊓ Q₂ = ⁅P, P⁆ ∧
      (∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) ∧
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) ∧ Nonempty (↥Q₂ ≃* QuaternionGroup 2) ∧
      σ ∈ Subgroup.normalizer (Q₁ : Set G) ∧ σ ∈ Subgroup.normalizer (Q₂ : Set G) := by
  obtain ⟨z, hz, hD, hzP, hzc, hsq, hcomm, hcen⟩ := extraspecial_facts hP
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two hz
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_zpowers hz (Subgroup.mem_zpowers z)
  have hσz : σ * z * σ⁻¹ = z :=
    conj_eq_of_mem_derived hP hσP (by rw [hD]; exact Subgroup.mem_zpowers z)
  have hcardz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  obtain ⟨x, hxP, hxx⟩ : ∃ x ∈ P, x * x = z := by
    by_contra hcon
    push Not at hcon
    have hsq1 : ∀ a ∈ P, a * a = 1 := fun a ha =>
      (eq_one_or_eq_of_mem_zpowers hz (hsq a ha)).resolve_right (hcon a ha)
    have hle : ⁅P, P⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq1 _ (P.mul_mem ha hb))).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hsq1 a ha), inv_eq_of_mul_eq_one_right (hsq1 b hb)]
    exact hz1 (Subgroup.mem_bot.mp (hle (by rw [hD]; exact Subgroup.mem_zpowers z)))
  obtain ⟨y, hy⟩ : ∃ y, σ * x * σ⁻¹ = y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, σ * y * σ⁻¹ = w := ⟨_, rfl⟩
  have hyP : y ∈ P := by
    rw [← hy]
    exact (Subgroup.mem_normalizer_iff.mp hσP x).mp hxP
  have hwP : w ∈ P := by
    rw [← hw]
    exact (Subgroup.mem_normalizer_iff.mp hσP y).mp hyP
  have hyy : y * y = z := by
    rw [← hy]
    calc σ * x * σ⁻¹ * (σ * x * σ⁻¹) = σ * (x * x) * σ⁻¹ := by group
      _ = z := by rw [hxx, hσz]
  have htr : x * y * w ∈ Subgroup.zpowers z := by
    rw [← hD, ← hw, ← hy]
    exact mul_conj_mul_conj_mem hP hσ hσP hfix hxP
  have hxy : x * y ≠ y * x := by
    intro hxy
    have hww : w * w = z := by
      rw [← hw]
      calc σ * y * σ⁻¹ * (σ * y * σ⁻¹) = σ * (y * y) * σ⁻¹ := by group
        _ = z := by rw [hyy, hσz]
    have htt : x * y * w * (x * y * w) = 1 := mul_self_eq_one_of_mem_zpowers hz htr
    have htc : (x * y)⁻¹ * (x * y * w) = (x * y * w) * (x * y)⁻¹ :=
      commute_of_mem_zpowers htr (hzc _ (P.inv_mem (P.mul_mem hxP hyP)))
    have hxyxy : x * y * (x * y) = 1 := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = x * x * (y * y) := by group
        _ = 1 := by rw [hxx, hyy, hzz]
    have hww1 : w * w = 1 := by
      have hwexp : w = (x * y)⁻¹ * (x * y * w) := by group
      rw [hwexp]
      calc (x * y)⁻¹ * (x * y * w) * ((x * y)⁻¹ * (x * y * w))
          = (x * y)⁻¹ * ((x * y * w) * (x * y)⁻¹) * (x * y * w) := by group
        _ = (x * y)⁻¹ * ((x * y)⁻¹ * (x * y * w)) * (x * y * w) := by rw [← htc]
        _ = (x * y * (x * y))⁻¹ * (x * y * w * (x * y * w)) := by group
        _ = 1 := by rw [hxyxy, htt, inv_one, one_mul]
    exact hz1 (hww.symm.trans hww1)
  have hordx : orderOf x = 4 := by
    have hx4 : x ^ 4 = 1 := by
      calc x ^ 4 = x * x * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := by rw [hxx, hzz]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, pow_two, hxx]; exact hz1) hx4
  have hzx : z ∈ Subgroup.zpowers x := by
    rw [← hxx]
    exact (Subgroup.zpowers x).mul_mem (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff]
    have hyx : y * x * y⁻¹ = ⁅y, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [hyx]
    exact (Subgroup.zpowers x).mul_mem (Subgroup.zpowers_le.mpr hzx (hcomm y hyP x hxP))
      (Subgroup.mem_zpowers x)
  have hyx : y ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hk] at hxy
    exact hxy (Commute.self_zpow x k).eq
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Subgroup G, Subgroup.zpowers x ⊔ Subgroup.zpowers y = Q₁ :=
    ⟨_, rfl⟩
  have hxQ₁ : x ∈ Q₁ := by
    rw [← hQ₁]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyQ₁ : y ∈ Q₁ := by
    rw [← hQ₁]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hzQ₁ : z ∈ Q₁ := by
    rw [← hQ₁]
    exact Subgroup.mem_sup_left hzx
  have hwQ₁ : w ∈ Q₁ := by
    have hwexp : w = (x * y)⁻¹ * (x * y * w) := by group
    rw [hwexp]
    refine Q₁.mul_mem (Q₁.inv_mem (Q₁.mul_mem hxQ₁ hyQ₁)) ?_
    rw [← hQ₁]
    exact Subgroup.mem_sup_left (Subgroup.zpowers_le.mpr hzx htr)
  have hQ₁P : Q₁ ≤ P := by
    rw [← hQ₁]
    exact sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr hyP)
  have hcardQ₁ : Nat.card Q₁ = 8 := by
    rw [← hQ₁, CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hyN (by rw [hyy]; exact hzx) hyx,
      Nat.card_zpowers, hordx]
  have hσQ₁ : σ ∈ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hQ₁]
    refine mem_normalizer_sup_zpowers ?_ ?_
    · rw [hy, hQ₁]
      exact hyQ₁
    · rw [hw, hQ₁]
      exact hwQ₁
  obtain ⟨e₁⟩ := nonempty_quaternion_of_three_action hcardQ₁ ⟨x, hxQ₁, y, hyQ₁, hxy⟩ hσ hσQ₁
    ⟨x, hxQ₁, fun h => hxy (by rw [hy] at h; rw [h])⟩
  obtain ⟨c₁, -, -, -, hinv₁, -, -, hcen₁, -, -⟩ := quaternion_facts e₁
  have hzc₁ : z = c₁ := (hinv₁ z hzQ₁ hzz).resolve_left hz1
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : Subgroup G, P ⊓ Subgroup.centralizer (Q₁ : Set G) = Q₂ := ⟨_, rfl⟩
  have hmemQ₂ : ∀ b, b ∈ Q₂ ↔ b ∈ P ∧ ∀ a ∈ Q₁, a * b = b * a := by
    intro b
    rw [← hQ₂, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hQ₂P : Q₂ ≤ P := fun b hb => ((hmemQ₂ b).mp hb).1
  have hcomm12 : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a := fun a ha b hb =>
    ((hmemQ₂ b).mp hb).2 a ha
  have hC1 := card_le_mul_card_inf_centralizer (Y := P) (x := x) hzc
    (fun a ha => hcomm a ha x hxP)
  have hC2 := card_le_mul_card_inf_centralizer (Y := P ⊓ Subgroup.centralizer ({x} : Set G))
    (x := y) (fun a ha => hzc a ha.1) (fun a ha => hcomm a ha.1 y hyP)
  have hC2le : P ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Q₂ := by
    rintro b ⟨⟨hbP, hbx⟩, hby⟩
    rw [hmemQ₂]
    refine ⟨hbP, fun a ha => ?_⟩
    have hle : Q₁ ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [← hQ₁]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hbx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hby).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hQ₂ge : 8 ≤ Nat.card Q₂ := by
    have h3 := Subgroup.card_le_of_le hC2le
    rw [hcardz, hP32] at hC1
    rw [hcardz] at hC2
    omega
  have hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z := by
    apply le_antisymm
    · rintro q ⟨hq₁, hq₂⟩
      rcases hcen₁ q hq₁ (fun r hr => (hcomm12 r hr q hq₂).symm) with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h, ← hzc₁]
        exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      exact ⟨hzQ₁, (hmemQ₂ z).mpr ⟨hzP, fun a ha => hzc a (hQ₁P ha)⟩⟩
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₂ hcomm12).1
  rw [hinf, hcardz, hcardQ₁] at hprod
  have hsupP : Q₁ ⊔ Q₂ ≤ P := sup_le hQ₁P hQ₂P
  have hsuple := Subgroup.card_le_of_le hsupP
  rw [hP32] at hsuple
  have hQ₂8 : Nat.card Q₂ = 8 := by omega
  have hsup : Q₁ ⊔ Q₂ = P := Subgroup.eq_of_le_of_card_ge hsupP (by rw [hP32]; omega)
  have hQ₂nab : ∃ a ∈ Q₂, ∃ b ∈ Q₂, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hle : Q₂ ≤ Subgroup.zpowers z := by
      intro b hb
      refine hcen b (hQ₂P hb) fun a ha => ?_
      have hPc : P ≤ Subgroup.centralizer ({b} : Set G) := by
        rw [← hsup]
        refine sup_le (fun q hq => ?_) (fun q hq => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm12 q hq b hb)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcon q hq b hb)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hPc ha)).symm
    have := Subgroup.card_le_of_le hle
    rw [hcardz, hQ₂8] at this
    omega
  have hσQ₂ : σ ∈ Subgroup.normalizer (Q₂ : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨hbP, hbc⟩ := (hmemQ₂ b).mp hb
    rw [hmemQ₂]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hσP b).mp hbP, fun a ha => ?_⟩
    have ha' : σ⁻¹ * a * σ ∈ Q₁ := (Subgroup.mem_normalizer_iff''.mp hσQ₁ a).mp ha
    have hc := hbc _ ha'
    calc a * (σ * b * σ⁻¹) = σ * ((σ⁻¹ * a * σ) * b) * σ⁻¹ := by group
      _ = σ * (b * (σ⁻¹ * a * σ)) * σ⁻¹ := by rw [hc]
      _ = σ * b * σ⁻¹ * a := by group
  have hσact : ∃ e ∈ Q₂, σ * e * σ⁻¹ ≠ e := by
    by_contra hcon
    push Not at hcon
    have hle : Q₂ ≤ Subgroup.zpowers z := fun b hb => by
      rw [← hD]
      exact hfix b (hQ₂P hb) (hcon b hb)
    have := Subgroup.card_le_of_le hle
    rw [hcardz, hQ₂8] at this
    omega
  exact ⟨Q₁, Q₂, hQ₁P, hQ₂P, hsup, hinf.trans hD.symm, hcomm12, ⟨e₁⟩,
    nonempty_quaternion_of_three_action hQ₂8 hQ₂nab hσ hσQ₂ hσact, hσQ₁, hσQ₂⟩

theorem eq_or_eq_of_quaternion_of_fixedPointFree {P Q₁ Q₂ : Subgroup G}
    (hsup : Q₁ ⊔ Q₂ = P) (hinf : Q₁ ⊓ Q₂ = ⁅P, P⁆)
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    {Q : Subgroup G} (hQP : Q ≤ P) (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) :
    Q = Q₁ ∨ Q = Q₂ := by
  obtain ⟨e₁⟩ := hQ₁
  obtain ⟨e₂⟩ := hQ₂
  obtain ⟨e⟩ := hQ
  obtain ⟨c₁, hc₁Q, hc₁1, hc₁c₁, hinv₁, hsq₁, -, hcen₁, -, i₁, hi₁, j₁, hj₁, -, -, -, -, hij₁⟩ :=
    quaternion_facts e₁
  obtain ⟨c₂, -, -, -, hinv₂, hsq₂, -, -, -, -⟩ := quaternion_facts e₂
  obtain ⟨c, -, hc1, -, hinv, -, -, -, -, i, hi, j, hj, -, -, -, -, hij⟩ := quaternion_facts e
  have hQ₁P : Q₁ ≤ P := by
    rw [← hsup]
    exact le_sup_left
  have hder : ∀ d ∈ ⁅P, P⁆, d = 1 ∨ d = c₁ := by
    intro d hd
    rw [← hinf] at hd
    exact hcen₁ d hd.1 fun r hr => (hcomm r hr d hd.2).symm
  have hc₁P : c₁ ∈ Q₁ ⊓ Q₂ := by
    rw [hinf, ← hij₁]
    exact Subgroup.commutator_mem_commutator (hQ₁P hi₁) (hQ₁P hj₁)
  have hc₂ : c₂ = c₁ := ((hinv₂ c₁ hc₁P.2 hc₁c₁).resolve_left hc₁1).symm
  have hc : c = c₁ := by
    refine (hder c ?_).resolve_left hc1
    rw [← hij]
    exact Subgroup.commutator_mem_commutator (hQP hi) (hQP hj)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₂ hcomm).2
  have hunion : ∀ q ∈ Q, q ∈ Q₁ ∨ q ∈ Q₂ := by
    intro q hq
    have hqP : q ∈ ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := by
      rw [hsup]
      exact hQP hq
    rw [hset] at hqP
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hqP
    by_cases hb1 : b * b = 1
    · left
      rcases hinv₂ b hb hb1 with h | h
      · rw [h, mul_one]
        exact ha
      · rw [h, hc₂]
        exact Q₁.mul_mem ha hc₁Q
    by_cases ha1 : a * a = 1
    · right
      rcases hinv₁ a ha ha1 with h | h
      · rw [h, one_mul]
        exact hb
      · rw [h]
        exact Q₂.mul_mem hc₁P.2 hb
    left
    have ha2 : a * a = c₁ := (hsq₁ a ha).resolve_left ha1
    have hb2 : b * b = c₁ := by
      rw [← hc₂]
      exact (hsq₂ b hb).resolve_left hb1
    have hab : a * b * (a * b) = 1 := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm a ha b hb]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, hc₁c₁]
    rcases hinv (a * b) hq hab with h | h
    · rw [h]
      exact Q₁.one_mem
    · rw [h, hc]
      exact hc₁Q
  have hle : Q ≤ Q₁ ∨ Q ≤ Q₂ := by
    by_contra hcon
    obtain ⟨h₁, h₂⟩ := not_or.mp hcon
    obtain ⟨a, haQ, ha₁⟩ := SetLike.not_le_iff_exists.mp h₁
    obtain ⟨b, hbQ, hb₂⟩ := SetLike.not_le_iff_exists.mp h₂
    have ha₂ : a ∈ Q₂ := (hunion a haQ).resolve_left ha₁
    have hb₁ : b ∈ Q₁ := (hunion b hbQ).resolve_right hb₂
    rcases hunion (a * b) (Q.mul_mem haQ hbQ) with h | h
    · exact ha₁ (by simpa using Q₁.mul_mem h (Q₁.inv_mem hb₁))
    · exact hb₂ (by simpa using Q₂.mul_mem (Q₂.inv_mem ha₂) h)
  rcases hle with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h
      ((card_eq_eight_of_quaternion e₁).trans (card_eq_eight_of_quaternion e).symm).le)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h
      ((card_eq_eight_of_quaternion e₂).trans (card_eq_eight_of_quaternion e).symm).le)

private theorem central_product_facts {Q₁ Q₂ : Subgroup G} {z : G}
    (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z) :
    Nat.card (Q₁ ⊔ Q₂ : Subgroup G) = 32 ∧ (∀ a ∈ Q₁ ⊔ Q₂, a * z = z * a) ∧
      (∀ b ∈ Q₁ ⊔ Q₂, (∀ a ∈ Q₁ ⊔ Q₂, b * a = a * b) → b ∈ Subgroup.zpowers z) ∧
      (∀ a ∈ Q₁ ⊔ Q₂, ∀ b ∈ Q₁ ⊔ Q₂, ⁅a, b⁆ ∈ Subgroup.zpowers z) ∧
      Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (Q₁ : Set G) ∧
      Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (Q₂ : Set G) := by
  have hzQ : z ∈ Q₁ ⊓ Q₂ := by
    rw [hinf]
    exact Subgroup.mem_zpowers z
  obtain ⟨-, -, hcen₁, hcom₁, -⟩ := quaternion_facts_of_mem e₁ hz hzQ.1
  obtain ⟨-, -, hcen₂, hcom₂, -⟩ := quaternion_facts_of_mem e₂ hz hzQ.2
  have hm : ∀ {t : G}, t = 1 ∨ t = z → t ∈ Subgroup.zpowers z := by
    rintro t (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  have hset := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₂ hcomm
  have hdec : ∀ x ∈ Q₁ ⊔ Q₂, ∃ a ∈ Q₁, ∃ b ∈ Q₂, a * b = x := by
    intro x hx
    have hx' : x ∈ ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := hx
    rw [hset.2] at hx'
    exact Set.mem_mul.mp hx'
  have hzc : ∀ a ∈ Q₁ ⊔ Q₂, a * z = z * a := by
    have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha z hzQ.2))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzQ.1 b hb).symm)
    exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  refine ⟨?_, hzc, ?_, ?_, ?_, ?_⟩
  · have h := hset.1
    rw [hinf, Nat.card_zpowers, hz, card_eq_eight_of_quaternion e₁,
      card_eq_eight_of_quaternion e₂] at h
    omega
  · intro b hb hcb
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hdec b hb
    have h₁ : ∀ r ∈ Q₁, b₁ * r = r * b₁ := by
      intro r hr
      have h := hcb r (Subgroup.mem_sup_left hr)
      have hc := hcomm r hr b₂ hb₂
      calc b₁ * r = b₁ * r * b₂ * b₂⁻¹ := by group
        _ = b₁ * (b₂ * r) * b₂⁻¹ := by rw [mul_assoc b₁ r b₂, hc]
        _ = b₁ * b₂ * r * b₂⁻¹ := by group
        _ = r * (b₁ * b₂) * b₂⁻¹ := by rw [h]
        _ = r * b₁ := by group
    have h₂ : ∀ r ∈ Q₂, b₂ * r = r * b₂ := by
      intro r hr
      have h := hcb r (Subgroup.mem_sup_right hr)
      have hc := hcomm b₁ hb₁ r hr
      calc b₂ * r = b₁⁻¹ * (b₁ * b₂ * r) := by group
        _ = b₁⁻¹ * (r * (b₁ * b₂)) := by rw [h]
        _ = b₁⁻¹ * (r * b₁ * b₂) := by group
        _ = b₁⁻¹ * (b₁ * r * b₂) := by rw [← hc]
        _ = r * b₂ := by group
    exact Subgroup.mul_mem _ (hm (hcen₁ b₁ hb₁ h₁)) (hm (hcen₂ b₂ hb₂ h₂))
  · have hc₁ : ∀ a ∈ Q₁, ∀ x ∈ Q₁ ⊔ Q₂, ⁅a, x⁆ ∈ Subgroup.zpowers z := by
      intro a ha x hx
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec x hx
      have hc' : x₂ * a⁻¹ = a⁻¹ * x₂ := (Commute.inv_right (hcomm a ha x₂ hx₂).symm).eq
      have h : ⁅a, x₁ * x₂⁆ = ⁅a, x₁⁆ := by
        simp only [commutatorElement_def]
        calc a * (x₁ * x₂) * a⁻¹ * (x₁ * x₂)⁻¹ = a * x₁ * (x₂ * a⁻¹) * x₂⁻¹ * x₁⁻¹ := by group
          _ = a * x₁ * (a⁻¹ * x₂) * x₂⁻¹ * x₁⁻¹ := by rw [hc']
          _ = a * x₁ * a⁻¹ * x₁⁻¹ := by group
      rw [h]
      exact hm (hcom₁ a ha x₁ hx₁)
    have hc₂ : ∀ b ∈ Q₂, ∀ x ∈ Q₁ ⊔ Q₂, ⁅b, x⁆ ∈ Subgroup.zpowers z := by
      intro b hb x hx
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec x hx
      have hc' : x₁ * b⁻¹ = b⁻¹ * x₁ := (Commute.inv_right (hcomm x₁ hx₁ b hb)).eq
      have h : ⁅b, x₁ * x₂⁆ = ⁅b, x₂⁆ := by
        rw [hcomm x₁ hx₁ x₂ hx₂]
        simp only [commutatorElement_def]
        calc b * (x₂ * x₁) * b⁻¹ * (x₂ * x₁)⁻¹ = b * x₂ * (x₁ * b⁻¹) * x₁⁻¹ * x₂⁻¹ := by group
          _ = b * x₂ * (b⁻¹ * x₁) * x₁⁻¹ * x₂⁻¹ := by rw [hc']
          _ = b * x₂ * b⁻¹ * x₂⁻¹ := by group
      rw [h]
      exact hm (hcom₂ b hb x₂ hx₂)
    intro a ha x hx
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdec a ha
    have h₂ := hc₂ a₂ ha₂ x hx
    have hcz : a₁ * ⁅a₂, x⁆ = ⁅a₂, x⁆ * a₁ :=
      commute_of_mem_zpowers h₂ (hzc a₁ (Subgroup.mem_sup_left ha₁))
    have h : ⁅a₁ * a₂, x⁆ = ⁅a₂, x⁆ * ⁅a₁, x⁆ := by
      calc ⁅a₁ * a₂, x⁆ = a₁ * ⁅a₂, x⁆ * a₁⁻¹ * ⁅a₁, x⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅a₂, x⁆ * ⁅a₁, x⁆ := by rw [hcz]; group
    rw [h]
    exact Subgroup.mul_mem _ h₂ (hc₁ a₁ ha₁ x hx)
  · refine sup_le Subgroup.le_normalizer fun b hb => ?_
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [← hcomm n hn b hb, mul_inv_cancel_right]
    exact hn
  · refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [hcomm a ha n hn, mul_inv_cancel_right]
    exact hn

private theorem swap_facts {Q₁ Q₂ : Subgroup G} {z τ : G}
    (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z)
    (hτmap : Q₁.map (MulAut.conj τ).toMonoidHom = Q₂) (hτ2 : τ * τ ∈ Q₁ ⊔ Q₂) :
    (∀ a ∈ Q₁, τ⁻¹ * a * τ ∈ Q₂) ∧ τ * z * τ⁻¹ = z := by
  have hzQ : z ∈ Q₁ ⊓ Q₂ := by
    rw [hinf]
    exact Subgroup.mem_zpowers z
  obtain ⟨hinv₂, -⟩ := quaternion_facts_of_mem e₂ hz hzQ.2
  have hN₁ := (central_product_facts e₁ e₂ hcomm hz hinf).2.2.2.2.1
  have hτ₁ : ∀ a ∈ Q₁, τ * a * τ⁻¹ ∈ Q₂ := fun a ha => by
    rw [← hτmap]
    exact ⟨a, ha, rfl⟩
  refine ⟨fun a ha => ?_, ?_⟩
  · have ha' : (τ * τ)⁻¹ * a * (τ * τ) ∈ Q₁ :=
      (Subgroup.mem_normalizer_iff''.mp (hN₁ hτ2) a).mp ha
    have hexp : τ⁻¹ * a * τ = τ * ((τ * τ)⁻¹ * a * (τ * τ)) * τ⁻¹ := by group
    rw [hexp]
    exact hτ₁ _ ha'
  · have hzz : z * z = 1 := mul_self_eq_one_of_mem_zpowers hz (Subgroup.mem_zpowers z)
    have hsq : τ * z * τ⁻¹ * (τ * z * τ⁻¹) = 1 := by
      calc τ * z * τ⁻¹ * (τ * z * τ⁻¹) = τ * (z * z) * τ⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    refine (hinv₂ _ (hτ₁ z hzQ.1) hsq).resolve_left fun h1 => ne_one_of_orderOf_eq_two hz ?_
    calc z = τ⁻¹ * (τ * z * τ⁻¹) * τ := by group
      _ = 1 := by rw [h1]; group

theorem card_eq_sixtyFour {Q₁ Q₂ P T : Subgroup G} {z τ : G}
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hP : Q₁ ⊔ Q₂ = P)
    (hτN : τ ∈ Subgroup.normalizer (P : Set G)) (hτ2 : τ * τ ∈ P) (hτP : τ ∉ P)
    (hT : P ⊔ Subgroup.zpowers τ = T) : Nat.card T = 64 := by
  obtain ⟨e₁⟩ := hQ₁
  obtain ⟨e₂⟩ := hQ₂
  subst hP hT
  rw [CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hτN hτ2 hτP,
    (central_product_facts e₁ e₂ hcomm hz hinf).1]

theorem centralizer_inter_eq {Q₁ Q₂ P T : Subgroup G} {z τ : G}
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hP : Q₁ ⊔ Q₂ = P)
    (hτN : τ ∈ Subgroup.normalizer (P : Set G))
    (hτmap : Q₁.map (MulAut.conj τ).toMonoidHom = Q₂) (hτ2 : τ * τ ∈ P) (hτP : τ ∉ P)
    (hT : P ⊔ Subgroup.zpowers τ = T) :
    T ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z := by
  obtain ⟨e₁⟩ := hQ₁
  obtain ⟨e₂⟩ := hQ₂
  subst hP hT
  obtain ⟨-, hzc, hcen, -, -, hN₂⟩ := central_product_facts e₁ e₂ hcomm hz hinf
  obtain ⟨hτ₁, hτz⟩ := swap_facts e₁ e₂ hcomm hz hinf hτmap hτ2
  have hzQ : z ∈ Q₁ ⊓ Q₂ := by
    rw [hinf]
    exact Subgroup.mem_zpowers z
  apply le_antisymm
  · rintro t ⟨htT, htc⟩
    have htc' := Subgroup.mem_centralizer_iff.mp htc
    by_cases htP : t ∈ Q₁ ⊔ Q₂
    · exact hcen t htP fun a ha => (htc' a (Subgroup.mem_sup_left ha)).symm
    · exfalso
      have hp : t * τ ∈ Q₁ ⊔ Q₂ := mul_mem_of_mem_sup_zpowers hτN hτ2 hτP htT htP
      obtain ⟨-, -, -, -, i, hi, _j, _hj, hii, -⟩ := quaternion_facts_of_mem e₁ hz hzQ.1
      have hti : t * i * t⁻¹ = i := by
        rw [← htc' i (Subgroup.mem_sup_left (Subgroup.mem_sup_left hi)), mul_inv_cancel_right]
      have hmem : t * i * t⁻¹ ∈ Q₂ := by
        have h := (Subgroup.mem_normalizer_iff.mp (hN₂ hp) _).mp (hτ₁ i hi)
        have hexp : t * i * t⁻¹ = t * τ * (τ⁻¹ * i * τ) * (t * τ)⁻¹ := by group
        rw [hexp]
        exact h
      rw [hti] at hmem
      have hiz : i ∈ Subgroup.zpowers z := by
        rw [← hinf]
        exact ⟨hi, hmem⟩
      exact ne_one_of_orderOf_eq_two hz (hii.symm.trans (mul_self_eq_one_of_mem_zpowers hz hiz))
  · rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hzQ.1), ?_⟩
    have hle : Q₁ ⊔ Q₂ ⊔ Subgroup.zpowers τ ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hzc a ha)) ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc τ * z = τ * z * τ⁻¹ * τ := by group
        _ = z * τ := by rw [hτz]
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ht)

theorem card_centralizer_ge_sixteen {Q₁ Q₂ P T : Subgroup G} {z τ : G}
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hP : Q₁ ⊔ Q₂ = P)
    (hτN : τ ∈ Subgroup.normalizer (P : Set G))
    (hτmap : Q₁.map (MulAut.conj τ).toMonoidHom = Q₂) (hτ2 : τ * τ ∈ P) (hτP : τ ∉ P)
    (hT : P ⊔ Subgroup.zpowers τ = T) :
    ∀ x ∈ T, orderOf x = 2 →
      16 ≤ Nat.card (T ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  obtain ⟨e₁⟩ := hQ₁
  obtain ⟨e₂⟩ := hQ₂
  subst hP hT
  obtain ⟨hcard, hzc, -, hcom, -, hN₂⟩ := central_product_facts e₁ e₂ hcomm hz hinf
  obtain ⟨hτ₁, hτz⟩ := swap_facts e₁ e₂ hcomm hz hinf hτmap hτ2
  have hzQ : z ∈ Q₁ ⊓ Q₂ := by
    rw [hinf]
    exact Subgroup.mem_zpowers z
  have hcardz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hz1 := ne_one_of_orderOf_eq_two hz
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_zpowers hz (Subgroup.mem_zpowers z)
  intro x hxT hx2
  by_cases hxP : x ∈ Q₁ ⊔ Q₂
  · have h := card_le_mul_card_inf_centralizer hzc fun a ha => hcom a ha x hxP
    rw [hcard, hcardz] at h
    have := Subgroup.card_le_of_le (inf_le_inf_right (Subgroup.centralizer ({x} : Set G))
      (le_sup_left : Q₁ ⊔ Q₂ ≤ Q₁ ⊔ Q₂ ⊔ Subgroup.zpowers τ))
    omega
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hp : x * τ ∈ Q₁ ⊔ Q₂ := mul_mem_of_mem_sup_zpowers hτN hτ2 hτP hxT hxP
  have hxQ : ∀ a ∈ Q₁, x * a * x⁻¹ ∈ Q₂ := by
    intro a ha
    have h := (Subgroup.mem_normalizer_iff.mp (hN₂ hp) _).mp (hτ₁ a ha)
    have hexp : x * a * x⁻¹ = x * τ * (τ⁻¹ * a * τ) * (x * τ)⁻¹ := by group
    rw [hexp]
    exact h
  have hxz : x * z * x⁻¹ = z := by
    have hτz' : τ⁻¹ * z * τ = z := by
      calc τ⁻¹ * z * τ = τ⁻¹ * (τ * z * τ⁻¹) * τ := by rw [hτz]
        _ = z := by group
    calc x * z * x⁻¹ = x * τ * (τ⁻¹ * z * τ) * (x * τ)⁻¹ := by group
      _ = x * τ * z * (x * τ)⁻¹ := by rw [hτz']
      _ = z := by rw [hzc _ hp, mul_inv_cancel_right]
  let ψ : ↥Q₁ →* G :=
    { toFun := fun q => (q : G) * (x * q * x⁻¹)
      map_one' := by simp
      map_mul' := fun q r => by
        show (q : G) * r * (x * (q * r) * x⁻¹) =
          (q : G) * (x * q * x⁻¹) * ((r : G) * (x * r * x⁻¹))
        have hc := hcomm r r.2 _ (hxQ q q.2)
        calc (q : G) * r * (x * (q * r) * x⁻¹) = q * (r * (x * q * x⁻¹)) * (x * r * x⁻¹) := by
              group
          _ = q * ((x * q * x⁻¹) * r) * (x * r * x⁻¹) := by rw [hc]
          _ = q * (x * q * x⁻¹) * (r * (x * r * x⁻¹)) := by group }
  have hψ : ∀ q : ↥Q₁, ψ q = (q : G) * (x * q * x⁻¹) := fun q => rfl
  have hRP : ψ.range ≤ (Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨q, rfl⟩
    rw [hψ, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨Subgroup.mul_mem_sup q.2 (hxQ q q.2), ?_⟩
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hc := hcomm q q.2 _ (hxQ q q.2)
    rw [hxinv] at hc ⊢
    calc (q : G) * (x * q * x) * x = q * x * q * (x * x) := by group
      _ = x * x * (q * x * q) := by rw [hxx, mul_one, one_mul]
      _ = x * (x * q * x * q) := by group
      _ = x * (q * (x * q * x)) := by rw [← hc]
  have hzR : z ∉ ψ.range := by
    rintro ⟨q, hq⟩
    rw [hψ] at hq
    have h1 : x * q * x⁻¹ ∈ Q₁ := by
      have hexp : x * q * x⁻¹ = (q : G)⁻¹ * z := by
        rw [← hq]
        group
      rw [hexp]
      exact Q₁.mul_mem (Q₁.inv_mem q.2) hzQ.1
    have h2 : x * q * x⁻¹ ∈ Subgroup.zpowers z := by
      rw [← hinf]
      exact ⟨h1, hxQ q q.2⟩
    rcases eq_one_or_eq_of_mem_zpowers hz h2 with h | h
    · have hq1 : (q : G) = 1 := by
        calc (q : G) = x⁻¹ * (x * q * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      rw [h, hq1, one_mul] at hq
      exact hz1 hq.symm
    · rw [h] at hq
      have hq1 : (q : G) = 1 := mul_eq_right.mp hq
      rw [hq1, mul_one, mul_inv_cancel] at h
      exact hz1 h.symm
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hle : ψ.ker.map Q₁.subtype ≤ Subgroup.zpowers z := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) * (x * q * x⁻¹) = 1 := hq
      have h1 : x * q * x⁻¹ = (q : G)⁻¹ := eq_inv_of_mul_eq_one_right hq'
      have h2 : (q : G)⁻¹ ∈ Subgroup.zpowers z := by
        rw [← hinf]
        exact ⟨Q₁.inv_mem q.2, h1 ▸ hxQ q q.2⟩
      have h3 := (Subgroup.zpowers z).inv_mem h2
      rwa [inv_inv] at h3
    have h := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective Q₁.subtype_injective, hcardz] at h
  have hrange : 4 ≤ Nat.card ψ.range := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [card_eq_eight_of_quaternion e₁] at h
    have h' := Nat.mul_le_mul_right (Nat.card ψ.range) hker
    rw [h] at h'
    omega
  have hzN : z ∈ Subgroup.normalizer (ψ.range : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [← hzc n (hRP hn).1, mul_inv_cancel_right]
    exact hn
  have hcard1 := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hzN
    (by rw [hzz]; exact ψ.range.one_mem) hzR
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * x = x * z * x⁻¹ * x := by rw [hxz]
      _ = x * z := by group
  have hle1 : ψ.range ⊔ Subgroup.zpowers z ≤
      (Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({x} : Set G) :=
    sup_le hRP (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left hzQ.1, hzx⟩)
  have hC8 : 8 ≤ Nat.card ((Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    have := Subgroup.card_le_of_le hle1
    omega
  have hxN : x ∈ Subgroup.normalizer
      (((Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hn.2, mul_inv_cancel_right]
    exact hn
  have hcard2 := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hxN
    (by rw [hxx]; exact Subgroup.one_mem _) fun h => hxP h.1
  have hle2 : (Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers x ≤
      (Q₁ ⊔ Q₂ ⊔ Subgroup.zpowers τ) ⊓ Subgroup.centralizer ({x} : Set G) :=
    sup_le (inf_le_inf_right _ le_sup_left)
      (Subgroup.zpowers_le.mpr ⟨hxT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have := Subgroup.card_le_of_le hle2
  omega

theorem exists_elemAbelian_eight {Q₁ Q₂ P : Subgroup G} {z : G}
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) (hz : orderOf z = 2)
    (hinf : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hP : Q₁ ⊔ Q₂ = P) :
    ∃ E : Subgroup G, E ≤ P ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨e₁⟩ := hQ₁
  obtain ⟨e₂⟩ := hQ₂
  subst hP
  have hzQ : z ∈ Q₁ ⊓ Q₂ := by
    rw [hinf]
    exact Subgroup.mem_zpowers z
  obtain ⟨-, -, -, -, i₁, hi₁, j₁, hj₁, hii₁, hjj₁, hji₁, hjiji₁⟩ :=
    quaternion_facts_of_mem e₁ hz hzQ.1
  obtain ⟨-, -, -, -, i₂, hi₂, j₂, hj₂, hii₂, hjj₂, hji₂, -⟩ := quaternion_facts_of_mem e₂ hz hzQ.2
  have hzc := (central_product_facts e₁ e₂ hcomm hz hinf).2.1
  have hz1 := ne_one_of_orderOf_eq_two hz
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_zpowers hz (Subgroup.mem_zpowers z)
  have hcardz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hred : ∀ {a b : G}, a ∈ Q₁ → b ∈ Q₂ → a * b ∈ Subgroup.zpowers z →
      a ∈ Subgroup.zpowers z := by
    intro a b ha hb hab
    rw [← hinf] at hab ⊢
    refine ⟨ha, ?_⟩
    have h := Q₂.mul_mem hab.2 (Q₂.inv_mem hb)
    rwa [mul_inv_cancel_right] at h
  have hsqz : ∀ {a : G}, a * a = z → a ∉ Subgroup.zpowers z := fun haa ha =>
    hz1 (haa.symm.trans (mul_self_eq_one_of_mem_zpowers hz ha))
  have huP : i₁ * i₂ ∈ Q₁ ⊔ Q₂ := Subgroup.mul_mem_sup hi₁ hi₂
  have hvP : j₁ * j₂ ∈ Q₁ ⊔ Q₂ := Subgroup.mul_mem_sup hj₁ hj₂
  have huu : i₁ * i₂ * (i₁ * i₂) = 1 := by
    calc i₁ * i₂ * (i₁ * i₂) = i₁ * (i₂ * i₁) * i₂ := by group
      _ = i₁ * (i₁ * i₂) * i₂ := by rw [hcomm i₁ hi₁ i₂ hi₂]
      _ = i₁ * i₁ * (i₂ * i₂) := by group
      _ = 1 := by rw [hii₁, hii₂, hzz]
  have hvv : j₁ * j₂ * (j₁ * j₂) = 1 := by
    calc j₁ * j₂ * (j₁ * j₂) = j₁ * (j₂ * j₁) * j₂ := by group
      _ = j₁ * (j₁ * j₂) * j₂ := by rw [hcomm j₁ hj₁ j₂ hj₂]
      _ = j₁ * j₁ * (j₂ * j₂) := by group
      _ = 1 := by rw [hjj₁, hjj₂, hzz]
  have h12 : j₂ * i₁ = i₁ * j₂ := (hcomm i₁ hi₁ j₂ hj₂).symm
  have huv : j₁ * j₂ * (i₁ * i₂) = i₁ * i₂ * (j₁ * j₂) := by
    have hz2 : z * (i₂ * j₂) = i₂ * j₂ * z :=
      (hzc _ (Subgroup.mem_sup_right (Q₂.mul_mem hi₂ hj₂))).symm
    calc j₁ * j₂ * (i₁ * i₂) = j₁ * (j₂ * i₁) * i₂ := by group
      _ = j₁ * (i₁ * j₂) * i₂ := by rw [h12]
      _ = j₁ * i₁ * (j₂ * i₂) := by group
      _ = i₁ * j₁ * z * (i₂ * j₂ * z) := by rw [hji₁, hji₂]
      _ = i₁ * j₁ * (z * (i₂ * j₂)) * z := by group
      _ = i₁ * j₁ * (i₂ * j₂ * z) * z := by rw [hz2]
      _ = i₁ * j₁ * (i₂ * j₂) * (z * z) := by group
      _ = i₁ * (j₁ * i₂) * j₂ := by rw [hzz, mul_one]; group
      _ = i₁ * (i₂ * j₁) * j₂ := by rw [hcomm j₁ hj₁ i₂ hi₂]
      _ = i₁ * i₂ * (j₁ * j₂) := by group
  have hu : i₁ * i₂ ∉ Subgroup.zpowers z := fun h => hsqz hii₁ (hred hi₁ hi₂ h)
  have hv : j₁ * j₂ ∉ Subgroup.zpowers z := fun h => hsqz hjj₁ (hred hj₁ hj₂ h)
  have hvu : j₁ * j₂ * (i₁ * i₂) ∉ Subgroup.zpowers z := by
    intro h
    have hexp : j₁ * j₂ * (i₁ * i₂) = j₁ * i₁ * (j₂ * i₂) := by
      calc j₁ * j₂ * (i₁ * i₂) = j₁ * (j₂ * i₁) * i₂ := by group
        _ = j₁ * (i₁ * j₂) * i₂ := by rw [h12]
        _ = j₁ * i₁ * (j₂ * i₂) := by group
    rw [hexp] at h
    exact hsqz hjiji₁ (hred (Q₁.mul_mem hj₁ hi₁) (Q₂.mul_mem hj₂ hi₂) h)
  have hcz : ∀ g ∈ Q₁ ⊔ Q₂, ∀ c ∈ Subgroup.zpowers z, g * c = c * g := fun g hg c hc =>
    commute_of_mem_zpowers hc (hzc g hg)
  have huN : i₁ * i₂ ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [hcz _ huP n hn, mul_inv_cancel_right]
    exact hn
  have hu1 : i₁ * i₂ * (i₁ * i₂) ∈ Subgroup.zpowers z := by
    rw [huu]
    exact Subgroup.one_mem _
  have hA := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem huN hu1 hu
  have hvA : Subgroup.zpowers z ⊔ Subgroup.zpowers (i₁ * i₂) ≤
      Subgroup.centralizer ({j₁ * j₂} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc _ hvP).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr huv.symm
  have hvN : j₁ * j₂ ∈ Subgroup.normalizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers (i₁ * i₂) : Subgroup G) : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hvA hn), mul_inv_cancel_right]
    exact hn
  have hvA' : j₁ * j₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers (i₁ * i₂) := fun h =>
    hvu (mul_mem_of_mem_sup_zpowers huN hu1 hu h hv)
  have hE := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hvN
    (by rw [hvv]; exact Subgroup.one_mem _) hvA'
  refine ⟨Subgroup.zpowers z ⊔ Subgroup.zpowers (i₁ * i₂) ⊔ Subgroup.zpowers (j₁ * j₂),
    sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzQ.1))
      (Subgroup.zpowers_le.mpr huP)) (Subgroup.zpowers_le.mpr hvP), ?_, by rw [hE, hA, hcardz]⟩
  have hEz : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact hzz)
  have hEu : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers (i₁ * i₂)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact huu)
  have hEv : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers (j₁ * j₂)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact hvv)
  have hcA : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers (i₁ * i₂), a * b = b * a :=
    fun a ha b hb => commute_of_mem_zpowers hb (hcz _ huP a ha).symm
  have hcE : ∀ a ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (i₁ * i₂),
      ∀ b ∈ Subgroup.zpowers (j₁ * j₂), a * b = b * a :=
    fun a ha b hb => commute_of_mem_zpowers hb (Subgroup.mem_centralizer_singleton_iff.mp (hvA ha))
  exact (hEz.sup_of_commute hEu hcA).sup_of_commute hEv hcE

end CFSG.RankThree.GF2n.Parrott.Remarks
