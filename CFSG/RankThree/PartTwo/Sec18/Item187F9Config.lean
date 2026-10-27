module

public import CFSG.RankThree.PartTwo.Sec18.Item187F4Shape
public import CFSG.RankThree.PartTwo.Sec18.Item187F7Nonab
public import CFSG.RankThree.PartTwo.Sec18.Item187F8Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

private theorem mem_Fix_iff_forall {V : Type} [Group V] {L : Subgroup (MulAut V)} {v : V} :
    v ∈ Fix L ↔ ∀ f ∈ L, f v = v :=
  ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
    fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩

private theorem index_Fix_le_of_le {V : Type} [Group V] [Finite V] {L L' : Subgroup (MulAut V)}
    (h : L ≤ L') : (Fix L).index ≤ (Fix L').index := by
  have hsub : Fix L' ≤ Fix L := fun v hv =>
    mem_Fix_iff_forall.2 fun f hf => mem_Fix_iff_forall.1 hv f (h hf)
  exact Subgroup.index_antitone hsub

private theorem index_Fix_conj {V : Type} [Group V] [Finite V] (c r : MulAut V) :
    (Fix (Subgroup.zpowers (c * r * c⁻¹))).index = (Fix (Subgroup.zpowers r)).index := by
  have hset : Fix (Subgroup.zpowers (c * r * c⁻¹)) =
      (Fix (Subgroup.zpowers r)).map (MulEquiv.toMonoidHom (c : V ≃* V)) := by
    ext v
    constructor
    · intro hv
      refine Subgroup.mem_map.2
        ⟨c⁻¹ v, mem_Fix_iff_forall.2 fun f hf => ?_, MulAut.apply_inv_self V c v⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      have h1 := mem_Fix_iff_forall.1 hv _ (Subgroup.zpow_mem_zpowers _ k)
      rw [conj_zpow, MulAut.mul_apply V, MulAut.mul_apply V] at h1
      calc (r ^ k) (c⁻¹ v) = c⁻¹ (c ((r ^ k) (c⁻¹ v))) := (MulAut.inv_apply_self V c _).symm
        _ = c⁻¹ v := by rw [h1]
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hv
      rw [← hwv]
      refine mem_Fix_iff_forall.2 fun f hf => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      have hw' := mem_Fix_iff_forall.1 hw (r ^ k) (Subgroup.zpow_mem_zpowers _ k)
      change ((c * r * c⁻¹) ^ k) (c w) = c w
      rw [conj_zpow, MulAut.mul_apply V, MulAut.mul_apply V, MulAut.inv_apply_self V c, hw']
  rw [hset]
  exact Subgroup.index_map_equiv _ (c : V ≃* V)

private theorem sq_mem_of_relIndex_le_two {V : Type} [Group V] [Finite V]
    {D D₀ : Subgroup (MulAut V)} (hle : D₀ ≤ D) (h2 : D₀.relIndex D ≤ 2) {x : MulAut V}
    (hx : x ∈ D) : x ^ 2 ∈ D₀ := by
  by_cases h1 : D₀.relIndex D = 1
  · exact D₀.pow_mem (Subgroup.relIndex_eq_one.1 h1 hx) 2
  · have hidx : (D₀.subgroupOf D).index = 2 := by
      have h0 : (D₀.subgroupOf D).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
      unfold Subgroup.relIndex at h1 h2
      omega
    haveI : (D₀.subgroupOf D).Normal := Subgroup.normal_of_index_eq_two hidx
    have key := Subgroup.pow_index_mem (D₀.subgroupOf D) ⟨x, hx⟩
    rw [hidx] at key
    exact Subgroup.mem_subgroupOf.1 key

private theorem card_le_two_of_isCyclic {V : Type} [Group V] [Finite V]
    {S E : Subgroup (MulAut V)} [IsCyclic S] (hES : E ≤ S) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 := by
  classical
  haveI : IsCyclic E := Subgroup.isCyclic_of_le hES
  haveI : Fintype E := Fintype.ofFinite E
  have h := IsCyclic.card_pow_eq_one_le (α := E) (n := 2) (by norm_num)
  have hall : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa [sq] using hE2 a.1 a.2)
  simp only [hall, Finset.filter_true, Finset.card_univ] at h
  rw [Nat.card_eq_fintype_card]
  exact h

private theorem commutator_le_of_normalizes {V : Type} [Group V] {P : Subgroup (MulAut V)}
    {z : MulAut V} (hzP : z ∈ Subgroup.normalizer (P : Set (MulAut V))) :
    ⁅P, Subgroup.zpowers z⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro p hp w hw
  have hwP : w ∈ Subgroup.normalizer (P : Set (MulAut V)) := Subgroup.zpowers_le.2 hzP hw
  have h : w * p⁻¹ * w⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hwP p⁻¹).1 (P.inv_mem hp)
  have e : ⁅p, w⁆ = p * (w * p⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact P.mul_mem hp h

private theorem isPGroup_commutator_zpowers {V : Type} [Group V] {P : Subgroup (MulAut V)}
    {z : MulAut V} (hP5 : IsPGroup 5 P) (hzP : z ∈ Subgroup.normalizer (P : Set (MulAut V))) :
    IsPGroup 5 ↥⁅P, Subgroup.zpowers z⁆ :=
  IsPGroup.to_le hP5 (commutator_le_of_normalizes hzP)

private theorem sixteen_le_index_Fix_commutator {V : Type} [Group V] [Finite V]
    (hV : ∀ v : V, v * v = 1)
    {P : Subgroup (MulAut V)} {z : MulAut V} (hP5 : IsPGroup 5 P) (hz2 : z * z = 1)
    (hzP : z ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (hKnc : ¬ IsCyclic ↥⁅P, Subgroup.zpowers z⁆) : 16 ≤ (Fix (Subgroup.zpowers z)).index := by
  obtain ⟨hgen, hinv⟩ := commutator_zpowers_inverted hz2 hzP
  exact sixteen_le_index_fix hV (isPGroup_commutator_zpowers hP5 hzP) hKnc hz2 _ hgen.symm
    (fun y hy => by obtain ⟨p, hp, rfl⟩ := hy; exact hinv p hp)

private theorem conj_mem_commutator_zpowers {V : Type} [Group V] {P : Subgroup (MulAut V)}
    {z g : MulAut V}
    (hgP : g ∈ Subgroup.normalizer (P : Set (MulAut V))) (hgz : g * z * g⁻¹ = z)
    {k : MulAut V} (hk : k ∈ ⁅P, Subgroup.zpowers z⁆) :
    g * k * g⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆ := by
  have hgz' : ∀ n : ℤ, g * z ^ n * g⁻¹ = z ^ n := fun n => by
    rw [← conj_zpow, hgz]
  have hle : ⁅P, Subgroup.zpowers z⁆ ≤
      (⁅P, Subgroup.zpowers z⁆).comap (MulEquiv.toMonoidHom (MulAut.conj g)) := by
    rw [Subgroup.commutator_le]
    intro p hp w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [Subgroup.mem_comap]
    have hp' : g * p * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hgP p).1 hp
    have hw' : g * z ^ n * g⁻¹ ∈ Subgroup.zpowers z := by
      rw [hgz' n]
      exact Subgroup.zpow_mem_zpowers z n
    have e : (MulEquiv.toMonoidHom (MulAut.conj g)) ⁅p, z ^ n⁆ =
        ⁅g * p * g⁻¹, g * z ^ n * g⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hp' hw'
  exact hle hk

private theorem normalizer_commutator_zpowers {V : Type} [Group V] {P : Subgroup (MulAut V)}
    {z g : MulAut V} (hgP : g ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (hgz : g * z * g⁻¹ = z) :
    g ∈ Subgroup.normalizer ((⁅P, Subgroup.zpowers z⁆ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_commutator_zpowers hgP hgz hh, fun hh => ?_⟩
  have hg'P : g⁻¹ ∈ Subgroup.normalizer (P : Set (MulAut V)) := Subgroup.inv_mem _ hgP
  have hzg : g * z = z * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  have hg'z : g⁻¹ * z * g⁻¹⁻¹ = z := by
    calc g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hzg]
      _ = z := by group
  have key := conj_mem_commutator_zpowers hg'P hg'z hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at key
  exact key

theorem bad_config_false {V : Type} [Group V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (P S E : Subgroup (MulAut V)) (c : MulAut V)
    (hP5 : IsPGroup 5 P) (hS2 : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hcP : c ∈ Subgroup.normalizer (P : Set (MulAut V)))
    (hcS : c ∈ Subgroup.normalizer (S : Set (MulAut V))) (hc3 : c ^ 3 = 1)
    (hfaith : ∀ s ∈ S, (∀ p ∈ P, s * p = p * s) → s = 1)
    (hshape : Shape81 S c)
    (hperf : (IsCyclic S ∧ ∀ s ∈ S, c * s * c⁻¹ = s) → ⁅P, Subgroup.zpowers c⁆ = P)
    (hES : E ≤ S) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE1 : E ≠ ⊥) (hoff : (Fix E).index ≤ 2 * Nat.card E) : False := by
  have hnontriv : ∀ z ∈ S, z ≠ 1 → ∃ p ∈ P, z * p ≠ p * z := by
    intro z hz hz1
    by_contra hcon
    exact hz1 (hfaith z hz fun p hp => by
      by_contra hne
      exact hcon ⟨p, hp, hne⟩)
  unfold Shape81 at hshape
  rcases hshape with ⟨hScyc, hcS'⟩ |
    ⟨z, hzS, hzo, hzc, hzcen, hrz, hEcl, Q, hQS, hzcomm, _hQc, hQgen⟩
  ·
    haveI : IsCyclic S := hScyc
    obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 := by
      rcases E.bot_or_exists_ne_one with h | h
      · exact absurd h hE1
      · exact h
    have hzS : z ∈ S := hES hzE
    have hz2 : z * z = 1 := hE2 z hzE
    have hzP : z ∈ Subgroup.normalizer (P : Set (MulAut V)) := hSP hzS
    have hzc' : z * c = c * z := by
      have h := hcS' z hzS
      calc z * c = c * z * c⁻¹ * c := by rw [h]
        _ = c * z := by group
    have hcard := card_le_two_of_isCyclic hES hE2
    have hz : ∃ p ∈ P, z * p ≠ p * z := hnontriv z hzS hz1
    have hKnc := not_isCyclic_commutator_cyc hP5 hz2 hc3 hzP hcP hzc' (hperf ⟨hScyc, hcS'⟩) hz
    have h16 := sixteen_le_index_Fix_commutator hV hP5 hz2 hzP hKnc
    have hle := index_Fix_le_of_le (Subgroup.zpowers_le.2 hzE)
    omega
  ·
    have hz2 : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rw [hzo, sq] at h
      exact h
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      norm_num at hzo
    have hzP : z ∈ Subgroup.normalizer (P : Set (MulAut V)) := hSP hzS
    have hzQ : ∀ q ∈ Q, q * z = z * q := fun q hq => hzcen q (hQS hq)
    have hQP : Q ≤ Subgroup.normalizer (P : Set (MulAut V)) := fun q hq => hSP (hQS hq)
    have hKnc := not_isCyclic_commutator_q8 hP5 hz2 hQP hzP hzQ hzcomm (hnontriv z hzS hz1)
    obtain ⟨hEcard, hzE | ⟨r, hrS, hro, hrz', hEr⟩⟩ := hEcl E hES hEab hE2 hE1
    ·
      have h16 := sixteen_le_index_Fix_commutator hV hP5 hz2 hzP hKnc
      have hle := index_Fix_le_of_le (Subgroup.zpowers_le.2 hzE)
      omega
    ·
      have hzeq : z = (r * (c * r * c⁻¹)) ^ 2 := hrz r hrS hro hrz'
      have hFr : (Fix (Subgroup.zpowers r)).index ≤ 4 := by
        have h := hoff
        rw [hEr, Nat.card_zpowers, hro] at h
        omega
      have hle16 : (Fix (Subgroup.zpowers z)).index ≤ 16 := by
        have hmul := index_fix_le_mul (F₁ := Subgroup.zpowers r)
          (F₂ := Subgroup.zpowers (c * r * c⁻¹)) (F := Subgroup.zpowers z) ?_
        · have hFc := index_Fix_conj c r
          calc (Fix (Subgroup.zpowers z)).index ≤
                (Fix (Subgroup.zpowers r)).index * (Fix (Subgroup.zpowers (c * r * c⁻¹))).index :=
                hmul
            _ ≤ 4 * 4 := by rw [hFc]; exact Nat.mul_le_mul hFr hFr
            _ = 16 := by norm_num
        · intro v h1 h2
          have hrv : (r * (c * r * c⁻¹)) v = v := by
            rw [MulAut.mul_apply V, h2 _ (Subgroup.mem_zpowers _), h1 _ (Subgroup.mem_zpowers _)]
          have hzv : z v = v := by
            rw [hzeq, sq, MulAut.mul_apply V, hrv, hrv]
          have hzst : z ∈ MulAction.stabilizer (MulAut V) v := MulAction.mem_stabilizer_iff.2 hzv
          intro f hf
          exact MulAction.mem_stabilizer_iff.1 (Subgroup.zpowers_le.2 hzst hf)
      obtain ⟨hgen, hinv⟩ := commutator_zpowers_inverted hz2 hzP
      have hQK : Q ≤ Subgroup.normalizer
          ((⁅P, Subgroup.zpowers z⁆ : Subgroup (MulAut V)) : Set (MulAut V)) :=
        fun q hq =>
          normalizer_commutator_zpowers (hQP hq) (by rw [hzQ q hq, mul_inv_cancel_right])
      have hcK : c ∈ Subgroup.normalizer
          ((⁅P, Subgroup.zpowers z⁆ : Subgroup (MulAut V)) : Set (MulAut V)) :=
        normalizer_commutator_zpowers hcP hzc
      have hDK : Q ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer
          ((⁅P, Subgroup.zpowers z⁆ : Subgroup (MulAut V)) : Set (MulAut V)) :=
        sup_le hQK (Subgroup.zpowers_le.2 hcK)
      have heD : z ∈ ⁅Q ⊔ Subgroup.zpowers c, Q ⊔ Subgroup.zpowers c⁆ :=
        Subgroup.commutator_mono le_sup_left le_sup_left hzcomm
      have hinv' : ∀ y ∈ {y : MulAut V | ∃ p ∈ P, y = ⁅p, z⁆}, z * y * z⁻¹ = y⁻¹ :=
        fun y hy => by
          obtain ⟨p, hp, rfl⟩ := hy
          exact hinv p hp
      have hD : ∀ D₀ : Subgroup (MulAut V), D₀ ≤ Q ⊔ Subgroup.zpowers c →
          D₀.relIndex (Q ⊔ Subgroup.zpowers c) ≤ 2 → D₀ = Q ⊔ Subgroup.zpowers c := by
        intro D₀ hle h2
        have hcD : c ∈ Q ⊔ Subgroup.zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
        have hc2 : c ^ 2 ∈ D₀ := sq_mem_of_relIndex_le_two hle h2 hcD
        have hc4 : (c ^ 2) ^ 2 ∈ D₀ := D₀.pow_mem hc2 2
        have e4 : (c ^ 2) ^ 2 = c := by
          calc (c ^ 2) ^ 2 = c ^ 3 * c := by group
            _ = c := by rw [hc3, one_mul]
        rw [e4] at hc4
        have hcD₀ : c ∈ D₀ := hc4
        have hcomm : ∀ t ∈ Q, t * (c * t * c⁻¹)⁻¹ ∈ D₀ := by
          intro t ht
          have htD : t ∈ Q ⊔ Subgroup.zpowers c := Subgroup.mem_sup_left ht
          have hu : (t * c) ^ 2 ∈ D₀ :=
            sq_mem_of_relIndex_le_two hle h2 ((Q ⊔ Subgroup.zpowers c).mul_mem htD hcD)
          have ht2 : t ^ 2 ∈ D₀ := sq_mem_of_relIndex_le_two hle h2 htD
          have key : t * (c * t * c⁻¹)⁻¹ = (t * c) ^ 2 * c⁻¹ * (t ^ 2)⁻¹ * c⁻¹ := by
            simp only [sq]
            group
          rw [key]
          exact D₀.mul_mem (D₀.mul_mem (D₀.mul_mem hu (D₀.inv_mem hcD₀)) (D₀.inv_mem ht2))
            (D₀.inv_mem hcD₀)
        have hQD₀ : Q ≤ D₀ := fun q hq =>
          (Subgroup.closure_le D₀).2 (by rintro x ⟨t, ht, rfl⟩; exact hcomm t ht) (hQgen q hq)
        exact le_antisymm hle (sup_le hQD₀ (Subgroup.zpowers_le.2 hcD₀))
      have h64 := sixtyfour_le_index_fix hV (isPGroup_commutator_zpowers hP5 hzP) hKnc hz2 _
        hgen.symm hinv' hDK heD hD
      omega

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
