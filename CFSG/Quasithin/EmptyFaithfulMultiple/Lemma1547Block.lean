module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Facts
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

structure IsA4 (X Q : Subgroup G) : Prop where
  le : Q ≤ X
  normal : X ≤ Subgroup.normalizer (Q : Set G)
  card_Q : Nat.card Q = 4
  sq : ∀ q ∈ Q, q ^ 2 = 1
  card : Nat.card X = 12
  cube : ∀ x ∈ X, x ^ 3 ∈ Q
  fpf : ∀ p ∈ X, orderOf p = 3 → ∀ q ∈ Q, p * q = q * p → q = 1

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := (MulAut.conj g).injective hyx
  rwa [← this]

theorem le_normalizer_sup [Finite G] {A B C : Subgroup G}
    (hA : C ≤ Subgroup.normalizer (A : Set G)) (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro c hc
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hmap : (A ⊔ B).map (MulAut.conj c).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hA hc) a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hB hc) b).mp hb
  exact hmap ⟨x, hx, rfl⟩

theorem card_evenWeight_three : Nat.card (Multiplicative ↥(evenWeight 3)) = 4 := by
  have : Nat.card (Multiplicative ↥(evenWeight 3)) =
      Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rfl))
  rw [this, Nat.card_eq_fintype_card]
  decide

section Short

variable [Finite G] {X : Subgroup G}

theorem isA4_of_isAltType (hX : IsShort2 X) (halt : IsAltType X 3) : IsA4 X (pCoreOf 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := pCoreOf 2 X with hQdef
  set U : Subgroup G := blockU X with hUdef
  have hUQX : U = ⁅Q, X⁆ := rfl
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 X
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 X
  obtain ⟨α, hαs, hαker, β, hβs, hβker, -⟩ := halt
  have hcardQ' : Nat.card Q = Nat.card (CFSG.pCore 2 X) := by
    rw [hQdef, pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  have hA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl
  have hcardX : Nat.card X = 3 * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv, hA3, hαker,
      hcardQ']
  have hcube : ∀ x ∈ X, x ^ 3 ∈ Q := by
    intro x hx
    have h1 : α (⟨x, hx⟩ ^ 3) = 1 := by
      have h := pow_card_eq_one' (x := α ⟨x, hx⟩)
      rw [hA3] at h
      rw [map_pow, h]
    have h2 : (⟨x, hx⟩ : X) ^ 3 ∈ CFSG.Open.pCore 2 X := by
      rw [← hαker]
      exact h1
    exact ⟨_, h2, rfl⟩
  have hZU : blockZ X ≤ U := inf_le_left
  have hcardU : Nat.card U = 4 * Nat.card (blockZ X) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, card_evenWeight_three]
  obtain ⟨hshort1, -, ⟨hUZQ, hU2⟩, -, -⟩ := hX
  have hUQ : U ≤ Q := hUZQ.trans inf_le_left
  have hUC : U ≤ Subgroup.centralizer (Q : Set G) := hUZQ.trans inf_le_right
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have hmap : U.map (MulAut.conj x).toMonoidHom ≤ U := by
      rw [hUQX, Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hXQ hx) q).mp hq
      · rintro _ ⟨y, hy, rfl⟩
        exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
    exact hmap ⟨u, hu, rfl⟩
  obtain ⟨p₀, hp₀⟩ := exists_prime_orderOf_dvd_card' (G := X) 3
    (by rw [hcardX]; exact dvd_mul_right 3 _)
  have hsup : ∀ p ∈ X, orderOf p = 3 → Q ⊔ Subgroup.zpowers p = X := by
    intro p hpX hp
    refine Subgroup.eq_of_le_of_card_ge (sup_le hQX (Subgroup.zpowers_le.mpr hpX)) ?_
    rw [hcardX]
    have h1 : Nat.card Q ∣ Nat.card ↥(Q ⊔ Subgroup.zpowers p) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : 3 ∣ Nat.card ↥(Q ⊔ Subgroup.zpowers p) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers p ≤ Q ⊔ Subgroup.zpowers p)
      rwa [Nat.card_zpowers, hp] at this
    have hcop : Nat.Coprime 3 (Nat.card Q) := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h2 h1)
  have hmem : ∀ p ∈ X, orderOf p = 3 → ∀ x ∈ X, ∃ q ∈ Q, ∃ y ∈ Subgroup.zpowers p, x = q * y := by
    intro p hpX hp x hx
    have hpQ : Subgroup.zpowers p ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.zpowers_le.mpr hpX).trans hXQ
    have : x ∈ ((Q ⊔ Subgroup.zpowers p : Subgroup G) : Set G) := by rw [hsup p hpX hp]; exact hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q _ hpQ] at this
    obtain ⟨q, hq, y, hy, rfl⟩ := this
    exact ⟨q, hq, y, hy, rfl⟩
  have hQp : ∀ p : G, orderOf p = 3 → ∀ y ∈ Subgroup.zpowers p, y ∈ Q → y = 1 := by
    intro p hp y hy hyQ
    have h3 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers p) hy
      rwa [Nat.card_zpowers, hp] at this
    obtain ⟨k, hk⟩ := hQ2 ⟨y, hyQ⟩
    have h2 : orderOf y ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h2)
  have hQR : ∀ p ∈ X, orderOf p = 3 → Q ≤ ⁅Q, Subgroup.zpowers p⁆ := by
    intro p hpX hp
    set R : Subgroup G := ⁅Q, Subgroup.zpowers p⁆ with hRdef
    have hRU : R ≤ U := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hpX)
    have hRQ : R ≤ Q := hRU.trans hUQ
    set N : Subgroup G := R ⊔ Subgroup.zpowers p with hNdef
    have hNX : N ≤ X := sup_le (hRQ.trans hQX) (Subgroup.zpowers_le.mpr hpX)
    have hpRn : p ∈ Subgroup.normalizer (R : Set G) := by
      refine mem_normalizer_of_conj_mem fun r hr => ?_
      have hmap : R.map (MulAut.conj p).toMonoidHom ≤ R := by
        rw [hRdef, Subgroup.map_commutator]
        refine Subgroup.commutator_mono ?_ ?_
        · rintro _ ⟨q', hq', rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp (hXQ hpX) q').mp hq'
        · rintro _ ⟨z, hz, rfl⟩
          exact (Subgroup.zpowers p).mul_mem ((Subgroup.zpowers p).mul_mem
            (Subgroup.mem_zpowers p) hz) ((Subgroup.zpowers p).inv_mem (Subgroup.mem_zpowers p))
      exact hmap ⟨r, hr, rfl⟩
    have hpR : Subgroup.zpowers p ≤ Subgroup.normalizer (R : Set G) :=
      Subgroup.zpowers_le.mpr hpRn
    have hpN : p ∈ Subgroup.normalizer (N : Set G) :=
      le_normalizer_sup (C := Subgroup.zpowers p) hpR Subgroup.le_normalizer
        (Subgroup.mem_zpowers p)
    have hQN : Q ≤ Subgroup.normalizer (N : Set G) := by
      intro q hq
      refine mem_normalizer_of_conj_mem fun n hn => ?_
      have hmap : N.map (MulAut.conj q).toMonoidHom ≤ N := by
        rw [hNdef, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨r, hr, rfl⟩
          have hrq : q * r = r * q := Subgroup.mem_centralizer_iff.mp (hUC (hRU hr)) q hq
          show q * r * q⁻¹ ∈ N
          rw [hrq, mul_inv_cancel_right]
          exact Subgroup.mem_sup_left hr
        · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
          show q * p * q⁻¹ ∈ N
          have : q * p * q⁻¹ = ⁅q, p⁆ * p := by simp [commutatorElement_def, mul_assoc]
          rw [this]
          exact N.mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq
            (Subgroup.mem_zpowers p))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers p))
      exact hmap ⟨n, hn, rfl⟩
    have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
      rw [← hsup p hpX hp]
      exact sup_le hQN ((Subgroup.zpowers_le).mpr hpN)
    have hNn : (N.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
    have hquot : IsPGroup 2 (X ⧸ N.subgroupOf X) := by
      intro z
      induction z using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨q, hq, y, hy, hxqy⟩ := hmem p hpX hp x x.2
        obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
        refine ⟨k, ?_⟩
        have hqX : q ∈ X := hQX hq
        have hyX : y ∈ X := (Subgroup.zpowers_le.mpr hpX) hy
        have hx : x = ⟨q, hqX⟩ * ⟨y, hyX⟩ := Subtype.ext hxqy
        have hyN : ((⟨y, hyX⟩ : X) : X ⧸ N.subgroupOf X) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hy))
        rw [hx, QuotientGroup.mk_mul, hyN, mul_one, ← QuotientGroup.mk_pow]
        have : (⟨q, hqX⟩ : X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
        rw [this, QuotientGroup.mk_one]
    have htop := hshort1 (N.subgroupOf X) hquot
    intro q hq
    have hqN : q ∈ N := by
      have : (⟨q, hQX hq⟩ : X) ∈ N.subgroupOf X := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have : q ∈ ((R ⊔ Subgroup.zpowers p : Subgroup G) : Set G) := hqN
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hpR] at this
    obtain ⟨r, hr, y, hy, hry'⟩ := this
    have hry : r * y = q := hry'
    have hyQ : y ∈ Q := by
      have : y = r⁻¹ * q := by rw [← hry]; group
      rw [this]
      exact Q.mul_mem (Q.inv_mem (hRQ hr)) hq
    have hy1 := hQp p hp y hy hyQ
    rw [← hry, hy1, mul_one]
    exact hr
  have hp₀X : (p₀ : G) ∈ X := p₀.2
  have hp₀3 : orderOf (p₀ : G) = 3 := by rw [Subgroup.orderOf_coe, hp₀]
  have hQU : Q = U := le_antisymm
    ((hQR _ hp₀X hp₀3).trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hp₀X)))
    hUQ
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hUC (hQU ▸ hx)) y hy).symm
  have hQsq : ∀ q ∈ Q, q ^ 2 = 1 := fun q hq => hU2 q (show q ∈ U by rw [← hQU]; exact hq)
  have hfpf : ∀ p ∈ X, orderOf p = 3 → ∀ q ∈ Q, p * q = q * p → q = 1 := by
    intro p hpX hp w hwQ hw
    have hσ : ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp (hXQ hpX) q).mp hq
    let S : Subgroup G :=
      { carrier := {w | ∃ q ∈ Q, w = q * (p * q⁻¹ * p⁻¹)}
        mul_mem' := by
          rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
          refine ⟨q₁ * q₂, Q.mul_mem hq₁ hq₂, ?_⟩
          have h1 : p * q₁⁻¹ * p⁻¹ ∈ Q := hσ _ (Q.inv_mem hq₁)
          have h2 : p * q₂⁻¹ * p⁻¹ ∈ Q := hσ _ (Q.inv_mem hq₂)
          have hc := hQcomm _ h1 _ (Q.mul_mem hq₂ h2)
          calc q₁ * (p * q₁⁻¹ * p⁻¹) * (q₂ * (p * q₂⁻¹ * p⁻¹))
              = q₁ * ((p * q₁⁻¹ * p⁻¹) * (q₂ * (p * q₂⁻¹ * p⁻¹))) := by group
            _ = q₁ * ((q₂ * (p * q₂⁻¹ * p⁻¹)) * (p * q₁⁻¹ * p⁻¹)) := by rw [hc]
            _ = q₁ * q₂ * (p * (q₁ * q₂)⁻¹ * p⁻¹) := by group
        one_mem' := ⟨1, Q.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨q, hq, rfl⟩
          refine ⟨q⁻¹, Q.inv_mem hq, ?_⟩
          have hc := hQcomm _ (hσ q hq) _ (Q.inv_mem hq)
          calc (q * (p * q⁻¹ * p⁻¹))⁻¹ = (p * q * p⁻¹) * q⁻¹ := by group
            _ = q⁻¹ * (p * q * p⁻¹) := hc
            _ = q⁻¹ * (p * q⁻¹⁻¹ * p⁻¹) := by rw [inv_inv] }
    have hQS : Q ≤ S := by
      refine (hQR p hpX hp).trans (Subgroup.commutator_le.mpr fun q hq y hy => ?_)
      obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hy : y ∈ Submonoid.powers p)
      induction n with
      | zero => exact ⟨1, Q.one_mem, by simp⟩
      | succ n ih =>
        have hqn : p ^ n * q * (p ^ n)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hXQ (X.pow_mem hpX n)) q).mp hq
        have hS1 : p ^ n * q * (p ^ n)⁻¹ * (p * (p ^ n * q * (p ^ n)⁻¹)⁻¹ * p⁻¹) ∈ S :=
          ⟨_, hqn, rfl⟩
        have : ⁅q, p ^ (n + 1)⁆ =
            ⁅q, p ^ n⁆ * (p ^ n * q * (p ^ n)⁻¹ * (p * (p ^ n * q * (p ^ n)⁻¹)⁻¹ * p⁻¹)) := by
          rw [commutatorElement_def, commutatorElement_def, pow_succ]
          group
        rw [this]
        exact S.mul_mem (ih (Subgroup.npow_mem_zpowers p n)) hS1
    let ψ : Q → Q := fun q => ⟨q * (p * q⁻¹ * p⁻¹), Q.mul_mem q.2 (hσ _ (Q.inv_mem q.2))⟩
    have hψs : Function.Surjective ψ := by
      intro v
      obtain ⟨q, hq, hv⟩ := hQS v.2
      exact ⟨⟨q, hq⟩, Subtype.ext hv.symm⟩
    have hψi := Finite.injective_iff_surjective.mpr hψs
    have h1 : ψ ⟨w, hwQ⟩ = ψ 1 := by
      apply Subtype.ext
      change w * (p * w⁻¹ * p⁻¹) = 1 * (p * 1⁻¹ * p⁻¹)
      have : p * w⁻¹ * p⁻¹ = w⁻¹ := by
        have hw' : p * w⁻¹ = w⁻¹ * p := by
          calc p * w⁻¹ = (w * p⁻¹)⁻¹ := by group
            _ = (p⁻¹ * w)⁻¹ := by
              congr 1
              calc w * p⁻¹ = p⁻¹ * (p * w) * p⁻¹ := by group
                _ = p⁻¹ * (w * p) * p⁻¹ := by rw [hw]
                _ = p⁻¹ * w := by group
            _ = w⁻¹ * p := by group
        rw [hw', mul_inv_cancel_right]
      rw [this]
      group
    exact congrArg Subtype.val (hψi h1)
  have hZ1 : blockZ X = ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    have hwU : w ∈ U := hw.1
    have hwC : w ∈ Subgroup.centralizer (X : Set G) := hw.2
    exact hfpf _ hp₀X hp₀3 w (hQU ▸ hwU) (Subgroup.mem_centralizer_iff.mp hwC _ hp₀X)
  have hcardQ : Nat.card Q = 4 := by
    rw [hQU, hcardU, hZ1, Subgroup.card_bot, mul_one]
  exact ⟨hQX, hXQ, hcardQ, hQsq, by rw [hcardX, hcardQ], hcube, hfpf⟩

end Short

@[expose] def syl3 (X : Subgroup G) : Set (Subgroup G) := {P | P ≤ X ∧ Nat.card P = 3}

theorem cjSub_zpowers (g p : G) :
    cjSub g (Subgroup.zpowers p) = Subgroup.zpowers (g * p * g⁻¹) := by
  rw [cjSub, MonoidHom.map_zpowers]
  rfl

theorem mem_normalizer_of_cjSub_eq [Finite G] {g : G} {A : Subgroup G} (hA : cjSub g A = A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← hA, mem_cjSub]
  simpa [mul_assoc] using hx

namespace IsA4

variable {X Q : Subgroup G}

theorem isPGroup (h : IsA4 X Q) : IsPGroup 2 Q :=
  IsPGroup.of_card (n := 2) (by rw [h.card_Q]; norm_num)

theorem eq_one_of_mem_zpowers (h : IsA4 X Q) {p : G} (hp : orderOf p = 3) {y : G}
    (hy : y ∈ Subgroup.zpowers p) (hyQ : y ∈ Q) : y = 1 := by
  have h3 : orderOf y ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers p) hy
    rwa [Nat.card_zpowers, hp] at this
  have h2 : y ^ 2 = 1 := h.sq y hyQ
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 2) h3 (orderOf_dvd_of_pow_eq_one h2))

theorem eq_one_of_mem_of_card (h : IsA4 X Q) {P : Subgroup G} (hP : Nat.card P = 3) {y : G}
    (hy : y ∈ P) (hyQ : y ∈ Q) : y = 1 := by
  have h3 : orderOf y ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard P hy
    rwa [hP] at this
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 2) h3
    (orderOf_dvd_of_pow_eq_one (h.sq y hyQ)))

theorem sup_eq [Finite G] (h : IsA4 X Q) {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 3) :
    Q ⊔ P = X := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le h.le hPX) ?_
  rw [h.card]
  have h1 : 4 ∣ Nat.card ↥(Q ⊔ P) := h.card_Q ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : 3 ∣ Nat.card ↥(Q ⊔ P) := hP ▸ Subgroup.card_dvd_of_le le_sup_right
  exact Nat.le_of_dvd Nat.card_pos
    ((by norm_num : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd h2 h1)

theorem card_zpowers {p : G} (hp : orderOf p = 3) : Nat.card (Subgroup.zpowers p) = 3 := by
  rw [Nat.card_zpowers, hp]

theorem mem_mul [Finite G] (h : IsA4 X Q) {p : G} (hpX : p ∈ X) (hp : orderOf p = 3) {x : G}
    (hx : x ∈ X) :
    ∃ q ∈ Q, ∃ n : ℕ, x = q * p ^ n := by
  have hpQ : Subgroup.zpowers p ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.mpr hpX).trans h.normal
  have : x ∈ ((Q ⊔ Subgroup.zpowers p : Subgroup G) : Set G) := by
    rw [h.sup_eq (Subgroup.zpowers_le.mpr hpX) (card_zpowers hp)]
    exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q _ hpQ] at this
  obtain ⟨q, hq, y, hy, hxy⟩ := this
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hy : y ∈ Submonoid.powers p)
  exact ⟨q, hq, n, hxy.symm⟩

theorem conj_mem (h : IsA4 X Q) {x : G} (hx : x ∈ X) {q : G} (hq : q ∈ Q) : x * q * x⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (h.normal hx) q).mp hq

theorem exists_commutator [Finite G] (h : IsA4 X Q) {p : G} (hpX : p ∈ X) (hp : orderOf p = 3)
    {w : G} (hw : w ∈ Q) :
    ∃ q ∈ Q, w = q * (p * q⁻¹ * p⁻¹) := by
  let ψ : Q → Q := fun q => ⟨q * (p * q⁻¹ * p⁻¹), Q.mul_mem q.2 (h.conj_mem hpX (Q.inv_mem q.2))⟩
  have hψi : Function.Injective ψ := by
    intro a b hab
    have hab' : (a : G) * (p * (a : G)⁻¹ * p⁻¹) = b * (p * (b : G)⁻¹ * p⁻¹) :=
      congrArg Subtype.val hab
    have hcom : p * ((b : G)⁻¹ * a) = ((b : G)⁻¹ * a) * p := by
      have h1 : (b : G)⁻¹ * a = (p * (b : G)⁻¹ * p⁻¹) * (p * (a : G)⁻¹ * p⁻¹)⁻¹ := by
        have := hab'
        have hc : (b : G)⁻¹ * a * (p * (a : G)⁻¹ * p⁻¹) = (p * (b : G)⁻¹ * p⁻¹) := by
          calc (b : G)⁻¹ * a * (p * (a : G)⁻¹ * p⁻¹)
              = (b : G)⁻¹ * (a * (p * (a : G)⁻¹ * p⁻¹)) := by group
            _ = (b : G)⁻¹ * (b * (p * (b : G)⁻¹ * p⁻¹)) := by rw [hab']
            _ = p * (b : G)⁻¹ * p⁻¹ := by group
        rw [← hc]
        group
      have h2 : (p * (b : G)⁻¹ * p⁻¹) * (p * (a : G)⁻¹ * p⁻¹)⁻¹ = p * ((b : G)⁻¹ * a) * p⁻¹ := by
        group
      calc p * ((b : G)⁻¹ * a) = (p * ((b : G)⁻¹ * a) * p⁻¹) * p := by group
        _ = ((b : G)⁻¹ * a) * p := by rw [← h2, ← h1]
    have h1 := h.fpf p hpX hp _ (Q.mul_mem (Q.inv_mem b.2) a.2) hcom
    apply Subtype.ext
    calc (a : G) = b * ((b : G)⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hψi) ⟨w, hw⟩
  exact ⟨q, q.2, (congrArg Subtype.val hq).symm⟩

theorem exists_orderOf_eq_three [Finite G] (h : IsA4 X Q) : ∃ p ∈ X, orderOf p = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [h.card]; norm_num)
  exact ⟨p, p.2, by rw [Subgroup.orderOf_coe, hp]⟩

theorem mem_of_mem_normalizer [Finite G] (h : IsA4 X Q) {P : Subgroup G} (hPX : P ≤ X)
    (hP : Nat.card P = 3) {x : G} (hx : x ∈ X) (hxP : x ∈ Subgroup.normalizer (P : Set G)) :
    x ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨p, hpP⟩, hp⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hP])
  have hp3 : orderOf p = 3 := by rw [← hp, Subgroup.orderOf_mk]
  obtain ⟨q, hq, n, rfl⟩ := h.mem_mul (hPX hpP) hp3 hx
  have hpn : p ^ n ∈ P := P.pow_mem hpP n
  have hqN : q ∈ Subgroup.normalizer (P : Set G) := by
    have : q = (q * p ^ n) * (p ^ n)⁻¹ := by group
    rw [this]
    exact (Subgroup.normalizer (P : Set G)).mul_mem hxP
      ((Subgroup.normalizer (P : Set G)).inv_mem (Subgroup.le_normalizer hpn))
  have hcP : q * p * q⁻¹ * p⁻¹ ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hqN p).mp hpP) (P.inv_mem hpP)
  have hcQ : q * p * q⁻¹ * p⁻¹ ∈ Q := by
    have : q * p * q⁻¹ * p⁻¹ = q * (p * q⁻¹ * p⁻¹) := by group
    rw [this]
    exact Q.mul_mem hq (h.conj_mem (hPX hpP) (Q.inv_mem hq))
  have h1 := h.eq_one_of_mem_of_card hP hcP hcQ
  have hcom : p * q = q * p := by
    calc p * q = (q * p * q⁻¹ * p⁻¹)⁻¹ * (q * p) := by group
      _ = q * p := by rw [h1, inv_one, one_mul]
  rw [h.fpf p (hPX hpP) hp3 q hq hcom, one_mul]
  exact hpn

theorem eq_bot_or_eq [Finite G] (h : IsA4 X Q) {W : Subgroup G} (hWQ : W ≤ Q)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = Q := by
  classical
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
  obtain ⟨p, hpX, hp⟩ := h.exists_orderOf_eq_three
  have hpw : p * w * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hXW hpX) w).mp hwW
  have hne : p * w * p⁻¹ ≠ w := by
    intro heq
    apply hw1
    apply Subtype.ext
    refine h.fpf p hpX hp w (hWQ hwW) ?_
    calc p * w = p * w * p⁻¹ * p := by group
      _ = w * p := by rw [heq]
  have hne1 : p * w * p⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    apply Subtype.ext
    calc w = p⁻¹ * (p * w * p⁻¹) * p := by group
      _ = 1 := by rw [h1]; group
  have h3 : 3 ≤ Nat.card W := by
    have : Fintype W := Fintype.ofFinite W
    let s : Finset W := {1, ⟨w, hwW⟩, ⟨p * w * p⁻¹, hpw⟩}
    have hs : s.card = 3 := by
      simp only [s]
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro heq
        exact hne (congrArg Subtype.val heq).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun heq => hw1 heq.symm, fun heq => hne1 ?_⟩
        exact (congrArg Subtype.val heq).symm
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ s
  have hdvd : Nat.card W ∣ 4 := h.card_Q ▸ Subgroup.card_dvd_of_le hWQ
  have h4 : Nat.card W = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card W ∣ 2 ^ 2 from hdvd) with
      ⟨k, hk, hk'⟩
    interval_cases k <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hWQ (by rw [h4, h.card_Q])

theorem cjSub_mem_syl3 {P : Subgroup G} (hP : P ∈ syl3 X) (g : G) :
    cjSub g P ∈ syl3 (cjSub g X) :=
  ⟨cjSub_mono hP.1, by rw [card_cjSub]; exact hP.2⟩

theorem card_syl3 [Finite G] (h : IsA4 X Q) : Nat.card (syl3 X) = 4 := by
  obtain ⟨p, hpX, hp⟩ := h.exists_orderOf_eq_three
  set P₀ : Subgroup G := Subgroup.zpowers p with hP₀def
  have hP₀X : P₀ ≤ X := Subgroup.zpowers_le.mpr hpX
  have hfmem : ∀ q ∈ Q, cjSub q P₀ ∈ syl3 X := fun q hq =>
    ⟨cjSub_le (Subgroup.le_normalizer (h.le hq)) hP₀X, by rw [card_cjSub, card_zpowers hp]⟩
  let f : Q → syl3 X := fun q => ⟨cjSub q P₀, hfmem q q.2⟩
  have hfi : Function.Injective f := by
    intro a b hab
    have hab' : cjSub (a : G) P₀ = cjSub (b : G) P₀ := congrArg Subtype.val hab
    have hN : (b : G)⁻¹ * a ∈ Subgroup.normalizer (P₀ : Set G) := by
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 : (a : G) * x * (a : G)⁻¹ ∈ cjSub (b : G) P₀ := by
        rw [← hab', mem_cjSub]
        simpa [mul_assoc] using hx
      rw [mem_cjSub] at h1
      simpa [mul_assoc] using h1
    have hmem := h.mem_of_mem_normalizer hP₀X (card_zpowers hp)
      (X.mul_mem (X.inv_mem (h.le b.2)) (h.le a.2)) hN
    have h1 := h.eq_one_of_mem_zpowers hp hmem (Q.mul_mem (Q.inv_mem b.2) a.2)
    apply Subtype.ext
    calc (a : G) = b * ((b : G)⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  have hfs : Function.Surjective f := by
    rintro ⟨P, hPX, hP⟩
    have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPX.trans h.normal
    have hpmem : p ∈ ((Q ⊔ P : Subgroup G) : Set G) := by rw [h.sup_eq hPX hP]; exact hpX
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q P hPQ] at hpmem
    obtain ⟨u, hu, y, hy, huy'⟩ := hpmem
    have huy : u * y = p := huy'
    obtain ⟨q, hq, hqu⟩ := h.exists_commutator hpX hp (Q.inv_mem hu)
    refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
    show cjSub q P₀ = P
    have hqp : q * p * q⁻¹ = y := by
      calc q * p * q⁻¹ = q * (p * q⁻¹ * p⁻¹) * p := by group
        _ = u⁻¹ * p := by rw [← hqu]
        _ = y := by rw [← huy]; group
    rw [hP₀def, cjSub_zpowers, hqp]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_
    rw [hP, Nat.card_zpowers]
    have : orderOf y = 3 := by
      rw [← hqp]
      have := (MulAut.conj q).orderOf_eq p
      rw [MulAut.conj_apply] at this
      rw [this, hp]
    rw [this]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩), h.card_Q]

theorem eq_one_of_forall_mem_normalizer [Finite G] (h : IsA4 X Q) {x : G} (hx : x ∈ X)
    (hN : ∀ P ∈ syl3 X, x ∈ Subgroup.normalizer (P : Set G)) : x = 1 := by
  obtain ⟨p, hpX, hp⟩ := h.exists_orderOf_eq_three
  set P₀ : Subgroup G := Subgroup.zpowers p with hP₀def
  have hP₀X : P₀ ≤ X := Subgroup.zpowers_le.mpr hpX
  have hP₀ : P₀ ∈ syl3 X := ⟨hP₀X, card_zpowers hp⟩
  obtain ⟨q, hq, hq1, -⟩ := exists_ne_of_card_eq_four h.card_Q 1
  have hP₁ : cjSub q P₀ ∈ syl3 X :=
    ⟨cjSub_le (Subgroup.le_normalizer (h.le hq)) hP₀X, by rw [card_cjSub, card_zpowers hp]⟩
  have hx0 := h.mem_of_mem_normalizer hP₀X hP₀.2 hx (hN P₀ hP₀)
  have hx1 := h.mem_of_mem_normalizer hP₁.1 hP₁.2 hx (hN _ hP₁)
  by_contra hx1'
  have horder : ∀ P ∈ syl3 X, x ∈ P → Subgroup.zpowers x = P := by
    intro P hP hxP
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) ?_
    rw [hP.2, Nat.card_zpowers]
    have h3 : orderOf x ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard P hxP
      rwa [hP.2] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1'
    · rw [h1]
  have heq : cjSub q P₀ = P₀ := (horder _ hP₁ hx1).symm.trans (horder _ hP₀ hx0)
  have hqN := mem_normalizer_of_cjSub_eq heq
  exact hq1 (h.eq_one_of_mem_zpowers hp (h.mem_of_mem_normalizer hP₀X hP₀.2 (h.le hq) hqN) hq)

theorem le_of_forall_syl3_le [Finite G] (h : IsA4 X Q) {H : Subgroup G}
    (hH : ∀ P ∈ syl3 X, P ≤ H) : X ≤ H := by
  obtain ⟨p, hpX, hp⟩ := h.exists_orderOf_eq_three
  have hP₀X : Subgroup.zpowers p ≤ X := Subgroup.zpowers_le.mpr hpX
  have hpH : p ∈ H := hH _ ⟨hP₀X, card_zpowers hp⟩ (Subgroup.mem_zpowers p)
  have hconj : ∀ q ∈ Q, q * p * q⁻¹ ∈ H := by
    intro q hq
    have hmem : cjSub q (Subgroup.zpowers p) ∈ syl3 X :=
      ⟨cjSub_le (Subgroup.le_normalizer (h.le hq)) hP₀X, by rw [card_cjSub, card_zpowers hp]⟩
    apply hH _ hmem
    rw [cjSub_zpowers]
    exact Subgroup.mem_zpowers _
  have hQH : Q ≤ H := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := h.exists_commutator hpX hp hw
    have : q * (p * q⁻¹ * p⁻¹) = q * p * q⁻¹ * p⁻¹ := by group
    rw [this]
    exact H.mul_mem (hconj q hq) (H.inv_mem hpH)
  rw [← h.sup_eq hP₀X (card_zpowers hp)]
  exact sup_le hQH (Subgroup.zpowers_le.mpr hpH)

theorem cjSub' [Finite G] (h : IsA4 X Q) (g : G) : IsA4 (cjSub g X) (cjSub g Q) := by
  have hpow : ∀ (x : G) (n : ℕ), (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
    intro x n
    have := map_pow (MulAut.conj g⁻¹) x n
    simp only [MulAut.conj_apply, inv_inv] at this
    exact this.symm
  have hone : ∀ x : G, g⁻¹ * x * g = 1 → x = 1 := by
    intro x hx
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [hx]; group
  refine ⟨cjSub_mono h.le, ?_, by rw [card_cjSub, h.card_Q], ?_, by rw [card_cjSub, h.card], ?_, ?_⟩
  · intro y hy
    rw [mem_cjSub] at hy
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [mem_cjSub] at hw ⊢
    have hc := h.conj_mem hy hw
    have : g⁻¹ * (y * w * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * w * g) * (g⁻¹ * y * g)⁻¹ := by
      group
    rw [this]
    exact hc
  · intro q hq
    rw [mem_cjSub] at hq
    have := h.sq _ hq
    rw [hpow] at this
    exact hone _ this
  · intro x hx
    rw [mem_cjSub] at hx ⊢
    rw [← hpow]
    exact h.cube _ hx
  · intro p hp hp3 q hq hpq
    rw [mem_cjSub] at hp hq
    have hord : orderOf (g⁻¹ * p * g) = 3 := by
      have := (MulAut.conj g⁻¹).orderOf_eq p
      rw [MulAut.conj_apply, inv_inv] at this
      rw [this, hp3]
    have hcom : (g⁻¹ * p * g) * (g⁻¹ * q * g) = (g⁻¹ * q * g) * (g⁻¹ * p * g) := by
      calc (g⁻¹ * p * g) * (g⁻¹ * q * g) = g⁻¹ * (p * q) * g := by group
        _ = g⁻¹ * (q * p) * g := by rw [hpq]
        _ = (g⁻¹ * q * g) * (g⁻¹ * p * g) := by group
    exact hone _ (h.fpf _ hp hord _ hq hcom)

end IsA4

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
