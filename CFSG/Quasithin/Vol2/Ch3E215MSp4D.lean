module

public import CFSG.Quasithin.Vol2.Ch3E215MSp4C

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem P_le_X (h : E2.Pair X T M V g) : (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) ≤ X :=
  h.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)

theorem normal_Z (h : E2.Pair X T M V g) :
    ((V ⊓ B6.conjSub g V).subgroupOf ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))).Normal :=
  normal_subgroupOf h.inf_conj_le_P fun _ hz _ hp => conj_eq_of_mem_Z h (P_le_X h hp) hz

theorem commutator_mem_Z_of_kerIn (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hJ : IsPGroup 2 ↥(kerIn M X)) {r k : ℕ} (hk : 0 < k) (hr : IsPrimitivePrimeDivisor r k)
    {x : G} (hx : x ∈ X) (hxo : orderOf x = r)
    (hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤ 2 ^ k)
    {j : G} (hj : j ∈ kerIn M X) {p : G} (hp : p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) :
    j * p * j⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_Z h
  set P := (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ B6.conjSub g V with hZdef
  set Q := ↥P ⧸ Z.subgroupOf P
  have hJX : kerIn M X ≤ X := kerIn_le.trans h.le_X
  set act := actQ (L := X) h.le_normalizer_P h.le_normalizer_Z with hact
  let Y : Subgroup Q :=
    { carrier := {q | ∀ i : ↥(kerIn M X), act ⟨i, hJX i.2⟩ q = q}
      mul_mem' := fun {a b} ha hb i => by
        show act ⟨i, hJX i.2⟩ (a * b) = a * b
        rw [map_mul, ha i, hb i]
      one_mem' := fun i => map_one _
      inv_mem' := fun {a} ha i => by
        show act ⟨i, hJX i.2⟩ a⁻¹ = a⁻¹
        rw [map_inv, ha i] }
  have hJn : ∀ y ∈ X, ∀ i ∈ kerIn M X, y⁻¹ * i * y ∈ kerIn M X := fun y hy i hi => by
    have := (le_normalizer_kerIn M X (X.inv_mem hy) i).mp hi
    simpa using this
  have hYinv : ∀ y : ↥X, ∀ q ∈ Y, act y q ∈ Y := by
    intro y q hq i
    have hi' := hJn y y.2 i i.2
    have e : (⟨i, hJX i.2⟩ : ↥X) * y = y * ⟨(y : G)⁻¹ * i * y, hJX hi'⟩ := by
      apply Subtype.ext
      show (i : G) * y = y * ((y : G)⁻¹ * i * y)
      group
    show act ⟨i, hJX i.2⟩ (act y q) = act y q
    rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply]
    congr 1
    exact hq ⟨_, hi'⟩
  rcases eq_or_eq_of_le_normalizer h hchar hk hr hx hxo hPZ (le_comapQ h.inf_conj_le_P Y)
      (comapQ_le Y) (le_normalizer_comapQ h.le_normalizer_P h.le_normalizer_Z hYinv) with
    hN | hN
  · exfalso
    let _ : MulAction ↥(kerIn M X) Q :=
      MulAction.compHom Q (act.comp (Subgroup.inclusion hJX))
    have hcong := hJ.card_modEq_card_fixedPoints Q
    have hQ : Nat.card Q = 2 ^ k := relIndex_P_eq_two_pow h hchar hk hr hx hxo hPZ
    have hfix : MulAction.fixedPoints ↥(kerIn M X) Q = {1} := by
      ext q
      constructor
      · intro hq
        have hqY : q ∈ Y := fun i => hq i
        obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
        have h1 : (q' : G) ∈ comapQ Y := mem_comapQ.2 ⟨q'.2, hqY⟩
        rw [hN] at h1
        exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)
      · rintro rfl i
        show ((act.comp (Subgroup.inclusion hJX)) i) (1 : Q) = 1
        exact map_one _
    rw [hQ, hfix, Nat.card_unique] at hcong
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
    rw [hc] at hcong
    unfold Nat.ModEq at hcong
    omega
  · have hpN : p ∈ comapQ Y := by rw [hN]; exact hp
    obtain ⟨hp', hpY⟩ := mem_comapQ.1 hpN
    have h1 := hpY ⟨j, hj⟩
    rw [hact, actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have hw : ((j * p * j⁻¹)⁻¹ * p : G) ∈ Z := h1
    have hw' := Z.inv_mem hw
    have e : j * p * j⁻¹ * p⁻¹ = p * ((j * p * j⁻¹)⁻¹ * p)⁻¹ * p⁻¹ := by group
    rw [e, conj_eq_of_mem_Z h (P_le_X h hp) hw']
    exact hw'

end CFSG.Quasithin.Ch3E215M.Sp4
