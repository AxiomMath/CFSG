module

public import CFSG.Quasithin.Vol2.Ch10SecBInner3
public import CFSG.Quasithin.Vol2.Ch10SecCCard

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

theorem realizesVia_transport {V W : Type*} [CommGroup V] [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut V)} {H' : Subgroup (MulAut W)} {U Z : Subgroup V} {U' Z' : Subgroup W}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (ψ : ↥H ≃* ↥H') (e : ↥U ≃* ↥U')
    (heZ : ∀ u : ↥U, ((e u : ↥U') : W) ∈ Z' ↔ (u : V) ∈ Z) (hZU : Z' ≤ U')
    (hU : ∀ h' : ↥H', ∀ u ∈ U', (h' : MulAut W) u ∈ U')
    (hZ : ∀ h' : ↥H', ∀ z ∈ Z', (h' : MulAut W) z ∈ Z')
    (hc : ∀ (g : ↥H) (u : ↥U) (hu : (g : MulAut V) (u : V) ∈ U),
      ((ψ g : ↥H') : MulAut W) ((e u : ↥U') : W) = ((e ⟨_, hu⟩ : ↥U') : W)) :
    D.RealizesVia H' U' Z' (ψ.toMonoidHom.comp π) := by
  obtain ⟨hπs, -, hks, hUinv, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨ψ.surjective.comp hπs, hZU, hks, hU, hZ, hsec, hker, β.comp e.symm.toMonoidHom,
    hβs.comp e.symm.surjective, fun u' => ?_, fun γ u' m hu' hm hβm => ?_⟩
  · have h1 := hβk (e.symm u')
    rw [← heZ, MulEquiv.apply_symm_apply] at h1
    exact h1
  · have hu : ((π γ : ↥H) : MulAut V) ((e.symm u' : ↥U) : V) ∈ U := hUinv (π γ) _ (e.symm u').2
    have h1 := hc (π γ) (e.symm u') hu
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (⟨((ψ.toMonoidHom.comp π γ : ↥H') : MulAut W) (u' : W), hu'⟩ : ↥U') =
        e ⟨_, hu⟩ := Subtype.ext h1
    have hβm' : β (e.symm u') = QuotientGroup.mk m := hβm
    change β (e.symm ⟨_, hu'⟩) = _
    rw [h2, MulEquiv.symm_apply_apply]
    exact hβe γ (e.symm u') m hu hm hβm'

variable {G : Type} [Group G]

theorem le_normalizer_of_conj_mem {L Y : Subgroup G}
    (h : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) : L ≤ Subgroup.normalizer (Y : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h l hl y hy, fun hy => ?_⟩
  have h1 := h l⁻¹ (L.inv_mem hl) _ hy
  have e : l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem exists_autOnEquiv {L Y W : Subgroup G} (hY : L ≤ Subgroup.normalizer (Y : Set G))
    (hW : L ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ l ∈ L, l ∈ Subgroup.centralizer (Y : Set G) ↔ l ∈ Subgroup.centralizer (W : Set G)) :
    ∃ ψ : ↥(autOn L Y) ≃* ↥(autOn L W), ∀ (l : G) (hl : l ∈ L),
      ψ ⟨conjAct Y ⟨l, hY hl⟩, SecB.mem_autOn_iff.mpr ⟨⟨l, hY hl⟩, hl, rfl⟩⟩ =
        ⟨conjAct W ⟨l, hW hl⟩, SecB.mem_autOn_iff.mpr ⟨⟨l, hW hl⟩, hl, rfl⟩⟩ := by
  let fY : ↥L →* ↥(autOn L Y) :=
    ((conjAct Y).comp (Subgroup.inclusion hY)).codRestrict (autOn L Y) fun l =>
      SecB.mem_autOn_iff.mpr ⟨⟨l, hY l.2⟩, l.2, rfl⟩
  let fW : ↥L →* ↥(autOn L W) :=
    ((conjAct W).comp (Subgroup.inclusion hW)).codRestrict (autOn L W) fun l =>
      SecB.mem_autOn_iff.mpr ⟨⟨l, hW l.2⟩, l.2, rfl⟩
  have hsY : Function.Surjective fY := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp ha
    exact ⟨⟨x, hxL⟩, rfl⟩
  have hsW : Function.Surjective fW := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp ha
    exact ⟨⟨x, hxL⟩, rfl⟩
  have hk : fY.ker = fW.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj, ← Subtype.coe_inj]
    change conjAct Y ⟨l, hY l.2⟩ = 1 ↔ conjAct W ⟨l, hW l.2⟩ = 1
    rw [A4.conjAct_eq_one_iff, A4.conjAct_eq_one_iff]
    exact h l l.2
  refine ⟨((QuotientGroup.quotientKerEquivOfSurjective _ hsY).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsW), fun l hl => ?_⟩
  have e1 : (QuotientGroup.quotientKerEquivOfSurjective _ hsY).symm
      ⟨conjAct Y ⟨l, hY hl⟩, SecB.mem_autOn_iff.mpr ⟨⟨l, hY hl⟩, hl, rfl⟩⟩ =
      QuotientGroup.mk ⟨l, hl⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1]
  rfl

theorem le_normalizer_of_comm {X A B : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hA : A ≤ X) (hB : B ≤ X) : B ≤ Subgroup.normalizer (A : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hX a (hA ha) b (hB hb)

theorem zpow_eq_one_or_self {z : G} (hz2 : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_sup_zpowers {W : Subgroup G} {z y : G}
    (hN : Subgroup.zpowers z ≤ Subgroup.normalizer (W : Set G)) (hz2 : z ^ 2 = 1)
    (hy : y ∈ W ⊔ Subgroup.zpowers z) : ∃ v ∈ W, y = v ∨ y = v * z := by
  have hy' : y ∈ (↑(W ⊔ Subgroup.zpowers z) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hy'
  obtain ⟨v, hv, w, hw, hvw⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨v, hv, ?_⟩
  have hvw' : v * z ^ k = y := hvw
  rw [← hvw']
  rcases zpow_eq_one_or_self hz2 k with h | h
  · left
    rw [h, mul_one]
  · right
    rw [h]

theorem card_sup_zpowers [Finite G] {W : Subgroup G} {z : G} (hzW : z ∉ W) (hz2 : z ^ 2 = 1)
    (hN : Subgroup.zpowers z ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥(W ⊔ Subgroup.zpowers z) = 2 * Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := fun h => hzW (h ▸ W.one_mem)
  have e := card_sup_mul_card_inf (H := W) (K := Subgroup.zpowers z) hN
  have hbot : W ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    rcases zpow_eq_one_or_self hz2 k with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ hxW) hzW
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hz2 hz1] at e
  rw [e, mul_comm]

end CFSG.Quasithin.Vol2.Ch10.SecC
