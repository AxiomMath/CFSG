module

public import CFSG.Quasithin.Vol2.Ch11SecBK6A
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT
public import CFSG.Quasithin.Vol2.Ch11SecBK2A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commutatorElement_eq {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (w : ↥V) :
    ⁅(w : G), a⁆ = ((w * (SecA.conjV V a ha w)⁻¹ : ↥V) : G) := by
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe]
  group

theorem r2_of_param (hfl : Flag24 L V X T V₁ V₂ n) [IsMulCommutative ↥V]
    {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M] (hK : Nat.card K = 2 ^ n)
    {f : ↥V → M} (hfdiv : ∀ a b, f (a * b⁻¹) = f a - f b)
    (hfeq : ∀ a b, f a = f b → a * b⁻¹ ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V)
    (hfsurj : Function.Surjective f) {v₀ v₁ : M}
    (hind : ∀ s t : K, s • v₀ + t • v₁ = 0 → s = 0 ∧ t = 0)
    (hV₁ : ∀ w : ↥V, (w : G) ∈ V₁ ↔ ∃ s : K, f w = s • v₀)
    (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ ∃ s t : K, f w = s • v₀ + t • v₁)
    (hact : ∀ p ∈ autOn (T ⊓ L) V, ∃ φ : K, ∀ (w : ↥V) (s t : K), f w = s • v₀ + t • v₁ →
      f (p w) = (s + φ * t) • v₀ + t • v₁)
    (hR₂ : ∀ p ∈ autOn (T ⊓ L) V, (∀ w : ↥V, (w : G) ∈ V₂ → f (p w) = f w) →
      p ∈ pCoreOf 2 (perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V))))
    (hO2 : ∀ s ∈ pCoreOf 2 (perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V))),
      ∀ u ∈ V₂.subgroupOf V, s u = u)
    {A : Subgroup G} (hAT : A ≤ T) (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X))
    (hAR : ¬ A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    ⁅V₂, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁ ∧
      E3.mQuot A (A ⊓ Subgroup.centralizer (V₂ : Set G)) = n ∧
      E3.mQuot V₂ (V₂ ⊓ Subgroup.centralizer (A : Set G)) = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₂V := hfl.le₂
  have hV₁V : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hfl.T_le_V
  have hAP : autOn A V ≤ autOn (T ⊓ L) V := autOn_le_sylow hfl hAT (autOn_le_of_aSet hfl hA)
  have hcP : ∀ a (ha : a ∈ A), SecA.conjV V a (hAV ha) ∈ autOn (T ⊓ L) V :=
    fun a ha => hAP (SecA.conjV_mem_autOn ha (hAV ha))
  have huniq : ∀ s t s' t' : K, s • v₀ + t • v₁ = s' • v₀ + t' • v₁ → s = s' ∧ t = t' := by
    intro s t s' t' h
    have h' : (s - s') • v₀ + (t - t') • v₁ = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, h, sub_self]
    exact ⟨sub_eq_zero.mp (hind _ _ h').1, sub_eq_zero.mp (hind _ _ h').2⟩
  obtain ⟨w₁, hw₁⟩ := hfsurj v₁
  have hw₁' : f w₁ = (0 : K) • v₀ + (1 : K) • v₁ := by rw [hw₁, zero_smul, one_smul, zero_add]
  have hw₁V₂ : (w₁ : G) ∈ V₂ := (hV₂ w₁).mpr ⟨0, 1, hw₁'⟩
  have hφ : ∀ a (ha : a ∈ A), ∃ φ : K, ∀ (w : ↥V) (s t : K), f w = s • v₀ + t • v₁ →
      f (SecA.conjV V a (hAV ha) w) = (s + φ * t) • v₀ + t • v₁ := fun a ha => hact _ (hcP a ha)
  have hφw₁ : ∀ a (ha : a ∈ A) (φ : K), (∀ (w : ↥V) (s t : K), f w = s • v₀ + t • v₁ →
      f (SecA.conjV V a (hAV ha) w) = (s + φ * t) • v₀ + t • v₁) →
      (f (SecA.conjV V a (hAV ha) w₁) = f w₁ ↔ φ = 0) := by
    intro a ha φ hφa
    rw [hφa w₁ 0 1 hw₁', hw₁']
    constructor
    · intro h
      simpa using (huniq _ _ _ _ h).1
    · intro h
      rw [h, zero_mul, zero_add]
  have hzero : ∀ a (ha : a ∈ A), f (SecA.conjV V a (hAV ha) w₁) = f w₁ →
      ∀ w : ↥V, (w : G) ∈ V₂ → f (SecA.conjV V a (hAV ha) w) = f w := by
    intro a ha h w hw
    obtain ⟨φ, hφa⟩ := hφ a ha
    have hφ0 := (hφw₁ a ha φ hφa).mp h
    obtain ⟨s, t, hst⟩ := (hV₂ w).mp hw
    rw [hφa w s t hst, hφ0, zero_mul, add_zero, hst]
  have hcent : ∀ a (ha : a ∈ A), f (SecA.conjV V a (hAV ha) w₁) = f w₁ →
      a ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro a ha h
    have hp := hR₂ _ (hcP a ha) (hzero a ha h)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h3 := congrArg Subtype.val (hO2 _ hp ⟨v, hV₂V hv⟩ hv)
    rw [SecA.conjV_apply_coe] at h3
    change a * v * a⁻¹ = v at h3
    calc v * a = a * v * a⁻¹ * a := by rw [h3]
      _ = a * v := by group
  obtain ⟨a₀, ha₀, hne⟩ : ∃ a₀, ∃ ha₀ : a₀ ∈ A,
      f (SecA.conjV V a₀ (hAV ha₀) w₁) ≠ f w₁ := by
    by_contra hcon
    push Not at hcon
    exact hAR fun a ha => mem_r2_of_conjV hfl (le_sup_right (α := Subgroup G) (hAT ha)) (hAV ha)
      (hR₂ _ (hcP a ha) (hzero a ha (hcon a ha)))
  obtain ⟨φ₀, hφ₀⟩ := hφ a₀ ha₀
  have hφ₀ne : φ₀ ≠ 0 := fun h0 => hne ((hφw₁ a₀ ha₀ φ₀ hφ₀).mpr h0)
  have hcomm_le : ⁅V₂, A⁆ ≤ V₁ := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    obtain ⟨φ, hφa⟩ := hφ a ha
    obtain ⟨s, t, hst⟩ := (hV₂ ⟨v, hV₂V hv⟩).mp hv
    have e := commutatorElement_eq (hAV ha) ⟨v, hV₂V hv⟩
    change ⁅v, a⁆ = _ at e
    rw [e, hV₁]
    refine ⟨-(φ * t), ?_⟩
    rw [hfdiv, hφa _ s t hst, hst, add_smul, neg_smul]
    abel
  have hle_sup : V₁ ≤ ⁅V₂, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := by
    intro v hv
    obtain ⟨c, hc⟩ := (hV₁ ⟨v, hV₁V hv⟩).mp hv
    obtain ⟨u, hu⟩ := hfsurj ((-(c / φ₀)) • v₁)
    have hu' : f u = (0 : K) • v₀ + (-(c / φ₀)) • v₁ := by rw [hu, zero_smul, zero_add]
    have huV₂ : (u : G) ∈ V₂ := (hV₂ u).mpr ⟨0, _, hu'⟩
    set c₀ : ↥V := u * (SecA.conjV V a₀ (hAV ha₀) u)⁻¹ with hc₀
    have ht : φ₀ * -(c / φ₀) = -c := by field_simp
    have hfc : f ⟨v, hV₁V hv⟩ = f c₀ := by
      rw [hc₀, hfdiv, hφ₀ u 0 _ hu', hu', hc, zero_add, ht]
      module
    have hz := hfeq _ _ hfc
    have hvG : v = ((⟨v, hV₁V hv⟩ * c₀⁻¹ : ↥V) : G) * (c₀ : G) := by
      rw [← Subgroup.coe_mul, inv_mul_cancel_right]
    rw [hvG, sup_comm]
    refine Subgroup.mul_mem_sup ⟨Subtype.prop _, hz⟩ ?_
    rw [hc₀, ← commutatorElement_eq (hAV ha₀) u]
    exact Subgroup.commutator_mem_commutator huV₂ ha₀
  have hcentV₁ : ∀ a ∈ A, ∀ v ∈ V₁, a * v * a⁻¹ = v := by
    intro a ha v hv
    obtain ⟨t, ht, htV, hteq⟩ := SecA.mem_autOn_iff.mp (hcP a ha)
    have hFOC := factFlagOneCentral_holds G L V T V₁ n hfl.elem hfl.two_le hfl.le_normalizer
      hfl.commutator_eq hfl.nat hfl.sylow hfl.T_le_V hfl.T_le_L hfl.cV_le hV₁V hfl.stable₁
      hfl.index₁ hfl.T_le_V₁
    have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hV₁V hv⟩ : ↥V) : G)) hteq
    simp only [SecA.conjV_apply_coe] at h1
    rw [h1]
    have h2 := Subgroup.mem_centralizer_iff.mp (hFOC ht) v hv
    rw [← h2, mul_inv_cancel_right]
  have hCA : V₂ ⊓ Subgroup.centralizer (A : Set G) = V₁ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hv₂, hvA⟩ := Subgroup.mem_inf.mp hv
      obtain ⟨s, t, hst⟩ := (hV₂ ⟨v, hV₂V hv₂⟩).mp hv₂
      have hfix : SecA.conjV V a₀ (hAV ha₀) ⟨v, hV₂V hv₂⟩ = ⟨v, hV₂V hv₂⟩ := by
        apply Subtype.ext
        rw [SecA.conjV_apply_coe]
        change a₀ * v * a₀⁻¹ = v
        rw [Subgroup.mem_centralizer_iff.mp hvA a₀ ha₀, mul_inv_cancel_right]
      have h1 := hφ₀ _ s t hst
      rw [hfix, hst] at h1
      have h2 := (huniq _ _ _ _ h1).1
      have ht0 : t = 0 := by
        have h3 : φ₀ * t = 0 := by linear_combination -h2
        exact (mul_eq_zero.mp h3).resolve_left hφ₀ne
      exact (hV₁ ⟨v, hV₂V hv₂⟩).mpr ⟨s, by rw [hst, ht0, zero_smul, add_zero]⟩
    · intro v hv
      refine Subgroup.mem_inf.mpr ⟨hfl.le₁₂ hv, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      calc a * v = a * v * a⁻¹ * a := by group
        _ = v * a := by rw [hcentV₁ a ha v hv]
  have hidx₁₂ : V₁.relIndex V₂ = 2 ^ n := by
    have h := Subgroup.relIndex_mul_relIndex (V ⊓ Subgroup.centralizer (L : Set G)) V₁ V₂
      hfl.cV_le hfl.le₁₂
    rw [hfl.index₁, hfl.index₂, mul_two, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨le_antisymm (sup_le hcomm_le hfl.cV_le) hle_sup, ?_, ?_⟩
  swap
  · unfold E3.mQuot
    rw [hCA, hidx₁₂, padicValNat.prime_pow]
  choose φ hφs using fun a : ↥A => hφ a a.2
  have hφmul : ∀ a b : ↥A, φ (a * b) = φ a + φ b := by
    intro a b
    have e1 := hφs (a * b) w₁ 0 1 hw₁'
    have hconj : SecA.conjV V ((a * b : ↥A) : G) (hAV (a * b).2) =
        SecA.conjV V a (hAV a.2) * SecA.conjV V b (hAV b.2) :=
      SecA.conjV_mul V (hAV a.2) (hAV b.2)
    have e2 := hφs b w₁ 0 1 hw₁'
    rw [zero_add, mul_one] at e2
    have e3 := hφs a (SecA.conjV V b (hAV b.2) w₁) (φ b) 1 e2
    rw [hconj, MulAut.mul_apply, e3] at e1
    have := (huniq _ _ _ _ e1).1
    linear_combination -this
  let Φ : ↥A →* Multiplicative K :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (φ a)) fun a b => by rw [hφmul]; rfl
  have hker : Φ.ker = (A ⊓ Subgroup.centralizer (V₂ : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (φ a) = Multiplicative.ofAdd 0 ↔ _
    rw [Multiplicative.ofAdd.apply_eq_iff_eq]
    constructor
    · intro h0
      exact ⟨a.2, hcent a a.2 ((hφw₁ a a.2 (φ a) (hφs a)).mpr h0)⟩
    · intro h
      refine (hφw₁ a a.2 (φ a) (hφs a)).mp (congrArg f (Subtype.ext ?_))
      rw [SecA.conjV_apply_coe]
      rw [← Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 _ hw₁V₂,
        mul_inv_cancel_right]
  have hup : (A ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex A ≤ 2 ^ n := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans (le_of_eq hK)
  have hne0 : (A ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex A ≠ 0 :=
    E3.relIndex_ne_zero' A _
  apply le_antisymm
  · unfold E3.mQuot
    have h1 : 2 ^ padicValNat 2 ((A ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex A) ≤ 2 ^ n :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) pow_padicValNat_dvd).trans hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  · by_contra hlt
    push Not at hlt
    have hA' : autOn A V ∈ E3.aSet n (autOn X V) := hA
    have hDA : A ⊓ Subgroup.centralizer (V₂ : Set G) ≤ A := inf_le_left
    have hdvd := Ch11.SecS.relIndex_autOn_dvd hDA hAV
    have hmq : E3.mQuot (autOn A V) (autOn (A ⊓ Subgroup.centralizer (V₂ : Set G)) V) < n := by
      refine lt_of_le_of_lt ?_ hlt
      unfold E3.mQuot
      rw [← padicValNat_dvd_iff_le hne0]
      exact pow_padicValNat_dvd.trans hdvd
    have hfixeq := hA'.2.2.2 _ (autOn_mono hDA) hmq
    have hw₁B' : ∀ b ∈ autOn (A ⊓ Subgroup.centralizer (V₂ : Set G)) V, b w₁ = w₁ := by
      intro b hb
      obtain ⟨d, hd, hdV, rfl⟩ := SecA.mem_autOn_iff.mp hb
      apply Subtype.ext
      rw [SecA.conjV_apply_coe,
        ← Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 _ hw₁V₂,
        mul_inv_cancel_right]
    have hw₁B : w₁ ∈ fixV (autOn (A ⊓ Subgroup.centralizer (V₂ : Set G)) V) := hw₁B'
    rw [hfixeq] at hw₁B
    have hw₁A : ∀ b ∈ autOn A V, b w₁ = w₁ := hw₁B
    exact hne (congrArg f (hw₁A _ (SecA.conjV_mem_autOn ha₀ (hAV ha₀))))

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
