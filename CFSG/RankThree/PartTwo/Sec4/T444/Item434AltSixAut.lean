module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

open Equiv Equiv.Perm Subgroup
open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix (xPermutation
  yPermutation generating_pair)

@[expose] def F06 : Subgroup (alternatingGroup (Fin 6)) :=
  (F0 6).comap (alternatingGroup (Fin 6)).subtype

theorem mem_F06 {x : alternatingGroup (Fin 6)} :
    x ∈ F06 ↔ ∃ w, vecPerm2 6 w = (x : Perm (Fin 6)) := by
  rw [F06, Subgroup.mem_comap, Subgroup.coe_subtype, F0_eq_range f0Facts_six]
  exact ⟨fun ⟨v, hv⟩ => ⟨_, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem sign_vecPerm2_six : ∀ w : Fin 2 → ZMod 3, sign (vecPerm2 6 w) = 1 := by
  decide +kernel

theorem F0_six_le_alternatingGroup : F0 6 ≤ alternatingGroup (Fin 6) := by
  rw [F0_eq_range f0Facts_six]
  rintro _ ⟨v, rfl⟩
  exact mem_alternatingGroup.mpr (sign_vecPerm2_six _)

theorem card_F06 : Nat.card F06 = 9 := by
  rw [← card_F0 f0Facts_six]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe F0_six_le_alternatingGroup).toEquiv

theorem isElemAbelian_F06 : CFSG.Assembly.IsElemAbelian 3 F06 := by
  have hab := isElemAbelian_F0 f0Facts_six
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact congrArg (fun z : F0 6 => (z : Perm (Fin 6))) (hab.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  · exact hab.2 _ hx

@[expose] def k1Perm : Perm (Fin 6) := swap 0 1 * swap 3 4

@[expose] def k2Perm : Perm (Fin 6) := swap 0 3 * swap 3 1 * swap 1 4 * swap 2 5

@[expose] def k3Perm : Perm (Fin 6) := swap 0 4 * swap 4 1 * swap 1 3 * swap 2 5

@[expose] def mPerm : Perm (Fin 6) := swap 3 5 * swap 5 4

theorem centralizer_vecPerm2_six : ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∀ g : Perm (Fin 6),
    sign g = 1 → g * vecPerm2 6 v = vecPerm2 6 v * g → ∃ w, vecPerm2 6 w = g := by
  decide +kernel

theorem normalizes_F06 : ∀ u ∈ [k1Perm, k2Perm, yPermutation * k1Perm * yPermutation⁻¹,
    yPermutation * k2Perm * yPermutation⁻¹, mPerm],
    (∃ w, vecPerm2 6 w = u * c1 6 * u⁻¹) ∧ ∃ w, vecPerm2 6 w = u * c2 6 * u⁻¹ := by
  decide +kernel

theorem centralizer_k1_k2 : ∀ g : Perm (Fin 6), sign g = 1 → g * k1Perm = k1Perm * g →
    g * k2Perm = k2Perm * g → g = 1 ∨ g = k1Perm ∨ g = k2Perm ∨ g = k3Perm := by
  decide +kernel

theorem orders_six : (yPermutation * mPerm) ^ 3 = 1 ∧ (yPermutation * k1Perm * mPerm) ^ 3 ≠ 1 ∧
    yPermutation ^ 5 = 1 ∧ (yPermutation * k2Perm) ^ 5 ≠ 1 ∧ (yPermutation * k3Perm) ^ 5 ≠ 1 := by
  decide +kernel

theorem signs_six : sign k1Perm = 1 ∧ sign k2Perm = 1 ∧ sign k3Perm = 1 ∧ sign mPerm = 1 ∧
    sign yPermutation = 1 ∧ c1 6 = xPermutation := by
  decide +kernel

@[expose] def alt6 (σ : Perm (Fin 6)) (h : sign σ = 1) : alternatingGroup (Fin 6) :=
  ⟨σ, mem_alternatingGroup.mpr h⟩

theorem centralizer_le_F06 {f : alternatingGroup (Fin 6)} (hf : f ∈ F06) (hf1 : f ≠ 1) :
    Subgroup.centralizer {f} ≤ F06 := by
  obtain ⟨v, hv⟩ := mem_F06.mp hf
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hf1
    apply Subtype.ext
    rw [← hv]
    simp [vecPerm2]
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg
  have hg' : (g : Perm (Fin 6)) * vecPerm2 6 v = vecPerm2 6 v * g := by
    rw [hv]
    exact congrArg Subtype.val hg
  obtain ⟨w, hw⟩ := centralizer_vecPerm2_six v hv0 g (mem_alternatingGroup.mp g.2) hg'
  exact mem_F06.mpr ⟨w, hw⟩

variable {r : MulAut (alternatingGroup (Fin 6))}

theorem c1_mem_F06 (h : sign (c1 6) = 1) : alt6 (c1 6) h ∈ F06 :=
  mem_F06.mpr ⟨![1, 0], (f0Facts_six).e1⟩

theorem fix_of_normalizes (hr : ∀ f ∈ F06, r f = f) (h3 : Nat.Coprime (orderOf r) 3)
    {u : alternatingGroup (Fin 6)}
    (h1 : ∃ w, vecPerm2 6 w = (u : Perm (Fin 6)) * c1 6 * (u : Perm (Fin 6))⁻¹)
    (h2 : ∃ w, vecPerm2 6 w = (u : Perm (Fin 6)) * c2 6 * (u : Perm (Fin 6))⁻¹) : r u = u := by
  have hc1 : sign (c1 6) = 1 := by decide +kernel
  have hc2 : sign (c2 6) = 1 := by decide +kernel
  set a := alt6 (c1 6) hc1
  set b := alt6 (c2 6) hc2
  have ha : a ∈ F06 := mem_F06.mpr ⟨![1, 0], f0Facts_six.e1⟩
  have hb : b ∈ F06 := mem_F06.mpr ⟨![0, 1], f0Facts_six.e2⟩
  have hua : u * a * u⁻¹ ∈ F06 := mem_F06.mpr h1
  have hub : u * b * u⁻¹ ∈ F06 := mem_F06.mpr h2
  set f₀ := u⁻¹ * r u with hf₀
  have hcomm : ∀ c ∈ F06, u * c * u⁻¹ ∈ F06 → f₀ * c = c * f₀ := by
    intro c hc hcu
    have e1 := hr _ hcu
    rw [map_mul, map_mul, map_inv, hr c hc] at e1
    rw [hf₀]
    calc u⁻¹ * r u * c = u⁻¹ * (r u * c * (r u)⁻¹) * r u := by group
      _ = u⁻¹ * (u * c * u⁻¹) * r u := by rw [e1]
      _ = c * (u⁻¹ * r u) := by group
  have hc1ne : c1 6 ≠ 1 := by decide +kernel
  have hf₀F : f₀ ∈ F06 := by
    refine centralizer_le_F06 ha ?_ (mem_centralizer_singleton_iff.mpr (hcomm a ha hua))
    intro h
    exact hc1ne (congrArg Subtype.val h)
  have hrf : r f₀ = f₀ := hr f₀ hf₀F
  have huf : u * f₀ = r u := by rw [hf₀, mul_inv_cancel_left]
  have hpow : ∀ k : ℕ, (r ^ k) u = u * f₀ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hrf, pow_succ', ← mul_assoc, huf]
  have hk := hpow (orderOf r)
  rw [pow_orderOf_eq_one, MulAut.one_apply, left_eq_mul] at hk
  have hf3 : f₀ ^ 3 = 1 := isElemAbelian_F06.2 f₀ hf₀F
  have hd : orderOf f₀ ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one h3]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hf3)
  have hf1 : f₀ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hf₀] at hf1
  exact (inv_mul_eq_one.mp hf1).symm

theorem eq_one_of_fix_F06 (hr : ∀ f ∈ F06, r f = f) (h3 : Nat.Coprime (orderOf r) 3) :
    r = 1 := by
  obtain ⟨hk1, hk2, hk3, hm, hy, hx⟩ := signs_six
  set y := alt6 yPermutation hy
  set k₁ := alt6 k1Perm hk1
  set k₂ := alt6 k2Perm hk2
  set m := alt6 mPerm hm
  have hN := normalizes_F06
  have hfix : ∀ u : alternatingGroup (Fin 6), (u : Perm (Fin 6)) ∈ [k1Perm, k2Perm,
      yPermutation * k1Perm * yPermutation⁻¹, yPermutation * k2Perm * yPermutation⁻¹, mPerm] →
      r u = u := fun u hu => fix_of_normalizes hr h3 (hN _ hu).1 (hN _ hu).2
  have hrk₁ : r k₁ = k₁ := hfix k₁ (by simp [k₁, alt6])
  have hrk₂ : r k₂ = k₂ := hfix k₂ (by simp [k₂, alt6])
  have hrm : r m = m := hfix m (by simp [m, alt6])
  have hryk₁ : r (y * k₁ * y⁻¹) = y * k₁ * y⁻¹ := hfix _ (by simp [y, k₁, alt6])
  have hryk₂ : r (y * k₂ * y⁻¹) = y * k₂ * y⁻¹ := hfix _ (by simp [y, k₂, alt6])
  set t₀ := y⁻¹ * r y with ht₀
  have hct : ∀ k : alternatingGroup (Fin 6), r k = k → r (y * k * y⁻¹) = y * k * y⁻¹ →
      t₀ * k = k * t₀ := by
    intro k hk hyk
    rw [map_mul, map_mul, map_inv, hk] at hyk
    rw [ht₀]
    calc y⁻¹ * r y * k = y⁻¹ * (r y * k * (r y)⁻¹) * r y := by group
      _ = y⁻¹ * (y * k * y⁻¹) * r y := by rw [hyk]
      _ = k * (y⁻¹ * r y) := by group
  have h1 := congrArg Subtype.val (hct k₁ hrk₁ hryk₁)
  have h2 := congrArg Subtype.val (hct k₂ hrk₂ hryk₂)
  have hcases := centralizer_k1_k2 t₀ (mem_alternatingGroup.mp t₀.2) h1 h2
  have hry : r y = y * t₀ := by rw [ht₀, mul_inv_cancel_left]
  obtain ⟨hord1, hord2, hord3, hord4, hord5⟩ := orders_six
  have hty : t₀ = 1 := by
    rcases hcases with h | h | h | h
    · exact Subtype.ext h
    · exfalso
      have e : (y * m) ^ 3 = 1 := Subtype.ext hord1
      have e' := congrArg r e
      rw [map_pow, map_mul, hry, hrm, map_one] at e'
      apply hord2
      have := congrArg Subtype.val e'
      simpa [y, m, alt6, h] using this
    · exfalso
      have e : y ^ 5 = 1 := Subtype.ext hord3
      have e' := congrArg r e
      rw [map_pow, hry, map_one] at e'
      apply hord4
      have := congrArg Subtype.val e'
      simpa [y, alt6, h] using this
    · exfalso
      have e : y ^ 5 = 1 := Subtype.ext hord3
      have e' := congrArg r e
      rw [map_pow, hry, map_one] at e'
      apply hord5
      have := congrArg Subtype.val e'
      simpa [y, alt6, h] using this
  have hry' : r y = y := by rw [hry, hty, mul_one]
  have hrx : r DegreeSix.x = DegreeSix.x :=
    hr _ (mem_F06.mpr ⟨![1, 0], f0Facts_six.e1.trans hx⟩)
  have hry0 : r DegreeSix.y = DegreeSix.y := hry'
  have hle : Subgroup.closure ({DegreeSix.x, DegreeSix.y} : Set (alternatingGroup (Fin 6))) ≤
      r.toMonoidHom.eqLocus (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hrx
    · exact hry0
  rw [generating_pair] at hle
  exact MulEquiv.ext fun z => hle (Subgroup.mem_top z)

theorem eq_bot_of_F06_le_normalizer {X : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (hX : ¬ 3 ∣ Nat.card X)
    (hN : F06.map MulAut.conj ≤ normalizer (X : Set (MulAut (alternatingGroup (Fin 6))))) :
    X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))) :=
    DegreeSix.inner_conjugation_injective
  set X₀ := X.comap MulAut.conj with hX₀
  have hX₀card : Nat.card X₀ ∣ Nat.card X := by
    have h1 : X₀.map MulAut.conj ≤ X := Subgroup.map_comap_le _ _
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le h1
  have hX₀3 : Nat.Coprime 3 (Nat.card X₀) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hX (h.trans hX₀card)
  have hNX₀ : F06 ≤ normalizer (X₀ : Set (alternatingGroup (Fin 6))) := by
    intro f hf
    rw [mem_normalizer_iff]
    intro x
    have hfN := hN ⟨f, hf, rfl⟩
    rw [hX₀, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hfN _)
  have hX₀bot : X₀ = ⊥ := by
    rw [eq_bot_iff]
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three isElemAbelian_F06
      (by rw [card_F06]; norm_num) hNX₀ hX₀3 fun v hv hv1 => ?_
    have hle : X₀ ⊓ Subgroup.centralizer {v} ≤ X₀ ⊓ F06 :=
      inf_le_inf_left _ (centralizer_le_F06 hv hv1)
    refine hle.trans ?_
    have hcop : Nat.Coprime (Nat.card X₀) (Nat.card F06) := by
      rw [card_F06, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.mp hX₀3)
    rw [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot]
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hfix : ∀ f ∈ F06, r f = f := by
    intro f hf
    have hfN := hN ⟨f, hf, rfl⟩
    have hconj : r * MulAut.conj f * r⁻¹ = MulAut.conj (r f) := by
      ext z
      simp [MulAut.conj_apply, MulAut.mul_apply]
    have hmem : MulAut.conj (r f * f⁻¹) ∈ X := by
      rw [map_mul, map_inv, ← hconj]
      have h1 : MulAut.conj f * r⁻¹ * (MulAut.conj f)⁻¹ ∈ X :=
        (mem_normalizer_iff.mp hfN _).mp (inv_mem hr)
      have h2 := mul_mem hr h1
      simpa [mul_assoc] using h2
    have h0 : r f * f⁻¹ ∈ X₀ := hmem
    rw [hX₀bot, Subgroup.mem_bot, mul_inv_eq_one] at h0
    exact h0
  have h3 : Nat.Coprime (orderOf r) 3 := by
    have h := orderOf_dvd_natCard (⟨r, hr⟩ : X)
    rw [Subgroup.orderOf_mk] at h
    exact Nat.Coprime.coprime_dvd_left h
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX).symm
  exact eq_one_of_fix_F06 hfix h3

end CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
