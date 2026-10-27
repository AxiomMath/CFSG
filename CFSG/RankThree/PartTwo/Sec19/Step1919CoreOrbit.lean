module

public import CFSG.RankThree.PartTwo.Sec19.Step1919Narrow
public import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1919CoreProof

variable {G : Type} [Group G]

@[expose] def cenMod (M K : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M}
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun k hk => ?_⟩
    have hxN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hxM
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp (hy k hk)
    have e : x * y * k * (x * y)⁻¹ * k⁻¹ =
        (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (hx k hk)
  one_mem' := ⟨M.one_mem, fun k _ => by
    rw [show (1 : G) * k * 1⁻¹ * k⁻¹ = 1 by group]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun k hk => ?_⟩
    have hxN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (M.inv_mem hxM)
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.inv_mem _ (hx k hk))
    have e : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ = x⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h1

variable [Finite G]

theorem mem_cenMod_of_ne {M K K' : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hK' : K' ∈ oTwoComponentsIn M) (hne : K ≠ K') {x : G} (hx : x ∈ K) : x ∈ cenMod M K' :=
  ⟨le_of_mem_oTwoComponentsIn hK hx, fun _ hk =>
    Step1910Proof.commutator_mem_pCoreOf hK hK' hne hx hk⟩

omit [Finite G] in
theorem not_mem_cenMod {M K : Subgroup G} {x : G}
    (hx : ∃ k ∈ K, x * k * x⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) : x ∉ cenMod M K := by
  rintro ⟨-, h⟩
  obtain ⟨k, hk, hxk⟩ := hx
  exact hxk (h k hk)

omit [Finite G] in
theorem conj_mem_cenMod {M K : Subgroup G} {w x : G} (hw : w ∈ M) (hx : x ∈ cenMod M K) :
    w * x * w⁻¹ ∈ cenMod M (K.map (MulAut.conj w).toMonoidHom) := by
  obtain ⟨hxM, hxK⟩ := hx
  refine ⟨M.mul_mem (M.mul_mem hw hxM) (M.inv_mem hw), ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hwN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hw
  have h1 := (Subgroup.mem_normalizer_iff.mp hwN _).mp (hxK k hk)
  have e : w * x * w⁻¹ * (MulAut.conj w).toMonoidHom k * (w * x * w⁻¹)⁻¹ *
      ((MulAut.conj w).toMonoidHom k)⁻¹ = w * (x * k * x⁻¹ * k⁻¹) * w⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact h1

omit [Finite G] in
theorem le_normalizer_of_le {E X Y : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hXE : X ≤ E) (hYE : Y ≤ E) : X ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hEc g (hXE hg) h (hYE hh), mul_inv_cancel_right]
    exact hh
  · intro hh
    have hw := hYE hh
    have e : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hEc g⁻¹ (E.inv_mem (hXE hg)) _ hw]
        _ = g * h * g⁻¹ := by group
    rw [e]
    exact hh

theorem card_le_of_chain {E : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEe : ∀ e ∈ E, e ^ 3 = 1) {x₁ x₂ x₃ x₄ : G} (h₁ : x₁ ∈ E) (h₂ : x₂ ∈ E) (h₃ : x₃ ∈ E)
    (h₄ : x₄ ∈ E) (hn₁ : x₁ ≠ 1) (hn₂ : x₂ ∉ Subgroup.zpowers x₁)
    (hn₃ : x₃ ∉ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hn₄ : x₄ ∉ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃) :
    81 ≤ Nat.card E := by
  have hV₁E : Subgroup.zpowers x₁ ≤ E := Subgroup.zpowers_le.mpr h₁
  have hV₂E : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ E :=
    sup_le hV₁E (Subgroup.zpowers_le.mpr h₂)
  have hV₃E : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ≤ E :=
    sup_le hV₂E (Subgroup.zpowers_le.mpr h₃)
  have hV₄E : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ⊔
      Subgroup.zpowers x₄ ≤ E := sup_le hV₃E (Subgroup.zpowers_le.mpr h₄)
  have ho : ∀ {x : G} {Y : Subgroup G}, x ∈ E → x ∉ Y → orderOf x = 3 := fun hx hxY =>
    orderOf_eq_prime (hEe _ hx) fun h => hxY (h ▸ Subgroup.one_mem _)
  have h1 : Nat.card (Subgroup.zpowers x₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEe _ h₁) hn₁
  have h2 := Step1919NarrowRank.card_sup_zpowers_of_orderOf _ (ho h₂ hn₂) hn₂
    (fun z hz => hEc z (hV₁E hz) x₂ h₂)
  have h3 := Step1919NarrowRank.card_sup_zpowers_of_orderOf _ (ho h₃ hn₃) hn₃
    (fun z hz => hEc z (hV₂E hz) x₃ h₃)
  have h4 := Step1919NarrowRank.card_sup_zpowers_of_orderOf _ (ho h₄ hn₄) hn₄
    (fun z hz => hEc z (hV₃E hz) x₄ h₄)
  have h5 := Subgroup.card_le_of_le hV₄E
  rw [h4, h3, h2, h1] at h5
  omega

omit [Finite G] in
theorem not_mem_of_le_cenMod {M K V : Subgroup G} (hV : V ≤ cenMod M K) {x : G}
    (hx : ∃ k ∈ K, x * k * x⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) : x ∉ V :=
  fun h => not_mem_cenMod hx (hV h)

omit [Finite G] in
theorem mem_normalizer_of_sq_mem {K : Subgroup G} {w : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (h2 : w * w ∈ Subgroup.normalizer (K : Set G)) : w ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨k, hk⟩ := hw
  have hcop : Nat.Coprime 2 (orderOf w) :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, pow_two]
  exact Subgroup.pow_mem _ h2 m

omit [Finite G] in
theorem map_conj_ne_of_pow {K : Subgroup G} {w : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hwK : w ∉ Subgroup.normalizer (K : Set G)) :
    K ≠ K.map (MulAut.conj w).toMonoidHom ∧ K ≠ K.map (MulAut.conj (w * w)).toMonoidHom ∧
      K.map (MulAut.conj w).toMonoidHom ≠ K.map (MulAut.conj (w * w)).toMonoidHom := by
  have h1 : K ≠ K.map (MulAut.conj w).toMonoidHom := fun h =>
    hwK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  refine ⟨h1, fun h => ?_, fun h => ?_⟩
  · exact hwK (mem_normalizer_of_sq_mem hw (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm))
  · apply h1
    have h3 := congrArg (Subgroup.map (MulAut.conj w⁻¹).toMonoidHom) h
    rw [Step199Proof.map_conj_map_conj, Step199Proof.map_conj_map_conj, inv_mul_cancel,
      Step199Proof.map_conj_one, show w⁻¹ * (w * w) = w by group] at h3
    exact h3

theorem conj_eq_of_mem_zpowers {u x : G} (hu : ∃ k : ℕ, u ^ 3 ^ k = 1) (hx3 : x ^ 3 = 1)
    (hux : u * x * u⁻¹ ∈ Subgroup.zpowers x) : u * x * u⁻¹ = x := by
  classical
  by_cases hx1 : x = 1
  · rw [hx1]
    group
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hux)
  rw [hxo, Finset.mem_range] at hm
  interval_cases m
  · exfalso
    apply hx1
    rw [pow_zero] at hmx
    calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
      _ = 1 := by rw [← hmx]; group
  · rw [← hmx, pow_one]
  ·
    have h2 : u * u ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : u * (u * x * u⁻¹) * u⁻¹ = x := by
        rw [← hmx, ← conj_pow, ← hmx, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
          hx3, one_mul, pow_one]
      calc u * u * x = u * (u * x * u⁻¹) * u⁻¹ * (u * u) := by group
        _ = x * (u * u) := by rw [e]
    obtain ⟨k, hk⟩ := hu
    have hcop : Nat.Coprime 2 (orderOf u) :=
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
    have hu : u ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [← hn, pow_two]
      exact Subgroup.pow_mem _ h2 n
    rw [Subgroup.mem_centralizer_singleton_iff] at hu
    rw [hu, mul_inv_cancel_right]

theorem card_eq_of_chain3 {E : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEe : ∀ e ∈ E, e ^ 3 = 1) {x₁ x₂ x₃ : G} (h₁ : x₁ ∈ E) (h₂ : x₂ ∈ E) (h₃ : x₃ ∈ E)
    (hn₁ : x₁ ≠ 1) (hn₂ : x₂ ∉ Subgroup.zpowers x₁)
    (hn₃ : x₃ ∉ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ : Subgroup G) =
      27 := by
  have hV₁E : Subgroup.zpowers x₁ ≤ E := Subgroup.zpowers_le.mpr h₁
  have hV₂E : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ E :=
    sup_le hV₁E (Subgroup.zpowers_le.mpr h₂)
  have ho : ∀ {x : G} {Y : Subgroup G}, x ∈ E → x ∉ Y → orderOf x = 3 := fun hx hxY =>
    orderOf_eq_prime (hEe _ hx) fun h => hxY (h ▸ Subgroup.one_mem _)
  have h1 : Nat.card (Subgroup.zpowers x₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEe _ h₁) hn₁
  have h2 := Step1919NarrowRank.card_sup_zpowers_of_orderOf _ (ho h₂ hn₂) hn₂
    (fun z hz => hEc z (hV₁E hz) x₂ h₂)
  have h3 := Step1919NarrowRank.card_sup_zpowers_of_orderOf _ (ho h₃ hn₃) hn₃
    (fun z hz => hEc z (hV₂E hz) x₃ h₃)
  rw [h3, h2, h1]

theorem conj_eq_of_mem_normalizer {M E K K' K'' : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ e ∈ E, e ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hK : K ∈ oTwoComponentsIn M) (hK' : K' ∈ oTwoComponentsIn M)
    (hK'' : K'' ∈ oTwoComponentsIn M) (h12 : K ≠ K') (h13 : K ≠ K'') (h23 : K' ≠ K'')
    {x x' x'' : G} (hxE : x ∈ E) (hx'E : x' ∈ E) (hx''E : x'' ∈ E) (hxK : x ∈ K)
    (hx'K : x' ∈ K')
    (hxn : ∃ k ∈ K, x * k * x⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx'n : ∃ k ∈ K', x' * k * x'⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx''n : ∃ k ∈ K'', x'' * k * x''⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    {u : G} (huE : u ∈ Subgroup.normalizer (E : Set G)) (hu3 : ∃ k : ℕ, u ^ 3 ^ k = 1)
    (huK : u ∈ Subgroup.normalizer (K : Set G)) : u * x * u⁻¹ = x := by
  have hx1 : x ≠ 1 := fun h => not_mem_cenMod hxn (h ▸ (cenMod M K).one_mem)
  have hyE : u * x * u⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp huE x).mp hxE
  have hyK : u * x * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp huK x).mp hxK
  refine conj_eq_of_mem_zpowers hu3 (hEe x hxE) ?_
  by_contra hy
  have := card_le_of_chain hEc hEe hxE hyE hx'E hx''E hx1 hy
    (not_mem_of_le_cenMod (sup_le (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK hK' h12 hxK))
      (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK hK' h12 hyK))) hx'n)
    (not_mem_of_le_cenMod (sup_le (sup_le (Subgroup.zpowers_le.mpr
      (mem_cenMod_of_ne hK hK'' h13 hxK)) (Subgroup.zpowers_le.mpr
        (mem_cenMod_of_ne hK hK'' h13 hyK))) (Subgroup.zpowers_le.mpr
          (mem_cenMod_of_ne hK' hK'' h23 hx'K))) hx''n)
  omega

theorem commute_of_mem_normalizer {M E K₁ K₂ K₃ : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ e ∈ E, e ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hK₁ : K₁ ∈ oTwoComponentsIn M) (hK₂ : K₂ ∈ oTwoComponentsIn M)
    (hK₃ : K₃ ∈ oTwoComponentsIn M) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    {x₁ x₂ x₃ : G} (hx₁E : x₁ ∈ E) (hx₂E : x₂ ∈ E) (hx₃E : x₃ ∈ E) (hx₁K : x₁ ∈ K₁)
    (hx₂K : x₂ ∈ K₂) (hx₃K : x₃ ∈ K₃)
    (hx₁n : ∃ k ∈ K₁, x₁ * k * x₁⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx₂n : ∃ k ∈ K₂, x₂ * k * x₂⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx₃n : ∃ k ∈ K₃, x₃ * k * x₃⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    {u : G} (huE : u ∈ Subgroup.normalizer (E : Set G)) (hu3 : ∃ k : ℕ, u ^ 3 ^ k = 1)
    (hu₁ : u ∈ Subgroup.normalizer (K₁ : Set G)) (hu₂ : u ∈ Subgroup.normalizer (K₂ : Set G))
    (hu₃ : u ∈ Subgroup.normalizer (K₃ : Set G)) : ∀ e ∈ E, u * e * u⁻¹ = e := by
  have e₁ := conj_eq_of_mem_normalizer hEc hEe hE27 hK₁ hK₂ hK₃ h12 h13 h23 hx₁E hx₂E hx₃E hx₁K
    hx₂K hx₁n hx₂n hx₃n huE hu3 hu₁
  have e₂ := conj_eq_of_mem_normalizer hEc hEe hE27 hK₂ hK₁ hK₃ (Ne.symm h12) h23 h13 hx₂E hx₁E
    hx₃E hx₂K hx₁K hx₂n hx₁n hx₃n huE hu3 hu₂
  have e₃ := conj_eq_of_mem_normalizer hEc hEe hE27 hK₃ hK₁ hK₂ (Ne.symm h13) (Ne.symm h23) h12
    hx₃E hx₁E hx₂E hx₃K hx₁K hx₃n hx₁n hx₂n huE hu3 hu₃
  have hc : ∀ {x : G}, u * x * u⁻¹ = x → x ∈ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * u = u * x * u⁻¹ * u := by rw [hx]
      _ = u * x := by group
  have hx₁1 : x₁ ≠ 1 := fun h => not_mem_cenMod hx₁n (h ▸ (cenMod M K₁).one_mem)
  have hle : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ≤ E :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hx₁E) (Subgroup.zpowers_le.mpr hx₂E))
      (Subgroup.zpowers_le.mpr hx₃E)
  have hEeq : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ = E :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hE27, card_eq_of_chain3 hEc hEe hx₁E hx₂E hx₃E hx₁1
        (not_mem_of_le_cenMod (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK₁ hK₂ h12 hx₁K)) hx₂n)
        (not_mem_of_le_cenMod (sup_le (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK₁ hK₃ h13 hx₁K))
          (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK₂ hK₃ h23 hx₂K))) hx₃n)])
  have hEC : E ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← hEeq]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr (hc e₁)) (Subgroup.zpowers_le.mpr (hc e₂)))
      (Subgroup.zpowers_le.mpr (hc e₃))
  intro e he
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hEC he)
  rw [← h, mul_inv_cancel_right]

theorem false_of_not_mem_normalizer {M E F K K' K'' : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ e ∈ E, e ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hFE : F ≤ E) (hF9 : Nat.card F = 9)
    (hK : K ∈ oTwoComponentsIn M) (hK' : K' ∈ oTwoComponentsIn M)
    (hK'' : K'' ∈ oTwoComponentsIn M) (h12 : K ≠ K') (h13 : K ≠ K'') (h23 : K' ≠ K'')
    {x x' x'' : G} (hxE : x ∈ E) (hx'E : x' ∈ E) (hx''E : x'' ∈ E) (hxK : x ∈ K)
    (hx'K : x' ∈ K') (hx''K : x'' ∈ K'')
    (hxn : ∃ k ∈ K, x * k * x⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx'n : ∃ k ∈ K', x' * k * x'⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx''n : ∃ k ∈ K'', x'' * k * x''⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    {u : G} (huM : u ∈ M) (huE : u ∈ Subgroup.normalizer (E : Set G))
    (hu3 : ∃ k : ℕ, u ^ 3 ^ k = 1) (huF : ∀ f ∈ F, u * f * u⁻¹ = f)
    (huK : u ∉ Subgroup.normalizer (K : Set G)) : False := by
  have hx'C : x' ∈ cenMod M K := mem_cenMod_of_ne hK' hK (Ne.symm h12) hx'K
  have hx''C : x'' ∈ cenMod M K := mem_cenMod_of_ne hK'' hK (Ne.symm h13) hx''K
  set V := Subgroup.zpowers x' ⊔ Subgroup.zpowers x'' with hVdef
  have hVC : V ≤ cenMod M K :=
    sup_le (Subgroup.zpowers_le.mpr hx'C) (Subgroup.zpowers_le.mpr hx''C)
  have hVE : V ≤ E := sup_le (Subgroup.zpowers_le.mpr hx'E) (Subgroup.zpowers_le.mpr hx''E)
  have hx'1 : x' ≠ 1 := fun h => not_mem_cenMod hx'n (h ▸ (cenMod M K').one_mem)
  have hx''V : x'' ∉ Subgroup.zpowers x' :=
    not_mem_of_le_cenMod (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK' hK'' h23 hx'K)) hx''n
  have hV9 : Nat.card V = 9 := by
    rw [hVdef, Step1919NarrowRank.card_sup_zpowers_of_orderOf _
      (orderOf_eq_prime (hEe _ hx''E) (fun h => hx''V (h ▸ Subgroup.one_mem _))) hx''V
      (fun z hz => hEc z ((Subgroup.zpowers_le.mpr hx'E) hz) x'' hx''E), Nat.card_zpowers,
      orderOf_eq_prime (hEe _ hx'E) hx'1]
  have hFV : F ⊓ V ≠ ⊥ := by
    intro h
    have h1 := Sec6.card_sup_mul_card_inf (le_normalizer_of_le hEc hFE hVE)
    rw [h, Subgroup.card_bot, mul_one, hF9, hV9] at h1
    have h2 : Nat.card (F ⊔ V : Subgroup G) ≤ 27 := hE27 ▸ Subgroup.card_le_of_le (sup_le hFE hVE)
    omega
  obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFV
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hfF : f ∈ F := (Subgroup.mem_inf.mp hf).1
  have hfE : f ∈ E := hFE hfF
  have hfC : f ∈ cenMod M K := hVC (Subgroup.mem_inf.mp hf).2
  obtain ⟨hne1, hne2, hne3⟩ := map_conj_ne_of_pow hu3 huK
  have huuM : u * u ∈ M := M.mul_mem huM huM
  have hfC1 : f ∈ cenMod M (K.map (MulAut.conj u).toMonoidHom) := by
    have := conj_mem_cenMod huM hfC
    rwa [huF f hfF] at this
  have hfC2 : f ∈ cenMod M (K.map (MulAut.conj (u * u)).toMonoidHom) := by
    have := conj_mem_cenMod huuM hfC
    rwa [show u * u * f * (u * u)⁻¹ = u * (u * f * u⁻¹) * u⁻¹ by group, huF f hfF,
      huF f hfF] at this
  have hK1 := Sec18.map_conj_mem_oTwoComponentsIn hK huM
  have hK2 := Sec18.map_conj_mem_oTwoComponentsIn hK huuM
  have hx1K : u * x * u⁻¹ ∈ K.map (MulAut.conj u).toMonoidHom := ⟨x, hxK, rfl⟩
  have hx2K : (u * u) * x * (u * u)⁻¹ ∈ K.map (MulAut.conj (u * u)).toMonoidHom :=
    ⟨x, hxK, rfl⟩
  have hx1E : u * x * u⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp huE x).mp hxE
  have hx2E : (u * u) * x * (u * u)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mul_mem _ huE huE) x).mp hxE
  have hx1n := Step1919Narrow.conj_exists_not_mem huM hxn
  have hx2n := Step1919Narrow.conj_exists_not_mem huuM hxn
  have := card_le_of_chain hEc hEe hfE hxE hx1E hx2E hf1'
    (not_mem_of_le_cenMod (Subgroup.zpowers_le.mpr hfC) hxn)
    (not_mem_of_le_cenMod (sup_le (Subgroup.zpowers_le.mpr hfC1)
      (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK hK1 hne1 hxK))) hx1n)
    (not_mem_of_le_cenMod (sup_le (sup_le (Subgroup.zpowers_le.mpr hfC2)
      (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK hK2 hne2 hxK)))
      (Subgroup.zpowers_le.mpr (mem_cenMod_of_ne hK1 hK2 hne3 hx1K))) hx2n)
  omega

theorem mem_normalizer_of_pow {M E F J : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ e ∈ E, e ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hFE : F ≤ E) (hF9 : Nat.card F = 9) (hJ : J ∈ oTwoComponentsIn M) {y : G} (hyE : y ∈ E)
    (hyJ : y ∈ J) (hyn : ∃ k ∈ J, y * k * y⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    {u : G} (huM : u ∈ M) (huE : u ∈ Subgroup.normalizer (E : Set G))
    (hu3 : ∃ k : ℕ, u ^ 3 ^ k = 1) (huF : ∀ f ∈ F, u * f * u⁻¹ = f)
    (hue : ∃ e ∈ E, u * e * u⁻¹ ≠ e) {g : G} (hgM : g ∈ M)
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) :
    g ∈ Subgroup.normalizer (J : Set G) := by
  by_contra hgJ
  obtain ⟨hne1, hne2, hne3⟩ := map_conj_ne_of_pow hg3 hgJ
  have hggM : g * g ∈ M := M.mul_mem hgM hgM
  have hJ₁ := Sec18.map_conj_mem_oTwoComponentsIn hJ hgM
  have hJ₂ := Sec18.map_conj_mem_oTwoComponentsIn hJ hggM
  have hy₁J : g * y * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := ⟨y, hyJ, rfl⟩
  have hy₂J : (g * g) * y * (g * g)⁻¹ ∈ J.map (MulAut.conj (g * g)).toMonoidHom := ⟨y, hyJ, rfl⟩
  have hy₁E : g * y * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE y).mp hyE
  have hy₂E : (g * g) * y * (g * g)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mul_mem _ hgE hgE) y).mp hyE
  have hy₁n := Step1919Narrow.conj_exists_not_mem hgM hyn
  have hy₂n := Step1919Narrow.conj_exists_not_mem hggM hyn
  by_cases h0 : u ∈ Subgroup.normalizer (J : Set G)
  · by_cases h1 : u ∈ Subgroup.normalizer (J.map (MulAut.conj g).toMonoidHom : Set G)
    · by_cases h2 : u ∈ Subgroup.normalizer (J.map (MulAut.conj (g * g)).toMonoidHom : Set G)
      · obtain ⟨e, he, hue'⟩ := hue
        exact hue' (commute_of_mem_normalizer hEc hEe hE27 hJ hJ₁ hJ₂ hne1 hne2 hne3 hyE hy₁E
          hy₂E hyJ hy₁J hy₂J hyn hy₁n hy₂n huE hu3 h0 h1 h2 e he)
      · exact false_of_not_mem_normalizer hEc hEe hE27 hFE hF9 hJ₂ hJ hJ₁ (Ne.symm hne2)
          (Ne.symm hne3) hne1 hy₂E hyE hy₁E hy₂J hyJ hy₁J hy₂n hyn hy₁n huM huE hu3 huF h2
    · exact false_of_not_mem_normalizer hEc hEe hE27 hFE hF9 hJ₁ hJ hJ₂ (Ne.symm hne1) hne3
        hne2 hy₁E hyE hy₂E hy₁J hyJ hy₂J hy₁n hyn hy₂n huM huE hu3 huF h1
  · exact false_of_not_mem_normalizer hEc hEe hE27 hFE hF9 hJ hJ₁ hJ₂ hne1 hne2 hne3 hyE hy₁E
      hy₂E hyJ hy₁J hy₂J hyn hy₁n hy₂n huM huE hu3 huF h0

end Step1919CoreProof

end CFSG.RankThree.PartTwo.Sec19
