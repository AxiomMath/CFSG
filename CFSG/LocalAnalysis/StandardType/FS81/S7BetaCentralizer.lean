module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7CentralOdd
import CFSG.LocalAnalysis.StandardType.FS81.S7FixedPointSylow
import CFSG.LocalAnalysis.StandardType.FS81.S7Coprime
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.QuasithinUnique

open scoped Pointwise

private theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] {P : Subgroup G} :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := by
  intro a ha
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G),
      ∀ c ∈ Subgroup.centralizer (P : Set G),
        g * c * g⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) k).1 hk
      simpa using this
    have h1 := hc _ hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * k := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key a ha c, fun h => by simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ h⟩

private theorem mem_normalizer_centralizer_singleton {G : Type} [Group G] {β a : G}
    (ha : a * β = β * a) :
    a ∈ Subgroup.normalizer (Subgroup.centralizer ({β} : Set G) : Set G) := by
  have key : ∀ g : G, g * β = β * g → ∀ c ∈ Subgroup.centralizer ({β} : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer ({β} : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have hgc : Commute g β := hg
    calc g * c * g⁻¹ * β = g * c * (g⁻¹ * β) := by group
      _ = g * c * (β * g⁻¹) := by rw [hgc.inv_left.eq]
      _ = g * (c * β) * g⁻¹ := by group
      _ = g * (β * c) * g⁻¹ := by rw [hc]
      _ = g * β * c * g⁻¹ := by group
      _ = β * g * c * g⁻¹ := by rw [hg]
      _ = β * (g * c * g⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key a ha c, fun h => ?_⟩
  have hainv : a⁻¹ * β = β * a⁻¹ := (show Commute a β from ha).inv_left.eq
  simpa [mul_assoc] using key a⁻¹ hainv (a * c * a⁻¹) h

private theorem orderOf_conj_eq {G : Type} [Group G] (a x : G) :
    orderOf (a * x * a⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq a (SemiconjBy.conj_mk a x)).symm

private theorem eq_one_of_mem_zpowers_of_order_two_of_pow {G : Type} [Group G] {σ l : G}
    (hσ : orderOf σ = 2) (hl : l ∈ Subgroup.zpowers σ)
    (hl3 : ∃ n : ℕ, l ^ (3 ^ n) = 1) : l = 1 := by
  obtain ⟨n, hn⟩ := hl3
  have h1 : orderOf l ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
  have h2 : orderOf l ∣ 2 := by
    rw [← hσ]
    exact orderOf_dvd_of_mem_zpowers hl
  have hodd : ∀ m : ℕ, ¬ 2 ∣ 3 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      intro h
      exact ih ((Nat.Coprime.dvd_mul_right (by norm_num : Nat.Coprime 2 3)).mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h2' | h2'
  · exact orderOf_eq_one_iff.mp h2'
  · exfalso
    exact hodd n (h2' ▸ h1)

private theorem zpowers_le_pCoreOf_of_central {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {σ : G} (hσH : σ ∈ H) (hσc : ∀ h ∈ H, h * σ = σ * h)
    (hσ : orderOf σ = 2) : Subgroup.zpowers σ ≤ pCoreOf 2 H := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    (N := Subgroup.zpowers σ) (H := H) ?_ ?_ ?_
  · exact Subgroup.zpowers_le.mpr hσH
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [Subgroup.mem_zpowers_iff] at hz ⊢
      obtain ⟨k, rfl⟩ := hz
      exact ⟨k, ((show Commute c σ from hσc c hc).zpow_right k).mul_inv_cancel.symm⟩
    · intro hz
      rw [Subgroup.mem_zpowers_iff] at hz ⊢
      obtain ⟨k, hk⟩ := hz
      refine ⟨k, ?_⟩
      rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group, ← hk]
      simpa using
        (((show Commute c σ from hσc c hc).inv_left).zpow_right k).mul_inv_cancel.symm
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hσ]
    norm_num

private theorem mem_zpowers_of_mul_mem_zpowers {G : Type} [Group G] {β σ p l x : G}
    (hβ : orderOf β = 3) (hσ : orderOf σ = 2)
    (hp : p ∈ Subgroup.zpowers β) (hl : l ∈ Subgroup.zpowers σ)
    (hpl : p * l = x) (hx3 : ∃ n : ℕ, x ^ (3 ^ n) = 1) (hpx : p * x = x * p) :
    x ∈ Subgroup.zpowers β := by
  have hcomm : Commute p⁻¹ x := (show Commute p x from hpx).inv_left
  obtain ⟨n, hn⟩ := hx3
  have hp3 : p ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_mem_zpowers hp).trans (by simp [hβ])
  have hxlarge : x ^ (3 ^ (n + 1)) = 1 := by
    rw [pow_succ, pow_mul, hn, one_pow]
  have hpinv : (p⁻¹) ^ (3 ^ (n + 1)) = 1 := by
    rw [pow_succ', pow_mul, show p⁻¹ ^ 3 = 1 by rw [inv_pow, hp3, inv_one], one_pow]
  have hl1 : l = 1 := by
    refine eq_one_of_mem_zpowers_of_order_two_of_pow hσ hl ⟨n + 1, ?_⟩
    have hlx : l = p⁻¹ * x := by rw [← hpl]; group
    rw [hlx, hcomm.mul_pow, hpinv, hxlarge, one_mul]
  rw [← hpl, hl1, mul_one]
  exact hp

private theorem exists_zpow_mul_of_mem_sup_zpowers_of_le_normalizer
    {G : Type} [Group G] {β : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (Subgroup.zpowers β : Set G)) {x : G}
    (hx : x ∈ Subgroup.zpowers β ⊔ L) :
    ∃ k : ℤ, ∃ l ∈ L, β ^ k * l = x := by
  have hx' : x ∈ (Subgroup.zpowers β : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers β) L hL]
    exact hx
  obtain ⟨y, hy, l, hl, hyl⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨k, l, hl, hyl⟩

private theorem exists_zpow_mul_of_mem_sup_zpowers
    {G : Type} [Group G] {β : G} {L : Subgroup G}
    (hLc : ∀ l ∈ L, l * β = β * l) {x : G}
    (hx : x ∈ Subgroup.zpowers β ⊔ L) :
    ∃ k : ℤ, ∃ l ∈ L, β ^ k * l = x := by
  refine exists_zpow_mul_of_mem_sup_zpowers_of_le_normalizer ?_ hx
  intro l hl
  rw [Subgroup.zpowers_eq_closure]
  refine Subgroup.normalizer_le_normalizer_closure ({β} : Set G) ?_
  rw [Subgroup.normalizer_singleton]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hLc l hl)

theorem centralizer_le_of_betaData {G : Type} [Group G] [Finite G] {Y L A : Subgroup G}
    {b₀ β σ : G} (h : BetaData Y L A b₀ β σ) :
    ∀ y ∈ Subgroup.centralizer ({β} : Set G), y * σ = σ * y →
      (∀ p ∈ pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G)), y * p = p * y) →
      y ∈ pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G)) ⊔ Subgroup.zpowers β := by
  classical
  intro y hyβ _hyσ hyP
  set P : Subgroup G := pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G))
  set Z : Subgroup G :=
    Subgroup.centralizer ({β} : Set G) ⊓ Subgroup.centralizer (P : Set G)
  have hβcent : β ∈ Subgroup.centralizer ({β} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hβP : β ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact h.L_cent q
      ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2)
        (L ⊓ Subgroup.centralizer ({σ} : Set G)) hq).1)
  have hβZ : β ∈ Z := ⟨hβcent, hβP⟩
  have hβc : ∀ z ∈ Z, z * β = β * z := fun _ hz =>
    Subgroup.mem_centralizer_singleton_iff.mp hz.1
  have hAβ : ∀ a ∈ A, a * β = β * a := fun a ha => h.L_cent a (h.A_le ha)
  have hAinf : A ≤ L ⊓ Subgroup.centralizer ({σ} : Set G) := fun a ha =>
    ⟨h.A_le ha, Subgroup.mem_centralizer_singleton_iff.mpr (h.A_cent a ha)⟩
  have hAnormΓ : A ≤ Subgroup.normalizer
      (Subgroup.centralizer ({β} : Set G) : Set G) := fun a ha =>
    mem_normalizer_centralizer_singleton (h.L_cent a (h.A_le ha))
  have hAnormP : A ≤ Subgroup.normalizer (P : Set G) :=
    hAinf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2)
      (L ⊓ Subgroup.centralizer ({σ} : Set G)))
  have hAnormCP : A ≤ Subgroup.normalizer
      (Subgroup.centralizer (P : Set G) : Set G) :=
    hAnormP.trans normalizer_le_normalizer_centralizer
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      (H := Subgroup.centralizer ({β} : Set G))
      (K := Subgroup.centralizer (P : Set G)) ⟨hAnormΓ ha, hAnormCP ha⟩
  have hF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∀ x ∈ Z,
      (∃ n : ℕ, x ^ (3 ^ n) = 1) → (∀ a ∈ F, a * x = x * a) →
      x ∈ Subgroup.zpowers β := by
    intro F hFA hFcard x hxZ hx3 hxF
    obtain ⟨y, hyY, hyb⟩ := h.A_conj F hFA hFcard
    have hcx : (y * b₀ * y⁻¹) * x = x * (y * b₀ * y⁻¹) := hxF _ hyb
    have hyx : y⁻¹ * x * y ∈ Subgroup.centralizer ({b₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y⁻¹ * x * y) * b₀ = y⁻¹ * (x * (y * b₀ * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * b₀ * y⁻¹) * x) * y := by rw [← hcx]
        _ = b₀ * (y⁻¹ * x * y) := by group
    have hxY : x ∈ Y := by
      have hyxY := h.b₀_cent hyx
      have hxeq : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      rw [hxeq]
      exact Y.mul_mem (Y.mul_mem hyY hyxY) (Y.inv_mem hyY)
    have hxβ : x * β = β * x := Subgroup.mem_centralizer_singleton_iff.mp hxZ.1
    obtain ⟨i, l, hl_mem, hpl⟩ :=
      exists_zpow_mul_of_mem_sup_zpowers h.L_cent (h.Y_cent x hxY hxβ)
    have hp_mem : β ^ i ∈ Subgroup.zpowers β := Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    have hpcomm : β ^ i * x = x * β ^ i := by
      have hcomm : Commute β x := (Subgroup.mem_centralizer_singleton_iff.mp hxZ.1).symm
      exact (hcomm.zpow_left i).eq
    have hpZ : β ^ i ∈ Z := Subgroup.zpowers_le.mpr hβZ hp_mem
    have hlZ : l ∈ Z := by
      have hlx : l = (β ^ i)⁻¹ * x := by rw [← hpl]; group
      rw [hlx]
      exact Z.mul_mem (Z.inv_mem hpZ) hxZ
    have hlC : ∀ q ∈ P, l * q = q * l := fun q hq =>
      (Subgroup.mem_centralizer_iff.mp hlZ.2 q hq).symm
    have hlσ : l ∈ Subgroup.zpowers σ := h.centP l hl_mem hlC
    exact mem_zpowers_of_mul_mem_zpowers h.β_ord h.σ_ord hp_mem hlσ hpl hx3 hpcomm
  have hS : ∀ T : Subgroup G, T ≤ Z → IsPGroup 3 T → Nat.card T ≤ 3 :=
    card_le_three_of_fixed_point h.A_elem h.A_card hAZ hβZ h.β_ord hβc hAβ hF
  obtain ⟨K, hKZ, hKnorm, hKcop, hZK, hKmem⟩ :=
    exists_normalComplement_of_central_three hβZ h.β_ord hβc hS
  have hAnormK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hxZ : x ∈ Z
    · have haxZ : a * x * a⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hAZ ha) x).mp hxZ
      simp only [hKmem x hxZ, hKmem (a * x * a⁻¹) haxZ, orderOf_conj_eq]
    · have haxZ : a * x * a⁻¹ ∉ Z := fun hx =>
        hxZ ((Subgroup.mem_normalizer_iff.mp (hAZ ha) x).mpr hx)
      simp only [show ¬x ∈ K from fun hx => hxZ (hKZ hx),
        show ¬a * x * a⁻¹ ∈ K from fun hx => haxZ (hKZ hx)]
  have hKY : K ≤ Y :=
    le_of_hyperplane_conj h.b₀_cent h.A_elem h.A_card h.A_conj hAnormK hKcop
  have hσP : Subgroup.zpowers σ ≤ P := by
    have hσH : σ ∈ L ⊓ Subgroup.centralizer ({σ} : Set G) :=
      ⟨h.σ_mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hσc : ∀ g ∈ L ⊓ Subgroup.centralizer ({σ} : Set G), g * σ = σ * g :=
      fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg.2
    exact zpowers_le_pCoreOf_of_central hσH hσc h.σ_ord
  have hKσ : K ≤ Subgroup.zpowers σ := by
    intro k hkK
    have hkZ : k ∈ Z := hKZ hkK
    have hkY : k ∈ Y := hKY hkK
    have hkβ : k * β = β * k := Subgroup.mem_centralizer_singleton_iff.mp hkZ.1
    obtain ⟨i, l, hl_mem, hpl⟩ :=
      exists_zpow_mul_of_mem_sup_zpowers h.L_cent (h.Y_cent k hkY hkβ)
    have hp_mem : β ^ i ∈ Subgroup.zpowers β := Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    have hpZ : β ^ i ∈ Z := Subgroup.zpowers_le.mpr hβZ hp_mem
    have hlZ : l ∈ Z := by
      have hlx : l = (β ^ i)⁻¹ * k := by rw [← hpl]; group
      rw [hlx]
      exact Z.mul_mem (Z.inv_mem hpZ) hkZ
    have hlC : ∀ q ∈ P, l * q = q * l := fun q hq =>
      (Subgroup.mem_centralizer_iff.mp hlZ.2 q hq).symm
    have hlσ : l ∈ Subgroup.zpowers σ := h.centP l hl_mem hlC
    have hl2 : orderOf l ∣ 2 := by
      rw [← h.σ_ord]
      exact orderOf_dvd_of_mem_zpowers hlσ
    have hlK : l ∈ K :=
      (hKmem l hlZ).mpr (fun h3 => absurd (h3.trans hl2) (by norm_num : ¬ 3 ∣ 2))
    have hpK : β ^ i ∈ K := by
      have hp_eq : β ^ i = k * l⁻¹ := by rw [← hpl]; group
      rw [hp_eq]
      exact K.mul_mem hkK (K.inv_mem hlK)
    have hp3dvd : orderOf (β ^ i) ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hp_mem
      rwa [h.β_ord] at this
    have hpndvd : ¬ 3 ∣ orderOf (β ^ i) := (hKmem (β ^ i) hpZ).mp hpK
    have hp1 : β ^ i = 1 := by
      obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).mp hp3dvd
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (h3 ▸ dvd_rfl) hpndvd
    rw [← hpl, hp1, one_mul]
    exact hlσ
  have hyZ : y ∈ Z := ⟨hyβ, Subgroup.mem_centralizer_iff.mpr (fun p hp => (hyP p hp).symm)⟩
  obtain ⟨i, k, hkK, hpk⟩ :=
    exists_zpow_mul_of_mem_sup_zpowers (L := K)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKZ hk).1) (hZK hyZ)
  have hp_mem : β ^ i ∈ Subgroup.zpowers β := Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
  have hy : y ∈ Subgroup.zpowers β ⊔ P := by
    rw [← hpk]
    exact Subgroup.mul_mem_sup hp_mem (hσP (hKσ hkK))
  simpa [sup_comm] using hy

end CFSG.StandardType.FrameRoute.FS81

end
