module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspM22Cent
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspDefs

public section

namespace CFSG.Quasithin.H13.Ch4.I436

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_pow_two_involution {A : Type*} [Monoid A] (a : A) (k : ℕ) (hk : a ^ (2 ^ k) = 1)
    (ha : a ≠ 1) : ∃ j : ℕ, a ^ (2 ^ j) * a ^ (2 ^ j) = 1 ∧ a ^ (2 ^ j) ≠ 1 := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one] at hk
    exact absurd hk ha
  | succ k ih =>
    by_cases h : a ^ (2 ^ k) = 1
    · exact ih h
    · refine ⟨k, ?_, h⟩
      rw [← pow_add, ← two_mul, ← pow_succ', hk]

theorem pow_apply_eq {X : Type*} [Group X] {Y : Subgroup X} {α : MulAut X}
    (h : ∀ y ∈ Y, α y = y) (n : ℕ) : ∀ y ∈ Y, (α ^ n) y = y := by
  induction n with
  | zero => intro y _; rfl
  | succ n ih =>
    intro y hy
    rw [pow_succ, MulAut.mul_apply, h y hy, ih y hy]

theorem aut_eq_one_of_pow {X : Type*} [Group X] (Y : Subgroup X)
    (hinv : ∀ β : MulAut X, β * β = 1 → (∀ y ∈ Y, β y = y) → β = 1) (α : MulAut X) (k : ℕ)
    (hk : α ^ (2 ^ k) = 1) (hfix : ∀ y ∈ Y, α y = y) : α = 1 := by
  by_contra ha
  obtain ⟨j, hj2, hj1⟩ := exists_pow_two_involution α k hk ha
  exact hj1 (hinv _ hj2 (pow_apply_eq hfix _))

theorem card_dvd_of_fix {n : ℕ} {N : Subgroup (Equiv.Perm (Fin n))} (Y : Subgroup ↥N)
    {α : MulAut ↥N} {u : Equiv.Perm (Fin n)} (hα : ∀ h : ↥N, (α h : Equiv.Perm (Fin n)) =
      u * h * u⁻¹) (hfix : ∀ y ∈ Y, α y = y) :
    Nat.card ↥Y ∣ Nat.card ↥(centralizerIn N u) := by
  have hle : Y.map N.subtype ≤ centralizerIn N u := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨y.2, ?_⟩
    have h1 := congrArg Subtype.val (hfix y hy)
    rw [hα] at h1
    simp only [Subgroup.coe_subtype]
    calc (y : Equiv.Perm (Fin n)) * u = u * y * u⁻¹ * u := by rw [h1]
      _ = u * y := by group
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective N.subtype_injective] at h

theorem mul_self_eq_one_of_conj {X : Type*} [Group X] (hc : Subgroup.center X = ⊥) {g : X}
    (h : MulAut.conj g * MulAut.conj g = 1) : g * g = 1 := by
  have hm : g * g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun φ : MulAut X => φ z) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * (g * g) = g * (g * z * g⁻¹) * g⁻¹ * (g * g) := by rw [h1]
      _ = g * g * z := by group
  rw [hc, Subgroup.mem_bot] at hm
  exact hm

theorem m23_aut_eq_one
    (Y : Subgroup ↥NativeSporadic.M23) (hY : Nat.card ↥Y = 960) (α : MulAut ↥NativeSporadic.M23)
    (hα2 : α * α = 1) (hfix : ∀ y ∈ Y, α y = y) : α = 1 := by
  obtain ⟨g, rfl⟩ := CFSG.QuasithinUnique.Ch1.m23_all_inner α
  have hg2 := mul_self_eq_one_of_conj m23_center_eq_bot' hα2
  by_contra hne
  have hg1 : g ≠ 1 := fun h => hne (by rw [h, map_one])
  have ho : orderOf (g : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hg2) hg1
  have h := card_dvd_of_fix Y (u := (g : Equiv.Perm (Fin 23))) (fun h => rfl) hfix
  rw [hY, m23_inv_centralizer_card _ g.2 ho] at h
  norm_num at h

theorem m22_aut_eq_one
    (Y : Subgroup ↥NativeSporadic.M22) (hY : Nat.card ↥Y = 960) (α : MulAut ↥NativeSporadic.M22)
    (hα2 : α * α = 1) (hfix : ∀ y ∈ Y, α y = y) : α = 1 := by
  by_contra hne
  by_cases hin : α ∈ inner NativeSporadic.M22
  · obtain ⟨g, rfl⟩ := hin
    have hg2 := mul_self_eq_one_of_conj m22_center_eq_bot' hα2
    have hg1 : g ≠ 1 := fun h => hne (by rw [h, map_one])
    have ho : orderOf (g : Equiv.Perm (Fin 22)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hg2) hg1
    have h := card_dvd_of_fix Y (u := (g : Equiv.Perm (Fin 22))) (fun h => rfl) hfix
    rw [hY, m22_inv_centralizer_card _ g.2 ho] at h
    norm_num at h
  · have hδ' := inv_conj_mem NativeSporadic.M22 m22_delta_normalizes m22_delta_sq
    obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq
      m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hin
    set u := g * m22Delta with hu
    have huN : m22Delta⁻¹ * u ∈ NativeSporadic.M22 := by
      simpa [u, mul_assoc] using hδ' g hg
    have hu2N : u * u ∈ NativeSporadic.M22 := by
      have : u * u = g * (m22Delta * g * m22Delta⁻¹) * (m22Delta * m22Delta) := by
        simp only [u]
        group
      rw [this]
      exact NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem hg (m22_delta_normalizes g hg))
        m22_delta_sq
    have hu2 : u * u = 1 := by
      have hc : (⟨u * u, hu2N⟩ : ↥NativeSporadic.M22) ∈ Subgroup.center ↥NativeSporadic.M22 := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz := congrArg (fun φ : MulAut ↥NativeSporadic.M22 => (φ z : Equiv.Perm (Fin 22))) hα2
        simp only [MulAut.mul_apply, MulAut.one_apply] at hz
        rw [hαg, hαg] at hz
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        calc (z : Equiv.Perm (Fin 22)) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by
              rw [hz]
          _ = u * u * z := by group
      rw [m22_center_eq_bot', Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    have hu1 : u ≠ 1 := by
      intro h1
      apply hin
      refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
      rw [hαg, h1]
      simp
    have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have h := card_dvd_of_fix Y hαg hfix
    rw [hY] at h
    rcases m22_outer_centralizer_card u huN ho with hc | hc <;> rw [hc] at h <;> norm_num at h

theorem autCenter_pow {X : Type*} [Group X] (α : MulAut X) (n : ℕ) :
    L3M.autCenter α ^ n = L3M.autCenter (α ^ n) := by
  induction n with
  | zero =>
    ext y
    induction y using QuotientGroup.induction_on with
    | H x => rfl
  | succ n ih =>
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, L3M.autCenter_mk, L3M.autCenter_mk,
        L3M.autCenter_mk, MulAut.mul_apply]

theorem autCenter_one {X : Type*} [Group X] : L3M.autCenter (1 : MulAut X) = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x => rfl

theorem conjOn_pow {G : Type} [Group G] (K : Subgroup G) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) (x : ↥K) :
    (((L3M.conjOn K hr ^ n) x : ↥K) : G) = r ^ n * x * (r ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, L3M.coe_conjOn, ih, pow_succ']
    group

theorem card_of_E16_L24 {X : Type} [Group X]
    (h : IsExt X (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 2 2 2 Y)) : Nat.card X = 960 := by
  obtain ⟨V, _, hV, hQ, hc⟩ := card_of_isExt h
  rw [hc, card_of_isE2 hV, CFSG.Quasithin.F420.card_of_statedPSL_two_two hQ]
  norm_num

theorem insp436M22M23_holds :
    Insp436M22M23 := by
  intro G _ _ K M M₀ R₀ hKq hM₀K _ _ hC hcl hR₀2 hR₀N hR₀C _ r hr
  set ψ : MulAut ↥K := L3M.conjOn K (hR₀N hr) with hψ
  have hψfix : ∀ x : ↥K, (x : G) ∈ M₀ → ψ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hψ, L3M.coe_conjOn, ← Subgroup.mem_centralizer_iff.mp (hR₀C hr) _ hx,
      mul_inv_cancel_right]
  obtain ⟨k, hk⟩ := hR₀2 ⟨r, hr⟩
  have hrk : r ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hψk : ψ ^ (2 ^ k) = 1 := by
    ext x
    rw [hψ, conjOn_pow, hrk]
    simp
  have hψ1 : L3M.autCenter ψ = 1 := by
    rcases hC with ⟨⟨e⟩, hext⟩ | ⟨⟨e⟩, hext⟩
    ·
      rw [hcl] at hext
      set I := imageModCenter K M₀ with hI
      have hIc : Nat.card ↥I = 960 := card_of_E16_L24 hext
      set β := L3M.autCenter ψ with hβ
      have hβfix : ∀ z ∈ I, β z = z := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hβ, QuotientGroup.mk'_apply, L3M.autCenter_mk,
          hψfix x (Subgroup.mem_subgroupOf.mp hx)]
      have hβk : β ^ (2 ^ k) = 1 := by rw [hβ, autCenter_pow, hψk, autCenter_one]
      set α := MulAut.congr e β with hα
      have hαk : α ^ (2 ^ k) = 1 := by rw [hα, ← map_pow, hβk, map_one]
      set Y := I.map e.toMonoidHom with hY
      have hYc : Nat.card ↥Y = 960 := by
        rw [hY, Subgroup.card_map_of_injective e.injective, hIc]
      have hαfix : ∀ y ∈ Y, α y = y := by
        rintro _ ⟨z, hz, rfl⟩
        simp only [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, hβfix z hz]
      have hα1 : α = 1 := aut_eq_one_of_pow Y (fun β' hβ'2 hβ'fix =>
        m22_aut_eq_one Y hYc β' hβ'2 hβ'fix) α k hαk hαfix
      have := (MulAut.congr e).injective (hα1.trans (map_one _).symm)
      exact this
    ·
      rw [hcl] at hext
      have hM₀c : Nat.card ↥M₀ = 960 := card_of_E16_L24 hext
      set α := MulAut.congr e ψ with hα
      have hαk : α ^ (2 ^ k) = 1 := by rw [hα, ← map_pow, hψk, map_one]
      set Y := (M₀.subgroupOf K).map e.toMonoidHom with hY
      have hYc : Nat.card ↥Y = 960 := by
        rw [hY, Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM₀K).toEquiv, hM₀c]
      have hαfix : ∀ y ∈ Y, α y = y := by
        rintro _ ⟨z, hz, rfl⟩
        simp only [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, hψfix z (Subgroup.mem_subgroupOf.mp hz)]
      have hα1 : α = 1 := aut_eq_one_of_pow Y (fun β' hβ'2 hβ'fix =>
        m23_aut_eq_one Y hYc β' hβ'2 hβ'fix) α k hαk hαfix
      have hψ1 : ψ = 1 := (MulAut.congr e).injective (hα1.trans (map_one _).symm)
      rw [hψ1, autCenter_one]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg Subtype.val (L3M.eq_of_autCenter_eq_one hKq.1 ψ hψ1 ⟨x, hx⟩)
  rw [hψ, L3M.coe_conjOn] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

end CFSG.Quasithin.H13.Ch4.I436
