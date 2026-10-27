module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.ModFacts
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Assembly CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

variable {G : Type*} [Group G]

omit [Group G] in
theorem perm3_conj_cube : ∀ a σ : Equiv.Perm (Fin 3), a ≠ 1 → a ^ 3 = 1 →
    σ * a * σ⁻¹ = a ∨ σ * a * σ⁻¹ = a⁻¹ := by decide +kernel

theorem isElemAbelian_mono' {p : ℕ} {A B : Subgroup G} (hAB : A ≤ B) (hB : IsElemAbelian p B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem mem_normalizer_inf' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => Subgroup.mem_inf.mpr ⟨(hA x).mp (Subgroup.mem_inf.mp hx).1,
      (hB x).mp (Subgroup.mem_inf.mp hx).2⟩,
    fun hx => Subgroup.mem_inf.mpr ⟨(hA x).mpr (Subgroup.mem_inf.mp hx).1,
      (hB x).mpr (Subgroup.mem_inf.mp hx).2⟩⟩

theorem mem_normalizer_centralizer' {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (E : Set G), ∀ x ∈ Subgroup.centralizer (E : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro e he
    have he' : g⁻¹ * e * g ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) e).mp he
    have h1 := hx _ he'
    calc e * (g * x * g⁻¹) = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * e := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem inv_mul_mem_of_relIndex_two {A B : Subgroup G} (h2 : A.relIndex B = 2) {x w : G}
    (hx : x ∈ B) (hw : w ∈ B) (hxA : x ∉ A) (hwA : w ∉ A) : x⁻¹ * w ∈ A := by
  have h2' : (A.subgroupOf B).index = 2 := h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2'
  have key : ∀ b : G, ∀ hb : b ∈ B, b ∉ A → b⁻¹ * (a : G) ∈ A := by
    intro b hb hbA
    have hb' : (⟨b⁻¹, B.inv_mem hb⟩ : B) ∉ A.subgroupOf B := fun h =>
      hbA (by simpa using A.inv_mem (Subgroup.mem_subgroupOf.mp h))
    rcases ha ⟨b⁻¹, B.inv_mem hb⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Subgroup.mem_subgroupOf.mp h1
    · exact absurd h1 hb'
  have h1 := key x hx hxA
  have h2 := key w hw hwA
  have e : x⁻¹ * w = (x⁻¹ * (a : G)) * (w⁻¹ * (a : G))⁻¹ := by group
  rw [e]
  exact A.mul_mem h1 (A.inv_mem h2)

theorem exists_unique_fixed_of_card_eight {K Z : Subgroup G} (hK : IsElemAbelian 2 K)
    (hK8 : Nat.card K = 8) (hZK : Z ≤ K) (hZ4 : Nat.card Z = 4) {d : G}
    (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hd3 : d ^ 3 = 1)
    (hdZ : ∀ z ∈ Z, d * z * d⁻¹ = z → z = 1) :
    ∃ k ∈ K, k ≠ 1 ∧ d * k * d⁻¹ = k ∧ ∀ x ∈ K, d * x * d⁻¹ = x → x = 1 ∨ x = k := by
  have hconj : ∀ x ∈ K, d * x * d⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hdK x).mp hx
  have hconji : ∀ x ∈ K, d⁻¹ * x * d⁻¹⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdK) x).mp hx
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup K,
      F = (Subgroup.centralizer ({d} : Set G)).subgroupOf K := ⟨_, rfl⟩
  have hFix : ∀ x : K, conjPermOf hconj hconji x = x ↔ d * (x : G) = (x : G) * d := by
    intro x
    rw [Subtype.ext_iff, conjPermOf_apply_val, mul_inv_eq_iff_eq_mul]
  have hmem : ∀ x : K, x ∈ F ↔ d * (x : G) = (x : G) * d := by
    intro x
    simp [hFdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  have hcardF : Nat.card {x : K // conjPermOf hconj hconji x = x} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hFix, hmem])
  have hmod : Nat.card K ≡ Nat.card {x : K // conjPermOf hconj hconji x = x} [MOD 3] :=
    natCard_fixed_modEq_three _ (conjPermOf_pow_three hconj hconji hd3)
  rw [hK8, hcardF] at hmod
  have hdvd : Nat.card F ∣ 8 := by
    have := Subgroup.card_subgroup_dvd_card F
    rwa [hK8] at this
  have hne8 : Nat.card F ≠ 8 := by
    intro h8
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h8, hK8])
    have hZbot : Z = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hzF : (⟨z, hZK hz⟩ : K) ∈ F := by
        rw [htop]
        exact Subgroup.mem_top _
      have hc : d * z = z * d := (hmem _).mp hzF
      exact hdZ z hz (by rw [hc, mul_inv_cancel_right])
    rw [hZbot] at hZ4
    simp at hZ4
  have hF2 : Nat.card F = 2 := by
    have h3 : Nat.card F % 3 = 2 := by
      unfold Nat.ModEq at hmod
      omega
    have hcle : Nat.card F ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize hc : Nat.card F = c at h3 hdvd hne8 hcle ⊢
    interval_cases c <;> first | rfl | omega
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF2
    exact absurd hF2 (by norm_num)
  obtain ⟨⟨k', hk'F⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have hk'1 : k' ≠ 1 := fun h => hne1 (Subtype.ext h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk'sq : k' ^ 2 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    exact hK.2 _ k'.2)
  have hord : orderOf k' = 2 := orderOf_eq_prime hk'sq hk'1
  have hzp : Subgroup.zpowers k' = F := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk'F) ?_
    simp [hF2, Nat.card_zpowers, hord]
  refine ⟨(k' : G), k'.2, fun h => hk'1 (Subtype.ext (by simpa using h)), ?_, ?_⟩
  · have hk := (hmem k').mp hk'F
    rw [hk, mul_inv_cancel_right]
  · intro x hxK hxd
    have hxF : (⟨x, hxK⟩ : K) ∈ F := by
      rw [hmem]
      rw [mul_inv_eq_iff_eq_mul] at hxd
      exact hxd
    have hmemz : (⟨x, hxK⟩ : K) ∈ Subgroup.zpowers k' := by
      rw [hzp]
      exact hxF
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemz
    have hmod2 : k' ^ (m % (orderOf k' : ℤ)) = ⟨x, hxK⟩ := by
      rw [zpow_mod_orderOf, hm]
    simp only [hord, Nat.cast_ofNat] at hmod2
    have hm2 : m % (2 : ℤ) = 0 ∨ m % (2 : ℤ) = 1 := by omega
    rcases hm2 with h0 | h1
    · rw [h0, zpow_zero] at hmod2
      left
      exact congrArg Subtype.val hmod2.symm
    · rw [h1, zpow_one] at hmod2
      right
      exact congrArg Subtype.val hmod2.symm

end CFSG.Quasithin.Kleidman.F53Hss36
