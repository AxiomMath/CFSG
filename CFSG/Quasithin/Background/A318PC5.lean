module

public import CFSG.Quasithin.Background.A318PC2

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4

section Centralizer

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

theorem centralizer_le_S (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hP : CFSG.pPrimeCore 3 X = ⊥) {x : X} (hx : orderOf x = 3) {y : GL (Fin 3) K}
    (hxy : IsPGLAt e x y) (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z)
    (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hA : ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x) :
    ∀ c : X, (∀ s ∈ S, c * s = s * c) → c ∈ S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup X := Subgroup.centralizer (S : Set X) with hC
  set Z' : Subgroup X := (Subgroup.center ↥S).map S.subtype with hZ'
  have hCnorm : C.Normal := by
    constructor
    intro c hc g
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by simpa using hSn.conj_mem s hs g⁻¹
    have := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * s := by group
  have hZ'C : Z' ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨s, hs⟩)
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Subgroup.card_map_of_injective S.subtype_injective, hZ]
  have h3 : ∀ c ∈ C, (∃ k : ℕ, orderOf c = 3 ^ k) → c ∈ Z' := by
    intro c hcC ⟨k, hk⟩
    have hcS : c ∈ S := mem_of_mem_sup_of_centralizes hK hq hx hxy hy3 hnon (hA c ⟨k, hk⟩) hcC
    exact ⟨⟨c, hcS⟩, Subgroup.mem_center_iff.2 fun s =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hcC) s s.2), rfl⟩
  set Z'' : Subgroup ↥C := Z'.subgroupOf C with hZ''
  have hZ''card : Nat.card Z'' = 3 := by
    rw [hZ'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'C).toEquiv, hZ'card]
  have hZ''p : IsPGroup 3 Z'' := IsPGroup.of_card (n := 1) (by rw [hZ''card]; norm_num)
  obtain ⟨P, hZP⟩ := hZ''p.exists_le_sylow
  have hPZ : (P : Subgroup ↥C) ≤ Z'' := by
    intro g hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨g, hg⟩
    have hk' : orderOf ((g : ↥C) : X) = 3 ^ k := by
      rw [Subgroup.orderOf_coe]
      have := Subgroup.orderOf_coe (⟨g, hg⟩ : (P : Subgroup ↥C))
      simp only at this
      rw [this, hk]
    exact h3 _ g.2 ⟨k, hk'⟩
  have hPeq : (P : Subgroup ↥C) = Z'' := le_antisymm hPZ hZP
  have hPcard : Nat.card (P : Subgroup ↥C) = 3 := by rw [hPeq, hZ''card]
  have hPc : ∀ (z : ↥C), z ∈ (P : Subgroup ↥C) → ∀ g : ↥C, g * z = z * g := by
    intro z hz g
    rw [hPeq] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hz' : ((z : ↥C) : X) = (w : X) := hwz.symm
    rw [hz']
    exact (Subgroup.mem_centralizer_iff.1 g.2 _ w.2).symm
  have hnorm : Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) ≤ Subgroup.centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hPc z hz g).symm
  set φ := MonoidHom.transferSylow P hnorm with hφ
  have hN3 : ¬ 3 ∣ Nat.card φ.ker := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
  have hker : ∀ c : ↥C, ¬ 3 ∣ orderOf c → c ∈ φ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (φ c) ∣ orderOf c := orderOf_map_dvd φ c
    have h2 : orderOf (φ c) ∣ 3 := by
      have := orderOf_dvd_natCard (φ c)
      rwa [hPcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h1) hc
  have hord_ker : ∀ n : ↥C, n ∈ φ.ker → ¬ 3 ∣ orderOf n := by
    intro n hn hdiv
    apply hN3
    have := orderOf_dvd_natCard (⟨n, hn⟩ : φ.ker)
    rw [← Subgroup.orderOf_coe (⟨n, hn⟩ : φ.ker)] at this
    exact hdiv.trans this
  set K : Subgroup X := φ.ker.map C.subtype with hKdef
  have hKnorm : K.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    have hgn : g * (n : X) * g⁻¹ ∈ C := hCnorm.conj_mem _ n.2 g
    refine ⟨⟨g * (n : X) * g⁻¹, hgn⟩, hker _ ?_, rfl⟩
    have hord : orderOf (⟨g * (n : X) * g⁻¹, hgn⟩ : ↥C) = orderOf n := by
      rw [← Subgroup.orderOf_coe (⟨g * (n : X) * g⁻¹, hgn⟩ : ↥C), ← Subgroup.orderOf_coe n]
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (n : X)
      simpa [MulAut.conj_apply] using this
    rw [hord]
    exact hord_ker n hn
  have hKcop : Nat.Coprime 3 (Nat.card K) := by
    rw [hKdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3
  have hKbot : K = ⊥ := CFSG.pPrimeCore_eq_bot_iff.mp hP K hKnorm hKcop
  have hkerbot : φ.ker = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hKbot
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkerbot
  have hcard : Nat.card ↥C ≤ 3 := by
    rw [← hPcard]
    exact Nat.card_le_card_of_injective φ hinj
  have hPtop : (P : Subgroup ↥C) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card (P : Subgroup ↥C) ≤ Nat.card ↥C := Subgroup.card_le_card_group _
    omega
  intro c hc
  have hcC : c ∈ C := Subgroup.mem_centralizer_iff.2 fun h hh => (hc h hh).symm
  have : (⟨c, hcC⟩ : ↥C) ∈ (P : Subgroup ↥C) := by rw [hPtop]; exact Subgroup.mem_top _
  rw [hPeq] at this
  obtain ⟨w, -, hw⟩ := this
  have hwc : (w : X) = c := hw
  rw [← hwc]
  exact w.2

end Centralizer

end A318P

end CFSG.Quasithin
