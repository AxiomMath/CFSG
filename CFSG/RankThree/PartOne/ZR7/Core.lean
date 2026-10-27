module

public import CFSG.RankThree.PartOne.ZR7.Cyc

public section

namespace CFSG.RankThree.PartOne.ZR7

variable {G : Type} [Group G]

theorem exists_noncomm_Z [Finite G] {p : ℕ} (hp : p.Prime) {P Q R Z : Subgroup G}
    (hPp : IsPGroup p ↥P) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) {f c n b' : G}
    (hfP : f ∈ P) (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q)
    (hcp : c ^ p = 1) (hRQ : R ≤ Q) (hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hQRZ : ∀ q ∈ Q, ∃ x ∈ R, ∃ z ∈ Z, q = x * z)
    (hRn : ∀ g ∈ P, ∀ x ∈ R, g * x * g⁻¹ ∈ R) [IsCyclic ↥R]
    (hRc : ∃ r ∈ R, c * r ≠ r * c) (hb'R : b' ∈ R) (hb'p : b' ^ p = 1)
    (hb'1 : b' ≠ 1) (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hnb : n * b' * n⁻¹ ∉ Subgroup.zpowers b')
    (hnc : ∀ x ∈ P, c * (n * x * n⁻¹) * c⁻¹ = n * (c * x * c⁻¹) * n⁻¹) :
    ∃ z ∈ Z, c * z ≠ z * c := by
  classical
  by_contra hcon
  push Not at hcon
  have hRP : R ≤ P := hRQ.trans hQP
  obtain ⟨hR'Q, hinf⟩ := conj_le_of_swap hp hPp hQP hQn hfP hPf hcP hcQ hcp hRP hRn
    (fun q hq s hs => hQab q hq s (hRQ hs)) hRc hb'R hb'p hb'1 hnP hnb
  have hR'n := conjSub_normal hnP hRn
  obtain ⟨r, hr, hcr⟩ := hRc
  have hy : n * r * n⁻¹ ∈ conjSub n R := mem_conjSub.2 ⟨r, hr, rfl⟩
  have hcy : c * (n * r * n⁻¹) ≠ (n * r * n⁻¹) * c := by
    intro h
    apply hcr
    have h2 : c * (n * r * n⁻¹) * c⁻¹ = n * r * n⁻¹ := by rw [h]; group
    have h3 : n * (c * r * c⁻¹) * n⁻¹ = n * r * n⁻¹ := (hnc r (hRP hr)).symm.trans h2
    have h4 : c * r * c⁻¹ = r := mul_left_cancel (mul_right_cancel h3)
    calc c * r = (c * r * c⁻¹) * c := by group
      _ = r * c := by rw [h4]
  obtain ⟨x₀, hx₀, z₀, hz₀, hyz⟩ := hQRZ _ (hR'Q hy)
  have hcy' : c * (n * r * n⁻¹) * c⁻¹ * (n * r * n⁻¹)⁻¹ ∈ R := by
    rw [hyz]
    have hz := hcon z₀ hz₀
    have e : c * (x₀ * z₀) * c⁻¹ * (x₀ * z₀)⁻¹ = (c * x₀ * c⁻¹) * x₀⁻¹ := by
      have : c * (x₀ * z₀) * c⁻¹ = (c * x₀ * c⁻¹) * z₀ := by
        calc c * (x₀ * z₀) * c⁻¹ = (c * x₀ * c⁻¹) * (c * z₀ * c⁻¹) := by group
          _ = (c * x₀ * c⁻¹) * z₀ := by rw [hz]; group
      rw [this]
      group
    rw [e]
    exact R.mul_mem (hRn c hcP x₀ hx₀) (R.inv_mem hx₀)
  have hcy'' : c * (n * r * n⁻¹) * c⁻¹ * (n * r * n⁻¹)⁻¹ ∈ conjSub n R :=
    (conjSub n R).mul_mem (hR'n c hcP _ hy) ((conjSub n R).inv_mem hy)
  have hmem : c * (n * r * n⁻¹) * c⁻¹ * (n * r * n⁻¹)⁻¹ ∈ R ⊓ conjSub n R := ⟨hcy', hcy''⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  apply hcy
  calc c * (n * r * n⁻¹)
      = (c * (n * r * n⁻¹) * c⁻¹ * (n * r * n⁻¹)⁻¹) * ((n * r * n⁻¹) * c) := by group
    _ = (n * r * n⁻¹) * c := by rw [hmem, one_mul]

theorem card_Z_eq [Finite G] {p : ℕ} (hp : p.Prime) {P Q R Z : Subgroup G}
    (hPp : IsPGroup p ↥P) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) {f c n₁ n₂ b b' : G}
    (hfP : f ∈ P) (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q)
    (hcp : c ^ p = 1) (hRQ : R ≤ Q) (hZQ : Z ≤ Q) (hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hQRZ : ∀ q ∈ Q, ∃ x ∈ R, ∃ z ∈ Z, q = x * z)
    (hRn : ∀ g ∈ P, ∀ x ∈ R, g * x * g⁻¹ ∈ R) (hZn : ∀ g ∈ P, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z)
    [IsCyclic ↥R] [IsCyclic ↥Z] (hRc : ∃ r ∈ R, c * r ≠ r * c) (hZc : ∃ z ∈ Z, c * z ≠ z * c)
    (hb'R : b' ∈ R) (hb'p : b' ^ p = 1) (hb'1 : b' ≠ 1) (hbZ : b ∈ Z) (hbp : b ^ p = 1)
    (hb1 : b ≠ 1) (hn₁P : n₁ ∈ Subgroup.normalizer (P : Set G))
    (hn₁ : n₁ * b' * n₁⁻¹ ∉ Subgroup.zpowers b') (hn₂P : n₂ ∈ Subgroup.normalizer (P : Set G))
    (hn₂ : n₂ * b * n₂⁻¹ ∉ Subgroup.zpowers b) : Nat.card Z = Nat.card R := by
  classical
  have hRP : R ≤ P := hRQ.trans hQP
  have hZP : Z ≤ P := hZQ.trans hQP
  obtain ⟨h1Q, h1inf⟩ := conj_le_of_swap hp hPp hQP hQn hfP hPf hcP hcQ hcp hRP hRn
    (fun q hq s hs => hQab q hq s (hRQ hs)) hRc hb'R hb'p hb'1 hn₁P hn₁
  have hLB : Nat.card R ≤ Nat.card Z := by
    have := card_le_of_inf_bot hQRZ h1Q h1inf
    rwa [card_conjSub] at this
  obtain ⟨h2Q, h2inf⟩ := conj_le_of_swap hp hPp hQP hQn hfP hPf hcP hcQ hcp hZP hZn
    (fun q hq s hs => hQab q hq s (hZQ hs)) hZc hbZ hbp hb1 hn₂P hn₂
  have hQ' : ∀ q ∈ Q, ∃ z ∈ Z, ∃ x ∈ R, q = z * x := by
    intro q hq
    obtain ⟨x, hx, z, hz, rfl⟩ := hQRZ q hq
    exact ⟨z, hz, x, hx, hQab x (hRQ hx) z (hZQ hz)⟩
  have hUB : Nat.card Z ≤ Nat.card R := by
    have := card_le_of_inf_bot hQ' h2Q h2inf
    rwa [card_conjSub] at this
  exact le_antisymm hUB hLB

theorem card_Z_eq_mul [Finite G] {p : ℕ} (hp : p.Prime) {P Z : Subgroup G}
    (hZn : ∀ g ∈ P, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z) [IsCyclic ↥Z] {c b : G} (hcP : c ∈ P)
    (hbZ : b ∈ Z) (hbp : b ^ p = 1) (hb1 : b ≠ 1)
    (hcomm : ∀ z ∈ Z, (c * z * c⁻¹ * z⁻¹) ^ p = 1) (hZc : ∃ z ∈ Z, c * z ≠ z * c) :
    Nat.card Z = p * Nat.card ↥(Z ⊓ Subgroup.centralizer ({c} : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : CommGroup ↥Z := IsCyclic.commGroup
  let κ : ↥Z →* ↥Z :=
    { toFun := fun z => ⟨c * z * c⁻¹, hZn c hcP z z.2⟩
      map_one' := by ext; simp
      map_mul' := fun z z' => by ext; simp [mul_assoc] }
  let ψ : ↥Z →* ↥Z := MonoidHom.mk' (fun z => κ z * z⁻¹) (fun z z' => by
    simp only [map_mul, mul_inv_rev]
    ac_rfl)
  have hψ : ∀ z : ↥Z, ((ψ z : ↥Z) : G) = c * z * c⁻¹ * (z : G)⁻¹ := fun z => rfl
  have hker : ψ.ker = (Z ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf Z := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : c * z * c⁻¹ * (z : G)⁻¹ = 1 := by rw [← hψ, h]; rfl
      refine ⟨z.2, ?_⟩
      calc (z : G) * c = (c * z * c⁻¹ * (z : G)⁻¹)⁻¹ * (c * z) := by group
        _ = c * z := by rw [h1]; group
    · rintro ⟨-, h⟩
      refine Subtype.ext ?_
      rw [hψ]
      have : (z : G) * c = c * z := h
      have h2 : (z : G) * c⁻¹ = c⁻¹ * z := by
        calc (z : G) * c⁻¹ = c⁻¹ * (c * z) * c⁻¹ := by group
          _ = c⁻¹ * (z * c) * c⁻¹ := by rw [this]
          _ = c⁻¹ * z := by group
      calc c * z * c⁻¹ * (z : G)⁻¹ = c * (z * c⁻¹) * (z : G)⁻¹ := by group
        _ = 1 := by rw [h2]; group
  have hkercard : Nat.card ψ.ker = Nat.card ↥(Z ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
  set bZ : ↥Z := ⟨b, hbZ⟩ with hbZdef
  have hbZo : orderOf bZ = p := by
    rw [← Subgroup.orderOf_coe bZ]
    exact hbo
  have hrange : ψ.range ≤ Subgroup.zpowers bZ := by
    rintro _ ⟨z, rfl⟩
    by_cases h1 : ψ z = 1
    · rw [h1]
      exact one_mem _
    · refine mem_zpowers_of_cyclic hp (R := ↥Z) ?_ ?_ h1 (fun h => hb1 (congrArg Subtype.val h))
      · refine Subtype.ext ?_
        have := hcomm z z.2
        rw [Subgroup.coe_pow, hψ]
        simpa using this
      · exact Subtype.ext (by simpa using hbp)
  have hcardr : Nat.card ψ.range = p := by
    have hd : Nat.card ψ.range ∣ Nat.card (Subgroup.zpowers bZ) := Subgroup.card_dvd_of_le hrange
    rw [Nat.card_zpowers, hbZo] at hd
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exfalso
      obtain ⟨z, hz, hne⟩ := hZc
      have hzr : ψ ⟨z, hz⟩ = 1 := by
        have : ψ.range = ⊥ := Subgroup.card_eq_one.1 h
        exact (Subgroup.mem_bot.1 (this ▸ MonoidHom.mem_range.2 ⟨⟨z, hz⟩, rfl⟩))
      apply hne
      have h1 : c * z * c⁻¹ * z⁻¹ = 1 := by
        have := congrArg Subtype.val hzr
        rw [hψ] at this
        simpa using this
      calc c * z = (c * z * c⁻¹ * z⁻¹) * (z * c) := by group
        _ = z * c := by rw [h1, one_mul]
    · exact h
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hkercard, hcardr] at this
  rw [← this, mul_comm]

end CFSG.RankThree.PartOne.ZR7
