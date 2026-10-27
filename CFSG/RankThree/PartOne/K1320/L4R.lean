module

public import CFSG.RankThree.PartOne.K1320.L4Frame
public import CFSG.RankThree.PartOne.K1320.L4Cls
public import CFSG.RankThree.PartOne.K1320.L4Torus

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)

variable {G : Type} [Group G] [Finite G]

theorem R_le_kZero {p f r : ℕ} {E : Subgroup G} {R : Subgroup G} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrf : r ∣ 2 ^ f - 1) (hRcard : Nat.card R = r) {s₁ s₂ t : MulAut E} (hKs₁ : KFAt p E f s₁)
    (hKs₂ : KFAt p E f s₂) (hKt : KFAt p E (2 * f) t)
    (hc1 : kZero p E t ≤ Subgroup.centralizer (kZero p E s₁ : Set G))
    (hc2 : kZero p E t ≤ Subgroup.centralizer (kZero p E s₂ : Set G))
    (hc12 : kZero p E s₁ ≤ Subgroup.centralizer (kZero p E s₂ : Set G))
    (hRE : ∀ x ∈ R, ∀ e ∈ E, x * e = e * x)
    (hR1 : R ≤ Subgroup.centralizer (kZero p E s₁ : Set G))
    (hR2 : R ≤ Subgroup.centralizer (kZero p E s₂ : Set G))
    (he : CFSG.twoLocalOddRank G = 3) : R ≤ kZero p E t := by
  by_contra hnot
  have hRK : R ⊓ kZero p E t = ⊥ := by
    have hd : Nat.card ↥(R ⊓ kZero p E t) ∣ r := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hr).1 hd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hnot
      have : R ⊓ kZero p E t = R :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hRcard])
      rw [← this]
      exact inf_le_right
  have hRN : R ≤ Subgroup.normalizer (kZero p E t : Set G) := fun x hx =>
    mem_normalizer_kZero t (hRE x hx)
  have hrg : r ∣ 2 ^ (2 * f) - 1 := by
    have : 2 ^ f - 1 ∣ 2 ^ (2 * f) - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
      rwa [one_pow, ← pow_mul, mul_comm] at this
    exact hrf.trans this
  have h4 := four_le_localRank_of_blocks hr hr2 hKt.2.1 hKs₁.2.1 hKs₂.2.1 hrg hrf hrf hc1 hc2 hc12
    hRcard hRN hRK hR1 hR2
  exact false_of_four_le_localRank hr hr2 h4 he

omit [Finite G] in
theorem pElementSubgroup_le_pElementSubgroup {p : ℕ} (X₀ X : Subgroup G)
    (h : pElementSubgroup p X₀ ≤ X) : pElementSubgroup p X₀ ≤ pElementSubgroup p X := by
  unfold pElementSubgroup at *
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure ⟨h (Subgroup.subset_closure hx), hx.2⟩

omit [Finite G] in
theorem kZero_le_pElementSubgroup {p : ℕ} {E : Subgroup G} (t : MulAut E) {X : Subgroup G}
    (h : kZero p E t ≤ X) : kZero p E t ≤ pElementSubgroup p X :=
  pElementSubgroup_le_pElementSubgroup _ X h

namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (fr : Row8Frame p A L E f K)

theorem R_normal {c : G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) (hEA : E = A)
    (B : Bridge p E) (hcard : Nat.card E = p ^ 3) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K - 1)
    (hM7 : ∀ g : ↥(M8 K), g ∈ (blk8M (K := K)).range →
      g ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K)) → g ^ r = 1 → g ∈ Rr K r)
    {zs : MulAut E} (hzs : zs ∈ reflectionSet p E)
    (hzsc : ∀ g ∈ torusImage E L, g * zs = zs * g) (hzsL : zs ∉ torusImage E L)
    (hzsconj : ∃ g ∈ reflectionGroup p E, g * fr.r₁ * g⁻¹ = zs)
    (hRzs : pullG fr.ε ((Rr K r).map (q8 K)) ≤ kZero p E zs) :
    ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
      conjAut E y hy ∈ reflectionGroup p E →
        conjBy y (pullG fr.ε ((Rr K r).map (q8 K))) = pullG fr.ε ((Rr K r).map (q8 K)) := by
  intro y hy hyX
  set R := pullG fr.ε ((Rr K r).map (q8 K)) with hR
  have hRcard : Nat.card R = r := by
    rw [hR, fr.card_R hZ (Rr K r)]
    exact rootsOfUnity_card hr hrq
  obtain ⟨hRL, hR0, hR0', hRE⟩ := fr.R_data h hF hF13 hZ hEA (Rm := Rr K r)
    (by rintro _ ⟨ζ, -, rfl⟩; exact ⟨ζ, rfl⟩)
  have hy' : y⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer (E : Set G)).inv_mem hy
  have hRle : Rr K r ≤ (blk8M (K := K)).range := by
    rintro _ ⟨ζ, -, rfl⟩
    exact Tl_mem_range_blk8M ζ
  have hR1 : R ≤ kZero p E fr.r₁ := by
    rw [fr.kz₁ h hF13 hZ]
    exact pullG_mono _ (Subgroup.map_mono hRle)
  obtain ⟨k, hk, hkK, hkr⟩ := fr.kf₀.2.2.2.2
  have hconjk : conjAut E k hk = fr.r₀ := hkr
  have hR1' : R ≤ kZero p E (fr.r₀ * fr.r₁ * fr.r₀⁻¹) := by
    have h1 := kZero_conj p fr.r₁ hk
    rw [hconjk] at h1
    rw [h1]
    intro x hx
    rw [Equivariance.mem_conjBy]
    have hkx : k⁻¹ * x * k = x := by
      have := Subgroup.mem_centralizer_iff.1 (hR0 hx) k⁻¹ ((kZero p E fr.r₀).inv_mem hkK)
      calc k⁻¹ * x * k = x * k⁻¹ * k := by rw [this]
        _ = x := by group
    rw [hkx]
    exact hR1 hx
  have hzsr₀ : zs ≠ fr.r₀ := fun h1 => hzsL (h1 ▸ fr.mem₀L)
  have hzsr₁ : zs ≠ fr.r₁ := fun h1 => hzsL (h1 ▸ fr.mem₁L)
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  have hzs1 : zs ≠ fr.r₀ * fr.r₁ * fr.r₀⁻¹ := fun h1 =>
    hzsL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀))
  have hzs2 : zs ≠ fr.r₁ * fr.r₀ * fr.r₁⁻¹ := fun h1 =>
    hzsL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁))
  have hcl := B.vclass h hcard fr.mem₀ fr.mem₁ hzs fr.ord₀₁ (hzsc _ hL₀) (hzsc _ hL₁)
    hzsr₀ hzsr₁ hzs1 hzs2 hzsconj
  have hgX : conjAut E y⁻¹ hy' ∈ reflectionGroup p E := by
    rw [Equivariance.conjAut_inv hy]
    exact (reflectionGroup p E).inv_mem hyX
  have hRw : R ≤ kZero p E (conjAut E y⁻¹ hy' * fr.r₁ * (conjAut E y⁻¹ hy')⁻¹) := by
    rcases hcl _ hgX with h1 | h1 | h1
    · rw [h1]; exact hR1
    · rw [h1]; exact hR1'
    · rw [h1]; exact hRzs
  rw [kZero_conj p fr.r₁ hy'] at hRw
  have hRy : conjBy y R ≤ kZero p E fr.r₁ := by
    have := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hRw
    rwa [show Subgroup.map (MulAut.conj y).toMonoidHom (conjBy y⁻¹ (kZero p E fr.r₁)) =
      conjBy y (conjBy y⁻¹ (kZero p E fr.r₁)) from rfl, Equivariance.conjBy_conjBy_inv] at this
  have hle : conjBy y R ≤ R := by
    intro x hx
    have hxK : x ∈ kZero p E fr.r₁ := hRy hx
    rw [fr.kz₁ h hF13 hZ] at hxK
    obtain ⟨hxL, hxQ⟩ := mem_pullG.1 hxK
    obtain ⟨g₁, hg₁, hg₁x⟩ := hxQ
    have hρ := Equivariance.mem_conjBy.1 hx
    have hxE : ∀ e ∈ E, x * e = e * x := by
      intro e he
      have hye : y⁻¹ * e * y ∈ E := by simpa using (Subgroup.mem_normalizer_iff.1 hy' e).1 he
      have hρe := hRE _ hρ (y⁻¹ * e * y) hye
      calc x * e = y * ((y⁻¹ * x * y) * (y⁻¹ * e * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * e * y) * (y⁻¹ * x * y)) * y⁻¹ := by rw [hρe]
        _ = e * x := by group
    have hxr : x ^ r = 1 := by
      have hρr : (y⁻¹ * x * y) ^ r = 1 := by
        have hd : orderOf (y⁻¹ * x * y) ∣ r := hRcard ▸ Subgroup.orderOf_dvd_natCard R hρ
        exact orderOf_dvd_iff_pow_eq_one.1 hd
      have h2 : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      rw [h2, conj_pow, hρr]
      group
    have hg₁c : g₁ ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hb1 : q8 K t ∈ (T8 p K).map (q8 K) := Subgroup.mem_map_of_mem _ ht
      rw [← fr.hAT] at hb1
      obtain ⟨b, hb, hbt⟩ := Subgroup.mem_map.1 hb1
      have hbE : (b : G) ∈ E := by
        rw [hEA]
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hb)).1
      have hcomm : fr.ε b * fr.ε ⟨x, hxL⟩ = fr.ε ⟨x, hxL⟩ * fr.ε b := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (hxE _ hbE).symm
      rw [hbt, ← hg₁x] at hcomm
      exact q8_inj (K := K) (by rw [map_mul, map_mul]; exact hcomm)
    have hg₁r : g₁ ^ r = 1 := by
      have h1 : q8 K (g₁ ^ r) = 1 := by
        rw [map_pow, hg₁x, ← map_pow]
        have : (⟨x, hxL⟩ : ↥L) ^ r = 1 := Subtype.ext hxr
        rw [this, map_one]
      exact q8_inj (K := K) (h1.trans (map_one _).symm)
    have hg₁R := hM7 g₁ hg₁ hg₁c hg₁r
    exact mem_pullG.2 ⟨hxL, hg₁x ▸ Subgroup.mem_map_of_mem _ hg₁R⟩
  have hcardeq : Nat.card (conjBy y R) = Nat.card R := by
    rw [conjBy, Subgroup.card_map_of_injective (MulAut.conj y).injective]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardeq]))

end Row8Frame

end CFSG.RankThree.PartOne.K1320
