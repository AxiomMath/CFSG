module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B4
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B7
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Swap
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

@[expose] def diagLine (j : ℕ) : Subgroup A10 := zpowers (a₁ * a₂ ^ j)

theorem diag_pow (j n : ℕ) : (a₁ * a₂ ^ j) ^ n = a₁ ^ n * a₂ ^ (j * n) := by
  rw [(Commute.pow_right a₁₂_commute j).mul_pow, pow_mul]

theorem diag_pow_five (j : ℕ) : (a₁ * a₂ ^ j) ^ 5 = 1 := by
  rw [diag_pow, a₁_pow, pow_mul', a₂_pow, one_pow, one_mul]

theorem diag_ne_one (j : ℕ) : a₁ * a₂ ^ j ≠ 1 := by
  intro h
  have h1 : a₁ ^ 1 * a₂ ^ j = a₁ ^ 0 * a₂ ^ 0 := by simpa using h
  have := (exp_inj h1).1
  norm_num at this

theorem diag_mem_check (j k n : ℕ) (h : (a₁ * a₂ ^ j) ^ n = a₁ * a₂ ^ k) : j % 5 = k % 5 := by
  rw [diag_pow] at h
  have h1 : a₁ ^ n * a₂ ^ (j * n) = a₁ ^ 1 * a₂ ^ k := by simpa using h
  obtain ⟨hn, hjn⟩ := exp_inj h1
  rw [Nat.mul_mod, hn] at hjn
  simpa using hjn

theorem diag_not_line₁ (j n : ℕ) (hj : j % 5 ≠ 0) : a₁ ^ n ≠ a₁ * a₂ ^ j := by
  intro h
  have h1 : a₁ ^ n * a₂ ^ 0 = a₁ ^ 1 * a₂ ^ j := by simpa using h
  exact hj (exp_inj h1).2.symm

theorem diag_not_line₂ (j n : ℕ) : a₂ ^ n ≠ a₁ * a₂ ^ j := by
  intro h
  have h1 : a₁ ^ 0 * a₂ ^ n = a₁ ^ 1 * a₂ ^ j := by simpa using h
  have := (exp_inj h1).1
  norm_num at this

theorem diagLine_le (j : ℕ) : diagLine j ≤ S₀ := (zpowers_le).2 (mem_S₀.2 ⟨1, j, by simp⟩)

theorem card_diagLine (j : ℕ) : Nat.card (diagLine j) = 5 :=
  card_zpowers_of_pow_eq (diag_pow_five j) (diag_ne_one j)

theorem mem_zpowers_five {x y : A10} (hy : y ^ 5 = 1) :
    x ∈ zpowers y ↔ ∃ n : Fin 5, y ^ (n : ℕ) = x := by
  rw [mem_zpowers_nat]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n % 5, Nat.mod_lt _ (by norm_num)⟩, (pow_eq_pow_mod n hy).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩

theorem line₁_eq : line₁ = zpowers a₁ := by
  rw [← zpowers_a₁_pow (i := 1) (by rw [pow_one]; exact a₁_ne), pow_one]

theorem line₂_eq : line₂ = zpowers a₂ := by
  rw [← zpowers_a₂_pow (j := 1) (by rw [pow_one]; exact a₂_ne), pow_one]

theorem diagLine_ne_line₁ (j : ℕ) (hj : j % 5 ≠ 0) : diagLine j ≠ line₁ := by
  intro h
  have hmem : a₁ * a₂ ^ j ∈ zpowers a₁ := line₁_eq ▸ h ▸ mem_zpowers _
  obtain ⟨n, hn⟩ := (mem_zpowers_five a₁_pow).1 hmem
  exact diag_not_line₁ j n hj hn

theorem diagLine_ne_line₂ (j : ℕ) : diagLine j ≠ line₂ := by
  intro h
  have hmem : a₁ * a₂ ^ j ∈ zpowers a₂ := line₂_eq ▸ h ▸ mem_zpowers _
  obtain ⟨n, hn⟩ := (mem_zpowers_five a₂_pow).1 hmem
  exact diag_not_line₂ j n hn

theorem diagLine_inj {j k : ℕ} (h : diagLine j = diagLine k) : j % 5 = k % 5 := by
  have hmem : a₁ * a₂ ^ k ∈ diagLine j := h ▸ mem_zpowers _
  obtain ⟨n, hn⟩ := (mem_zpowers_five (diag_pow_five j)).1 hmem
  exact diag_mem_check j k n hn

theorem no_invariant_line {ℓ : Subgroup A10} (hℓ : ℓ ≤ S₀) (hℓ5 : Nat.card ℓ = 5)
    (hinv : ∀ n ∈ normalizer (S₀ : Set A10), ℓ.map (MulAut.conj n).toMonoidHom = ℓ) : False := by
  obtain ⟨n, hn, h1, h2⟩ := a10_swap
  by_cases h₁ : ℓ = line₁
  · subst h₁
    exact line₁_ne_line₂ ((hinv n hn).symm.trans h1)
  by_cases h₂ : ℓ = line₂
  · subst h₂
    exact line₁_ne_line₂ (h2.symm.trans (hinv n hn))
  obtain ⟨j, hj0, hjℓ⟩ : ∃ j : ℕ, j % 5 ≠ 0 ∧ diagLine j ≠ ℓ := by
    by_cases hd : diagLine 1 = ℓ
    · exact ⟨2, by decide, fun h => absurd (diagLine_inj (h.trans hd.symm)) (by decide)⟩
    · exact ⟨1, by decide, hd⟩
  obtain ⟨n', hn', hmap⟩ := orbit_diag hℓ (diagLine_le j) hℓ5 (card_diagLine j) h₁ h₂
    (diagLine_ne_line₁ j hj0) (diagLine_ne_line₂ j)
  exact hjℓ (hmap.symm.trans (hinv n' hn'))

namespace Mz614

variable {G : Type} [Group G] [Finite G]

structure A10Setup (m : Mz614 G) where
  ψ : ↥m.L ≃* A10
  mem_iff : ∀ x : ↥m.L, x ∈ (m.A ⊓ m.L).subgroupOf m.L ↔ ψ x ∈ S₀

theorem exists_A10Setup (m : Mz614 G) (h620 : m.C620) (hr : m.r = 5)
    (hL : UC22.IsAlt ↥m.L 10) : Nonempty (A10Setup m) := by
  obtain ⟨e⟩ := hL
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card ((m.A ⊓ m.L).subgroupOf m.L) = 5 ^ (Nat.card ↥m.L).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, m.card_A_inf_L h620,
      hr, Nat.card_congr e.toEquiv, factorization_A10]
  obtain ⟨ψ, hψ⟩ := exists_iso_sylow e (Sylow.ofCard _ hcard)
  exact ⟨⟨ψ, hψ⟩⟩

namespace A10Setup

variable {m : Mz614 G} (D : A10Setup m)

@[expose] noncomputable def ι : A10 →* G := m.L.subtype.comp D.ψ.symm.toMonoidHom

theorem ι_apply (σ : A10) : D.ι σ = ((D.ψ.symm σ : ↥m.L) : G) := rfl

theorem ι_mem_L (σ : A10) : D.ι σ ∈ m.L := (D.ψ.symm σ).2

theorem ι_injective : Function.Injective D.ι :=
  m.L.subtype_injective.comp D.ψ.symm.injective

theorem ι_ψ (x : ↥m.L) : D.ι (D.ψ x) = (x : G) := by
  rw [ι_apply, MulEquiv.symm_apply_apply]

theorem exists_ι {x : G} (hx : x ∈ m.L) : ∃ σ : A10, D.ι σ = x :=
  ⟨D.ψ ⟨x, hx⟩, D.ι_ψ ⟨x, hx⟩⟩

theorem ι_mem_B_iff (σ : A10) : D.ι σ ∈ m.A ⊓ m.L ↔ σ ∈ S₀ := by
  have h := D.mem_iff (D.ψ.symm σ)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

@[expose] noncomputable def img (X : Subgroup G) : Subgroup A10 := (X.subgroupOf m.L).map D.ψ.toMonoidHom

theorem mem_img {X : Subgroup G} {σ : A10} : σ ∈ D.img X ↔ D.ι σ ∈ X := by
  rw [img, Subgroup.mem_map_equiv]
  rfl

theorem img_injective {X Y : Subgroup G} (hX : X ≤ m.L) (hY : Y ≤ m.L) (h : D.img X = D.img Y) :
    X = Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, rfl⟩ := D.exists_ι (hX hx)
    exact D.mem_img.1 (h ▸ D.mem_img.2 hx)
  · intro hx
    obtain ⟨σ, rfl⟩ := D.exists_ι (hY hx)
    exact D.mem_img.1 (h.symm ▸ D.mem_img.2 hx)

theorem img_map_ι (T : Subgroup A10) : D.img (T.map D.ι) = T := by
  ext σ
  rw [D.mem_img]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    exact D.ι_injective hτσ ▸ hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

theorem map_ι_img {X : Subgroup G} (hX : X ≤ m.L) : (D.img X).map D.ι = X := by
  apply D.img_injective (Subgroup.map_le_iff_le_comap.2 fun σ _ => D.ι_mem_L σ) hX
  rw [img_map_ι]

theorem map_ι_le_L (T : Subgroup A10) : T.map D.ι ≤ m.L := by
  rintro _ ⟨σ, -, rfl⟩
  exact D.ι_mem_L σ

theorem card_map_ι (T : Subgroup A10) : Nat.card (T.map D.ι) = Nat.card T :=
  Subgroup.card_map_of_injective D.ι_injective

theorem img_conj (σ : A10) {X : Subgroup G} (hX : X ≤ m.L) :
    D.img (X.map (MulAut.conj (D.ι σ)).toMonoidHom) = (D.img X).map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [D.mem_img]
  constructor
  · rintro ⟨x, hx, hxτ⟩
    obtain ⟨ρ, rfl⟩ := D.exists_ι (hX hx)
    refine ⟨ρ, D.mem_img.2 hx, ?_⟩
    apply D.ι_injective
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] at hxτ ⊢
    exact hxτ
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨D.ι ρ, D.mem_img.1 hρ, ?_⟩
    simp [MulAut.conj_apply]

theorem ι_mem_LW (h620 : m.C620) {σ : A10} (hσ : σ ∈ normalizer (S₀ : Set A10)) :
    D.ι σ ∈ m.L ⊓ m.W := by
  refine ⟨D.ι_mem_L σ, mem_W_of_mem_L h620 (D.ι_mem_L σ) fun b hb => ?_⟩
  obtain ⟨β, rfl⟩ := D.exists_ι hb.2
  have hβ := (D.ι_mem_B_iff β).1 hb
  rw [← map_inv, ← map_mul, ← map_mul, D.ι_mem_B_iff]
  exact (mem_normalizer_iff.1 hσ β).1 hβ

theorem ν₀_conj_B : ∀ b ∈ m.A ⊓ m.L, D.ι ν₀ * b * (D.ι ν₀)⁻¹ = b ^ 2 := by
  intro b hb
  obtain ⟨β, rfl⟩ := D.exists_ι hb.2
  have hβ := (D.ι_mem_B_iff β).1 hb
  rw [← map_inv, ← map_mul, ← map_mul, ν₀_conj hβ, ← map_pow, sq]

include D in
theorem c621 (h620 : m.C620) (hr : m.r = 5) : m.C621 := by
  intro W' hW'B hW'N
  by_contra hcon
  have hcon' : W' ≠ ⊥ ∧ W' ≠ m.A ⊓ m.L := by
    refine ⟨fun h => hcon (Or.inl h), fun h => hcon (Or.inr h)⟩
  have hdvd : Nat.card W' ∣ 5 ^ 2 := by
    rw [← hr, ← m.card_A_inf_L h620]
    exact Subgroup.card_dvd_of_le hW'B
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  interval_cases k
  · exact hcon'.1 (Subgroup.eq_bot_of_card_eq W' (by simpa using hk'))
  · have hW'L : W' ≤ m.L := hW'B.trans inf_le_right
    apply no_invariant_line (ℓ := D.img W')
    · intro σ hσ
      exact (D.ι_mem_B_iff σ).1 (hW'B (D.mem_img.1 hσ))
    · rw [img, Subgroup.card_map_of_injective D.ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'L).toEquiv, hk', pow_one]
    · intro n hn
      rw [← D.img_conj n hW'L]
      congr 1
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.1 (hW'N (D.ι_mem_LW h620 hn)) w).1 hw
      · intro w hw
        refine ⟨(D.ι n)⁻¹ * w * D.ι n, ?_, ?_⟩
        · have := (mem_normalizer_iff.1 (hW'N ((m.L ⊓ m.W).inv_mem (D.ι_mem_LW h620 hn))) w).1 hw
          simpa using this
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
  · exact hcon'.2 (Subgroup.eq_of_le_of_card_ge hW'B (by rw [hk', m.card_A_inf_L h620, hr]))

theorem ne_Z_of_le (h620 : m.C620) {X : Subgroup G} (hX : X ≤ m.A ⊓ m.L) (hX1 : X ≠ ⊥) :
    X ≠ m.Z := by
  intro hXZ
  apply hX1
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ m.Z ⊓ m.L := ⟨hXZ ▸ hx, (hX hx).2⟩
  rwa [inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2] at h1

theorem map_ι_line_le {ℓ : Subgroup A10} (hℓ : ℓ ≤ S₀) : ℓ.map D.ι ≤ m.A ⊓ m.L := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (D.ι_mem_B_iff σ).2 (hℓ hσ)

theorem img_conj_of_mem_N (h620 : m.C620) {Z₂ Z₃ : Subgroup G} (hZ₂L : Z₂ ≤ m.A ⊓ m.L)
    (hZ₃L : Z₃ ≤ m.A ⊓ m.L) (hZ₂1 : Z₂ ≠ ⊥) (hZ₃1 : Z₃ ≠ ⊥) (hZ₂₃ : Z₂ ⊓ Z₃ = ⊥)
    (horb : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Z₂ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₃)
    (h₂ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₂)
    (h₃ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₃)
    {n : A10} (hn : n ∈ normalizer (S₀ : Set A10)) :
    (D.img Z₂).map (MulAut.conj n).toMonoidHom = D.img Z₂ ∨
      (D.img Z₂).map (MulAut.conj n).toMonoidHom = D.img Z₃ := by
  have hZ₂L' : Z₂ ≤ m.L := hZ₂L.trans inf_le_right
  rcases m.map_conj_pair h620 hZ₂L hZ₃L hZ₂1 hZ₃1 hZ₂₃ horb h₂ h₃ (D.ι_mem_LW h620 hn) with
    ⟨h, -⟩ | ⟨h, -⟩
  · left
    rw [← D.img_conj n hZ₂L', h]
  · right
    rw [← D.img_conj n hZ₂L', h]

theorem img_mem_lines (h620 : m.C620) {Z₂ Z₃ : Subgroup G} (hZ₂L : Z₂ ≤ m.A ⊓ m.L)
    (hZ₃L : Z₃ ≤ m.A ⊓ m.L) (hZ₂c : Nat.card Z₂ = 5) (hZ₃c : Nat.card Z₃ = 5)
    (hZ₂₃ : Z₂ ⊓ Z₃ = ⊥)
    (horb : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Z₂ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₃)
    (h₂ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₂)
    (h₃ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₃) :
    D.img Z₂ = line₁ ∨ D.img Z₂ = line₂ := by
  have hne : ∀ X : Subgroup G, Nat.card X = 5 → X ≠ ⊥ := fun X hX h => by
    rw [h, Subgroup.card_bot] at hX
    norm_num at hX
  have hcard : Nat.card (D.img Z₂) = 5 := by
    rw [img, Subgroup.card_map_of_injective D.ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZ₂L.trans inf_le_right)).toEquiv, hZ₂c]
  have hle : D.img Z₂ ≤ S₀ := fun σ hσ => (D.ι_mem_B_iff σ).1 (hZ₂L (D.mem_img.1 hσ))
  by_contra hcon
  have h1 : D.img Z₂ ≠ line₁ := fun h => hcon (Or.inl h)
  have h2 : D.img Z₂ ≠ line₂ := fun h => hcon (Or.inr h)
  have hdiag : ∀ j : ℕ, j % 5 ≠ 0 → diagLine j = D.img Z₂ ∨ diagLine j = D.img Z₃ := by
    intro j hj
    obtain ⟨n, hn, hmap⟩ := orbit_diag hle (diagLine_le j) hcard (card_diagLine j) h1 h2
      (diagLine_ne_line₁ j hj) (diagLine_ne_line₂ j)
    rw [← hmap]
    exact D.img_conj_of_mem_N h620 hZ₂L hZ₃L (hne Z₂ hZ₂c) (hne Z₃ hZ₃c) hZ₂₃ horb h₂ h₃ hn
  have hd1 := hdiag 1 (by decide)
  have hd2 := hdiag 2 (by decide)
  have hd3 := hdiag 3 (by decide)
  have h12 : diagLine 1 ≠ diagLine 2 := fun h => absurd (diagLine_inj h) (by decide)
  have h13 : diagLine 1 ≠ diagLine 3 := fun h => absurd (diagLine_inj h) (by decide)
  have h23 : diagLine 2 ≠ diagLine 3 := fun h => absurd (diagLine_inj h) (by decide)
  rcases hd1 with e1 | e1 <;> rcases hd2 with e2 | e2 <;> rcases hd3 with e3 | e3
  · exact h12 (e1.trans e2.symm)
  · exact h12 (e1.trans e2.symm)
  · exact h13 (e1.trans e3.symm)
  · exact h23 (e2.trans e3.symm)
  · exact h23 (e2.trans e3.symm)
  · exact h13 (e1.trans e3.symm)
  · exact h12 (e1.trans e2.symm)
  · exact h12 (e1.trans e2.symm)

theorem ν₂_lines : line₁.map (MulAut.conj ν₂).toMonoidHom = line₂ ∧
    line₂.map (MulAut.conj ν₂).toMonoidHom = line₁ := by
  constructor
  · rw [line₁_eq, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [ν₂_a₁, pow_zero, one_mul]
    exact zpowers_a₂_pow (by
      intro h
      have h1 : a₁ ^ 0 * a₂ ^ 2 = a₁ ^ 0 * a₂ ^ 0 := by simpa using h
      have := (exp_inj h1).2
      norm_num at this)
  · rw [line₂_eq, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [ν₂_a₂, pow_zero, mul_one, pow_one, line₁_eq]

theorem exists_w (hK : UCK.K322) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) (hne : ¬ m.C623) :
    ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = line₁.map D.ι ∧
      (line₁.map D.ι).map (MulAut.conj w).toMonoidHom = m.Z := by
  have hyLW := D.ι_mem_LW h620 ν₀_mem
  have hs2 : 2 ^ 2 % m.r = m.r - 1 := by rw [hr]; norm_num
  obtain ⟨Z₂, Z₃, hZ₂L, hZ₃L, hZ₂c, hZ₃c, hZ₂₃, horb, h₂, h₃⟩ :=
    m.exists_pair_of_k322 hK h69 h620 (D.c621 h620 hr) hr hyLW D.ν₀_conj_B hs2 hne
  rw [hr] at hZ₂c hZ₃c
  have hne₁ : ∀ X : Subgroup G, Nat.card X = 5 → X ≠ ⊥ := fun X hX h => by
    rw [h, Subgroup.card_bot] at hX
    norm_num at hX
  have hZ₂₃' : Z₂ ≠ Z₃ := by
    intro h
    apply hne₁ Z₂ hZ₂c
    rw [← inf_idem Z₂]
    nth_rewrite 2 [h]
    exact hZ₂₃
  have hZ₃₂ : Z₃ ⊓ Z₂ = ⊥ := by rw [inf_comm]; exact hZ₂₃
  have horb' : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Z₃ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₂ :=
    fun w hw => by
      rcases horb w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have hl₂ := D.img_mem_lines h620 hZ₂L hZ₃L hZ₂c hZ₃c hZ₂₃ horb h₂ h₃
  have hl₃ := D.img_mem_lines h620 hZ₃L hZ₂L hZ₃c hZ₂c hZ₃₂ horb' h₃ h₂
  have himg_ne : D.img Z₂ ≠ D.img Z₃ := fun h =>
    hZ₂₃' (D.img_injective (hZ₂L.trans inf_le_right) (hZ₃L.trans inf_le_right) h)
  set Y₁ := line₁.map D.ι with hY₁
  set Y₂ := line₂.map D.ι with hY₂
  have hY : (Z₂ = Y₁ ∧ Z₃ = Y₂) ∨ (Z₂ = Y₂ ∧ Z₃ = Y₁) := by
    have e₂ := D.map_ι_img (hZ₂L.trans inf_le_right)
    have e₃ := D.map_ι_img (hZ₃L.trans inf_le_right)
    rcases hl₂ with h2 | h2 <;> rcases hl₃ with h3 | h3
    · exact absurd (h2.trans h3.symm) himg_ne
    · left
      exact ⟨by rw [← e₂, h2], by rw [← e₃, h3]⟩
    · right
      exact ⟨by rw [← e₂, h2], by rw [← e₃, h3]⟩
    · exact absurd (h2.trans h3.symm) himg_ne
  have hY₁L : Y₁ ≤ m.A ⊓ m.L := D.map_ι_line_le line₁_le
  have hY₂L : Y₂ ≤ m.A ⊓ m.L := D.map_ι_line_le line₂_le
  have hY₁Z : Y₁ ≠ m.Z := A10Setup.ne_Z_of_le h620 hY₁L
    (fun h => by
      have := D.card_map_ι line₁
      rw [← hY₁, h, Subgroup.card_bot, card_line₁] at this
      norm_num at this)
  have hY₂Z : Y₂ ≠ m.Z := A10Setup.ne_Z_of_le h620 hY₂L
    (fun h => by
      have := D.card_map_ι line₂
      rw [← hY₂, h, Subgroup.card_bot, card_line₂] at this
      norm_num at this)
  have hY₁₂ : Y₁ ≠ Y₂ := fun h => line₁_ne_line₂ (by rw [← D.img_map_ι line₁, ← D.img_map_ι line₂,
    ← hY₁, ← hY₂, h])
  have horbY : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Y₁ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Y₂ := by
    intro w hw
    rcases hY with ⟨e2, e3⟩ | ⟨e2, e3⟩
    · rw [← e2, ← e3]; exact horb w hw
    · rcases horb w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (h.trans e2))
      · exact Or.inr (Or.inl (h.trans e3))
  have hreach : ∀ Y, (Y = Y₁ ∨ Y = Y₂) → ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Y := by
    rintro Y (rfl | rfl)
    · rcases hY with ⟨e2, -⟩ | ⟨-, e3⟩
      · exact e2 ▸ h₂
      · exact e3 ▸ h₃
    · rcases hY with ⟨-, e3⟩ | ⟨e2, -⟩
      · exact e3 ▸ h₃
      · exact e2 ▸ h₂
  set t := D.ι ν₂ with ht
  have htLW : t ∈ m.L ⊓ m.W := D.ι_mem_LW h620 spt_ν₂_mem
  have htY₁ : Y₁.map (MulAut.conj t).toMonoidHom = Y₂ := by
    apply D.img_injective _ (D.map_ι_le_L _)
    · rw [D.img_conj ν₂ (D.map_ι_le_L _), D.img_map_ι, D.img_map_ι, ν₂_lines.1]
    · rintro _ ⟨y, hy, rfl⟩
      exact m.L.mul_mem (m.L.mul_mem htLW.1 (D.map_ι_le_L _ hy)) (m.L.inv_mem htLW.1)
  have htZ : m.Z.map (MulAut.conj t).toMonoidHom = m.Z := m.map_conj_Z_of_mem_L htLW.1
  have horbY' : ∀ w ∈ m.W, ∀ Y, (Y = Y₁ ∨ Y = Y₂) →
      Y.map (MulAut.conj w).toMonoidHom = m.Z ∨ Y.map (MulAut.conj w).toMonoidHom = Y₁ ∨
        Y.map (MulAut.conj w).toMonoidHom = Y₂ := by
    intro w hw Y hY'
    obtain ⟨w', hw', rfl⟩ := hreach Y hY'
    rw [← map_conj_mul_uc6]
    exact horbY _ (m.W.mul_mem hw hw')
  obtain ⟨w₁, hw₁, hw₁Z⟩ := hreach Y₁ (Or.inl rfl)
  have hinj := map_conj_injective_uc6 w₁
  rcases horbY' w₁ hw₁ Y₁ (Or.inl rfl) with h | h | h
  · exact ⟨w₁, hw₁, hw₁Z, h⟩
  · exact absurd (hinj (h.trans hw₁Z.symm)) hY₁Z
  ·
    refine ⟨w₁ * t, m.W.mul_mem hw₁ htLW.2, ?_, ?_⟩
    · rw [map_conj_mul_uc6, htZ, hw₁Z]
    · rw [map_conj_mul_uc6, htY₁]
      rcases horbY' w₁ hw₁ Y₂ (Or.inr rfl) with h' | h' | h'
      · exact h'
      · exact absurd (hinj (h'.trans hw₁Z.symm)) hY₂Z
      · exact absurd (hinj (h'.trans h.symm)) hY₁₂.symm

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
