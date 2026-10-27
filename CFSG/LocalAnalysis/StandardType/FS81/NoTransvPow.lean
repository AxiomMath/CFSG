module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvB2

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem fs81Nt_pRank_le_card (H : Subgroup G) : CFSG.Open.pRank 3 H ≤ Nat.card G := by
  refine csSup_le' fun k ⟨F, _, _, hF⟩ => ?_
  have h1 : 3 ^ k ≤ Nat.card G := hF ▸ Subgroup.card_le_card_group F
  exact (Nat.lt_pow_self (by norm_num)).le.trans h1

theorem fs81Nt_le_pRank {H F : Subgroup G} (hFH : F ≤ H) (hF : IsElemAbelian 3 F) {k : ℕ}
    (hk : Nat.card F = 3 ^ k) : k ≤ CFSG.Open.pRank 3 H := by
  refine le_csSup ⟨Nat.card G, fun k' ⟨F', _, _, hF'⟩ => ?_⟩ ⟨F, hFH, hF, hk⟩
  have h1 : 3 ^ k' ≤ Nat.card G := hF' ▸ Subgroup.card_le_card_group F'
  exact (Nat.lt_pow_self (by norm_num)).le.trans h1

theorem fs81Nt_pRank_le {H : Subgroup G} {m : ℕ}
    (h : ∀ F : Subgroup G, F ≤ H → IsElemAbelian 3 F → Nat.card F ≤ 3 ^ m) :
    CFSG.Open.pRank 3 H ≤ m :=
  csSup_le' fun k ⟨F, hFH, hF, hk⟩ =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk ▸ h F hFH hF)

theorem fs81Nt_le_twoLocalPrimeRank {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) {k : ℕ}
    (hk : k ≤ CFSG.Open.pRank 3 H) : k ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
  le_csSup_of_le ⟨Nat.card G, fun _ ⟨H', _, hH'⟩ => hH' ▸ fs81Nt_pRank_le_card H'⟩ ⟨H, hH, rfl⟩ hk

theorem fs81Nt_twoLocalPrimeRank_le {m : ℕ}
    (h : ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → CFSG.Open.pRank 3 H ≤ m) :
    CFSG.Open.twoLocalPrimeRank 3 G ≤ m :=
  csSup_le' fun _ ⟨H, hH, hk⟩ => hk ▸ h H hH

theorem card_elemAb_le_of_C {b₀ : G} {K : Subgroup G} {n : ℕ} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hK3 : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n)
    {F : Subgroup G} (hFC : F ≤ Subgroup.centralizer ({b₀} : Set G)) (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ (n + 1) := by
  have hb3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hcommC : ∀ a ∈ Subgroup.centralizer ({b₀} : Set G), ∀ b ∈ Subgroup.zpowers b₀,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have : a * b₀ = b₀ * a := (Subgroup.mem_centralizer_iff.mp ha b₀ rfl).symm
    exact ((Commute.zpow_right this i)).eq
  have hF' : IsElemAbelian 3 (F ⊔ Subgroup.zpowers b₀) :=
    IsElemAbelian.sup_of_commute hF (isElemAbelian_zpowers hb3) fun a ha => hcommC a (hFC ha)
  have hb0C : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]
  have hF'C : F ⊔ Subgroup.zpowers b₀ ≤ Subgroup.centralizer ({b₀} : Set G) :=
    sup_le hFC (Subgroup.zpowers_le.mpr hb0C)
  set FK := (F ⊔ Subgroup.zpowers b₀) ⊓ K with hFK
  have hFKel : IsElemAbelian 3 FK := hF'.mono inf_le_left
  have hFKcard : Nat.card FK ≤ 3 ^ n := hK3 FK inf_le_right hFKel
  have hle : F ⊔ Subgroup.zpowers b₀ ≤ FK ⊔ Subgroup.zpowers b₀ := by
    intro x hx
    obtain ⟨k, hk, -, i, hxk⟩ := fs81Fus_exists_mul_zpow hb₀ hKC hKn hKz hOut hA2 (hF'C hx)
      (hF'.2 x hx)
    have hkF : k ∈ F ⊔ Subgroup.zpowers b₀ := by
      have := (F ⊔ Subgroup.zpowers b₀).mul_mem hx
        ((F ⊔ Subgroup.zpowers b₀).zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)) (-i))
      rwa [hxk, zpow_neg, mul_inv_cancel_right] at this
    rw [hxk]
    exact (FK ⊔ Subgroup.zpowers b₀).mul_mem (Subgroup.mem_sup_left ⟨hkF, hk⟩)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers b₀ i))
  have h1 : Nat.card F ≤ Nat.card ↥(F ⊔ Subgroup.zpowers b₀) :=
    Subgroup.card_le_of_le le_sup_left
  have h2 : Nat.card ↥(FK ⊔ Subgroup.zpowers b₀) ≤ Nat.card FK * Nat.card (Subgroup.zpowers b₀) :=
    fs81Fus_card_sup_le fun a ha => hcommC a (hF'C ha.1)
  rw [Nat.card_zpowers, hb₀] at h2
  calc Nat.card F ≤ Nat.card ↥(FK ⊔ Subgroup.zpowers b₀) := h1.trans (Subgroup.card_le_of_le hle)
    _ ≤ Nat.card FK * 3 := h2
    _ ≤ 3 ^ n * 3 := Nat.mul_le_mul_right _ hFKcard
    _ = 3 ^ (n + 1) := (pow_succ 3 n).symm

@[expose] def dsign {n : ℕ} (k₀ k₁ : Fin (n + 1)) : Fin (n + 1) → ZMod 3 :=
  fun k => if k = k₀ ∨ k = k₁ then -1 else 1

namespace TransvP1

variable {b₀ : G} {K E P₁ : Subgroup G}

theorem exists_two_lift_mat (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hM : M * M = 1)
    (hM0 : M *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hd : ∃ d ∈ Subgroup.normalizer (E : Set G), B.Acts d M) :
    ∃ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) ∧
      B.Acts d M ∧ d * b₀ * d⁻¹ = b₀ ∧ (∃ j : ℕ, d ^ 2 ^ j = 1) ∧
        ∀ x ∈ P₁, d ^ 2 * x * (d ^ 2)⁻¹ = x := by
  obtain ⟨d, hdN, hdA⟩ := hd
  obtain ⟨d', hd'N, hd'P, hd'E⟩ := hP.exists_lift h hdN
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hd'A : B.Acts d' M := fun j => by rw [hd'E _ (hbE j)]; exact hdA j
  have hdb : d' * b₀ * d'⁻¹ = b₀ := by
    have hcol : (fun i => M i 0) = Pi.single 0 1 :=
      (Matrix.mulVec_single_one M 0).symm.trans hM0
    have h := hd'A 0
    rw [hcol, B.vec_single, hB.2.1] at h
    exact h
  have hd2E : ∀ y ∈ E, d' ^ 2 * y = y * d' ^ 2 := by
    intro y hy
    obtain ⟨e, rfl⟩ := B.exists_vec_eq (hB.1 ▸ hy)
    have h1 : d' ^ 2 * B.vec e * (d' ^ 2)⁻¹ = B.vec e := by
      rw [show d' ^ 2 * B.vec e * (d' ^ 2)⁻¹ =
          d' * (d' * B.vec e * d'⁻¹) * d'⁻¹ by rw [pow_two]; group,
        B.acts_vec' (by rw [hB.1]; exact hd'N) hd'A,
        B.acts_vec' (by rw [hB.1]; exact hd'N) hd'A,
        Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
    exact mul_inv_eq_iff_eq_mul.mp h1
  obtain ⟨j, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d').ne'
  obtain ⟨r, rfl⟩ := ho
  set d₁ := d' ^ (2 * r + 1) with hd₁
  have hd₁E : ∀ y ∈ E, d₁ * y * d₁⁻¹ = d' * y * d'⁻¹ := by
    intro y hy
    have hc : Commute ((d' ^ 2) ^ r) y := Commute.pow_left (hd2E y hy) r
    rw [hd₁, pow_succ, pow_mul, show (d' ^ 2) ^ r * d' * y * ((d' ^ 2) ^ r * d')⁻¹ =
      (d' ^ 2) ^ r * (d' * y * d'⁻¹) * ((d' ^ 2) ^ r)⁻¹ by group]
    have hc' : Commute ((d' ^ 2) ^ r) (d' * y * d'⁻¹) :=
      Commute.pow_left (hd2E _ ((Subgroup.mem_normalizer_iff.mp hd'N y).mp hy)) r
    rw [hc'.eq, mul_inv_cancel_right]
  have hd₁A : B.Acts d₁ M := fun i => by rw [hd₁E _ (hbE i)]; exact hd'A i
  have hd₁N : d₁ ∈ Subgroup.normalizer (E : Set G) := Subgroup.pow_mem _ hd'N _
  have hd₁P : d₁ ∈ Subgroup.normalizer (P₁ : Set G) := Subgroup.pow_mem _ hd'P _
  have hd₁pow : d₁ ^ 2 ^ j = 1 := by
    rw [hd₁, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  refine ⟨d₁, hd₁N, hd₁P, hd₁A, by rw [hd₁E _ h.b0_mem, hdb], ⟨j, hd₁pow⟩, fun x hx => ?_⟩
  have hc : d₁ ^ 2 ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : d₁ ^ 2 * y * (d₁ ^ 2)⁻¹ = y := by
      rw [show d₁ ^ 2 * y * (d₁ ^ 2)⁻¹ = d₁ * (d₁ * y * d₁⁻¹) * d₁⁻¹ by rw [pow_two]; group,
        hd₁E _ hy, hd₁E _ ((Subgroup.mem_normalizer_iff.mp hd'N y).mp hy),
        show d' * (d' * y * d'⁻¹) * d'⁻¹ = d' ^ 2 * y * (d' ^ 2)⁻¹ by rw [pow_two]; group,
        hd2E y hy, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hco : (orderOf (d₁ ^ 2)).Coprime 3 := by
    have h1 : (d₁ ^ 2) ^ 2 ^ j = 1 := by rw [← pow_mul, mul_comm, pow_mul, hd₁pow, one_pow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
      (Nat.Coprime.pow_left j (by norm_num))
  exact hP.fix_of_coprime h hc (Subgroup.pow_mem _ hd₁P 2) hco hx

theorem exists_two_lift (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {t : Fin (n + 1) → ZMod 3}
    (ht : SignRealized B E t) :
    ∃ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) ∧
      B.Acts d (spMat 1 t) ∧ d * b₀ * d⁻¹ = b₀ ∧ (∃ j : ℕ, d ^ 2 ^ j = 1) ∧
        ∀ x ∈ P₁, d ^ 2 * x * (d ^ 2)⁻¹ = x := by
  obtain ⟨d, hdN, hdP, hdA, hdb, hpow, hd2⟩ :=
    hP.exists_two_lift_mat h B hB (M := spMat (1 : Equiv.Perm (Fin (n + 1))) t)
      (by
        refine spMat_mul_self 1 t (by simp) fun j => ?_
        have hj : t j * t j = 1 := by
          rcases ht.1 j with h | h <;> rw [h] <;> decide
        simpa using hj)
      (by
        rw [spMat_mulVec]
        funext i
        by_cases hi : i = 0
        · subst hi
          have h1 : (Equiv.symm (1 : Equiv.Perm (Fin (n + 1)))) 0 = 0 := rfl
          rw [h1]
          simp [ht.2.1]
        · have h1 : (Equiv.symm (1 : Equiv.Perm (Fin (n + 1)))) i = i := rfl
          rw [h1]
          simp [hi])
      ht.2.2
  exact ⟨d, hdN, hdP, hdA, hdb, hpow, hd2⟩

end TransvP1

namespace TransvP1

variable {b₀ : G} {K E P₁ : Subgroup G}

theorem card_cent_B2_ge_of_fixed (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {B₂ : Subgroup G} (hB₂P : B₂ ≤ P₁)
    (hAB₂ : E ⊓ K ≤ B₂) (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂)
    (hab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} {d : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) (hdP : d ∈ Subgroup.normalizer (P₁ : Set G))
    (hdA : B.Acts d M) (hdb : d * b₀ * d⁻¹ = b₀) (hdB₂ : ∀ x ∈ B₂, d * x * d⁻¹ ∈ B₂)
    (hd2 : ∀ x ∈ P₁, d ^ 2 * x * (d ^ 2)⁻¹ = x)
    {ι : Type} [Fintype ι] (emb : (ι → ZMod 3) →ₗ[ZMod 3] Coords (n + 1))
    (hemb : Function.Injective emb) (hemb0 : ∀ g, emb g 0 = 0)
    (hfix : ∀ g, M *ᵥ emb g = emb g) :
    3 ^ Fintype.card ι * 3 ^ Fintype.card ι ≤
      Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have _ := hdP
  have hcard : Nat.card (ι → ZMod 3) = 3 ^ Fintype.card ι := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  have hvA : ∀ g, B.vec (emb g) ∈ E ⊓ K := fun g =>
    ⟨hB.1 ▸ B.vec_mem_span _, B.vec_mem_of_zero hB.2.2 (hemb0 g)⟩
  have hvfix : ∀ g, d * B.vec (emb g) * d⁻¹ = B.vec (emb g) := fun g => by
    rw [B.acts_vec' (by rw [hB.1]; exact hdN) hdA, hfix]
  set F := B₂ ⊓ Subgroup.centralizer ({d} : Set G) with hF
  have hmemF : ∀ {x : G}, x ∈ B₂ → d * x * d⁻¹ = x → x ∈ F := fun {x} hx hdx =>
    ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact mul_inv_eq_iff_eq_mul.mp hdx⟩
  let f : ↥F →* ↥(E ⊓ K) := (transvBeta b₀ K E).comp
    (Subgroup.inclusion ((inf_le_left.trans hB₂P).trans hP.le))
  have hfx : ∀ x : ↥F, ((f x : ↥(E ⊓ K)) : G) = tb b₀ x := fun x => rfl
  have hker : 3 ^ Fintype.card ι ≤ Nat.card f.ker := by
    rw [← hcard]
    refine Nat.card_le_card_of_injective (fun g => ⟨⟨B.vec (emb g), hmemF (hAB₂ (hvA g))
      (hvfix g)⟩, Subtype.ext (by
        rw [hfx]
        exact tb_eq_one_of_mem_E h (hvA g).1)⟩) fun g g' hgg' =>
      hemb (B.vec_injective ?_)
    have := congrArg (fun z : f.ker => ((z : ↥F) : G)) hgg'
    simpa using this
  have hrange : 3 ^ Fintype.card ι ≤ Nat.card f.range := by
    rw [← hcard]
    have hpre : ∀ g, ∃ x : ↥F, f x = ⟨B.vec (emb g), hvA g⟩ := by
      intro g
      obtain ⟨x₀', hx₀', hx₀b⟩ := hP.surj _ (hvA ((2 : ZMod 3) • g))
      obtain ⟨j, hj⟩ := hcos x₀' hx₀'
      set x₀ := x₀' * b₀ ^ j with hx₀
      have hx₀b' : tb b₀ x₀ = B.vec (emb ((2 : ZMod 3) • g)) := by
        rw [hx₀, tb_mul (hP.le hx₀') (hP.le (hP.E_le (E.zpow_mem h.b0_mem j))),
          tb_eq_one_of_mem_E h (E.zpow_mem h.b0_mem j), mul_one, hx₀b]
      have hdx₀ : d * x₀ * d⁻¹ ∈ B₂ := hdB₂ x₀ hj
      set x := x₀ * (d * x₀ * d⁻¹) with hxdef
      have hxB : x ∈ B₂ := B₂.mul_mem hj hdx₀
      have hdx : d * x * d⁻¹ = x := by
        rw [hxdef, show d * (x₀ * (d * x₀ * d⁻¹)) * d⁻¹ =
          (d * x₀ * d⁻¹) * (d ^ 2 * x₀ * (d ^ 2)⁻¹) by rw [pow_two]; group,
          hd2 x₀ (hB₂P hj), hab _ hdx₀ _ hj]
      refine ⟨⟨x, hmemF hxB hdx⟩, Subtype.ext ?_⟩
      rw [hfx]
      show tb b₀ x = B.vec (emb g)
      rw [hxdef, tb_mul (hP.le (hB₂P hj)) (hP.le (hB₂P hdx₀)), tb_conj hdb, hx₀b',
        B.acts_vec' (by rw [hB.1]; exact hdN) hdA, hfix, ← B.vec_add]
      congr 1
      rw [← map_add, ← add_smul, show (2 : ZMod 3) + 2 = 1 by decide, one_smul]
    choose xg hxg using hpre
    refine Nat.card_le_card_of_injective (fun g => ⟨f (xg g), xg g, rfl⟩) fun g g' hgg' =>
      hemb (B.vec_injective ?_)
    have := congrArg (fun z : f.range => ((z : ↥(E ⊓ K)) : G)) hgg'
    simp only at this
    rw [hxg g, hxg g'] at this
    exact this
  have := Subgroup.card_ker_mul_card_range f
  rw [← this]
  exact Nat.mul_le_mul hker hrange

theorem card_cent_B2_ge (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {B₂ : Subgroup G} (hB₂P : B₂ ≤ P₁)
    (hAB₂ : E ⊓ K ≤ B₂) (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂)
    (hab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hinv : ∀ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) →
      ∀ t : Fin (n + 1) → ZMod 3, t 0 = 1 → B.Acts d (spMat 1 t) → ∀ x ∈ B₂, d * x * d⁻¹ ∈ B₂)
    {k₀ k₁ : Fin (n + 1)} (hk₀ : k₀ ≠ 0) (hk₁ : k₁ ≠ 0) (hk : k₀ ≠ k₁) {d : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) (hdP : d ∈ Subgroup.normalizer (P₁ : Set G))
    (hdA : B.Acts d (spMat 1 (dsign k₀ k₁))) (hd2 : ∀ x ∈ P₁, d ^ 2 * x * (d ^ 2)⁻¹ = x) :
    3 ^ (n - 2) * 3 ^ (n - 2) ≤
      Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have hd0 : dsign k₀ k₁ 0 = 1 := by simp [dsign, Ne.symm hk₀, Ne.symm hk₁]
  set S : Finset (Fin (n + 1)) := Finset.univ \ {0, k₀, k₁} with hSdef
  have hScard : S.card = n - 2 := by
    rw [hSdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simp [Ne.symm hk₀, Ne.symm hk₁]),
      Finset.card_insert_of_notMem (by simp [hk]), Finset.card_singleton]
    omega
  let emb : (↥S → ZMod 3) →ₗ[ZMod 3] Coords (n + 1) :=
    { toFun := fun g k => if hk : k ∈ S then g ⟨k, hk⟩ else 0
      map_add' := by
        intro g g'
        funext k
        by_cases hk : k ∈ S <;> simp [hk]
      map_smul' := by
        intro c g
        funext k
        by_cases hk : k ∈ S <;> simp [hk] }
  have hemb : Function.Injective emb := by
    intro g g' hgg'
    funext x
    have h1 : emb g x.1 = emb g' x.1 := by rw [hgg']
    simpa [emb, x.2] using h1
  have hemb0 : ∀ g, emb g 0 = 0 := fun g => by simp [emb, hSdef]
  have hfix : ∀ g, spMat (1 : Equiv.Perm (Fin (n + 1))) (dsign k₀ k₁) *ᵥ emb g = emb g := by
    intro g
    rw [spMat_mulVec]
    funext i
    rw [show (Equiv.symm (1 : Equiv.Perm (Fin (n + 1)))) i = i from rfl]
    by_cases hi : i ∈ S
    · have hne : ¬ (i = k₀ ∨ i = k₁) := by
        simp only [hSdef, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
          Finset.mem_singleton, true_and] at hi
        tauto
      simp [emb, hi, dsign, hne]
    · simp [emb, hi]
  have hFgen := hP.card_cent_B2_ge_of_fixed h B hB hB₂P hAB₂ hcos hab hdN hdP hdA
    (sign_fix_b0 B hB.2.1 hdA hd0) (hinv d hdN hdP (dsign k₀ k₁) hd0 hdA) hd2
    emb hemb hemb0 hfix
  have hScard' : Fintype.card ↥S = n - 2 := by rw [Fintype.card_coe, hScard]
  simpa [hScard'] using hFgen

theorem le_twoLocalPrimeRank_of_cent_2pow {d : G} {j : ℕ} (hd1 : d ≠ 1)
    (hdj : d ^ 2 ^ j = 1) {F : Subgroup G} (hFc : F ≤ Subgroup.centralizer ({d} : Set G))
    (hFel : IsElemAbelian 3 F) {m : ℕ} (hFcard : Nat.card F = 3 ^ m) :
    m ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  have h2loc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers d : Set G)) := by
    refine ⟨Subgroup.zpowers d, ?_, ?_, rfl⟩
    · intro hbot
      apply hd1
      have : d ∈ Subgroup.zpowers d := Subgroup.mem_zpowers d
      rwa [hbot, Subgroup.mem_bot] at this
    · intro y
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp y.2
      refine ⟨j, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdj, one_zpow]
  have hFN : F ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    intro x hx
    have hxd : Commute x d := (Subgroup.mem_centralizer_iff.mp (hFc hx) d rfl).symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right hxd i).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers d i
    · intro hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : y = x⁻¹ * d ^ i * x := by rw [hi]; group
      rw [this, mul_assoc, ← (Commute.zpow_right hxd i).eq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact Subgroup.zpow_mem_zpowers d i
  exact fs81Nt_le_twoLocalPrimeRank h2loc (fs81Nt_le_pRank hFN hFel hFcard)

theorem not_exp_three (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hKl : KleinSigns B E) (hd3 : DiagSigns3 B E) {k₀ k₁ : Fin (n + 1)} (hk₀ : k₀ ≠ 0)
    (hk₁ : k₁ ≠ 0) (hk : k₀ ≠ k₁) (hds : SignRealized B E (dsign k₀ k₁)) (hn : 6 ≤ n)
    (hrank : CFSG.Open.twoLocalPrimeRank 3 G ≤ n + 1) : ¬ ∀ x ∈ P₁, x ^ 3 = 1 := by
  intro hexp
  obtain ⟨B₂, hB₂P, hAB₂, hB₂E, hcos, hb₀B₂, hinv⟩ := hP.exists_B2 h B hB hsc hKl
  have hab := hP.B2_comm h B hB hsc hd3 hB₂P hB₂E hcos hinv
  obtain ⟨d, hdN, hdP, hdA, hdb, ⟨j, hdj⟩, hd2⟩ := hP.exists_two_lift h B hB hds
  have hF := hP.card_cent_B2_ge h B hB hB₂P hAB₂ hcos hab hinv hk₀ hk₁ hk hdN hdP hdA hd2
  set F := B₂ ⊓ Subgroup.centralizer ({d} : Set G) with hFdef
  have hFel : IsElemAbelian 3 F :=
    ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexp x (hB₂P hx.1)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFel.isPGroup
  have hm' : 2 * n - 4 ≤ m := by
    rw [hm, ← pow_add] at hF
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hF
    omega
  have hd1 : d ≠ 1 := by
    intro hd
    have := B.acts_spMat_one hdA k₀
    rw [hd, one_mul, inv_one, mul_one] at this
    have hv : (dsign k₀ k₁ k₀).val = 2 := by simp [dsign]
    rw [hv] at this
    have h2 : B.b k₀ * 1 = B.b k₀ * B.b k₀ := by rw [mul_one, ← pow_two]; exact this
    have h1 : B.b k₀ = 1 := (mul_left_cancel h2).symm
    have := B.ord k₀
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hFc : F ≤ Subgroup.centralizer ({d} : Set G) := by rw [hFdef]; exact inf_le_right
  have hle := le_twoLocalPrimeRank_of_cent_2pow hd1 hdj hFc hFel hm
  omega

theorem not_exp_three_swap (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hKl : KleinSigns B E) (hd3 : DiagSigns3 B E) (hA9 : 9 ≤ Nat.card ↥(E ⊓ K))
    {k₀ k₁ : Fin (n + 1)} (hk₀ : k₀ ≠ 0) (hk₁ : k₁ ≠ 0) (hk : k₀ ≠ k₁)
    (hsw : ∃ d ∈ Subgroup.normalizer (E : Set G),
      B.Acts d (spMat (Equiv.swap k₀ k₁) fun _ => 1))
    (hn : 4 ≤ n) (hrank : CFSG.Open.twoLocalPrimeRank 3 G ≤ n + 1) :
    ¬ ∀ x ∈ P₁, x ^ 3 = 1 := by
  intro hexp
  obtain ⟨B₂, hB₂P, hAB₂, hB₂E, hcos, hb₀B₂, hinv⟩ := hP.exists_B2 h B hB hsc hKl
  have hab := hP.B2_comm h B hB hsc hd3 hB₂P hB₂E hcos hinv
  have hcomm : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K :=
    fun x hx y hy => hP.comm_mem_A h B hB hsc hx hy
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) :=
    spMat (Equiv.swap k₀ k₁) (fun _ => 1) with hMdef
  have hM : M * M = 1 := by
    rw [hMdef]
    exact spMat_mul_self _ _ (Equiv.swap_mul_self k₀ k₁) (fun j => by simp)
  have hM0 : M *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hMdef, spMat_mulVec]
    funext i
    rw [Equiv.symm_swap]
    by_cases hi : i = 0
    · subst hi
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hk₀) (Ne.symm hk₁)]
      simp
    · have h : (Equiv.swap k₀ k₁) i ≠ 0 := by
        by_cases hik₀ : i = k₀
        · subst hik₀
          rw [Equiv.swap_apply_left]
          exact hk₁
        · by_cases hik₁ : i = k₁
          · subst hik₁
            rw [Equiv.swap_apply_right]
            exact hk₀
          · rw [Equiv.swap_apply_of_ne_of_ne hik₀ hik₁]
            exact hi
      simp [hi, h]
  obtain ⟨d, hdN, hdP, hdA, hdb, ⟨j, hdj⟩, hd2⟩ :=
    hP.exists_two_lift_mat h B hB hM hM0 hsw
  have hdB₂ : ∀ x ∈ B₂, d * x * d⁻¹ ∈ B₂ :=
    hP.B2_normalizer h hcomm hB₂P hAB₂ hB₂E hcos hab hA9 hdP
  set S : Finset (Fin (n + 1)) := Finset.univ \ {0, k₁} with hSdef
  have hScard : S.card = n - 1 := by
    rw [hSdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simp [Ne.symm hk₁]), Finset.card_singleton]
    omega
  have hk₀S : k₀ ∈ S := by simp [hSdef, hk₀, hk]
  let emb : (↥S → ZMod 3) →ₗ[ZMod 3] Coords (n + 1) :=
    { toFun := fun g k =>
        if k = k₁ then g ⟨k₀, hk₀S⟩
        else if hk : k ∈ S then g ⟨k, hk⟩ else 0
      map_add' := by
        intro g g'
        funext k
        by_cases h1 : k = k₁
        · simp [h1]
        · by_cases h2 : k ∈ S <;> simp [h1, h2]
      map_smul' := by
        intro c g
        funext k
        by_cases h1 : k = k₁
        · simp [h1]
        · by_cases h2 : k ∈ S <;> simp [h1, h2] }
  have hemb : Function.Injective emb := by
    intro g g' hgg'
    funext x
    have hx : (x : Fin (n + 1)) ≠ k₁ := by
      intro hk
      have hmem : k₁ ∈ S := by simpa [hk] using x.2
      rw [hSdef, Finset.mem_sdiff] at hmem
      exact hmem.2 (by simp)
    have h1 : emb g x.1 = emb g' x.1 := by rw [hgg']
    simpa [emb, hx, x.2] using h1
  have hemb0 : ∀ g, emb g 0 = 0 := fun g => by
    simp [emb, hSdef, Ne.symm hk₁]
  have hfix : ∀ g, M *ᵥ emb g = emb g := by
    intro g
    rw [hMdef, spMat_mulVec]
    funext i
    rw [Equiv.symm_swap, one_mul]
    by_cases hi0 : i = 0
    · subst hi0
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hk₀) (Ne.symm hk₁)]
    · by_cases hik₀ : i = k₀
      · subst hik₀
        rw [Equiv.swap_apply_left]
        simp [emb, hk, hk₀S]
      · by_cases hik₁ : i = k₁
        · subst hik₁
          rw [Equiv.swap_apply_right]
          simp [emb, hk, hk₀S]
        · rw [Equiv.swap_apply_of_ne_of_ne hik₀ hik₁]
  have hF := hP.card_cent_B2_ge_of_fixed h B hB hB₂P hAB₂ hcos hab hdN hdP hdA hdb hdB₂ hd2
    emb hemb hemb0 hfix
  have hScard' : Fintype.card ↥S = n - 1 := by rw [Fintype.card_coe, hScard]
  rw [hScard'] at hF
  set F := B₂ ⊓ Subgroup.centralizer ({d} : Set G) with hFdef
  have hFel : IsElemAbelian 3 F :=
    ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexp x (hB₂P hx.1)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFel.isPGroup
  have hm' : 2 * (n - 1) ≤ m := by
    rw [hm, ← pow_add] at hF
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hF
    omega
  have hdbk : d * B.b k₀ * d⁻¹ = B.b k₁ := by
    have h := hdA k₀
    have hcol : (fun i => M i k₀) = Pi.single k₁ 1 := by
      funext i
      rw [hMdef, spMat_apply, Equiv.swap_apply_left]
      by_cases hi : i = k₁ <;> simp [hi]
    rw [hcol, B.vec_single] at h
    exact h
  have hd1 : d ≠ 1 := by
    intro hd
    have hb : B.b k₀ = B.b k₁ := by
      rw [hd, one_mul, inv_one, mul_one] at hdbk
      exact hdbk
    have hv : B.vec (Pi.single k₀ (1 : ZMod 3)) = B.vec (Pi.single k₁ 1) := by
      rw [B.vec_single, B.vec_single, hb]
    have hs : Pi.single k₀ (1 : ZMod 3) = Pi.single k₁ 1 := B.vec_injective hv
    have h1 := congrFun hs k₀
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hk] at h1
    exact one_ne_zero h1
  have hFc : F ≤ Subgroup.centralizer ({d} : Set G) := by rw [hFdef]; exact inf_le_right
  have hle := le_twoLocalPrimeRank_of_cent_2pow hd1 hdj hFc hFel hm
  omega

end TransvP1

namespace TransvP1

variable {b₀ : G} {K E P₁ : Subgroup G}

theorem coprime_mu (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1) : μ.Coprime 3 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  rintro ⟨m, rfl⟩
  apply hne
  intro x hx
  rw [hμ x hx, pow_mul, h.elem.2 _ (tb_mem (hP.le hx)).1, one_pow]

theorem mem_E_of_cube_eq_one (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1) {y : G} (hy : y ∈ P₁)
    (hy3 : y ^ 3 = 1) : y ∈ E := by
  refine hP.mem_E h hy ?_
  have h1 : tb b₀ y ^ μ = 1 := by rw [← hμ y hy, hy3]
  have h3 : tb b₀ y ^ 3 = 1 := h.elem.2 _ (tb_mem (hP.le hy)).1
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
    (hP.coprime_mu h hμ hne)) (orderOf_dvd_of_pow_eq_one h3)
  exact orderOf_eq_one_iff.mp this

theorem conj_b0_pow (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1) {y : G} (hy : y ∈ P₁) :
    b₀⁻¹ * y * b₀ = y ^ (1 + 3 * μ) := by
  have hco := hP.coprime_mu h hμ hne
  have h3 : tb b₀ y ^ 3 = 1 := h.elem.2 _ (tb_mem (hP.le hy)).1
  have hμ2 : tb b₀ y ^ (μ * μ) = tb b₀ y := by
    have hmod : μ * μ % 3 = 1 := by
      have : μ % 3 = 1 ∨ μ % 3 = 2 := by
        have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.coprime_comm.mp hco)
        omega
      rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
    rw [← Nat.mod_add_div (μ * μ) 3, pow_add, pow_mul, h3, one_pow, mul_one, hmod, pow_one]
  have htb : tb b₀ y = y ^ (3 * μ) := by
    rw [pow_mul, hμ y hy, ← pow_mul, hμ2]
  calc b₀⁻¹ * y * b₀ = tb b₀ y * y := by simp only [tb]; group
    _ = y ^ (3 * μ) * y := by rw [htb]
    _ = y ^ (1 + 3 * μ) := by rw [add_comm, pow_succ]

theorem not_conj_b0_inv (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1)
    (hA1 : ∃ a ∈ E ⊓ K, a ≠ 1) {m : G} (hmP : m ∈ Subgroup.normalizer (P₁ : Set G)) {a : G}
    (ha : a ∈ E ⊓ K) : m * b₀ * m⁻¹ ≠ b₀⁻¹ * a := by
  intro hm
  have hb3 : b₀ ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b₀
  have key : ∀ y ∈ P₁, b₀ * y * b₀⁻¹ = b₀⁻¹ * y * b₀ := by
    intro y hy
    have hy' : m⁻¹ * y * m ∈ P₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmP) y).mp hy
      rwa [inv_inv] at this
    have h1 := hP.conj_b0_pow h hμ hne hy'
    have h2 : m * (b₀⁻¹ * (m⁻¹ * y * m) * b₀) * m⁻¹ = y ^ (1 + 3 * μ) := by
      rw [h1, show m * (m⁻¹ * y * m) ^ (1 + 3 * μ) * m⁻¹ = (m * (m⁻¹ * y * m) * m⁻¹) ^ (1 + 3 * μ)
        from (conj_pow).symm]
      congr 1
      group
    have h3 : m * b₀⁻¹ * m⁻¹ = a⁻¹ * b₀ := by
      rw [show m * b₀⁻¹ * m⁻¹ = (m * b₀ * m⁻¹)⁻¹ by group, hm]
      group
    have h4 : m * (b₀⁻¹ * (m⁻¹ * y * m) * b₀) * m⁻¹ = a⁻¹ * (b₀ * y * b₀⁻¹) * a := by
      rw [show m * (b₀⁻¹ * (m⁻¹ * y * m) * b₀) * m⁻¹ =
        (m * b₀⁻¹ * m⁻¹) * y * (m * b₀⁻¹ * m⁻¹)⁻¹ by group, h3]
      group
    have hbyb : b₀ * y * b₀⁻¹ ∈ P₁ := P₁.mul_mem (P₁.mul_mem (hP.E_le h.b0_mem) hy)
      (P₁.inv_mem (hP.E_le h.b0_mem))
    have h5 : a⁻¹ * (b₀ * y * b₀⁻¹) * a = b₀ * y * b₀⁻¹ := by
      have hc : (b₀ * y * b₀⁻¹) * a * (b₀ * y * b₀⁻¹)⁻¹ = a := (hP.le hbyb).2.1 a ha
      calc a⁻¹ * (b₀ * y * b₀⁻¹) * a
          = a⁻¹ * ((b₀ * y * b₀⁻¹) * a * (b₀ * y * b₀⁻¹)⁻¹) * (b₀ * y * b₀⁻¹) := by group
        _ = b₀ * y * b₀⁻¹ := by rw [hc]; group
    rw [← h5, ← h4, h2, hP.conj_b0_pow h hμ hne hy]
  obtain ⟨a₁, ha₁, ha₁1⟩ := hA1
  obtain ⟨x, hx, hxa⟩ := hP.surj a₁ ha₁
  apply ha₁1
  rw [← hxa]
  have h1 := key x hx
  have hbinv : b₀⁻¹ = b₀ ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hb3]
  have h2 : b₀⁻¹ * x * b₀ = x := by
    have : b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹ = b₀ * (b₀⁻¹ * x * b₀) * b₀⁻¹ := by rw [h1]
    rw [show b₀ * (b₀⁻¹ * x * b₀) * b₀⁻¹ = x by group,
      show b₀ * (b₀ * x * b₀⁻¹) * b₀⁻¹ = b₀ ^ 2 * x * (b₀ ^ 2)⁻¹ by rw [pow_two]; group,
      ← hbinv, inv_inv] at this
    exact this
  simp only [tb]
  rw [show x * b₀ * x⁻¹ = b₀ by
    calc x * b₀ * x⁻¹ = b₀ * (b₀⁻¹ * x * b₀) * x⁻¹ := by group
      _ = b₀ := by rw [h2]; group, inv_mul_cancel]

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
