module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67PairA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

private theorem exists_mul_of_mem_sup {W₁ W₂ : Subgroup G}
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {v : G}
    (hv : v ∈ W₁ ⊔ W₂) : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v := by
  rw [Subgroup.sup_eq_closure] at hv
  refine Subgroup.closure_induction (p := fun v _ => ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v)
    ?_ ?_ ?_ ?_ hv
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, W₂.one_mem, by simp⟩
    · exact ⟨1, W₁.one_mem, x, hx, by simp⟩
  · exact ⟨1, W₁.one_mem, 1, W₂.one_mem, by simp⟩
  · rintro x y hx hy ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨a₁ * b₁, W₁.mul_mem ha₁ hb₁, a₂ * b₂, W₂.mul_mem ha₂ hb₂, by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm b₁ hb₁ a₂ ha₂]
        _ = a₁ * a₂ * (b₁ * b₂) := by group⟩
  · rintro x hx ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    exact ⟨a₁⁻¹, W₁.inv_mem ha₁, a₂⁻¹, W₂.inv_mem ha₂,
      by rw [← mul_inv_rev a₂ a₁, hcomm a₁ ha₁ a₂ ha₂]⟩

private theorem mul_eq_mul_iff {W₁ W₂ : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ W₁) (ha₂ : a₂ ∈ W₂) (hb₁ : b₁ ∈ W₁) (hb₂ : b₂ ∈ W₂) :
    a₁ * a₂ = b₁ * b₂ ↔ a₁ = b₁ ∧ a₂ = b₂ := by
  constructor
  · intro h
    have hmem : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
      calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
        _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [h]
        _ = b₂ * a₂⁻¹ := by group
    have h1 : b₁⁻¹ * a₁ ∈ W₁ := W₁.mul_mem (W₁.inv_mem hb₁) ha₁
    have h2 : b₂ * a₂⁻¹ ∈ W₂ := W₂.mul_mem hb₂ (W₂.inv_mem ha₂)
    have hbot : b₁⁻¹ * a₁ = 1 := by
      have : b₁⁻¹ * a₁ ∈ W₁ ⊓ W₂ := ⟨h1, by rw [hmem]; exact h2⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this
    have ha₁eq : a₁ = b₁ := by
      have h' : b₁ * (b₁⁻¹ * a₁) = b₁ * 1 := congrArg (fun t => b₁ * t) hbot
      calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
        _ = b₁ * 1 := h'
        _ = b₁ := by rw [mul_one]
    have h2' : a₁ * a₂ = a₁ * b₂ := by rw [h, ha₁eq]
    exact ⟨ha₁eq, mul_left_cancel h2'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem isKleinFour_of_card_four_of_sq {W : Subgroup G} (hcard : Nat.card W = 4)
    (hsq : ∀ x ∈ W, x ^ 2 = 1) : IsKleinFour ↥W where
  card_four := hcard
  exponent_two := by
    haveI : Fintype ↥W := Fintype.ofFinite ↥W
    haveI : Nontrivial ↥W := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
      norm_num
    rw [Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)]
    intro x hx
    refine orderOf_eq_prime ?_ hx
    apply Subtype.ext
    simpa using hsq (x : G) x.2

private theorem relIndex_centralizer_le_two_of_kleinFour {W R : Subgroup G}
    (hW : IsKleinFour ↥W) (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hR : IsPGroup 2 ↥R) :
    (Subgroup.centralizer (W : Set G)).relIndex R ≤ 2 := by
  haveI : IsKleinFour ↥W := hW
  let ψ : ↥R →* MulAut ↥W :=
    (Subgroup.normalizerMonoidHom (H := W)).comp (Subgroup.inclusion hRW)
  have hker : ψ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf R := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change Subgroup.normalizerMonoidHom (H := W) (Subgroup.inclusion hRW x) = 1 ↔
      (x : G) ∈ Subgroup.centralizer (W : Set G)
    rw [← MonoidHom.mem_ker (f := Subgroup.normalizerMonoidHom (H := W)),
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hr2 : IsPGroup 2 ↥ψ.range :=
      hR.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hd6 : Nat.card ψ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [CFSG.kleinFour_automorphism_card ↥W] at this
    obtain ⟨n, hn⟩ := hr2.exists_card_eq
    rw [hn] at hd6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h4 : 4 ∣ 2 ^ n := by
        have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        simpa using this
      have := h4.trans hd6
      omega
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact hrange

theorem not_le_normalizer_W (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ¬ conjSubgroup V g ⊓ M ≤ normalizer (W₁ : Set G) := by
  intro hBN
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hB : IsElemAbelian 2 B :=
    (E3.isElemAbelian_conjSubgroup h.elemAbelian g).mono inf_le_left
  have hB2 : IsPGroup 2 ↥B := hB.isPGroup
  have hW₁V : W₁ ≤ V := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂V : W₂ ≤ V := by rw [← h.sup_eq]; exact le_sup_right
  have hne : W₁ ≠ W₂ := by
    intro heq
    have hbot : W₁ = ⊥ := by simpa [heq] using h.inf_eq
    have hcard : Nat.card W₁ = 1 := by rw [hbot]; simp
    have h4 : Nat.card W₁ = 4 := h.card₁
    omega
  have hBN₂ : B ≤ normalizer (W₂ : Set G) := by
    intro b hb
    rcases h.perm b hb.2 with ⟨-, hfix₂⟩ | ⟨hswap₁, -⟩
    · exact conjSubgroup_eq_iff_mem_normalizer.mp hfix₂
    · exfalso
      have hfix₁ : conjSubgroup W₁ b = W₁ :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hBN hb)
      exact hne (hfix₁.symm.trans hswap₁)
  have key : ∀ W : Subgroup G, Nat.card W = 4 → (∀ x ∈ W, x ^ 2 = 1) →
      B ≤ normalizer (W : Set G) → W ≤ conjSubgroup M g := by
    intro W hW4 hWsq hWnorm
    have hKW : IsKleinFour ↥W := isKleinFour_of_card_four_of_sq hW4 hWsq
    set F : Subgroup G := B ⊓ Subgroup.centralizer (W : Set G)
    have hFB : F ≤ B := inf_le_left
    have hrelC : (Subgroup.centralizer (W : Set G)).relIndex B ≤ 2 :=
      relIndex_centralizer_le_two_of_kleinFour hKW hWnorm hB2
    have hrel : F.relIndex B ≤ 2 := by
      change (B ⊓ Subgroup.centralizer (W : Set G)).relIndex B ≤ 2
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact hrelC
    have hFcard : 4 ≤ Nat.card F := by
      have hmul := Subgroup.relIndex_mul_card (H := F) (K := B)
      rw [inf_eq_left.mpr hFB, card_B h hg] at hmul
      have hpos : 0 < F.relIndex B := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' B F)
      nlinarith
    have hFV : F ≤ conjSubgroup V g := hFB.trans inf_le_left
    have hcle := (h.conj g).centralizer_le F hFV hFcard
    intro w hw
    exact hcle (Subgroup.mem_centralizer_iff.mpr (fun f hf =>
      (Subgroup.mem_centralizer_iff.mp hf.2 w hw).symm))
  have h1 : W₁ ≤ conjSubgroup M g :=
    key W₁ h.card₁ (fun x hx => h.elemAbelian.2 x (hW₁V hx)) hBN
  have h2 : W₂ ≤ conjSubgroup M g :=
    key W₂ h.card₂ (fun x hx => h.elemAbelian.2 x (hW₂V hx)) hBN₂
  exact hg.2.1 (h.sup_eq ▸ sup_le h1 h2)

theorem exists_swap (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ∃ s ∈ conjSubgroup V g ⊓ M, conjSubgroup W₁ s = W₂ ∧ conjSubgroup W₂ s = W₁ := by
  by_contra hcon
  apply not_le_normalizer_W h hg
  intro b hb
  rcases h.perm b hb.2 with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact conjSubgroup_eq_iff_mem_normalizer.mp h1
  · exact absurd ⟨b, hb, h1, h2⟩ hcon

theorem relIndex_centralizer_B (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    (centralizer (V : Set G)).relIndex (conjSubgroup V g ⊓ M) = 4 := by
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hB : IsElemAbelian 2 B :=
    (E3.isElemAbelian_conjSubgroup h.elemAbelian g).mono inf_le_left
  have hB2 : IsPGroup 2 ↥B := hB.isPGroup
  have hle4 : (centralizer (V : Set G)).relIndex B ≤ 4 :=
    s1667_relIndex_centralizer_le_four h.elemAbelian h.sup_eq h.inf_eq h.card₁ h.card₂
      hB (fun b hb => h.perm b hb.2)
  have hnotle : ¬ (centralizer (V : Set G)).relIndex B ≤ 2 := by
    intro hle2
    set F : Subgroup G := B ⊓ Subgroup.centralizer (V : Set G)
    have hFB : F ≤ B := inf_le_left
    have hrel : F.relIndex B ≤ 2 := by
      change (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B ≤ 2
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact hle2
    have hFcard : 4 ≤ Nat.card F := by
      have hmul := Subgroup.relIndex_mul_card (H := F) (K := B)
      rw [inf_eq_left.mpr hFB, card_B h hg] at hmul
      have hpos : 0 < F.relIndex B := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' B F)
      nlinarith
    have hFV : F ≤ conjSubgroup V g := hFB.trans inf_le_left
    have hcle := (h.conj g).centralizer_le F hFV hFcard
    have hVle : V ≤ Subgroup.centralizer (F : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.mpr (fun f hf =>
        (Subgroup.mem_centralizer_iff.mp hf.2 v hv).symm)
    exact hg.2.1 (hVle.trans hcle)
  have hidx : (centralizer (V : Set G)).relIndex B =
      (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  have hpow : (centralizer (V : Set G)).relIndex B =
      2 ^ E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hidx, E3.relIndex_eq_two_pow hB2]
  have hk_le : E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 := by
    by_contra hk
    have h3 : 3 ≤ E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) := by
      have := Nat.lt_of_not_le hk; omega
    have h8 : 8 ≤ 2 ^ E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ _ := Nat.pow_le_pow_right (by norm_num) h3
    rw [← hpow] at h8
    omega
  have hk_ge : 2 ≤ E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) := by
    by_contra hk
    have h1 : E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) ≤ 1 := by
      have := Nat.lt_of_not_le hk; omega
    have h2 : 2 ^ E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 := by
      calc 2 ^ _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    rw [← hpow] at h2
    exact hnotle h2
  have hk2 : E3.mQuot B (B ⊓ Subgroup.centralizer (V : Set G)) = 2 :=
    le_antisymm hk_le hk_ge
  rw [hpow, hk2]
  norm_num

theorem card_centralizer_swap (h : Cfg1667 M V W₁ W₂) {s : G} (hs : s * s = 1)
    (hs₁ : conjSubgroup W₁ s = W₂) (hs₂ : conjSubgroup W₂ s = W₁) :
    Nat.card (V ⊓ centralizer ({s} : Set G) : Subgroup G) = 4 := by
  set F : Subgroup G := V ⊓ Subgroup.centralizer ({s} : Set G)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj_id : ∀ x : G, s * (s * x * s⁻¹) * s⁻¹ = x := by
    intro x
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
      _ = x := by rw [hs, hsinv, hs]; simp
  have hW₁V : W₁ ≤ V := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂V : W₂ ≤ V := by rw [← h.sup_eq]; exact le_sup_right
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨a, hW₁V ha⟩ ⟨b, hW₂V hb⟩)
  have hsW₂ : ∀ w ∈ W₁, s * w * s⁻¹ ∈ W₂ := by
    intro w hw
    rw [← hs₁]
    exact mem_conjSubgroup_iff.mpr (by rw [hconj_id w]; exact hw)
  have hsW₁ : ∀ w ∈ W₂, s * w * s⁻¹ ∈ W₁ := by
    intro w hw
    rw [← hs₂]
    exact mem_conjSubgroup_iff.mpr (by rw [hconj_id w]; exact hw)
  let f : ↥W₁ → ↥F := fun w =>
    ⟨w.1 * (s * w.1 * s⁻¹), by
      refine ⟨V.mul_mem (hW₁V w.2) (hW₂V (hsW₂ w.1 w.2)),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hsys : s * (w.1 * (s * w.1 * s⁻¹)) * s⁻¹ = w.1 * (s * w.1 * s⁻¹) := by
        calc s * (w.1 * (s * w.1 * s⁻¹)) * s⁻¹
            = (s * w.1 * s⁻¹) * (s * (s * w.1 * s⁻¹) * s⁻¹) := by group
          _ = (s * w.1 * s⁻¹) * w.1 := by rw [hconj_id w.1]
          _ = w.1 * (s * w.1 * s⁻¹) :=
              Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm
                ⟨s * w.1 * s⁻¹, hW₂V (hsW₂ w.1 w.2)⟩ ⟨w.1, hW₁V w.2⟩)
      exact (mul_inv_eq_iff_eq_mul.mp hsys).symm⟩
  have hfinj : Function.Injective f := by
    intro w₁ w₂ hw
    have hG : (w₁ : G) * (s * w₁ * s⁻¹) = (w₂ : G) * (s * w₂ * s⁻¹) :=
      congrArg Subtype.val hw
    have huniq := (mul_eq_mul_iff h.inf_eq w₁.2 (hsW₂ w₁.1 w₁.2) w₂.2
      (hsW₂ w₂.1 w₂.2)).mp hG
    exact Subtype.ext huniq.1
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨hvV, hvs⟩ := Subgroup.mem_inf.mp v.2
    have hvV' : (v : G) ∈ W₁ ⊔ W₂ := by rw [h.sup_eq]; exact hvV
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁w₂⟩ := exists_mul_of_mem_sup hcomm hvV'
    have hvs' : (v : G) * s = s * (v : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hvs
    have hsv : s * (v : G) * s⁻¹ = (v : G) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hvs'.symm
    have hdecomp : (s * w₂ * s⁻¹) * (s * w₁ * s⁻¹) = (v : G) := by
      calc (s * w₂ * s⁻¹) * (s * w₁ * s⁻¹) = s * (w₂ * w₁) * s⁻¹ := by group
        _ = s * (w₁ * w₂) * s⁻¹ := by rw [← hcomm w₁ hw₁ w₂ hw₂]
        _ = s * (v : G) * s⁻¹ := by rw [hw₁w₂]
        _ = (v : G) := hsv
    have heq : w₁ * w₂ = (s * w₂ * s⁻¹) * (s * w₁ * s⁻¹) :=
      hw₁w₂.trans hdecomp.symm
    have hw₂eq : w₂ = s * w₁ * s⁻¹ :=
      (mul_eq_mul_iff h.inf_eq hw₁ hw₂ (hsW₁ w₂ hw₂) (hsW₂ w₁ hw₁)).mp heq |>.2
    refine ⟨⟨w₁, hw₁⟩, ?_⟩
    apply Subtype.ext
    show w₁ * (s * w₁ * s⁻¹) = (v : G)
    rw [← hw₂eq]
    exact hw₁w₂
  have hbij : Function.Bijective f := ⟨hfinj, hfsurj⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hbij)
  exact hcard.symm.trans h.card₁

theorem exists_not_commute (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ∃ a ∈ V ⊓ conjSubgroup M g, ∃ b ∈ conjSubgroup V g ⊓ M, a * b ≠ b * a := by
  obtain ⟨s, hsB, hs₁, hs₂⟩ := exists_swap h hg
  have hVs : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup h.elemAbelian g
  have hs2 : s * s = 1 := by
    have := hVs.2 s hsB.1
    rwa [pow_two] at this
  have hcard := card_centralizer_swap h hs2 hs₁ hs₂
  by_contra hcon
  have hUle : V ⊓ conjSubgroup M g ≤ V ⊓ centralizer ({s} : Set G) := by
    intro a ha
    refine ⟨ha.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    by_contra hne
    exact hcon ⟨a, ha, s, hsB, hne⟩
  have hle := Subgroup.card_le_of_le hUle
  rw [card_U h hg, hcard] at hle
  omega

theorem card_U_inf_B (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    Nat.card (V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) = 2 := by
  set U : Subgroup G := V ⊓ conjSubgroup M g
  set B : Subgroup G := conjSubgroup V g ⊓ M
  obtain ⟨a, haU, b, hbB, hne⟩ := exists_not_commute h hg
  have hmem : ⁅a, b⁆ ∈ U ⊓ B :=
    commutator_U_B_le h hg (Subgroup.commutator_mem_commutator haU hbB)
  have hne1 : ⁅a, b⁆ ≠ 1 := by
    intro h1
    apply hne
    rw [commutatorElement_def] at h1
    have h2 : a * b * a⁻¹ = b := by
      have := mul_inv_eq_iff_eq_mul.mp h1
      simpa using this
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hnebot : U ⊓ B ≠ ⊥ := by
    intro hbot
    exact hne1 (Subgroup.mem_bot.mp (by rw [← hbot]; exact hmem))
  have hgt : 1 < Nat.card (U ⊓ B : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hnebot)
  have hle : Nat.card (U ⊓ B : Subgroup G) ≤ 2 := card_U_inf_B_le h hg
  omega

theorem exists_eq_zpowers (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ∃ z : G, orderOf z = 2 ∧
      V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z := by
  set U : Subgroup G := V ⊓ conjSubgroup M g
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hcard : Nat.card (U ⊓ B : Subgroup G) = 2 := card_U_inf_B h hg
  haveI hnt : Nontrivial ↥(U ⊓ B) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(U ⊓ B))
  have hzG : ((z : G)) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzV : (z : G) ∈ V := z.2.1.1
  have hz2 : (z : G) ^ 2 = 1 := h.elemAbelian.2 z hzV
  have hzord : orderOf (z : G) = 2 := orderOf_eq_prime hz2 hzG
  refine ⟨(z : G), hzord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2) ?_).symm
  exact le_of_eq (by rw [Nat.card_zpowers, hzord, hcard])

theorem B_inf_centralizer_eq (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    conjSubgroup V g ⊓ M ⊓ centralizer (V : Set G) =
      V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
  set U : Subgroup G := V ⊓ conjSubgroup M g
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hcardCV : Nat.card (B ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = 2 := by
    have hrel : (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B = 4 := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact relIndex_centralizer_B h hg
    have hmul := Subgroup.relIndex_mul_card
      (H := B ⊓ Subgroup.centralizer (V : Set G)) (K := B)
    rw [inf_eq_left.mpr inf_le_left, hrel, card_B h hg] at hmul
    omega
  have hle : U ⊓ B ≤ B ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf inf_le_right ?_
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr (fun v hv =>
      (Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm
        ⟨x, hx.1.1⟩ ⟨v, hv⟩)).symm)
  have heq : U ⊓ B = B ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (by rw [card_U_inf_B h hg, hcardCV]))
  exact heq.symm

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
