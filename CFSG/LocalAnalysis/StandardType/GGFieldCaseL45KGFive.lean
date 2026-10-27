module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGThompson
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneFiveRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem ggL45_mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ n ∈ H, g * n * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨h m, fun hm => ?_⟩
  let f : H → H := fun n => ⟨g * n * g⁻¹, h n n.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  obtain ⟨n, hn⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hm⟩
  have h1 : g * n * g⁻¹ = g * m * g⁻¹ := congrArg Subtype.val hn
  have h2 : (n : G) = m := by simpa using h1
  exact h2 ▸ n.2

theorem ggL45_pow_gcd_mem {M : Subgroup G} {a : G} {r n : ℕ} (hr : a ^ r ∈ M) (hn : a ^ n ∈ M) :
    a ^ Nat.gcd r n ∈ M := by
  have e := Nat.gcd_eq_gcd_ab r n
  have h : a ^ ((Nat.gcd r n : ℕ) : ℤ) = (a ^ r) ^ (Nat.gcdA r n) * (a ^ n) ^ (Nat.gcdB r n) := by
    rw [e, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [zpow_natCast] at h
  rw [h]
  exact M.mul_mem (M.zpow_mem hr _) (M.zpow_mem hn _)

theorem pow_pow_mem_of_pow_mem {M : Subgroup G} {p : ℕ} (hp : p.Prime) {a : G} {N j r : ℕ}
    (hN : a ^ p ^ N ∈ M) (hr0 : 0 < r) (hr : r < p ^ (j + 1)) (har : a ^ r ∈ M) :
    a ^ p ^ j ∈ M := by
  have hg := ggL45_pow_gcd_mem har hN
  obtain ⟨v, -, hgv⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right r (p ^ N))
  have hvr : p ^ v ≤ r := by rw [← hgv]; exact Nat.le_of_dvd hr0 (Nat.gcd_dvd_left _ _)
  have hvj : v ≤ j := by
    by_contra hc
    have : p ^ (j + 1) ≤ p ^ v := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  rw [hgv] at hg
  have e : a ^ p ^ j = (a ^ p ^ v) ^ p ^ (j - v) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hvj]
  rw [e]
  exact M.pow_mem hg _

theorem card_inf_mul_pow_le [Finite G] {A M : Subgroup G} {p : ℕ} (hp : p.Prime) {a : G}
    (haA : a ∈ A) {N j : ℕ} (hN : a ^ p ^ N ∈ M) (hj : a ^ p ^ j ∉ M) :
    Nat.card (A ⊓ M : Subgroup G) * p ^ (j + 1) ≤ Nat.card A := by
  let f : Fin (p ^ (j + 1)) × (A ⊓ M : Subgroup G) → A := fun im =>
    ⟨a ^ (im.1 : ℕ) * im.2, A.mul_mem (A.pow_mem haA _) im.2.2.1⟩
  have aux : ∀ (i i' : ℕ) (m m' : G), m ∈ M → m' ∈ M → i < i' → i' < p ^ (j + 1) →
      a ^ i * m = a ^ i' * m' → False := by
    intro i i' m m' hm hm' hii hi' he
    have e : a ^ (i' - i) = m * m'⁻¹ := by
      have h1 : a ^ i' = a ^ i * a ^ (i' - i) := by rw [← pow_add, Nat.add_sub_cancel' hii.le]
      rw [h1, mul_assoc] at he
      have h2 := mul_left_cancel he
      rw [h2]
      group
    refine hj (pow_pow_mem_of_pow_mem (r := i' - i) hp hN (by omega) (by omega) ?_)
    rw [e]
    exact M.mul_mem hm (M.inv_mem hm')
  have hf : Function.Injective f := by
    rintro ⟨i, m⟩ ⟨i', m'⟩ h
    have h' : a ^ (i : ℕ) * m = a ^ (i' : ℕ) * m' := congrArg Subtype.val h
    have hii : (i : ℕ) = i' := by
      rcases lt_trichotomy (i : ℕ) i' with hlt | heq | hgt
      · exact (aux _ _ _ _ m.2.2 m'.2.2 hlt i'.2 h').elim
      · exact heq
      · exact (aux _ _ _ _ m'.2.2 m.2.2 hgt i.2 h'.symm).elim
    have hi : i = i' := Fin.ext hii
    subst hi
    have : (m : G) = m' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext this)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fin, mul_comm] at this

theorem ggL45_exists_telescope {H N : Subgroup G} (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {w h : G}
    (hwH : ∀ t ∈ H, w⁻¹ * t * w ∈ H) (hwN : w ∈ N)
    (hhN : h ∈ Subgroup.normalizer (N : Set G)) (hh : h ∈ H) :
    ∀ n : ℕ, ∃ y ∈ H, (h ^ n)⁻¹ * y ∈ N ∧
      y⁻¹ * (w⁻¹ * y * w) = h⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) := by
  have hc : ∀ n : ℕ, (w ^ n)⁻¹ * h * w ^ n ∈ H := by
    intro n
    induction n with
    | zero => simpa using hh
    | succ n ih =>
      have := hwH _ ih
      rw [pow_succ]
      simpa [mul_assoc] using this
  intro n
  induction n with
  | zero => exact ⟨1, H.one_mem, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyN, hyt⟩ := ih
    refine ⟨y * ((w ^ n)⁻¹ * h * w ^ n), H.mul_mem hy (hc n), ?_, ?_⟩
    · have hcN : h⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) ∈ N := by
        have h1 : h⁻¹ * (w ^ n)⁻¹ * h⁻¹⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) ((w ^ n)⁻¹)).mp
            (N.inv_mem (N.pow_mem hwN n))
        have := N.mul_mem h1 (N.pow_mem hwN n)
        simpa [mul_assoc] using this
      have hyh : h⁻¹ * y = y * h⁻¹ := hab _ (H.inv_mem hh) _ hy
      have hhh : h⁻¹ * (h ^ n)⁻¹ = (h ^ n)⁻¹ * h⁻¹ := (Commute.self_pow h n).inv_inv.eq
      have e : (h ^ (n + 1))⁻¹ * (y * ((w ^ n)⁻¹ * h * w ^ n)) =
          ((h ^ n)⁻¹ * y) * (h⁻¹ * ((w ^ n)⁻¹ * h * w ^ n)) := by
        rw [pow_succ, mul_inv_rev, hhh]
        calc (h ^ n)⁻¹ * h⁻¹ * (y * ((w ^ n)⁻¹ * h * w ^ n))
            = (h ^ n)⁻¹ * (h⁻¹ * y) * ((w ^ n)⁻¹ * h * w ^ n) := by group
          _ = (h ^ n)⁻¹ * (y * h⁻¹) * ((w ^ n)⁻¹ * h * w ^ n) := by rw [hyh]
          _ = _ := by group
      rw [e]
      exact N.mul_mem hyN hcN
    · have hch : ((w ^ n)⁻¹ * h * w ^ n) * h⁻¹ = h⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) :=
        hab _ (hc n) _ (H.inv_mem hh)
      calc (y * ((w ^ n)⁻¹ * h * w ^ n))⁻¹ * (w⁻¹ * (y * ((w ^ n)⁻¹ * h * w ^ n)) * w)
          = ((w ^ n)⁻¹ * h * w ^ n)⁻¹ * (y⁻¹ * (w⁻¹ * y * w)) *
              (w⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) * w) := by group
        _ = ((w ^ n)⁻¹ * h * w ^ n)⁻¹ * (h⁻¹ * ((w ^ n)⁻¹ * h * w ^ n)) *
              (w⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) * w) := by rw [hyt]
        _ = ((w ^ n)⁻¹ * h * w ^ n)⁻¹ * (((w ^ n)⁻¹ * h * w ^ n) * h⁻¹) *
              (w⁻¹ * ((w ^ n)⁻¹ * h * w ^ n) * w) := by rw [hch]
        _ = h⁻¹ * ((w ^ (n + 1))⁻¹ * h * w ^ (n + 1)) := by rw [pow_succ]; group

theorem conj_inv_pow' (g t : G) (n : ℕ) : (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
  simpa using (conj_pow (a := g⁻¹) (b := t) (i := n))

theorem conj_inv_zpow' (g t : G) (n : ℤ) : (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
  simpa using (conj_zpow (a := g⁻¹) (b := t) (i := n))

end General

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.kg_HK_central
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I))
    (hP2f : ∀ α : MulAut K, GGL45InP p θ I (ggL45KgE K _ hcfg.kg_B1N) α →
      ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → α h = h)
    {h : G} (hh : h ∈ U ⊓ K) {b : G} (hb : b ∈ U₁) : h * b = b * h := by
  have := hP2f _ (hcfg.kg_inP θ hiff hb) ⟨h, hh.2⟩ (hcfg.kg_inS_of_mem hh.1 hh.2)
  exact ((ggL45_rhoK_fix_iff _ _).mp this).symm

theorem GGL45Config.kg_normalizer_B1
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {s : ℕ}
    (hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t))
    (hP2e : ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → h ^ p ^ s = 1)
    (hP2n : ∃ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K)
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    (hB₁ : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ U₁) (hx : x ∉ U₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  apply ggL45_mem_normalizer_of_conj_mem
  intro b hb
  have hbU : b ∈ U := hcfg.bs_le hb.1
  have hzU : g * b * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg b).mp hbU
  have hcent : ∀ u ∈ U, (g * b * g⁻¹) * u = u * (g * b * g⁻¹) := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
      simpa using this
    have hc : b * (g⁻¹ * u * g) = (g⁻¹ * u * g) * b :=
      (Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hu')) b hb
    calc g * b * g⁻¹ * u = g * (b * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * b) * g⁻¹ := by rw [hc]
      _ = u * (g * b * g⁻¹) := by group
  have hzp : (g * b * g⁻¹) ^ p = 1 := by
    rw [conj_pow, hcfg.isElemAbelian.2 b hb.1]
    group
  have hzBs : g * b * g⁻¹ ∈ Bs :=
    hcfg.mem_of_commute hzU (hcent x (hcfg.bs_le hcfg.x_mem)) hzp
  have hzU₁ : g * b * g⁻¹ ∈ U₁ := hcfg.kg_mem_part_of_cent θ hinn hiff hmul hP2e hP2n hP4 hzU
    (fun h hh => hcent h hh.1)
  exact hcfg.inf_part_le hB₁ hx ⟨hzBs, hzU₁⟩

theorem GGL45Config.kg_normalizer_part
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {s : ℕ}
    (hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t))
    (hP2e : ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → h ^ p ^ s = 1)
    (hP2n : ∃ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K)
    (hP2f : ∀ α : MulAut K, GGL45InP p θ I (ggL45KgE K _ hcfg.kg_B1N) α →
      ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → α h = h)
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (U₁ : Set G) := by
  apply ggL45_mem_normalizer_of_conj_mem
  intro u hu
  have hzU : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg u).mp (hcfg.part_le hu)
  refine hcfg.kg_mem_part_of_cent θ hinn hiff hmul hP2e hP2n hP4 hzU fun h hh => ?_
  have hh' : g⁻¹ * h * g ∈ U ⊓ K := by
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) h).mp hh.1
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) h).mp hh.2
  have hc := hcfg.kg_HK_central θ hiff hP2f hh' hu
  calc g * u * g⁻¹ * h = g * (u * (g⁻¹ * h * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * h * g) * u) * g⁻¹ := by rw [hc]
    _ = h * (g * u * g⁻¹) := by group

theorem GGL45Config.kg_V_inter
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hΩ : ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), v ^ p = 1 → v ∈ Subgroup.zpowers d)
    {g : G} (hgd : g ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G)) {c : G}
    (hc : c ∈ U ⊓ Subgroup.centralizer (K : Set G))
    (hcg : g⁻¹ * c * g ∈ U ⊓ Subgroup.centralizer (K : Set G)) : c = 1 := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hc1
  obtain ⟨N, hN⟩ := hcfg.isPGroup ⟨c, hc.1⟩
  have hex : ∃ i, c ^ p ^ i = 1 := ⟨N, by simpa using congrArg Subtype.val hN⟩
  classical
  set i := Nat.find hex with hi
  have hi0 : i ≠ 0 := fun h0 => by
    have := Nat.find_spec hex
    rw [← hi, h0, pow_zero, pow_one] at this
    exact hc1 this
  obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hc'1 : c ^ p ^ i' ≠ 1 := Nat.find_min hex (by omega)
  have hc'p : (c ^ p ^ i') ^ p = 1 := by
    have := Nat.find_spec hex
    rw [← hi, hi', pow_succ, pow_mul] at this
    exact this
  have hc'V : c ^ p ^ i' ∈ U ⊓ Subgroup.centralizer (K : Set G) := Subgroup.pow_mem _ hc _
  have hgc'V : g⁻¹ * c ^ p ^ i' * g ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    rw [← conj_inv_pow']
    exact Subgroup.pow_mem _ hcg _
  have hgc'1 : g⁻¹ * c ^ p ^ i' * g ≠ 1 := by
    intro h
    apply hc'1
    have := congrArg (fun t => g * t * g⁻¹) h
    simpa [mul_assoc] using this
  have hgc'p : (g⁻¹ * c ^ p ^ i' * g) ^ p = 1 := by
    rw [conj_inv_pow', hc'p]
    group
  have hdo : orderOf d = p := orderOf_eq_prime hcfg.d_pow hcfg.d_ne
  have key : ∀ t, t ∈ Subgroup.zpowers d → t ≠ 1 → t ^ p = 1 →
      Subgroup.zpowers t = Subgroup.zpowers d := fun t ht ht1 htp =>
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hdo, orderOf_eq_prime htp ht1])
  have h1 := key _ (hΩ _ hc'V hc'p) hc'1 hc'p
  have h2 := key _ (hΩ _ hgc'V hgc'p) hgc'1 hgc'p
  apply hgd
  have hinv : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    ggL45_mem_normalizer_of_conj_mem fun n hn => by
      rw [← h1] at hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← h2, inv_inv, ← conj_inv_zpow']
      exact Subgroup.zpow_mem_zpowers _ _
  simpa using Subgroup.inv_mem _ hinv

theorem GGL45Config.kg_abelian_of_move
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I))
    (hB₁ : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ U₁) (hx : x ∉ U₁)
    (hpk : GGL45TorusPackage p I θ (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)
      (ggL45KgE K _ hcfg.kg_B1N))
    (hΩ : ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), v ^ p = 1 → v ∈ Subgroup.zpowers d)
    {g₀ : G} (hg₀U : g₀ ∈ U) (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁)
    {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hgN : g ∉ Subgroup.normalizer (U₁ : Set G)) :
    ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨-, -, hcommV, -⟩ := hcfg.kg_torus θ hinn hiff hpk
  obtain ⟨s, hs, -, -, -, -, hP2m, hP2e, hP2n, hP2f, ⟨a₁, a₂, ha₁, ha₂, -, -, -, hind⟩, hP4⟩ :=
    hpk
  have hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t) := fun h t hh ht => (hP2m h t hh ht).2
  have hHU₁ : ∀ h ∈ U ⊓ K, h ∈ U₁ := fun h hh =>
    hcfg.kg_S_mem θ hinn hiff hmul (hcfg.kg_inS_of_mem hh.1 hh.2)
  have hHab : ∀ a ∈ U ⊓ K, ∀ b ∈ U ⊓ K, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      (hP2m ⟨a, ha.2⟩ ⟨b, hb.2⟩ (hcfg.kg_inS_of_mem ha.1 ha.2) (hcfg.kg_inS_of_mem hb.1 hb.2)).1
  have hUp : IsPGroup p U := hcfg.isPGroup
  have hpow1 : ∀ u ∈ U, ∃ M : ℕ, u ^ p ^ M = 1 := fun u hu => by
    obtain ⟨M, hM⟩ := hUp ⟨u, hu⟩
    exact ⟨M, by simpa using congrArg Subtype.val hM⟩
  have hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have hgU' : ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun u hu => by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
  have hgB : g ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    hcfg.kg_normalizer_B1 θ hinn hiff hmul hP2e hP2n hP4 hB₁ hx hg
  have hgd : g ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun hgd =>
    hgN (hcfg.kg_normalizer_part θ hinn hiff hmul hP2e hP2n hP2f hP4 hg
      (ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hgB, hgd⟩))
  set N : Subgroup G := U₁.map (MulAut.conj g).toMonoidHom with hNdef
  have memN : ∀ n, n ∈ N ↔ g⁻¹ * n * g ∈ U₁ := fun n => by
    rw [hNdef, Subgroup.mem_map_equiv]
    simp
  have hNU : N ≤ U := fun n hn => by
    have := hgU _ (hcfg.part_le ((memN n).mp hn))
    simpa [mul_assoc] using this
  have hUNN : U ≤ Subgroup.normalizer (N : Set G) := fun u hu =>
    ggL45_mem_normalizer_of_conj_mem fun n hn => by
      rw [memN]
      have := hcfg.conj_mem_part (hgU' u hu) ((memN n).mp hn)
      have e : g⁻¹ * (u * n * u⁻¹) * g =
          g⁻¹ * u * g * (g⁻¹ * n * g) * (g⁻¹ * u * g)⁻¹ := by group
      rw [e]
      exact this
  have hcardN : Nat.card N = Nat.card U₁ :=
    Subgroup.card_map_of_injective (fun a b h => (MulAut.conj g).injective h)
  have hg₀'U : g * g₀ * g⁻¹ ∈ U := hgU _ hg₀U
  have hNcyc : U ≤ Subgroup.zpowers (g * g₀ * g⁻¹) ⊔ N := by
    intro u hu
    have hm := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hcyc (hgU' u hu))
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at hm
    have e1 : (MulAut.conj g).toMonoidHom (g⁻¹ * u * g) = u := by simp [mul_assoc]
    have e2 : (MulAut.conj g).toMonoidHom g₀ = g * g₀ * g⁻¹ := by simp
    rw [e1, e2] at hm
    exact hm
  have hNU₁ : ¬ N ≤ U₁ := fun hle => hgN (ggL45_mem_normalizer_of_conj_mem fun u hu => hle (by
    rw [memN]
    simpa [mul_assoc] using hu))
  have hU₁N : ¬ U₁ ≤ N := fun hle =>
    hNU₁ (Subgroup.eq_of_le_of_card_ge hle hcardN.le ▸ le_refl _)
  have hcommN : ∀ a ∈ N, ∀ b ∈ N,
      g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    intro a ha b hb
    have := hcommV _ ((memN a).mp ha) _ ((memN b).mp hb)
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) *
        (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact this
  have hAab : ∀ a ∈ U₁, a ∈ N → ∀ b ∈ U₁, b ∈ N → a * b = b * a := by
    intro a ha haN b hb hbN
    have hc := hcfg.kg_V_inter hΩ hgd (hcommV a ha b hb) (hcommN a haN b hbN)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc
  obtain ⟨w, hwN, j, hNle, hwj1, hwj⟩ :=
    exists_gen_mod_of_cyclic hcfg.part_le hcfg.le_normalizer_part hUp hg₀U hcyc hNU hNU₁
  obtain ⟨u₀, hu₀, j', hU₁le, hu₀j1, hu₀j⟩ :=
    exists_gen_mod_of_cyclic hNU hUNN hUp hg₀'U hNcyc hcfg.part_le hU₁N
  have hwU : w ∈ U := hNU hwN
  have c1 : Nat.card N ≤ Nat.card (N ⊓ U₁ : Subgroup G) * p ^ (j + 1) :=
    card_le_card_inf_mul_of_le_sup hwN (hcfg.le_normalizer_part hwU) hNle (pow_pos hp.pos _) hwj1
  obtain ⟨M₀, hM₀⟩ := hpow1 u₀ (hcfg.part_le hu₀)
  have c2 : Nat.card (U₁ ⊓ N : Subgroup G) * p ^ (j' + 1) ≤ Nat.card U₁ :=
    card_inf_mul_pow_le hp hu₀ (N := M₀) (by rw [hM₀]; exact N.one_mem) hu₀j
  have hjj : p ^ (j' + 1) ≤ p ^ (j + 1) := by
    have hpos : 0 < Nat.card (U₁ ⊓ N : Subgroup G) := Nat.card_pos
    rw [inf_comm] at c1
    exact Nat.le_of_mul_le_mul_left (c2.trans (hcardN.symm.le.trans c1)) hpos
  have c3 : Nat.card (U₁ ⊔ N : Subgroup G) ≤ Nat.card N * p ^ (j + 1) := by
    have := card_le_card_inf_mul_of_le_sup (A := U₁ ⊔ N) (U₁ := N)
      ((le_sup_left : U₁ ≤ U₁ ⊔ N) hu₀) (hUNN (hcfg.part_le hu₀))
      (sup_le hU₁le le_sup_right) (pow_pos hp.pos _) hu₀j1
    rw [inf_eq_right.mpr le_sup_right] at this
    exact this.trans (Nat.mul_le_mul_left _ hjj)
  have hdec : ∀ u ∈ U₁, ∃ z ∈ U ⊓ K, z⁻¹ * u ∈ N := by
    by_cases hA : ∃ h ∈ U ⊓ K, h ^ p ^ j ∉ N
    · obtain ⟨h, hh, hhj⟩ := hA
      obtain ⟨M, hM⟩ := hpow1 h hh.1
      have c4 := card_inf_mul_pow_le hp (A := Subgroup.zpowers h ⊔ N) (M := N)
        ((le_sup_left : Subgroup.zpowers h ≤ _) (Subgroup.mem_zpowers h))
        (N := M) (by rw [hM]; exact N.one_mem) hhj
      rw [inf_eq_right.mpr le_sup_right] at c4
      have hle : Subgroup.zpowers h ⊔ N ≤ U₁ ⊔ N :=
        sup_le_sup_right (Subgroup.zpowers_le.mpr (hHU₁ h hh)) N
      have heq : Subgroup.zpowers h ⊔ N = U₁ ⊔ N :=
        Subgroup.eq_of_le_of_card_ge hle (c3.trans c4)
      intro u hu
      have hu' : u ∈ ((Subgroup.zpowers h ⊔ N : Subgroup G) : Set G) := by
        rw [heq]
        exact (le_sup_left : U₁ ≤ U₁ ⊔ N) hu
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (Subgroup.zpowers_le.mpr (hUNN hh.1))] at hu'
      obtain ⟨z, hz, n, hn, hzn⟩ := hu'
      refine ⟨z, (Subgroup.zpowers_le.mpr hh) hz, ?_⟩
      rw [← hzn]
      simpa using hn
    · simp only [not_exists, not_and, not_not] at hA
      exfalso
      obtain ⟨k', hk', hact⟩ := hcfg.kg_powmap θ hiff hP4 (U.pow_mem hwU _) hwj
        (by rw [← pow_mul, ← pow_succ]; exact hwj1)
      have hwH : ∀ t ∈ U ⊓ K, w⁻¹ * t * w ∈ U ⊓ K := fun t ht =>
        ⟨U.mul_mem (U.mul_mem (U.inv_mem hwU) ht.1) hwU, by
          simpa using (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ (hcfg.le_normalizer hwU)) t).mp ht.2⟩
      have hVg : ∀ h ∈ U ⊓ K,
          g⁻¹ * h ^ p ^ (s - 1) * g ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
        intro h hh
        obtain ⟨y', -, hyN, hyt⟩ := ggL45_exists_telescope hHab hwH hwN (hUNN hh.1) hh (p ^ j)
        have hyN' : y' ∈ N := by
          have := N.mul_mem (hA h hh) hyN
          simpa using this
        have hc' := hcommN y'⁻¹ (N.inv_mem hyN') w⁻¹ (N.inv_mem hwN)
        have e2 : y'⁻¹ * w⁻¹ * y'⁻¹⁻¹ * w⁻¹⁻¹ = y'⁻¹ * (w⁻¹ * y' * w) := by group
        have e3 : h⁻¹ * h ^ (1 + p ^ (s - 1) * k') = (h ^ p ^ (s - 1)) ^ k' := by
          rw [pow_add, pow_one, ← pow_mul]
          group
        rw [e2, hyt, hact h hh, e3, ← conj_inv_pow'] at hc'
        have hhp : (h ^ p ^ (s - 1)) ^ p = 1 := by
          rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
          simpa using congrArg Subtype.val (hP2e ⟨h, hh.2⟩ (hcfg.kg_inS_of_mem hh.1 hh.2))
        have hp1 : (g⁻¹ * h ^ p ^ (s - 1) * g) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
          rw [conj_inv_pow', hhp]
          simpa using (U ⊓ Subgroup.centralizer (K : Set G)).one_mem
        have hg1 := ggL45_pow_gcd_mem hc' hp1
        rwa [Nat.gcd_comm, (Nat.Prime.coprime_iff_not_dvd hp).mpr hk', pow_one] at hg1
      have hzind := hcfg.kg_zind θ hinn hiff hx hs hP2m hP2e hP4 ha₁ ha₂ hind 1 hp.not_dvd_one
      simp only [pow_one] at hzind
      have hUK : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a → (a : G) ∈ U ⊓ K := fun a ha =>
        ⟨hcfg.part_le (hcfg.kg_S_mem θ hinn hiff hmul ha), a.2⟩
      have hzp : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
          ((a : G) ^ p ^ (s - 1)) ^ p = 1 := by
        intro a ha
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
        simpa using congrArg Subtype.val (hP2e a ha)
      set z₁ := (a₁ : G) ^ p ^ (s - 1) with hz₁
      set z₂ := (a₂ : G) ^ p ^ (s - 1) with hz₂
      have hz₁1 : z₁ ≠ 1 := fun h => by
        have := (hzind 1 0 (by rw [pow_one, pow_zero, mul_one]; exact h)).1
        exact hp.not_dvd_one this
      have hdo : orderOf d = p := orderOf_eq_prime hcfg.d_pow hcfg.d_ne
      have hgz₁ : g⁻¹ * z₁ * g ∈ Subgroup.zpowers d :=
        hΩ _ (hVg _ (hUK a₁ ha₁)) (by rw [conj_inv_pow', hzp a₁ ha₁]; group)
      have hgz₂ : g⁻¹ * z₂ * g ∈ Subgroup.zpowers d :=
        hΩ _ (hVg _ (hUK a₂ ha₂)) (by rw [conj_inv_pow', hzp a₂ ha₂]; group)
      have hgz₁1 : g⁻¹ * z₁ * g ≠ 1 := fun h => hz₁1 (by
        have := congrArg (fun t => g * t * g⁻¹) h
        simpa [mul_assoc] using this)
      have heqz : Subgroup.zpowers (g⁻¹ * z₁ * g) = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgz₁)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hdo,
            orderOf_eq_prime (by rw [conj_inv_pow', hzp a₁ ha₁]; group) hgz₁1])
      rw [← heqz] at hgz₂
      obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hgz₂)
      rw [conj_inv_pow'] at hi
      have hz₂ : z₂ = z₁ ^ i := by
        have := congrArg (fun t => g * t * g⁻¹) hi
        simpa [mul_assoc] using this.symm
      have := (hzind ((p - 1) * i) 1 (by
        have hz₁p : z₁ ^ p = 1 := hzp a₁ ha₁
        have e : (p - 1) * i + i = p * i := by
          have := hp.one_lt
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this.le]
        rw [hz₂, pow_one, ← pow_add, e, pow_mul, hz₁p, one_pow])).2
      exact hp.not_dvd_one this
  intro a ha b hb
  obtain ⟨z, hz, hzN⟩ := hdec a ha
  obtain ⟨z', hz', hzN'⟩ := hdec b hb
  have hn : z⁻¹ * a ∈ U₁ := U₁.mul_mem (U₁.inv_mem (hHU₁ z hz)) ha
  have hn' : z'⁻¹ * b ∈ U₁ := U₁.mul_mem (U₁.inv_mem (hHU₁ z' hz')) hb
  have h1 : (z⁻¹ * a) * z' = z' * (z⁻¹ * a) := (hcfg.kg_HK_central θ hiff hP2f hz' hn).symm
  have h2 : z * z' = z' * z := hcfg.kg_HK_central θ hiff hP2f hz (hHU₁ z' hz')
  have h3 : (z⁻¹ * a) * (z'⁻¹ * b) = (z'⁻¹ * b) * (z⁻¹ * a) := hAab _ hn hzN _ hn' hzN'
  have h4 : z * (z'⁻¹ * b) = (z'⁻¹ * b) * z := hcfg.kg_HK_central θ hiff hP2f hz hn'
  calc a * b = z * (z⁻¹ * a) * (z' * (z'⁻¹ * b)) := by group
    _ = z * ((z⁻¹ * a) * z') * (z'⁻¹ * b) := by group
    _ = z * (z' * (z⁻¹ * a)) * (z'⁻¹ * b) := by rw [h1]
    _ = (z * z') * ((z⁻¹ * a) * (z'⁻¹ * b)) := by group
    _ = (z' * z) * ((z'⁻¹ * b) * (z⁻¹ * a)) := by rw [h2, h3]
    _ = z' * (z * (z'⁻¹ * b)) * (z⁻¹ * a) := by group
    _ = z' * ((z'⁻¹ * b) * z) * (z⁻¹ * a) := by rw [h4]
    _ = b * a := by group

end Config

theorem ggL45FiveRankInput_of_known (hraw : GGRawInnFieldInput)
    (hisoI : GGRawInndiagIsoInput) (hsub : GGNbrSubcomponentInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hcD4 : GGL45CyclicD4IOneInput)
    (hgr : GGNbrGraphInput) (hD4 : GGL45D4BstarProperInput) (hnone : GGL44iiiTriD4NoneInput)
    (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) (hT : GGStdSubNotTorsionInput)
    (hK : GGL45KnownForms) : GGL45FiveRankInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 hΩ
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨R, _, I, θ, hinn, hiff, hpk⟩ :=
    hcfg.kg_package hraw hisoI hsub hgr hD4 hnone hStdL hE6 hT hK hI1
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hisoI hcfg
  obtain ⟨g₀, hg₀U, hcyc⟩ := hcfg.exists_cyclic_of_iOne hpc hcD4 hI1
  left
  refine ⟨fun hcomm => ?_, fun g hg hgN =>
    hcfg.kg_abelian_of_move θ hinn hiff hB₁U₁ hxU₁ hpk hΩ hg₀U hcyc hg hgN⟩
  have hab : IsMulCommutative U₁ := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  obtain ⟨s, hs, -, -, -, -, hP2m, hP2e, -, -, hP3, hP4⟩ := hpk
  exact thompson_eq_of_cent_bound hcfg.part_le hcfg.le_normalizer_part hcfg.isPGroup hab hg₀U
    hcyc (hcfg.kg_cent_bound θ hinn hiff hxU₁ hs hP2m hP2e hP3 hP4 hab)

end CFSG.StandardType
