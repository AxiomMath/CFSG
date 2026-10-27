module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Transfer
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.HypA
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Monolith

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type u} [Group Γ] {p : ℕ} {A W Z : Subgroup Γ} {T : Γ → Subgroup Γ}

namespace Setup

theorem eq_one_of_map_mem_centralizer [Finite Γ] [Z.Normal] (h : Setup p A W Z T) {a : Γ}
    (ha : a ∈ A)
    (hc : ∀ x ∈ W.map (QuotientGroup.mk' Z),
      QuotientGroup.mk' Z a * x = x * QuotientGroup.mk' Z a) : a = 1 := by
  by_contra ha1
  obtain ⟨hTW, hTZ, hfix⟩ := h.fixed a ha ha1
  have hcover : ∀ w ∈ W, ∃ z ∈ Z, ∃ t ∈ T a, w = z * t := by
    intro w hw
    have hmem : QuotientGroup.mk' Z w ∈
        (W ⊓ Subgroup.centralizer {a}).map (QuotientGroup.mk' Z) := by
      rw [map_inf_centralizer_singleton h.prime h.isElemAbelian (QuotientGroup.mk' Z)
        h.normalizes h.coprime ha]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ hw,
        Subgroup.mem_centralizer_singleton_iff.mpr (hc _ (Subgroup.mem_map_of_mem _ hw)).symm⟩
    obtain ⟨c, hcmem, hcw⟩ := hmem
    obtain ⟨z, hz, t, ht, rfl⟩ := hfix c hcmem
    refine ⟨w * t⁻¹, ?_, t, ht, by group⟩
    have h1 : QuotientGroup.mk' Z z = 1 := mk'_eq_one_iff.mpr hz
    rw [← mk'_eq_one_iff, map_mul, map_inv, ← hcw, map_mul, h1, one_mul, mul_inv_cancel]
  have hle : ⁅W, W⁆ ≤ ⁅T a, T a⁆ := commutator_le_of_forall_mul h.le hTW h.central hcover
  have hWT : W ≤ T a :=
    calc W = ⁅W, W⁆ := h.perfect.symm
      _ ≤ ⁅T a, T a⁆ := hle
      _ ≤ T a := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hZT : Z ≤ T a ⊓ Z := le_inf (h.le.trans hWT) le_rfl
  rw [hTZ] at hZT
  exact h.ne_bot (eq_bot_iff.mpr hZT)

theorem injOn_map [Z.Normal] (h : Setup p A W Z T) : Set.InjOn (QuotientGroup.mk' Z) A := by
  intro a ha b hb hab
  have h1 : a * b⁻¹ ∈ A ⊓ Z :=
    Subgroup.mem_inf.mpr ⟨mul_mem ha (inv_mem hb), mem_of_mk'_eq hab⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem isElemAbelian_map [Z.Normal] (h : Setup p A W Z T) :
    IsElemAbelian p (A.map (QuotientGroup.mk' Z)) :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_image p _ A h.isElemAbelian

theorem commute_of_commute_component [Finite Γ] [Z.Normal] (h : Setup p A W Z T)
    {J : Subgroup (Γ ⧸ Z)} (hJ : J ∈ simpleComponents (W.map (QuotientGroup.mk' Z)))
    {b : Γ ⧸ Z} (hb : b ∈ A.map (QuotientGroup.mk' Z)) (hbJ : ∀ t ∈ J, b * t = t * b) :
    ∀ x ∈ W.map (QuotientGroup.mk' Z), b * x = x * b := by
  have hAs := h.isASimple
  have hle : (⨆ J' ∈ simpleComponents (W.map (QuotientGroup.mk' Z)), J') ≤
      Subgroup.centralizer ({b} : Set (Γ ⧸ Z)) := by
    refine iSup₂_le fun J' hJ' x hx => ?_
    obtain ⟨c, hc, rfl⟩ := hAs.components_transitive hJ hJ'
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcb : Commute c b :=
      comm_of_mem_of_isMulCommutative h.isElemAbelian_map.1 hc hb
    have htb : Commute t b := (hbJ t ht).symm
    exact ((hcb.mul_left htb).mul_left hcb.inv_left).eq
  intro x hx
  have hx' : x ∈ ⨆ J' ∈ simpleComponents (W.map (QuotientGroup.mk' Z)), J' := by
    rw [hAs.iSup_components]
    exact hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx')).symm

end Setup

@[expose] def stab (A Z : Subgroup Γ) [Z.Normal] (J : Subgroup (Γ ⧸ Z)) : Subgroup Γ :=
  A ⊓ (Subgroup.normalizer (J : Set (Γ ⧸ Z))).comap (QuotientGroup.mk' Z)

theorem mem_stab_iff {A Z : Subgroup Γ} [Z.Normal] {J : Subgroup (Γ ⧸ Z)} {a : Γ} :
    a ∈ stab A Z J ↔
      a ∈ A ∧ QuotientGroup.mk' Z a ∈ Subgroup.normalizer (J : Set (Γ ⧸ Z)) := Iff.rfl

namespace Setup

theorem card_stab_le [Finite Γ] [Z.Normal] (h : Setup p A W Z T)
    (hB : signalizerMcBrideHypothesisB p (W.map (QuotientGroup.mk' Z)))
    {J : Subgroup (Γ ⧸ Z)} (hJ : J ∈ simpleComponents (W.map (QuotientGroup.mk' Z))) :
    Nat.card (stab A Z J) ≤ p := by
  have hJl : J ∈ lcal (W.map (QuotientGroup.mk' Z)) := by
    refine mem_lcal_iff.mpr ⟨hJ.1, Subgroup.Normal.isSubnormal hJ.2.1, hJ.2.2.1, ?_⟩
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hJ.2.2.2
    exact hxy (congrArg Subtype.val (isMulCommutative_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩))
  have hBA : (stab A Z J).map (QuotientGroup.mk' Z) ≤ A.map (QuotientGroup.mk' Z) :=
    Subgroup.map_mono inf_le_left
  have hBJ : (stab A Z J).map (QuotientGroup.mk' Z) ≤
      Subgroup.normalizer (J : Set (Γ ⧸ Z)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.2
  have hdvd := card_range_conj_dvd h.prime h.isElemAbelian_map hB hJl hBA hBJ
  set ρ := J.normalizerMonoidHom.comp (Subgroup.inclusion hBJ)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hρb : ∀ t : J, ((ρ b t : J) : Γ ⧸ Z) = (b : Γ ⧸ Z) * t * (b : Γ ⧸ Z)⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe J (Subgroup.inclusion hBJ b) t
    have hbJ : ∀ t ∈ J, (b : Γ ⧸ Z) * t = t * (b : Γ ⧸ Z) := by
      intro t ht
      have := hρb ⟨t, ht⟩
      rw [hb] at this
      exact mul_inv_eq_iff_eq_mul.mp this.symm
    have hbA : (b : Γ ⧸ Z) ∈ A.map (QuotientGroup.mk' Z) := hBA b.2
    have hcent := h.commute_of_commute_component hJ hbA hbJ
    obtain ⟨a, ha, hab⟩ := b.2
    have ha1 : a = 1 :=
      h.eq_one_of_map_mem_centralizer ha.1 fun x hx => by rw [hab]; exact hcent x hx
    refine Subtype.ext ?_
    rw [← hab, ha1, map_one]
    rfl
  have hcard1 : Nat.card ((stab A Z J).map (QuotientGroup.mk' Z)) = Nat.card ρ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hcard2 : Nat.card ((stab A Z J).map (QuotientGroup.mk' Z)) = Nat.card (stab A Z J) :=
    card_map_eq_of_injOn (h.injOn_map.mono inf_le_left)
  rw [← hcard2, hcard1]
  exact Nat.le_of_dvd h.prime.pos hdvd

theorem sq_le_card_inf_centralizer [Finite Γ] (h : Setup p A W Z T) :
    p ^ 2 ≤ Nat.card (A ⊓ Subgroup.centralizer (Z : Set Γ) : Subgroup Γ) := by
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨h.prime⟩
  have hAp : IsPGroup p A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A h.isElemAbelian
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer (Z : Set Γ) : Subgroup Γ) ∣ p ^ k :=
    hk ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow h.prime).mp hdvd
  have hj1 : j ≤ 1 := by
    by_contra hj1
    push Not at hj1
    exact (not_lt.mpr (Nat.pow_le_pow_right h.prime.pos hj1)) (hj ▸ hlt)
  have hA₀ : Nat.card (A ⊓ Subgroup.centralizer (Z : Set Γ) : Subgroup Γ) ≤ p := by
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right h.prime.pos hj1
      _ = p := pow_one p
  have hrank : p ^ 2 * Nat.card (A ⊓ Subgroup.centralizer (Z : Set Γ) : Subgroup Γ) ≤
      Nat.card A :=
    calc _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ hA₀
      _ = p ^ 3 := by ring
      _ ≤ Nat.card A := h.rank
  have hZcop : Nat.Coprime p (Nat.card Z) :=
    h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h.le)
  have hgen := iSup_inf_centralizer_sdiff h.prime h.isElemAbelian
    (inf_le_left : A ⊓ Subgroup.centralizer (Z : Set Γ) ≤ A) hrank h.normalizes_Z hZcop
  have hbot : ∀ b ∈ A, b ∉ A ⊓ Subgroup.centralizer (Z : Set Γ) →
      Z ⊓ Subgroup.centralizer {b} = ⊥ := by
    intro b hb hb0
    have hinv : A ≤
        Subgroup.normalizer ((Z ⊓ Subgroup.centralizer {b} : Subgroup Γ) : Set Γ) := by
      refine le_normalizer_of_conj_mem fun a ha x hx =>
        Subgroup.mem_inf.mpr ⟨h.conj_mem_Z ha hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hab : Commute a b := h.comm ha hb
      have hxb : Commute x b := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      exact ((hab.mul_left hxb).mul_left hab.inv_left).eq
    rcases h.minimal _ inf_le_left hinv with h1 | h1
    · exact h1
    · exfalso
      apply hb0
      refine Subgroup.mem_inf.mpr ⟨hb, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : z ∈ Z ⊓ Subgroup.centralizer {b} := by rw [h1]; exact hz
      exact Subgroup.mem_centralizer_singleton_iff.mp hz'.2
  apply h.ne_bot
  rw [← hgen]
  exact eq_bot_iff.mpr (iSup₂_le fun b hb => iSup_le fun hb0 => (hbot b hb hb0).le)

theorem exists_good [Finite Γ] [Z.Normal] (h : Setup p A W Z T)
    (hB : signalizerMcBrideHypothesisB p (W.map (QuotientGroup.mk' Z)))
    {J : Subgroup (Γ ⧸ Z)} (hJ : J ∈ simpleComponents (W.map (QuotientGroup.mk' Z))) :
    ∃ a ∈ A, (∀ z ∈ Z, z * a = a * z) ∧ a ∉ stab A Z J := by
  by_contra hcon
  push Not at hcon
  have hle : A ⊓ Subgroup.centralizer (Z : Set Γ) ≤ stab A Z J := fun a ha =>
    hcon a ha.1 (Subgroup.mem_centralizer_iff.mp ha.2)
  have h1 := Subgroup.card_le_of_le hle
  have h4 : p < p ^ 2 := by nlinarith [h.prime.two_le]
  exact absurd (h.sq_le_card_inf_centralizer.trans (h1.trans (h.card_stab_le hB hJ)))
    (not_le.mpr h4)

end Setup

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
