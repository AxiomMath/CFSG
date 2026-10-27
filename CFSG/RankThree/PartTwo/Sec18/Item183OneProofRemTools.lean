module

public import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace Rem187QProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_le_pCore_of_le {K L : Subgroup G} (hKL : K ≤ L) :
    ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hKL)).ker ≤
      CFSG.pCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hKL) with hφ
  refine le_sSup ⟨inferInstance, ?_⟩
  have himg : φ.ker.map (Subgroup.inclusion hKL) ≤ CFSG.pCore 2 L := by
    rintro _ ⟨k, hk, rfl⟩
    have hk1 : QuotientGroup.mk' (CFSG.pCore 2 L) (Subgroup.inclusion hKL k) = 1 := hk
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact ((CFSG.pCore_isPGroup (p := 2) (G := L)).to_le himg).of_equiv
    (φ.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hKL)).symm

omit [Finite G] in
theorem card_quotient_pCore_congr {K K' : Subgroup G} (h : K = K') :
    Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card (K' ⧸ CFSG.pCore 2 K') := by
  subst h
  rfl

theorem card_quotient_pCore_le_card_range {K L : Subgroup G} (hKL : K ≤ L) :
    Nat.card (K ⧸ CFSG.pCore 2 K) ≤
      Nat.card ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hKL)).range := by
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hKL) with hφ
  have hker := ker_le_pCore_of_le hKL
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have h2 := Subgroup.card_mul_index (CFSG.pCore 2 K)
  rw [Subgroup.index_eq_card] at h2
  have hk : Nat.card φ.ker ≤ Nat.card (CFSG.pCore 2 K) := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card (CFSG.pCore 2 K) := Nat.card_pos
  have hle : Nat.card (CFSG.pCore 2 K) * Nat.card (K ⧸ CFSG.pCore 2 K) ≤
      Nat.card (CFSG.pCore 2 K) * Nat.card φ.range := by
    rw [h2, ← h1]
    exact Nat.mul_le_mul_right _ hk
  exact Nat.le_of_mul_le_mul_left hle hpos

theorem eq_sup_pCoreOf_of_card_le {K L : Subgroup G} (hKL : K ≤ L)
    (hcard : Nat.card (L ⧸ CFSG.pCore 2 L) ≤ Nat.card (K ⧸ CFSG.pCore 2 K)) :
    L = K ⊔ CFSG.Open.pCoreOf 2 L := by
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hKL) with hφ
  have hrange : φ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
      (hcard.trans (card_quotient_pCore_le_card_range hKL)))
  refine le_antisymm (fun l hl => ?_) (sup_le hKL (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 L) (⟨l, hl⟩ : L) ∈ φ.range := by
    rw [hrange]
    trivial
  obtain ⟨k, hk⟩ := hmem
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 L) (Subgroup.inclusion hKL k) =
      QuotientGroup.mk' (CFSG.pCore 2 L) (⟨l, hl⟩ : L) := hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
  have hr : (k : G)⁻¹ * l ∈ CFSG.Open.pCoreOf 2 L := (mem_pCore_iff_mem_pCoreOf _).mp hk'
  have heq : l = (k : G) * ((k : G)⁻¹ * l) := by group
  rw [heq]
  exact Subgroup.mul_mem_sup k.2 hr

omit [Finite G] in
theorem mem_sectionCentralizer_of_eq_sup {A Y Y' : Subgroup G} {a : G} (haA : a ∈ A)
    (hY'Y : Y' ≤ Y) (hY : Y = Y' ⊔ CFSG.Open.pCoreOf 2 Y)
    (haY : a ∈ Subgroup.normalizer (Y : Set G))
    (ha : ∀ y ∈ Y', a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) :
    a ∈ sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) := by
  refine ⟨haA, fun y hy => ?_⟩
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have haO : a ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y haY
  have hy' : y ∈ (Y' : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y' O (hY'Y.trans hYO), ← hY]
    exact hy
  obtain ⟨y', hy', r, hr, rfl⟩ := hy'
  have h1 := ha y' hy'
  have h2 : a * r * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp haO r).mp hr
  have h3 : y' * (a * r * a⁻¹ * r⁻¹) * y'⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hYO (hY'Y hy')) _).mp (O.mul_mem h2 (O.inv_mem hr))
  have e : a * (y' * r) * a⁻¹ * (y' * r)⁻¹ =
      (a * y' * a⁻¹ * y'⁻¹) * (y' * (a * r * a⁻¹ * r⁻¹) * y'⁻¹) := by group
  rw [e]
  exact O.mul_mem h1 h3

theorem coe_zpowers_eq_of_mem {S : Set G} {c c₁ : G} (hS : S = (Subgroup.zpowers c₁ : Set G))
    (hc₁ : orderOf c₁ = 3) (hc : c ∈ S) (hc1 : c ≠ 1) : S = (Subgroup.zpowers c : Set G) := by
  rw [hS] at hc ⊢
  have hc' : c ∈ Subgroup.zpowers c₁ := hc
  have hle : Subgroup.zpowers c ≤ Subgroup.zpowers c₁ := Subgroup.zpowers_le.mpr hc'
  have hdvd : orderOf c ∣ 3 := hc₁ ▸ orderOf_dvd_of_mem_zpowers hc'
  have hc3 : orderOf c = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hcard : Nat.card (Subgroup.zpowers c₁) ≤ Nat.card (Subgroup.zpowers c) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hc₁, hc3]
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem_normalizer_zpowers {c g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({c} : Set G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      ∀ x : G, x ∈ Subgroup.centralizer ({c} : Set G) →
        h * x * h⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    intro h hh x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have h1 : h⁻¹ * c * h⁻¹⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hh) c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hck : c = h * c ^ k * h⁻¹ := by rw [hk]; group
    have hxk : Commute x (c ^ k) := (Commute.zpow_right (show Commute x c from hx) k)
    rw [hck]
    calc h * x * h⁻¹ * (h * c ^ k * h⁻¹) = h * (x * c ^ k) * h⁻¹ := by group
      _ = h * (c ^ k * x) * h⁻¹ := by rw [hxk.eq]
      _ = h * c ^ k * h⁻¹ * (h * x * h⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro x hx
  have hxc : Commute x c := (Subgroup.mem_centralizer_singleton_iff.mp hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [(Commute.zpow_right hxc k).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers c k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : y = c ^ k := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * c ^ k * x := by rw [hk]
        _ = c ^ k := by rw [mul_assoc, ← (Commute.zpow_right hxc k).eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers c k

omit [Finite G] in
theorem map_conj_mem_scriptH {A M H : Subgroup G} {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwM : w ∈ M) (hH : H ∈ scriptH A M) :
    H.map (MulAut.conj w).toMonoidHom ∈ scriptH A M := by
  have hf : Function.Injective (MulAut.conj w).toMonoidHom := (MulAut.conj w).injective
  have hA' : A.map (MulAut.conj w).toMonoidHom = A := map_conj_eq_of_mem_normalizer hwA
  have hM' : M.map (MulAut.conj w).toMonoidHom = M :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hwM)
  rw [mem_scriptH_iff_mem_scriptH₀] at hH ⊢
  refine ⟨?_, fun htop => hH.2 ?_⟩
  · have h1 := (map_mem_scriptH₀_iff (MulAut.conj w).toMonoidHom hf).mpr hH.1
    rwa [hA', hM'] at h1
  · apply Subgroup.map_injective hf
    rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj w).surjective]

theorem mem_normalizer_iSup_pCoreOf {𝓕 : Set (Subgroup G)} {x : G}
    (hx : ∀ H ∈ 𝓕, H.map (MulAut.conj x).toMonoidHom ∈ 𝓕) :
    x ∈ Subgroup.normalizer
      ((⨆ H ∈ 𝓕, CFSG.Open.pCoreOf 2 H : Subgroup G) : Set G) := by
  set R : Subgroup G := ⨆ H ∈ 𝓕, CFSG.Open.pCoreOf 2 H with hR
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hle : R.map (MulAut.conj x).toMonoidHom ≤ R := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun H hH => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← pCoreOf_map _ hf]
    exact le_iSup₂ (f := fun H (_ : H ∈ 𝓕) => CFSG.Open.pCoreOf 2 H) _ (hx H hH)
  have heq : R.map (MulAut.conj x).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hf])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem pCoreOf_perfectResidual_le (H : Subgroup G) :
    CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ CFSG.Open.pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.map_subtype_le _))
    ((le_normalizer_inSubgroup_perfectResidual H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

end Rem187QProof

end CFSG.RankThree.PartTwo.Sec18
