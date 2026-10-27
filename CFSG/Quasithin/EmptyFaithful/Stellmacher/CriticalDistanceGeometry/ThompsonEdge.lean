module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasD
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

omit [Finite G] in
private theorem isElemAbelian_map_conj {A : Subgroup G} (g : G) (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hA _

omit [Finite G] in
private theorem card_map_conj (g : G) (A : Subgroup G) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  (Nat.card_congr
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm

omit [Finite G] in
private theorem isMaxElemAbelian_map_conj {P A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hA : IsMaxElemAbelian P A) :
    IsMaxElemAbelian P (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hAP, hAe, hmax⟩ := hA
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hg
  refine ⟨?_, isElemAbelian_map_conj g hAe, fun B hBP hBe => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp (hAP ha)
  · have hB' : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg' b).mp (hBP hb)
    have h1 := hmax _ hB' (isElemAbelian_map_conj g⁻¹ hBe)
    rw [card_map_conj] at h1
    rw [card_map_conj]
    exact h1

theorem thompsonJ_eq_of_le_of_le {P P' : Subgroup G} (_hP : IsPGroup 2 P) (hPP' : P' ≤ P)
    (hJ : thompsonJ P ≤ P') : thompsonJ P' = thompsonJ P := by
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
    have hA₀le : A₀ ≤ P' := (le_iSup₂_of_le A₀ hA₀ le_rfl).trans hJ
    have h1 : Nat.card A₀ ≤ Nat.card A := hA.2.2 A₀ hA₀le hA₀.2.1
    have h2 : Nat.card A ≤ Nat.card A₀ := hA₀.2.2 A (hA.1.trans hPP') hA.2.1
    exact le_iSup₂_of_le A
      ⟨hA.1.trans hPP', hA.2.1, fun B hB hBe => (hA₀.2.2 B hB hBe).trans (by omega)⟩ le_rfl
  · refine iSup_le fun A => iSup_le fun hA => ?_
    exact le_iSup₂_of_le A
      ⟨(le_iSup₂_of_le A hA le_rfl).trans hJ, hA.2.1,
        fun B hB hBe => hA.2.2 B (hB.trans hPP') hBe⟩ le_rfl

omit [Finite G] in
theorem thompsonJ_mem_normalizer {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((thompsonJ P : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ x ∈ thompsonJ P, g * x * g⁻¹ ∈ thompsonJ P := by
    intro g hg x hx
    have hle : thompsonJ P ≤ (thompsonJ P).comap (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_iSup₂_of_le _ (isMaxElemAbelian_map_conj hg hA) le_rfl
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem thompsonJ_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    thompsonJ P ≠ ⊥ := by
  have hcard : 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq P (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hcard
  have hx2 : (x : G) ^ 2 = 1 := by
    have : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  have hxne : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hE : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers (x : G)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
  have hxP : Subgroup.zpowers (x : G) ≤ P := Subgroup.zpowers_le.mpr x.2
  have hle := hA₀.2.2 _ hxP hE
  intro hJ
  have hA₀bot : A₀ ≤ ⊥ := hJ ▸ le_iSup₂_of_le A₀ hA₀ le_rfl
  have hcz : Nat.card (Subgroup.zpowers (x : G)) = 2 := by
    rw [Nat.card_zpowers]
    have : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
    rw [this, hx]
  have : Nat.card A₀ = 1 := by
    rw [le_bot_iff.mp hA₀bot, Subgroup.card_bot]
  omega

theorem not_thompsonJ_le_of_normalized (hA : F53Amalgam H M S) {δ ν : Geo H M} (h : ν ∈ nbrs δ)
    {N : Subgroup G} (hN : N ≤ Qv ν) (hNδ : stab δ ≤ Subgroup.normalizer (N : Set G)) :
    ¬ thompsonJ (Qv ν) ≤ N := by
  intro hJN
  have hQ : IsPGroup 2 (Qv ν) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (stab ν)
  have hJeq := thompsonJ_eq_of_le_of_le hQ hN hJN
  have hνN : stab ν ≤ Subgroup.normalizer ((thompsonJ (Qv ν) : Subgroup G) : Set G) :=
    fun g hg => thompsonJ_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab ν) hg)
  have hδN : stab δ ≤ Subgroup.normalizer ((thompsonJ (Qv ν) : Subgroup G) : Set G) := by
    intro g hg
    rw [← hJeq]
    exact thompsonJ_mem_normalizer (hNδ hg)
  have hJle : thompsonJ (Qv ν) ≤ stab δ ⊓ stab ν := by
    have hQle : Qv ν ≤ stab δ ⊓ stab ν := by
      refine le_inf ?_ (CFSG.LieType.BorelTits.pCoreOf_le 2 (stab ν))
      exact Qv_le_stab_of_mem_nbrs hA (δ := ν) (μ := δ) (by
        show (graph (H ⊔ M) H M).Adj ν δ
        exact (show (graph (H ⊔ M) H M).Adj δ ν from h).symm)
    refine iSup_le fun A => iSup_le fun hA' => hA'.1.trans hQle
  have hbot := eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj δ ν from h) hJle hδN hνN
  exact thompsonJ_ne_bot hQ (Qv_ne_bot hA ν) hbot

theorem not_thompsonJ_le_Qv (hA : F53Amalgam H M S) {δ ν : Geo H M} (h : ν ∈ nbrs δ)
    (hle : Qv δ ≤ Qv ν) : ¬ thompsonJ (Qv ν) ≤ Qv δ :=
  not_thompsonJ_le_of_normalized hA h hle (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ))

end F53

end CFSG.Quasithin
