module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartOne

open StrongP

namespace Sec15Frattini

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_of_isSylowOf {K R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * g ∈ Subgroup.normalizer (R : Set G) := by
  have hRK : R ≤ K := hR.le
  have hle : conjSub g R ≤ K := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg r).1 (hRK hr)
  have hcs : CFSG.ABGLocalTools.IsSylowOf p (conjSub g R) K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [card_conjSub]
    exact hR.card_eq
  obtain ⟨k, hk, hkconj⟩ := hR.exists_mem_conj hcs
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hA : g * x * g⁻¹ ∈ conjSub g R ↔ x ∈ R := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  have hB := hkconj (g * x * g⁻¹)
  have hC : k⁻¹ * (g * x * g⁻¹) * k = (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ := by group
  rw [← hA, hB, hC]

theorem exists_mem_normalizer_of_normal {K R : Subgroup G} [K.Normal]
    (hR : CFSG.ABGLocalTools.IsSylowOf p R (K ⊔ R)) {g : G}
    (hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ K ⊔ R) :
    ∃ k ∈ K, k⁻¹ * g ∈ Subgroup.normalizer (R : Set G) := by
  have hle : (K ⊔ R).map (MulAut.conj g).toMonoidHom ≤ K ⊔ R := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have h1 : g * (k * r) * g⁻¹ = (g * k * g⁻¹) * (g * r * g⁻¹) := by group
    show g * (k * r) * g⁻¹ ∈ K ⊔ R
    rw [h1]
    exact (K ⊔ R).mul_mem (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem ‹K.Normal› k hk g)) (hconj r hr)
  have heq : (K ⊔ R).map (MulAut.conj g).toMonoidHom = K ⊔ R :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hg : g ∈ Subgroup.normalizer ((K ⊔ R : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hle (Subgroup.mem_map_of_mem _ hx)
    · intro hx
      have h2 : g * x * g⁻¹ ∈ (K ⊔ R).map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
      obtain ⟨y, hy, hyx⟩ := h2
      have h3 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have : y = x := by simpa using h3
      exact this ▸ hy
  obtain ⟨k', hk', hn⟩ := exists_mem_normalizer_of_isSylowOf hR hg
  obtain ⟨k, hk, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hk'
  refine ⟨k, hk, ?_⟩
  have h1 := (Subgroup.normalizer (R : Set G)).mul_mem (Subgroup.le_normalizer hr) hn
  have h2 : r * ((k * r)⁻¹ * g) = k⁻¹ * g := by group
  rwa [h2] at h1

theorem isSylowOf_sup_of_coprime {V R : Subgroup G} [V.Normal] (hR : IsPGroup p ↥R)
    (hV : ¬ p ∣ Nat.card ↥V) : CFSG.ABGLocalTools.IsSylowOf p R (V ⊔ R) := by
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_sup_right, hR, ?_⟩
  rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal V R]
  have hdisj : Disjoint R V := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hV)
  have h1 : R.relIndex V = Nat.card ↥V := by
    rw [← Subgroup.inf_relIndex_right R V, disjoint_iff.1 hdisj, Subgroup.relIndex_bot_left]
  rw [h1]; exact hV

theorem comap_eq_sup_of_sylow {H Hb : Type} [Group H] [Finite H] [Group Hb] [Finite Hb] (π : H →* Hb)
    (hπ : Function.Surjective π) {Qb : Subgroup Hb} (hQb : IsPGroup p ↥Qb) {S : Subgroup H}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S (Qb.comap π)) : Qb.comap π = π.ker ⊔ S := by
  have hker : π.ker ≤ Qb.comap π := fun x hx => by
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 hx)]; exact Qb.one_mem
  have hSle : S ≤ Qb.comap π := hS.le
  refine le_antisymm ?_ (sup_le hker hSle)
  set T := π.ker ⊔ S with hT
  have hTQ : T ≤ Qb.comap π := sup_le hker hSle
  have h1 : T.relIndex (Qb.comap π) ∣ π.ker.relIndex (Qb.comap π) :=
    Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  have h2 : T.relIndex (Qb.comap π) ∣ S.relIndex (Qb.comap π) :=
    Subgroup.relIndex_dvd_of_le_left _ le_sup_right
  have h3 : π.ker.relIndex (Qb.comap π) = Nat.card ↥Qb := by
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hπ]
  have h4 : ¬ p ∣ S.relIndex (Qb.comap π) := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).2.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQb
  rw [h3, hn] at h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).1 h1
  have hm0 : m = 0 := by
    by_contra hm0
    exact h4 ((dvd_pow_self p hm0).trans (hm ▸ h2))
  rw [hm0, pow_zero] at hm
  exact Subgroup.relIndex_eq_one.1 hm

end Sec15Frattini

end CFSG.RankThree.PartOne
