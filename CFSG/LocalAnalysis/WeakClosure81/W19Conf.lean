module

public import CFSG.LocalAnalysis.WeakClosure81.W19Struct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuAct
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Conf196 (D : Data G) (V X : Subgroup G) (g : G) (K : Subgroup G) : Prop where
  le_T : conjSubgroup V g ≤ D.T
  isE : E1.IsE 1 (X ⊔ D.T) D.T (conjSubgroup V g) K

namespace Hyp193

variable {D : Data G} {V₀ : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem isSolvable (h : Hyp193 D V₀ p X) : Group.IsSolvable ↥(X ⊔ D.T) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  exact CFSG.Quasithin.A312Ru.isSolvable_of_card_pq Nat.prime_two h.prime (Ne.symm h.odd)
    (a := b) (b := a) (by rw [Hyp193.card_sup h, ha, hb, mul_comm])

end Hyp193

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem le_H (hc : Conf196 D V X g K) : K ≤ X ⊔ D.T := hc.isE.1

theorem isElemAbelian_A (c : MinCex193 D V₀ V p X) (_hc : Conf196 D V X g K) :
    IsElemAbelian 2 (conjSubgroup V g) :=
  E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g

theorem A_le_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) : conjSubgroup V g ≤ K :=
  (E3.card_le_of_isE c.hyp.isSylowIn_T hc.le_T (hc.isElemAbelian_A c) hc.isE).1

theorem isSolvable_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    Group.IsSolvable ↥K := by
  haveI := c.hyp.isSolvable
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hc.le_H)

theorem eOneAmb (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    E1.EOneAmb K (conjSubgroup V g) :=
  (E1.eOne_iff_amb (hc.A_le_K c)).1 (E1.isE_eOne_of_isSolvable hc.isE (hc.isSolvable_K c)).1

theorem relIndex_A (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    (pCoreOf 2 K).relIndex (conjSubgroup V g) = 2 := by
  obtain ⟨p', -, -, R, -, -, -, -, -, -, -, h⟩ := hc.eOneAmb c
  exact h

theorem not_A_le_pCoreOf (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    ¬ conjSubgroup V g ≤ pCoreOf 2 K := fun h => by
  have h1 := hc.relIndex_A c
  rw [Subgroup.relIndex_eq_one.2 h] at h1
  exact absurd h1 (by norm_num)

theorem pCoreOf_le_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    pCoreOf 2 (X ⊔ D.T) ≤ K := by
  intro t ht
  have htT := Hyp193.pCoreOf_le_T c.hyp ht
  refine (hc.isE.2.1 ?_).2
  refine ⟨htT, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right htT),
    fun a ha => ?_⟩
  have haH : a ∈ X ⊔ D.T := Subgroup.mem_sup_right (hc.le_T ha)
  have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T) haH
  have h1 : a * t⁻¹ * a⁻¹ ∈ pCoreOf 2 (X ⊔ D.T) :=
    (Subgroup.mem_normalizer_iff.1 hnorm t⁻¹).1 (Subgroup.inv_mem _ ht)
  have e : ⁅t, a⁆ = t * (a * t⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ ht h1

theorem pCoreOf_le (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    pCoreOf 2 (X ⊔ D.T) ≤ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hc.pCoreOf_le_K c)
    (hc.le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem V_le_pCoreOf (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) : V ≤ pCoreOf 2 K :=
  c.V_le_pCoreOf.trans (hc.pCoreOf_le c)

theorem g_not_mem_M (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) : g ∉ D.M := by
  intro hg
  apply hc.not_A_le_pCoreOf c
  have h : conjSubgroup V g = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (c.setting.pair.le_normalizer hg)
  rw [h]
  exact hc.V_le_pCoreOf c

theorem exists_orderOf_eq (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    ∃ x ∈ K, orderOf x = p := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  obtain ⟨p', hp', hp'2, R, hRK, -, hOR, hRp, -, hRne, -, -⟩ := hc.eOneAmb c
  obtain ⟨x, hxR, hxO⟩ : ∃ x ∈ R, x ∉ pCoreOf 2 K := by
    by_contra hcon
    exact hRne (le_antisymm (fun x hx => by
      by_contra hxO; exact hcon ⟨x, hx, hxO⟩) hOR)
  have hxK : x ∈ K := hRK hxR
  obtain ⟨k, hk⟩ := hRp x hxR
  have hdvd : p' ∣ orderOf x := by
    by_contra hnd
    have hcop : Nat.Coprime p' (orderOf x) := (Nat.Prime.coprime_iff_not_dvd hp').2 hnd
    exact hxO (E1.mem_of_pow_mem_of_coprime (a := p' ^ k) (b := orderOf x)
      (Nat.Coprime.pow_left k hcop) hk (by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _))
  have hK1 : orderOf x ∣ Nat.card ↥K := by
    have := orderOf_dvd_natCard (⟨x, hxK⟩ : ↥K)
    rwa [← Subgroup.orderOf_coe] at this
  have hKH : Nat.card ↥K ∣ Nat.card ↥(X ⊔ D.T) := Subgroup.card_dvd_of_le hc.le_H
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 c.hyp.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  rw [Hyp193.card_sup c.hyp, ha, hb] at hKH
  have h3 : p' ∣ p ^ a * 2 ^ b := (hdvd.trans hK1).trans hKH
  have hpp : p' = p := by
    rcases (Nat.Prime.dvd_mul hp').1 h3 with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hp' c.hyp.prime).1 (hp'.dvd_of_dvd_pow h)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 (hp'.dvd_of_dvd_pow h)) hp'2
  have hpK : p ∣ Nat.card ↥K := hpp ▸ hdvd.trans hK1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem mem_twoResidual (c : MinCex193 D V₀ V p X) {x : G} (hxK : x ∈ K) (hx : orderOf x = p) :
    x ∈ twoResidual K := by
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient K x hxK
  exact E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (k := 1)
    (by rw [pow_one, ← hx, pow_orderOf_eq_one]; exact Subgroup.one_mem _) hk

end Conf196

end CFSG.LocalAnalysis.WeakClosure81
