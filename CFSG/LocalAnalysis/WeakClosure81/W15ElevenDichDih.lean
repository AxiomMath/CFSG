module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichAct
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichInv
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Rec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem b15_W15ElevenDichDih_perm_four {K I : Subgroup G} (hIK : I ≤ K)
    (hKN : K ≤ normalizer (I : Set G)) (hcK : Nat.card ↥K = 24) (hcI : Nat.card ↥I = 4)
    (hI : IsElemAbelian 2 I) {x t : G} (hxK : x ∈ K) (htK : t ∈ K) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hfix : I ⊓ centralizer ({x} : Set G) = ⊥) (htt : t * t = 1)
    (hmov : ¬ I ≤ centralizer ({t} : Set G)) : Nonempty (↥K ≃* Equiv.Perm (Fin 4)) := by
  haveI hcommI : IsMulCommutative ↥I := hI.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let xK : ↥K := ⟨x, hxK⟩
  let tK : ↥K := ⟨t, htK⟩
  refine CFSG.Quasithin.Fan86.Sigma3.Klein24.nonempty_perm_four
    (G := ↥K) (N := I.subgroupOf K) (x := xK) (t := tK) ?_
  refine ⟨hcK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hIK).2 hKN
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIK).toEquiv).trans hcI
  · intro a ha b hb
    have haI : (a : G) ∈ I := Subgroup.mem_subgroupOf.mp ha
    have hbI : (b : G) ∈ I := Subgroup.mem_subgroupOf.mp hb
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (mul_comm' (⟨(a : G), haI⟩ : ↥I) ⟨(b : G), hbI⟩)
  · refine orderOf_eq_prime ?_ ?_
    · show xK ^ 3 = 1
      ext
      simpa [xK] using hx3
    · show xK ≠ 1
      intro h
      exact hx1 (Subtype.ext_iff.mp h)
  · intro n hn hxn
    have hnI : (n : G) ∈ I := Subgroup.mem_subgroupOf.mp hn
    have hcent : (n : G) ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhx : h = x := Set.mem_singleton_iff.mp hh
      rw [hhx]
      have h1 : x * (n : G) * x⁻¹ = (n : G) := by
        have := congrArg Subtype.val hxn
        simpa [xK] using this
      calc x * (n : G) = (x * (n : G) * x⁻¹) * x := by group
        _ = (n : G) * x := by rw [h1]
    have hmem : (n : G) ∈ I ⊓ centralizer ({x} : Set G) := ⟨hnI, hcent⟩
    rw [hfix] at hmem
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
  · ext
    simpa [tK] using htt
  · obtain ⟨g, hgI, hgC⟩ := SetLike.not_le_iff_exists.mp hmov
    refine ⟨⟨g, hIK hgI⟩, Subgroup.mem_subgroupOf.2 hgI, ?_⟩
    intro heq
    apply hgC
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhx : h = t := Set.mem_singleton_iff.mp hh
    rw [hhx]
    have h1 : t * g * t⁻¹ = g := by
      have := congrArg Subtype.val heq
      simpa [tK] using this
    calc t * g = (t * g * t⁻¹) * t := by group
      _ = g * t := by rw [h1]

namespace Cfg1511

variable {M V₀ V U S H Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem s4Branch15_of_not_le
    (c : Cfg1511 M V₀ V U S H S Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hcard : Nat.card ↥X = p) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 (tSub15 M V₀ V U S))
    (hAQ : ¬ A ≤ qSub15 M V₀ V U H S) : S4Branch15 M V₀ V U S H := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI hNormI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  let N := ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀
  haveI : Finite N := by dsimp only [N]; infer_instance
  have hNp : Nat.card N = p := by
    dsimp only [N]
    exact (c.card_quot_eq_card_X hX).trans hcard
  obtain ⟨ρ, -, hρker⟩ := c.exists_action_tSub15 hX
  obtain ⟨hAT, -, hAsq⟩ := comm_sq_of_mem_elemFamilyIn_two hA
  let ρA : ↥A →* MulAut N := ρ.comp (Subgroup.inclusion hAT)
  have hindex : ρA.ker.index ≤ 2 := index_ker_le_two_of_card_prime hNp ρA hAsq
  have hI2 : Nat.card ↥(iHull15 V₀ U H) ≤
      2 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) :=
    c.card_iHull15_le_mul_card_inf_centralizer hX hA hAT ρ hρker hindex
  have hI : IsElemAbelian 2 (iHull15 V₀ U H) := c.isElemAbelian_iHull15
  have hvT : v ∈ tSub15 M V₀ V U S := c.V₀_le_tSub15 hX.mem
  have hvv : v * v = 1 := by
    simpa [pow_two] using c.cex.hyp.elemAbelian₀.2 v hX.mem
  have hvN : v ∈ normalizer (iHull15 V₀ U H : Set G) :=
    c.tSub15_le_normalizer_iHull15 hvT
  obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have haT : a ∈ tSub15 M V₀ V U S := hAT haA
  let σ : MulAut N := ρ ⟨a, haT⟩
  let τ : MulAut N := ρ ⟨v, hvT⟩
  have ha2 : a * a = 1 := by
    have := congrArg Subtype.val (hAsq ⟨a, haA⟩)
    simpa using this
  have hσ1 : σ ≠ 1 := by
    intro hs
    exact haQ (hρker ⟨a, haT⟩ (by simpa [σ] using hs))
  have hτ1 : τ ≠ 1 := by
    intro hs
    exact c.not_mem_qSub15 hX (hρker ⟨v, hvT⟩ (by simpa [τ] using hs))
  have hσσ : σ * σ = 1 := by
    dsimp only [σ]
    rw [← map_mul,
      show (⟨a, haT⟩ : ↥(tSub15 M V₀ V U S)) * ⟨a, haT⟩ = 1 by
        ext
        simpa using ha2,
      map_one]
  have hττ : τ * τ = 1 := by
    dsimp only [τ]
    rw [← map_mul,
      show (⟨v, hvT⟩ : ↥(tSub15 M V₀ V U S)) * ⟨v, hvT⟩ = 1 by
        ext
        simpa using hvv,
      map_one]
  have hστ : σ = τ := mulAut_eq_of_card_prime hNp σ τ hσσ hττ hσ1 hτ1
  have havQ : a * v ∈ qSub15 M V₀ V U H S :=
    hρker (⟨a, haT⟩ * ⟨v, hvT⟩) (by
      rw [map_mul]
      change σ * τ = 1
      rw [hστ, hττ])
  have havC : a * v ∈ centralizer (iHull15 V₀ U H : Set G) :=
    c.qSub15_le_centralizer_iHull15 hX havQ
  have hI2' : Nat.card ↥(iHull15 V₀ U H) ≤
      2 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) :=
    hI2.trans (Nat.mul_le_mul_left 2
      (Subgroup.card_le_of_le (inf_centralizer_le_of_mul_mem_centralizer haA havC)))
  have hcard_Cv_mul : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) *
      Nat.card ↥(v1Sub15 V₀ U) = Nat.card ↥(iHull15 V₀ U H) := by
    rw [← hX.commutator_eq, card_inf_centralizer_mul_card_commutator_zpowers hI hvN hvv]
  have hle_v1 : Nat.card ↥(v1Sub15 V₀ U) ≤ 2 := by
    have hle : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) *
        Nat.card ↥(v1Sub15 V₀ U) ≤
        2 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) := by
      rw [hcard_Cv_mul]
      exact hI2'
    rw [mul_comm 2] at hle
    exact Nat.le_of_mul_le_mul_left hle Nat.card_pos
  have hcard_v1 : Nat.card ↥(v1Sub15 V₀ U) = 2 := by
    have hgt : 1 < Nat.card ↥(v1Sub15 V₀ U) :=
      (Subgroup.one_lt_card_iff_ne_bot (v1Sub15 V₀ U)).2 (c.cex.v1Sub15_ne_bot c.std)
    omega
  obtain ⟨x, hxX, hx1, hxp, hvx, hcx⟩ := c.exists_generator_inv hX hcard
  have hxN : x ∈ normalizer (iHull15 V₀ U H : Set G) :=
    Hyp1510.le_normalizer_iHull15 V₀ U H (hX.le_H c hxX)
  have hCv_eq : iHull15 V₀ U H ⊓ centralizer ({v} : Set G) = v1Sub15 V₀ U := by
    rw [← hX.commutator_eq]
    exact le_antisymm
      (inf_centralizer_le_commutator_of_inv hI c.prime c.p_ne_two hxp hxN hvN hvv hvx hcx)
      (commutator_zpowers_le_inf_centralizer_of_mul_self hI hvN hvv)
  have hcard_Cv : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) = 2 := by
    rw [hCv_eq, hcard_v1]
  have hcard_I : Nat.card ↥(iHull15 V₀ U H) = 4 := by
    have h := card_inf_centralizer_mul_card_commutator_zpowers hI hvN hvv
    rw [hX.commutator_eq, hcard_v1, hcard_Cv] at h
    omega
  have hXN : X ≤ normalizer (iHull15 V₀ U H : Set G) := fun y hy =>
    Hyp1510.le_normalizer_iHull15 V₀ U H (hX.le_H c hy)
  have hmod : Nat.card ↥(iHull15 V₀ U H) ≡ 1 [MOD p] :=
    card_modEq_one_of_isPGroup_inf_centralizer_eq_bot hX.isPGroup hXN hX.cent
  have hp3 : p = 3 := by
    have hmod' : 4 ≡ 1 [MOD p] := by rwa [hcard_I] at hmod
    have hdvd : p ∣ 3 := by
      have := (Nat.modEq_iff_dvd' (show (1 : ℕ) ≤ 4 by norm_num)).mp hmod'.symm
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq c.prime Nat.prime_three).mp hdvd
  have hcard_K : Nat.card ↥(kHull15 V₀ H) = 24 := by
    rw [c.card_kHull15_eq hX, hcard, hp3, hcard_I]
  have hKN : kHull15 V₀ H ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.hyp.kHull15_le.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  have hx3 : x ^ 3 = 1 := by rw [hp3] at hxp; exact hxp
  have hvK : v ∈ kHull15 V₀ H := Hyp1510.V₀_le_kHull15 V₀ H hX.mem
  have hmov : ¬ iHull15 V₀ U H ≤ centralizer ({v} : Set G) := by
    intro hle
    have hEq : iHull15 V₀ U H ⊓ centralizer ({v} : Set G) = iHull15 V₀ U H :=
      inf_eq_left.mpr hle
    have hcard_eq : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) =
        Nat.card ↥(iHull15 V₀ U H) := by rw [hEq]
    rw [hcard_Cv, hcard_I] at hcard_eq
    omega
  have hKperm : Nonempty (↥(kHull15 V₀ H) ≃* Equiv.Perm (Fin 4)) :=
    b15_W15ElevenDichDih_perm_four (Hyp1510.iHull15_le_kHull15 V₀ U H) hKN hcard_K
      hcard_I hI (hX.le_kHull15 hxX) hvK hx3 hx1 hcx hvv hmov
  have hN3 : Nat.card N = 3 := hNp.trans hp3
  have hQ : qSub15 M V₀ V U H S ≤ kHull15 V₀ H ⊔ cSub15 M V₀ V U H S := by
    rw [c.qSub15_eq_sup hX]
    exact sup_le_sup_right (Hyp1510.iHull15_le_kHull15 V₀ U H) _
  have hTle : tSub15 M V₀ V U S ≤ kHull15 V₀ H ⊔ cSub15 M V₀ V U H S := by
    intro t ht
    let tT : ↥(tSub15 M V₀ V U S) := ⟨t, ht⟩
    by_cases hρt : ρ tT = 1
    · exact hQ (hρker tT hρt)
    · have hρt_eq : ρ tT = τ := mulAut_eq_of_card_three hN3 (ρ tT) τ hρt hτ1
      have htvQ : t * v⁻¹ ∈ qSub15 M V₀ V U H S :=
        hρker (tT * ⟨v, hvT⟩⁻¹) (by
          rw [map_mul, map_inv]
          change ρ tT * τ⁻¹ = 1
          rw [hρt_eq]
          exact mul_inv_cancel τ)
      have ht_eq : t = (t * v⁻¹) * v := by group
      rw [ht_eq]
      exact mul_mem (hQ htvQ) (Subgroup.mem_sup_left hvK)
  exact ⟨hKperm, hTle⟩

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81