module

public import CFSG.LinearAlgebra.FrobeniusPowerNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBWNormInnerPowerMap
public import CFSG.LocalAnalysis.StandardType.GGTBWNormCartanScalar
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterNoglue
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGK1ScLin
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

namespace LinearFrob

theorem dvd_sq_sub_one_of_natCast_sq_eq_one {p q : ℕ} (h : ((q : ℕ) : ZMod p) ^ 2 = 1) :
    p ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · apply (ZMod.natCast_eq_zero_iff _ p).1
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, h, Nat.cast_one, sub_self]

theorem five_le_of_not_dvd_four_pow_sub_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ (2 ^ n) ^ 2 - 1) : 5 ≤ p := by
  have h3 : p ≠ 3 := by
    rintro rfl
    apply hpq
    rw [← pow_mul, pow_mul', show (2 : ℕ) ^ 2 = 4 by norm_num]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have := hp.two_le
  omega

theorem not_dvd_card_ker_largeEvenProjMk {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {H : Subgroup (GL ι K)} {p : ℕ} (hp : p.Prime) (hp1 : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (LargeEvenProjMk H).ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (LargeEvenProjMk H).ker) p hdvd
  apply hp1
  rw [← hx]
  apply orderOf_dvd_of_pow_eq_one
  have hxk : ((x : H) : GL ι K) ∈ LargeEvenScalars ι K := by
    have h1 := x.2
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨u, hu⟩ := hxk
  have hu1 : u ^ (Nat.card K - 1) = 1 := by
    have h1 : Nat.card Kˣ = Nat.card K - 1 := by
      rw [Nat.card_units]
    rw [← h1]
    exact pow_card_eq_one'
  apply Subtype.ext
  apply Subtype.ext
  change ((x : H) : GL ι K) ^ (Nat.card K - 1) = 1
  rw [← hu, ← map_pow, hu1, map_one]

theorem exists_conj_eq_pow_card_largeEvenProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp1 : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hE : IsElemAbelian p E) :
    ∃ z : LargeEvenProj (LargeEvenSLGroup (Fin d) K), ∀ x ∈ E, z * x * z⁻¹ = x ^ Nat.card K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  let H := LargeEvenSLGroup (Fin d) K
  obtain ⟨P, hPp, -, hPmap, hPker⟩ := CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker
    (LargeEvenProjMk H) (QuotientGroup.mk'_surjective _) (not_dvd_card_ker_largeEvenProjMk hp hp1)
    (TableB.isPGroup_of_isElemAbelian hE)
  have hinj : ∀ x ∈ P, LargeEvenProjMk H x = 1 → x = 1 := fun x hx h1 => by
    have hx' : x ∈ P ⊓ (LargeEvenProjMk H).ker := ⟨hx, h1⟩
    rw [hPker] at hx'
    exact hx'
  have hmemE : ∀ x ∈ P, LargeEvenProjMk H x ∈ E := fun x hx => hPmap ▸ ⟨x, hx, rfl⟩
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hc : x * y * x⁻¹ * y⁻¹ = 1 := hinj _
      (P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)) (by
        have hab : LargeEvenProjMk H x * LargeEvenProjMk H y =
            LargeEvenProjMk H y * LargeEvenProjMk H x :=
          TableB.IsElemAbelian.comm hE (hmemE x hx) (hmemE y hy)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
        group)
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hc, one_mul]
  let S : Subgroup (GL (Fin d) K) := P.map H.subtype
  haveI : Finite S := inferInstanceAs (Finite ↥(H.subtype '' (P : Set H)))
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hPcomm x hx y hy)
  have hScard : (Nat.card S : K) ≠ 0 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk, Nat.cast_pow]
    refine pow_ne_zero _ fun h0 => ?_
    have h2 := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  obtain ⟨g, hgdet, hg⟩ := CFSG.LinearAlgebra.exists_conj_eq_pow_card_GL hScomm hScard
  have hgH : g ∈ H := TypeA.mem_largeEvenSLGroup_iff.mpr hgdet
  refine ⟨LargeEvenProjMk H ⟨g, hgH⟩, fun x hx => ?_⟩
  rw [← hPmap] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
  congr 1
  apply Subtype.ext
  have h1 := hg (s : GL (Fin d) K) ⟨s, hs, rfl⟩
  rw [Nat.card_eq_fintype_card]
  simpa using h1

end LinearFrob

section Row


open LinearFrob in
theorem ggTorusWNormSC_linear_frob {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 3 ≤ d) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hpq (by
    rw [show Nat.card K ^ 2 - 1 = Nat.card K ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_left _)
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp
    (center_largeEvenProj_largeEvenSLGroup_eq_bot hd)
    (NbrInnerMore.ggOutdiagPrime_linear hp hp1 (by omega))
    (ggCenterPrime_linear_gcd (by omega) hp hp2 fun h1 => hp1 h1.2) ψ hψ hker hperf hA hAI hsc
    (k := Nat.card K) fun E hE _ _ => exists_conj_eq_pow_card_largeEvenProj hp hp2 hp1 hE
  rw [hgen] at hu
  have hs : ggLin (p := p) ι u ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    have h1 := Subgroup.mem_map_of_mem (ggLin (p := p) ι) hu
    rw [MonoidHom.map_closure] at h1
    convert h1 using 2
    ext x
    simp
  have hsq := scalar_sq_eq_one_of_cartan_reflection_datum hp5 M hM C hC h α hpair
    (fun i => ggLin (p := p) ι (φ i)) hlin (ggLin (p := p) ι u) hs (Nat.card K : ZMod p)
    (ggLin_apply_of_forall_pow ι hupow)
  exact hpq (dvd_sq_sub_one_of_natCast_sq_eq_one hsq)

end Row

theorem largeEvenLabelAll_wnorm_linear_frob
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))
    (hr : 3 ≤ lab.rank) (hpq : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2 hpq
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hpq ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
    change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_frob (d := r + 1) hp hp5 (by omega) (by rwa [hK])
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_linear_frob (d := 4) hp hp5 (by norm_num) (by rwa [hK])

end CFSG.StandardType

end
