module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticMovingFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticMovingSupport
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticPermutationFour
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix Polynomial CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (permSp)
open CFSG.StandardType.WitSpNs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped commutatorElement


theorem four_dvd_movingBlock_of_full_planeFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (t : ↥E) (ht3 : (t : StatedSp n K) ^ 3 = 1)
    (i : Fin 4 → Fin n) (hi : Function.Injective i) (hmoving : ∀ a, k (i a) t ≠ 1) :
    4 ∣ Nat.card (ggAutomizer
      ⁅spSupported (t : StatedSp n K) {X ^ 2 + X + 1},
        spSupported (t : StatedSp n K) {X ^ 2 + X + 1}⁆ E) := by
  classical
  let U : StatedSp n K := movingU i k t
  let u : StatedSp n K := A₀ * U * A₀⁻¹
  have hU2 : U * U = 1 := movingU_mul_self i hi
  have hu2 : u * u = 1 := by
    change (MulAut.conj A₀ U) * (MulAut.conj A₀ U) = 1
    rw [← map_mul, hU2, map_one]
  have huN : u ∈ Subgroup.normalizer (E : Set (StatedSp n K)) :=
    movingU_mem_normalizer_of_full_frame hK hdet hM hframe hsurj i t
  obtain ⟨t', haligned, heq⟩ := exists_aligned_moving_generator hK hdet hM hframe hsurj i hi t hmoving
  have hut : u * (t : StatedSp n K) * u⁻¹ = t' := heq
  let T : StatedSp n K := A₀⁻¹ * t' * A₀
  have ht'3 : (t' : StatedSp n K) ^ 3 = 1 := by
    rw [← hut]
    change ((MulAut.conj u) (t : StatedSp n K)) ^ 3 = 1
    rw [← map_pow, ht3, map_one]
  have hT3 : T ^ 3 = 1 := by
    change ((MulAut.conj A₀⁻¹) (t' : StatedSp n K)) ^ 3 = 1
    rw [← map_pow, ht'3, map_one]
  let I : Finset (Fin n) := Finset.univ.image i
  have hIrange : (I : Set (Fin n)) = Set.range i := by ext j; simp [I]
  have hIP : ∀ j ∈ I, M ^ (Multiplicative.toAdd (k j t')).val = M := by
    intro j hj
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hj
    rw [haligned a]
    change M ^ 1 = M
    exact _root_.pow_one M
  have hImoving : ∀ j ∈ I, k j t' ≠ 1 := by
    intro j hj
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hj
    rw [haligned a]
    decide +kernel
  let a : StatedSp n K := A₀ * U
  have haT : a * T * a⁻¹ = (t : StatedSp n K) := by
    calc a * T * a⁻¹ = u * (t' : StatedSp n K) * u⁻¹ := by dsimp [a, T, u]; group
      _ = u * (u * (t : StatedSp n K) * u⁻¹) * u⁻¹ := by rw [← hut]
      _ = (u * u) * (t : StatedSp n K) * (u * u)⁻¹ := by group
      _ = t := by rw [hu2]; simp
  let B : Equiv.Perm (Fin n) →* StatedSp n K :=
    { toFun := fun π => A₀ * permSp K π * A₀⁻¹
      map_one' := by rw [permSp_one_of_injective, mul_one, mul_inv_cancel]
      map_mul' := fun π ρ => by rw [permSp_mul_of_injective]; group }
  let S : Subgroup (StatedSp n K) := spSupported (t : StatedSp n K) {X ^ 2 + X + 1}
  have hmember : ∀ π : Equiv.Perm (Fin n), (∀ j ∉ Set.range i, π j = j) →
      u * B π * u⁻¹ ∈ S := by
    intro π hfix
    have hfixI : ∀ j ∉ I, π j = j := by
      intro j hj
      apply hfix j
      change j ∉ (I : Set (Fin n)) at hj
      rwa [hIrange] at hj
    have hπI := permSp_mem_spBlock_of_fix_outside (K := K) π hfixI
    have hcomm := permSp_commute_of_constant_planes (hframe t') hIP π hfixI
    have hfixT := fix_fixed_of_supported_moving hK hdet hM (hframe t') hImoving hπI
    have hm := conj_mem_movingFactor_of_fix_fixed hK a hT3 hcomm hfixT
    rw [haT] at hm
    change u * B π * u⁻¹ ∈ spSupported (t : StatedSp n K) {X ^ 2 + X + 1}
    have he : u * B π * u⁻¹ = a * permSp K π * a⁻¹ := by dsimp [u, B, a]; group
    rw [he]
    exact hm
  let φ : StatedSp n K →* StatedSp n K := (MulAut.conj u).toMonoidHom
  let S' : Subgroup (StatedSp n K) := S.map φ
  let H : Subgroup (StatedSp n K) := ⁅S, S⁆
  let H' : Subgroup (StatedSp n K) := ⁅S', S'⁆
  obtain ⟨p, q, r, s, g, h, hfix, hgp, hhr, hg2, hh2, hgh, hg1, hh1, hne⟩ :=
    exists_klein_commutator_permutations i hi
  have hsrc : ∀ π ∈ ({p, q, r, s} : Set (Equiv.Perm (Fin n))), B π ∈ S' := by
    intro π hπ
    refine Subgroup.mem_map.mpr ⟨u * B π * u⁻¹, hmember π (hfix π hπ), ?_⟩
    change u * (u * B π * u⁻¹) * u⁻¹ = B π
    calc u * (u * B π * u⁻¹) * u⁻¹ = (u * u) * B π * (u * u)⁻¹ := by group
      _ = B π := by rw [hu2]; simp
  have hgJ : B g ∈ H' := by
    rw [hgp]
    have hp := hsrc p (by simp)
    have hq := hsrc q (by simp)
    simpa only [commutatorElement_def, map_mul, map_inv] using
      Subgroup.commutator_mem_commutator hp hq
  have hhJ : B h ∈ H' := by
    rw [hhr]
    have hr := hsrc r (by simp)
    have hs := hsrc s (by simp)
    simpa only [commutatorElement_def, map_mul, map_inv] using
      Subgroup.commutator_mem_commutator hr hs
  have hfour : 4 ∣ Nat.card (ggAutomizer H' E) :=
    four_dvd_of_klein_permutations_in_full_frame hframe hsurj hg2 hh2 hgh hg1 hh1 hne hgJ hhJ
  have hHmap : H.map φ = H' := by
    change (⁅S, S⁆).map φ = ⁅S.map φ, S.map φ⁆
    rw [Subgroup.map_commutator]
  have hEmap : E.map φ = E := by
    simpa only [φ, MulEquiv.toMonoidHom_eq_coe] using
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp huN
  have hcard : Nat.card (ggAutomizer H' E) = Nat.card (ggAutomizer H E) := by
    calc Nat.card (ggAutomizer H' E) = Nat.card (ggAutomizer (H.map φ) (E.map φ)) := by
            rw [hHmap, hEmap]
      _ = Nat.card (ggAutomizer H E) := by
            rw [F4AutWeyl.ggAutomizer_map_eq (MulAut.conj u).injective H E rfl,
              Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rwa [hcard] at hfour

end CFSG.StandardType.QTwoSymplecticCav

end
