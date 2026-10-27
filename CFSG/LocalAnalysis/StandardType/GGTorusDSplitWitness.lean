module

public import CFSG.LocalAnalysis.StandardType.GGTorusDSplitTorus
public import CFSG.LocalAnalysis.StandardType.GGTBTorItems

@[expose] public noncomputable section

namespace CFSG.StandardType.DSplitTorus

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.SeitzReduction Matrix Multiplicative
open CFSG.LieType.Universal.Spin DScalarTorus TableBSymp TableBOrth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ}

theorem mem_primeTorus_iff (hp : p.Prime) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (g : StatedOmega (StatedQuadPlus N K)) :
    g ∈ (omPlusTorus (m := N) hζ).range ↔ g ^ p = 1 ∧ g ∈ (torusHom (K := K) (N := N)).range := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hz : Function.Injective (zmodPowHom hζ) := ReflSp.zmodPowHom_injective hζ hζo
  have htors : ∀ u : Kˣ, u ^ p = 1 → ∃ a, zmodPowHom hζ a = u := by
    obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := K)
    intro u hu
    let ζm := l.symm.toMonoidHom
    have hpm : ∀ a, ∃ b, ζm b = zmodPowHom hζ a :=
      fun a => ⟨l (zmodPowHom hζ a), l.symm_apply_apply _⟩
    obtain ⟨a, ha⟩ := TorC.exists_eq_of_pow_eq_one
      (m := Nat.card K - 1) (by have := Finite.one_lt_card (α := K); omega)
      hp l.symm.injective hz hpm (l u) (by
        change (l.symm (l u)) ^ p = 1
        rw [l.symm_apply_apply]
        exact hu)
    exact ⟨a, by
      change zmodPowHom hζ a = l.symm (l u) at ha
      rwa [l.symm_apply_apply] at ha⟩
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_pow]
      have hf : f ^ p = 1 := ReflInner.pow_eq_one_of_zmod f
      rw [hf, map_one]
    · exact ⟨fun i => zmodPowHom hζ (f i), rfl⟩
  · rintro ⟨hgp, a, rfl⟩
    have ha : ∀ i, a i ^ p = 1 := by
      have ht : torusHom (a ^ p) = torusHom (1 : Fin N → Kˣ) := by
        rw [map_pow, hgp, map_one]
      have h := torusHom_injective ht
      exact fun i => congrFun h i
    choose f hf using fun i => htors (a i) (ha i)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    rw [coe_omPlusTorus, omPlusTorusGL_apply, coe_torusHom]
    congr 1
    exact funext hf

theorem exists_ggTorusTorWit_split (hp : p.Prime) (hp2 : p ≠ 2) (hN : 4 ≤ N)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    ∃ w : GGTorusTorWit (Nat.card K - 1) N (StatedOmega (StatedQuadPlus N K))
        (scalarA (omPlusTorus (m := N) hζ).range),
      w.Holds (CartanMatrix.D N) (ggCoxeterMatrixD N) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ1 : ζ ≠ 1 := fun h => hp.ne_one (by simpa [h] using hζo.symm)
  have hpK : p ∣ Nat.card K - 1 := by
    have h := orderOf_dvd_natCard ζ
    rwa [hζo, Nat.card_units] at h
  have hK : 4 ≤ Nat.card K := by
    have h := Nat.le_of_dvd (show 0 < Nat.card K - 1 by
      have := Finite.one_lt_card (α := K); omega) hpK
    have := hp.two_le
    omega
  obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := K)
  have hm : Odd (Nat.card K - 1) := by
    simpa only [Nat.card_units] using AutPSL.odd_card_units (K := K)
  obtain ⟨n, hn⟩ := exists_simple_representatives hK hN
  have hnK : ∀ i (a : Fin N → Kˣ),
      n i * torusHom a * (n i)⁻¹ =
        torusHom (a * (corTuple (Matrix.of (TauCeti.DynkinType.typeDSimpleRoot N hN))
          i (rootCoordinates hN a i))⁻¹) := by
    intro i a
    let χ := l.symm.toMonoidHom
    let b : Fin N → Multiplicative (ZMod (Nat.card K - 1)) := fun j => l (a j)
    have hab : (fun j => χ (b j)) = a := funext fun j => l.symm_apply_apply _
    have hroot : χ (rootCoordinates hN b i) = rootCoordinates hN a i := by
      rw [rootCoordinates_apply, rootCoordinates_apply, map_prod]
      apply Finset.prod_congr rfl
      intro j _
      rw [map_zpow, show χ (b j) = a j from l.symm_apply_apply _]
    have h := hn (Nat.card K - 1) χ i b
    rw [hab, simpleReflection_eq_mul_corTuple] at h
    convert h using 2
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply, map_mul, map_inv, corTuple_apply,
      Matrix.of_apply, map_zpow, hroot]
    rw [show χ (b j) = a j from l.symm_apply_apply _]
  have hZ : Subgroup.center (StatedOmega (StatedQuadPlus N K)) = ⊥ := by
    rw [center_statedOmega_quadPlus (by omega)]
    exact scalars_subgroupOf_omegaPlus_eq_bot (by omega)
  have hτ : Function.Injective (omPlusTorus (m := N) hζ) := fun a b hab =>
    omPlusTorusGL_injective hζ hζo (congrArg Subtype.val hab)
  have hnτ : ∀ i f, n i * omPlusTorus hζ f * (n i)⁻¹ =
      omPlusTorus hζ (simpleReflection hN i f) :=
    fun i f => hn p (zmodPowHom hζ) i f
  obtain ⟨w, hw, -, -, -, -, -⟩ := exists_ggTorusTorWit_of_planeCoordinates hp2 hm hN
    l (torusHom (K := K) (N := N)) torusHom_injective
    (omPlusTorus (m := N) hζ) hτ (mem_primeTorus_iff hp hζ hζo) ζ hζ hζ1 n hnK hnτ
    hZ (centralizer_le_torus hp hp2 hζ hζo)
    (fun g _ u hu => ggKGOmR_isSignedPerm hp hζ hζo g u hu)
    (fun g i hi => ggKGOmR_not_sgnAut hN hp hp2 hζ hζo i ⟨g, hi⟩)
  exact ⟨w, hw⟩

end CFSG.StandardType.DSplitTorus
