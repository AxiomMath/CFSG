module

public import CFSG.Quasithin.Background.HSL3PairNPrime

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def torusHom (K : Type) [Field K] :
    Kˣ × Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun p := ⟨Matrix.diagonal ![(p.1 : K), (p.2 : K), ((p.1 : K) * p.2)⁻¹], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact mul_inv_cancel₀ (mul_ne_zero p.1.ne_zero p.2.ne_zero)⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) K)
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' p q := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp
    · simp
    · simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Fin.reduceFinMk, Matrix.cons_val]
      ring

theorem coe_torusHom (p : Kˣ × Kˣ) :
    ((torusHom K p : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(p.1 : K), (p.2 : K), ((p.1 : K) * p.2)⁻¹] := rfl

theorem torusHom_injective : Function.Injective (torusHom K) := by
  intro p q h
  have h0 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h1 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp only [coe_torusHom, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem torusHom_mem_upperTriangular (p : Kˣ × Kˣ) :
    torusHom K p ∈ LinearFlag.upperTriangular 3 K := fun i j hij => by
  rw [coe_torusHom]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem exists_torus_mul {b : Matrix.SpecialLinearGroup (Fin 3) K}
    (hb : b ∈ LinearFlag.upperTriangular 3 K) :
    ∃ p : Kˣ × Kˣ, ∃ u ∈ LinearFlag.unitriangular 3 K, b = torusHom K p * u := by
  have hbU : (b : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun _ _ h => hb _ _ h
  have hdet : (b : Matrix (Fin 3) (Fin 3) K) 0 0 * (b : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (b : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := b.prop
    rw [Matrix.det_of_isUpperTriangular hbU, Fin.prod_univ_three] at h
    exact h
  have h0 : (b : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h1 : (b : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  set p : Kˣ × Kˣ := (Units.mk0 _ h0, Units.mk0 _ h1) with hp
  set d := torusHom K p with hd
  have hdU : (d : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    fun _ _ h => torusHom_mem_upperTriangular p _ _ h
  have hdb : ∀ i, (d : Matrix (Fin 3) (Fin 3) K) i i = (b : Matrix (Fin 3) (Fin 3) K) i i := by
    intro i
    rw [hd, coe_torusHom, Matrix.diagonal_apply_eq]
    fin_cases i
    · simp [hp]
    · simp [hp]
    · simp only [hp, Units.val_mk0, Fin.reduceFinMk, Matrix.cons_val]
      rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_of_mul_eq_one_left hdet]
  refine ⟨p, d⁻¹ * b, ⟨(LinearFlag.upperTriangular 3 K).mul_mem
    ((LinearFlag.upperTriangular 3 K).inv_mem (torusHom_mem_upperTriangular p)) hb, fun i => ?_⟩,
    (mul_inv_cancel_left d b).symm⟩
  have hdinv : (((d⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := LinearFlag.coe_inv_isUpperTriangular hdU
  rw [Matrix.SpecialLinearGroup.coe_mul,
    LinearFlag.mul_apply_self_of_isUpperTriangular hdinv hbU, ← hdb, mul_comm]
  exact LinearFlag.coe_inv_apply_self_of_isUpperTriangular hdU i

theorem le_nPrime [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K) :
    n ≤ E3.nPrime X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  set U₀ := (LinearFlag.unitriangular 3 K).map SL3One.rho with hU₀
  have hU₀L : U₀ ≤ pairSL K := by
    rw [← SL3One.range_rho]
    exact Subgroup.map_le_range _ _
  have hU₀p : IsPGroup 2 U₀ := by
    rw [hU₀, ← hP₀]
    exact P₀.isPGroup'.map _
  obtain ⟨S, hS, hUS⟩ := exists_isSylowIn_ge 2 (hU₀L.trans hX1) hU₀p
  have hSU : S ⊓ pairSL K = U₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hUS hU₀L)
    obtain ⟨g, rfl⟩ := SL3One.exists_rho_of_mem hx.2
    have hQ : IsPGroup 2 ((S ⊓ pairSL K).comap SL3One.rho) :=
      hS.isPGroup.to_inf_left.comap_of_injective _ SL3One.rho_injective
    have hle : (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) ≤
        (S ⊓ pairSL K).comap SL3One.rho := by
      rw [hP₀]
      intro u hu
      exact ⟨hUS ⟨u, hu, rfl⟩, SL3One.rho_mem_pairSL u⟩
    have heq := P₀.is_maximal' hQ hle
    have hg : g ∈ (S ⊓ pairSL K).comap SL3One.rho := hx
    rw [heq, hP₀] at hg
    exact ⟨g, hg, rfl⟩
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (U₀ : Set (MulAut (PairMod K))) := by
    intro s hs
    rw [← hSU, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x,
      Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) x]
  set B := (torusHom K).range.map SL3One.rho with hB
  have hSB : (S : Set (MulAut (PairMod K))) * B ⊆ B * S := by
    rintro _ ⟨s, hs, _, ⟨_, ⟨p, rfl⟩, rfl⟩, rfl⟩
    have h1 : s * SL3One.rho (torusHom K p) * s⁻¹ ∈ pairSL K :=
      (Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) _).mp (SL3One.rho_mem_pairSL _)
    obtain ⟨b, hb⟩ := SL3One.exists_rho_of_mem h1
    have hbN : SL3One.rho b ∈ Subgroup.normalizer (U₀ : Set (MulAut (PairMod K))) := by
      rw [hb]
      have htN : SL3One.rho (torusHom K p) ∈
          Subgroup.normalizer (U₀ : Set (MulAut (PairMod K))) := by
        apply Subgroup.le_normalizer_map
        refine ⟨torusHom K p, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearFlag.normalizer_unitriangular]
        exact torusHom_mem_upperTriangular p
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSN s hs) htN)
        (Subgroup.inv_mem _ (hSN s hs))
    have hbU : b ∈ LinearFlag.upperTriangular 3 K := by
      rw [← LinearFlag.normalizer_unitriangular, Subgroup.mem_normalizer_iff]
      intro u
      have h2 := Subgroup.mem_normalizer_iff.mp hbN (SL3One.rho u)
      rw [Subgroup.mem_map_iff_mem SL3One.rho_injective, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem SL3One.rho_injective] at h2
      exact h2
    obtain ⟨p', u, hu, hbe⟩ := exists_torus_mul hbU
    refine ⟨SL3One.rho (torusHom K p'), ⟨_, ⟨p', rfl⟩, rfl⟩, SL3One.rho u * s,
      S.mul_mem (hUS ⟨u, hu, rfl⟩) hs, ?_⟩
    change SL3One.rho (torusHom K p') * (SL3One.rho u * s) = s * SL3One.rho (torusHom K p)
    rw [← mul_assoc, ← map_mul, ← hbe, hb]
    group
  have hBS : (B : Set (MulAut (PairMod K))) * S = S * B := mul_comm_of_subset hSB
  have hBX : B ≤ X := by
    refine le_trans ?_ hX1
    rw [← SL3One.range_rho]
    exact Subgroup.map_le_range _ _
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩ _ ⟨_, ⟨q, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm p q]
  have hq : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hBodd : Odd (Nat.card B) := by
    have h1 : Nat.card B = Nat.card (torusHom K).range :=
      Subgroup.card_map_of_injective SL3One.rho_injective
    have h2 : Nat.card (torusHom K).range = Nat.card (Kˣ × Kˣ) :=
      (Nat.card_congr (MonoidHom.ofInjective torusHom_injective).toEquiv).symm
    rw [h1, h2, Nat.card_prod, Nat.card_units, hK]
    exact hq.mul hq
  let δ : Kˣ →* Kˣ × Kˣ := MonoidHom.prod (MonoidHom.id Kˣ) invMonoidHom
  set φ : Kˣ →* MulAut (PairMod K) := SL3One.rho.comp ((torusHom K).comp δ) with hφ
  have hφi : Function.Injective φ := SL3One.rho_injective.comp (torusHom_injective.comp
    fun a b h => (Prod.ext_iff.mp h).1)
  have hYB : φ.range ≤ B := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, ⟨δ t, rfl⟩, rfl⟩
  have hYc : Nat.card φ.range = 2 ^ n - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_units, hK]
  have hYcyc : IsCyclic φ.range := isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact E3.le_nPrime hYB hBX hYcyc hYc hBab hBodd hS hBS

theorem nPrime_eq [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K) :
    E3.nPrime X = n :=
  le_antisymm (nPrime_le hn hK hX1 hX2) (le_nPrime (by omega) hK hX1 hX2)

theorem H4_SL3Pair_nPrime {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hn : 2 ≤ n) (hreal : BinaryNaturalSL H V₁ ⊥ 3 n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : E3.nPrime M = n := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have h1 : pairSL K ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq hn hK h1 h2

end SL3Pair

end H

end CFSG.Quasithin
