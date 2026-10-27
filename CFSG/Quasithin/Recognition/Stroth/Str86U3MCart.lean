module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model3
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.SteinbergCBTwistedField
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement Matrix

variable {K : Type} [Field K] [Finite K]

noncomputable section

theorem toAdd_matAut {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (g : GL ι K) (v : H.StdMod ι K) :
    Multiplicative.toAdd (H.matAut g v) = (g : Matrix ι ι K) *ᵥ Multiplicative.toAdd v := by
  rw [← ofAdd_toAdd v]
  exact H.toAddMap_matAut g (Multiplicative.toAdd v)

theorem exists_uJGL_zero_of_sq_eq_one [CharP K 2] {k : ℕ}
    (hK : Nat.card K = (2 ^ k) ^ 2)
    {y : GL (Fin 3) K} (hy : y ∈ H.SU3.ujSub k K) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ b : K, b ≠ 0 ∧ y = H.SU3.uJGL k 0 b := by
  obtain ⟨a, b, -, rfl⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hy
  have hsq : H.SU3.uJGL k (a + a) (b + b + a * H.SU3.bar k a) = 1 := by
    rw [← uJGL_mul]
    exact hy2
  rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add] at hsq
  have h02 : a * H.SU3.bar k a = 0 := by
    have h := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K) 0 2)) hsq
    simpa [H.SU3.coe_uJGL, H.SU3.uJMat] using h
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h02 with h | h
    · exact h
    · rw [H.SU3.bar_apply] at h
      exact (pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h
  refine ⟨b, ?_, by rw [ha]⟩
  intro hb
  apply hy1
  rw [ha, hb]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.SU3.coe_uJGL, H.SU3.uJMat]

theorem matAut_uJGL_zero_fix_iff [CharP K 2] {k : ℕ} {b : K} (hb : b ≠ 0)
    (v : H.StdMod (Fin 3) K) :
    H.matAut (H.SU3.uJGL k 0 b) v = v ↔ (Multiplicative.toAdd v) 2 = 0 := by
  constructor
  · intro hv
    have h := congrArg (fun w : H.StdMod (Fin 3) K => (Multiplicative.toAdd w) 0) hv
    rw [toAdd_matAut (H.SU3.uJGL k 0 b) v, H.SU3.coe_uJGL, uJMat_mulVec] at h
    have hb2 : b * (Multiplicative.toAdd v) 2 = 0 := by
      apply add_left_cancel (a := (Multiplicative.toAdd v) 0)
      simpa using h
    exact (mul_eq_zero.mp hb2).resolve_left hb
  · intro hv2
    apply Multiplicative.toAdd.injective
    rw [toAdd_matAut (H.SU3.uJGL k 0 b) v, H.SU3.coe_uJGL, uJMat_mulVec]
    ext i
    fin_cases i <;> simp [hv2]

theorem natImage_ujSub_exists_normalizer_mod_fix [CharP K 2] {k : ℕ} (hk : 2 ≤ k)
    (hK : Nat.card K = (2 ^ k) ^ 2)
    {y : MulAut (H.StdMod (Fin 3) K)} (hy : y ∈ H.natImage (H.SU3.ujSub k K))
    (hy2 : y * y = 1) (hy1 : y ≠ 1)
    {X1 X2 : H.StdMod (Fin 3) K} (hX1 : y X1 ≠ X1) (hX2 : y X2 ≠ X2) :
    ∃ A ∈ H.natImage (su3Anti K k) ⊓
        Subgroup.normalizer (H.natImage (H.SU3.ujSub k K) :
          Set (MulAut (H.StdMod (Fin 3) K))),
      y (A X1 * X2⁻¹) = A X1 * X2⁻¹ := by
  rw [H.natImage_eq_map] at hy
  obtain ⟨y0, hy0, rfl⟩ := hy
  have hy02 : y0 * y0 = 1 := by
    apply H.matHom_injective
    simpa using hy2
  have hy01 : y0 ≠ 1 := by
    intro h
    apply hy1
    rw [h, map_one]
  obtain ⟨b, hb, rfl⟩ := exists_uJGL_zero_of_sq_eq_one (K := K) (k := k) hK hy0 hy02 hy01
  have hx1 : (Multiplicative.toAdd X1) 2 ≠ 0 := by
    intro h
    exact hX1 ((matAut_uJGL_zero_fix_iff (k := k) hb X1).mpr h)
  have hx2 : (Multiplicative.toAdd X2) 2 ≠ 0 := by
    intro h
    exact hX2 ((matAut_uJGL_zero_fix_iff (k := k) hb X2).mpr h)
  obtain ⟨h, hh, hsec⟩ := u3_cartan_transitive_mod_perp (F := K) hk hK
    (su3Anti K k ⊓ Subgroup.normalizer (H.SU3.ujSub k K : Set (GL (Fin 3) K)))
    (fun n hn => ⟨1, Subgroup.one_mem _, n, hn, (one_mul n).symm⟩)
    (Multiplicative.toAdd X1) (Multiplicative.toAdd X2) hx1 hx2
  refine ⟨H.matAut h, ⟨?_, ?_⟩, ?_⟩
  · rw [H.natImage_eq_map]
    exact ⟨h, hh.1, rfl⟩
  · rw [H.natImage_eq_map]
    exact Subgroup.le_normalizer_map (H := H.SU3.ujSub k K) H.matHom ⟨h, hh.2, rfl⟩
  · have hX2inv : X2⁻¹ = X2 :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using H.SL3One.stdMod_sq_eq_one X2)
    rw [H.matHom_apply, matAut_uJGL_zero_fix_iff (k := k) hb, hX2inv, toAdd_mul,
      toAdd_matAut h X1, Pi.add_apply, hsec]
    exact CharTwo.add_self_eq_zero _

theorem natImage_statedSU_exists_normalizer_mod_fix {k : ℕ}
    (hk : 2 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    {T : Subgroup (MulAut (H.StdMod (Fin 3) K))}
    (hTL : T ≤ H.natImage (StatedSU 3 (2 ^ k) K)) (hT : IsPGroup 2 T)
    (hTc : (2 ^ k) ^ 3 ≤ Nat.card T)
    {u : MulAut (H.StdMod (Fin 3) K)} (huT : u ∈ T) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    (2 ^ k) ^ 2 ≤ (fixV (Subgroup.zpowers u)).index ∧
      ∀ w₁ w₂ : H.StdMod (Fin 3) K, u w₁ ≠ w₁ → u w₂ ≠ w₂ →
        ∃ n ∈ H.natImage (StatedSU 3 (2 ^ k) K) ⊓
            Subgroup.normalizer (T : Set (MulAut (H.StdMod (Fin 3) K))),
          u (n w₁ * w₂⁻¹) = n w₁ * w₂⁻¹ := by
  haveI : CharP K 2 :=
    CFSG.Quasithin.SteinbergCB.charP_two_of_card (by omega) hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup (MulAut (H.StdMod (Fin 3) K)) :=
    H.natImage (StatedSU 3 (2 ^ k) K)
  let U0 : Subgroup (MulAut (H.StdMod (Fin 3) K)) := H.natImage (H.SU3.ujSub k K)
  let U1 : Subgroup (MulAut (H.StdMod (Fin 3) K)) := H.natImage (H.SU3.uiSub k K)
  let c : MulAut (H.StdMod (Fin 3) K) := H.matAut (H.SU3.wittGL (K := K))
  have hV2 : ∀ v : H.StdMod (Fin 3) K, v ^ 2 = 1 := fun v => H.SL3One.stdMod_sq_eq_one v
  have huord : orderOf u = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact hu2
    · exact hu1
  have hcodim : 2 * k ≤ rkIdx (fixV (Subgroup.zpowers u)) :=
    H.SU3.le_rkIdx_fixV_of_involution (n := k) (by omega) hK
      (hTL.trans Subgroup.le_normalizer) huT huord
  have hcardL : Nat.card L = Nat.card (StatedSU 3 (2 ^ k) K) := by
    dsimp [L]
    rw [H.natImage_eq_map]
    exact Subgroup.card_map_of_injective H.matHom_injective
  have hL2 : (Nat.card L).factorization 2 = 3 * k := by
    have h2 := H.SU3.card_statedSU_two (K := K) (n := k) (by omega) hK
    have h2' : 2 ^ (Nat.card L).factorization 2 = 2 ^ (3 * k) := by
      rw [hcardL, h2, ← pow_mul, mul_comm k 3]
    exact Nat.pow_right_injective (by norm_num) h2'
  have hTcard : Nat.card T = (2 ^ k) ^ 3 := by
    obtain ⟨t, ht⟩ := hT.exists_card_eq
    have hdvd : 2 ^ t ∣ Nat.card L := by
      rw [← ht]
      exact Subgroup.card_dvd_of_le hTL
    have htle : t ≤ (Nat.card L).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos.ne')).mp hdvd
    have h3k : 3 * k ≤ t := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      calc 2 ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul, mul_comm k 3]
        _ ≤ Nat.card T := hTc
        _ = 2 ^ t := ht
    have ht3 : t = 3 * k := by
      apply le_antisymm _ h3k
      rw [hL2] at htle
      exact htle
    rw [ht, ht3, ← pow_mul, mul_comm k 3]
  have hTsyl : IsSylowIn 2 T L := by
    refine isSylowIn_of_card_eq hTL ?_
    rw [hTcard, hL2, ← pow_mul, mul_comm k 3]
  have huiCard : Nat.card (H.SU3.uiSub k K) = (2 ^ k) ^ 3 := by
    rw [IsSylowIn.card_eq (H.SU3.isSylowIn_uiSub (K := K) (n := k) (by omega) hK)]
    exact H.SU3.card_statedSU_two (K := K) (n := k) (by omega) hK
  have hU1le : U1 ≤ L := by
    dsimp [U1, L]
    rw [H.natImage_eq_map, H.natImage_eq_map]
    exact Subgroup.map_mono H.SU3.uiSub_le
  have hU1card : Nat.card U1 = (2 ^ k) ^ 3 := by
    dsimp [U1]
    rw [H.natImage_eq_map, Subgroup.card_map_of_injective H.matHom_injective, huiCard]
  have hU1syl : IsSylowIn 2 U1 L := by
    refine isSylowIn_of_card_eq hU1le ?_
    rw [hU1card, hL2, ← pow_mul, mul_comm k 3]
  obtain ⟨g, hgL, hgiff⟩ := Ch1Sec3.exists_conj_of_isSylowIn (p := 2) hU1syl hTsyl
  have hTmap : T = U1.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨g⁻¹ * x * g, (hgiff x).mp hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hgiff (g * y * g⁻¹)).mpr (by simpa [MulAut.conj_apply, mul_assoc] using hy)
  have hU1U0 : U1 = U0.map (MulAut.conj c).toMonoidHom := by
    dsimp [U1, U0, c]
    rw [H.natImage_eq_map, H.natImage_eq_map, H.SU3.uiSub, Subgroup.map_map,
      Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro s
    change H.matHom (H.SU3.wittGL * s * H.SU3.wittGL⁻¹) = MulAut.conj c (H.matHom s)
    rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
    rfl
  have hLanti : H.natImage (su3Anti K k) = L.map (MulAut.conj c⁻¹).toMonoidHom := by
    dsimp [L, c]
    rw [H.natImage_eq_map, H.natImage_eq_map, su3Anti, Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro s
    change H.matHom (H.SU3.wittGL⁻¹ * s * H.SU3.wittGL) = MulAut.conj c⁻¹ (H.matHom s)
    rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
    rfl
  have hLmap : L = (H.natImage (su3Anti K k)).map (MulAut.conj c).toMonoidHom := by
    rw [hLanti, Subgroup.map_map]
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom =
        MonoidHom.id (MulAut (H.StdMod (Fin 3) K)) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  let b : MulAut (H.StdMod (Fin 3) K) := g⁻¹ * u * g
  have hbU1 : b ∈ U1 := (hgiff u).mp huT
  have hbu : u = g * b * g⁻¹ := by simp [b, mul_assoc]
  have hb2 : b * b = 1 := by
    simp only [b]
    rw [show (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2]
    group
  have hb1 : b ≠ 1 := by
    intro h
    rw [hbu, h] at hu1
    exact hu1 (by group)
  rw [hU1U0] at hbU1
  obtain ⟨y, hyU0, hyb⟩ := Subgroup.mem_map.mp hbU1
  have hyb' : MulAut.conj c y = b := hyb
  have hb_eq : b = c * y * c⁻¹ := by
    rw [← hyb']
    exact MulAut.conj_apply c y
  have hy2 : y * y = 1 := by
    apply (MulAut.conj c).injective
    rw [map_mul, map_one, hyb', hb2]
  have hy1 : y ≠ 1 := by
    intro h
    apply hb1
    rw [hb_eq, h]
    group
  refine ⟨?_, ?_⟩
  · have hidx : (fixV (Subgroup.zpowers u)).index =
        2 ^ rkIdx (fixV (Subgroup.zpowers u)) := B1.index_eq_two_pow hV2 _
    calc (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm k 2]
      _ ≤ 2 ^ rkIdx (fixV (Subgroup.zpowers u)) :=
        pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hcodim
      _ = (fixV (Subgroup.zpowers u)).index := hidx.symm
  · intro w₁ w₂ hu1w1 hu1w2
    let X1 : H.StdMod (Fin 3) K := c⁻¹ (g⁻¹ w₁)
    let X2 : H.StdMod (Fin 3) K := c⁻¹ (g⁻¹ w₂)
    have hX1 : y X1 ≠ X1 := by
      intro hfix
      apply hu1w1
      calc u w₁ = g (b (g⁻¹ w₁)) := by simp [hbu, mul_assoc]
        _ = g (c (y X1)) := by rw [hb_eq]; simp [X1, mul_assoc]
        _ = g (c X1) := by rw [hfix]
        _ = w₁ := by simp [X1, mul_assoc]
    have hX2 : y X2 ≠ X2 := by
      intro hfix
      apply hu1w2
      calc u w₂ = g (b (g⁻¹ w₂)) := by simp [hbu, mul_assoc]
        _ = g (c (y X2)) := by rw [hb_eq]; simp [X2, mul_assoc]
        _ = g (c X2) := by rw [hfix]
        _ = w₂ := by simp [X2, mul_assoc]
    obtain ⟨A, hA, hAeq⟩ := natImage_ujSub_exists_normalizer_mod_fix (K := K) (k := k) hk hK
      hyU0 hy2 hy1 hX1 hX2
    have hA1L : c * A * c⁻¹ ∈ L := by
      rw [hLmap]
      exact ⟨A, hA.1, by simp [MulAut.conj_apply]⟩
    have hA1N : c * A * c⁻¹ ∈
        Subgroup.normalizer (U1 : Set (MulAut (H.StdMod (Fin 3) K))) := by
      rw [hU1U0, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨A, hA.2, by simp [MulAut.conj_apply]⟩
    have hnL : g * (c * A * c⁻¹) * g⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hgL hA1L) (L.inv_mem hgL)
    have hNmap := Subgroup.le_normalizer_map (H := U1) (MulAut.conj g).toMonoidHom
    rw [← hTmap] at hNmap
    have hnN : g * (c * A * c⁻¹) * g⁻¹ ∈
        Subgroup.normalizer (T : Set (MulAut (H.StdMod (Fin 3) K))) :=
      hNmap ⟨c * A * c⁻¹, hA1N, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine ⟨g * (c * A * c⁻¹) * g⁻¹, ⟨hnL, hnN⟩, ?_⟩
    have hz : (g * (c * A * c⁻¹) * g⁻¹) w₁ * w₂⁻¹ = g (c (A X1 * X2⁻¹)) := by
      calc (g * (c * A * c⁻¹) * g⁻¹) w₁ * w₂⁻¹
          = g (c (A X1)) * (g (c X2))⁻¹ := by simp [X1, X2, mul_assoc]
        _ = g (c (A X1 * X2⁻¹)) := by simp [mul_assoc]
    have hfix : u (g (c (A X1 * X2⁻¹))) = g (c (A X1 * X2⁻¹)) := by
      calc u (g (c (A X1 * X2⁻¹)))
          = g (b (g⁻¹ (g (c (A X1 * X2⁻¹))))) := by simp [hbu, mul_assoc]
        _ = g (b (c (A X1 * X2⁻¹))) := by simp
        _ = g (c (y (c⁻¹ (c (A X1 * X2⁻¹))))) := by rw [hb_eq]; simp [mul_assoc]
        _ = g (c (A X1 * X2⁻¹)) := by
          have hcz : c⁻¹ (c (A X1 * X2⁻¹)) = A X1 * X2⁻¹ := by
            change (c⁻¹ * c) (A X1 * X2⁻¹) = _
            rw [inv_mul_cancel]
            rfl
          rw [hcz, hAeq]
    rw [hz, hfix]

end

end CFSG.Quasithin.Stroth

end
