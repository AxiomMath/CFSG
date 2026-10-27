module

public import CFSG.Quasithin.Background.HSz
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj

public section

namespace CFSG.Quasithin

namespace B45Sz

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.H

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem two_mul_rk_le_rkIdx (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : Subgroup (MulAut (StdMod (Fin 4) K))}
    (hAN : A ≤ natNorm (suzukiGroup a K)) (hA1 : A ≠ ⊥) (hAel : IsElemAbelian2 A) :
    2 * rk ↥A ≤ rkIdx (fixV A) := by
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have hrk : rk ↥A ≤ 2 * a + 1 := (rk_le_pRank le_rfl hAel).trans (Sz.pRank_le ha hK hAN)
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have hbo : orderOf (b : MulAut (StdMod (Fin 4) K)) = 2 :=
    orderOf_eq_prime (hAel.2 b b.2) (fun h => hb1 (Subtype.ext h))
  have h2 := Sz.rkIdx_fixV_of_involution ha hK (hAN b.2) hbo
  have h3 : rkIdx (fixV (Subgroup.zpowers (b : MulAut (StdMod (Fin 4) K)))) ≤
      rkIdx (fixV A) :=
    rkIdx_anti (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr b.2 hy))
  omega

variable (a K) in
@[expose] noncomputable def rootImage :
    Subgroup (MulAut (StdMod (Fin 4) K)) :=
  (suzukiZ0 a K).map (natAut (suzukiGroup a K))

omit [Finite K] in
theorem rootImage_le_natImage :
    rootImage a K ≤ natImage (suzukiGroup a K) :=
  Subgroup.map_le_range _ _

omit [Finite K] in
theorem toAddMap_natAut_suzukiSElt_zero (v : K)
    (x : Fin 4 → K) :
    toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 v)) x =
      ![x 0, x 1, v * x 0 + x 2, v ^ 2 ^ (a + 1) * x 0 + v * x 1 + x 3] := by
  rw [toAddMap_natAut, coe_suzukiSElt, Sz.suzukiS_mulVec]
  have hθ : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  ext i
  fin_cases i <;> simp [suzukiN, zero_pow hθ]

theorem mem_rootImage_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : MulAut (StdMod (Fin 4) K)} :
    g ∈ rootImage a K ↔ ∃ v : K, natAut (suzukiGroup a K) (suzukiSElt a K 0 v) = g := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hz
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, (mem_suzukiZ0_iff hK).mpr ⟨v, rfl⟩, rfl⟩

theorem mem_fixV_rootImage_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : StdMod (Fin 4) K} :
    x ∈ fixV (rootImage a K) ↔
      Multiplicative.toAdd x 0 = 0 ∧ Multiplicative.toAdd x 1 = 0 := by
  constructor
  · intro hx
    have h := hx _ ((mem_rootImage_iff hK).mpr ⟨1, rfl⟩)
    have h' : toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 1))
        (Multiplicative.toAdd x) = Multiplicative.toAdd x := congrArg Multiplicative.toAdd h
    rw [toAddMap_natAut_suzukiSElt_zero] at h'
    have h2 := congrFun h' 2
    have h3 := congrFun h' 3
    simp only [Matrix.cons_val, one_mul, one_pow] at h2 h3
    have e0 : Multiplicative.toAdd x 0 = 0 := by simpa using h2
    refine ⟨e0, ?_⟩
    simpa [e0] using h3
  · rintro ⟨h0, h1⟩ g hg
    obtain ⟨v, rfl⟩ := (mem_rootImage_iff hK).mp hg
    apply Multiplicative.toAdd.injective
    change toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 v)) (Multiplicative.toAdd x) = _
    rw [toAddMap_natAut_suzukiSElt_zero, h0, h1]
    ext i
    fin_cases i <;> simp [h0, h1]

theorem fixV_rootImage (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    fixV (rootImage a K) =
      fixV (Subgroup.zpowers (natAut (suzukiGroup a K) (suzukiSElt a K 0 1))) := by
  ext x
  rw [mem_fixV_rootImage_iff hK, mem_fixV_zpowers_iff]
  constructor
  · rintro ⟨h0, h1⟩
    apply Multiplicative.toAdd.injective
    change toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 1)) (Multiplicative.toAdd x) = _
    rw [toAddMap_natAut_suzukiSElt_zero]
    ext i
    fin_cases i <;> simp [h0, h1]
  · intro h
    have h' : toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 1))
        (Multiplicative.toAdd x) = Multiplicative.toAdd x := congrArg Multiplicative.toAdd h
    rw [toAddMap_natAut_suzukiSElt_zero] at h'
    have h2 := congrFun h' 2
    have h3 := congrFun h' 3
    simp only [Matrix.cons_val, one_mul, one_pow] at h2 h3
    have e0 : Multiplicative.toAdd x 0 = 0 := by simpa using h2
    refine ⟨e0, ?_⟩
    simpa [e0] using h3

theorem rkIdx_fixV_rootImage (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rkIdx (fixV (rootImage a K)) = 2 * (2 * a + 1) := by
  rw [fixV_rootImage hK, Sz.rkIdx_fixV_suzukiSElt hK]

theorem rk_rootImage (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rk ↥(rootImage a K) = 2 * a + 1 := by
  unfold rk rootImage
  rw [Subgroup.card_map_of_injective (natAut_injective _),
    CFSG.QuasithinUnique.Setup.Family.card_suzukiZ0 hK, padicValNat.prime_pow]

theorem isElemAbelian2_rootImage
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : IsElemAbelian2 (rootImage a K) := by
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  have hθ : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨v, rfl⟩ := (mem_rootImage_iff hK).mp hx
    obtain ⟨w, rfl⟩ := (mem_rootImage_iff hK).mp hy
    rw [← map_mul, ← map_mul, suzukiSElt_mul hK, suzukiSElt_mul hK]
    simp [zero_pow hθ, add_comm]
  · obtain ⟨v, rfl⟩ := (mem_rootImage_iff hK).mp hx
    rw [← map_pow, sq, suzukiSElt_mul hK]
    simp [zero_pow hθ, CharTwo.add_self_eq_zero, suzukiSElt_zero_zero hK]

theorem rootImage_ne_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rootImage a K ≠ ⊥ := by
  intro h
  have hmem : natAut (suzukiGroup a K) (suzukiSElt a K 0 1) ∈ rootImage a K :=
    (mem_rootImage_iff hK).mpr ⟨1, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun g : MulAut (StdMod (Fin 4) K) =>
    toAddMap g (Pi.single 0 1) 2) hmem
  simp only [toAddMap_natAut_suzukiSElt_zero, toAddMap_one] at h1
  simp at h1

theorem isQuadratic_rootImage
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : IsQuadratic (rootImage a K) := by
  unfold IsQuadratic commV
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, x, rfl⟩
  obtain ⟨v, rfl⟩ := (mem_rootImage_iff hK).mp hg
  rw [SetLike.mem_coe, mem_fixV_rootImage_iff hK]
  have e : Multiplicative.toAdd (natAut (suzukiGroup a K) (suzukiSElt a K 0 v) x * x⁻¹) =
      toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 v)) (Multiplicative.toAdd x) -
        Multiplicative.toAdd x := by
    rw [toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rfl
  rw [e, toAddMap_natAut_suzukiSElt_zero]
  simp

theorem qOf_qhatOf_eq_two {V : Type} [CommGroup V] [Finite V]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V))) {f : ℕ}
    (hL : BinaryNaturalSz L ⊤ ⊥ f) :
    qOf G = ((2 : ℚ) : WithTop ℚ) ∧ qhatOf G = ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hL
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLG hGN
  have : Finite (StdMod (Fin 4) K) := Finite.of_equiv V e.toEquiv
  have hq : qOf G = qOf (G.map (congrHom e)) := (H13.kq_map_congr e G 2).symm
  have hqh : qhatOf G = qhatOf (G.map (congrHom e)) := (H13.kq_map_congr e G 3).symm
  set X := G.map (congrHom e) with hX
  have hlow : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf X := by
    refine le_kq_iff.mpr fun A hA _ => ?_
    have h := two_mul_rk_le_rkIdx ha hK (hA.1.trans h2) hA.2.1 hA.2.2
    have hmul := hA.rAV_mul
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
    have h' : (2 : ℚ) * (rk ↥A : ℚ) ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast h
    rw [← hmul] at h'
    exact le_of_mul_le_mul_right h' hpos
  have hup : qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
    refine kq_le_iff.mpr ⟨rootImage a K, ⟨rootImage_le_natImage.trans h1, rootImage_ne_bot hK,
      isElemAbelian2_rootImage hK⟩, (isQuadratic_iff_commSeries_two _).mp
        (isQuadratic_rootImage hK), ?_⟩
    unfold rAV
    rw [rkIdx_fixV_rootImage hK, rk_rootImage hK]
    have hn : ((2 * a + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have hle := qhatOf_le_qOf X
  have hq2 : qOf X = ((2 : ℚ) : WithTop ℚ) := le_antisymm hup (hlow.trans hle)
  have hqh2 : qhatOf X = ((2 : ℚ) : WithTop ℚ) := le_antisymm (hle.trans hup) hlow
  exact ⟨hq.trans hq2, hqh.trans hqh2⟩

end B45Sz

end CFSG.Quasithin
