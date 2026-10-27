module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.E6Three

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Module

variable {W : Type*} [CommGroup W]

omit [CommGroup W] in
theorem mem_fixV_zpowers_iff' [CommGroup W] {b : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers b) ↔ b w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem two_mul_rkIdx_fixV_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {b : MulAut W}
    (hb : b * b = 1) : 2 * rkIdx (fixV (Subgroup.zpowers b)) ≤ rk W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fixV (Subgroup.zpowers b) with hF
  let f : W →* W :=
    { toFun := fun w => b w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        show b (v * w) * (v * w)⁻¹ = b v * v⁻¹ * (b w * w⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hf : ∀ w, f w = b w * w⁻¹ := fun _ => rfl
  have hker : f.ker = F := by
    ext w
    rw [MonoidHom.mem_ker, hF, mem_fixV_zpowers_iff', hf]
    exact mul_inv_eq_one
  have hinv : ∀ x : W, x⁻¹ = x := fun x => by
    have hx := hW x
    rw [sq] at hx
    exact inv_eq_of_mul_eq_one_right hx
  have hrange : f.range ≤ F := by
    rintro _ ⟨w, rfl⟩
    rw [hF, mem_fixV_zpowers_iff', hf]
    have hbb : b (b w) = w := by
      have := congrArg (fun φ : MulAut W => φ w) hb
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, hbb, hinv (b w), hinv w, mul_comm]
  have hidx : F.index = Nat.card f.range := by rw [← hker]; exact Subgroup.index_ker f
  have hdvd : F.index ∣ Nat.card F := hidx ▸ Subgroup.card_dvd_of_le hrange
  have h2 := rk_add_rkIdx F
  have hle : rkIdx F ≤ rk ↥F := by
    unfold rkIdx rk
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').1 (pow_padicValNat_dvd.trans hdvd)
  omega

theorem two_mul_mParam_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : Even (Nat.card X)) : 2 * E3.mParam X ≤ rk W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W) := Finite.of_injective (fun φ : MulAut W => (φ : W → W))
    DFunLike.coe_injective
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.1 hX)
  have ht' : orderOf (t : MulAut W) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htt : (t : MulAut W) * t = 1 := by rw [← sq, ← ht']; exact pow_orderOf_eq_one _
  have hmem : rkIdx (fixV (Subgroup.zpowers (t : MulAut W))) ∈ {n : ℕ | ∃ s ∈ X, orderOf s = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers s))} := ⟨t, t.2, ht', rfl⟩
  have hle : E3.mParam X ≤ rkIdx (fixV (Subgroup.zpowers (t : MulAut W))) := by
    simp only [E3.mParam, hX, ↓reduceIte]
    exact Nat.sInf_le hmem
  have := two_mul_rkIdx_fixV_le hW htt
  omega

end Module

section Sixteen

variable {G : Type} [Group G] [Finite G] {T M V W : Subgroup G}

@[expose] def HypE615 (hV : IsElemAbelian 2 V) (M : Subgroup G) : Prop :=
  1 < E3.rParam V ∨ 2 < E3.mParam (autI hV M)

omit [Finite G] in
theorem mQuot_bot_eq_rk (hV : IsElemAbelian 2 V) : E3.mQuot V ⊥ = rk (IntMod V hV) := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]
  rfl

omit [Finite G] in
theorem rParam_le_mQuot (hUV : W ≤ V)
    (hC : ¬ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    E3.rParam V ≤ E3.mQuot V W :=
  iInf₂_le W ⟨hUV, hC⟩

theorem one_le_rParam (h : HypE61 T M V) : 1 ≤ E3.rParam V := by
  unfold E3.rParam
  refine le_iInf₂ fun U hU => ?_
  have h0 : E3.mQuot V U ≠ 0 := fun h0 => hU.2 (by
    rw [(E3.mQuot_eq_zero_iff h.isPGroup_V hU.1).1 h0]
    exact Subgroup.centralizer_le_normalizer _)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

theorem HypE61.charTwo_M (h : HypE61 T M V) : CharTwo M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.qtke.2.1 M h.inM.1.1 ⟨h.sylow.1.toSylow h.sylow.2, h.inM.2⟩

theorem e6_6_two (h : HypE61 T M V) {A : Subgroup G} (hAM : A ≤ M) (hA : IsPGroup 2 A) :
    CharTwo (M ⊓ Subgroup.centralizer (A : Set G)) :=
  CT.CharTwo.inf_centralizer h.charTwo_M hAM hA

theorem e6_16_one (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (h15 : HypE615 hV M)
    (hWV : W ≤ V) (hW : E3.mQuot V W = 1) (hC : ¬ Subgroup.centralizer (W : Set G) ≤ M) :
    E3.rParam V = 1 ∧ 2 < E3.mParam (autI hV M) ∧ W ∈ gammaE64 V M := by
  have hCN : ¬ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hC (hle.trans h.normalizer_le)
  have hr1 : E3.rParam V ≤ 1 := by
    have h1 := rParam_le_mQuot hWV hCN
    rw [hW] at h1
    exact_mod_cast h1
  have hr : E3.rParam V = 1 := le_antisymm hr1 (one_le_rParam h)
  have hm : 2 < E3.mParam (autI hV M) := by
    rcases h15 with h15 | h15
    · rw [hr] at h15
      exact absurd h15 (lt_irrefl 1)
    · exact h15
  have hW1 : W ≠ ⊥ := by
    rintro rfl
    have h1 := mQuot_bot_eq_rk hV
    have h2 := E3.mParam_le_rk (autI hV M)
    omega
  exact ⟨hr, hm, mem_gammaE64_of_mQuot_lt hV h hWV hW1 hC (by omega)⟩

theorem e6_16_two (h : HypE61 T M V) (hWV : W ≤ V)
    (hW : ¬ CharTwo (Subgroup.centralizer (W : Set G))) :
    ¬ Subgroup.centralizer (W : Set G) ≤ M := by
  intro hle
  apply hW
  have h1 := e6_6_two h (hWV.trans (h.le.trans h.inM.2)) (h.isPGroup_V.to_le hWV)
  rwa [inf_eq_right.2 hle] at h1

theorem e6_17 (h311 : Theorem311Stmt) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (h15 : HypE615 hV M) (hr : E3.rParam V = 1) :
    2 < E3.mParam (autI hV M) ∧ 6 ≤ E3.mQuot V ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : 2 < E3.mParam (autI hV M) := by
    rcases h15 with h15 | h15
    · rw [hr] at h15
      exact absurd h15 (lt_irrefl 1)
    · exact h15
  refine ⟨hm, ?_⟩
  rw [mQuot_bot_eq_rk hV]
  by_cases hev : Even (Nat.card (autI hV M))
  · have := two_mul_mParam_le (W := IntMod V hV) IntMod.sq_eq_one hev
    omega
  · exfalso
    have hTC : T ≤ Subgroup.centralizer (V : Set G) := by
      have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.normal
      have hP : IsPGroup 2 (autI hV T) := B6.isPGroup_autOn h.sylow.1 V
      have hdvd : Nat.card (autI hV T) ∣ Nat.card (autI hV M) :=
        Subgroup.card_dvd_of_le (autI_mono hV h.inM.2)
      have h1 : Nat.card (autI hV T) = 1 := by
        rcases hP.card_eq_or_dvd with h1 | h2
        · exact h1
        · exact absurd (even_iff_two_dvd.2 (h2.trans hdvd)) hev
      exact (autI_eq_bot_iff hV hTN).1 (Subgroup.card_eq_one.1 h1)
    obtain ⟨U, hUV, hCN, hUr⟩ := exists_eq_rParam' (V := V) (by rw [hr]; exact ENat.one_ne_top)
    have hU1' : E3.mQuot V U = 1 := by
      rw [hr] at hUr
      exact_mod_cast hUr
    have hmrk : E3.mParam (autI hV M) = rk (IntMod V hV) := by
      simp only [E3.mParam, hev, ↓reduceIte]
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      rw [mQuot_bot_eq_rk hV] at hU1'
      omega
    have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun hCM =>
      hCN fun g hg => inf_centralizer_le_normalizer h hUV hU1 ⟨hCM hg, hg⟩
    have hUΓ : U ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hUV hU1 hCM (by omega)
    have hTU : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUV (hTC ht))
    exact hCM (e6_13 h311 h hUV hU1 hUΓ.2.2.2 hTU)

end Sixteen

end E6

end CFSG.Quasithin
