module

public import CFSG.Quasithin.EmptyFaithful.S146zRSL2Set
public import CFSG.Quasithin.EmptyFaithful.S146zSAut
public import CFSG.Quasithin.EmptyFaithful.S146zQArith

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Lift

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_le_sup_of_isPGroup_quotient (S : Setting146 G T M) {K : Subgroup G}
    [(imageOTwoQuot (mcOf T) K).Normal]
    (hq : IsPGroup 2 (OTwoQuot (mcOf T) ⧸ imageOTwoQuot (mcOf T) K)) :
    mcOf T ≤ K ⊔ T := by
  classical
  have hHT : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hPi : ¬ 2 ∣ (imageOTwoQuot (mcOf T) T).index := by
    have := (q_hatT_sylow S).2.2
    rwa [show ((imageOTwoQuot (mcOf T) T).subgroupOf ⊤).index = (imageOTwoQuot (mcOf T) T).index
      from Subgroup.relIndex_top_right _] at this
  intro g hg
  obtain ⟨n, hn, t', ht', hx⟩ := q_exists_mul_of_sylow hq hPi (qPi (mcOf T) ⟨g, hg⟩)
  obtain ⟨k, hk, rfl⟩ := hn
  obtain ⟨τ, hτ, rfl⟩ := ht'
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hτT : (τ : G) ∈ T := Subgroup.mem_subgroupOf.mp hτ
  have hz : (⟨g, hg⟩ : ↥(mcOf T))⁻¹ * (k * τ) ∈ CFSG.Open.pCore 2 ↥(mcOf T) := by
    have h1 : qPi (mcOf T) ⟨g, hg⟩ = qPi (mcOf T) (k * τ) := by
      rw [hx]
      exact (map_mul (qPi (mcOf T)) k τ).symm
    exact QuotientGroup.eq.mp h1
  have hzT : g⁻¹ * ((k : G) * (τ : G)) ∈ T :=
    S.pCoreOf_le_T hHT ⟨_, hz, rfl⟩
  have e : g = (k : G) * ((τ : G) * (g⁻¹ * ((k : G) * (τ : G)))⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hkK (T.mul_mem hτT (T.inv_mem hzT))

end Lift

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G}

theorem q_L216_index_and_sup (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5) (hmax : PMaximal T M 5)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 ∧
      mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T := by
  classical
  have hq : 4 ≤ Nat.card (GaloisField 2 4) := by rw [SBc16.card_galoisField16]; norm_num
  have hpF : 5 ∣ Nat.card (GaloisField 2 4) - 1 := by rw [SBc16.card_galoisField16]; norm_num
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp (conjSub_mem_cComp_of_mem hK₁ hsG)
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) = 4080 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact SBc16.card_L216
  have hbot : imageOTwoQuot (mcOf T) K₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hA : Nat.card (MulAut ↥(imageOTwoQuot (mcOf T) K₁)) =
      2 ^ 2 * Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by
    rw [← Nat.card_congr (MulAut.congr e1).toEquiv, ← Nat.card_congr e1.toEquiv,
      SBc16.card_mulAut_L216, SBc16.card_L216]
    norm_num
  have hidx := q_index_dvd_of_card_aut_pow hF hbot hA
  have hsup : imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) =
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) := by
    rw [hKz, q_image_sup hK₁G hK₂G]
  rw [hsup] at hidx
  have hidx32 : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 2 ^ 5 :=
    hidx
  have : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).Normal := by
    rw [← hsup]
    exact hF.normal
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 5)).mp hidx32
  have hpq : IsPGroup 2 (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) :=
    IsPGroup.of_card (n := j) (by rw [← Subgroup.index_eq_card, hj])
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := by
    rw [hKz]
    exact sup_le hK₁G hK₂G
  refine ⟨by simpa using hidx32, le_antisymm ?_ (sup_le hKzG ?_)⟩
  · exact q_le_sup_of_isPGroup_quotient S hpq
  · exact hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)

theorem q_stage14614C4_data (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5) (hmax : PMaximal T M 5)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁) {m : ℕ} (hm : 2 ≤ m)
    (hpm : 5 ∣ 2 ^ m - 1)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) :
    m = 4 ∧ mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
      (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 := by
  classical
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpF : 5 ∣ Nat.card (GaloisField 2 m) - 1 := by rw [hcardF]; exact hpm
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hKle := q_hatK_le hK₁ hsG hKz
  have hm4 : m = 4 := by
    refine m_eq_four_of_prime_dvd hm hpm fun r hr hd => ?_
    rcases q_prime_dvd_pred S hred hmax hF hq e1.symm hKle hr (by rw [hcardF]; exact hd) with h | h
    · exact Or.inl h
    · exact Or.inr h.2
  subst hm4
  obtain ⟨hidx, hII⟩ := q_L216_index_and_sup h36 hlist iS S hred hmax hK₁ hsT hsN hKz e
  exact ⟨rfl, hII, hidx⟩

end Main

end CFSG.Quasithin
