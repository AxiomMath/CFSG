module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg
public import CFSG.Quasithin.EmptyFaithful.S146P20

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Transfer

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_hX_of_eq_sup (_S : Setting146 G T M)
    (h : mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T) :
    ∀ x : OTwoQuot (mcOf T), ∃ l ∈ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)),
      ∃ t ∈ imageOTwoQuot (mcOf T) T, x = l * t := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := qPi_surjective (mcOf T) x
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := le_sup_left.trans h.symm.le
  have hnorm := le_normalizer_conjClosure (oTwoUpper H) (mcOf T)
  have hg0 : g ∈ conjClosure (oTwoUpper H) (mcOf T) ⊔ T := h.le hg
  have hg' : g ∈ T ⊔ conjClosure (oTwoUpper H) (mcOf T) := by rwa [sup_comm] at hg0
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hTG.trans hnorm)] at hg'
  obtain ⟨t, ht, k, hk, rfl⟩ := hg'
  have htG : t ∈ mcOf T := hTG ht
  have hkG : k ∈ mcOf T := hKzG hk
  have hconj : t * k * t⁻¹ ∈ conjClosure (oTwoUpper H) (mcOf T) :=
    (Subgroup.mem_normalizer_iff.mp (hnorm htG) k).mp hk
  have hconjG : t * k * t⁻¹ ∈ mcOf T :=
    (mcOf T).mul_mem ((mcOf T).mul_mem htG hkG) ((mcOf T).inv_mem htG)
  refine ⟨qPi (mcOf T) ⟨t * k * t⁻¹, hconjG⟩,
    mem_imageOTwoQuot_iff.mpr ⟨_, hconjG, hconj, rfl⟩, qPi (mcOf T) ⟨t, htG⟩,
    mem_imageOTwoQuot_iff.mpr ⟨_, htG, ht, rfl⟩, ?_⟩
  rw [← map_mul]
  exact congrArg (qPi (mcOf T)) (Subtype.ext (by simp))

theorem e9_primes_of_solvable (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) {A : Subgroup (OTwoQuot (mcOf T))}
    (hHA : imageOTwoQuot (mcOf T) H ≤ A) (hA : Group.IsSolvable ↥A) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card A → r = 2 ∨ r = 3 := by
  intro r hr hd
  rcases q_prime_dvd_of_solvable_hat S hred hmax hHA hA hr hd with h | h | ⟨hp5, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · have := hshape.1
    omega

theorem e9_normalizer_le_of_hat (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {T0 : Subgroup G} (_h1 : pCoreOf 2 H ≤ T0) (_h2 : T0 ≤ T)
    (h : Subgroup.normalizer ((imageOTwoQuot (mcOf T) T0 : Subgroup (OTwoQuot (mcOf T))) :
        Set (OTwoQuot (mcOf T))) ≤ imageOTwoQuot (mcOf T) H) :
    Subgroup.normalizer (T0 : Set G) ⊓ mcOf T ≤ H := by
  intro x hx
  have hxG : x ∈ mcOf T := hx.2
  have hmem : qPi (mcOf T) ⟨x, hxG⟩ ∈ imageOTwoQuot (mcOf T) H :=
    h (q_image_mem_normalizer (inf_le_left : Subgroup.normalizer (T0 : Set G) ⊓ mcOf T ≤ _)
      (mem_imageOTwoQuot_iff.mpr ⟨x, hxG, hx, rfl⟩))
  exact (E9P2.Cfg.qPi_mem_image_iff
    ((E9P2.Cfg.pCoreOf_mcOf_le_T S).trans hred.isHTM.1.1) hxG).mp hmem

theorem e9z4_fstar_of_C1 (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hC : Stage14614C1 T H p) : oTwoUpper H ≤ oTwoFstarIn (mcOf T) :=
  oTwoUpper_le_oTwoFstarIn_of_kz_P20 S hred hC.1

end Transfer

end CFSG.Quasithin
