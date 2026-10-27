module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Conj
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Gam
public import CFSG.RankThree.PartOne.SEITZ6.G2NormU

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem commute_1_10 (x y : K) : Commute (xp 1 x) (xp 10 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem normal_form (g : adjointGroup .G2 K)
    (hne0 : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ≠ 0) :
    ∃ (c : ℕ → K) (μ : K), c 1 = 0 ∧ μ = coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ∧
      ∀ s : K, g * xp 7 s * g⁻¹ = ordProd c * xp 10 (μ * s) * (ordProd c)⁻¹ := by
  have hct := g2_isCTGroupDatum K
  have hext := g2_steinbergExtras K
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := CFSG.LieType.Steinberg.exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, a1, bb1, c1⟩ := borel_stab_X7 hb₁
  obtain ⟨χ₂, a2, bb2, c2⟩ := borel_stab_X7 hb₂
  obtain ⟨t, ht, hv, hc⟩ := nrep_stab_X7 (K := K) w
  have hlam : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * coordAt (rt 10) (rootVec .G2 K (rt t))) := by
    rw [hg, mul_smul, mul_smul, a2, smul_smul_comm, hv, bb1, coordAt_smul]
  have ht12 : t < 12 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  have ht10 : t = 10 := by
    by_contra hne
    apply hne0
    rw [hlam, coordAt_rootVec_ne (rt_ne_rt_ten t ht12 hne).symm]
    simp
  subst ht10
  have hlam' : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) =
      ((χ₁⁻¹ : Kˣ) : K) * (χ₂ : K) := by
    rw [hlam, coordAt_rootVec_self (isRoot_rt (by norm_num))]
    simp
  have hy : ∀ s : K, g * xp 7 s * g⁻¹ = b₁ * xp 10 ((χ₂ : K) * s) * b₁⁻¹ := by
    intro s
    rw [hg, show b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂ * xp 7 s *
        (b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂)⁻¹ =
        b₁ * (CFSG.LieType.Steinberg.nrep hct w * (b₂ * xp 7 s * b₂⁻¹) *
          (CFSG.LieType.Steinberg.nrep hct w)⁻¹) * b₁⁻¹ by group, c2, hc]
  obtain ⟨t0, ht0, u0, hu0, hb⟩ := mem_borel_iff.1 hb₁
  obtain ⟨a, b, hab⟩ := mem_Tg_iff.1 ht0
  obtain ⟨c, hc'⟩ := exists_ordProd hu0
  have hχ : (χ₁ : K) = (a : K) := by
    have h1 := c1 1
    have h2 : b₁ * xp 7 1 * b₁⁻¹ = xp 7 ((a : K) * 1) := by
      rw [hb, hc', hab, show torusElement .G2 K e0 a * torusElement .G2 K e1 b * ordProd c *
          xp 7 1 * (torusElement .G2 K e0 a * torusElement .G2 K e1 b * ordProd c)⁻¹ =
          (torusElement .G2 K e0 a * torusElement .G2 K e1 b) * (ordProd c * xp 7 1 *
            (ordProd c)⁻¹) * (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ by group,
        (ordProd_commute_x7 c 1).eq, mul_inv_cancel_right, torus_conj_xp7]
    rw [h2] at h1
    simpa using (xp_inj (p := 7) (by norm_num) h1).symm
  have hχu : χ₁ = a := Units.ext hχ
  subst hχu
  have hsplit : u0 = ordProd (mk6 (c 0) 0 (c 4) (c 8) (c 3 + c 1 ^ 2 * c 4 + c 1 * c 8)
      (c 7 + c 1 * c 4 ^ 2)) * xp 1 (c 1) := by rw [hc', ← ordProd_split]
  obtain ⟨m0, m1, m4, m8, m3, m7, hT⟩ := torus_conj_ordProd ht0
  set c' := mk6 (c 0) 0 (c 4) (c 8) (c 3 + c 1 ^ 2 * c 4 + c 1 * c 8) (c 7 + c 1 * c 4 ^ 2)
    with hc'def
  refine ⟨mk6 (m0 * c' 0) (m1 * c' 1) (m4 * c' 4) (m8 * c' 8) (m3 * c' 3) (m7 * c' 7),
    ((χ₁⁻¹ : Kˣ) : K) * (χ₂ : K), ?_, hlam'.symm, fun s => ?_⟩
  · simp [mk6, hc'def]
  · rw [hy s, hb, hsplit]
    have e1 : ∀ z : K, (ordProd c' * xp 1 (c 1)) * xp 10 z * (ordProd c' * xp 1 (c 1))⁻¹ =
        ordProd c' * xp 10 z * (ordProd c')⁻¹ := by
      intro z
      rw [show (ordProd c' * xp 1 (c 1)) * xp 10 z * (ordProd c' * xp 1 (c 1))⁻¹ =
          ordProd c' * (xp 1 (c 1) * xp 10 z * (xp 1 (c 1))⁻¹) * (ordProd c')⁻¹ by group,
        (commute_1_10 (c 1) z).eq]
      group
    rw [show t0 * (ordProd c' * xp 1 (c 1)) * xp 10 ((χ₂ : K) * s) *
        (t0 * (ordProd c' * xp 1 (c 1)))⁻¹ =
        t0 * ((ordProd c' * xp 1 (c 1)) * xp 10 ((χ₂ : K) * s) *
          (ordProd c' * xp 1 (c 1))⁻¹) * t0⁻¹ by group, e1,
      show t0 * (ordProd c' * xp 10 ((χ₂ : K) * s) * (ordProd c')⁻¹) * t0⁻¹ =
        (t0 * ordProd c' * t0⁻¹) * (t0 * xp 10 ((χ₂ : K) * s) * t0⁻¹) *
          (t0 * ordProd c' * t0⁻¹)⁻¹ by group, hT c', hab, torus_conj_xp10,
      ← mul_assoc ((χ₁⁻¹ : Kˣ) : K) (χ₂ : K) s]

end CFSG.RankThree.PartOne.SEITZ2
