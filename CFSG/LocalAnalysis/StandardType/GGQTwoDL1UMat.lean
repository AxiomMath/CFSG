module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UMatA
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem qtwoDL1_unitMat_block (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n) {J : Finset (Fin n)}
    (hJ : J.card = 0 ∨ J.card = 3) {g : GL (Fin n) K} {τ : K ≃+* K}
    (hg : ∀ d : Fin n → K, (∀ l, d l ^ 3 = 1) → ∏ l, d l = 1 → (∀ a ∈ J, ∀ b ∈ J, d a = d b) →
      ∃ c : K, (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) =
        c • (Matrix.diagonal d * (g : Matrix (Fin n) (Fin n) K))) :
    τ = RingEquiv.refl K ∧
      ∀ a b, a ≠ b → (a ∉ J ∨ b ∉ J) → (g : Matrix (Fin n) (Fin n) K) a b = 0 := by
  classical
  obtain ⟨ω, hω3, hω1⟩ := p9uUMat_exists_omega hK
  obtain ⟨π, hπ⟩ := p9uUMat_exists_perm g
  have hω2_3 : (ω * ω) ^ 3 = 1 := by rw [mul_pow, hω3, one_mul]
  have hω_mul : ω * (ω * ω) = 1 := by
    calc ω * (ω * ω) = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω2_mul : (ω * ω) * ω = 1 := by rw [mul_comm]; exact hω_mul
  have hω0 : ω ≠ 0 := p9uUMat_omega_ne_zero hω3
  have key : ∀ d : Fin n → K, p9uUMat_Allowed J d → ∃ c : K,
      (∀ a b, (g : Matrix (Fin n) (Fin n) K) a b * τ (d b) =
        c * d a * (g : Matrix (Fin n) (Fin n) K) a b) ∧
      (∀ y, τ (d y) = c * d (π y)) := by
    intro d hd
    obtain ⟨c, hc⟩ := hg d hd.1 hd.2.1 hd.2.2
    refine ⟨c, fun a b => p9uUMat_entry hc a b, fun y => ?_⟩
    have h := p9uUMat_entry hc (π y) y
    have h' : (g : Matrix (Fin n) (Fin n) K) (π y) y * τ (d y) =
        (g : Matrix (Fin n) (Fin n) K) (π y) y * (c * d (π y)) := by
      rw [h]; ring
    exact mul_left_cancel₀ (hπ y) h'
  have hpair_contra : τ ω = ω * ω → False := by
    intro h1
    have hτ3 : (τ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
    have hpair : ∀ i j : Fin n, i ≠ j → i ∉ J → j ∉ J → π i = j := by
      intro i j hij hi hj
      have hd : p9uUMat_Allowed J (p9uUMat_two i j ω (ω * ω)) :=
        p9uUMat_two_allowed hij hi hj hω3 hω2_3 hω_mul
      obtain ⟨c, hentry, hrel⟩ := key _ hd
      have hc3 : c ^ 3 = 1 := by
        have h := hrel i
        rw [p9uUMat_two_apply_i] at h
        have hmul : c * p9uUMat_two i j ω (ω * ω) (π i) = τ ω := h.symm
        have := congrArg (fun t : K => t ^ 3) hmul
        simpa [mul_pow, hd.1 (π i), hτ3] using this
      have hc1 : c = 1 := p9uUMat_coeff_one hK hn hij hω3 hω1 hc3 hrel
      have hi' := hrel i
      rw [p9uUMat_two_apply_i, hc1, one_mul] at hi'
      have hval : p9uUMat_two i j ω (ω * ω) (π i) = ω * ω := by rw [← hi', h1]
      have keyj : ∀ m : Fin n, p9uUMat_two i j ω (ω * ω) m = ω * ω → m = j := by
        intro m hm
        by_cases hmj : m = j
        · exact hmj
        · by_cases hmi : m = i
          · subst hmi
            rw [p9uUMat_two_apply_i] at hm
            exact absurd hm (p9uUMat_omega_ne_sq hω3 hω1)
          · rw [p9uUMat_two_apply_of_ne hmi hmj] at hm
            exact absurd hm.symm (p9uUMat_omega_sq_ne_one hω3 hω1)
      exact keyj (π i) hval
    have hCcard : (Finset.univ \ J).card = n - J.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    by_cases hge : 3 ≤ (Finset.univ \ J).card
    · obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hge
      obtain ⟨i, j, k, hij, hik, hjk, hteq⟩ := Finset.card_eq_three.mp htcard
      subst hteq
      have hiJ : i ∉ J := (Finset.mem_sdiff.mp (ht (by simp))).2
      have hjJ : j ∉ J := (Finset.mem_sdiff.mp (ht (by simp))).2
      have hkJ : k ∉ J := (Finset.mem_sdiff.mp (ht (by simp))).2
      exact hjk ((hpair i j hij hiJ hjJ).symm.trans (hpair i k hik hiJ hkJ))
    · have hCle : (Finset.univ \ J).card ≤ 2 := by omega
      have hJ3 : J.card = 3 := by
        rcases hJ with h | h
        · exfalso; rw [h, Nat.sub_zero] at hCcard; omega
        · exact h
      have hCpos : 1 ≤ (Finset.univ \ J).card := by
        rw [hCcard]; rcases hJ with h | h <;> rw [h] <;> omega
      obtain ⟨xc, hxcC⟩ := Finset.card_pos.mp hCpos
      have hxcJ : xc ∉ J := (Finset.mem_sdiff.mp hxcC).2
      let d := p9uUMat_onJ J ω
      have hd : p9uUMat_Allowed J d := p9uUMat_onJ_allowed hJ hω3
      obtain ⟨c, hentry, hrel⟩ := key d hd
      have hdJ : ∀ y, y ∈ J → d y = ω := fun y hy => p9uUMat_onJ_apply_mem hy
      have hdC : ∀ y, y ∉ J → d y = 1 := fun y hy => p9uUMat_onJ_apply_notMem hy
      by_cases hA : ∃ y ∈ J, π y ∉ J
      · obtain ⟨y0, hy0J, hy0C⟩ := hA
        have hcy0 : c = ω * ω := by
          have h := hrel y0
          rw [hdJ y0 hy0J, hdC (π y0) hy0C, mul_one, h1] at h
          exact h.symm
        have himg : (J.image π).card = 3 := by
          rw [Finset.card_image_of_injective _ π.injective, hJ3]
        have hlt : (Finset.univ \ J).card < (J.image π).card := by
          rw [himg]; exact hCle.trans_lt (by norm_num)
        obtain ⟨e, heimg, heC⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        obtain ⟨y1, hy1J, hy1e⟩ := Finset.mem_image.mp heimg
        have hy1J' : π y1 ∈ J := by
          rw [hy1e]
          by_contra hnot
          exact heC (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hnot⟩)
        have h := hrel y1
        rw [hdJ y1 hy1J, hdJ (π y1) hy1J', hcy0, h1, hω2_mul] at h
        exact p9uUMat_omega_sq_ne_one hω3 hω1 h
      · have hcase' : ∀ y ∈ J, π y ∈ J := by
          intro y hy
          by_contra hnot
          exact hA ⟨y, hy, hnot⟩
        have hcω : c = ω := by
          obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hJ3]; norm_num)
          have h := hrel y
          rw [hdJ y hy, hdJ (π y) (hcase' y hy), h1] at h
          exact mul_right_cancel₀ hω0 h.symm
        have h := hrel xc
        rw [hdC xc hxcJ, map_one, hcω] at h
        by_cases hpx : π xc ∈ J
        · rw [hdJ (π xc) hpx] at h
          exact p9uUMat_omega_sq_ne_one hω3 hω1 h.symm
        · rw [hdC (π xc) hpx, mul_one] at h
          exact hω1 h.symm
  have htau : τ ω = ω := by
    have hτ3 : (τ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
    rcases p9uUMat_cube_eq hK hω3 hω1 hτ3 with h | h | h
    · exfalso
      exact hω1 (τ.injective (by rw [h, map_one]))
    · exact h
    · exact (hpair_contra h).elim
  have htau_eq : τ = RingEquiv.refl K := by
    ext x
    by_cases hx : x = 0
    · subst hx; simp
    · rcases p9uUMat_cube_eq hK hω3 hω1 (p9uUMat_pow_three hK hx) with h | h | h
      · rw [h]; simp
      · rw [h, htau]; rfl
      · rw [h, map_mul, htau]; rfl
  refine ⟨htau_eq, ?_⟩
  intro a b hab habJ
  have hrel_id : ∀ d : Fin n → K, p9uUMat_Allowed J d → ∃ c : K, c ≠ 0 ∧
      ∀ y, d y = c * d (π y) := by
    intro d hd
    obtain ⟨c, hentry, hrel⟩ := key d hd
    refine ⟨c, ?_, fun y => ?_⟩
    · intro hc0
      have h := hrel (⟨0, by omega⟩ : Fin n)
      rw [hc0, zero_mul] at h
      have hdy0 : d (⟨0, by omega⟩ : Fin n) ≠ 0 := by
        have := hd.1 (⟨0, by omega⟩ : Fin n)
        intro h0
        rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at this
        exact one_ne_zero this.symm
      refine hdy0 (τ.injective ?_)
      rw [h, map_zero]
    · have h := hrel y
      rw [htau_eq] at h
      simpa using h
  have hπfix : ∀ x, x ∉ J → π x = x := by
    intro x hx
    by_cases hcx : ∃ y, y ∉ J ∧ y ≠ x
    · obtain ⟨y, hy, hyx⟩ := hcx
      have hd : p9uUMat_Allowed J (p9uUMat_two x y ω (ω * ω)) :=
        p9uUMat_two_allowed (Ne.symm hyx) hx hy hω3 hω2_3 hω_mul
      obtain ⟨c, hcne, hrel⟩ := hrel_id _ hd
      have hc3 : c ^ 3 = 1 := by
        have h := hrel x
        rw [p9uUMat_two_apply_i] at h
        have hmul : c * p9uUMat_two x y ω (ω * ω) (π x) = ω := h.symm
        have := congrArg (fun t : K => t ^ 3) hmul
        simpa [mul_pow, hd.1 (π x), hω3] using this
      have hc1 : c = 1 :=
        p9uUMat_coeff_one (τ := RingEquiv.refl K) (π := π) hK hn (Ne.symm hyx) hω3 hω1 hc3
          (fun m => by simpa using hrel m)
      have h := hrel x
      rw [p9uUMat_two_apply_i, hc1, one_mul] at h
      by_cases hxi : π x = x
      · exact hxi
      · exfalso
        by_cases hxy : π x = y
        · rw [hxy, p9uUMat_two_apply_j (Ne.symm hyx) ω (ω * ω)] at h
          exact (p9uUMat_omega_ne_sq hω3 hω1) h
        · rw [p9uUMat_two_apply_of_ne hxi hxy _ _] at h
          exact hω1 h
    · have hy : ∀ y, y ∉ J → y = x := by
        intro y hy
        by_contra hyx
        exact hcx ⟨y, hy, hyx⟩
      have hJ3 : J.card = 3 := by
        rcases hJ with h | h
        · exfalso
          have hJempty : J = ∅ := Finset.card_eq_zero.mp h
          have hxuniv : ∀ y : Fin n, y = x := by
            intro y
            by_cases hyJ : y ∈ J
            · rw [hJempty] at hyJ; exact absurd hyJ (Finset.notMem_empty y)
            · exact hy y hyJ
          obtain ⟨y, z, hyz⟩ :=
            Fintype.exists_pair_of_one_lt_card (α := Fin n) (by simp [Fintype.card_fin]; omega)
          exact hyz ((hxuniv y).trans (hxuniv z).symm)
        · exact h
      let d := p9uUMat_onJ J ω
      have hd : p9uUMat_Allowed J d := p9uUMat_onJ_allowed hJ hω3
      obtain ⟨c, hcne, hrel⟩ := hrel_id d hd
      have hdi : d x = 1 := p9uUMat_onJ_apply_notMem hx
      have h := hrel x
      rw [hdi] at h
      by_cases hxi : π x = x
      · exact hxi
      · exfalso
        have hπxJ : π x ∈ J := by
          by_contra hnot
          exact hxi (hy (π x) hnot)
        change 1 = c * p9uUMat_onJ J ω (π x) at h
        rw [p9uUMat_onJ_apply_mem hπxJ] at h
        have hcω : c = ω * ω := by
          have h2 : c * ω = 1 := h.symm
          have h3 : c * ω = (ω * ω) * ω := by rw [h2, hω2_mul]
          exact mul_right_cancel₀ hω0 h3
        obtain ⟨y, hyJ⟩ := Finset.card_pos.mp (by rw [hJ3]; norm_num)
        have h2 := hrel y
        change p9uUMat_onJ J ω y = c * p9uUMat_onJ J ω (π y) at h2
        rw [p9uUMat_onJ_apply_mem hyJ, hcω] at h2
        by_cases hpy : π y ∈ J
        · rw [p9uUMat_onJ_apply_mem hpy, hω2_mul] at h2
          exact hω1 h2
        · have hpyx : π y = x := hy (π y) hpy
          rw [hpyx, p9uUMat_onJ_apply_notMem hx, mul_one] at h2
          exact (p9uUMat_omega_ne_sq hω3 hω1) h2
  have hπJ : ∀ b, b ∈ J → π b ∈ J := by
    intro b hb
    by_contra hpb
    have hfix : π (π b) = π b := hπfix (π b) hpb
    have hpb' : π b = b := π.injective hfix
    rw [hpb'] at hpb
    exact hpb hb
  have hsep : ∀ a b, a ≠ b → (a ∉ J ∨ b ∉ J) →
      (g : Matrix (Fin n) (Fin n) K) a b = 0 := by
    intro a b hab habJ
    by_contra hgab
    have hsepval : ∃ d : Fin n → K, p9uUMat_Allowed J d ∧ d a ≠ d (π b) := by
      by_cases hbJ : b ∈ J
      · have haJ : a ∉ J := by
          rcases habJ with h | h
          · exact h
          · exact absurd hbJ h
        have hpbJ : π b ∈ J := hπJ b hbJ
        by_cases hc : ∃ c, c ∉ J ∧ c ≠ a
        · obtain ⟨c, hcJ, hca⟩ := hc
          let d : Fin n → K := fun l => p9uUMat_onJ J ω l * p9uUMat_two a c (ω * ω) ω l
          have hd : p9uUMat_Allowed J d :=
            p9uUMat_Allowed.mul (p9uUMat_onJ_allowed hJ hω3)
              (p9uUMat_two_allowed (Ne.symm hca) haJ hcJ hω2_3 hω3 hω2_mul)
          have hda : d a = ω * ω := by
            change (p9uUMat_onJ J ω a) * (p9uUMat_two a c (ω * ω) ω a) = ω * ω
            rw [p9uUMat_onJ_apply_notMem haJ, p9uUMat_two_apply_i, one_mul]
          have hdb : d (π b) = ω := by
            change (p9uUMat_onJ J ω (π b)) * (p9uUMat_two a c (ω * ω) ω (π b)) = ω
            rw [p9uUMat_onJ_apply_mem hpbJ,
              p9uUMat_two_apply_of_ne (fun h => haJ (by rwa [h] at hpbJ))
                (fun h => hcJ (by rwa [h] at hpbJ)) (ω * ω) ω, mul_one]
          exact ⟨d, hd, by rw [hda, hdb]; exact (p9uUMat_omega_ne_sq hω3 hω1).symm⟩
        · have hda : p9uUMat_onJ J ω a = 1 := p9uUMat_onJ_apply_notMem haJ
          have hdb : p9uUMat_onJ J ω (π b) = ω := p9uUMat_onJ_apply_mem hpbJ
          exact ⟨p9uUMat_onJ J ω, p9uUMat_onJ_allowed hJ hω3, by
            rw [hda, hdb]; exact hω1.symm⟩
      · have hpb : π b = b := hπfix b hbJ
        by_cases haJ : a ∈ J
        · by_cases hc : ∃ c, c ∉ J ∧ c ≠ b
          · obtain ⟨c, hcJ, hcb⟩ := hc
            let d : Fin n → K := fun l => p9uUMat_onJ J ω l * p9uUMat_two b c (ω * ω) ω l
            have hd : p9uUMat_Allowed J d :=
              p9uUMat_Allowed.mul (p9uUMat_onJ_allowed hJ hω3)
                (p9uUMat_two_allowed (Ne.symm hcb) hbJ hcJ hω2_3 hω3 hω2_mul)
            have hda : d a = ω := by
              change (p9uUMat_onJ J ω a) * (p9uUMat_two b c (ω * ω) ω a) = ω
              rw [p9uUMat_onJ_apply_mem haJ,
                p9uUMat_two_apply_of_ne (fun h => hbJ (by rwa [h] at haJ))
                  (fun h => hcJ (by rwa [h] at haJ)) (ω * ω) ω, mul_one]
            have hdb : d b = ω * ω := by
              change (p9uUMat_onJ J ω b) * (p9uUMat_two b c (ω * ω) ω b) = ω * ω
              rw [p9uUMat_onJ_apply_notMem hbJ, p9uUMat_two_apply_i, one_mul]
            exact ⟨d, hd, by rw [hpb, hda, hdb]; exact p9uUMat_omega_ne_sq hω3 hω1⟩
          · have hda : p9uUMat_onJ J ω a = ω := p9uUMat_onJ_apply_mem haJ
            have hdb : p9uUMat_onJ J ω b = 1 := p9uUMat_onJ_apply_notMem hbJ
            exact ⟨p9uUMat_onJ J ω, p9uUMat_onJ_allowed hJ hω3, by
              rw [hpb, hda, hdb]; exact hω1⟩
        · have hda : p9uUMat_two a b ω (ω * ω) a = ω := p9uUMat_two_apply_i a b ω (ω * ω)
          have hdb : p9uUMat_two a b ω (ω * ω) b = ω * ω :=
            p9uUMat_two_apply_j hab ω (ω * ω)
          exact ⟨p9uUMat_two a b ω (ω * ω),
            p9uUMat_two_allowed hab haJ hbJ hω3 hω2_3 hω_mul, by
              rw [hpb, hda, hdb]
              exact p9uUMat_omega_ne_sq hω3 hω1⟩
    obtain ⟨d, hd, hsep'⟩ := hsepval
    obtain ⟨c, hentry, hrelτ⟩ := key d hd
    have hrel : ∀ y, d y = c * d (π y) := fun y => by
      have h := hrelτ y
      rw [htau_eq] at h
      simpa using h
    have hcne : c ≠ 0 := by
      intro hc0
      have h := hrel (⟨0, by omega⟩ : Fin n)
      rw [hc0, zero_mul] at h
      have hdy0 : d (⟨0, by omega⟩ : Fin n) ≠ 0 := by
        have := hd.1 (⟨0, by omega⟩ : Fin n)
        intro h0
        rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at this
        exact one_ne_zero this.symm
      exact hdy0 h
    have hb_eq : d (π b) = d a := by
      have h := hentry a b
      rw [htau_eq] at h
      rw [hrel b] at h
      have h2 : c * d (π b) = c * d a := by
        have h3 : c * d (π b) * (g : Matrix (Fin n) (Fin n) K) a b =
            c * d a * (g : Matrix (Fin n) (Fin n) K) a b := by
          calc c * d (π b) * (g : Matrix (Fin n) (Fin n) K) a b =
              (g : Matrix (Fin n) (Fin n) K) a b * (c * d (π b)) := by ring
            _ = c * d a * (g : Matrix (Fin n) (Fin n) K) a b := h
        exact mul_right_cancel₀ hgab h3
      exact mul_left_cancel₀ hcne h2
    exact hsep' hb_eq.symm
  exact hsep a b hab habJ

theorem qtwoDL1_unitMat_mem_block (hK : Nat.card K = 4) {n : ℕ} {J : Finset (Fin n)}
    {g : GL (Fin n) K} (hgU : ggIsUnitaryMat (p := 2) (f := 1) g)
    (hgJ : ∀ a b, a ≠ b → (a ∉ J ∨ b ∉ J) → (g : Matrix (Fin n) (Fin n) K) a b = 0)
    {k : ℕ} {c₀ : K}
    (hgk : ((g ^ (2 ^ k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c₀ • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ s ∈ coordBlockSU K 2 1 J, s ^ (2 ^ k) = 1 ∧
      ∃ c : K, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c • (g : Matrix (Fin n) (Fin n) K) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨1, Subgroup.one_mem _, one_pow _, 1, ?_⟩
    exact Subsingleton.elim _ _
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hU : ggIsUnitaryMat (p := 2) (f := 1) (g ^ (2 ^ k)) :=
      p9uUMat_isUnitary_pow hgU (2 ^ k)
    have hc0_3 : c₀ ^ 3 = 1 := by
      have hU' := hU
      unfold ggIsUnitaryMat at hU'
      rw [hgk] at hU'
      exact p9uUMat_unitary_scalar_cube hn hU'
    obtain ⟨c, hc3, hc2k⟩ := p9uUMat_scalar_root hc0_3 k
    have hc0_ne : c₀ ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : 3 ≠ 0)] at hc0_3
      exact one_ne_zero hc0_3.symm
    have hc_ne : c ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : 3 ≠ 0)] at hc3
      exact one_ne_zero hc3.symm
    set A : Matrix (Fin n) (Fin n) K := c • (g : Matrix (Fin n) (Fin n) K) with hA
    have hAdet_ne0 : A.det ≠ 0 := by
      rw [hA, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hc_ne) (Matrix.GeneralLinearGroup.det_ne_zero g)
    let gA : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet_ne0
    have hgA : (gA : Matrix (Fin n) (Fin n) K) = A := rfl
    have hconj : conjTr (unitaryInvolution K 2 1) (c • (g : Matrix (Fin n) (Fin n) K)) =
        unitaryInvolution K 2 1 c • conjTr (unitaryInvolution K 2 1)
          (g : Matrix (Fin n) (Fin n) K) := by
      ext i j
      simp [conjTr, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply]
    have huni_mat : conjTr (unitaryInvolution K 2 1) A * A = 1 := by
      rw [hA, hconj, Matrix.smul_mul, Matrix.mul_smul]
      have hgc : conjTr (unitaryInvolution K 2 1) (g : Matrix (Fin n) (Fin n) K) *
          (g : Matrix (Fin n) (Fin n) K) = 1 := by
        simpa [ggIsUnitaryMat] using hgU
      rw [hgc, smul_smul,
        show unitaryInvolution K 2 1 c * c = 1 by
          rw [unitaryInvolution_apply, pow_one, ← pow_succ, hc3], one_smul]
    have huni : ggIsUnitaryMat (p := 2) (f := 1) gA := by
      unfold ggIsUnitaryMat
      rw [hgA]
      exact huni_mat
    have hgpow : (g : Matrix (Fin n) (Fin n) K) ^ (2 ^ k) = c₀ • 1 := by
      rw [← Units.val_pow_eq_pow_val, hgk]
    have hApow : A ^ (2 ^ k) = 1 := by
      rw [hA, p9uUMat_smul_pow, hgpow]
      rw [smul_smul, show c ^ (2 ^ k) * c₀ = 1 by rw [hc2k, inv_mul_cancel₀ hc0_ne],
        one_smul]
    have hdet_pow : A.det ^ (2 ^ k) = 1 := by
      have := congrArg Matrix.det hApow
      rwa [Matrix.det_pow, Matrix.det_one] at this
    have hdet3 : A.det ^ 3 = 1 := by
      have h' := congrArg Matrix.det huni_mat
      rw [Matrix.det_mul, p9uUMat_det_conjTr, Matrix.det_one] at h'
      rw [unitaryInvolution_apply, pow_one] at h'
      simpa [pow_succ] using h'
    have hcop : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
    have hgcd : Nat.gcd 3 (2 ^ k) = 1 := hcop.gcd_eq_one
    have hdet1 : A.det = 1 := by
      have := (pow_gcd_eq_one (a := A.det) (m := 3) (n := 2 ^ k)).mpr ⟨hdet3, hdet_pow⟩
      rwa [hgcd, pow_one] at this
    have hAdiag : ∀ i, i ∉ J → A i i = 1 := by
      intro i hi
      have hcol : ∀ k, k ≠ i → A k i = 0 := by
        intro k hk
        rw [hA, Matrix.smul_apply, hgJ k i hk (Or.inr hi), smul_zero]
      have h1 : (A ^ (2 ^ k)) i i = (A i i) ^ (2 ^ k) := p9uUMat_diag_of_col_zero hcol _
      have h2 : (conjTr (unitaryInvolution K 2 1) A * A) i i =
          unitaryInvolution K 2 1 (A i i) * A i i := p9uUMat_entry_diag_of_col_zero hcol
      have hpp : (A i i) ^ (2 ^ k) = 1 := by rw [← h1, hApow]; simp
      have h3 : (A i i) ^ 3 = 1 := by
        have hh := congrFun (congrFun huni_mat i) i
        rw [h2, unitaryInvolution_apply, pow_one] at hh
        simpa [pow_succ] using hh
      have := (pow_gcd_eq_one (a := A i i) (m := 3) (n := 2 ^ k)).mpr ⟨h3, hpp⟩
      rwa [hgcd, pow_one] at this
    let suA : Su K 2 1 n := ⟨gA, hdet1, huni⟩
    have hmem : suA ∈ coordBlockSU K 2 1 J := by
      rw [mem_coordBlockSU_iff]
      intro i j hij
      change (gA : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0
      rw [hgA]
      by_cases hii : i = j
      · subst hii
        have hiJ : i ∉ J := by rcases hij with h | h <;> exact h
        rw [hAdiag i hiJ, if_pos rfl]
      · rw [hA, Matrix.smul_apply, hgJ i j hii hij, smul_zero, if_neg hii]
    have hpowGL : gA ^ (2 ^ k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hgA, hApow, Units.val_one]
    have hpowSu : suA ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using hpowGL
    exact ⟨suA, hmem, hpowSu, c, by
      change (gA : Matrix (Fin n) (Fin n) K) = c • (g : Matrix (Fin n) (Fin n) K)
      rw [hgA, hA]⟩

end CFSG.StandardType.QTwo

end
