module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L : Subgroup G}

theorem AmalgamS3.coreIn_eq_bot (hA : AmalgamS3 G₀ G₁ G₂ T L) {W : Subgroup G} {r : G}
    (hW_le_Dμ : W ≤ coreIn (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) G₁) (hr : r ∈ G₂) (hr1 : r ∉ G₁)
    (hrD : ∀ d ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * d * r⁻¹ * d⁻¹ ∈ W) :
    coreIn (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) G₁ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup G := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂
  let H : Subgroup G := G₁ ⊓ G₂
  let Dμ : Subgroup G := coreIn D G₁
  have hDμ_le_D : Dμ ≤ D := coreIn_le_right D G₁
  have hDμ_le_G1 : Dμ ≤ G₁ := coreIn_le_left D G₁
  have hG1_N : G₁ ≤ Subgroup.normalizer (Dμ : Set G) := le_normalizer_coreIn D G₁
  have hr_N : r ∈ Subgroup.normalizer (Dμ : Set G) := by
    refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
    have hxD : x ∈ D := hDμ_le_D hx
    have hcomm : r * x * r⁻¹ * x⁻¹ ∈ W := hrD x hxD
    have hprod : r * x * r⁻¹ = (r * x * r⁻¹ * x⁻¹) * x := by group
    rw [hprod]
    exact Dμ.mul_mem (hW_le_Dμ hcomm) hx

  have hH_N : H ≤ Subgroup.normalizer (Dμ : Set G) := inf_le_left.trans hG1_N
  have hr_span_N : Subgroup.zpowers r ≤ Subgroup.normalizer (Dμ : Set G) :=
    Subgroup.zpowers_le.mpr hr_N
  have hG2_eq : G₂ = H ⊔ Subgroup.zpowers r := by
    have hKle : H ⊔ Subgroup.zpowers r ≤ G₂ :=
      sup_le inf_le_right (Subgroup.zpowers_le.mpr hr)
    have hne : H ⊔ Subgroup.zpowers r ≠ H := by
      intro h
      have hrH : r ∈ H := by
        rw [← h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
      exact hr1 hrH.1
    have hprod := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers r) G₂
      le_sup_left hKle
    rw [hA.relIndex_inf_G₂] at hprod
    have hne1 : H.relIndex (H ⊔ Subgroup.zpowers r) ≠ 1 := by
      intro h
      exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) le_sup_left)
    have hdvd : H.relIndex (H ⊔ Subgroup.zpowers r) ∣ 3 := ⟨_, hprod.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne1
    · have hb1 : (H ⊔ Subgroup.zpowers r).relIndex G₂ = 1 := by
        rw [h3] at hprod
        omega
      exact (le_antisymm hKle (Subgroup.relIndex_eq_one.mp hb1)).symm
  have hG2_N : G₂ ≤ Subgroup.normalizer (Dμ : Set G) := by
    rw [hG2_eq]
    exact sup_le hH_N hr_span_N

  have hDμ_le_G0 : Dμ ≤ G₀ := hDμ_le_G1.trans hA.hyp.le₁
  have hDμ_2 : IsPGroup 2 Dμ := (pCoreOf_isPGroup 2 G₁).to_le (hDμ_le_D.trans inf_le_left)
  have hG0_N : G₀ ≤ Subgroup.normalizer (Dμ : Set G) := by
    rw [hA.hyp.gen]
    exact sup_le hG1_N hG2_N
  have hDμ_le_O2 : Dμ ≤ pCoreOf 2 G₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDμ_le_G0 hG0_N hDμ_2
  exact le_bot_iff.mp (hA.hyp.o2_trivial ▸ hDμ_le_O2)

theorem AmalgamA.false_of_elemAbelian (hA : AmalgamA G₀ G₁ G₂ T L) {W : Subgroup G} {r : G}
    (hWD : W ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) (hW : IsElemAbelian 2 W)
    (hWn : G₂ ≤ Subgroup.normalizer (W : Set G))
    (hQ₂W : pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G))
    (hQ₁W : ¬ pCoreOf 2 G₁ ≤ Subgroup.centralizer (W : Set G))
    (hr : r ∈ G₂) (hr1 : r ∉ G₁)
    (hrD : ∀ d ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * d * r⁻¹ * d⁻¹ ∈ W) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q1 : Subgroup G := pCoreOf 2 G₁
  let Q2 : Subgroup G := pCoreOf 2 G₂
  let D : Subgroup G := Q1 ⊓ Q2
  let C : Subgroup G := Subgroup.centralizer (W : Set G)
  let H : Subgroup G := G₁ ⊓ G₂
  have hQ1T : Q1 ≤ T := F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁
  have hQ2T : Q2 ≤ T := hA.pCoreOf_le_T
  have hWD' : W ≤ D := hWD
  have hQ2C : Q2 ≤ C := hQ₂W
  have hQ1notC : ¬ Q1 ≤ C := hQ₁W

  have hTC : T ⊓ C = Q2 := by
    have hQ2_le : Q2 ≤ T ⊓ C := le_inf hQ2T hQ2C
    have hrel : (T ⊓ C).relIndex T ∣ 2 := by
      have hprod := Subgroup.relIndex_mul_relIndex Q2 (T ⊓ C) T hQ2_le inf_le_left
      rw [hA.relIndex_pCoreOf_T] at hprod
      exact ⟨Q2.relIndex (T ⊓ C), by rw [mul_comm]; exact hprod.symm⟩
    have hne1 : (T ⊓ C).relIndex T ≠ 1 := by
      intro h
      have hTle : T ≤ T ⊓ C := Subgroup.relIndex_eq_one.mp h
      exact hQ1notC (hQ1T.trans (hTle.trans inf_le_right))
    rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
    · exact absurd h1 hne1
    · have hprod := Subgroup.relIndex_mul_relIndex Q2 (T ⊓ C) T hQ2_le inf_le_left
      rw [hA.relIndex_pCoreOf_T, h2] at hprod
      have hQ2rel : Q2.relIndex (T ⊓ C) = 1 := by omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hQ2rel) hQ2_le

  have hstep2 : ∀ g ∈ G₁, W ≤ conjSub g Q2 := by
    intro g hg
    by_cases hgG₂ : g ∈ G₂
    · have hQ2fix : conjSub g Q2 = Q2 :=
        F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 G₂ hgG₂)
      rw [hQ2fix]
      exact hWD'.trans inf_le_right
    · by_contra hnot
      let W' : Subgroup G := conjSub g W
      let Q2' : Subgroup G := conjSub g Q2
      let T' : Subgroup G := conjSub g T
      have hgQ1 : conjSub g Q1 = Q1 :=
        F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 G₁ hg)
      have hWT' : W ≤ T' := by
        have h : Q1 ≤ T' := by
          rw [← hgQ1]
          exact conjSub_mono g hQ1T
        exact (hWD'.trans inf_le_left).trans h
      have hW'T : W' ≤ T := by
        have h : W' ≤ Q1 := by
          rw [← hgQ1]
          exact conjSub_mono g (hWD'.trans inf_le_left)
        exact h.trans hQ1T
      have hW'ea : IsElemAbelian 2 W' := F7.isElemAbelian_conjSub hW
      have hW'n : conjSub g G₂ ≤ Subgroup.normalizer (W' : Set G) :=
        conjSub_le_normalizer (g := g) (H := G₂) (K := W) hWn
      have hQ2'W' : Q2' ≤ Subgroup.centralizer (W' : Set G) := by
        have h := conjSub_mono g hQ2C
        rwa [← conjSub_centralizer] at h
      have hT'C' : T' ⊓ Subgroup.centralizer (W' : Set G) = Q2' := by
        have h := congrArg (conjSub g) hTC
        rwa [conjSub_inf, ← conjSub_centralizer] at h
      have hrelQ2'T' : Q2'.relIndex T' = 2 := by
        have h := Subgroup.relIndex_map_map_of_injective
          (f := (MulAut.conj g).toMonoidHom) Q2 T (MulEquiv.injective (MulAut.conj g))
        rw [hA.relIndex_pCoreOf_T] at h
        exact h
      obtain ⟨w, hwW, hwQ2'⟩ := Set.not_subset.mp hnot
      have hwT' : w ∈ T' := hWT' hwW
      have hw_not_cent : w ∉ Subgroup.centralizer (W' : Set G) := by
        intro hwC
        have hmem : w ∈ T' ⊓ Subgroup.centralizer (W' : Set G) := ⟨hwT', hwC⟩
        rw [hT'C'] at hmem
        exact hwQ2' hmem
      have hcomm_not : ∃ w₁ ∈ W', w * w₁ ≠ w₁ * w := by
        by_contra h
        push Not at h
        exact hw_not_cent (by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (h y hy).symm)
      have hW'_not_Q2 : ¬ W' ≤ Q2 := by
        intro hle
        obtain ⟨w₁, hw₁W', hw₁ne⟩ := hcomm_not
        have hw₁C : w₁ ∈ Subgroup.centralizer (W : Set G) := hQ2C (hle hw₁W')
        exact hw₁ne (Subgroup.mem_centralizer_iff.mp hw₁C w hwW)
      obtain ⟨w', hw'W', hw'Q2⟩ := Set.not_subset.mp hW'_not_Q2
      have hw'_not_cent : w' ∉ Subgroup.centralizer (W : Set G) := by
        intro hw'C
        have hmem : w' ∈ T ⊓ Subgroup.centralizer (W : Set G) := ⟨hW'T hw'W', hw'C⟩
        rw [hTC] at hmem
        exact hw'Q2 hmem
      obtain ⟨w₀, hw₀W, hw₀ne⟩ : ∃ w₀ ∈ W, w' * w₀ ≠ w₀ * w' := by
        by_contra h
        push Not at h
        exact hw'_not_cent (by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (h y hy).symm)
      let z : G := w' * w₀ * w'⁻¹ * w₀⁻¹
      have hz_ne : z ≠ 1 := by
        intro hz
        apply hw₀ne
        have h2 : w' * w₀ = w₀ * w' := by
          calc w' * w₀ = (w' * w₀ * w'⁻¹ * w₀⁻¹) * (w₀ * w') := by group
            _ = 1 * (w₀ * w') := by
                rw [show w' * w₀ * w'⁻¹ * w₀⁻¹ = 1 from hz]
            _ = w₀ * w' := by rw [one_mul]
        exact h2
      have hzW : z ∈ W := by
        have hw'G₂ : w' ∈ G₂ := hA.hyp.sylow₂.1 (hW'T hw'W')
        have hconj : w' * w₀ * w'⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWn hw'G₂) w₀).mp hw₀W
        have hz_eq : z = (w' * w₀ * w'⁻¹) * w₀⁻¹ := by
          show w' * w₀ * w'⁻¹ * w₀⁻¹ = (w' * w₀ * w'⁻¹) * w₀⁻¹
          rfl
        rw [hz_eq]
        exact W.mul_mem hconj (W.inv_mem hw₀W)
      have hzW' : z ∈ W' := by
        have hw₀T' : w₀ ∈ T' := hWT' hw₀W
        have hw₀G' : w₀ ∈ conjSub g G₂ := (conjSub_mono g hA.hyp.sylow₂.1) hw₀T'
        have hconj : w₀ * w'⁻¹ * w₀⁻¹ ∈ W' :=
          (Subgroup.mem_normalizer_iff.mp (hW'n hw₀G') w'⁻¹).mp (W'.inv_mem hw'W')
        have hz_eq : z = w' * (w₀ * w'⁻¹ * w₀⁻¹) := by
          show w' * w₀ * w'⁻¹ * w₀⁻¹ = w' * (w₀ * w'⁻¹ * w₀⁻¹)
          group
        rw [hz_eq]
        exact W'.mul_mem hw'W' hconj
      have hw₀Q2' : w₀ ∉ Q2' := by
        intro hw₀Q2'
        have hcent : w₀ ∈ Subgroup.centralizer (W' : Set G) := hQ2'W' hw₀Q2'
        have hcomm : w' * w₀ = w₀ * w' := Subgroup.mem_centralizer_iff.mp hcent w' hw'W'
        have hz1 : z = 1 := by
          have hcomm' : w₀ * w'⁻¹ = w'⁻¹ * w₀ := by
            have := congrArg (fun t => w'⁻¹ * t * w'⁻¹) hcomm
            simpa [mul_assoc] using this
          calc z = w' * (w₀ * w'⁻¹) * w₀⁻¹ := by
                show w' * w₀ * w'⁻¹ * w₀⁻¹ = w' * (w₀ * w'⁻¹) * w₀⁻¹
                group
            _ = w' * (w'⁻¹ * w₀) * w₀⁻¹ := by rw [hcomm']
            _ = 1 := by group
        exact hz_ne hz1
      have hTeq : T = Q2 ⊔ Subgroup.zpowers w' := by
        have hw'T : w' ∈ T := hW'T hw'W'
        have hKle : Q2 ⊔ Subgroup.zpowers w' ≤ T :=
          sup_le hQ2T (Subgroup.zpowers_le.mpr hw'T)
        have hprod := Subgroup.relIndex_mul_relIndex Q2 (Q2 ⊔ Subgroup.zpowers w') T
          le_sup_left hKle
        rw [hA.relIndex_pCoreOf_T] at hprod
        have hne1 : Q2.relIndex (Q2 ⊔ Subgroup.zpowers w') ≠ 1 := by
          intro h
          exact hw'Q2 (Subgroup.relIndex_eq_one.mp h
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers w')))
        have hdvd : Q2.relIndex (Q2 ⊔ Subgroup.zpowers w') ∣ 2 := ⟨_, hprod.symm⟩
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd h1 hne1
        · have hb1 : (Q2 ⊔ Subgroup.zpowers w').relIndex T = 1 := by
            rw [h2] at hprod
            omega
          exact (le_antisymm hKle (Subgroup.relIndex_eq_one.mp hb1)).symm
      have hT'eq : T' = Q2' ⊔ Subgroup.zpowers w₀ := by
        have hw₀T' : w₀ ∈ T' := hWT' hw₀W
        have hKle : Q2' ⊔ Subgroup.zpowers w₀ ≤ T' :=
          sup_le (conjSub_mono g hQ2T) (Subgroup.zpowers_le.mpr hw₀T')
        have hprod := Subgroup.relIndex_mul_relIndex Q2' (Q2' ⊔ Subgroup.zpowers w₀) T'
          le_sup_left hKle
        rw [hrelQ2'T'] at hprod
        have hne1 : Q2'.relIndex (Q2' ⊔ Subgroup.zpowers w₀) ≠ 1 := by
          intro h
          exact hw₀Q2' (Subgroup.relIndex_eq_one.mp h
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers w₀)))
        have hdvd : Q2'.relIndex (Q2' ⊔ Subgroup.zpowers w₀) ∣ 2 := ⟨_, hprod.symm⟩
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd h1 hne1
        · have hb1 : (Q2' ⊔ Subgroup.zpowers w₀).relIndex T' = 1 := by
            rw [h2] at hprod
            omega
          exact (le_antisymm hKle (Subgroup.relIndex_eq_one.mp hb1)).symm
      have hQ2Cz : Q2 ≤ Subgroup.centralizer ({z} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp (hQ2C hq) z hzW
      have hw'Cz : w' ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (F7.isElemAbelian_comm hW'ea hw'W' hzW').symm
      have hTCz : T ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [hTeq]
        exact sup_le hQ2Cz (Subgroup.zpowers_le.mpr hw'Cz)
      have hQ2'Cz : Q2' ≤ Subgroup.centralizer ({z} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp (hQ2'W' hq) z hzW'
      have hw₀Cz : w₀ ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (F7.isElemAbelian_comm hW hw₀W hzW).symm
      have hT'Cz : T' ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [hT'eq]
        exact sup_le hQ2'Cz (Subgroup.zpowers_le.mpr hw₀Cz)
      have hG1Cz : G₁ ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [← hA.gen g hg hgG₂]
        exact sup_le hTCz hT'Cz
      have hzG1 : z ∈ G₁ := hA.hyp.sylow₁.1 (hQ1T ((hWD' hzW).1))
      have hzCentG1 : z ∈ Subgroup.centralizer (G₁ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hG1Cz hy) z (by simp)).symm
      have hzCenter : z ∈ centerOf G₁ := ⟨hzG1, hzCentG1⟩
      have hz1 : z = 1 := by
        have hzbot : z ∈ (⊥ : Subgroup G) := by
          rw [← hA.center]
          exact hzCenter
        exact Subgroup.mem_bot.mp hzbot
      exact hz_ne hz1

  let Dμ : Subgroup G := coreIn D G₁
  have hDμ_le_D : Dμ ≤ D := coreIn_le_right D G₁
  have hDμ_le_G1 : Dμ ≤ G₁ := coreIn_le_left D G₁
  have hG1_N : G₁ ≤ Subgroup.normalizer (Dμ : Set G) := le_normalizer_coreIn D G₁
  have hW_le_Dμ : W ≤ Dμ := by
    intro w hwW
    change w ∈ coreIn D G₁
    rw [mem_coreIn]
    have hwG1 : w ∈ G₁ := hA.hyp.sylow₁.1 (hQ1T ((hWD' hwW).1))
    refine ⟨hwG1, fun h hh => ⟨?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff''.mp (le_normalizer_pCoreOf 2 G₁ hh) w).mp
        (hWD' hwW).1
    · exact (mem_conjSub (g := h) (x := w) (H := Q2)).mp (hstep2 h hh hwW)

  have hDμ_bot : Dμ = ⊥ := hA.coreIn_eq_bot hW_le_Dμ hr hr1 hrD
  have hW_bot : W = ⊥ := le_bot_iff.mp (hDμ_bot ▸ hW_le_Dμ)
  apply hQ₁W
  rw [hW_bot]
  have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    simp at hx
    subst hx
    exact Subgroup.one_mem _
  rw [htop]
  exact le_top

end CFSG.Quasithin.F112Crit.APrime

end
