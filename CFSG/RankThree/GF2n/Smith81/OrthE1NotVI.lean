module

public import CFSG.RankThree.GF2n.Smith81.OrthNoA2
public import CFSG.RankThree.GF2n.Smith81.InvolCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem not_caseVI_of_caseE1 [Finite G] {M Q Z B : Subgroup G}
    (hc : Cfg M Q Z B) {t : G} (ht : CtxD4 M Q Z B t) (hE : CaseE1 M Q Z B t) :
    ¬ CaseVI M Q Z (Lgen M (LB M Q B)) := by
  intro hVI
  obtain ⟨hQ, hNt, hR⟩ := hE
  obtain ⟨-, htL, htQ, -⟩ := ht
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨f, -, hf, -⟩ := hc.ctx.hyp.cp
  obtain ⟨n, hn⟩ : ∃ n, CaseE6 M Q Z B n := hVI
  obtain ⟨V₁, V₂, hL⟩ := CaseE6.exists_linSetup hn
  have hWn : Nat.card Q = Nat.card Z ^ (2 * n + 1) := LinSetup.width hc.ctx.hyp hL
  have hn4 : n = 4 := by
    have h := Nat.pow_right_injective hq2 (hWn.symm.trans hQ)
    omega
  subst hn4
  obtain ⟨K, fK, finK, hKc, φ, hφr, hφk, -⟩ := hn
  haveI : CharP K 2 := orthE2_charP_two (hKc.trans hf)
  have hker : ∀ s : ↥(Lgen M (LB M Q B)), φ s = 1 ↔ (s : G) ∈ Q := fun s => by
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have htS : t ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) htL
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, R = Rt M (LB M Q B) t := ⟨_, rfl⟩
  have hRS : R ≤ Lgen M (LB M Q B) := by
    rw [hRdef]
    exact Rt_le_Lgen M (LB M Q B) t
  have hNR : Nt M (LB M Q B) t = inSubgroup (pCore 2) R := by
    rw [hRdef]
    rfl
  rw [← hRdef, hNR] at hR
  let ψ : ↥R →* GL (Fin 4) K := φ.comp (Subgroup.inclusion hRS)
  have hψker : ∀ r : ↥R, ψ r = 1 ↔ (r : G) ∈ Q := fun r => hker (Subgroup.inclusion hRS r)
  have hu1 : φ ⟨t, htS⟩ ≠ 1 := fun h => htQ ((hker _).mp h)
  have hu2 : φ ⟨t, htS⟩ * φ ⟨t, htS⟩ = 1 := by
    rw [← map_mul]
    apply (hker _).mpr
    show t * t ∈ Q
    rw [← pow_two]
    exact hc.ctx.sq_mem_Q_of_mem_LB htL
  have hcomQ : ∀ m ∈ M, ⁅conjSubgroup m (LB M Q B), conjSubgroup m (LB M Q B)⁆ ≤ Q := by
    intro m hm
    have h := (hc.ctx.conj_of_mem hm).commutator_LB_le_Q
    rw [hc.ctx.LB_conj hm] at h
    exact h
  have hkey : ∀ m ∈ M, ∀ a b : ↥(Lgen M (LB M Q B)), (a : G) ∈ conjSubgroup m (LB M Q B) →
      (b : G) ∈ conjSubgroup m (LB M Q B) → φ a * φ b = φ b * φ a := by
    intro m hm a b ha hb
    have hmem : ⁅(a : G), (b : G)⁆ ∈ Q := hcomQ m hm (Subgroup.commutator_mem_commutator ha hb)
    have h1 : φ ⁅a, b⁆ = 1 := (hker _).mpr hmem
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcomm : ∀ g ∈ ψ.range, g * φ ⟨t, htS⟩ = φ ⟨t, htS⟩ * g := by
    let C : Subgroup ↥(Lgen M (LB M Q B)) :=
      (Subgroup.centralizer ({φ ⟨t, htS⟩} : Set (GL (Fin 4) K))).comap φ
    have hRC : R ≤ C.map (Lgen M (LB M Q B)).subtype := by
      rw [hRdef]
      unfold Rt
      refine iSup_le fun m => iSup_le fun hm => iSup_le fun hmt => ?_
      intro x hx
      have hxS : x ∈ Lgen M (LB M Q B) :=
        (le_iSup₂ (f := fun (m : G) (_ : m ∈ M) => conjSubgroup m (LB M Q B)) m hm) hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
      show φ ⟨x, hxS⟩ ∈ Subgroup.centralizer ({φ ⟨t, htS⟩} : Set (GL (Fin 4) K))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hkey m hm ⟨t, htS⟩ ⟨x, hxS⟩ hmt hx
    rintro g ⟨r, rfl⟩
    obtain ⟨c, hcC, hcr⟩ := Subgroup.mem_map.mp (hRC r.2)
    have hcinc : c = Subgroup.inclusion hRS r := Subtype.ext hcr
    have hcC' : φ c ∈ Subgroup.centralizer ({φ ⟨t, htS⟩} : Set (GL (Fin 4) K)) := hcC
    have hcent := (Subgroup.mem_centralizer_iff.mp hcC') (φ ⟨t, htS⟩) (Set.mem_singleton _)
    show φ (Subgroup.inclusion hRS r) * φ ⟨t, htS⟩ = φ ⟨t, htS⟩ * φ (Subgroup.inclusion hRS r)
    rw [← hcinc]
    exact hcent.symm
  obtain ⟨X₀, hX₀le, hX₀norm, hX₀pow, d, hcardX, m, hm, hdvd⟩ :=
    involution_centralizer_index hu2 hu1 hcomm
  have hP₀mem : ∀ r : ↥R, r ∈ X₀.comap ψ ↔ ψ r ∈ X₀ := fun r => Iff.rfl
  have hψX : ∀ r : ↥R, ψ r ∈ ψ.range := fun r => MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hP₀norm : (X₀.comap ψ).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hP₀mem] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact hX₀norm _ (hψX g) _ hx
  have hP₀x : ∀ x : ↥R, x ∈ X₀.comap ψ → ∃ j : ℕ, x ^ 2 ^ j = 1 := by
    intro x hx
    have h4 : ψ (x ^ 4) = 1 := by
      rw [map_pow]
      exact hX₀pow _ ((hP₀mem x).mp hx)
    have hq : ((x ^ 4 : ↥R) : G) ∈ Q := (hψker (x ^ 4)).mp h4
    obtain ⟨k, hk⟩ := isPGroup_Q' hc.ctx.hyp ⟨_, hq⟩
    refine ⟨k + 2, ?_⟩
    have hk' : (x ^ 4) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    calc x ^ 2 ^ (k + 2) = (x ^ 4) ^ 2 ^ k := by
          rw [← pow_mul]
          congr 1
          ring
      _ = 1 := hk'
  have hP₀2 : IsPGroup 2 (X₀.comap ψ) := fun g => by
    obtain ⟨j, hj⟩ := hP₀x g.1 g.2
    exact ⟨j, Subtype.ext hj⟩
  have hPpc : X₀.comap ψ ≤ CFSG.pCore 2 ↥R := le_sSup ⟨hP₀norm, hP₀2⟩
  have hPN : X₀.comap ψ ≤ (inSubgroup (pCore 2) R).subgroupOf R := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hPpc hx, rfl⟩
  have hidx2 : (X₀.subgroupOf ψ.range).index = d := by
    have h2 := Subgroup.card_mul_index (X₀.subgroupOf ψ.range)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀le).toEquiv] at h2
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := X₀))
    rw [h2, hcardX]
  have hPidx : (X₀.comap ψ).index = d := by
    rw [Subgroup.index_comap]
    exact hidx2
  have hq2N : Nat.card K ^ 2 ∣ Nat.card (↥R ⧸ (inSubgroup (pCore 2) R).subgroupOf R) := by
    unfold QuotSat IsOmegaPlus IsOmegaMinus at hR
    rcases hR with ⟨hNR, K₂, fK₂, finK₂, ⟨hK₂, hne⟩⟩ | ⟨hNR, K₂, fK₂, finK₂, ⟨hK₂, b, c, hirr, hne⟩⟩
    · have eR := hne.some
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hΩ := orthE2_card_omega_plus_two (K := K₂) (by rw [hK₂]; exact hq4)
      have hK₂K : Nat.card K₂ = Nat.card K := hK₂.trans hKc.symm
      have hdivZ : ((Nat.card K₂ : ℕ) : ℤ) ^ 2 ∣
          (Nat.card ↥(StatedOmega (StatedQuadPlus 2 K₂)) : ℤ) := by
        rw [hΩ]
        exact dvd_mul_right _ _
      have hdivN : Nat.card K₂ ^ 2 ∣ Nat.card ↥(StatedOmega (StatedQuadPlus 2 K₂)) := by
        exact_mod_cast hdivZ
      rw [Nat.card_congr eR.toEquiv, ← hK₂K]
      exact hdivN
    · have eR := hne.some
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hΩ := orthE2_card_omega_minus_two (K := K₂) hirr
      have hK₂K : Nat.card K₂ = Nat.card K := hK₂.trans hKc.symm
      have hdivZ : ((Nat.card K₂ : ℕ) : ℤ) ^ 2 ∣
          (Nat.card ↥(StatedOmega (StatedQuadMinus 2 K₂ b c)) : ℤ) := by
        rw [hΩ]
        exact dvd_mul_right _ _
      have hdivN : Nat.card K₂ ^ 2 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 2 K₂ b c)) := by
        exact_mod_cast hdivZ
      rw [Nat.card_congr eR.toEquiv, ← hK₂K]
      exact hdivN
  have hq2d : Nat.card K ^ 2 ∣ d := by
    rw [← hPidx]
    exact dvd_trans hq2N (Subgroup.index_dvd_of_le hPN)
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hqm : Nat.card K ∣ m := by
    have h : Nat.card K * Nat.card K ∣ Nat.card K * m := by
      rw [← pow_two]
      exact dvd_trans hq2d hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hqpos h
  have h2m : 2 ∣ m := dvd_trans (even_iff_two_dvd.mp (involCard_even (K := K))) hqm
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m)

end CFSG.RankThree.GF2n.Smith81
