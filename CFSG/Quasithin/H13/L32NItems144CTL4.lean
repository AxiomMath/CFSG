module

public import CFSG.Quasithin.H13.L32NItems144CTL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem conj_mem_of_forall (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two)
    (hV : StmtL32NModule) {d : G} (hdH : d ∈ l32nH T V) (hd1 : d ≠ 1)
    (hall : ∀ h ∈ l32nH T V, h⁻¹ * d * h ∈ T ⊓ Subgroup.centralizer (L : Set G)) : False := by
  set H := l32nH T V with hHdef
  set P : Subgroup G := (Subgroup.normalClosure {(⟨d, hdH⟩ : ↥H)}).map H.subtype with hP
  have hPD : P ≤ T ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hP, Subgroup.map_le_iff_le_comap, Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨d', hd', hconj⟩ := hx
    rw [Set.mem_singleton_iff] at hd'
    subst hd'
    obtain ⟨u, rfl⟩ := isConj_iff.mp hconj
    show ((u * ⟨d, hdH⟩ * u⁻¹ : ↥H) : G) ∈ T ⊓ Subgroup.centralizer (L : Set G)
    have := hall _ (H.inv_mem u.2)
    simpa using this
  have hdP : d ∈ P := ⟨⟨d, hdH⟩, Subgroup.subset_normalClosure (Set.mem_singleton _), rfl⟩
  have hP1 : P ≠ ⊥ := fun h => hd1 (by rw [h] at hdP; exact Subgroup.mem_bot.mp hdP)
  have hP2 : IsPGroup 2 P := (isPGroup_D S).to_le hPD
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have hn := (Subgroup.normalClosure_normal (s := {(⟨d, hdH⟩ : ↥H)}))
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hn.conj_mem y hy _, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩, ?_, ?_⟩
      · have := hn.conj_mem y hy (⟨h, hh⟩⁻¹)
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        rw [show (y : G) = h * x * h⁻¹ from hyx]
        group
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hPD hx).2 l hl).symm)
  have hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G) := sup_le hLP (S.TH.trans hHP)
  exact lemma12_8_3_four h12213 (S.hyp.hyp1281One h13322 hV) (S.hyp.isTSub_fsuV1 hV)
    (hHP.trans (normalizer_le_M S h13322 hP1 hP2 hLT))

theorem exists_conj_mem (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two) (hV : StmtL32NModule)
    {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g) (hσ2 : σ * σ = 1)
    (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ (hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V),
      D.ρ ⟨c, hcN⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) {d : G}
    (hdD : d ∈ T ⊓ Subgroup.centralizer (L : Set G)) (hd1 : d ≠ 1) :
    ∃ j : ℕ, (c ^ j)⁻¹ * (S.cfg.z * d) * c ^ j ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
  by_contra hne
  push Not at hne
  have hcH : c ∈ l32nH T V := oTwoUpper_le _ hcK
  have hdC : d ∈ Subgroup.centralizer (fsuU T V : Set G) := centralizer_L_le_cent S hdD.2
  have hdH : d ∈ l32nH T V := S.cent_le_H hdC
  have hzZ : S.cfg.z ∈ centerOf (fsuU T V) := S.mem_center_iff.mpr (Or.inr rfl)
  have hzV1 : S.cfg.z ∈ fsuV1 T V := S.zU ▸ hzZ
  have hCn : l32nH T V ≤ Subgroup.normalizer (Subgroup.centralizer (fsuU T V : Set G) : Set G) :=
    (L14332.l32nH_le_normalizer_fsuU T V).trans (normalizer_le_normalizer_centralizer'' _)
  have hconj : ∀ j : ℕ, (c ^ j)⁻¹ * d * c ^ j ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    intro j
    have hcj : c ^ j ∈ l32nH T V := (l32nH T V).pow_mem hcH j
    have he : (c ^ j)⁻¹ * d * c ^ j ∈ Subgroup.centralizer (fsuU T V : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hCn hcj)) d).mp
        hdC
      simpa using this
    obtain ⟨m, hmV, hmD⟩ := exists_mem_V_mul_mem S he
    have hmC : m ∈ Subgroup.centralizer (fsuU T V : Set G) := by
      have h1 := (Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).inv_mem (centralizer_L_le_cent S hmD.2)) he
      rwa [show (((c ^ j)⁻¹ * d * c ^ j) * m⁻¹)⁻¹ * ((c ^ j)⁻¹ * d * c ^ j) = m by group] at h1
    rcases S.mem_center_iff.mp ⟨V_le_U hmV, hmC⟩ with hm1 | hmz
    · rw [hm1, inv_one, mul_one] at hmD
      exact hmD
    · exfalso
      apply hne j
      have hzc : (c ^ j)⁻¹ * S.cfg.z * c ^ j = S.cfg.z := by
        have := S.comm_V1 ((l32nH T V).inv_mem hcj) hzV1
        simpa using this
      have hze : S.cfg.z * ((c ^ j)⁻¹ * d * c ^ j) = ((c ^ j)⁻¹ * d * c ^ j) * S.cfg.z :=
        Subgroup.mem_centralizer_iff.mp he _ hzZ.1
      have hz2 : S.cfg.z * S.cfg.z = 1 := by
        rw [← pow_two]
        exact S.elem.2 _ hzV1.1
      have hzinv : S.cfg.z⁻¹ = S.cfg.z := (eq_inv_of_mul_eq_one_left hz2).symm
      rw [hmz, hzinv] at hmD
      have e2 : (c ^ j)⁻¹ * (S.cfg.z * d) * c ^ j = ((c ^ j)⁻¹ * d * c ^ j) * S.cfg.z := by
        calc (c ^ j)⁻¹ * (S.cfg.z * d) * c ^ j =
            ((c ^ j)⁻¹ * S.cfg.z * c ^ j) * ((c ^ j)⁻¹ * d * c ^ j) := by group
          _ = ((c ^ j)⁻¹ * d * c ^ j) * S.cfg.z := by rw [hzc, hze]
      rw [e2]
      exact hmD
  refine conj_mem_of_forall S h12213 h13322 hV hdH hd1 fun h hh => ?_
  have hTS := S.hyp.isSylowTwoOf_l32nH hV
  have hHKT := C1Pack12.oTwoUpper_sup_eq_of_sylow hTS
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper (l32nH T V) : Set G) :=
    S.TH.trans (le_normalizer_oTwoUpper _)
  have hmem : h ∈ ((oTwoUpper (l32nH T V) ⊔ T : Subgroup G) : Set G) := by
    rw [hHKT]; exact hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hmem
  obtain ⟨k, hkK, t, htT, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨j, hj⟩ := exists_mul_pow_mem_normalizer S hσW hσ2 h21 hcK hcfpf hσc
    ((oTwoUpper _).inv_mem hkK)
  have hnD := (Subgroup.mem_normalizer_iff.mp hj _).mp (hconj j)
  have htD := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem
    (T_le_normalizer S htT)) _).mp hnD
  have e : (k * t)⁻¹ * d * (k * t) =
      t⁻¹ * ((k⁻¹ * c ^ j) * ((c ^ j)⁻¹ * d * c ^ j) * (k⁻¹ * c ^ j)⁻¹) * t⁻¹⁻¹ := by
    group
  rw [e]
  exact htD

end Setup

end L1444CTL

end CFSG.Quasithin.H13
