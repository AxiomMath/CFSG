module

public import CFSG.Quasithin.H13.L32NLem1444a
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsInst

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj t).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ht y).mp hy
  · intro hx
    refine ⟨t⁻¹ * x * t, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp hx
    simpa using this

variable [Finite G]

theorem mem_normalizer_commutator {A B : Subgroup G} {t : G}
    (hA : t ∈ Subgroup.normalizer (A : Set G)) (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have h := Subgroup.map_commutator A B (MulAut.conj t).toMonoidHom
  rw [map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB] at h
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have : (MulAut.conj t).toMonoidHom x ∈ (⁅A, B⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
    ⟨x, hx, rfl⟩
  rw [h] at this
  simpa [MulAut.conj_apply] using this

theorem exists_central_of_normalized {P N : Subgroup G} (hP : IsPGroup 2 P) (hNP : N ≤ P)
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ w ∈ N, w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have : (N.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hne : N.subgroupOf P ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNP hx⟩ : ↥P) ∈ N.subgroupOf P := hx
    rw [h] at hx'
    have := congrArg Subtype.val (Subgroup.mem_bot.mp hx')
    simpa using this
  obtain ⟨⟨w, hwN, hwZ⟩, hw1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨w, hwN, fun h => hw1 (Subtype.ext (Subtype.ext h)), fun p hp => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨p, hp⟩)

theorem fsuV1_le_commutator {T V V₂ X : Subgroup G} (hzU : centerOf (fsuU T V) = fsuV1 T V)
    (hUT : fsuU T V ≤ T) (hT2 : IsPGroup 2 T) (hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G))
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hVXU : ⁅V₂, X⁆ ≤ fsuU T V)
    (hVX : Nat.card ↥⁅V₂, X⁆ = 8) (hV₁ : Nat.card ↥(fsuV1 T V) = 2) :
    fsuV1 T V ≤ ⁅V₂, X⁆ := by
  have hne : ⁅V₂, X⁆ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hVX
    omega
  obtain ⟨w, hw, hw1, hwT⟩ := exists_central_of_normalized hT2 (hVXU.trans hUT)
    (fun t ht => mem_normalizer_commutator (hTV₂ ht) (hTX ht)) hne
  have hwV₁ : w ∈ fsuV1 T V := by
    rw [← hzU]
    exact ⟨hVXU hw, Subgroup.mem_centralizer_iff.mpr fun u hu => hwT u (hUT hu)⟩
  intro v hv
  have hcases : ∀ y ∈ fsuV1 T V, y = 1 ∨ y = w := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    right
    obtain ⟨y₀, -, hy₀⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV₁
    have e1 := hy₀ ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
    have e2 := hy₀ ⟨w, hwV₁⟩ (fun h => hw1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  rcases hcases v hv with rfl | rfl
  · exact Subgroup.one_mem _
  · exact hw

theorem exists_mul_oTwoUpper {P T : Subgroup G} (hT : IsSylowTwoOf T P) {g : G} (hg : g ∈ P) :
    ∃ t ∈ T, ∃ g' ∈ oTwoUpper P, g = t * g' := by
  have hTN : T ≤ Subgroup.normalizer ((oTwoUpper P : Subgroup G) : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun y hy => conj_mem_oTwoUpper (Subgroup.le_normalizer
      (hT.1 ht)) hy
  have hg' : g ∈ oTwoUpper P ⊔ T := by rw [C1Pack12.oTwoUpper_sup_eq_of_sylow hT]; exact hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at hg'
  obtain ⟨k, hk, t, ht, rfl⟩ := hg'
  refine ⟨t, ht, t⁻¹ * k * t, ?_, by group⟩
  have := conj_mem_oTwoUpper (Subgroup.le_normalizer (P.inv_mem (hT.1 ht))) hk
  simpa using this

theorem fsuV2_le_commutator (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11) {T L V V₂ X : Subgroup G} {g : G}
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hVX : Nat.card ↥⁅V₂, X⁆ = 8)
    (hVXE : ⁅V₂, X⁆ ≤ l32nE T V V₂ g) : V₂ ≤ ⁅V₂, X⁆ := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  have S := L128P.setting128A h1222 h12213 hs
  have hU : L128A.uA V₂ (fsuV1 T V) = fsuU T V := (lemma12_8_8_six h1222 hs).symm
  have hzU := L1444.zU_eq h1332 h1334 h1222 h12213 h hext
  have hUT : fsuU T V ≤ T := hU ▸ S.uA_le_T
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV₂.1.2.2
  have hVXU : ⁅V₂, X⁆ ≤ fsuU T V := hVXE.trans (inf_le_left.trans inf_le_left)
  have hV1X := fsuV1_le_commutator hzU hUT h.fsu.sylow.1 hTV₂ hTX hVXU hVX (by
    simpa using hs.v1.2.1)
  have hTP : T ≤ p128 T L V := le_inf le_sup_right (le_iInf₂ fun Y ⟨_, _, hY⟩ => hY.2.2)
  obtain ⟨t, ht, g', hg', rfl⟩ :=
    exists_mul_oTwoUpper (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTP) hgP
  have htH : t ∈ l32nH T V := h.le_l32nH hV ht
  have hgood : L128A.Good (fsuV1 T V) (oTwoUpper (p128 T L V)) g' :=
    ⟨hg', fun hN => hgH ((l32nH T V).mul_mem htH hN)⟩
  have htW : t ∈ Subgroup.normalizer ((l32nW T V V₂ : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun w hw => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ htH) w).mp hw.1
    · exact (Subgroup.mem_normalizer_iff.mp
        (F7.normalizer_le_normalizer_centralizer V₂ (hTV₂ ht)) w).mp hw.2
  have hWg : CFSG.conjugate (l32nW T V V₂) (t * g') =
      rconj (L128A.wA V₂ (fsuV1 T V)) g' := by
    ext x
    rw [show CFSG.conjugate (l32nW T V V₂) (t * g') = rconj (l32nW T V V₂) (t * g') from rfl,
      mem_rconj, mem_rconj, L128A.wA, hU]
    rw [show t * g' * x * (t * g')⁻¹ = t * (g' * x * g'⁻¹) * t⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp htW _).symm
  have hWgT : CFSG.conjugate (l32nW T V V₂) (t * g') ≤ T := hWg ▸ S.rconj_wA_le_T hgood
  have hEU : l32nE T V V₂ (t * g') ≤
      L128A.uA V₂ (fsuV1 T V) ⊓ rconj (L128A.uA V₂ (fsuV1 T V)) g' := by
    rw [l32nE, hWg]
    refine le_inf (hU ▸ inf_le_left.trans inf_le_left) ?_
    exact inf_le_right.trans (Subgroup.map_mono inf_le_left)
  have hWgI : CFSG.conjugate (l32nW T V V₂) (t * g') ≤
      oTwoUpper (p128 T L V) ⊔ L128A.uA V₂ (fsuV1 T V) := by
    rw [hWg, ← S.sup_rconj_uA_eq hgood]
    exact (Subgroup.map_mono inf_le_left).trans le_sup_right
  have hcomm : ⁅l32nE T V V₂ (t * g'), CFSG.conjugate (l32nW T V V₂) (t * g')⁆ ≤ V₂ :=
    (Subgroup.commutator_mono hEU hWgI).trans (S.commutator_inf_rconj_le hgood)
  have h4 := (h12811 G T L V 3 (fsuV1 T V) V₂ hs (t * g') hgP hgH).2.2
  rw [show zU128 V (fsuV1 T V) = fsuV1 T V from hzU] at h4
  obtain ⟨a, haV₂, haV₁⟩ : ∃ a ∈ V₂, a ∉ fsuV1 T V := S.exists_mem_not_mem
  by_contra hnot
  have haX : a ∉ ⁅V₂, X⁆ := fun haX => hnot fun v hv => by
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
      by_contra hc
      push Not at hc
      have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hc
      have h2 := hs.v1.2.1
      rw [this, Subgroup.card_bot] at h2
      norm_num at h2
    rcases S.V_cases hz hz1 haV₂ haV₁ v hv with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hV1X hz
    · exact haX
    · exact Subgroup.mul_mem _ (hV1X hz) haX
  have hle : ⁅V₂, X⁆ ≤ V₂ := by
    intro b hb
    have hbE : b ∈ l32nE T V V₂ (t * g') := hVXE hb
    have hbC : b ∈ centralizerMod (fsuV1 T V) (l32nE T V V₂ (t * g'))
        (CFSG.conjugate (l32nW T V V₂) (t * g')) := by
      refine ⟨hbE, Subgroup.centralizer_le_normalizer _ ?_, fun x hx => ?_⟩
      · rw [← hzU]
        exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (Subgroup.mem_centralizer_iff.mp hy.2 b (hVXU hb)).symm
      · have hxN : x ∈ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) :=
          mem_normalizer_commutator (hTV₂ (hWgT hx)) (hTX (hWgT hx))
        have h1 : b * x * b⁻¹ * x⁻¹ ∈ ⁅V₂, X⁆ := by
          rw [show b * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) by group]
          exact Subgroup.mul_mem _ hb ((Subgroup.mem_normalizer_iff.mp hxN _).mp
            (Subgroup.inv_mem _ hb))
        have h2 : b * x * b⁻¹ * x⁻¹ ∈ V₂ :=
          hcomm (Subgroup.commutator_mem_commutator hbE hx)
        obtain ⟨z, hz, hz1⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
          by_contra hc
          push Not at hc
          have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hc
          have h2' := hs.v1.2.1
          rw [this, Subgroup.card_bot] at h2'
          norm_num at h2'
        rcases S.V_cases hz hz1 haV₂ haV₁ _ h2 with h3 | h3 | h3 | h3
        · rw [h3]; exact Subgroup.one_mem _
        · rw [h3]; exact hz
        · exact absurd (h3 ▸ h1) haX
        · exfalso
          apply haX
          have : a = z⁻¹ * (b * x * b⁻¹ * x⁻¹) := by rw [h3]; group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV1X hz)) h1
    have := h4.le (Subgroup.mem_sup_left hbC)
    exact (sup_le le_rfl hs.le) this
  have hcard := Subgroup.card_le_of_le hle
  rw [hVX, hV₂.1.2.1] at hcard
  norm_num at hcard

end CFSG.Quasithin.H13.L14413
