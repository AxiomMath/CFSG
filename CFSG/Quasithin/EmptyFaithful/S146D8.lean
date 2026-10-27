module

public import CFSG.Quasithin.EmptyFaithful.S146D7
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section TwoFixed

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.commutator_VZ_mem (S : Setting146 G T M) {b : G} (hbM : b ∈ M)
    (hbH : b ∈ mcOf T) {v : G} (hv : v ∈ VZ T M) : b * v * b⁻¹ * v⁻¹ ∈ Zz := by
  have hVN : M = Subgroup.normalizer (VZ T M : Set G) := S.hyp1281.normalizer_VZ.symm
  have hVcard : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hZcard : Nat.card Zz = 2 := S.card_Z
  have hZV : Zz ≤ VZ T M := le_conjClosure _ _
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hHTM
  have hVU : VZ T M ≤ uOfL22 T M := le_conjClosure _ _
  have hvN : v ∈ Subgroup.normalizer (Zz : Set G) := hUN (hVU hv)
  have hbc : ∀ z ∈ Zz, b * z * b⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hbH z hz
    calc b * z * b⁻¹ = (b * z) * b⁻¹ := rfl
      _ = (z * b) * b⁻¹ := by rw [← this]
      _ = z := by group
  have hbc' : ∀ z ∈ Zz, b⁻¹ * z * b = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hbH) z hz
    calc b⁻¹ * z * b = (b⁻¹ * z) * b⁻¹⁻¹ := by group
      _ = (z * b⁻¹) * b⁻¹⁻¹ := by rw [← this]
      _ = z := by group
  by_cases hvZ : v ∈ Zz
  · rw [hbc v hvZ]
    simp
  · have hw : b * v * b⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hVN ▸ hbM) v).mp hv
    have hwZ : b * v * b⁻¹ ∉ Zz := by
      intro hz
      apply hvZ
      have h1 := hbc' _ hz
      have e : b⁻¹ * (b * v * b⁻¹) * b = v := by group
      rw [e] at h1
      rw [h1]
      exact hz
    have h2 : v⁻¹ * (b * v * b⁻¹) ∈ Zz := inv_mul_mem_of_card_four hZV hVcard hZcard hv hw hvZ hwZ
    have e : b * v * b⁻¹ * v⁻¹ = v * (v⁻¹ * (b * v * b⁻¹)) * v⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hvN _).mp h2

theorem Setting146.isPGroup_of_decomp (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) : IsPGroup 2 U₁ := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hUQ : uOfL22 T M ≤ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf hG
  have hG₁U : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hKU : K ≤ Subgroup.normalizer (uOfL22 T M : Set G) := hKG.trans hG₁U
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have h1 : ⁅uOfL22 T M, K⁆ ≤ uOfL22 T M := S145.commutator_le_of_le_normalizer hKU
  have h2 : U₁ ⊔ U₂ ≤ uOfL22 T M := by
    rw [← hdec.sup]
    exact sup_le h1 hZU
  exact (pCoreOf_isPGroup 2 (mcOf T)).to_le ((le_sup_left.trans h2).trans hUQ)

theorem Setting146.lt_of_decomp (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) : Zz < U₁ := by
  rcases hdec.natural with ⟨-, -, hirr⟩ | ⟨-, ⟨-, hirr, -⟩ | ⟨h5, -⟩⟩
  · exact hirr.1
  · exact hirr.1
  · refine lt_of_le_of_ne hdec.Z₁ fun h => ?_
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := Zz) (S.isPGroup_of_decomp hK hdec)
    rw [h5, ← h, Subgroup.relIndex_self] at h1
    norm_num at h1

theorem Setting146.not_le_B (S : Setting146 G T M) {K : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (c21K : Conc14621 T K) (c22K : Conc14622 T M K) : ¬ K ≤ M ⊓ mcOf T := by
  intro hKB
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hTB : T ≤ M ⊓ mcOf T := le_inf hTM hTH
  have hNH : Subgroup.normalizer (Zz : Set G) = mcOf T := S.normalizer_Z
  have hHN : ∀ g ∈ mcOf T, g ∈ Subgroup.normalizer (Zz : Set G) := fun g hg => by
    rw [hNH]; exact hg
  have hPN : mcOf T ≤ Subgroup.normalizer (perfectCore (mcOf T) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (mcOf T))
  obtain ⟨N, hKN, hNB, hHN'⟩ : ∃ N : Subgroup G, K ≤ N ∧ N ≤ M ⊓ mcOf T ∧
      mcOf T ≤ Subgroup.normalizer (N : Set G) := by
    rcases c21K with ⟨hper, -⟩ | ⟨⟨t, ht, htn, hper⟩, -⟩ | ⟨Kp, hKp, hKpK, hHK, hHKp, hper, -, -⟩
    · exact ⟨K, le_rfl, hKB, by rw [← hper]; exact hPN⟩
    · refine ⟨perfectCore (mcOf T), by rw [hper]; exact le_sup_left, ?_, hPN⟩
      rw [hper]
      refine sup_le hKB ?_
      intro x hx
      have hx' : t⁻¹ * x * t ∈ K := mem_conjSub.mp hx
      have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [e]
      exact (M ⊓ mcOf T).mul_mem ((M ⊓ mcOf T).mul_mem (hTB ht) (hKB hx')) ((M ⊓ mcOf T).inv_mem (hTB ht))
    · exact ⟨K, le_rfl, hKB, hHK⟩
  have hUW : uOfL22 T M ≤ centralizerMod Zz (uOfL22 T M) N := by
    refine conjClosure_le fun h hh v hv => ?_
    have hhU : h * v * h⁻¹ ∈ uOfL22 T M := mem_conjClosure hh hv
    refine ⟨hhU, S.conjClosure_le_normalizer_Z hHTM hhU, fun n hn => ?_⟩
    have hn' : h⁻¹ * n * h ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hHN' (Subgroup.inv_mem _ hh)) n).mp hn
      simpa using this
    have hb := S.commutator_VZ_mem (hNB hn').1 (hNB hn').2 hv
    have hb' : v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹ ∈ Zz := by
      have := Subgroup.inv_mem _ hb
      have e : ((h⁻¹ * n * h) * v * (h⁻¹ * n * h)⁻¹ * v⁻¹)⁻¹ =
          v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹ := by group
      rwa [e] at this
    have h3 := (Subgroup.mem_normalizer_iff.mp (hHN h hh) _).mp hb'
    have e2 : h * (v * (h⁻¹ * n * h) * v⁻¹ * (h⁻¹ * n * h)⁻¹) * h⁻¹ =
        (h * v * h⁻¹) * n * (h * v * h⁻¹)⁻¹ * n⁻¹ := by group
    rwa [e2] at h3
  have hcomm : ⁅uOfL22 T M, K⁆ ≤ Zz := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have := (hUW hu).2.2 k (hKN hk)
    simpa [commutatorElement_def] using this
  obtain ⟨U₁, U₂, s, hdec⟩ := c22K.1
  have hlt := S.lt_of_decomp hK hdec
  have hU₁ : U₁ ≤ Zz := by
    have h1 : ⁅uOfL22 T M, K⁆ ⊔ Zz ≤ Zz := sup_le hcomm le_rfl
    rw [hdec.sup] at h1
    exact le_sup_left.trans h1
  exact hlt.not_ge hU₁

end TwoFixed

section Product

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem mem_pCoreOf_of_mem_pCore {H : Subgroup G} {x : ↥H} (h : x ∈ CFSG.pCore 2 ↥H) :
    (x : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff x).mpr h

theorem Setting146.mem_T_of_decomp (S : Setting146 G T M) {K K' : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K) (hc' : ⁅K', K⁆ ≤ pCoreOf 2 (mcOf T))
    {B : Subgroup G} (hTB : T ≤ B) (hKB : K ⊓ B ≤ T) {a k₁ k₂ : ↥(mcOf T)} (haB : (a : G) ∈ B)
    (hk₁ : (k₁ : G) ∈ K) (hk₂ : (k₂ : G) ∈ K')
    (hrr : (QuotientGroup.mk k₁ : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) * QuotientGroup.mk k₂ =
      QuotientGroup.mk a) : (k₁ : G) ∈ T := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hQT : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_le_T hHTM
  have hcomm₂ := modO2Image_commute hc'
  refine S.mem_of_normalizes hK hL3 hk₁ fun d hd => ?_
  have hdH : d ∈ mcOf T := hTH hd.1
  set d' : ↥(mcOf T) := ⟨d, hdH⟩ with hd'
  have hbk₂ : (QuotientGroup.mk k₂ : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) ∈ modO2Image (mcOf T) K' :=
    ⟨k₂, Subgroup.mem_subgroupOf.mpr hk₂, rfl⟩
  have hbd : (QuotientGroup.mk d' : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) ∈ modO2Image (mcOf T) K :=
    ⟨d', Subgroup.mem_subgroupOf.mpr hd.2, rfl⟩
  have hcm := hcomm₂ _ hbk₂ _ hbd
  have h1 : (QuotientGroup.mk (a * d' * a⁻¹) : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) =
      QuotientGroup.mk (k₁ * d' * k₁⁻¹) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← hrr]
    calc (QuotientGroup.mk k₁ * QuotientGroup.mk k₂ * QuotientGroup.mk d' *
          (QuotientGroup.mk k₁ * QuotientGroup.mk k₂)⁻¹ :
            ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T))
        = QuotientGroup.mk k₁ * (QuotientGroup.mk k₂ * QuotientGroup.mk d') *
            (QuotientGroup.mk k₂)⁻¹ * (QuotientGroup.mk k₁)⁻¹ := by group
      _ = QuotientGroup.mk k₁ * (QuotientGroup.mk d' * QuotientGroup.mk k₂) *
            (QuotientGroup.mk k₂)⁻¹ * (QuotientGroup.mk k₁)⁻¹ := by rw [hcm]
      _ = QuotientGroup.mk k₁ * QuotientGroup.mk d' * (QuotientGroup.mk k₁)⁻¹ := by group
  have h2 := mem_pCoreOf_of_mem_pCore (QuotientGroup.eq.mp h1)
  have hyB : (a : G) * d * (a : G)⁻¹ ∈ B := B.mul_mem (B.mul_mem haB (hTB hd.1)) (B.inv_mem haB)
  have e : (k₁ : G) * d * (k₁ : G)⁻¹ = ((a : G) * d * (a : G)⁻¹) *
      (((a : G) * d * (a : G)⁻¹)⁻¹ * ((k₁ : G) * d * (k₁ : G)⁻¹)) := by
    group
  have hmemB : (k₁ : G) * d * (k₁ : G)⁻¹ ∈ B := by
    rw [e]
    exact B.mul_mem hyB (hTB (hQT (by simpa using h2)))
  exact hKB ⟨K.mul_mem (K.mul_mem hk₁ hd.2) (K.inv_mem hk₁), hmemB⟩

theorem Setting146.mem_of_sup (S : Setting146 G T M) {K K' : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hK' : K' ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K)
    (hL3' : KbarIsL3Two K') (hc : ⁅K, K'⁆ ≤ pCoreOf 2 (mcOf T)) {B : Subgroup G} (hTB : T ≤ B)
    (hKB : K ⊓ B ≤ T) (hKB' : K' ⊓ B ≤ T) {a : G} (ha : a ∈ K ⊔ K') (haB : a ∈ B) : a ∈ T := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hQT : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_le_T hHTM
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKH' : K' ≤ mcOf T := le_of_mem_cComp hK'
  have hc' : ⁅K', K⁆ ≤ pCoreOf 2 (mcOf T) := by
    rw [Subgroup.commutator_comm]
    exact hc
  have hcomm₁ := modO2Image_commute hc
  have haH : a ∈ mcOf T := (sup_le hKH hKH') ha
  have hmem : (QuotientGroup.mk ⟨a, haH⟩ : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) ∈
      modO2Image (mcOf T) K ⊔ modO2Image (mcOf T) K' := by
    have h1 : (⟨a, haH⟩ : ↥(mcOf T)) ∈ (K ⊔ K').subgroupOf (mcOf T) := ha
    rw [Subgroup.subgroupOf_sup hKH hKH'] at h1
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T))) h1
    rw [Subgroup.map_sup] at this
    exact this
  have hN : modO2Image (mcOf T) K ≤ Subgroup.normalizer (modO2Image (mcOf T) K' : Set _) :=
    le_normalizer_of_forall_commute hcomm₁
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hmem
  obtain ⟨r₁, hr₁, r₂, hr₂, hrr⟩ := hmem
  obtain ⟨k₁, hk₁, rfl⟩ := Subgroup.mem_map.mp hr₁
  obtain ⟨k₂, hk₂, rfl⟩ := Subgroup.mem_map.mp hr₂
  have hrr' : (QuotientGroup.mk k₁ : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) * QuotientGroup.mk k₂ =
      QuotientGroup.mk ⟨a, haH⟩ := hrr
  have hrr'' : (QuotientGroup.mk k₂ : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) * QuotientGroup.mk k₁ =
      QuotientGroup.mk ⟨a, haH⟩ := by
    rw [← hrr']
    exact (hcomm₁ _ hr₁ _ hr₂).symm
  have hk₁' : (k₁ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₁
  have hk₂' : (k₂ : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk₂
  have hT₁ : (k₁ : G) ∈ T := S.mem_T_of_decomp hK hL3 hc' hTB hKB haB hk₁' hk₂' hrr'
  have hT₂ : (k₂ : G) ∈ T := S.mem_T_of_decomp hK' hL3' hc hTB hKB' haB hk₂' hk₁' hrr''
  have h3 : (QuotientGroup.mk (k₁ * k₂) : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) =
      QuotientGroup.mk ⟨a, haH⟩ := by
    rw [QuotientGroup.mk_mul]
    exact hrr'
  have h4 := mem_pCoreOf_of_mem_pCore (QuotientGroup.eq.mp h3)
  have e : a = ((k₁ : G) * k₂) * (((k₁ : G) * k₂)⁻¹ * a) := by group
  rw [e]
  exact T.mul_mem (T.mul_mem hT₁ hT₂) (hQT (by simpa using h4))

end Product

section Components

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem c21_cases (hTH : T ≤ mcOf T) (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K)
    {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) :
    perfectCore (mcOf T) = K ∨
      ∃ K' ∈ cComp (mcOf T), K' ≠ K ∧ perfectCore (mcOf T) = K ⊔ K' ∧ KbarIsL3Two K ∧
        KbarIsL3Two K' := by
  have hle : ∀ L ∈ cComp (mcOf T), L ≤ perfectCore (mcOf T) := fun L hL =>
    le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
  rcases c21 K hK with ⟨hper, -⟩ | ⟨⟨t, ht, htn, hper⟩, hL3⟩ | ⟨Kp, hKp, hKpK, -, -, hper, hL3, hL3p⟩
  · exact Or.inl hper
  · right
    have hK' : conjSub t K ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH ht)
    have hne : conjSub t K ≠ K := fun heq => htn (A38.map_conj_eq_iff.mp heq)
    refine ⟨conjSub t K, hK', hne, hper, hL3, ?_⟩
    rcases c21 _ hK' with ⟨hper', -⟩ | ⟨-, hL'⟩ | ⟨Kp, hKp, hKpK, -, -, hper', hL', -⟩
    · exact absurd (eq_of_le_cComp hK' hK (hper' ▸ hle K hK)).symm hne
    · exact hL'
    · exact hL'
  · exact Or.inr ⟨Kp, hKp, hKpK, hper, hL3, hL3p⟩

theorem Setting146.mem_T_of_mem_perfectCore (h37 : A37ForSQTK) (S : Setting146 G T M)
    (hB : HypB146 T M) (c2122 : ∀ K ∈ cComp (mcOf T), Conc14621 T K ∧ Conc14622 T M K) {a : G}
    (ha : a ∈ perfectCore (mcOf T)) (haB : a ∈ M ⊓ mcOf T) : a ∈ T := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hTB : T ≤ M ⊓ mcOf T := le_inf hTM hTH
  have hnsolv : ¬ Group.IsSolvable ↥(mcOf T) := fun hs => hHTM.2 (S.theorem_14_6_18 hB hHTM.1 hs)
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable (H := mcOf T) (X := mcOf T) le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hnsolv
  have hLB : ∀ L ∈ cComp (mcOf T), L ⊓ (M ⊓ mcOf T) ≤ T := by
    intro L hL
    obtain ⟨⟨U₁, U₂, s, hdec⟩, -⟩ := (c2122 L hL).2
    rcases S.inf_le_or_le hL hdec.mem.1 hdec.mem.2 hdec.dynkin hTB with h | h
    · exact h
    · exact absurd h (S.not_le_B hL (c2122 L hL).1 (c2122 L hL).2)
  rcases c21_cases hTH (fun L hL => (c2122 L hL).1) hK with hper | ⟨K', hK', hne, hper, hL3, hL3'⟩
  · rw [hper] at ha
    exact hLB K hK ⟨ha, haB⟩
  · rw [hper] at ha
    have h12 := lemma_1_2_1_two S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 hpc hK hK' hne.symm
    exact S.mem_of_sup hK hK' hL3 hL3' (h12.1.trans h12.2) hTB (hLB K hK) (hLB K' hK') ha haB

end Components

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem conc14623_two_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T M : Subgroup G}
    (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    (c2122 : ∀ K ∈ cComp (mcOf T), Conc14621 T K ∧ Conc14622 T M K) :
    M = yOfL22 T M ⊔ T ∧ T = M ⊓ mcOf T := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  obtain ⟨-, hone⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 fun K hK => (c2122 K hK).1
  have hTB : T ≤ M ⊓ mcOf T := le_inf hTM hTH
  have hPN : T ≤ Subgroup.normalizer (perfectCore (mcOf T) : Set G) :=
    hTH.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (mcOf T)))
  have hBT : M ⊓ mcOf T ≤ T := by
    intro b hb
    have hbH : b ∈ ((perfectCore (mcOf T) ⊔ T : Subgroup G) : Set G) := by
      rw [← hone]
      exact hb.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPN] at hbH
    obtain ⟨a, ha, t, ht, hat⟩ := hbH
    have haB : a ∈ M ⊓ mcOf T := by
      have : a = b * t⁻¹ := by rw [← hat]; group
      rw [this]
      exact (M ⊓ mcOf T).mul_mem hb ((M ⊓ mcOf T).inv_mem (hTB ht))
    have haT : a ∈ T := S.mem_T_of_mem_perfectCore h37 hB c2122 ha haB
    rw [← hat]
    exact T.mul_mem haT ht
  have hEq : T = M ⊓ mcOf T := le_antisymm hTB hBT
  refine ⟨S.hyp1281.eq_sup_of_inf_eq ?_, hEq⟩
  rw [S.normalizer_Z]
  exact hEq.symm

theorem stage14623_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Stage14623 := by
  intro G _ _ T M S hB c19 c20 c2122
  have c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K := fun K hK => (c2122 K hK).1
  exact ⟨conc14623_one_of_a3 h37 h38 S hB c19 c20 c21,
    conc14623_two_of_a3 h37 h38 S hB c19 c20 c2122,
    conc14623_three_cover h37 h38 h39 S hB c19 c20 c21,
    conc14623_three_direct h37 S c21 fun K hK => (c2122 K hK).2⟩

end Assembly

end CFSG.Quasithin
