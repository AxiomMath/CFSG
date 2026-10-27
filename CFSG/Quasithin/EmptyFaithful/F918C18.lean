module

public import CFSG.Quasithin.EmptyFaithful.F918C17
public import CFSG.Quasithin.EmptyFaithful.F918C19
public import CFSG.Quasithin.EmptyFaithful.F918C11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

@[expose] def Input14622Case3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T),
      (∃ Kp ∈ cComp (mcOf T), Kp ≠ K ∧ mcOf T ≤ Subgroup.normalizer (K : Set G) ∧
        mcOf T ≤ Subgroup.normalizer (Kp : Set G) ∧ perfectCore (mcOf T) = K ⊔ Kp ∧
        KbarIsL3Two K ∧ KbarIsL3Two Kp) → Conc14622 T M K

@[expose] def NoFaithfulFFInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T), mcOf T = conjClosure K T ⊔ T →
      (KbarIsL3Two K ∨ KbarIsA6 K) →
      HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 (mcOf T))

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem stage14622_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hD310 : D310) (hD391 : D391)
    (hNat : Insp14622Nat) (hI161 : AsI161A6) (hN4 : N4Stmt)
    (hN3 : Input14622Case3) (hNo : NoFaithfulFFInput) : Stage14622 := by
  have h21 := stage14621_of_a3 h37 h38 h39
  intro G _ _ T M S hB c19 c20 K hK c21
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hS' : IsSimpleGroup (KBar K) := (c19 _ hHTM).2 K hK
  have hodd := (c19 _ hHTM).1
  have c21all : ∀ K ∈ cComp (mcOf T), Conc14621 T K := h21 G T M S hB c19 c20
  obtain ⟨-, hHT⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 c21all
  obtain ⟨hKL, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  have hqtke := S.hyp.qtke
  have hsimp := S.hyp.simple
  have hnab := S.hyp.nonabelian
  have hcperf : perfectCore (mcOf T) ≤ mcOf T := perfectCore_le _
  have hHnorm : mcOf T ≤ Subgroup.normalizer ((perfectCore (mcOf T) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcperf).mp (perfectCore_normal _)
  have hle : ∀ L ∈ cComp (mcOf T), L ≤ perfectCore (mcOf T) := fun L hL =>
    le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
  rcases c21 with ⟨hper, -⟩ | ⟨⟨t, htT, htK, hper⟩, hL32⟩ | hc3
  ·
    have hK₀ : conjClosure K T = K := by
      apply le_antisymm
      · refine conjClosure_le fun t ht z hz => ?_
        have := (Subgroup.mem_normalizer_iff.mp (hHnorm (hTH ht)) z).mp (hper ▸ hz)
        rwa [hper] at this
      · exact le_conjClosure K T
    have hHeq : mcOf T = conjClosure K T ⊔ T := by rw [hK₀, ← hper]; exact hHT
    have hNo' := hNo G T M S hB c19 c20 K hK hHeq hKL
    obtain ⟨I, hI⟩ := isDecompUK_case1 h37 h38 S hK hS' hHeq hK₀ hKL hsT hsK hdyn hD310 hD391 hNat
      hI161 hN4 hNo'
    refine ⟨⟨_, _, _, hI⟩, fun Kp hKp hne => ?_⟩
    exact absurd (eq_of_le_cComp hK hKp (hper ▸ hle Kp hKp)) hne
  ·
    have hKt : conjSub t K ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH htT)
    have hall := cComp_subset_pair hqtke hsimp hnab h37 hpc hK hKt hper
    have hK₀ : conjClosure K T = perfectCore (mcOf T) := by
      apply le_antisymm
      · refine conjClosure_le fun t' ht' z hz => ?_
        exact (Subgroup.mem_normalizer_iff.mp (hHnorm (hTH ht')) z).mp
          (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK) hz)
      · rw [hper]
        refine sup_le (le_conjClosure K T) ?_
        rintro _ ⟨z, hz, rfl⟩
        exact mem_conjClosure htT hz
    have hHeq : mcOf T = conjClosure K T ⊔ T := by rw [hK₀]; exact hHT
    have hKtle : conjSub t K ≤ conjClosure K T := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_conjClosure htT hz
    have hKne : conjClosure K T ≠ K := by
      intro heq
      apply htK
      have h1 : conjSub t K ≤ K := hKtle.trans (le_of_eq heq)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_cComp hK hKt h1)
    have htt : t * t ∈ Subgroup.normalizer (K : Set G) := by
      have hKtt : conjSub (t * t) K ∈ cComp (mcOf T) :=
        map_conj_mem_cComp hK (hTH (T.mul_mem htT htT))
      rcases hall _ hKtt with h1 | h1
      · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
      · exfalso
        apply htK
        have hinv : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have h2 := SetLike.ext_iff.mp h1 (t * y * t⁻¹)
          rw [mem_conjSub, mem_conjSub] at h2
          have e1 : (t * t)⁻¹ * (t * y * t⁻¹) * (t * t) = t⁻¹ * y * t := by group
          have e2 : t⁻¹ * (t * y * t⁻¹) * t = y := by group
          rw [e1, e2] at h2
          simpa using h2.symm
        simpa using (Subgroup.normalizer (K : Set G)).inv_mem hinv
    have hNo' := hNo G T M S hB c19 c20 K hK hHeq (Or.inl hL32)
    have hKtV₁ : ∀ g ∈ conjSub t K, ∀ v ∈ quasithinOmegaOneCenter T, g * v = v * g := by
      intro g hg v hv
      exact ((Subgroup.mem_centralizer_iff.mp (le_of_mem_cComp hKt hg)) v hv).symm
    have hH : SQTKGroup ↥(mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
    have h : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K := by
      rw [hHeq]
      exact hypF918_of_setting146 h37 h38 S hK hS'
    obtain ⟨U₁, hV₁U₁, hsup, hnat, hcomm⟩ := case2_aux h hH hodd hS' hL32 hHeq hKne htT htK htt hKt
      hall hKtV₁ hsT hsK hdyn h37 h38 hD36 hD37 hD321 hI5 tensorTwistL32 hNo'
    refine ⟨⟨U₁, conjSub s U₁, s, ⟨⟨hsT, hsK⟩, hdyn, hV₁U₁, ?_, rfl, hsup, hnat⟩⟩, fun Kp hKp hne => ?_⟩
    · intro v hv
      rw [mem_conjSub]
      exact hV₁U₁ ((Subgroup.mem_normalizer_iff''.mp (h.H_le_normalizer_V₁ (hTH hsT)) v).mp hv)
    · rcases hall Kp hKp with h1 | h1
      · exact absurd h1 hne
      · rw [h1]
        exact hcomm
  ·
    exact hN3 G T M S hB c19 c20 K hK hc3

end Final

end CFSG.Quasithin
