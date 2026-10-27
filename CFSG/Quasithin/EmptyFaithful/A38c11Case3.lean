module

public import CFSG.Quasithin.EmptyFaithful.A38c11FF
public import CFSG.Quasithin.EmptyFaithful.A38c11Group
public import CFSG.Quasithin.Background.F918D1
public import CFSG.Quasithin.Background.F918D7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

@[expose] def Case3Direct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T), ∀ Kp ∈ cComp (mcOf T), Kp ≠ K →
      mcOf T ≤ Subgroup.normalizer (K : Set G) → mcOf T ≤ Subgroup.normalizer (Kp : Set G) →
      perfectCore (mcOf T) = K ⊔ Kp → KbarIsL3Two K → KbarIsL3Two Kp →
      (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) ⊓ (⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T) ≤
        quasithinOmegaOneCenter T

theorem input14622Case3_of_direct
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h56 : AsB56) (hD310 : D310)
    (hD391 : D391) (hNat : Insp14622Nat) (hR : Case3Direct) : Input14622Case3 := by
  intro G _ _ T M S hB c19 c20 K hK hcase
  obtain ⟨Kp, hKp, hne, hnK, hnKp, hper, hL32, hL32p⟩ := hcase
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hS' : IsSimpleGroup (KBar K) := (c19 _ hHTM).2 K hK
  obtain ⟨-, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  have hc21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K := stage14621_of_a3 h37 h38 h39 G T M S hB c19 c20
  obtain ⟨-, hHT⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 hc21
  have hK₀ : conjClosure K T = K := by
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hnK (hTH ht)) z).mp hz
    · exact le_conjClosure K T
  have hHle : conjClosure K T ⊔ T ≤ mcOf T := conjClosure_sup_le hKH hTH
  have hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (conjClosure K T ⊔ T) K :=
    hypF918_of_setting146 h37 h38 S hK hS'
  have hH' : SQTKGroup ↥(conjClosure K T ⊔ T) :=
    S.sqtkGroup_of_isHTM (S.isHTM_conjClosure_sup h37 h38 hK)
  have hNo := hasNoFaithfulFF_conjClosure_sup_of_normal h56 h37 h38 S c19 c20 hK hnK
  obtain ⟨I, hV₁I, hsup, hnat⟩ := case1_aux hF hH' rfl hK₀ hS' (Or.inl hL32) hsT hsK hdyn hD310 hD391 hNat
    asI161A6_of n4Stmt_of hNo
  have hHeq : mcOf T = Kp ⊔ (conjClosure K T ⊔ T) := by
    refine le_antisymm ?_ (sup_le hKpH hHle)
    rw [hHT, hper, hK₀]
    exact sup_le (sup_le (le_sup_of_le_right (le_sup_of_le_left le_rfl)) le_sup_left)
      (le_sup_of_le_right le_sup_right)
  have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ h ∈ mcOf T, h * z * h⁻¹ = z := by
    intro z hz h hh
    have hcomm : z * h = h * z := Subgroup.mem_centralizer_iff.mp hh z hz
    calc h * z * h⁻¹ = z * h * h⁻¹ := by rw [hcomm]
      _ = z := by group
  have hUab : ∀ a ∈ conjClosure (VZ T M) (mcOf T), ∀ b ∈ conjClosure (VZ T M) (mcOf T), a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm (S.lemma_14_5_15_two hHTM) ha hb
  have hUH : conjClosure (VZ T M) (mcOf T) ≤ mcOf T :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hHTM)).2.toHypF91.conjClosure_Vp_le_pCoreOf.trans
      (pCoreOf_le 2 _)
  have hdirect := hR G T M S hB c19 c20 K hK Kp hKp hne hnK hnKp hper hL32 hL32p
  obtain ⟨hEq, hbot⟩ := A38c11.case3_group hKH hKpH hHle hnK hnKp hHeq hUH
    (le_conjClosure (quasithinOmegaOneCenter T) M) hZc hUab (perfect_of_mem_cComp hKp) hdirect
  refine ⟨⟨I, conjSub s I, s, ⟨⟨hsT, hsK⟩, hdyn, hV₁I, ?_, rfl, hEq.trans hsup, hnat⟩⟩, fun Kp' hKp' hne' => ?_⟩
  · intro v hv
    rw [mem_conjSub]
    exact hV₁I ((Subgroup.mem_normalizer_iff''.mp (hF.H_le_normalizer_V₁ (hF.T_le_H hsT)) v).mp hv)
  · rcases cComp_subset_pair S.hyp.qtke S.hyp.simple S.hyp.nonabelian h37 hpc hK hKp hper Kp' hKp' with h1 | h1
    · exact absurd h1 hne'
    · rw [h1]
      exact hbot

end CFSG.Quasithin
