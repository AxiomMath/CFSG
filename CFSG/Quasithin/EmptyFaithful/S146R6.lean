module

public import CFSG.Quasithin.EmptyFaithful.S146R1
public import CFSG.Quasithin.EmptyFaithful.S146R5
public import CFSG.Quasithin.EmptyFaithful.S146B1
public import CFSG.Quasithin.EmptyFaithful.S146B3
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem stage146BranchACore_of_parts_three (h4 : Stage1461Four) (h1461five : Stage1461Five)
    (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617) (hH2 : Stage14611H2) :
    Stage146BranchACore := by
  intro G _ _ T M S hex
  obtain ⟨H, PQ, p, hred, hmax⟩ := exists_redCE h4 S hex
  have hp3 : p = 3 := h15 G T M S H PQ p hred hmax
  obtain ⟨-, ⟨H₀, H₁, H₂, t, hdec⟩, hZ⟩ := h12 G T M S H PQ p hred
  obtain ⟨hOF, h17'⟩ := h17 G T M S H PQ p hred hmax
  obtain ⟨-, h3, h4', h5⟩ := h17' H₀ H₁ H₂ t hdec
  have hZ' := hZ H₀ H₁ H₂ t hdec
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.conjClosure_Vp_le_pCoreOf
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hUH₁ : conjClosure (VZ T M) H ≤ H₁ := hUQ.trans hdec.Q₁
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    (le_conjClosure _ _ : quasithinOmegaOneCenter T ≤ VZ T M).trans (le_conjClosure _ _)
  have huHi_le : uHi T M H H₁ ≤ conjClosure (VZ T M) H :=
    sup_le (S145.commutator_le_of_le_normalizer (hH₁H.trans hHU)) hZU
  set T₀ : Subgroup G := T ⊓ Subgroup.normalizer (H₁ : Set G) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le inf_le_left
  have hT₀N₁ : T₀ ≤ Subgroup.normalizer (H₁ : Set G) := inf_le_right
  have hT₀NU : T₀ ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    (inf_le_left.trans hTH).trans hHU
  have hT₀NZ : T₀ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hx.1)
  have hT₀Nuhi : T₀ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) :=
    (le_inf (S145.le_normalizer_commutator hT₀NU hT₀N₁) hT₀NZ).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have huhiT₀ : uHi T M H H₁ ≤ T₀ :=
    le_inf ((huHi_le.trans hUQ).trans hQT) ((huHi_le.trans hUH₁).trans Subgroup.le_normalizer)
  have hlt : quasithinOmegaOneCenter T < uHi T M H H₁ := by
    refine lt_of_le_of_ne le_sup_right fun heq => ?_
    have hr := hdec.rank₁.2 hp3
    have h0 : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 0 := by
      rw [← heq]
      simp [mIdx]
    omega
  obtain ⟨u, hu1, huZ, hu⟩ := exists_fixed_mod hT₀2 huhiT₀ hlt hT₀Nuhi hT₀NZ
  have huU : u ∈ conjClosure (VZ T M) H := huHi_le hu1
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH huU
  have huT₀ : T₀ ≤ tZero T u := fun x hx =>
    (S146T.mem_tZero_iff huG).mpr ⟨hx.1, hu x hx⟩
  have huK : u ∈ uK T M H :=
    ((sup_le (Subgroup.commutator_mono le_rfl hH₁H)
      (hZ'.1.trans (Subgroup.commutator_mono le_rfl ((oTwoUpper_le H₁).trans hH₁H))) :
        uHi T M H H₁ ≤ uK T M H)) hu1
  have hInv := h3 u huK (Or.inl hu1) huZ huT₀
  have hI := h4' u huK (Or.inl hu1) huZ huT₀
  have hr4 : 4 < (pCoreOf 2 H).relIndex T := S.four_lt_relIndex_of_isOFourPlusOn hH hOF
  have hr5 : 4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) :=
    S.four_le_mIdx_of_isOFourPlusOn h1461five hred hp3 hOF hdec
  obtain ⟨hH₂C, hH₂S3, hH₂M⟩ := hH2 G T M S H PQ p hred hmax hp3 H₀ H₁ H₂ t hdec u hu1 huZ huT₀
  have hE5 : tZero T u ≤ T₀ := by
    intro s hs
    have hsT : s ∈ T := S146T.tZero_le T u hs
    refine ⟨hsT, ?_⟩
    by_contra hsN
    have hs0 : s ∉ H₀ := fun h0 => hsN (hdec.H₀_le_normalizer_H₁ h0)
    have hsconj : conjSub s H₁ = H₂ := hdec.conjSub_eq_of_not_mem (hTH hdec.t_mem) (hTH hsT) hs0
    have hsZ : s ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hsT)
    have hconjU : conjSub s (uHi T M H H₁) = uHi T M H H₂ := by
      unfold uHi
      have e1 : conjSub s ⁅conjClosure (VZ T M) H, H₁⁆ =
          ⁅conjSub s (conjClosure (VZ T M) H), conjSub s H₁⁆ := (conjSub_commutator s _ _).symm
      have e2 : conjSub s (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
        conjSub_eq_of_mem_normalizer (hHU (hTH hsT))
      have e3 : conjSub s (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
        conjSub_eq_of_mem_normalizer hsZ
      rw [show conjSub s (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T) =
          conjSub s ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ conjSub s (quasithinOmegaOneCenter T) from
          Subgroup.map_sup _ _ _, e1, e2, e3, hsconj]
    have h1 : s * u * s⁻¹ ∈ uHi T M H H₂ := by
      have hmem : s * u * s⁻¹ ∈ conjSub s (uHi T M H H₁) :=
        mem_conjSub.mpr (by simpa [mul_assoc] using hu1)
      rwa [hconjU] at hmem
    have hcomm : ⁅s, u⁆ ∈ quasithinOmegaOneCenter T := ((S146T.mem_tZero_iff huG).mp hs).2
    have h2 : s * u * s⁻¹ ∈ uHi T M H H₁ := by
      have e : s * u * s⁻¹ = ⁅s, u⁆ * u := by simp only [commutatorElement_def]; group
      rw [e]
      exact (uHi T M H H₁).mul_mem (Subgroup.mem_sup_right hcomm) hu1
    have h3 : s * u * s⁻¹ ∈ quasithinOmegaOneCenter T := by
      rw [← hdec.dir_inf]
      exact ⟨h2, h1⟩
    apply huZ
    have hz : s⁻¹ * (s * u * s⁻¹) = (s * u * s⁻¹) * s⁻¹ := S146T.comm_Z_T (T.inv_mem hsT) h3
    have e : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [e, hz]
    simpa using h3
  refine ⟨H, u, H₂ ⊔ T₀, hH, hInv, hI, hr4, hr5, ?_, hH₂C, hH₂S3, hH₂M, ?_⟩
  · exact hE5.trans le_sup_right
  · have hT₀H₂ : T₀ ≤ Subgroup.normalizer (H₂ : Set G) :=
      (hdec.inf_normalizer_le hTH).trans hdec.H₀_le_normalizer_H₂
    rw [oTwoUpper_sup_eq_oTwoUpper hT₀2 hT₀H₂]
    exact h5

theorem stage146BranchACore_of_parts_four (h2 : Stage1461Two) (h3 : Stage1461Three)
    (h5 : Stage1461Five) (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617) :
    Stage146BranchACore :=
  stage146BranchACore_of_parts_three (stage1461Four_of h2 h3) h5 h12 h15 h17 (stage14611H2_of h2)

theorem stageSection146_of_inputs_six (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617)
    (h20 : Stage14620) (h21 : Stage14621) (h22 : Stage14622)
    (h23 : Stage14623) (hD4 : Stage146D4) (h24 : Stage14624)
    (hF1 : Stage146FRank) (hF2 : Stage146FH2) (hF3 : Stage146FFour)
    (h9 : Stage1469) (h105 : Stage14610Five) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs h11 h113 hedge (stage146BranchACore_of_parts_four h2 h3 h5 h12 h15 h17)
      (stage146BranchBCore_of_parts stage14619_proof h20 h21 h22 h23 hD4 h24 hF1 hF2 hF3) h9 h105
      stage1463_one_proof (stage1463_two_of (stage1461Six_of h2 h3 h5))
      (stage1463_three_proof h1413) h634

end CFSG.Quasithin
