module

public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Quasithin.Background.C1Basic

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open
open scoped commutatorElement

universe u

section Gamma

variable {G : Type u} [Group G]

@[expose] def gammaE64 (V M : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ V ∧ U ≠ ⊥ ∧ ¬ Subgroup.centralizer (U : Set G) ≤ M ∧
    twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G)}

end Gamma

section Lemma65

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

theorem le_of_isSylowIn_of_le {Q P K : Subgroup G} (hQ : IsSylowIn 2 Q K) (hQP : Q ≤ P)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) : P ≤ Q := by
  have h1 : Q.relIndex P ∣ Q.relIndex K :=
    ⟨P.relIndex K, (Subgroup.relIndex_mul_relIndex Q P K hQP hPK).symm⟩
  have h2 : Q.relIndex P = 2 ^ E3.mQuot P Q := E3.relIndex_eq_two_pow hP Q
  by_contra hne
  have h3 : Q.relIndex P ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have h4 : 2 ∣ Q.relIndex P := by
    rw [h2]
    refine dvd_pow_self 2 fun h0 => h3 ?_
    rw [h2, h0, pow_zero]
  exact hQ.not_dvd_relIndex (h4.trans h1)

omit [Finite G] in
theorem normalizer_le_normalizer_of_char {Q C : Subgroup G} (hCQ : C ≤ Q)
    (hchar : (C.subgroupOf Q).Characteristic) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := Q)
    (C.subgroupOf Q)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at this

theorem e6_5_sylow_M (h : E6.HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    IsSylowIn 2 (T ⊓ Subgroup.centralizer (V : Set G)) (M ⊓ Subgroup.centralizer (U : Set G)) := by
  obtain ⟨hUV, -, -, hres⟩ := hU
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hQD : Q ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (inf_le_left.trans h.inM.2) (inf_le_right.trans (Subgroup.centralizer_le hUV))
  obtain ⟨P, hP, hQP⟩ := exists_isSylowIn_ge 2 hQD h.isPGroup_Q
  have hPres : P ≤ twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [← conjClosure_eq_twoPrimeResidual hP]
    exact le_conjClosure P _
  have hPQ : P ≤ Q :=
    le_of_isSylowIn_of_le h.isSylowIn_centralizer hQP (hPres.trans hres) hP.isPGroup
  have hPeq : P = Q := le_antisymm hPQ hQP
  rw [← hPeq]
  exact hP

theorem e6_5_one (h : E6.HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    IsSylowIn 2 (T ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.centralizer (U : Set G)) := by
  have hSyl := e6_5_sylow_M h hU
  obtain ⟨hUV, -, -, -⟩ := hU
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  set H := Subgroup.centralizer (U : Set G) with hH
  have hQH : Q ≤ H := inf_le_right.trans (Subgroup.centralizer_le hUV)
  obtain ⟨P', hP', hQP'⟩ := exists_isSylowIn_ge 2 hQH h.isPGroup_Q
  have hP'2 : IsPGroup 2 P' := hP'.isPGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP'Q : P' ≤ Q := by
    by_contra hne
    have hnil : Group.IsNilpotent ↥P' := hP'2.isNilpotent
    have hNC : NormalizerCondition ↥P' := Group.normalizerCondition_of_isNilpotent
    have hlt : Q.subgroupOf P' < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hne ?_
      intro x hx
      have := (Subgroup.subgroupOf_eq_top.1 htop)
      exact this hx
    have hlt2 := hNC _ hlt
    obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt hlt2
    have hxN' : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨g, hQP' hg⟩).1 hg
        exact h1
      · intro hg
        have hgP : g ∈ P' := by
          have h2 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ P' :=
            P'.mul_mem (P'.mul_mem (P'.inv_mem x.2) (hQP' hg)) x.2
          simpa [mul_assoc] using h2
        have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨g, hgP⟩).2
        exact h1 hg
    set P'' : Subgroup G := P' ⊓ Subgroup.normalizer (Q : Set G) with hP''
    have hQP'' : Q ≤ P'' := le_inf hQP' Subgroup.le_normalizer
    have hP''H : P'' ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
      le_inf (inf_le_right.trans h.normalizer_Q_le) (inf_le_left.trans hP'.le)
    have hP''2 : IsPGroup 2 P'' := hP'2.to_le inf_le_left
    have hP''Q : P'' ≤ Q := le_of_isSylowIn_of_le hSyl hQP'' hP''H hP''2
    apply hxQ
    exact hP''Q ⟨x.2, hxN'⟩
  have hPeq : P' = Q := le_antisymm hP'Q hQP'
  rw [← hPeq]
  exact hP'

theorem e6_5_two (h : E6.HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    cgsIn (Subgroup.centralizer (U : Set G)) (T ⊓ Subgroup.centralizer (V : Set G)) ≤
        Subgroup.centralizer (U : Set G) ⊓ M ∧
      Subgroup.centralizer (U : Set G) ⊓ M < Subgroup.centralizer (U : Set G) := by
  obtain ⟨-, -, hHM, -⟩ := hU
  refine ⟨?_, lt_of_le_of_ne inf_le_left fun heq => hHM ?_⟩
  · refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hchar => ?_
    refine inf_le_inf_left _ ?_
    have hNQC := normalizer_le_normalizer_of_char hCQ hchar
    have hUM := h.isUniqueM_of_le hC1 (h.isPGroup_Q.to_le hCQ) (inf_le_left.trans hNQC)
    exact hUM.1.2
  · rw [← heq]
    exact inf_le_right

theorem e6_5_three (h : E6.HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    V ≤ Subgroup.centralizer (U : Set G) ⊓ M ∧
      Subgroup.centralizer (U : Set G) ⊓ M ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hUV, hU1, -, -⟩ := hU
  refine ⟨le_inf (fun v hv => Subgroup.mem_centralizer_iff.2 fun u hu =>
    B2F.isElemAbelian_comm h.isElemAbelian (hUV hu) hv) (h.le.trans h.inM.2), ?_⟩
  intro g hg
  by_contra hgN
  have hTI := h.tiSet.2 g hg.2 hgN
  apply hU1
  rw [eq_bot_iff, ← hTI]
  intro u hu
  refine ⟨hUV hu, ?_⟩
  show u ∈ conjSubgroup V g
  rw [mem_conjSubgroup_iff]
  have hc : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hg.1 u hu).symm
  have e : g * u * g⁻¹ = u := by rw [hc]; group
  rw [e]
  exact hUV hu

theorem e6_5_cpu (h : E6.HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    SatisfiesCPU (Subgroup.centralizer (U : Set G)) (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer (U : Set G) ⊓ M) := by
  have h1 := e6_5_one h hU
  obtain ⟨h2, h3⟩ := e6_5_two h hU
  refine ⟨h2, h3, isTwoRadicalIn_of_sylow h1.le h1.isPGroup h1.not_dvd_relIndex h.Q_ne_bot, ?_⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  set H := Subgroup.centralizer (U : Set G) with hH
  have hC : conjClosure Q (H ⊓ M) ≤ H := conjClosure_le fun g hg z hz =>
    H.mul_mem (H.mul_mem (Subgroup.mem_inf.1 hg).1 (h1.le hz)) (H.inv_mem (Subgroup.mem_inf.1 hg).1)
  intro hdvd
  apply h1.not_dvd_relIndex
  refine hdvd.trans ?_
  rw [← Subgroup.relIndex_mul_relIndex Q (conjClosure Q (H ⊓ M)) H (le_conjClosure Q _) hC]
  exact Dvd.intro _ rfl

end Lemma65

end E6

end CFSG.Quasithin
