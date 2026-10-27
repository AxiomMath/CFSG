module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeQ1
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeLinear
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeNum
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNatZ2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeCartan

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_notLe_false
    {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) : False := by
  classical
  obtain ⟨m, hm⟩ := h2
  obtain ⟨k, hk, F, hFld, hFin, hFc, hU3'⟩ := hU3
  letI : Field F := hFld
  letI : Finite F := hFin
  have hQ1 : Q1 L1 L2 S = Z1 L1 L2 S :=
    str86_caseIIa_notLe_q1_eq_z1 hF hSB hk hFc hU3' hB2 hm hIIa hZ
  obtain ⟨g, hg, -, hW⟩ :=
    str86_caseIIa_notLe_linear hF hSB ⟨k, hk, F, hFld, hFin, hFc, hU3'⟩ hB2 hm hZ
  obtain ⟨-, hZX, hXY, hX'Y, hc1, hcent⟩ :=
    str86_caseIIa_notLe_numerics hF hSB hk hFc hU3' hB2 hm hII hZ hQ1 hg hW
  set Z := Z1 L1 L2 S with hZdef
  set X := Z ⊓ Q2 L1 L2 S with hXdef
  set X' := conjSubgroup Z g ⊓ Q2 L1 L2 S with hX'def
  set Y := Z ⊓ conjSubgroup Z g ⊓ Q2 L1 L2 S with hYdef
  have hYX : Y ≤ X := inf_le_inf_right _ inf_le_left
  have hXZ : X ≤ Z := inf_le_left
  have hYX' : Y ≤ X' := inf_le_inf_right _ inf_le_right
  have hk1 : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨t, htX', htY⟩ : ∃ t ∈ X', t ∉ Y := by
    by_contra hcon
    push Not at hcon
    have h1 : Y.relIndex X' = 1 := Subgroup.relIndex_eq_one.mpr hcon
    omega
  have htQ2 : t ∈ Q2 L1 L2 S := (Subgroup.mem_inf.mp htX').2
  have htZ : t ∉ Z := fun h =>
    htY (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h, (Subgroup.mem_inf.mp htX').1⟩, htQ2⟩)
  have htQ1 : t ∉ Q1 L1 L2 S := by rwa [hQ1]
  have ht2 : t * t = 1 := by
    have hgt : g * t * g⁻¹ ∈ Z :=
      (CFSG.Quasithin.mem_conjSubgroup_iff).mp (Subgroup.mem_inf.mp htX').1
    have hsq : (g * t * g⁻¹) ^ 2 = 1 :=
      (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 _ hgt
    have hsq' : g * (t * t) * g⁻¹ = 1 := by
      rw [← hsq, pow_two]
      group
    have h1 : t * t = g⁻¹ * (g * (t * t) * g⁻¹) * g := by group
    rw [h1, hsq']
    group
  have hYt : Z ⊓ Subgroup.centralizer ({t} : Set G) = Y := hcent t htX' htY
  have hidx : (Subgroup.centralizer ({t} : Set G)).relIndex Z ≤ (2 ^ k) ^ 2 := by
    rw [← Subgroup.inf_relIndex_left, hYt, ← Subgroup.relIndex_mul_relIndex Y X Z hYX hXZ,
      hXY, hZX]
    exact le_of_eq (by ring)
  obtain ⟨N, hN, hNZ, -, hNP1, hSC, hnat⟩ :=
    str86_natural_in_Z1_of_chief_one hF hSB hk hFc hU3' hII hIIa hc1 htQ2 htQ1 ht2 hidx
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  refine str86_caseIIa_notLe_cartan_false hF hSB hk hFc hU3' hN hNZ hNP1 hSC hnat
    (hQ2S htQ2) htQ1 ht2 ?_ ?_ hZX
  · rw [hYt]
    exact inf_le_right
  · rw [hYt]
    exact hXY

end CFSG.Quasithin.Stroth

end
