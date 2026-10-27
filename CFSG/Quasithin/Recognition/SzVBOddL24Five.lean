module

public import CFSG.Quasithin.Recognition.SzVBOddL24Master
public import CFSG.Quasithin.Recognition.SzVBOddL24Word

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem critDist_ne_five (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) :
    critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) ≠ 5 := by
  intro h5
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hV := F112J2.V_ne_bot h
  have hR := F112J2.hyp111R_of_setting hRO h
  have hinf : (L2 ⊔ S) ⊓ (K1 ⊔ S) = S := F112J2.inf_L2S_K1S hR h.s3
  have hb : 3 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) := by omega
  have hodd : Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) := by
    rw [h5]
    exact ⟨2, rfl⟩
  obtain ⟨g, hd2, -, hNT, hquad, ⟨y, hyN, hy2, hyQ⟩, -⟩ := exists_nData hyp hV hinf hb hodd
  obtain ⟨z, hK⟩ := kleinData_of_setting hRO h
  have hF := l24Facts_of_setting hRO h hL
  have hdist : dist (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S))
      (g⁻¹ • γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) = 3 := by
    rw [h5] at hd2
    have h1 := dist_smul g⁻¹ (γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S))
      (g • γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S))
    rw [inv_smul_smul] at h1
    rw [CosetGeom.dist_comm, h1]
    omega
  obtain ⟨x, l₁, l₂, k, hl₁, hl₂, hk, hx, hxδ⟩ := exists_word_five hRO h hdist
  have hpP : ((x⁻¹ * g⁻¹ : ↥(K1 ⊔ L2 ⊔ S)) : G) ∈ K1 ⊔ S := by
    have h1 : (x⁻¹ * g⁻¹) • γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) =
        γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) := by
      rw [mul_smul, ← hxδ, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hyp.le₂] at this
  have hP : K1 ⊔ S ≤ Subgroup.normalizer (conjClosure (conjClosure Zs L2) (K1 ⊔ S) : Set G) :=
    le_normalizer_conjClosure _ _
  have hgx : (g : G)⁻¹ = x * ((x⁻¹ * g⁻¹ : ↥(K1 ⊔ L2 ⊔ S)) : G) := by
    simp
  have hNx : conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) =
      conjSub (x : G) (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    rw [hgx, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hP hpP)]
  obtain ⟨t, htP, htV, hτ1, hτ3, hmem⟩ := exists_master hRO h hL hk hl₁ hl₂
  have htN : conjSub t (conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S))) =
      conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    rw [hNx, ← conjSub_mul]
    have e : t * (x : G) = x * ((x : G)⁻¹ * t * x) := by group
    rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hP (by rw [hx]; exact hmem))]
  have hWab : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    have := isElemAbelian_Vv_γ₁ hyp hV (by omega : 2 < critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S)
      (K1 ⊔ S) (conjClosure Zs L2))
    rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at this
  have hyP : y ∈ K1 ⊔ S := hF.S_le (hNT hyN)
  have hy : (⟨y, hyP⟩ : ↥(K1 ⊔ S)) ∉ kerAct (K1 ⊔ S) (conjClosure Zs L2) := fun hk =>
    hyQ (hF.ker_inv_le ⟨y, hyP⟩ (Subtype.ext hy2) hk)
  exact core_false hK hWab hF.S_le hF.S_pGroup hF.S_le_normalizer hF.S_transitive
    hF.card_five hNT hquad hyN hy2 hyP hy htP htN htV hτ1 hτ3

end CFSG.Quasithin.SzVB
