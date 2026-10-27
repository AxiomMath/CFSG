module

public import CFSG.Quasithin.Recognition.SzVBOddL24Facts
public import CFSG.Quasithin.Recognition.SzVBOddL24Core
public import CFSG.Quasithin.Recognition.SzVBOddL24Crit
public import CFSG.Quasithin.Recognition.SzVBOddL24Loc
public import CFSG.Quasithin.Recognition.SzVBOddL24Twin

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem kleinData_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    ∃ z : G, KleinData (K1 ⊔ S) (conjClosure Zs L2) z := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hZ : Zs ≠ ⊥ := by
    intro hZ
    have := h.card_Z
    rw [hZ, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hPc : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
    sup_le h.K1_cent_Z (F112J2.S_le_centralizer_Z h)
  exact ⟨z,
    { V_le := h.V_le.trans (pCoreOf_le 2 _)
      elemAbelian := hyp.elemAbelian
      card_eq := h.V_card
      z_mem := le_conjClosure Zs L2 hz
      z_ne_one := hz1'
      z_cent := fun x hx => ((Subgroup.mem_centralizer_iff.mp (hPc hx)) z hz).symm }⟩

omit [Finite G] in
theorem conj_eq_one_iff {H : Type*} [Group H] (σ τ : H) : σ⁻¹ * τ * σ = 1 ↔ τ = 1 := by
  constructor
  · intro h
    calc τ = σ * (σ⁻¹ * τ * σ) * σ⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    rw [h]
    group

omit [Finite G] in
theorem conj_pow_three_eq_one {H : Type*} [Group H] (σ τ : H) (h : τ ^ 3 = 1) :
    (σ⁻¹ * τ * σ) ^ 3 = 1 := by
  have h1 := conj_pow (a := σ⁻¹) (b := τ) (i := 3)
  rw [inv_inv] at h1
  rw [h1, h, mul_one, inv_mul_cancel]

theorem critDist_ne_three (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) :
    critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) ≠ 3 := by
  intro h3
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hV := F112J2.V_ne_bot h
  have hR := F112J2.hyp111R_of_setting hRO h
  have hinf : (L2 ⊔ S) ⊓ (K1 ⊔ S) = S := F112J2.inf_L2S_K1S hR h.s3
  have hb : 3 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) := h3.ge
  have hodd : Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) := by
    rw [h3]
    exact ⟨1, rfl⟩
  obtain ⟨g, hd2, -, hNT, hquad, ⟨y, hyN, hy2, hyQ⟩, -⟩ := exists_nData hyp hV hinf hb hodd
  obtain ⟨z, hK⟩ := kleinData_of_setting hRO h
  have hF := l24Facts_of_setting hRO h hL
  have hdist : dist (γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S))
      (g • γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) = 1 := by
    rw [h3] at hd2
    omega
  have hadj := dist_eq_one_iff_adj.mp hdist
  obtain ⟨k, hk1, hk2⟩ := exists_stab_smul_eq (adj_γ₀_γ₁ (G₀ := K1 ⊔ L2 ⊔ S) (G₁ := L2 ⊔ S)
    (G₂ := K1 ⊔ S)).symm hadj
  have hkP : (k : G) ∈ K1 ⊔ S := by
    have := mem_stab_of_smul_eq hk1
    rwa [stab_γ₁ hyp.le₂] at this
  have hl₁ : ((k⁻¹ * g : ↥(K1 ⊔ L2 ⊔ S)) : G) ∈ L2 ⊔ S := by
    have h1 : (k⁻¹ * g) • γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) =
        γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) := by
      rw [mul_smul, ← hk2, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₀ hyp.le₁] at this
  obtain ⟨l, hl, s, hs, hls⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h2.normalizes).mp hl₁
  have hg : (g : G) = k * l * s := by
    have e : ((k⁻¹ * g : ↥(K1 ⊔ L2 ⊔ S)) : G) = (k : G)⁻¹ * g := rfl
    rw [e] at hls
    calc (g : G) = k * ((k : G)⁻¹ * g) := by group
      _ = k * (l * s) := by rw [hls]
      _ = k * l * s := by group
  obtain ⟨t', htB, htodd, hτ1, hτ3⟩ := exists_order_three hRO h hL
  have ht₀K1 : (t' : G) ∈ K1 := F1.borelOf_le K1 S htB
  have ht₀V : ∀ a ∈ conjClosure Zs L2, (t' : G) * a = a * (t' : G) := fun a ha =>
    commute_klein_of_odd_order hK.elemAbelian hK.card_eq hK.z_mem hK.z_ne_one
      (hK.z_cent _ t'.2)
      (F7.conjSub_eq_of_mem_normalizer (borelOf_le_normalizer_conjClosure h htB)) htodd ha
  have hP : K1 ⊔ S ≤ Subgroup.normalizer (conjClosure (conjClosure Zs L2) (K1 ⊔ S) : Set G) :=
    le_normalizer_conjClosure _ _
  have hLV : L2 ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    le_sup_left.trans hyp.normalizes
  have hLT : L2 ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) ≤ S :=
    (inf_le_inf_right _ le_sup_left).trans (inf_centralizer_le_T hyp
      (F112J2.isNaturalS3_of_setting hRO h) (F112J2.relIndex_L2S hR h.s3))
  have hkey := conjSub_eq_of_twin hl (h.hyp.h2.borel_le htB) hLV ht₀V hLT
    (le_sup_right.trans hP) (hP t'.2)
  have hkW : conjSub (k : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) =
      conjClosure (conjClosure Zs L2) (K1 ⊔ S) :=
    F7.conjSub_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hP hkP))
  have hN : conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) =
      conjSub s⁻¹ (conjSub l⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S))) := by
    rw [hg, mul_inv_rev, mul_inv_rev, conjSub_mul, conjSub_mul, hkW]
  have ht₁N : conjSub (s⁻¹ * (t' : G) * s)
      (conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S))) =
      conjSub (g : G)⁻¹ (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    rw [hN, ← conjSub_mul, show s⁻¹ * (t' : G) * s * s⁻¹ = s⁻¹ * (t' : G) by group,
      conjSub_mul s⁻¹ (t' : G), hkey]
  have hsP : s ∈ K1 ⊔ S := hF.S_le hs
  have hWab : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    have := isElemAbelian_Vv_γ₁ hyp hV (by omega : 2 < critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S)
      (K1 ⊔ S) (conjClosure Zs L2))
    rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at this
  have hyP : y ∈ K1 ⊔ S := hF.S_le (hNT hyN)
  have hy : (⟨y, hyP⟩ : ↥(K1 ⊔ S)) ∉ kerAct (K1 ⊔ S) (conjClosure Zs L2) := fun hk =>
    hyQ (hF.ker_inv_le ⟨y, hyP⟩ (Subtype.ext hy2) hk)
  have ht₁P : s⁻¹ * (t' : G) * s ∈ K1 ⊔ S :=
    (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem ((K1 ⊔ S).inv_mem hsP) t'.2) hsP
  have ht₁V : s⁻¹ * (t' : G) * s ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).inv_mem (hF.S_le_normalizer hs))
      (borelOf_le_normalizer_conjClosure h htB)) (hF.S_le_normalizer hs)
  have hconj : (⟨s⁻¹ * (t' : G) * s, ht₁P⟩ : ↥(K1 ⊔ S)) =
      (⟨s, hsP⟩ : ↥(K1 ⊔ S))⁻¹ * t' * ⟨s, hsP⟩ := rfl
  set ρ := MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) with hρ
  refine core_false hK hWab hF.S_le hF.S_pGroup hF.S_le_normalizer hF.S_transitive
    hF.card_five hNT hquad hyN hy2 hyP hy ht₁P ht₁N ht₁V ?_ ?_
  · rw [hconj, map_mul, map_mul, map_inv]
    exact fun h1 => hτ1 ((conj_eq_one_iff _ _).mp h1)
  · rw [hconj, map_mul, map_mul, map_inv]
    exact conj_pow_three_eq_one _ _ hτ3

end CFSG.Quasithin.SzVB
