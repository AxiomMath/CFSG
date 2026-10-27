module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModK

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem r1_sub : ∀ r ∈ r1, r ∈ gm6 ∧ presv p1c r = true := by
  intro r hr
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hr
  have hall := cert_gmList_complete
  obtain ⟨⟨h0, h1, h2⟩, hin, hp⟩ := r1m_inGm A hA
  exact ⟨List.mem_map.2 ⟨A, hall _ (List.mem_range.2 h0) _ (List.mem_range.2 h1) _
    (List.mem_range.2 h2) hin, rfl⟩, hp⟩

theorem r2_sub : ∀ r ∈ r2, r ∈ gm6 ∧ presv l2c r = true := by
  intro r hr
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hr
  have hall := cert_gmList_complete
  obtain ⟨⟨h0, h1, h2⟩, hin, hp⟩ := r2m_inGm A hA
  exact ⟨List.mem_map.2 ⟨A, hall _ (List.mem_range.2 h0) _ (List.mem_range.2 h1) _
    (List.mem_range.2 h2) hin, rfl⟩, hp⟩

theorem XOf_le_normalizer_subG
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {l : List ℕ} {h0 : 0 ∈ l} {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l}
    (hz : ∀ z ∈ zs6, ∀ c ∈ l, z.app c ∈ l) :
    XOf L ≤ Subgroup.normalizer (C.subG l h0 hx : Set G) := by
  apply le_normalizer_of_maps
  intro x hxX w hw
  obtain ⟨hwV, hwl⟩ := hw
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := L_le_normalizer h (XOf_le L hxX)
  have hm := (Subgroup.mem_normalizer_iff.1 hxN w).1 hwV
  have e : C.cd ⟨x * w * x⁻¹, hm⟩ = (C.cB (conjAct V ⟨x, hxN⟩)).app (C.cd ⟨w, hwV⟩) :=
    cd_conj C hxN ⟨w, hwV⟩
  exact ⟨hm, by rw [e]; exact hz _ (cB_mem_zs6_of_mem_XOf h1222 h hC hxX hxN) _ hwl⟩

omit [Finite G] in
theorem sq_mem_centralizer {C : Coding ↥V} {r : G} (hr : r ∈ Subgroup.normalizer (V : Set G))
    (hsq : (C.cB (conjAct V ⟨r, hr⟩)).comp (C.cB (conjAct V ⟨r, hr⟩)) = B6.id) :
    r ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  have hr2 : r ^ 2 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hr 2
  rw [← conjAct_eq_one' hr2]
  have e : conjAct V ⟨r ^ 2, hr2⟩ = conjAct V ⟨r, hr⟩ * conjAct V ⟨r, hr⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (pow_two r)
  rw [e]
  apply C.cB_injective
  rw [C.cB_mul, C.cB_one, hsq]

theorem lemma12_7_2_two
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    IsFPoint L V (V1 T L V) ∧
      (L ⊔ T) ⊓ Subgroup.normalizer (V1 T L V : Set G) = P1 T L V ⊔ T ∧
      Nat.card ↥(autOn (R1 T L V) V) = 4 ∧
      (∀ r ∈ R1 T L V, r ^ 2 ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ r ∈ R1 T L V, r ∉ Subgroup.centralizer (V : Set G) →
        ⁅V, Subgroup.zpowers r⁆ = V1 T L V) ∧
      V ⊓ Subgroup.centralizer (R1 T L V : Set G) = V1 T L V := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV1 := V1_eq h hC
  have hR : ∀ a, a ∈ autOn (R1 T L V) V ↔ C.cB a ∈ r1 := by
    rw [R1, P1, hV1]
    exact mem_autOn_R h1222 h hC.1 p1c_lt id_mem_r1 r1_closed r1_sub r1_sq cert_n1 cert_m1
  have hRN : R1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (pof_le_normalizer h1222 h _)
  have hRsurj : ∀ B ∈ r1, ∃ x, ∃ hx : x ∈ Subgroup.normalizer (V : Set G), x ∈ R1 T L V ∧
      C.cB (conjAct V ⟨x, hx⟩) = B := by
    intro B hB
    obtain ⟨a, rfl⟩ := hC.1.2 B (r1_sub B hB).1
    obtain ⟨x, hx, hxR, rfl⟩ := mem_autOn'.1 ((hR a).2 hB)
    exact ⟨x, hx, hxR, rfl⟩
  have hcode : ∀ x (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ R1 T L V →
      C.cB (conjAct V ⟨x, hx⟩) ∈ r1 := fun x hx hxR => (hR _).1 (conjAct_mem_autOn hxR hx)
  refine ⟨⟨⟨inf_le_left, ?_⟩, ?_⟩, sup_inf_normalizer h (T_le_normalizer_V1 h1222 h), ?_, ?_, ?_,
    ?_⟩
  · rw [hV1]
    exact XOf_le_normalizer_subG h1222 h hC.1 zs6_presv_p1c
  · rw [hV1, C.card_subG p1c_nodup p1c_lt]
    rfl
  · have e : autOn (R1 T L V) V = C.subOf r1 id_mem_r1 r1_closed := by
      ext a
      rw [hR, C.mem_subOf]
    rw [e, C.card_subOf r1_nodup (fun B hB => hC.1.2 B (r1_sub B hB).1)]
    rfl
  · intro r hr
    exact sq_mem_centralizer (hRN hr) (r1_sq _ (hcode r (hRN hr) hr))
  · intro r hr hrC
    have hrN := hRN hr
    have hB := hcode r hrN hr
    have hne : C.cB (conjAct V ⟨r, hrN⟩) ≠ B6.id := fun he =>
      hrC ((conjAct_eq_one' hrN).1 (C.cB_eq_one.1 he))
    rw [hV1]
    apply le_antisymm
    · apply commutator_le_subG C ((Subgroup.zpowers_le).2 hrN)
      intro x hx hxr c hc
      exact r1_comm _ (hcode x hx ((Subgroup.zpowers_le).2 hr hxr)) c hc
    · intro g hg
      obtain ⟨hgV, hgl⟩ := hg
      obtain ⟨c, hc, hcB⟩ := r1_comm_surj _ hB hne _ hgl
      have hmem := Subgroup.commutator_mem_commutator (C.dc c).2 (Subgroup.mem_zpowers r)
      rw [commutator_eq_coe hrN] at hmem
      have e : (C.dc c * (conjAct V ⟨r, hrN⟩ (C.dc c))⁻¹ : ↥V) = ⟨g, hgV⟩ := by
        apply C.cd_injective
        rw [cd_commutator, C.cd_dc c hc, hcB]
      rw [e] at hmem
      exact hmem
  · rw [hV1]
    apply C.eq_subG inf_le_left
    intro v
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, ← r1_fix _ (C.cd_lt v)]
    constructor
    · rintro ⟨-, hv⟩ B hB
      obtain ⟨x, hx, hxR, rfl⟩ := hRsurj B hB
      exact (commute_iff_code C hx v).1 (hv x hxR)
    · intro hv
      exact ⟨v.2, fun x hxR => (commute_iff_code C (hRN hxR) v).2
        (hv _ (hcode x (hRN hxR) hxR))⟩

theorem lemma12_7_2_four
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    IsFLine L V (V2 T L V) ∧
      (L ⊔ T) ⊓ Subgroup.normalizer (V2 T L V : Set G) = P2 T L V ⊔ T ∧
      Nat.card ↥(autOn (R2 T L V) V) = 4 ∧
      (∀ r ∈ R2 T L V, r ^ 2 ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ r ∈ R2 T L V, r ∉ Subgroup.centralizer (V : Set G) →
        V ⊓ Subgroup.centralizer ({r} : Set G) = V2 T L V) ∧
      ⁅V, R2 T L V⁆ = V2 T L V := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV2 := V2_eq h hC
  have hR : ∀ a, a ∈ autOn (R2 T L V) V ↔ C.cB a ∈ r2 := by
    rw [R2, P2, hV2]
    exact mem_autOn_R h1222 h hC.1 l2c_lt id_mem_r2 r2_closed r2_sub r2_sq cert_n2 cert_m2
  have hRN : R2 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (pof_le_normalizer h1222 h _)
  have hRsurj : ∀ B ∈ r2, ∃ x, ∃ hx : x ∈ Subgroup.normalizer (V : Set G), x ∈ R2 T L V ∧
      C.cB (conjAct V ⟨x, hx⟩) = B := by
    intro B hB
    obtain ⟨a, rfl⟩ := hC.1.2 B (r2_sub B hB).1
    obtain ⟨x, hx, hxR, rfl⟩ := mem_autOn'.1 ((hR a).2 hB)
    exact ⟨x, hx, hxR, rfl⟩
  have hcode : ∀ x (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ R2 T L V →
      C.cB (conjAct V ⟨x, hx⟩) ∈ r2 := fun x hx hxR => (hR _).1 (conjAct_mem_autOn hxR hx)
  refine ⟨⟨⟨(V2_eq h hC ▸ C.subG_le _ _ _ : V2 T L V ≤ V), ?_⟩, ?_⟩,
    sup_inf_normalizer h (T_le_normalizer_V2 h1222 h), ?_, ?_, ?_, ?_⟩
  · rw [hV2]
    exact XOf_le_normalizer_subG h1222 h hC.1 zs6_presv_l2c
  · rw [hV2, C.card_subG l2c_nodup l2c_lt]
    rfl
  · have e : autOn (R2 T L V) V = C.subOf r2 id_mem_r2 r2_closed := by
      ext a
      rw [hR, C.mem_subOf]
    rw [e, C.card_subOf r2_nodup (fun B hB => hC.1.2 B (r2_sub B hB).1)]
    rfl
  · intro r hr
    exact sq_mem_centralizer (hRN hr) (r2_sq _ (hcode r (hRN hr) hr))
  · intro r hr hrC
    have hrN := hRN hr
    have hB := hcode r hrN hr
    have hne : C.cB (conjAct V ⟨r, hrN⟩) ≠ B6.id := fun he =>
      hrC ((conjAct_eq_one' hrN).1 (C.cB_eq_one.1 he))
    rw [hV2]
    apply C.eq_subG inf_le_left
    intro v
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, ← r2_fix _ hB hne _ (C.cd_lt v)]
    constructor
    · rintro ⟨-, hv⟩
      exact (commute_iff_code C hrN v).1 hv.symm
    · intro hv
      exact ⟨v.2, ((commute_iff_code C hrN v).2 hv).symm⟩
  · rw [hV2]
    apply le_antisymm
    · apply commutator_le_subG C hRN
      intro x hx hxR c hc
      exact r2_comm _ (hcode x hx hxR) c hc
    · intro g hg
      obtain ⟨hgV, hgl⟩ := hg
      obtain ⟨B, hB, c, hc, B', hB', c', hc', hcB⟩ := cert_r2span _ hgl
      obtain ⟨x, hx, hxR, rfl⟩ := hRsurj B hB
      obtain ⟨x', hx', hxR', rfl⟩ := hRsurj B' hB'
      have hc1 : c < 64 := List.mem_range.1 hc
      have hc2 : c' < 64 := List.mem_range.1 hc'
      have hm1 := Subgroup.commutator_mem_commutator (C.dc c).2 hxR
      have hm2 := Subgroup.commutator_mem_commutator (C.dc c').2 hxR'
      rw [commutator_eq_coe hx] at hm1
      rw [commutator_eq_coe hx'] at hm2
      have hm := Subgroup.mul_mem _ hm1 hm2
      rw [← Subgroup.coe_mul] at hm
      have e : (C.dc c * (conjAct V ⟨x, hx⟩ (C.dc c))⁻¹ *
          (C.dc c' * (conjAct V ⟨x', hx'⟩ (C.dc c'))⁻¹) : ↥V) = ⟨g, hgV⟩ := by
        apply C.cd_injective
        rw [C.cd_mul, cd_commutator, cd_commutator, C.cd_dc c hc1, C.cd_dc c' hc2]
        exact hcB.symm
      rw [e] at hm
      exact hm

end CFSG.Quasithin.H13.S127.Mod

end
