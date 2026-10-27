module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RW
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLVec

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_mem_Vt_not_mem_sup_of_SLNat (hc : Ctx M Q Z B) {t : G} (hSL : SLNat hc t) :
    ∃ v ∈ Vt M (LB M Q B) B Z t, v ∉ (B ⊔ Z : Subgroup G) := by
  obtain ⟨K, _, _, hK, m, hm, φ, hrange, hker, hRN, hZn, ψ, hψ⟩ := hSL
  by_contra hno
  push Not at hno
  have hle : Vt M (LB M Q B) B Z t ≤ B ⊔ Z := fun v hv => hno v hv
  haveI := hZn
  have hcardQ : Nat.card (↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ m := by
    rw [Nat.card_congr ψ.toEquiv,
      show Nat.card (Multiplicative (Fin m → K)) = Nat.card (Fin m → K) from rfl,
      Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  have hcardZ : Nat.card (Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Z_le_Vt).toEquiv
  have hcardV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ m * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf _), hcardQ, hcardZ]
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hcle := Subgroup.card_le_of_le hle
  rw [hcardV, hc.card_sup_Z, hBcard] at hcle
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ m := Nat.pow_le_pow_right (by omega) hm
  have h1 : Nat.card Z * Nat.card Z * Nat.card Z ≤ Nat.card Z * Nat.card Z * 1 := by
    calc Nat.card Z * Nat.card Z * Nat.card Z = Nat.card Z ^ 2 * Nat.card Z := by ring
      _ ≤ Nat.card Z ^ m * Nat.card Z := Nat.mul_le_mul_right _ hpow
      _ ≤ Nat.card Z * Nat.card Z * 1 := by rw [mul_one]; exact hcle
  have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega

theorem wpoint57_caseA (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t)
    (hSL : SLNat hc t) (hBt : B ≤ QB (Subgroup.zpowers t)) (hA : CaseA Q Z t)
    (hVQB : Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B) {v : G} (hvV : v ∈ Vt M (LB M Q B) B Z t)
    (hvBZ : v ∉ (B ⊔ Z : Subgroup G)) :
    ∃ C : Subgroup G, IsConjB M B C ∧ C ≠ B ∧ C ≤ Q ⊓ QB (Subgroup.zpowers t) ⊓ QB B := by
  obtain ⟨K, _, _, hK, m, hm, φ, hrange, hker, hRN, hZn, ψ, hψ⟩ := hSL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact hc.hyp.q4
  have hBZ : ∃ b ∈ B, b ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hc.conj
    exact hc.ne (Subgroup.eq_of_le_of_card_ge (fun x hx => hcon x hx)
      (by rw [hg, card_conjSubgroup]))
  obtain ⟨b, hbB, hbZ⟩ := hBZ
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt h.mem hbB
  have hvec0 : ∀ x : ↥(Vt M (LB M Q B) B Z t),
      Multiplicative.toAdd (ψ (QuotientGroup.mk x)) = 0 ↔ (x : G) ∈ Z := by
    intro x
    rw [toAdd_eq_zero, ← map_one ψ, ψ.injective.eq_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hyne : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨b, hbV⟩)) ≠ 0 :=
    fun hh => hbZ ((hvec0 _).mp hh)
  have hvZ : v ∉ Z := fun hz => hvBZ (Subgroup.mem_sup_right hz)
  have hxne : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hvV⟩)) ≠ 0 :=
    fun hh => hvZ ((hvec0 _).mp hh)
  obtain ⟨g, hgSL, hgy⟩ := exists_statedSL_mulVec_eq hm hxne hyne
  obtain ⟨c, hcomm, hcg⟩ := caseA_cover hc h hA hm hK4 φ hrange hker g hgSL
  have hwV : (c : G) * b * (c : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hRN c.2) b).mp hbV
  have hsec := hψ c ⟨b, hbV⟩ ⟨(c : G) * b * (c : G)⁻¹, hwV⟩ rfl
  rw [hcg, hgy] at hsec
  have hmk := ψ.injective (Multiplicative.toAdd.injective hsec)
  have hwv := (QuotientGroup.eq).mp hmk
  have hz : ((c : G) * b * (c : G)⁻¹)⁻¹ * v ∈ Z := Subgroup.mem_subgroupOf.mp hwv
  have hcM : (c : G) ∈ M := hc.Rt_le_M t c.2
  refine ⟨conjSubgroup (c : G) B, ⟨c, hcM, rfl⟩, ?_, ?_⟩
  · intro hCB
    apply hvBZ
    have hwC : (c : G) * b * (c : G)⁻¹ ∈ conjSubgroup (c : G) B := by
      rw [mem_conjSubgroup, show (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) * (c : G) = b by
        group]
      exact hbB
    have hwB : (c : G) * b * (c : G)⁻¹ ∈ B := by
      rw [hCB] at hwC
      exact hwC
    have key : (c : G) * b * (c : G)⁻¹ * (((c : G) * b * (c : G)⁻¹)⁻¹ * v) = v := by group
    rw [← key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwB) (Subgroup.mem_sup_right hz)
  · intro x hx
    rw [mem_conjSubgroup] at hx
    have e : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ = x := by group
    have hxP : x ∈ Q ⊓ QB (Subgroup.zpowers t) := by
      have h1 := caseA_conj_P hc hcM hcomm
        (show (c : G)⁻¹ * x * (c : G) ∈ Q ⊓ QB (Subgroup.zpowers t) from ⟨hc.le hx, hBt hx⟩)
      rwa [e] at h1
    have hxV : x ∈ Vt M (LB M Q B) B Z t := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hRN c.2) _).mp (hc.B_le_Vt h.mem hx)
      rwa [e] at h1
    exact ⟨hxP, (hVQB hxV).2⟩

theorem wpoint57_caseB (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t) (hSL : SLNat hc t)
    (hb : ∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) (hBt : B ≤ QB (Subgroup.zpowers t))
    (hA : ¬ CaseA Q Z t) (hVQB : Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B) {v : G}
    (hvV : v ∈ Vt M (LB M Q B) B Z t) (hvBZ : v ∉ (B ⊔ Z : Subgroup G)) :
    ∃ C : Subgroup G, IsConjB M B C ∧ C ≠ B ∧ C ≤ Q ⊓ QB (Subgroup.zpowers t) ⊓ QB B := by
  have hRT : RootTrans M Q Z B :=
    rootTrans_of_all h34 hc h (hspread G M Q Z B hc n h.width h.n_gt h.noA2 h.gen)
  obtain ⟨Y, k, -, -, hs⟩ := h.exists_root hc hb
  have hBY : B ≤ QB Y := root_le_QB_of_le_QB_zpowers hs hc.conj hBt
  have hVY : Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB Y) ⊔ Z :=
    stroth_5_7_caseB_core h34 hc h hRT hSL hs hBY hA
  have hgen : ∃ m ∈ M, t ∈ conjSubgroup m (LB M Q B) ∧
      ¬ conjSubgroup m B ≤ (B ⊔ Z : Subgroup G) := by
    by_contra hno
    push Not at hno
    apply hvBZ
    have hle : Vt M (LB M Q B) B Z t ≤ B ⊔ Z := by
      unfold Vt
      exact sup_le le_sup_right (iSup₂_le fun m hm => iSup_le fun ht => hno m hm ht)
    exact hle hvV
  obtain ⟨m, hm, htm, hmB⟩ := hgen
  obtain ⟨c₀, hc₀, hc₀BZ⟩ := Set.not_subset.mp hmB
  have hc₀V : c₀ ∈ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm htm hc₀
  obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_of_mem_sup
    (fun a (ha : a ∈ Q ⊓ QB Y) z hz => (Smith81.Z_central hc.hyp hz ha.1).symm) (hVY hc₀V)
  have hcm := hc.conj_of_mem hm
  have hazZ : a ∉ Z := fun haZ => hc₀BZ (by
    rw [haz]
    exact Subgroup.mem_sup_right (Z.mul_mem haZ hz))
  have haBm : a ∈ (conjSubgroup m B ⊔ Z : Subgroup G) := by
    have e : a = c₀ * z⁻¹ := by rw [haz]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₀) (Subgroup.mem_sup_right (Z.inv_mem hz))
  obtain ⟨p, hpQ, hap⟩ := hcm.exists_mem_conj_of_mem_sup haBm hazZ
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have hCconj := hcm.conj_of_mem hpM
  have ha1 : a ≠ 1 := fun h1 => hazZ (h1 ▸ Z.one_mem)
  have hCY : conjSubgroup p (conjSubgroup m B) ≤ QB Y :=
    Smith81.IsZConjugate.le_QB_of_mem hc.hyp hs.conj hCconj.conj ha1 hap ha.2
  refine ⟨conjSubgroup p (conjSubgroup m B), ⟨p * m, M.mul_mem hpM hm, ?_⟩, ?_, ?_⟩
  · rw [conjSubgroup_mul]
  · intro hCB
    apply hc₀BZ
    rw [haz]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hz)
    rw [hCB] at hap
    exact hap
  · intro x hx
    have hxV : x ∈ Vt M (LB M Q B) B Z t := by
      have hpR : p ∈ Rt M (LB M Q B) t := hc.Q_le_Rt h.mem hpQ
      rw [mem_conjSubgroup] at hx
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt h.mem hpR) _).mp
        (sec39_conjB_le_Vt hm htm hx)
      rwa [show p * (p⁻¹ * x * p) * p⁻¹ = x by group] at h1
    exact ⟨⟨(hVQB hxV).1, QB_le_QB_zpowers hs (hCY hx)⟩, (hVQB hxV).2⟩

end HS9

theorem sec57W_of (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement) :
    Sec57WStatement := by
  intro G _ _ M Q Z B hc n t h hSL hb hBt
  have h35 := (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.1
  have hVQB : Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B := hc.Vt_le_inf_QB_of_SLNat h h35 hSL
  obtain ⟨v, hvV, hvBZ⟩ := HS9.exists_mem_Vt_not_mem_sup_of_SLNat hc hSL
  by_cases hA : CaseA Q Z t
  · exact HS9.wpoint57_caseA hc h hSL hBt hA hVQB hvV hvBZ
  · exact HS9.wpoint57_caseB h34 hspread hc h hSL hb hBt hA hVQB hvV hvBZ

end CFSG.RankThree.GF2n.Stroth80
