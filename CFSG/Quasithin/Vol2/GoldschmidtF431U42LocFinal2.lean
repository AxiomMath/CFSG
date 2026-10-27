module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocFinal
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocGeomG
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG5

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem mem_L0S_twenty : (20 : Fin 45) ∈ L0S := (mem_L0S_iff 20).2 (by simp)

theorem mem_L0S_twentyfour : (24 : Fin 45) ∈ L0S := (mem_L0S_iff 24).2 (by simp)

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G) [Finite G]

omit [Finite G] in
theorem commute_of_conj {e : Y} (heP : e ∈ P2) {h : G} (hh : h = C.Φ2 e)
    (hc : h * C.tG * h⁻¹ = C.tG) : e * tPrime = tPrime * e := by
  subst hh
  have h1 : C.Φ2 e * C.tG = C.tG * C.Φ2 e := by
    calc C.Φ2 e * C.tG = C.Φ2 e * C.tG * (C.Φ2 e)⁻¹ * C.Φ2 e := by group
      _ = C.tG * C.Φ2 e := by rw [hc]
  rw [tG_def, ← C.Φ2_mul heP (Vsub_le_P2 tPrime_mem_Vsub),
    ← C.Φ2_mul (Vsub_le_P2 tPrime_mem_Vsub) heP] at h1
  exact C.Φ2_inj (P2.mul_mem heP (Vsub_le_P2 tPrime_mem_Vsub))
    (P2.mul_mem (Vsub_le_P2 tPrime_mem_Vsub) heP) h1

omit [Finite G] in
theorem X1_G (K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (C.V2 : Set G) ⊓ Subgroup.centralizer ({C.tG} : Set G))
    (hn : ∀ e ∈ Subgroup.normalizer (C.V2 : Set G) ⊓ Subgroup.centralizer ({C.tG} : Set G),
      ∀ k ∈ K, e * k * e⁻¹ ∈ K)
    (hN : Subgroup.zpowers C.tG ≤ K) (h4 : ¬ 4 ∣ Nat.card K) : K = Subgroup.zpowers C.tG := by
  have hKr : K ≤ C.φ2.range := fun g hg => C.norm g (hK hg).1
  have hKc : ∀ k ∈ C.pre2 K, k * tPrime = tPrime * k := by
    intro k hk
    obtain ⟨hkP, hkK⟩ := C.mem_pre2.1 hk
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hK hkK).2
    rw [tG_def, ← C.Φ2_mul hkP (Vsub_le_P2 tPrime_mem_Vsub),
      ← C.Φ2_mul (Vsub_le_P2 tPrime_mem_Vsub) hkP] at h1
    exact C.Φ2_inj (P2.mul_mem hkP (Vsub_le_P2 tPrime_mem_Vsub))
      (P2.mul_mem (Vsub_le_P2 tPrime_mem_Vsub) hkP) h1
  have hKn : ∀ e : Y, e ∈ P2 → e * tPrime = tPrime * e → ∀ k ∈ C.pre2 K,
      e * k * e⁻¹ ∈ C.pre2 K := by
    intro e heP hec k hk
    obtain ⟨hkP, hkK⟩ := C.mem_pre2.1 hk
    have he : C.Φ2 e ∈ Subgroup.normalizer (C.V2 : Set G) ⊓
        Subgroup.centralizer ({C.tG} : Set G) := by
      refine ⟨C.Φ2_mem_normalizer heP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [tG_def, ← C.Φ2_mul heP (Vsub_le_P2 tPrime_mem_Vsub),
        ← C.Φ2_mul (Vsub_le_P2 tPrime_mem_Vsub) heP, hec]
    have h1 := hn (C.Φ2 e) he (C.Φ2 k) hkK
    refine C.mem_pre2.2 ⟨P2.mul_mem (P2.mul_mem heP hkP) (P2.inv_mem heP), ?_⟩
    rwa [C.Φ2_mul (P2.mul_mem heP hkP) (P2.inv_mem heP), C.Φ2_mul heP hkP, C.Φ2_inv heP]
  have hNK' : tPrime ∈ C.pre2 K :=
    C.mem_pre2.2 ⟨Vsub_le_P2 tPrime_mem_Vsub, hN (Subgroup.mem_zpowers _)⟩
  have h4' : ¬ 4 ∣ Nat.card (C.pre2 K) := by
    rw [C.card_pre2 hKr]
    exact h4
  have hK' := eq_zpowers_of_normal (C.pre2 K) C.pre2_le hKc hKn hNK' h4'
  refine le_antisymm (fun g hg => ?_) hN
  obtain ⟨y, hyP, rfl⟩ := C.exists_Φ2_of_mem_range (hKr hg)
  have hy : y ∈ C.pre2 K := C.mem_pre2.2 ⟨hyP, hg⟩
  rw [hK'] at hy
  rcases mem_zpowers_two tPrime_sq hy with h | h
  · rw [h, C.Φ2_one]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _

@[expose] noncomputable def geomData : GeomData G where
  V2 := C.V2
  t := C.tG
  u0 := C.z
  u15 := C.Φ2 (sY 15)
  u20 := C.Φ2 (sY 20)
  u24 := C.Φ2 (sY 24)
  Pt := C.IsPt
  Ln := C.IsLn
  Q := C.QG
  hVab := fun _ ha _ hb => C.V2_comm ha hb
  ht := C.Φ2_mem_V2 tPrime_mem_Vsub
  ht2 := C.tG_sq
  hu0 := C.z_mem_V2
  hu15 := C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_fifteen)
  hu20 := C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_twenty)
  hu24 := C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_twentyfour)
  hu0sq := C.z_sq
  hu15sq := C.V2_sq (C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_fifteen))
  hu20sq := C.V2_sq (C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_twenty))
  hu24sq := C.V2_sq (C.Φ2_mem_V2 (sY_mem_Vsub mem_L0S_twentyfour))
  hrel := by
    have h0 : C.z = C.Φ2 (sY 0) := by rw [C.z_eq, sY_zero]
    rw [h0, tG_def, ← C.Φ2_mul (Vsub_le_P2 (sY_mem_Vsub zero_mem_L0S))
      (Vsub_le_P2 (sY_mem_Vsub mem_L0S_twenty)), ← C.Φ2_mul
      (Vsub_le_P2 (sY_mem_Vsub mem_L0S_twentyfour)) (Vsub_le_P2 tPrime_mem_Vsub), sY0_mul_sY20]
  hu15ne := C.isPt_ne_one (C.isPt_Φ2_sY mem_L0S_fifteen)
  hPt := fun g _ hu => C.isPt_conj hu g
  hLn := fun g _ hW => C.isLn_conj hW g
  hLnV := ⟨1, by ext x; rw [mem_map_conj]; simp⟩
  hPt0 := ⟨1, by group⟩
  hPt15 := C.isPt_Φ2_sY mem_L0S_fifteen
  hPt20 := C.isPt_Φ2_sY mem_L0S_twenty
  hPt24 := C.isPt_Φ2_sY mem_L0S_twentyfour
  hnPt := by
    rintro ⟨g, hg⟩
    exact C.not_conj_z tPrime_mem_Vsub not_isConj_tPrime g hg
  hnPt0 := by
    rw [C.z_eq, ← sY_zero]
    exact C.not_isPt_sY_mul (Or.inl rfl)
  hnPt20 := C.not_isPt_sY_mul (Or.inr (Or.inl rfl))
  hnPt24 := C.not_isPt_sY_mul (Or.inr (Or.inr rfl))
  line_unique := fun _ hu hut _ _ hW hW' huW htW huW' htW' =>
    C.line_unique hu hut hW hW' huW htW huW' htW'
  line_comm := fun _ _ hu hu' hut hu't huu' _ hW huW htW =>
    C.line_comm hu hu' hut hu't huu' hW huW htW
  hXact := by
    intro h hn hc
    obtain ⟨e, heP, rfl⟩ := C.exists_Φ2_of_mem_range (C.norm h hn)
    exact C.conj_u15 heP (C.commute_of_conj heP rfl hc)
  hQp := C.isPGroup_QG
  hQm := C.QG_maximal
  hQH := C.QG_le_centralizer
  htQ := C.tG_mem_QG
  hu15Q := C.mem_QG.2 ⟨sY 15, sY_mem_QY mem_L0S_fifteen, rfl⟩
  hQz := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := C.mem_QG.1 hq
    have hc := comm_xY_of_mem_T (mem_QY_iff.1 hy).1
    rw [C.z_eq, ← C.Φ2_mul (QY_le_P2 hy) mem_P2_xY, ← C.Φ2_mul mem_P2_xY (QY_le_P2 hy), hc]
  hQact := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := C.mem_QG.1 hq
    exact C.conj_u15 (QY_le_P2 hy) (mem_QY_iff.1 hy).2
  hX1 := fun K hK hn hN h4 => C.X1_G K hK hn hN h4

theorem centralizer_tG_le_range : Subgroup.centralizer ({C.tG} : Set G) ≤ C.φ2.range :=
  fun _ hh => C.norm _ (C.geomData.centralizer_le_normalizer hh)

end Ctx

end CFSG.Quasithin.H13.F431.U42
