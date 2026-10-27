module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

private theorem pRank_three_le_one_of_not_dvd_card {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h : ¬ 9 ∣ Nat.card H) : CFSG.Open.pRank 3 H ≤ 1 := by
  by_contra hcon
  obtain ⟨E, hEH, -, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) H
  apply h
  have h1 : 3 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact pow_dvd_pow 3 (by omega)
  exact h1.trans (Subgroup.card_dvd_of_le hEH)

theorem pRank_three_overgroup_alt6 {S Y : Subgroup (alternatingGroup (Fin 6))}
    (hS : IsSylowTwoOf S ⊤) (hSY : S ≤ Y) (hY : Y ≠ ⊤) : CFSG.Open.pRank 3 Y ≤ 1 := by
  refine pRank_three_le_one_of_not_dvd_card fun h9 => ?_
  have hG : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hidx : Nat.card Y * Y.index = 360 := by rw [Subgroup.card_mul_index, hG]
  have hodd : ¬ 2 ∣ Y.index := by
    have h1 : ¬ 2 ∣ S.index := by
      have e : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
      have := hS.2.2
      rwa [e] at this
    intro h2
    exact h1 (h2.trans (Subgroup.index_dvd_of_le hSY))
  obtain ⟨m, hm⟩ := h9
  have h40 : m * Y.index = 40 := by
    have : 9 * (m * Y.index) = 9 * 40 := by
      rw [← mul_assoc, ← hm]
      omega
    omega
  have hdvd : Y.index ∣ 40 := ⟨m, by rw [← h40, mul_comm]⟩
  have hk : Y.index = 1 ∨ Y.index = 5 := by
    have hle : Y.index ≤ 40 := Nat.le_of_dvd (by norm_num) hdvd
    revert hdvd hodd hle
    generalize Y.index = k
    intro hodd hle hdvd
    interval_cases k <;> omega
  rcases hk with h1 | h5
  · exact hY (Subgroup.index_eq_one.1 h1)
  ·
    have hcore : Y.normalCore = ⊥ := by
      rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
        (N := Y.normalCore) with h | h
      · exact h
      · exact absurd (eq_top_iff.2 (h ▸ Y.normalCore_le)) hY
    have hinj : Function.Injective (MulAction.toPermHom (alternatingGroup (Fin 6))
        (alternatingGroup (Fin 6) ⧸ Y)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
      exact hcore
    have hdvd5 := Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_perm, hG] at hdvd5
    have h5' : Nat.card (alternatingGroup (Fin 6) ⧸ Y) = 5 := h5
    rw [h5'] at hdvd5
    have : Nat.factorial 5 = 120 := by decide
    rw [this] at hdvd5
    omega

private theorem pRank_three_overgroup_of_mulEquiv {X Z : Type} [Group X] [Finite X] [Group Z]
    [Finite Z] (e : X ≃* Z) {T₀ : Subgroup Z} (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ Y : Subgroup Z, T₀ ≤ Y → Y ≠ ⊤ → CFSG.Open.pRank 3 Y ≤ 1)
    {S Y : Subgroup X} (hS : IsSylowTwoOf S ⊤) (hSY : S ≤ Y) (hY : Y ≠ ⊤) :
    CFSG.Open.pRank 3 Y ≤ 1 := by
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e (X := S) (Y := ⊤)).2 hS
    simpa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using this
  obtain ⟨g, hg⟩ := L246C127.exists_conj_of_isSylowTwoOf' hS' hT₀
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) :=
    (MulAut.conj g).injective.comp e.injective
  have hT : T₀ ≤ (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono (Subgroup.map_mono hSY)
  have hne : (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    rw [Subgroup.map_map]
    intro htop
    apply hY
    rw [← Subgroup.comap_map_eq_self_of_injective hinj Y, htop, Subgroup.comap_top]
  have h1 := h _ hT hne
  rw [Subgroup.map_map] at h1
  exact (CFSG.SectionRank.pRank_le_map (by norm_num) _ hinj Y).trans h1

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
private theorem card_and_exists_member_of_cert {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    (c : LatCert (Equiv.Perm (Fin n))) (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hc : c.check RN.enc = true) (Y : Subgroup ↥A)
    (hDY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y) :
    Nat.card A = c.msize ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
      L ≤ A ∧ Y = L.subgroupOf A ∧ Nat.card L ∈ c.sizes := by
  subst hM
  refine ⟨c.card_m (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc), ?_⟩
  obtain ⟨L, -, hLA, hYL, hcard⟩ := c.overgroup_cases (rawIsEnc n) hc Y hDY
  exact ⟨Subgroup.closure {g | g ∈ L}, hLA, hYL, hcard⟩

open CFSG.QuasithinUnique.Bridge.Over in
private theorem pRank_three_overgroup_permU33
    (Y : Subgroup ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup)
    (hDY : CertU33.D.subgroupOf CFSG.GH74.KGroups.U33.QP.originalSubgroup ≤ Y) (hne : Y ≠ ⊤) :
    CFSG.Open.pRank 3 Y ≤ 1 := by
  obtain ⟨hPc, L, hLP, hYL, hcard⟩ :=
    card_and_exists_member_of_cert CertU33.cert CertU33.closure_mGens CertU33.cert_check Y hDY
  have hLc : Nat.card L = 32 ∨ Nat.card L = 96 ∨ Nat.card L = 6048 := by
    have h : Nat.card L ∈ [32, 96, 96, 6048] := hcard
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  have hmsize : CertU33.cert.msize = 6048 := rfl
  have hYc : Nat.card Y = Nat.card L := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv
  refine pRank_three_le_one_of_not_dvd_card ?_
  rcases hLc with h | h | h
  · rw [hYc, h]
    norm_num
  · rw [hYc, h]
    norm_num
  · exfalso
    apply hne
    have hLeq : L = CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
      Subgroup.eq_of_le_of_card_ge hLP (by rw [h, hPc, hmsize])
    rw [hYL, hLeq, Subgroup.subgroupOf_self]

open CFSG.QuasithinUnique.Bridge.Over in
theorem pRank_three_overgroup_psu33
    {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) {S Y : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hSY : S ≤ Y) (hY : Y ≠ ⊤) : CFSG.Open.pRank 3 Y ≤ 1 := by
  have hL : CFSG.Blueprint.LieModel X .PSU 3 3 1 := Or.inl ⟨by decide, h⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  exact pRank_three_overgroup_of_mulEquiv e CertU33.isSylow_D
    (fun Y' hY' hne => pRank_three_overgroup_permU33 Y' hY' hne) hS hSY hY

end CFSG.Quasithin
