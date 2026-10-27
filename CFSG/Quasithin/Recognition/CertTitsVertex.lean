module

public import CFSG.Quasithin.Recognition.CertTitsJTable
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits CFSG.LieType.BorelTits

theorem titsH_inf_titsN
    : titsH ⊓ titsN = titsS := by
  refine le_antisymm ?_ (le_inf titsS_le_titsH titsS_le_titsN)
  have hle : titsH ⊓ titsN ≤ titsD := inf_le_left.trans titsH_le_titsD
  have hX : titsSD ≤ (titsH ⊓ titsN).subgroupOf titsD := fun x hx =>
    Subgroup.mem_inf.2 ⟨titsS_le_titsH hx, titsS_le_titsN hx⟩
  rcases titsD_overgroups _ hX with h | h | h | h
  · intro x hx
    have h1 : (⟨x, hle hx⟩ : titsD) ∈ (titsH ⊓ titsN).subgroupOf titsD := hx
    rw [h] at h1
    exact h1
  · exfalso
    have h1 : titsHD ≤ titsND := fun x hx => by
      have : x ∈ (titsH ⊓ titsN).subgroupOf titsD := h ▸ hx
      exact this.2
    have := Subgroup.card_dvd_of_le h1
    rw [card_titsHD, card_titsND] at this
    omega
  · exfalso
    have h1 : titsND ≤ titsHD := fun x hx => by
      have : x ∈ (titsH ⊓ titsN).subgroupOf titsD := h ▸ hx
      exact this.1
    have := Subgroup.card_dvd_of_le h1
    rw [card_titsHD, card_titsND] at this
    omega
  · exfalso
    have h1 : (⊤ : Subgroup titsD) ≤ titsHD := fun x _ => by
      have : x ∈ (titsH ⊓ titsN).subgroupOf titsD := h ▸ Subgroup.mem_top x
      exact this.1
    have := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_top, card_titsD, card_titsHD] at this
    omega

theorem mem_omegaOneCenter_titsHN_iff
    (x : Equiv.Perm (Fin 1755)) :
    x ∈ quasithinOmegaOneCenter (titsH ⊓ titsN) ↔ x = 1 ∨ x = titsZ := by
  rw [titsH_inf_titsN, mem_quasithinOmegaOneCenter_iff]
  constructor
  · rintro ⟨hxS, hxc, -⟩
    have hmem : x ∈ ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g.1 g.2)
    rw [titsS_center] at hmem
    exact hmem
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, one_mem _, one_pow 2⟩
    · exact ⟨titsZ_mem_titsS, titsZ_mem_centralizer_S, by rw [pow_two]; exact titsZ_mul_self⟩

theorem titsH_flag_orbit
    : ∀ f ∈ titsF5, ∃ h : titsH, titsHFlag h 0 = f := by
  classical
  let _ : MulAction titsH (Fin 8775) := MulAction.compHom _ titsHFlag
  have hsub : MulAction.orbit titsH (0 : Fin 8775) ⊆ titsF5 := by
    rintro _ ⟨h, rfl⟩
    exact (titsHFlag_mem h 0).2 (by rw [titsF5_eq]; simp)
  have hstab : MulAction.stabilizer titsH (0 : Fin 8775) = titsS.subgroupOf titsH := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have h1 := mem_titsSD_iff (Subgroup.inclusion titsH_le_titsD g)
    exact h1.symm
  have hcard : Set.ncard (MulAction.orbit titsH (0 : Fin 8775)) = 5 := by
    have h1 := Subgroup.card_mul_index (titsS.subgroupOf titsH)
    rw [card_subgroupOf_eq titsS_le_titsH, titsQS_facts.2.2.2, titsQH_facts.2.2.2] at h1
    have h2 : (titsS.subgroupOf titsH).index = 5 := by omega
    rw [← MulAction.index_stabilizer titsH (0 : Fin 8775), hstab, h2]
  have heq : MulAction.orbit titsH (0 : Fin 8775) = titsF5 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [titsF5_ncard, hcard]) (Set.toFinite _)
  intro f hf
  rw [← heq] at hf
  obtain ⟨h, rfl⟩ := hf
  exact ⟨h, rfl⟩

theorem pCoreOf_titsH_le_titsS
    : pCoreOf 2 titsH ≤ titsS := by
  have hSp : IsPGroup 2 (titsS.subgroupOf titsH) :=
    IsPGroup.of_card (n := 11) (by
      rw [card_subgroupOf_eq titsS_le_titsH, titsQS_facts.2.2.2]
      norm_num)
  have hidx : ¬ 2 ∣ (titsS.subgroupOf titsH).index := by
    have h := Subgroup.card_mul_index (titsS.subgroupOf titsH)
    rw [card_subgroupOf_eq titsS_le_titsH, titsQS_facts.2.2.2, titsQH_facts.2.2.2] at h
    have : (titsS.subgroupOf titsH).index = 5 := by omega
    rw [this]
    decide
  have hnorm := CFSG.LieType.BorelTits.pCore_normal (G := ↥titsH) 2
  have hle := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥titsH) 2).le_sylow_of_normal
    (hSp.toSylow hidx)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have := hle hy
  rw [IsPGroup.toSylow_coe] at this
  exact this

theorem pCoreOf_titsH
    : pCoreOf 2 titsH = titsJ := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ titsH := pCoreOf_le 2 titsH hx
    have hconj : ∀ h : titsH, (h : Equiv.Perm (Fin 1755))⁻¹ * x * h ∈ pCoreOf 2 titsH := by
      intro h
      have := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf 2 titsH (titsH.inv_mem h.2)) x).1 hx
      simpa using this
    have hfix : ∀ f ∈ titsF5, titsHFlag ⟨x, hxH⟩ f = f := by
      intro f hf
      obtain ⟨h, rfl⟩ := titsH_flag_orbit f hf
      have h1 := pCoreOf_titsH_le_titsS (hconj h)
      have h2 := (mem_titsSD_iff ⟨_, titsH_le_titsD (titsH.mul_mem (titsH.mul_mem
        (titsH.inv_mem h.2) hxH) h.2)⟩).1 h1
      have e : (⟨_, titsH_le_titsD (titsH.mul_mem (titsH.mul_mem (titsH.inv_mem h.2) hxH) h.2)⟩ :
          titsD) = (Subgroup.inclusion titsH_le_titsD h)⁻¹ *
            Subgroup.inclusion titsH_le_titsD ⟨x, hxH⟩ * Subgroup.inclusion titsH_le_titsD h :=
        rfl
      rw [e, map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_eq_iff_eq] at h2
      exact h2
    have h5 : titsH5 ⟨x, hxH⟩ = 1 := (titsH5_eq_one_iff _).2 hfix
    have hker : (⟨x, hxH⟩ : titsH) ∈ titsH5.ker := h5
    rw [titsH5_range_ker.2] at hker
    exact hker
  · have hJn := (Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1
      AT_Tits_intrinsic_local_pair.2.2.2.2.2.2.1
    exact le_pCoreOf_of_le_normalizer 2 titsJ_le_titsH hJn
      AT_Tits_intrinsic_local_pair.2.2.2.2.1

@[expose] def jVTable
    : VTable titsH titsN 512 where
  toVOps := jOps
  el := jEl
  el_inj := jEl_inj
  el_range := fun x => by
    rw [pCoreOf_titsH]
    exact ⟨fun hx => jEl_surj hx, fun ⟨i, hi⟩ => hi ▸ jEl_mem i⟩
  el_mul := jEl_mul
  el_inv := jEl_inv
  el_one := jEl_one
  Z_iff := fun x => by
    rw [mem_omegaOneCenter_titsHN_iff, jEl_z]

theorem titsVertexFacts
    : TitsLikeVertexFacts titsH titsN := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC⟩ := jModel_check
  exact titsLikeVertexFacts_of_table jVTable hC jC jC_mem jC_pow_five jEl_cc jGen jGen_mem jEl_cj

end CFSG.Quasithin
