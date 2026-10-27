module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_a

namespace CFSG
end CFSG
open CFSG


public theorem CFSG.lemma_3_2_b_no_solv {G : Type*} [Group G] [Finite G]
    (K R N : Subgroup G) [N.Normal]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hKnle : ¬ K ≤ N) :
    IsFrobeniusGroupWithKernelComplement
      (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  let _ : K.Normal := hfrob.normal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hN_le_K : N ≤ K := lemma_3_2_a_no_solv (K := K) (R := R) (N := N) hfrob hKnle
  have hmap_compl : (K.map q).IsComplement' (R.map q) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      rw [Subgroup.mem_map] at hxK hxR
      rcases hxK with ⟨k, hkK, hkx⟩
      rcases hxR with ⟨r, hrR, hrx⟩
      have hrk_eq : (r : G)⁻¹ * k ∈ N := by
        exact QuotientGroup.eq.mp (hrx.trans hkx.symm)
      have hr_inv_mem_K : (r : G)⁻¹ ∈ K := by
        have hmemK : (r : G)⁻¹ * k ∈ K := hN_le_K hrk_eq
        have : ((r : G)⁻¹ * k) * k⁻¹ ∈ K := K.mul_mem hmemK (K.inv_mem hkK)
        simpa [mul_assoc] using this
      have hr_mem_K : (r : G) ∈ K := by
        simpa using K.inv_mem hr_inv_mem_K
      have hr_eq_one : (r : G) = 1 := by
        have hr_bot : (r : G) ∈ (⊥ : Subgroup G) :=
          (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) hr_mem_K hrR
        simpa using hr_bot
      calc
        x = q r := hrx.symm
        _ = 1 := by simp [q, hr_eq_one]
    · rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := N) x
      rcases hfrob.isComplement'.2 g with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hgr⟩
      have hgr' : (k : G) * r = g := by
        simpa using hgr
      refine ⟨q k, ?_, q r, ?_, ?_⟩
      · exact ⟨k, hkK, rfl⟩
      · exact ⟨r, hrR, rfl⟩
      · change q (k * r) = q g
        simpa using congrArg q hgr'
  have hK_ne : K ≠ ⊥ := by
    intro hK_bot
    exact hKnle (hK_bot ▸ bot_le)
  have hKmap_ne : K.map q ≠ ⊥ := by
    intro hKmap_bot
    apply hKnle
    intro k hkK
    have hkq_mem_bot : q k ∈ (⊥ : Subgroup (G ⧸ N)) := by
      rw [← hKmap_bot]
      exact ⟨k, hkK, rfl⟩
    have hkq_eq_one : q k = 1 := by
      simpa using hkq_mem_bot
    simpa [q] using (QuotientGroup.eq_one_iff (N := N) k).mp hkq_eq_one
  have hRmap_ne : R.map q ≠ ⊥ := by
    intro hRmap_bot
    have hR_le_N : R ≤ N := by
      simpa [q] using (Subgroup.map_eq_bot_iff (H := R) (f := q)).1 hRmap_bot
    have hR_le_K : R ≤ K := hR_le_N.trans hN_le_K
    have hR_bot : R = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro r hrR
      exact (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) (hR_le_K hrR) hrR
    exact hfrob.complement_ne_bot hR_bot
  have hcent :
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hK_ne hfrob.complement_ne_bot
      hfrob.normal hfrob.isComplement').1 hfrob
  have hcent_quot :
      ∀ x : R.map q, x ≠ 1 → elementCentralizerIn (K.map q) (x : G ⧸ N) = ⊥ := by
    intro x hx_ne
    have hx_val_ne : (x : G ⧸ N) ≠ 1 := by
      intro hx_val_eq
      exact hx_ne (Subtype.ext hx_val_eq)
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyK, hyC⟩
    change y ∈ K.map q at hyK
    rw [Subgroup.mem_map] at hyK
    rcases hyK with ⟨k, hkK, hkq⟩
    have hxR : (x : G ⧸ N) ∈ R.map q := x.property
    rw [Subgroup.mem_map] at hxR
    rcases hxR with ⟨r, hrR, hrq⟩
    have hr_ne_one : (r : G) ≠ 1 := by
      intro hr_eq_one
      apply hx_val_ne
      calc
        (x : G ⧸ N) = q r := hrq.symm
        _ = 1 := by simp [q, hr_eq_one]
    have hr_sub_ne : (⟨r, hrR⟩ : R) ≠ 1 := by
      intro hr_eq_one
      exact hr_ne_one (congrArg Subtype.val hr_eq_one)
    have hcent_r : elementCentralizerIn K (r : G) = ⊥ := hcent ⟨r, hrR⟩ hr_sub_ne
    let comm : G := k * r * k⁻¹ * r⁻¹
    have hcomm_in_K : comm ∈ K := by
      dsimp [comm]
      have hconj : r * k⁻¹ * r⁻¹ ∈ K :=
        hfrob.normal.conj_mem k⁻¹ (K.inv_mem hkK) r
      simpa [mul_assoc] using K.mul_mem hkK hconj
    have hcomm_in_N : comm ∈ N := by
      have hy_comm : y * (x : G ⧸ N) = (x : G ⧸ N) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hy_comm' : q k * q r = q r * q k := by
        calc
          q k * q r = y * (x : G ⧸ N) := by simp [hkq, hrq]
          _ = (x : G ⧸ N) * y := hy_comm
          _ = q r * q k := by simp [hkq, hrq]
      have hq_comm : q comm = 1 := by
        dsimp [comm]
        have :=
          congrArg (fun t : G ⧸ N => t * (q k)⁻¹ * (q r)⁻¹) hy_comm'
        simpa [q, mul_assoc] using this
      exact (QuotientGroup.eq_one_iff (N := N) comm).mp hq_comm
    let f : K → K := fun a =>
      ⟨(a : G) * r * (a : G)⁻¹ * r⁻¹, by
        have hconj : r * (a : G)⁻¹ * r⁻¹ ∈ K :=
          hfrob.normal.conj_mem (a : G)⁻¹ (K.inv_mem a.property) r
        simpa [mul_assoc] using K.mul_mem a.property hconj⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hab_val :
          (a : G) * r * (a : G)⁻¹ * r⁻¹ = (b : G) * r * (b : G)⁻¹ * r⁻¹ :=
        congrArg Subtype.val hab
      have hab_mul : (a : G) * r * (a : G)⁻¹ = (b : G) * r * (b : G)⁻¹ := by
        have := congrArg (fun t : G => t * r) hab_val
        simpa [mul_assoc] using this
      have hcomm : (b : G)⁻¹ * (a : G) * r = r * ((b : G)⁻¹ * (a : G)) := by
        have := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) hab_mul
        simpa [mul_assoc] using this
      have hba_cent : (b : G)⁻¹ * (a : G) ∈ elementCentralizerIn K (r : G) := by
        refine ⟨K.mul_mem (K.inv_mem b.property) a.property, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hba_eq_one : (b : G)⁻¹ * (a : G) = 1 := by
        have hbot : (b : G)⁻¹ * (a : G) ∈ (⊥ : Subgroup G) := by
          rw [hcent_r] at hba_cent
          simpa using hba_cent
        simpa using hbot
      have := congrArg (fun t : G => (b : G) * t) hba_eq_one
      simpa [mul_assoc] using this
    let fN : N → N := fun a =>
      ⟨(a : G) * r * (a : G)⁻¹ * r⁻¹, by
        have hconj : r * (a : G)⁻¹ * r⁻¹ ∈ N :=
          (inferInstance : N.Normal).conj_mem (a : G)⁻¹ (N.inv_mem a.property) r
        simpa [mul_assoc] using N.mul_mem a.property hconj⟩
    have hfN_inj : Function.Injective fN := by
      intro a b hab
      apply Subtype.ext
      have hab_val :
          (a : G) * r * (a : G)⁻¹ * r⁻¹ = (b : G) * r * (b : G)⁻¹ * r⁻¹ :=
        congrArg Subtype.val hab
      have hab_mul : (a : G) * r * (a : G)⁻¹ = (b : G) * r * (b : G)⁻¹ := by
        have := congrArg (fun t : G => t * r) hab_val
        simpa [mul_assoc] using this
      have hcomm : (b : G)⁻¹ * (a : G) * r = r * ((b : G)⁻¹ * (a : G)) := by
        have := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) hab_mul
        simpa [mul_assoc] using this
      have hba_cent : (b : G)⁻¹ * (a : G) ∈ elementCentralizerIn K (r : G) := by
        refine ⟨hN_le_K (N.mul_mem (N.inv_mem b.property) a.property), ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hba_eq_one : (b : G)⁻¹ * (a : G) = 1 := by
        have hbot : (b : G)⁻¹ * (a : G) ∈ (⊥ : Subgroup G) := by
          rw [hcent_r] at hba_cent
          simpa using hba_cent
        simpa using hbot
      have := congrArg (fun t : G => (b : G) * t) hba_eq_one
      simpa [mul_assoc] using this
    have hfN_surj : Function.Surjective fN := Finite.surjective_of_injective hfN_inj
    obtain ⟨n, hn_eq⟩ := hfN_surj ⟨comm, hcomm_in_N⟩
    let nK : K := ⟨(n : G), hN_le_K n.property⟩
    have hfnK_eq : f nK = ⟨comm, hcomm_in_K⟩ := by
      apply Subtype.ext
      have hn_val : (n : G) * r * (n : G)⁻¹ * r⁻¹ = comm := congrArg Subtype.val hn_eq
      simpa [f, fN, nK, comm] using hn_val
    have hfk_eq : f ⟨k, hkK⟩ = ⟨comm, hcomm_in_K⟩ := by
      apply Subtype.ext
      simp [f, comm]
    have hk_eq_n : (⟨k, hkK⟩ : K) = nK := hf_inj (hfk_eq.trans hfnK_eq.symm)
    have hk_mem_N : k ∈ N := by
      have hk_val_eq : k = n := congrArg Subtype.val hk_eq_n
      simp [hk_val_eq]
    calc
      y = q k := hkq.symm
      _ = 1 := by simpa [q] using (QuotientGroup.eq_one_iff (N := N) k).2 hk_mem_N
  exact
    (lemma_3_1 (G := G ⧸ N) (K := K.map q) (R := R.map q) hKmap_ne hRmap_ne
      (by simpa [q] using (inferInstance : (K.map (QuotientGroup.mk' N)).Normal)) hmap_compl).2
      hcent_quot

public theorem CFSG.lemma_3_2_b {G : Type*} [Group G] [Finite G] (K R N : Subgroup G) [N.Normal]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (_hsolvK : Group.IsSolvable K)
    (hKnle : ¬ K ≤ N) :
    IsFrobeniusGroupWithKernelComplement
      (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) :=
  lemma_3_2_b_no_solv K R N hfrob hKnle
