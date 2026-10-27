module

public import Certificates.Kernel.Census.Pg.ClsSyl
public import CFSG.Certificates.Kernel.W16ClsSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCover
public import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelPgCls

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.W16Cls CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CertificateChecks.KernelPg

theorem sgs_rep {j : ℕ} (hj : j < 36) : Rep 128 sgsArr[j]! (permOfArr 128 sgsArr[j]!) :=
  (rep_permOfArr ((chainCheckFacts chain_check).strong_inv j (by rw [sgsArr_size]; exact hj))).1

theorem sgs_pr {j : ℕ} (hj : j < 36) :
    PR (C.S j) (permOfArr 128 sgsArr[j]!) ∧ PR (C.SI j) (permOfArr 128 sgsArr[j]!)⁻¹ := by
  have hb : sgsArr[j]! = unpack 128 8 (C.S j) := arrBind_sound (bS j hj)
  have hp := Orb.allN_iff.1 perm j hj
  have h1 : Rep 128 (unpack 128 8 (C.S j)) (permOfArr 128 sgsArr[j]!) := hb ▸ sgs_rep hj
  exact ⟨Orb.prep_of_rep h1, Orb.prep_of_rep (rep_inv_of_isInvA h1 (Orb.isInvA_unpack hp))⟩

@[expose] noncomputable def ab : Fin 2 → Equiv.Perm (Fin 128) :=
  ![permOfArr 128 sgsArr[3]!, permOfArr 128 sgsArr[23]!]

theorem ab_pr (k : Fin 2) : PR (A k) (ab k) ∧ PR (AI k) (ab k)⁻¹ := by
  fin_cases k
  · exact sgs_pr (j := 3) (by norm_num)
  · exact sgs_pr (j := 23) (by norm_num)

@[expose] noncomputable def H : Subgroup (Equiv.Perm (Fin 128)) := Subgroup.closure (Set.range ab)

theorem word_mem (c : ℕ) : ∃ x ∈ H, PR (wordP A c) x :=
  wordP_sound (fun k => (ab_pr k).1) c

theorem H_eq : H = Pg := by
  apply le_antisymm
  · rw [H, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure (RawSchreierDatum.mem_ofArrays_original.2 ?_)
    fin_cases k
    · exact ⟨3, by norm_num, rfl⟩
    · exact ⟨23, by norm_num, rfl⟩
  · change Subgroup.closure {g | g ∈ QPg.original.toList} ≤ H
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := RawSchreierDatum.mem_ofArrays_original.1 hg
    obtain ⟨x, hx, hpx⟩ := word_mem (W j)
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 words_ok j hj)] at hpx
    rw [pr_unique (sgs_pr hj).1 hpx]
    exact hx

theorem rep_facts {j : ℕ} (hj : j < 9) :
    PR (RK j) (repPerm j) ∧ Rep 128 repArrs[j]! (repPerm j) ∧ repPerm j ∈ Pg ∧
      repPerm j * repPerm j = 1 ∧ repPerm j ≠ 1 := by
  have hr := Orb.allN_iff.1 rep_ok j hj
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  obtain ⟨x, hx, hpx⟩ := word_mem (RW j)
  rw [Nat.eq_of_beq_eq_true h1] at hpx
  have hb : repArrs[j]! = unpack 128 8 (RK j) := arrBind_sound (bR j hj)
  have hrx : Rep 128 repArrs[j]! x := hb ▸ Orb.rep_unpack hpx
  have hinv := isInvA_of_rep hrx (rep_invCand hrx)
  have he : repPerm j = x := (rep_permOfArr hinv).1.unique hrx
  rw [he]
  refine ⟨hpx, hrx, H_eq ▸ hx, ?_, ?_⟩
  · exact pr_unique (pr_pc hpx hpx) ((Nat.eq_of_beq_eq_true h2) ▸ pr_pid)
  · intro h1'
    rw [h1'] at hpx
    have hshr : RK j >>> 1024 = 0 := by
      have h := orb_ok j hj
      unfold orbK at h
      simp only [Bool.and_eq_true] at h
      exact Nat.eq_of_beq_eq_true h.1.1.1.2
    have := pr_inj hpx pr_pid hshr pid_shr
    rw [this] at h3
    simp at h3

@[expose] def cls (j : ℕ) : Set (Equiv.Perm (Fin 128)) :=
  {x | ∃ g ∈ Pg, x = g * repPerm j * g⁻¹}

theorem cls_spec {j : ℕ} (hj : j < 9) :
    (∀ x, x ∈ cls j ↔ ∃ i < NC j, PR (Tc j i) x) ∧ Nat.card (cls j) = NC j ∧
      ∀ i < NC j, Tc j i >>> 1024 = 0 := by
  have h := orbK_sound ab_pr (rep_facts hj).1 (arith_ok.1 j hj).1 (orb_ok j hj)
  rw [← H, H_eq] at h
  exact h

theorem card_cent' {j : ℕ} (hj : j < 9) :
    Nat.card {x : Pg // (x : Equiv.Perm (Fin 128)) * repPerm j = repPerm j * x} =
      centTab[j]! := by
  have h1 := U16.card_orbit_subgroup_mul Pg (repPerm j)
  have h2 : Nat.card {x : Equiv.Perm (Fin 128) // ∃ h ∈ Pg, x = h * repPerm j * h⁻¹} = NC j :=
    (cls_spec hj).2.1
  rw [h2, card_Pg] at h1
  have h3 : Nat.card {x : Pg // (x : Equiv.Perm (Fin 128)) * repPerm j = repPerm j * x} =
      Nat.card ↥(Pg ⊓ Subgroup.centralizer ({repPerm j} : Set (Equiv.Perm (Fin 128)))) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, Subgroup.mem_inf.2 ⟨x.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 x.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
          Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [h3]
  obtain ⟨hpos, hmul⟩ := arith_ok.1 j hj
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hmul.symm)

@[expose] noncomputable def sylP (k : Fin 4) : Equiv.Perm (Fin 128) :=
  Classical.choose (word_mem (SG k))

theorem sylP_spec (k : Fin 4) : sylP k ∈ H ∧ PR (SGP k) (sylP k) := by
  have h := Classical.choose_spec (word_mem (SG k))
  refine ⟨h.1, ?_⟩
  rw [← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 sylG_ok k k.2)]
  exact h.2

@[expose] noncomputable def K : Subgroup (Equiv.Perm (Fin 128)) := Subgroup.closure (Set.range sylP)

theorem K_spec : (∀ x, x ∈ K ↔ ∃ i < 8192, PR (L i) x) ∧ Nat.card K = 8192 ∧
    ∀ i < 8192, L i >>> 1024 = 0 :=
  sylK_sound (fun k => (sylP_spec k).2) (by norm_num) syl_ok

theorem K_le : K ≤ Pg := by
  rw [K, Subgroup.closure_le, ← H_eq]
  rintro _ ⟨k, rfl⟩
  exact (sylP_spec k).1

theorem K_invol {y : Equiv.Perm (Fin 128)} (hy : y ∈ K) (h1 : y ≠ 1) (h2 : y * y = 1) :
    ∃ j < 9, y ∈ cls j := by
  obtain ⟨i, hi, hpy⟩ := (K_spec.1 y).1 hy
  obtain ⟨j, hj, idx, hidx, he⟩ := invCovK_spec cov_ok hi hpy h1 h2
  exact ⟨j, hj, ((cls_spec hj).1 y).2 ⟨idx, hidx, he ▸ hpy⟩⟩

theorem invol_cover {g : Equiv.Perm (Fin 128)} (hg : g ∈ Pg) (h1 : g ≠ 1) (h2 : g * g = 1) :
    ∃ j < 9, g ∈ cls j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' : Subgroup Pg := K.subgroupOf Pg
  have hK' : Nat.card K' = 2 ^ 13 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe K_le).toEquiv, K_spec.2.1]
    norm_num
  have hp : IsPGroup 2 K' := IsPGroup.of_card hK'
  have hidx : ¬ 2 ∣ K'.index := by
    have h := K'.card_mul_index
    rw [hK', card_Pg] at h
    have : K'.index = 405 := by omega
    rw [this]
    decide
  let S := hp.toSylow hidx
  let gP : Pg := ⟨g, hg⟩
  have hgP2 : gP ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext h2
  have hgP1 : gP ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have hord : orderOf gP = 2 := orderOf_eq_prime hgP2 hgP1
  have hz : IsPGroup 2 (Subgroup.zpowers gP) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨c, hc⟩ : ∃ c : Pg, c • S = Q := MulAction.exists_smul_eq Pg S Q
  have hgQ : gP ∈ (Q : Subgroup Pg) := hQ (Subgroup.mem_zpowers gP)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgQ
  have e : (MulAut.conj c)⁻¹ • gP = c⁻¹ * gP * c := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e] at hgQ
  have hyS : c⁻¹ * gP * c ∈ K' := (IsPGroup.mem_toSylow hp hidx).1 hgQ
  have hyK : ((c⁻¹ * gP * c : Pg) : Equiv.Perm (Fin 128)) ∈ K := Subgroup.mem_subgroupOf.1 hyS
  have hy1 : ((c⁻¹ * gP * c : Pg) : Equiv.Perm (Fin 128)) ≠ 1 := by
    intro h
    apply h1
    have h' : c⁻¹ * gP * c = 1 := Subtype.ext h
    have : gP = 1 := by
      calc gP = c * (c⁻¹ * gP * c) * c⁻¹ := by group
        _ = 1 := by rw [h']; group
    exact congrArg Subtype.val this
  have hy2 : ((c⁻¹ * gP * c : Pg) : Equiv.Perm (Fin 128)) *
      ((c⁻¹ * gP * c : Pg) : Equiv.Perm (Fin 128)) = 1 := by
    have : (c⁻¹ * gP * c) * (c⁻¹ * gP * c) = 1 := by
      calc (c⁻¹ * gP * c) * (c⁻¹ * gP * c) = c⁻¹ * (gP * gP) * c := by group
        _ = 1 := by rw [← pow_two, hgP2]; group
    exact congrArg Subtype.val this
  obtain ⟨j, hj, g', hg', hy⟩ := K_invol hyK hy1 hy2
  refine ⟨j, hj, (c : Equiv.Perm (Fin 128)) * g', Pg.mul_mem c.2 hg', ?_⟩
  have hy' : (c : Equiv.Perm (Fin 128))⁻¹ * g * c = g' * repPerm j * g'⁻¹ := by
    rw [← hy]
    rfl
  calc g = c * ((c : Equiv.Perm (Fin 128))⁻¹ * g * c) * (c : Equiv.Perm (Fin 128))⁻¹ := by group
    _ = _ := by rw [hy']; group

theorem cls_sub {j : ℕ} (hj : j < 9) {x : Equiv.Perm (Fin 128)} (hx : x ∈ cls j) :
    x ∈ Pg ∧ x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨-, -, hR, hsq, hne⟩ := rep_facts hj
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨Pg.mul_mem (Pg.mul_mem hg hR) (Pg.inv_mem hg), ?_, ?_⟩
  · calc g * repPerm j * g⁻¹ * (g * repPerm j * g⁻¹) = g * (repPerm j * repPerm j) * g⁻¹ := by
          group
      _ = 1 := by rw [hsq]; group
  · intro h
    apply hne
    calc repPerm j = g⁻¹ * (g * repPerm j * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

theorem cls_disj {j j' : ℕ} (hj : j < 9) (hj' : j' < 9) {x : Equiv.Perm (Fin 128)}
    (hx : x ∈ cls j) (hx' : x ∈ cls j') : j = j' := by
  by_contra hne
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨g', hg', he⟩ := hx'
  have hmem : repPerm j' ∈ cls j := by
    refine ⟨g'⁻¹ * g, Pg.mul_mem (Pg.inv_mem hg') hg, ?_⟩
    calc repPerm j' = g'⁻¹ * (g' * repPerm j' * g'⁻¹) * g' := by group
      _ = _ := by rw [← he]; group
  obtain ⟨i, hi, hpi⟩ := ((cls_spec hj).1 _).1 hmem
  have hshr : RK j' >>> 1024 = 0 := by
    have h := orb_ok j' hj'
    unfold orbK at h
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1.1.1.2
  have heq := pr_inj hpi (rep_facts hj').1 ((cls_spec hj).2.2 i hi) hshr
  have h2 := Orb.allN_iff.1 disj_ok j hj
  have h3 := Orb.allN_iff.1 h2 j' hj'
  simp only [Bool.or_eq_true, Nat.beq_eq_true_eq] at h3
  rcases h3 with h3 | h3
  · exact hne (Nat.eq_of_beq_eq_true h3)
  · have h4 := Orb.allN_iff.1 h3 i hi
    rw [heq] at h4
    simp at h4

theorem card_invol' :
    Nat.card {x : Pg // (x : Equiv.Perm (Fin 128)) * x = 1 ∧ (x : Equiv.Perm (Fin 128)) ≠ 1} =
      10575 := by
  let f : (Σ j : Fin 9, cls j) →
      {x : Pg // (x : Equiv.Perm (Fin 128)) * x = 1 ∧ (x : Equiv.Perm (Fin 128)) ≠ 1} :=
    fun p => ⟨⟨p.2.1, (cls_sub p.1.2 p.2.2).1⟩, (cls_sub p.1.2 p.2.2).2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨j, x, hx⟩ ⟨j', x', hx'⟩ h
      have e : x = x' := congrArg (fun y => ((y.1 : Pg) : Equiv.Perm (Fin 128))) h
      subst e
      have ej : j = j' := Fin.ext (cls_disj j.2 j'.2 hx hx')
      subst ej
      rfl
    · rintro ⟨⟨x, hx⟩, h2, h1⟩
      obtain ⟨j, hj, hxj⟩ := invol_cover hx h1 h2
      exact ⟨⟨⟨j, hj⟩, x, hxj⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_sigma]
  have : ∀ j : Fin 9, Nat.card (cls j) = NC j := fun j => (cls_spec j.2).2.1
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun j => NC j) 9]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  decide

theorem fix_ok : (List.range 9).all (fun j => neOneW [repArrs[j]!] &&
    (fixCntW [repArrs[j]!] == (fpTab[j]!).1) && (fixSqW [repArrs[j]!] == (fpTab[j]!).2)) = true := by
  simp only [neOneW, ← Array.any_toList]
  decide +kernel

theorem cert27821 : repCheck = true ∧ fpDistinct = true ∧ sumCheck = true ∧ centCheck = true ∧
    involCheck = true := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · unfold repCheck
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, fun j hj => ?_⟩
    obtain ⟨-, hrep, hR, hsq, hne⟩ := rep_facts hj
    have hfix := List.all_eq_true.1 fix_ok j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at hfix
    refine ⟨⟨⟨⟨⟨isInvA_of_rep hrep (rep_invCand hrep), ?_⟩, (inPg_iff hrep).2 hR⟩, hfix.1.1⟩,
      hfix.1.2⟩, hfix.2⟩
    exact (eqA_iff (rep_compA hrep hrep) rep_idA).2 hsq
  · unfold centCheck
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    obtain ⟨-, hrep, hR, -, -⟩ := rep_facts hj'
    have h1 : Nat.card {x : Pg // (x : Equiv.Perm (Fin 128)) * repPerm j =
        repPerm j * (x : Equiv.Perm (Fin 128))} = countW (commW repArrs[j]!) blocksPg [] :=
      card_eq_countW_Pg (f := commW repArrs[j]!) (Pr := fun π => π * repPerm j = repPerm j * π)
        fun w g hw hg => commW_iff hrep hR hw hg
    rw [← h1, card_cent' hj']
    exact beq_self_eq_true _
  · unfold involCheck
    have h1 : Nat.card {g : Pg // (g : Equiv.Perm (Fin 128)) * g = 1 ∧
        (g : Equiv.Perm (Fin 128)) ≠ 1} = countW involW blocksPg [] :=
      card_eq_countW_Pg (f := involW) (Pr := fun π => π * π = 1 ∧ π ≠ 1)
        fun w g hw hg => involW_iff hw hg
    rw [← h1, card_invol']
    rfl

end CertificateChecks.KernelPgCls
