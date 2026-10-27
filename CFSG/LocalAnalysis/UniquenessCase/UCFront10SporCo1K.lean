module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1KChi
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.Certificates.Kernel.SporLatDc2Sound
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1J

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.Cover CFSG.Blueprint
  CFSG.QuasithinUnique CFSG.KC.SLD2 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.EvenSporadicStandard.TwoCo1 (epsMask eMaskA)
open CFSG.KD.Co1K105 (letterOK)
open CFSG.Sporadic.Co1Schreier.Native (Rows)

theorem le_of_overgroups_sylow {L : Type} [Group L] [Finite L] {S₀ : Subgroup L}
    (hS₀ : IsSylowTwoOf S₀ ⊤) (h : ∀ Z : Subgroup L, S₀ ≤ Z → Z = S₀ ∨ 3 ∣ Nat.card Z)
    (S H : Subgroup L) (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) (h3 : ¬ 3 ∣ Nat.card H) :
    H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨hp₀, hi₀⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S₀ = S.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 L => (T : Subgroup L)) hg).symm
  have hle : S₀ ≤ H.map (MulAut.conj g).toMonoidHom := by
    rw [hST]
    exact Subgroup.map_mono hSH
  rcases h _ hle with he | h3'
  · rw [hST] at he
    exact (Subgroup.map_injective (MulAut.conj g).injective he).le
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h3'
    exact absurd h3' h3

theorem sep_eq : CFSG.KD.Co1K105.D.sep = (List.range 8).map (2 ^ ·) := rfl

section


theorem epsA_mem_co1Sylow : epsMask eMaskA ∈ co1Sylow := by
  rw [epsMask]
  exact epsHom_range_le_co1Sylow ⟨_, rfl⟩


theorem co1Sylow_le_Cz : co1Sylow ≤ Cz := by
  rintro _ ⟨s, hs, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (theta_mul_epsMask_eMaskA (s := s) hs)


@[expose] def gC (l : ℕ) : Cz := ⟨sGen l, co1Sylow_le_Cz (sGen_mem l)⟩

abbrev sylC : Subgroup Cz := Subgroup.closure (gC '' {l | l < 15})

theorem map_sylC : sylC.map Cz.subtype = co1Sylow := by
  rw [MonoidHom.map_closure, Set.image_image]
  exact closure_sGen

theorem card_sylC : Nat.card sylC = 2 ^ 21 := by
  rw [← Subgroup.card_map_of_injective Cz.subtype_injective, map_sylC, card_co1Sylow]

theorem zC_mem_sylC : zC ∈ sylC :=
  (Subgroup.mem_map_iff_mem Cz.subtype_injective).1 (by
    rw [map_sylC, Subgroup.coe_subtype, coe_zC]
    exact epsA_mem_co1Sylow)

@[expose] def xL (l : ℕ) : cA :=
  if l < 15 then chiC (gC l)
  else if l = 15 then
    ⟨bG 0 * bG 7 * bG 4, cA.mul_mem (cA.mul_mem (bG_mem 0) (bG_mem 7)) (bG_mem 4)⟩
  else ⟨bG 0, bG_mem 0⟩

theorem letter_xL {l : ℕ} (hl : l < 17) : ∃ R : Rows, MRep R (xL l : GL24) ∧
    letterOK Native.one qArr CFSG.KD.Co1K105.L l R = true := by
  have hP := letters_parts
  unfold xL
  split_ifs with h15 h16
  · rw [chiC_val]
    show ∃ R : Rows, MRep R (conjC (sGen l)) ∧
      letterOK Native.one qArr CFSG.KD.Co1K105.L l R = true
    unfold sGen
    split_ifs with h11 h4
    · exact ⟨_, rep_conjC (rep_co1MatEquiv (matHom_eps0 ⟨l, h11⟩)), hP.2.2.2.2.1 l h11⟩
    · have h := hP.2.2.2.2.2.1 (l - 11) h4
      rw [show 11 + (l - 11) = l by omega] at h
      exact ⟨_, rep_conjC (mrep_t24Gen ⟨l - 11, h4⟩), h⟩
    · omega
  · subst h16
    exact ⟨_, ((rep_bray 0).mul (rep_bray 7)).mul (rep_bray 4), hP.2.2.2.2.2.2.1⟩
  · obtain rfl : l = 16 := by omega
    exact ⟨_, rep_bray 0, hP.2.2.2.2.2.2.2⟩

end

theorem orderOf_zC :
    orderOf zC = 2 := by
  rw [← orderOf_injective chiC chiC_injective zC, chiC_zC, aC, Subgroup.orderOf_mk, orderOf_aG]


theorem card_range_eq : Nat.card qHom.range =
    CFSG.KD.Co1K105.C.N1 * CFSG.KD.Co1K105.C.N2 * 2 ^ CFSG.KD.Co1K105.C.k := by
  rw [card_range_qHom]
  show 44590694400 = 135 * 315 * 2 ^ 20
  norm_num

theorem sep_ok : ∀ g : qHom.range, (∀ p ∈ CFSG.KD.Co1K105.D.sep, act 512 g p = p) → g = 1 := by
  rintro ⟨_, x, rfl⟩ hg
  refine Subtype.ext (qHom_eq_one_of_fix fun i ⟨j, hj, hi⟩ => Fin.ext ?_)
  have hp : (i : ℕ) ∈ CFSG.KD.Co1K105.D.sep := by
    rw [sep_eq, hi]
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have e : act 512 (⟨qHom x, x, rfl⟩ : qHom.range) i = ((qHom x i : Fin 512) : ℕ) :=
    act_eq _ i
  exact e.symm.trans (hg i hp)


@[expose] def psi : Cz →* qHom.range := qHom.rangeRestrict.comp chiC

theorem psi_surjective : Function.Surjective psi :=
  qHom.rangeRestrict_surjective.comp chiC_surjective

theorem ker_psi : psi.ker = Subgroup.zpowers zC := by
  rw [psi, ← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict, ker_qHom, ← chiC_zC,
    ← MonoidHom.map_zpowers, Subgroup.comap_map_eq_self_of_injective chiC_injective]


theorem card_map_psi : Nat.card (sylC.map psi) = 2 ^ 20 := by
  have h := Subgroup.card_ker_mul_card_range (psi.domRestrict sylC)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, ker_psi, card_sylC] at h
  have hk : Nat.card ((Subgroup.zpowers zC).subgroupOf sylC) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 zC_mem_sylC)).toEquiv,
      Nat.card_zpowers, orderOf_zC]
  rw [hk, show (2 : ℕ) ^ 21 = 2 * 2 ^ 20 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

@[expose] def els : List qHom.range := (List.range 17).map fun l => qHom.rangeRestrict (xL l)

theorem els_length : els.length = CFSG.KD.Co1K105.C.nl := by
  show els.length = 17
  simp [els]

theorem els_getD {l : ℕ} (hl : l < 17) : els.getD l 1 = qHom.rangeRestrict (xL l) := by
  have hl' : l < els.length := by simpa [els] using hl
  rw [List.getD_eq_getElem _ _ hl']
  simp [els]

theorem act_els {l : ℕ} (hl : l < 17) {p : ℕ} (hp : p < 512) :
    act 512 (els.getD l 1) p = CFSG.KD.Co1K105.L l p := by
  obtain ⟨R, hR, hok⟩ := letter_xL hl
  rw [els_getD hl]
  exact (act_eq (qHom.rangeRestrict (xL l)) ⟨p, hp⟩).trans (qHom_letter hR hok ⟨p, hp⟩).1

theorem good_els : ∀ l < CFSG.KD.Co1K105.C.nl,
    CFSG.KC.E64F.Good 512 (tab 512 (els.getD l 1)).toArray (CFSG.KD.Co1K105.C.L l) := by
  intro l hl
  have hl17 : l < 17 := hl
  refine ⟨by rw [tab, List.size_toArray, List.length_map, List.length_finRange], fun p hp => ?_⟩
  have e1 : (tab 512 (els.getD l 1)).toArray.getD p 0 = act 512 (els.getD l 1) p := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
    rfl
  have h := act_lt (els.getD l 1) hp
  rw [act_els hl17 hp] at h
  rw [e1, act_els hl17 hp]
  exact ⟨rfl, h⟩

theorem els_take : els.take CFSG.KD.Co1K105.C.ns = (List.range 15).map fun l => psi (gC l) := by
  show ((List.range 17).map fun l => qHom.rangeRestrict (xL l)).take 15 = _
  rw [← List.map_take, List.take_range, show min 15 17 = 15 from rfl]
  refine List.map_congr_left fun l hl => ?_
  show qHom.rangeRestrict (xL l) = qHom.rangeRestrict (chiC (gC l))
  rw [xL, if_pos (List.mem_range.1 hl)]

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns}) =
    2 ^ CFSG.KD.Co1K105.C.k := by
  have e : Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns} = sylC.map psi := by
    rw [els_take, MonoidHom.map_closure, Set.image_image]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range, Set.mem_image]
  rw [e, card_map_psi, show CFSG.KD.Co1K105.C.k = 20 from rfl]

theorem isSylowTwoOf_S :
    IsSylowTwoOf (Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns}) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card card_S, ?_⟩
  rw [show ((Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns}).subgroupOf ⊤).index =
    (Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns}).index from
    Subgroup.relIndex_top_right _]
  have hi := Subgroup.card_mul_index (Subgroup.closure {x | x ∈ els.take CFSG.KD.Co1K105.C.ns})
  rw [card_S, card_range_eq, mul_comm (CFSG.KD.Co1K105.C.N1 * CFSG.KD.Co1K105.C.N2)] at hi
  rw [Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hi]
  show ¬ 2 ∣ 135 * 315
  norm_num

theorem k105In_centralizer_epsA :
    K105In (Subgroup.centralizer {epsMask eMaskA}) co1Sylow := by
  have hsound := dc2Check_sound (n := 512) CFSG.KD.Co1K105.C rfl CFSG.KD.Co1K105.D els
    els_length good_els card_S card_range_eq sep_ok (Certificates.certificate10507).2
  refine k105In_of_quotient isSylowTwoOf_co1Sylow co1Sylow_le_Cz psi.ker ?_
    (QuotientGroup.quotientKerEquivOfSurjective psi psi_surjective)
    fun S H hS hSH _ h3 => le_of_overgroups_sylow isSylowTwoOf_S hsound S H hS hSH h3
  rw [ker_psi, MonoidHom.map_zpowers, Subgroup.coe_subtype, coe_zC]
  exact Subgroup.zpowers_le.2 epsA_mem_co1Sylow

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
