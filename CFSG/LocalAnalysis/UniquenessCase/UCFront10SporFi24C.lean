module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InConj
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoB
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K

open Subgroup CFSG.QuasithinUnique CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi24
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi24Phi_range : fi24Phi.range = fi24P := by
  have hφa : fi24Phi ⟨fi24Sa, fi24Sa_mem⟩ = fi24Pa :=
    Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_a j)
  have hφb : fi24Phi ⟨fi24Sb, fi24Sb_mem⟩ = fi24Pb :=
    Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_b j)
  have htop : (⊤ : Subgroup ↥fi24K) =
      Subgroup.closure {⟨fi24Sa, fi24Sa_mem⟩, ⟨fi24Sb, fi24Sb_mem⟩} := by
    apply Subgroup.map_injective fi24K.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure]
    rw [show fi24K.subtype '' {⟨fi24Sa, fi24Sa_mem⟩, ⟨fi24Sb, fi24Sb_mem⟩} =
        ({fi24Sa, fi24Sb} : Set (Equiv.Perm (Fin 504))) from by
      ext x
      simp]
    exact fi24K_eq
  rw [← Subgroup.map_top (f := fi24Phi), htop, MonoidHom.map_closure, fi24P_eq]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · exact Or.inl hφa
    · exact Or.inr hφb
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, hφa⟩
    · exact ⟨_, Or.inr rfl, hφb⟩

theorem k105In_centralizer_fi24z_of
    (hL : ∀ S H : Subgroup ↥CFSG.Sporadic.FischerOddCore.fi24P, IsSylowTwoOf S ⊤ → S ≤ H →
      Group.IsSolvable ↥H → ¬ 3 ∣ Nat.card ↥H → H ≤ S) :
    K105In (Subgroup.centralizer {fi24z}) fi24T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ' : ↥fi24C →* ↥fi24K := fi24Rho.codRestrict fi24K fun c => by
    rw [← fi24Rho_range_card.1]
    exact ⟨c, rfl⟩
  have hρ's : Function.Surjective ρ' := by
    intro k
    have hk : (k : Equiv.Perm (Fin 504)) ∈ fi24Rho.range := by
      rw [fi24Rho_range_card.1]
      exact k.2
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, Subtype.ext hc⟩
  let ψ : ↥fi24C →* ↥fi24P := (fi24Phi.comp ρ').codRestrict fi24P fun c => by
    rw [← fi24Phi_range]
    exact ⟨ρ' c, rfl⟩
  have hψs : Function.Surjective ψ := by
    intro p
    have hp : (p : Equiv.Perm (Fin 378)) ∈ fi24Phi.range := by
      rw [fi24Phi_range]
      exact p.2
    obtain ⟨k, hk⟩ := hp
    obtain ⟨c, hc⟩ := hρ's k
    refine ⟨c, Subtype.ext ?_⟩
    change fi24Phi (ρ' c) = (p : Equiv.Perm (Fin 378))
    rw [hc, hk]
  have hcardψ : Nat.card ψ.ker = 8192 := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψs
    rw [card_fi24P, (fi24R2_centralizer_structure).1] at h
    have h' : Nat.card ψ.ker * 19595520 = 8192 * 19595520 := by
      rw [h]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hψP : IsPGroup 2 ψ.ker :=
    IsPGroup.of_card (n := 13) (by rw [hcardψ]; norm_num)
  obtain ⟨P₀, hNleP₀⟩ := hψP.exists_le_sylow
  let T₂ : Subgroup J := P₀.map fi24C.subtype
  have hT₂le : T₂ ≤ fi24C := Subgroup.map_subtype_le _
  have hCindex : Odd fi24C.index := by
    have h := Subgroup.card_mul_index fi24C
    rw [(fi24R2_centralizer_structure).1, card_J] at h
    have hC : 160526499840 = 2 ^ 21 * 76545 := by norm_num
    have hJ : 1255205709190661721292800 = 2 ^ 21 * 598528723330813275 := by norm_num
    rw [hC, hJ, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ 21 by norm_num) h
    have hNodd : Odd (76545 * fi24C.index) := h' ▸ (by norm_num)
    exact Nat.Odd.of_mul_right hNodd
  have hT₂ : IsSylowTwoOf T₂ ⊤ := by
    refine ⟨le_top, P₀.isPGroup'.map fi24C.subtype, ?_⟩
    change ¬ 2 ∣ T₂.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    change ¬ 2 ∣ (P₀.map fi24C.subtype).index
    rw [Subgroup.index_map_subtype]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h' | h'
    · exact P₀.not_dvd_index h'
    · exact hCindex.not_two_dvd_nat h'
  have hiT₂ : ¬ 2 ∣ T₂.index := by
    have h := hT₂.2.2
    change ¬ 2 ∣ T₂.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hC0 : K105In fi24C T₂ :=
    k105In_of_quotient hT₂ hT₂le ψ.ker (Subgroup.map_mono hNleP₀)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) hL
  obtain ⟨g, hg⟩ := isConj_iff.1 isConj_fi24R2_fi24z
  have hCg : fi24C.map (MulAut.conj g).toMonoidHom = Subgroup.centralizer {fi24z} := by
    rw [← centralizer_conj g fi24R2, hg]
  have hmapC := hC0.map_mulEquiv (MulAut.conj g)
  rw [hCg] at hmapC
  refine hmapC.of_isSylowTwoOf ?_ ?_ ?_ isSylowTwoOf_fi24T
  · rw [← hCg]
    exact Subgroup.map_mono hT₂le
  · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (comm_fi24z hs)
  · refine ⟨le_top, hT₂.2.1.map (MulAut.conj g).toMonoidHom, ?_⟩
    change ¬ 2 ∣ (T₂.map (MulAut.conj g).toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right,
      Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).bijective]
    exact hiT₂

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K
