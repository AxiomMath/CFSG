module

public import CFSG.Quasithin.H13.VolIC113d1
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem card_sl2_nine [Fact (Nat.Prime 3)] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)) = 720 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem exists_sl2_nine_alt6 [Fact (Nat.Prime 3)] :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2) →* alternatingGroup (Fin 6),
      Function.Surjective ψ ∧
        ψ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)) := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) hcard
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem mem_center_of_sq_eq_one {k : Type} [Field k] (hk : ringChar k ≠ 2)
    {g : Matrix.SpecialLinearGroup (Fin 2) k} (hg : g * g = 1) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hsq : (g : Matrix (Fin 2) (Fin 2) k) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one h2 g.2 hsq with h | h
  · refine ⟨1, one_pow _, ?_⟩
    rw [h, map_one]
  · refine ⟨-1, by rw [Fintype.card_fin]; norm_num, ?_⟩
    rw [h, map_neg, map_one]

@[expose] def a6t : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a6t_five : (a6t : Perm (Fin 6)) 5 = 5 := by decide

theorem a6t_sq : a6t * a6t = 1 := by decide

theorem a6t_ne_one : a6t ≠ 1 := by decide

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem pCoreOf_le_centralizer_of_alt6 (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h6 : IsAltBlockType L 6) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, α, hA⟩ := h6
  have hN : ((blockU L).subgroupOf L).Normal := blockU_subgroupOf_normal hL
  obtain ⟨ρ, hρs, hkerc, hker2, hker_mk, hρα⟩ := exists_quotient_hom hL α hA.1 hA.2.1
  obtain ⟨ψ, hψs, hψk⟩ := exists_sl2_nine_alt6
  have hk : ringChar (GaloisField 3 2) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 2) 3]
    norm_num
  obtain ⟨β, hβ, hβs⟩ := exists_surj_lift hk ρ hρs hkerc hker2 (no2_quotient hL) ψ hψs
  have hβx : ∀ g, ρ (β g) = ψ g := fun g => DFunLike.congr_fun hβ g
  have hcardE : Nat.card (↥L ⧸ (blockU L).subgroupOf L) = 360 * Nat.card ρ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv] at h1
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
    rw [h360] at h1
    exact h1
  have hle : Nat.card (↥L ⧸ (blockU L).subgroupOf L) ≤ 720 :=
    card_sl2_nine ▸ Nat.card_le_card_of_surjective β hβs
  obtain ⟨j, hj⟩ := hker2.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hcardE, hj] at hle
    omega
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnQ : n ∈ blockQ L := hn
  have hnL : n ∈ L := C1.blockQ_le L hnQ
  have hU : ∀ u ∈ blockU L, u * q = q * u := fun u hu =>
    (pCoreOf_comm_blockU hL hT hTN hq hu).symm
  interval_cases j
  ·
    have hmk : ((⟨n, hnL⟩ : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) ∈ ρ.ker := (hker_mk _).2 hnQ
    have h1 : ((⟨n, hnL⟩ : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) = 1 := by
      have hbot : ρ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
      rw [hbot] at hmk
      exact hmk
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hU n h1
  ·
    have hE : Nat.card (↥L ⧸ (blockU L).subgroupOf L) = 720 := by rw [hcardE, hj]; norm_num
    have hβi : Function.Injective β :=
      ((Nat.bijective_iff_surjective_and_card β).2 ⟨hβs, by rw [card_sl2_nine, hE]⟩).1
    obtain ⟨g, hg⟩ := hψs a6t
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (β g)
    have hαl : α l = a6t := by rw [← hρα, hl, hβx, hg]
    have hl2Q : ((l ^ 2 : ↥L) : G) ∈ blockQ L := by
      rw [← hker_mk, MonoidHom.mem_ker, hρα, map_pow, hαl, sq, a6t_sq]
    have hl2U : ((l ^ 2 : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) ≠ 1 := by
      intro h
      rw [QuotientGroup.mk_pow, hl, ← map_pow] at h
      have hg2 : g ^ 2 = 1 := hβi (h.trans (map_one β).symm)
      have hgc := mem_center_of_sq_eq_one hk (by rw [← sq]; exact hg2)
      rw [← hψk, MonoidHom.mem_ker, hg] at hgc
      exact a6t_ne_one hgc
    have hql : ((l ^ 2 : ↥L) : G) * q = q * ((l ^ 2 : ↥L) : G) := by
      set c := q * (l : G) * q⁻¹ * (l : G)⁻¹ with hc
      have hcU : c ∈ blockU L := commutator_mem_blockU hL hTN hq l.2
      have hc2 : c * c = 1 := by rw [← sq]; exact C1.blockU_sq hL c hcU
      have hlc : (l : G) * c * (l : G)⁻¹ ∈ blockU L := AppC.conj_mem_blockU l.2 hcU
      have hcomm : c * ((l : G) * c * (l : G)⁻¹) = ((l : G) * c * (l : G)⁻¹) * c :=
        AppC.blockU_comm_blockU hL hcU hlc
      have hkey : q * ((l ^ 2 : ↥L) : G) * q⁻¹ * ((l ^ 2 : ↥L) : G)⁻¹ =
          (l : G) * c * (l : G)⁻¹ * c⁻¹ := by
        have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
        rw [Subgroup.coe_pow, sq, hcinv, ← hcomm]
        calc q * ((l : G) * (l : G)) * q⁻¹ * ((l : G) * (l : G))⁻¹ =
            (q * (l : G) * q⁻¹ * (l : G)⁻¹) * ((l : G) * (q * (l : G) * q⁻¹ * (l : G)⁻¹) *
              (l : G)⁻¹) := by group
          _ = c * ((l : G) * c * (l : G)⁻¹) := by rw [hc]
      have hz := comm_mem_blockZ hL hT hTN hq hl2Q
      rw [hkey] at hz
      have h1 := comm_eq_one_of_fix_five hL hA (l := l) (by rw [hαl]; exact a6t_five) hcU hz
      rw [← hkey] at h1
      calc ((l ^ 2 : ↥L) : G) * q =
          (q * ((l ^ 2 : ↥L) : G) * q⁻¹ * ((l ^ 2 : ↥L) : G)⁻¹)⁻¹ * (q * ((l ^ 2 : ↥L) : G)) := by
            group
        _ = q * ((l ^ 2 : ↥L) : G) := by rw [h1, inv_one, one_mul]
    have hnker : ((⟨n, hnL⟩ : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) ∈ ρ.ker := (hker_mk _).2 hnQ
    have hl2ker : ((l ^ 2 : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) ∈ ρ.ker := (hker_mk _).2 hl2Q
    have htwo : ∀ a ∈ ρ.ker, a = 1 ∨ a = ((l ^ 2 : ↥L) : ↥L ⧸ (blockU L).subgroupOf L) := by
      intro a ha
      by_contra hne
      push Not at hne
      have : Fintype ρ.ker := Fintype.ofFinite _
      have h3 : 3 ≤ Nat.card ρ.ker := by
        have hs : ({⟨1, one_mem _⟩, ⟨_, hl2ker⟩, ⟨a, ha⟩} : Finset ρ.ker).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; exact hne.2 (congrArg Subtype.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hl2U (congrArg Subtype.val h).symm,
              fun h => hne.1 (congrArg Subtype.val h).symm⟩
        rw [← hs, Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
      rw [hj] at h3
      omega
    rcases htwo _ hnker with h1 | h1
    · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact hU n h1
    · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      set u' := ((⟨n, hnL⟩ : ↥L)⁻¹ * l ^ 2 : ↥L) with hu'
      have hu'U : (u' : G) ∈ blockU L := h1
      have hn' : n = ((l ^ 2 : ↥L) : G) * (u' : G)⁻¹ := by
        rw [hu']
        simp
      rw [hn']
      have hu'q : (u' : G)⁻¹ * q = q * (u' : G)⁻¹ := hU _ (inv_mem hu'U)
      calc ((l ^ 2 : ↥L) : G) * (u' : G)⁻¹ * q = ((l ^ 2 : ↥L) : G) * ((u' : G)⁻¹ * q) := by
            rw [mul_assoc]
        _ = ((l ^ 2 : ↥L) : G) * (q * (u' : G)⁻¹) := by rw [hu'q]
        _ = (((l ^ 2 : ↥L) : G) * q) * (u' : G)⁻¹ := by rw [mul_assoc]
        _ = q * (((l ^ 2 : ↥L) : G) * (u' : G)⁻¹) := by rw [hql, mul_assoc]

end CFSG.Quasithin.H13.VolI
