module

public import CFSG.RankThree.GF2n.Tim79aCitedSp42
public import CFSG.CGT.Timmesfeld75.AltCover
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldExceptional
public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix CFSG.Timmesfeld.ARS.CaseM CFSG.SignalizerFunctorTheorem.NonLocal
  CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Symplectic

theorem sp42CoverLiftStatement_holds :
    CFSG.RankThree.GF2n.Tim79a.Sp42CoverLiftStatement := by
  intro Γ _ _ φ hφ hcen hcom hcard t s v w hv hw hvw _hB htmat hsmat ht2 hs2
  classical
  let K : Subgroup Γ := φ.ker
  let Γ' : Subgroup Γ := commutator Γ
  let G' : Subgroup (StatedSp 2 (GaloisField 2 1)) :=
    commutator (StatedSp 2 (GaloisField 2 1))
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hKΓ' : K ≤ Γ' := hcom
  have hΓ'G' : Γ'.map φ = G' := by
    change (commutator Γ).map φ = commutator (StatedSp 2 (GaloisField 2 1))
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hφ]
    rfl
  have hcardG : Nat.card (StatedSp 2 (GaloisField 2 1)) = 720 := by
    rw [Nat.card_congr (spTwoTwoEquiv hF2).toEquiv,
      CFSG.RankThree.PartOne.KCSpComm.card_sympFour]
  have hcardG' : Nat.card G' = 360 := by
    rw [Nat.card_congr (commutatorSpTwoEquiv hF2).toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    rfl
  have hG'index : G'.index = 2 := by
    have h := G'.card_mul_index
    rw [hcardG', hcardG] at h
    omega
  have hG'normal : G'.Normal := inferInstance
  have hKsub : Nat.card (K.subgroupOf Γ') = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKΓ').toEquiv, hcard]
  have hφrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
  have hcardΓ : Nat.card Γ = 1440 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hcard, hφrange, Subgroup.card_top, hcardG] at h
    omega
  have hψrange : (φ.comp Γ'.subtype).range = G' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hΓ'G']
  have hψker : (φ.comp Γ'.subtype).ker = K.subgroupOf Γ' := by
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype]
  have hcardΓ' : Nat.card Γ' = 720 := by
    have h := Subgroup.card_ker_mul_card_range (φ.comp Γ'.subtype)
    rw [hψker, hKsub, hψrange, hcardG'] at h
    omega
  have hΓ'index : Γ'.index = 2 := by
    have h := Γ'.card_mul_index
    rw [hcardΓ', hcardΓ] at h
    omega
  let ψ : Γ' →* G' :=
    (φ.comp Γ'.subtype).codRestrict G' fun x =>
      hΓ'G'.symm ▸ Subgroup.mem_map_of_mem φ x.2
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : (y : StatedSp 2 (GaloisField 2 1)) ∈ Γ'.map φ := by
      rw [hΓ'G']
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hψker' : ψ.ker = K.subgroupOf Γ' := by
    rw [MonoidHom.ker_codRestrict, hψker]
  have hψker_le : ψ.ker ≤ Subgroup.center Γ' := by
    intro x hx
    rw [hψker'] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcen (Subgroup.mem_subgroupOf.mp hx)) (y : Γ)
  have hG'perf : Group.IsPerfect G' := by
    haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
    exact Group.IsPerfect.ofSurjective
      (f := (commutatorSpTwoEquiv hF2).symm.toMonoidHom)
      (commutatorSpTwoEquiv hF2).symm.surjective
  obtain ⟨hsup, hperfΓ'', hsurjΓ''⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective ψ hψ hψker_le hG'perf
  let Γ'' : Subgroup Γ := ⁅Γ', Γ'⁆
  have hmap_top : (⊤ : Subgroup Γ').map Γ'.subtype = Γ' := by
    simpa using Subgroup.subgroupOf_map_subtype (H := (⊤ : Subgroup Γ)) (K := Γ')
  have hsupΓ : Γ'' ⊔ K = Γ' := by
    have h := congrArg (Subgroup.map Γ'.subtype) hsup
    rw [Subgroup.map_sup, hmap_top, hψker', Subgroup.map_subgroupOf_eq_of_le hKΓ',
      Subgroup.map_subtype_commutator] at h
    exact h
  obtain ⟨zK, hzKne, hzKuniq⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hcard
  let z : Γ := zK.val
  have hzK : z ∈ K := zK.2
  have hz1 : z ≠ 1 := fun h => hzKne (Subtype.ext h)
  have hz2 : z * z = 1 := by
    have h := pow_card_eq_one' (G := K) (x := zK)
    rw [hcard] at h
    simpa [z, pow_two] using congrArg Subtype.val h
  have hzclass : ∀ k : Γ, k ∈ K → k = 1 ∨ k = z := by
    intro k hk
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      have hkK : (⟨k, hk⟩ : K) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (hzKuniq ⟨k, hk⟩ hkK)
  have hKΓ'' : K ≤ Γ'' := by
    by_contra hKle
    have hdisj : Disjoint K Γ'' := by
      rw [Subgroup.disjoint_def]
      intro x hxK hxΓ''
      by_contra hx1
      rcases hzclass x hxK with h | h
      · exact hx1 h
      · exact hKle (fun y hy => by
          rcases hzclass y hy with rfl | rfl
          · exact Γ''.one_mem
          · exact h ▸ hxΓ'')
    have hsub : Γ''.subgroupOf K = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj.symm
    have hrelK : Γ''.relIndex K = 2 := by
      rw [Subgroup.relIndex, hsub, Subgroup.index_bot, hcard]
    have hrel : Γ''.relIndex Γ' = 2 := by
      rw [← hsupΓ, sup_comm, Subgroup.relIndex_sup_right, hrelK]
    have hΓ''le : Γ'' ≤ Γ' := Subgroup.commutator_le_right (H₁ := Γ') (H₂ := Γ')
    have hidx : Γ''.index = 4 := by
      rw [← Subgroup.relIndex_mul_index hΓ''le, hrel, hΓ'index]
    have hcard4 : Nat.card (Γ ⧸ Γ'') = 4 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    haveI : IsMulCommutative (Γ ⧸ Γ'') :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard4]; norm_num)
    have hle : commutator Γ ≤ Γ'' :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Γ'')).mp inferInstance
    exact hKle (hKΓ'.trans hle)
  have hΓ'eq : Γ' = Γ'' := by
    rw [← hsupΓ, sup_eq_left.mpr hKΓ'']
  have hperfΓ' : Group.IsPerfect Γ' := by
    have hEtop : (commutator Γ') = ⊤ := by
      apply Subgroup.map_injective (Subgroup.subtype_injective Γ')
      rw [Subgroup.map_subtype_commutator, hmap_top]
      exact hΓ'eq.symm
    haveI : Group.IsPerfect ↥(commutator Γ') := hperfΓ''
    exact Group.IsPerfect.ofSurjective (f := (commutator Γ').subtype)
      (by rw [← MonoidHom.range_eq_top, Subgroup.range_subtype]; exact hEtop)
  let π : Γ' →* alternatingGroup (Fin 6) :=
    (commutatorSpTwoEquiv hF2).toMonoidHom.comp ψ
  have hπ : Function.Surjective π :=
    (commutatorSpTwoEquiv hF2).surjective.comp hψ
  have hπker : π.ker = K.subgroupOf Γ' := by
    ext x
    change (commutatorSpTwoEquiv hF2) (ψ x) = 1 ↔ (x : Γ) ∈ K
    constructor
    · intro h
      have hψ : ψ x = 1 := (commutatorSpTwoEquiv hF2).map_eq_one_iff.mp h
      rw [← MonoidHom.mem_ker, hψker'] at hψ
      exact Subgroup.mem_subgroupOf.mp hψ
    · intro hx
      have hψ : ψ x = 1 := by
        rw [← MonoidHom.mem_ker, hψker']
        exact Subgroup.mem_subgroupOf.mpr hx
      exact (commutatorSpTwoEquiv hF2).map_eq_one_iff.mpr hψ
  let z' : Γ' := ⟨z, hKΓ' hzK⟩
  have hz'ne : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hz'cen : ∀ x : Γ', x * z' = z' * x := by
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcen hzK) (x : Γ)
  have hkerπ : ∀ x : Γ', π x = 1 ↔ x = 1 ∨ x = z' := by
    intro x
    have hπx : π x = 1 ↔ ψ x = 1 := by
      change (commutatorSpTwoEquiv hF2) (ψ x) = 1 ↔ ψ x = 1
      exact (commutatorSpTwoEquiv hF2).map_eq_one_iff
    have hψx : ψ x = 1 ↔ (x : Γ) ∈ K := by
      rw [← MonoidHom.mem_ker, hψker', Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rcases hzclass (x : Γ) ((hψx.mp (hπx.mp hx))) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact map_one π
      · exact hπx.mpr (hψx.mpr hzK)
  let a : StatedSp 2 (GaloisField 2 1) := φ t
  let b : StatedSp 2 (GaloisField 2 1) := φ s
  have ha_mat : SpExtras.mat 2 (GaloisField 2 1) a = spTrans v 1 := by
    simpa [a, SpExtras.mat_apply, spTrans, spNil, spGram] using htmat
  have hb_mat : SpExtras.mat 2 (GaloisField 2 1) b = spTrans w 1 := by
    simpa [b, SpExtras.mat_apply, spTrans, spNil, spGram] using hsmat
  have ha2 : a * a = 1 := by
    rw [show a = φ t from rfl, ← map_mul, ht2, map_one]
  have hb2 : b * b = 1 := by
    rw [show b = φ s from rfl, ← map_mul, hs2, map_one]
  obtain ⟨A, hA, hAv⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq (m := 2) (K := GaloisField 2 1)
      hv hw
  let Ag : StatedSp 2 (GaloisField 2 1) := ⟨A, hA⟩
  have hconj : Ag * a * Ag⁻¹ = b := by
    apply SpExtras.mat_injective
    rw [CaseM.mat_conj_of_mat_eq (x := a) (v := v) (c := 1) ha_mat Ag,
      show SpExtras.mat 2 (GaloisField 2 1) Ag = (A : Matrix _ _ _) from rfl, hAv, hb_mat]
  have hconj_iff : a ∈ G' ↔ b ∈ G' := by
    constructor
    · intro ha
      have h := hG'normal.conj_mem a ha Ag
      rwa [← hconj]
    · intro hb
      have h := hG'normal.conj_mem b hb Ag⁻¹
      have h' : Ag⁻¹ * b * Ag = a := by
        rw [← hconj]
        group
      rwa [inv_inv, h'] at h
  have hab_mem : a * b ∈ G' := by
    by_cases ha : a ∈ G'
    · exact G'.mul_mem ha (hconj_iff.mp ha)
    · rw [Subgroup.mul_mem_iff_of_index_two hG'index]
      exact iff_of_false ha (fun hb => ha (hconj_iff.mpr hb))
  have hab_ne : a * b ≠ 1 := by
    intro hab
    have ha_eq_b : a = b := by
      calc a = a * (a * b) := by rw [hab, mul_one]
        _ = (a * a) * b := by group
        _ = b := by rw [ha2, one_mul]
    have hmat : spTrans v 1 = spTrans w 1 := by
      rw [← ha_mat, ← hb_mat, ha_eq_b]
    obtain ⟨x, hx⟩ : ∃ x, spForm v x ≠ 0 := by
      by_contra h
      push Not at h
      exact hv ((CFSG.RankThree.SubgroupLists.spForm_nondegenerate (n := 2)
        (K := GaloisField 2 1)).1 v fun y => by
          rw [CFSG.RankThree.SubgroupLists.spForm_eq_dotProduct]
          exact h y)
    have hform : spForm v x • v = spForm w x • w := by
      have h := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
        (GaloisField 2 1) => M *ᵥ x) hmat
      have h' : x + spForm v x • v = x + spForm w x • w := by
        simpa only [CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, one_mul] using h
      exact add_left_cancel h'
    have hv1 : spForm v x = 1 := by
      rcases CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one (spForm v x) with h | h
      · exact absurd h hx
      · exact h
    have hw01 : spForm w x = 0 ∨ spForm w x = 1 :=
      CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one (spForm w x)
    rw [hv1, one_smul] at hform
    rcases hw01 with hw0 | hw1
    · rw [hw0, zero_smul] at hform
      exact hv hform
    · rw [hw1, one_smul] at hform
      exact hvw hform
  have htsΓ' : t * s ∈ Γ' := by
    have hmem : φ (t * s) ∈ Γ'.map φ := by
      rw [hΓ'G']
      simpa [a, b, map_mul] using hab_mem
    obtain ⟨g, hgΓ', hgφ⟩ := Subgroup.mem_map.mp hmem
    have hdiff : g⁻¹ * (t * s) ∈ K := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgφ, inv_mul_cancel]
    have hdiffΓ' : g⁻¹ * (t * s) ∈ Γ' := hKΓ' hdiff
    have h := Γ'.mul_mem hgΓ' hdiffΓ'
    simpa using h
  intro hcomm
  have hts2 : (t * s) * (t * s) = 1 := by
    calc (t * s) * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hcomm]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs2, one_mul]
  let ts' : Γ' := ⟨t * s, htsΓ'⟩
  have hts'2 : ts' * ts' = 1 := Subtype.ext hts2
  have hπts_ne : π ts' ≠ 1 := by
    intro h
    have hψ1 : ψ ts' = 1 := by
      have h' : (commutatorSpTwoEquiv hF2) (ψ ts') = 1 := h
      exact (commutatorSpTwoEquiv hF2).map_eq_one_iff.mp h'
    have hval : (ψ ts' : StatedSp 2 (GaloisField 2 1)) = 1 := by
      simpa using congrArg Subtype.val hψ1
    have hval' : φ (t * s) = 1 := by
      simpa [ψ, ts'] using hval
    have hab1 : a * b = 1 := by
      simpa [a, b, map_mul] using hval'
    exact hab_ne hab1
  have hmem := CFSG.CGT.Timmesfeld75.involution_mem_ker_of_double_cover_six hπ hz'ne hz'2
    hz'cen hkerπ hperfΓ' ts' hts'2
  rcases hmem with h | h
  · exact hπts_ne (by rw [h, map_one])
  · exact hπts_ne (by rw [h]; exact (hkerπ z').mpr (Or.inr rfl))

end CFSG.RankThree.GF2n.Tim79a
