module

public import CFSG.Sporadic.Ly.IndexNineA11
public import CFSG.Sporadic.Schreier.LyGeneration
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.Sporadic.Ly

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.LySchreier

section

noncomputable abbrev lyCcover : Subgroup ↥CFSG.Sporadic.Ly.J := CFSG.Sporadic.LySchreier.lyC

noncomputable abbrev lyCz : Subgroup ↥CFSG.Sporadic.Ly.J :=
  Subgroup.centralizer {CFSG.Sporadic.LySchreier.lyz}

private theorem lyCs_eq_lyCz : lyCcover = lyCz := by
  show CFSG.Sporadic.LySchreier.lyC =
    Subgroup.centralizer {CFSG.Sporadic.LySchreier.lyz}
  exact CFSG.Sporadic.LySchreier.full_involution_centralizer.1

noncomputable def lyCzToCs (x : ↥lyCz) : ↥lyCcover :=
  ⟨x.1, by rw [lyCs_eq_lyCz]; exact x.2⟩

noncomputable def lyCzToCsHom : ↥lyCz →* ↥lyCcover where
  toFun := lyCzToCs
  map_one' := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

private theorem lyCzToCs_surjective : Function.Surjective lyCzToCsHom := by
  intro y
  exact ⟨⟨y.1, lyCs_eq_lyCz ▸ y.2⟩, Subtype.ext rfl⟩

noncomputable abbrev lyPi0 : ↥lyCcover →* ↥(alternatingGroup (Fin 11)) :=
  CFSG.Sporadic.LySchreier.lyCoverEquiv.toMonoidHom.comp
    (QuotientGroup.mk' CFSG.Sporadic.LySchreier.zGroup)

noncomputable abbrev lyPiC : ↥lyCz →* ↥(alternatingGroup (Fin 11)) :=
  lyPi0.comp lyCzToCsHom

private theorem lyZGroupCard : Nat.card CFSG.Sporadic.LySchreier.zGroup = 2 := by
  rw [CFSG.Sporadic.LySchreier.zGroup, Nat.card_zpowers,
    CFSG.Sporadic.LySchreier.orderOf_zC]

private theorem imgC_eq_lyPi0 (x : ↥lyCcover) :
    CFSG.Sporadic.LySchreier.imgC x = (lyPi0 x : Equiv.Perm (Fin 11)) := rfl

private theorem lyPi0_ker : lyPi0.ker = CFSG.Sporadic.LySchreier.zGroup := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [← CFSG.Sporadic.LySchreier.imgC_eq_one_iff, imgC_eq_lyPi0]
    exact congrArg Subtype.val hx
  · intro hx
    have h := (CFSG.Sporadic.LySchreier.imgC_eq_one_iff x).mpr hx
    rw [imgC_eq_lyPi0] at h
    exact Subtype.ext (by simpa using h)

private theorem lyPiC_ker :
    lyPiC.ker = CFSG.Sporadic.LySchreier.zGroup.comap lyCzToCsHom := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap,
    ← MonoidHom.mem_ker, lyPi0_ker]

private theorem lyPi0_surjective : Function.Surjective lyPi0 :=
  CFSG.Sporadic.LySchreier.lyCoverEquiv.surjective.comp
    (QuotientGroup.mk'_surjective CFSG.Sporadic.LySchreier.zGroup)

private theorem lyPiC_surjective : Function.Surjective lyPiC :=
  lyPi0_surjective.comp lyCzToCs_surjective

private theorem lyPiC_isPGroup : IsPGroup 2 lyPiC.ker := by
  rw [lyPiC_ker]
  have hdvd : Nat.card ↥(CFSG.Sporadic.LySchreier.zGroup.comap lyCzToCsHom) ∣ 2 := by
    have h := Subgroup.card_comap_dvd_of_injective CFSG.Sporadic.LySchreier.zGroup
      lyCzToCsHom (by
        intro x y h
        exact Subtype.ext (congrArg (fun z : ↥lyCcover => (z : ↥J)) h))
    simpa [lyZGroupCard] using h
  have hdvd' : Nat.card ↥(CFSG.Sporadic.LySchreier.zGroup.comap lyCzToCsHom) ∣ 2 ^ 1 := by
    rw [pow_one]
    exact hdvd
  obtain ⟨k, -, hk⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 1) Nat.prime_two).mp hdvd'

  exact IsPGroup.of_card (G := ↥(CFSG.Sporadic.LySchreier.zGroup.comap lyCzToCsHom))
    (p := 2) (n := k) hk

private theorem lyS_isSylow : CFSG.QuasithinUnique.IsSylowTwoOf
    CFSG.Sporadic.LySchreier.lyS ⊤ := by
  refine CFSG.QuasithinUnique.isSylowTwoOf_of_card_eq le_top ?_ ?_
  · exact IsPGroup.of_card (n := 8) (by rw [CFSG.Sporadic.LySchreier.card_lyS]; norm_num)
  · have hfac : (51765179004000000 : ℕ).factorization 2 = 8 := by
      simpa [card_J] using CFSG.Sporadic.LySchreier.card_J_factorization
    rw [CFSG.QuasithinUnique.twoPart, Subgroup.card_top, card_J,
      hfac, show (2 : ℕ) ^ 8 = 256 by norm_num]
    exact CFSG.Sporadic.LySchreier.card_lyS

private theorem lyCenter_characterization :
    ∀ x ∈ lyS, (∀ p ∈ lyS, x * p = p * x) → x = 1 ∨ x = lyz := by
  intro x hx hc
  have hcen : (⟨x, hx⟩ : lyS) ∈ Subgroup.center lyS := by
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (hc p p.2).symm
  rw [center_lyS, mem_zpowers_zS] at hcen
  rcases hcen with h | h
  · left
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_one] at h'
    exact h'
  · right
    exact congrArg Subtype.val h

private theorem lyS_map_eq {α : ↥J ≃* ↥J}
    (hα : lyS.map (α : ↥J →* ↥J) = lyS) :
    α lyz = lyz :=
  CFSG.LocalAnalysis.WeakClosure81.apply_eq_of_center_eq_pair
    lyz_mem_lyS lyz_ne_one (fun p hp => (lyz_comm_S p hp).symm)
    lyCenter_characterization hα

private theorem alt_no_normal_two :
    ∀ N : Subgroup ↥(alternatingGroup (Fin 11)), N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
  intro N hN h2
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (↥(alternatingGroup (Fin 11))) _ (alternatingGroup.isSimpleGroup (α := Fin 11)
      (by norm_num)) N hN with h | h
  · exact h
  · exfalso
    rw [h] at h2
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hcard : Nat.card (⊤ : Subgroup ↥(alternatingGroup (Fin 11))) = 19958400 := by
      rw [Subgroup.card_top, card_alternating_eleven]
    rw [hcard] at hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]; norm_num
    have h32 : ¬ (3 : ℕ) ∣ 2 := by norm_num
    exact h32 (Nat.Prime.dvd_of_dvd_pow (p := 3) (m := 2) (n := k) (by norm_num) h3)

private theorem lyCz_map_of_aut {α : ↥J ≃* ↥J}
    (hα : lyS.map (α : ↥J →* ↥J) = lyS) :
    lyCz.map (α : ↥J →* ↥J) = lyCz ∧
      (lyPiC.ker.map lyCz.subtype).map (α : ↥J →* ↥J) =
        lyPiC.ker.map lyCz.subtype := by
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.char_of_centralizer
    (z := lyz) ?_ lyPiC lyPiC_surjective lyPiC_isPGroup alt_no_normal_two α hα
  intro β hβ
  exact lyS_map_eq (α := β) hβ

theorem ly_index_nine_package :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IndexNinePackage ↥CFSG.Sporadic.Ly.J := by
  have hUC : lyS ≤ lyCz := by
    rw [lyCz, ← full_involution_centralizer.1]
    exact lyS_le_lyC
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.indexNinePackage_of_char_quotient
    (Γ := ↥CFSG.Sporadic.Ly.J) (Δ := ↥(alternatingGroup (Fin 11)))
    (U := lyS) (C := lyCz) lyS_isSylow hUC lyPiC lyPiC_surjective lyPiC_isPGroup
    (fun α hα => lyCz_map_of_aut hα) lyA11_index_nine_package

end

end CFSG.Sporadic.Ly
