module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4G

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4 CFSG.Assembly.LowTwoRank
open scoped Matrix

section Facts

variable (hM : MatFacts) (hc : chkF () = true)
include hM hc

theorem F4_le_M4 : F4 hM hc ≤ CFSG.Quasithin.KGJ4.M4 := by
  rw [F4, eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact fJn_mem j

theorem card_F4 : Nat.card ↥(F4 hM hc) = 2 ^ 10 := card_eSub _

theorem card_F4_subgroupOf :
    Nat.card ↥((F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4) = 2 ^ 10 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F4_le_M4 hM hc)).toEquiv, card_F4]

theorem normal_F4 : ((F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4).Normal := by
  refine ⟨fun f hf x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hf ⊢
  have h := (Subgroup.mem_normalizer_iff.mp (M4_le_eNorm hM hc x.2) f).mp hf
  simpa using h

theorem isPGroup_F4 : IsPGroup 2 ↥(F4 hM hc) := fun g => ⟨1, Subtype.ext (by
  rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
  exact eSub_sq _ _ g.2)⟩

theorem F4_le_ker : (F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4 ≤ (piM4 hM hc).ker := by
  have := isSimpleGroup_statedSL5
  have hn := (normal_F4 hM hc).map (piM4 hM hc) (piM4_surjective hM hc)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ _ hn with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h1 := Nat.card_le_card_of_surjective _
      ((piM4 hM hc).subgroupMap_surjective ((F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4))
    rw [h, Subgroup.card_top, card_statedSL5', card_F4_subgroupOf] at h1
    norm_num at h1

theorem ker_piM4 (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    (piM4 hM hc).ker = (F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4 := by
  have hk : Nat.card ↥(piM4 hM hc).ker = 2 ^ 10 := by
    have h1 := (piM4 hM hc).ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (piM4_surjective hM hc), Subgroup.card_top,
      card_statedSL5', hcard] at h1
    omega
  refine (Subgroup.eq_of_le_of_card_ge (F4_le_ker hM hc) ?_).symm
  rw [hk, card_F4_subgroupOf]

theorem m4_max (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    ∀ K : Subgroup G₀, F4 hM hc ≤ K → K ≤ CFSG.Quasithin.KGJ4.M4 →
      CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer (K : Set G₀) →
      K = F4 hM hc ∨ K = CFSG.Quasithin.KGJ4.M4 := by
  have := isSimpleGroup_statedSL5
  exact simple_of_surj (piM4 hM hc) (piM4_surjective hM hc) (ker_piM4 hM hc hcard)

theorem m4_min : ∀ N : Subgroup G₀, N ≤ F4 hM hc →
    CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer (N : Set G₀) → N = ⊥ ∨ N = F4 hM hc := by
  intro N hNF hMN
  have hb := fJ_basis hM hc
  let W : AddSubgroup (Fin 10 → ZMod 2) :=
    { carrier := {c | eElt fJ c ∈ N}
      zero_mem' := by
        show eElt fJ 0 ∈ N
        rw [eElt_zero]
        exact N.one_mem
      add_mem' := fun {c d} hc' hd' => by
        show eElt fJ (c + d) ∈ N
        rw [eElt_add hb.sq hb.comm]
        exact N.mul_mem hc' hd'
      neg_mem' := fun {c} hc' => by
        show eElt fJ (-c) ∈ N
        have : -c = c := funext fun i => ZMod.neg_eq_self_mod_two (c i)
        rw [this]
        exact hc' }
  have hW : ∀ γ : ↥(StatedSL 5 (ZMod 2)), ∀ v ∈ W, psiMat γ *ᵥ v ∈ W := by
    intro γ v hv
    obtain ⟨x, rfl⟩ := piM4_surjective hM hc γ
    show eElt fJ (psiMat (piM4 hM hc x) *ᵥ v) ∈ N
    rw [← piM4_conj hM hc x v]
    exact (Subgroup.mem_normalizer_iff.mp (hMN x.2) _).mp hv
  rcases psi_irred W hW with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := (mem_eSub_iff hb n).mp (hNF hn)
    have hc0 : c ∈ W := hn
    rw [h, AddSubgroup.mem_bot] at hc0
    rw [hc0, eElt_zero]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hNF fun f hf => ?_
    obtain ⟨c, rfl⟩ := (mem_eSub_iff hb f).mp hf
    have hc1 : c ∈ W := h ▸ AddSubgroup.mem_top c
    exact hc1

theorem m4_CE (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    CFSG.Quasithin.KGJ4.M4 ⊓ Subgroup.centralizer (F4 hM hc : Set G₀) ≤ F4 hM hc := by
  rintro x ⟨hx, hxC⟩
  obtain ⟨h, e⟩ := piM4_pairF hM hc ⟨x, hx⟩
  have h1 : eMat (fJ_basis hM hc) ⟨x, h⟩ = 1 := (eMat_eq_one_iff _ _).mpr hxC
  have h2 : psi (piM4 hM hc ⟨x, hx⟩) = psi 1 := by
    rw [← e, map_one]
    exact Units.ext h1
  have h4 : (⟨x, hx⟩ : ↥CFSG.Quasithin.KGJ4.M4) ∈ (piM4 hM hc).ker := psi_injective h2
  rw [ker_piM4 hM hc hcard, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem not_isPGroup_M4 : ¬ IsPGroup 2 ↥CFSG.Quasithin.KGJ4.M4 := fun h2 => by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h2.of_surjective _ (piM4_surjective hM hc))
  rw [card_statedSL5'] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 9999360)
  have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h4

theorem pCoreOf_M4 (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640) :
    CFSG.Open.pCoreOf 2 CFSG.Quasithin.KGJ4.M4 = F4 hM hc :=
  pCoreOf_eq_of_max (F4_le_M4 hM hc) (M4_le_eNorm hM hc) (isPGroup_F4 hM hc)
    (m4_max hM hc hcard) (not_isPGroup_M4 hM hc)

end Facts

end CFSG.Quasithin.KGC31.J4M4

end
