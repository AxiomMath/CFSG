module

public import CFSG.Quasithin.EmptyFaithful.SzF53Defs
public import CFSG.Quasithin.EmptyFaithful.S152FinShape
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace SzF53A1

theorem not_exists_surj_perm5_perm3 :
    ¬ ∃ f : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 3), Function.Surjective f := by
  rintro ⟨f, hf⟩
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA : (alternatingGroup (Fin 5)).index = 2 := alternatingGroup.index_eq_two
  have h3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.comp (alternatingGroup (Fin 5)).subtype).ker
    with h | h
  · have hinj : Function.Injective (f.comp (alternatingGroup (Fin 5)).subtype) :=
      (MonoidHom.ker_eq_bot_iff _).mp h
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 := (alternatingGroup (Fin 5)).card_mul_index
    rw [hA, S152Fin.card_Perm_five] at h2
    rw [h3] at h1
    omega
  · have hle : alternatingGroup (Fin 5) ≤ f.ker := fun x hx => by
      have hx' : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈
          (f.comp (alternatingGroup (Fin 5)).subtype).ker := by
        rw [h]; exact Subgroup.mem_top _
      exact hx'
    have h1 := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top, hA, h3] at h1
    omega

variable {G : Type} [Group G]

theorem index_pCoreOf_eq {H : Subgroup G} (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) :
    ((pCoreOf 2 H).subgroupOf H).index = 120 := by
  obtain ⟨ι⟩ := hq
  have h := S152Fin.card_OTwoQuot H
  rw [Nat.card_congr ι.toEquiv, S152Fin.card_Perm_five] at h
  exact h.symm

theorem subgroupOf_pCoreOf_le [Finite G] {H U L N : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) : (pCoreOf 2 H).subgroupOf H ≤ (cSecIn H L N).subgroupOf H :=
  fun _ hx => S152Fin.pCoreOf_le_cSecIn hU hs hx

theorem index_cSecIn_dvd [Finite G] {H U L N : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) : ((cSecIn H L N).subgroupOf H).index ∣ 120 := by
  have h := Subgroup.index_dvd_of_le (subgroupOf_pCoreOf_le hU hs)
  rwa [index_pCoreOf_eq hq] at h

theorem not_quotIsoWith_perm3 [Finite G] {H U L N J : Subgroup G} {Y : Type*} [Group Y]
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N)
    (h : QuotIsoWith H (cSecIn H L N) J (Equiv.Perm (Fin 3)) Y) : False := by
  obtain ⟨ι⟩ := hq
  obtain ⟨φ, hφ, hker, -⟩ := h
  have hle : CFSG.Open.pCore 2 ↥H ≤ φ.ker := by
    rw [hker, ← S152Fin.pCoreOf_subgroupOf]
    exact subgroupOf_pCoreOf_le hU hs
  let ψ : OTwoQuot H →* Equiv.Perm (Fin 3) := QuotientGroup.lift (CFSG.Open.pCore 2 ↥H) φ hle
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact not_exists_surj_perm5_perm3 ⟨ψ.comp ι.symm.toMonoidHom, hψ.comp ι.symm.surjective⟩

theorem shape_five [Finite G] {H U L N : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) (hshape : ChiefFactorShape H L N) :
    cSecIn H L N = pCoreOf 2 H ∧
      QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
      ∃ _ : (L.subgroupOf N).Normal, NaturalSn 5 H L N := by
  have hdvd := index_cSecIn_dvd hq hU hs
  obtain ⟨hNorm, h | h | h | h⟩ := hshape
  · exact (not_quotIsoWith_perm3 hq hU hs h.1).elim
  · refine ⟨?_, h.1, hNorm, h.2⟩
    have hc := S152Fin.QuotIsoWith.card_eq h.1
    rw [S152Fin.card_Perm_five] at hc
    have hrel := Subgroup.relIndex_mul_index (subgroupOf_pCoreOf_le hU hs)
    rw [← hc, index_pCoreOf_eq hq] at hrel
    have h1 : ((pCoreOf 2 H).subgroupOf H).relIndex ((cSecIn H L N).subgroupOf H) = 1 := by
      omega
    have h2 := Subgroup.relIndex_eq_one.mp h1
    refine le_antisymm (fun x hx => ?_) (S152Fin.pCoreOf_le_cSecIn hU hs)
    have hxH : x ∈ H := S152Fin.cSecIn_le_left H L N hx
    exact h2 (show (⟨x, hxH⟩ : ↥H) ∈ (cSecIn H L N).subgroupOf H from hx)
  · exfalso
    have hc := S152Fin.QuotIsoWith.card_eq h.1
    rw [S152Fin.card_Wr] at hc
    rw [← hc] at hdvd
    omega
  · exfalso
    have hc := S152Fin.QuotIsoWith.card_eq h.1
    rw [S152Fin.card_Wr_five] at hc
    rw [← hc] at hdvd
    omega

theorem card_eq_sixteen_mul_of_naturalSn {F L X : Subgroup G} [(L.subgroupOf X).Normal]
    (hLX : L ≤ X) (h : NaturalSn 5 F L X) : Nat.card X = 16 * Nat.card L := by
  obtain ⟨θ, β, -, -, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk]
    exact X1512.natKer_eq_bot (Or.inr rfl)
  have hcard : Nat.card (G6.coreMod 5) = Nat.card (↥X ⧸ L.subgroupOf X) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  rw [X1512.card_coreMod (Or.inr rfl)] at hcard
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf X)
  have h2 : Nat.card (L.subgroupOf X) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
  rw [h1, ← hcard, h2]
  norm_num

theorem card_eq_sixteen_mul [Finite G] {H U L N : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) (hshape : ChiefFactorShape H L N) :
    Nat.card N = 16 * Nat.card L := by
  obtain ⟨-, -, hn, hNat⟩ := shape_five hq hU hs hshape
  exact card_eq_sixteen_mul_of_naturalSn hs.2.2.1.le hNat

theorem pow_le_card_of_series [Finite G] {H U N : Subgroup G} {n : ℕ}
    (hseries : IsChiefSeriesFrom H U N n)
    (hstep : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      Nat.card N' = 16 * Nat.card L') :
    16 ^ n ≤ Nat.card N := by
  induction hseries with
  | bot => simp
  | central hs _ _ ih => exact ih.trans (Subgroup.card_le_of_le hs.2.2.1.le)
  | noncentral hs hnc _ ih =>
    rw [hstep _ _ hs hnc, pow_succ]
    omega

end SzF53A1

theorem F53EData.shape_five {G : Type} [Group G] [Finite G] {H S E L N : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hE : F53EData H S E)
    (hs : IsChiefStep H E L N) (hnc : ¬ IsCentralStep H L N) :
    cSecIn H L N = pCoreOf 2 H ∧
      QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
      ∃ _ : (L.subgroupOf N).Normal, NaturalSn 5 H L N :=
  SzF53A1.shape_five hq hE.abelian hs (hE.shape L N hs hnc)

theorem F53EData.card_eq_sixteen_mul {G : Type} [Group G] [Finite G] {H S E L N : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hE : F53EData H S E)
    (hs : IsChiefStep H E L N) (hnc : ¬ IsCentralStep H L N) :
    Nat.card N = 16 * Nat.card L :=
  SzF53A1.card_eq_sixteen_mul hq hE.abelian hs (hE.shape L N hs hnc)

theorem F53EData.card_ge {G : Type} [Group G] [Finite G] {H S E : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hSH : S ≤ H) (hE : F53EData H S E) :
    256 ≤ Nat.card E := by
  have _hEH : E ≤ H := hE.le.trans hSH
  have h := SzF53A1.pow_le_card_of_series hE.chief fun L N hs hnc =>
    hE.card_eq_sixteen_mul hq hs hnc
  norm_num at h
  exact h

end CFSG.Quasithin
