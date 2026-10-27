module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONFacts
public import CFSG.Sporadic.Schreier.ONInvolution
public import CFSG.Sporadic.Schreier.ONCentralQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

open CFSG.ONSchreier CFSG.AGLEmbedding.ParabHub Subgroup

theorem onT_le_onM :
    onT ≤ onM := by
  rw [onM_eq_centralizer_z]
  intro t ht
  have hz : onz ∈ CFSG.centerIn onT := by
    rw [onT_centerIn]
    exact mem_zpowers _
  refine mem_inf.2 ⟨onT_le ht, mem_centralizer_iff.2 fun g hg => ?_⟩
  rw [Set.mem_singleton_iff.1 hg]
  exact (mem_centralizer_iff.1 (mem_inf.1 hz).2 t ht).symm

theorem card_onT_subgroupOf_M :
    Nat.card (onT.subgroupOf onM) = 512 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe onT_le_onM).toEquiv, card_onT]

theorem onQ_le_onT :
    onQ ≤ onT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPg : IsPGroup 2 (onT.subgroupOf onM) :=
    IsPGroup.of_card (n := 9) (by rw [card_onT_subgroupOf_M]; norm_num)
  have hidx : ¬ 2 ∣ (onT.subgroupOf onM).index := by
    have h := (onT.subgroupOf onM).card_mul_index
    rw [card_onT_subgroupOf_M, card_onM] at h
    have hi : (onT.subgroupOf onM).index = 315 := by omega
    rw [hi]
    decide
  have hQn : (onQ.subgroupOf onM).Normal := by
    rw [← rhoM_ker]
    exact rhoM.normal_ker
  have hQp : IsPGroup 2 (onQ.subgroupOf onM) :=
    IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
  have hle := hQp.le_sylow_of_normal (hPg.toSylow hidx)
  intro x hx
  have h := hle (show (⟨x, onQ_le_M hx⟩ : onM) ∈ onQ.subgroupOf onM from hx)
  exact h

theorem eq_onT_of_le_onM
    {Y : Subgroup (Equiv.Perm (Fin N))} (hTY : onT ≤ Y) (hYM : Y ≤ onM)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = onT := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρR : ∀ m : onM, rhoM m ∈ onM120Chain.originalSubgroup := fun m => by
    rw [← rhoM_range]
    exact ⟨m, rfl⟩
  let φ : onM →* onM120Chain.originalSubgroup := rhoM.codRestrict _ hρR
  have hφker : φ.ker = onQ.subgroupOf onM := by
    rw [← rhoM_ker]
    exact MonoidHom.ker_codRestrict rhoM _ hρR
  set T' := onT.subgroupOf onM with hT'
  set Y' := Y.subgroupOf onM with hY'
  have hTY' : T' ≤ Y' := fun x hx => hTY hx
  have hkerT : φ.ker ≤ T' := by
    rw [hφker]
    exact fun x hx => onQ_le_onT hx
  have hcardT' : Nat.card T' = 512 := by
    rw [hT', card_onT_subgroupOf_M]
  have hcardφT : Nat.card (T'.map φ) = 128 := by
    let ψ : T' →* onM120Chain.originalSubgroup := φ.comp T'.subtype
    have hr : ψ.range = T'.map φ := by
      rw [MonoidHom.range_comp, range_subtype]
    have hk : Nat.card ψ.ker = 4 := by
      have : ψ.ker = φ.ker.subgroupOf T' := by
        ext t
        rfl
      rw [this, Nat.card_congr (subgroupOfEquivOfLe hkerT).toEquiv, hφker,
        card_onQ_subgroupOf_M]
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hk, hr, hcardT'] at h
    omega
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T'.map φ) ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 7) (by rw [hcardφT]; norm_num), ?_⟩
    rw [show ((T'.map φ).subgroupOf ⊤).index = (T'.map φ).index from relIndex_top_right _]
    have h := (T'.map φ).card_mul_index
    rw [hcardφT, card_onM120] at h
    have hi : (T'.map φ).index = 315 := by omega
    rw [hi]
    decide
  have h3Y : ¬ 3 ∣ Nat.card (Y'.map φ) := by
    intro h
    apply h3
    have h1 : Nat.card (Y'.map φ) ∣ Nat.card Y' := Subgroup.card_map_dvd _ _
    rw [hY', Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv] at h1
    exact h.trans h1
  have hYT : Y'.map φ = T'.map φ := by
    by_contra hne
    exact h3Y (threeDvdOver_onR _ _ hSyl (Subgroup.map_mono hTY') hne)
  have hY'T' : Y' ≤ T' := by
    calc Y' ≤ (Y'.map φ).comap φ := Subgroup.le_comap_map _ _
      _ = T' := by rw [hYT, Subgroup.comap_map_eq, sup_eq_left.2 hkerT]
  refine le_antisymm (fun y hy => ?_) hTY
  have h := hY'T' (show (⟨y, hYM hy⟩ : onM) ∈ Y' from hy)
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK
