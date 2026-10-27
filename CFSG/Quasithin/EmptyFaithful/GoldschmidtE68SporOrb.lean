module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Open

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}
  [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

@[expose] def genOver (us : List Γ) : Subgroup Γ := Subgroup.closure {x | x ∈ C.sg ++ us}

theorem S_le_genOver (us : List Γ) : C.S ≤ genOver C us := by
  rw [← C.hSeq]
  refine Subgroup.closure_mono fun x hx => ?_
  exact List.mem_append_left _ hx

variable {C}

theorem genTabs_sg_us {us : List Γ} {uTabs : List (Array ℕ)} (hus : genTabs n us = uTabs) :
    genTabs n (C.sg ++ us) = C.D.sTabs ++ uTabs := by
  rw [genTabs_append, C.hsg, hus]

theorem card_gen {us : List Γ} {uTabs : List (Array ℕ)} (hus : genTabs n us = uTabs)
    {O : OmegaData Lab} (hO : OmegaSpec C.A.act (C.D.sTabs ++ uTabs).toArray C.Δ O) :
    Nat.card (genOver C us) = O.lbl.size * 2 ^ C.k := by
  have hlet : (genTabs n (C.sg ++ us)).toArray = (C.D.sTabs ++ uTabs).toArray := by
    rw [genTabs_sg_us hus]
  have hsz : (C.sg ++ us).toArray.size = (C.D.sTabs ++ uTabs).toArray.size := by
    rw [← hlet]
    simp [genTabs_length]
  have hel : ∀ l < (C.D.sTabs ++ uTabs).toArray.size,
      (C.D.sTabs ++ uTabs).toArray[l]! = (tab n ((C.sg ++ us).toArray.getD l 1)).toArray := by
    intro l hl
    rw [← hlet] at hl ⊢
    exact genTabs_hel' (C.sg ++ us) l hl
  have h := hO.card_eq C.hlaw C.hΔ (C.sg ++ us).toArray hsz hel
    (H := genOver C us) (by simp [genOver]) (S_le_genOver C us)
  rw [h]
  have : Nat.card (stab C.hlaw C.hΔ) = 2 ^ C.k := C.S_card
  rw [this]

theorem index_gen {us : List Γ} {uTabs : List (Array ℕ)} (hus : genTabs n us = uTabs)
    {O : OmegaData Lab} (hO : OmegaSpec C.A.act (C.D.sTabs ++ uTabs).toArray C.Δ O) :
    (C.S.subgroupOf (genOver C us)).index = O.lbl.size := by
  have h1 := Subgroup.card_mul_index (C.S.subgroupOf (genOver C us))
  have h2 : Nat.card (C.S.subgroupOf (genOver C us)) = 2 ^ C.k := by
    rw [← C.S_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S_le_genOver C us)).toEquiv
  rw [h2, card_gen hus hO] at h1
  have hpos : 0 < 2 ^ C.k := Nat.two_pow_pos _
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem mem_pCoreOf_gen {us : List Γ} {uTabs : List (Array ℕ)} (hus : genTabs n us = uTabs)
    {O : OmegaData Lab} (hO : OmegaSpec C.A.act (C.D.sTabs ++ uTabs).toArray C.Δ O)
    (hodd : O.lbl.size % 2 = 1) {x : Γ} (hx : x ∈ C.S)
    (hfix : ∀ i < O.lbl.size, C.A.act (tab n x).toArray O.lbl[i]! = O.lbl[i]!) :
    x ∈ pCoreOf 2 (genOver C us) := by
  have hlet : (genTabs n (C.sg ++ us)).toArray = (C.D.sTabs ++ uTabs).toArray := by
    rw [genTabs_sg_us hus]
  have hsz : (C.sg ++ us).toArray.size = (C.D.sTabs ++ uTabs).toArray.size := by
    rw [← hlet]
    simp [genTabs_length]
  have hel : ∀ l < (C.D.sTabs ++ uTabs).toArray.size,
      (C.D.sTabs ++ uTabs).toArray[l]! = (tab n ((C.sg ++ us).toArray.getD l 1)).toArray := by
    intro l hl
    rw [← hlet] at hl ⊢
    exact genTabs_hel' (C.sg ++ us) l hl
  have hmem := hO.mem_iff C.hlaw C.hΔ (C.sg ++ us).toArray hsz hel
    (H := genOver C us) (by simp [genOver]) (S_le_genOver C us)
  have hodd' : ¬ 2 ∣ (C.S.subgroupOf (genOver C us)).index := by
    rw [index_gen hus hO]
    omega
  rw [mem_pCoreOf_iff (S_le_genOver C us) C.S_isPGroup hodd']
  refine ⟨S_le_genOver C us hx, fun y hy => ?_⟩
  obtain ⟨i, hi, hyi⟩ := (hmem y).mp hy
  change lab n C.A C.Δ (y⁻¹ * x * y) = C.Δ
  have h1 : lab n C.A C.Δ (y⁻¹ * x * y) =
      C.A.act (tab n y⁻¹).toArray (C.A.act (tab n x).toArray (lab n C.A C.Δ y)) := by
    rw [mul_assoc, lab_mul C.hlaw C.hΔ, lab_mul C.hlaw C.hΔ]
  rw [h1, hyi, hfix i hi]
  have h2 : lab n C.A C.Δ (y⁻¹ * y) = C.A.act (tab n y⁻¹).toArray (lab n C.A C.Δ y) :=
    lab_mul C.hlaw C.hΔ _ _
  rw [inv_mul_cancel, lab_one C.hlaw C.hΔ, hyi] at h2
  exact h2.symm

end CFSG.Quasithin.E6.Spor
