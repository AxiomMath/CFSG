module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.A5.G3.M23

theorem m23_core
    (B : Subgroup ↥Mg) (hD : IsSL25Group ↥B)
    (hUB : Tg.subgroupOf Mg ≤ Subgroup.normalizer (B : Set ↥Mg)) : False := by
  classical
  obtain ⟨j, hj1, hj2, -, -⟩ := sl25_sup_data tSylow hD hUB
  have hUcard : Nat.card ↥(Tg.subgroupOf Mg) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le).toEquiv, card_Tg]
    norm_num
  have hj : j = 0 := by
    have h2 : 2 ^ (7 + j) = 2 ^ 7 := by rw [← hj1, hUcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hYcard : Nat.card ↥(B ⊔ Tg.subgroupOf Mg) = 1920 := by rw [hj2]; norm_num
  have hY₀card : Nat.card ↥((B ⊔ Tg.subgroupOf Mg).map Mg.subtype) = 1920 := by
    rw [Subgroup.card_map_of_injective Mg.subtype_injective]
    exact hYcard
  have hY₀M : (B ⊔ Tg.subgroupOf Mg).map Mg.subtype ≤ Mg := Subgroup.map_subtype_le _
  have hTU : (Tg.subgroupOf Mg).map Mg.subtype = Tg := Subgroup.map_subgroupOf_eq_of_le Tg_le
  have hTY : Tg ≤ (B ⊔ Tg.subgroupOf Mg).map Mg.subtype :=
    hTU.symm.le.trans (Subgroup.map_mono le_sup_right)
  have hBY : B.map Mg.subtype ≤ (B ⊔ Tg.subgroupOf Mg).map Mg.subtype :=
    Subgroup.map_mono le_sup_left
  have hB₀M : B.map Mg.subtype ≤ Mg := Subgroup.map_subtype_le _
  have hD₀ : IsSL25Group ↥(B.map Mg.subtype) :=
    hD.of_equiv (B.equivMapOfInjective Mg.subtype Mg.subtype_injective)
  have hTB₀ : Tg ≤ Subgroup.normalizer ((B.map Mg.subtype : Subgroup (Perm (Fin 23))) :
      Set (Perm (Fin 23))) :=
    hTU.symm.le.trans (normalizer_map_subtype hUB)
  generalize (B ⊔ Tg.subgroupOf Mg).map Mg.subtype = Y₀ at hY₀card hY₀M hTY hBY
  generalize B.map Mg.subtype = B₀ at hBY hB₀M hD₀ hTB₀
  have hcl1 : C1.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C1.cert_check
  have hcl2 : C2.cert.closedOK RN.enc = true := LatCert.closedOK_of_check C2.cert_check
  rcases orbit_zero_cases hTY hY₀card with hA | hB | hC
  ·
    have hfix : ∀ y ∈ Y₀, y 0 = 0 := by
      intro y hy
      have hmem : y 0 ∈ MulAction.orbit ↥Y₀ (0 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      have key : ∀ z : Fin 23, tau z = 0 → z = 0 := by decide
      exact key _ ((hA _).mp hmem)
    have hB₀le : B₀ ≤ Subgroup.closure {g | g ∈ mGens1} := fun y hy =>
      fix_le_closure1 y (hB₀M hy) (hfix y (hBY hy))
    exact not_isSL25_of_latCert_amb C1.cert C1.cert_check C1.cert_tle (by decide)
      (m := 3465) (by decide) (by decide)
      (A5.G3.hA_of_latSixCheck C1.cert hcl1 [C1.aData1] C1.cert_latSix) B₀ hB₀le hD₀ hTB₀
  ·
    have hstab : Nat.card (MulAction.stabilizer ↥Y₀ (0 : Fin 23)) = 640 := by
      have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥Y₀ (0 : Fin 23))
      have h3 : (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).index = 3 := by
        rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hB]
      rw [h3, hY₀card] at h1
      omega
    have hZcard : Nat.card ↥((MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype) = 640 := by
      rw [Subgroup.card_map_of_injective Y₀.subtype_injective]
      exact hstab
    have hTZ : Tg ≤ (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype := fun t ht =>
      ⟨⟨t, hTY ht⟩, MulAction.mem_stabilizer_iff.mpr (closure_tGens_fix_zero t ht), rfl⟩
    have hZM : (MulAction.stabilizer ↥Y₀ (0 : Fin 23)).map Y₀.subtype ≤
        Subgroup.closure {g | g ∈ mGens1} := by
      rintro _ ⟨⟨z, hz⟩, hzs, rfl⟩
      exact fix_le_closure1 z (hY₀M hz) (MulAction.mem_stabilizer_iff.mp hzs)
    have hmem := A5.G3.card_mem_sizes_of_latCert C1.cert C1.cert_check _ hTZ hZM
    rw [hZcard] at hmem
    revert hmem
    decide
  ·
    have h19 := orbit_nineteen hTY hY₀card hC
    have hfix : ∀ y ∈ Y₀, y 19 ∈ ({19, 20} : Finset (Fin 23)) ∧
        y 20 ∈ ({19, 20} : Finset (Fin 23)) := by
      intro y hy
      have m19 : y 19 ∈ MulAction.orbit ↥Y₀ (19 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      have m20 : (20 : Fin 23) ∈ MulAction.orbit ↥Y₀ (19 : Fin 23) := (h19 20).mpr (by decide)
      have e : MulAction.orbit ↥Y₀ (20 : Fin 23) = MulAction.orbit ↥Y₀ (19 : Fin 23) :=
        MulAction.orbit_eq_iff.mpr m20
      have m20' : y 20 ∈ MulAction.orbit ↥Y₀ (20 : Fin 23) := ⟨⟨y, hy⟩, rfl⟩
      rw [e] at m20'
      have key : ∀ z : Fin 23, tau z = 1 → z ∈ ({19, 20} : Finset (Fin 23)) := by decide
      exact ⟨key _ ((h19 _).mp m19), key _ ((h19 _).mp m20')⟩
    have hB₀le : B₀ ≤ Subgroup.closure {g | g ∈ mGens2} := fun y hy =>
      stab2_le_closure y (hB₀M hy) (hfix y (hBY hy)).1 (hfix y (hBY hy)).2
    exact not_isSL25_of_latCert_amb C2.cert C2.cert_check C2.cert_tle (by decide)
      (m := 315) (by decide) (by decide)
      (A5.G3.hA_of_latSixCheck C2.cert hcl2 [C2.aData1, C2.aData2] C2.cert_latSix) B₀ hB₀le
      hD₀ hTB₀

theorem noSL25Norm_m23
    {X : Type} [Group X] (h : IsSporadic .M23 X) : NoSL25Norm X := by
  obtain ⟨e⟩ := h
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := e
  exact NoSL25Norm.of_mulEquiv e'.symm
    (noSL25Norm_of_sylow tSylow fun B hUB hD => m23_core B hD hUB)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
