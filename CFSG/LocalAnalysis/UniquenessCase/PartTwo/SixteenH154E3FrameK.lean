module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_e3_frame_map_sup {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {x : MulAut W} (hx : x ∈ X) :
    (L ⊔ L').map (MulAut.conj x).toMonoidHom = L ⊔ L' := by
  rw [Subgroup.map_sup]
  rcases F.perm x hx with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

private theorem s16h_e3_frame_K_map_le {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {x : MulAut W} (hx : x ∈ X) :
    (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))).map
        (MulAut.conj x).toMonoidHom ≤
      X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
  have hconj : (MulAut.conj x).toMonoidHom y = x * y * x⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hconj]
  refine ⟨X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro a ha
  have ha' : x⁻¹ * a * x ∈ L ⊔ L' := by
    have h := s16h_e3_frame_map_sup F (X.inv_mem hx)
    have hmem : (MulAut.conj x⁻¹).toMonoidHom a ∈ (L ⊔ L').map (MulAut.conj x⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ ha
    rw [h] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hcomm : (x⁻¹ * a * x) * y = y * (x⁻¹ * a * x) :=
    Subgroup.mem_centralizer_iff.mp hyC _ ha'
  calc a * (x * y * x⁻¹) = x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * y * x⁻¹) * a := by group

theorem s16h_e3_frame_K_map {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {x : MulAut W} (hx : x ∈ X) :
    (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))).map
        (MulAut.conj x).toMonoidHom =
      X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := by
  refine le_antisymm (s16h_e3_frame_K_map_le F hx) ?_
  intro y hy
  have hy' : (MulAut.conj x⁻¹).toMonoidHom y ∈
      X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) :=
    s16h_e3_frame_K_map_le F (X.inv_mem hx) (Subgroup.mem_map_of_mem _ hy)
  refine Subgroup.mem_map.mpr ⟨_, hy', ?_⟩
  simp [MulAut.conj_apply]
  group

private theorem s16h_e3_Z_of_unique_aux {W : Type} [CommGroup W]
    {X K S : Subgroup (MulAut W)} {p : ℕ} (hKX : K ≤ X)
    (hKS : ∀ k ∈ K, ∀ a ∈ S, a * k = k * a)
    (hKmap : ∀ x ∈ X, K.map (MulAut.conj x).toMonoidHom = K)
    {ZK : Subgroup ↥K} (hZ : Nat.card ↥ZK = p)
    (huniq : ∀ Z' : Subgroup ↥K, Nat.card ↥Z' = p → Z' = ZK) :
    Nat.card ↥(ZK.map K.subtype) = p ∧ ZK.map K.subtype ≤ X ∧
      (∀ x ∈ X, (ZK.map K.subtype).map (MulAut.conj x).toMonoidHom = ZK.map K.subtype) ∧
      ∀ z ∈ ZK.map K.subtype, ∀ a ∈ S, z * a = a * z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hZ
  · rintro _ ⟨k, -, rfl⟩
    exact hKX k.2
  · intro x hx
    have hKx := hKmap x hx
    have hle : (ZK.map K.subtype).map (MulAut.conj x).toMonoidHom ≤ K := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hmem : (MulAut.conj x).toMonoidHom (k : MulAut W) ∈
          K.map (MulAut.conj x).toMonoidHom := Subgroup.mem_map_of_mem _ k.2
      rwa [hKx] at hmem
    have hcard : Nat.card ↥((ZK.map K.subtype).map (MulAut.conj x).toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
        Subgroup.card_map_of_injective K.subtype_injective]
      exact hZ
    have hsub : ((ZK.map K.subtype).map (MulAut.conj x).toMonoidHom).subgroupOf K = ZK := by
      refine huniq _ ?_
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    calc (ZK.map K.subtype).map (MulAut.conj x).toMonoidHom
        = (((ZK.map K.subtype).map (MulAut.conj x).toMonoidHom).subgroupOf K).map K.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hle).symm
      _ = ZK.map K.subtype := by rw [hsub]
  · rintro _ ⟨k, -, rfl⟩ a ha
    exact (hKS k k.2 a ha).symm

theorem s16h_e3_frame_Z_of_unique {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U') {p : ℕ}
    {ZK : Subgroup ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W)))}
    (hZ : Nat.card ↥ZK = p)
    (huniq : ∀ Z' : Subgroup ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
      Set (MulAut W))), Nat.card ↥Z' = p → Z' = ZK) :
    Nat.card ↥(ZK.map (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
        Set (MulAut W))).subtype) = p ∧
      ZK.map (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
        Set (MulAut W))).subtype ≤ X ∧
      (∀ x ∈ X, (ZK.map (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
          Set (MulAut W))).subtype).map (MulAut.conj x).toMonoidHom =
        ZK.map (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
          Set (MulAut W))).subtype) ∧
      ∀ z ∈ ZK.map (X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) :
          Set (MulAut W))).subtype, ∀ a ∈ L ⊔ L', z * a = a * z :=
  s16h_e3_Z_of_unique_aux inf_le_left
    (fun k hk a ha => Subgroup.mem_centralizer_iff.mp hk.2 a ha)
    (fun x hx => s16h_e3_frame_K_map F hx) hZ huniq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
