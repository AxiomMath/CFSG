module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.Quasithin.EmptyFaithful.S152Y22
public import CFSG.Quasithin.EmptyFaithful.SBc14Pair

public section

namespace CFSG.Quasithin.FixR

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj {Q : Subgroup G} {g x : G} :
    x ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem frattini_two {C Q : Subgroup G} (hQ : IsSylowTwoOf Q C) {n : G}
    (hn : n ∈ Subgroup.normalizer (C : Set G)) :
    ∃ c ∈ C, c⁻¹ * n ∈ Subgroup.normalizer (Q : Set G) := by
  have hQ' : IsSylowTwoOf (Q.map (MulAut.conj n).toMonoidHom) C := by
    refine isSylowTwoOf_of_card_eq ?_ (hQ.isPGroup.map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hn y).mp (hQ.le hy)
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hQ.card_eq]
  obtain ⟨c, hcC, hc⟩ := hQ.exists_conj hQ'
  refine ⟨c, hcC, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ x : G, n⁻¹ * x * n ∈ Q ↔ c⁻¹ * x * c ∈ Q := fun x => by
    have := SetLike.ext_iff.mp hc x
    rwa [mem_map_conj, mem_map_conj] at this
  have h1 := key (n * y * n⁻¹)
  have e1 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
  have e2 : c⁻¹ * (n * y * n⁻¹) * c = (c⁻¹ * n) * y * (c⁻¹ * n)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

omit [Finite G] in
theorem exists_mul_of_mem_sup {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G)) {x : G}
    (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  have hle : W ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hWN Subgroup.le_normalizer
  have hNn : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hle
  have hx' : (⟨x, hx⟩ : ↥(W ⊔ N)) ∈ W.subgroupOf (W ⊔ N) ⊔ N.subgroupOf (W ⊔ N) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, n, hn, hwn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨w, hw, n, hn, congrArg Subtype.val hwn⟩

section Ker

variable {H T Γ : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_le_kerAct
    (hab : ∀ k ∈ oTwoUpper H, ∀ k' ∈ oTwoUpper H, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) :
    oTwoUpper H ≤ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) := fun k hk =>
  SBc14.mem_kerAct.mpr ⟨le_normalizer_pCoreOf 2 (oTwoUpper H) hk, fun k' hk' => hab k hk k' hk'⟩

theorem pCoreOf_oTwoUpper_le (H : Subgroup G) : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  rw [S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)]
  exact inf_le_right

theorem inf_kerAct_le_pCoreOf (hT : IsSylowTwoOf T H)
    (hab : ∀ k ∈ oTwoUpper H, ∀ k' ∈ oTwoUpper H, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) :
    T ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) ≤ pCoreOf 2 H := by
  set K := oTwoUpper H with hK
  set O := pCoreOf 2 K with hO
  set kA := SBc14.kerAct K O with hkA
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hKkA : K ≤ kA := oTwoUpper_le_kerAct hab
  have hOQ : O ≤ pCoreOf 2 H := pCoreOf_oTwoUpper_le H
  have hQT : pCoreOf 2 H ≤ T := hT.pCoreOf_le
  have hOkA : O ≤ kA := (pCoreOf_le 2 K).trans hKkA
  set C := H ⊓ kA with hC
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer (SBc14.le_normalizer_kerAct hHK hHO)
  have hKC : K ≤ C := le_inf hKH hKkA
  set D := T ⊓ kA with hD
  have hDC : D ≤ C := le_inf (inf_le_left.trans hT.le) inf_le_right
  have hOD : O ≤ D := le_inf (hOQ.trans hQT) hOkA
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    intro k hk d hd
    have h1 : d * k * d⁻¹ * k⁻¹ ∈ O := (SBc14.mem_kerAct.mp hd.2).2 k hk
    have h2 : k * d * k⁻¹ * d⁻¹ ∈ D := by
      have := hOD (O.inv_mem h1)
      have e : (d * k * d⁻¹ * k⁻¹)⁻¹ = k * d * k⁻¹ * d⁻¹ := by group
      rwa [e] at this
    have e : k * d * k⁻¹ = (k * d * k⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact D.mul_mem h2 hd
  have hCD : ∀ c ∈ C, ∃ t ∈ D, ∃ k ∈ K, t * k = c := by
    intro c hc
    have hcH : c ∈ T ⊔ K := by
      rw [sup_comm, C1Pack12.oTwoUpper_sup_eq_of_sylow hT]
      exact hc.1
    obtain ⟨t, htT, k, hkK, rfl⟩ := exists_mul_of_mem_sup (hT.le.trans hHK) hcH
    refine ⟨t, ⟨htT, ?_⟩, k, hkK, rfl⟩
    have h1 : t * k * k⁻¹ ∈ kA := kA.mul_mem hc.2 (kA.inv_mem (hKkA hkK))
    simpa using h1
  have hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    obtain ⟨t, htD, k, hkK, rfl⟩ := hCD c hc
    have e : t * k * d * (t * k)⁻¹ = t * (k * d * k⁻¹) * t⁻¹ := by group
    rw [e]
    exact D.mul_mem (D.mul_mem htD (hKD k hkK d hd)) (D.inv_mem htD)
  have hCnD : C ≤ Subgroup.normalizer (D : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hDn c hc x hx, fun hx => ?_⟩
    have := hDn c⁻¹ (C.inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have hDp : IsPGroup 2 D := hT.isPGroup.to_inf_left
  have hDO : D ≤ pCoreOf 2 C :=
    le_pCoreOf 2 hDC ((Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr hCnD) hDp
  have hCO : pCoreOf 2 C ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_left)
      (hHC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
  exact hDO.trans hCO

theorem pCoreOf_le_kerAct (H : Subgroup G) :
    pCoreOf 2 H ≤ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  intro y hy
  have hyH : y ∈ H := pCoreOf_le 2 H hy
  refine SBc14.mem_kerAct.mpr ⟨hHK.trans (normalizer_le_normalizer_pCoreOf 2 _) hyH, fun k hk => ?_⟩
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hKH hHK]
  refine ⟨?_, ?_⟩
  · have h1 : y * k * y⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp (hHK hyH) k).mp hk
    exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem hk)
  · have h1 : k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH hk)) y⁻¹).mp
        ((pCoreOf 2 H).inv_mem hy)
      exact this
    have e : y * k * y⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hy h1

theorem isSylowTwoOf_pCoreOf_kerAct (hTH : IsSylowTwoOf T H) (hTΓ : IsSylowTwoOf T Γ)
    (hHΓ : H ≤ Γ) (hΓK : Γ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hab : ∀ k ∈ oTwoUpper H, ∀ k' ∈ oTwoUpper H, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) :
    IsSylowTwoOf (pCoreOf 2 H)
      (Γ ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))) := by
  have hΓO : Γ ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    hΓK.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hΓC : Γ ≤ Subgroup.normalizer
      ((Γ ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) : Subgroup G) : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer (SBc14.le_normalizer_kerAct hΓK hΓO)
  have h1 := F7.isSylowTwoOf_inf_normal hTΓ inf_le_left (hTΓ.le.trans hΓC)
  have h2 : T ⊓ (Γ ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))) = pCoreOf 2 H := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact inf_kerAct_le_pCoreOf hTH hab ⟨hx.1, hx.2.2⟩
    · intro x hx
      exact ⟨hTH.pCoreOf_le hx, (pCoreOf_le 2 H).trans hHΓ hx, pCoreOf_le_kerAct H hx⟩
  rwa [h2] at h1

theorem exists_mul_mem_normalizer (hTH : IsSylowTwoOf T H) (hTΓ : IsSylowTwoOf T Γ)
    (hHΓ : H ≤ Γ) (hΓK : Γ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hab : ∀ k ∈ oTwoUpper H, ∀ k' ∈ oTwoUpper H, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 (oTwoUpper H))
    {n : G} (hn : n ∈ Γ) :
    ∃ c ∈ Γ ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)),
      c⁻¹ * n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have hΓO : Γ ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    hΓK.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hΓC : Γ ≤ Subgroup.normalizer
      ((Γ ⊓ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) : Subgroup G) : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer (SBc14.le_normalizer_kerAct hΓK hΓO)
  exact frattini_two (isSylowTwoOf_pCoreOf_kerAct hTH hTΓ hHΓ hΓK hab) (hΓC hn)

end Ker

end CFSG.Quasithin.FixR
