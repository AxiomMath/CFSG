module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixModel
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.FixVLatticeSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s1611e3_sixFixMod_mem_iff {W : Type} [CommGroup W]
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} (hker : Φ.ker = K)
    (X : Subgroup (MulAut (SixE6 × SixE6))) (u : SixE6 × SixE6) :
    u ∈ sixFixMod K X ↔ ∀ x ∈ X, Φ (x u) = Φ u := by
  simp only [sixFixMod, Set.mem_setOf_eq]
  constructor
  · intro hu x hx
    have h : x u * u⁻¹ ∈ Φ.ker := by rw [hker]; exact hu x hx
    have h1 : Φ (x u * u⁻¹) = 1 := MonoidHom.mem_ker.mp h
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  · intro hu x hx
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hu x hx]
    simp

private lemma s1611e3_fixV_image {W : Type} [CommGroup W] {M : Subgroup (MulAut W)}
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {Θ : ↥sixGhat ≃* ↥M}
    (hΦ : Function.Surjective Φ) (hker : Φ.ker = K)
    (hΘ : ∀ (g : ↥sixGhat) (u : SixE6 × SixE6),
      Φ ((g : MulAut (SixE6 × SixE6)) u) = ((Θ g : ↥M) : MulAut W) (Φ u))
    {X : Subgroup (MulAut (SixE6 × SixE6))} (hX : X ≤ sixGhat) (w : W) :
    w ∈ fixV ((X.subgroupOf sixGhat).map (M.subtype.comp Θ.toMonoidHom)) ↔
      w ∈ Φ '' sixFixMod K X := by
  constructor
  · intro hw
    simp only [fixV, Set.mem_setOf_eq] at hw
    obtain ⟨u, rfl⟩ := hΦ w
    refine (Set.mem_image Φ (sixFixMod K X) (Φ u)).mpr ⟨u, ?_, rfl⟩
    rw [s1611e3_sixFixMod_mem_iff hker X u]
    intro x hx
    have hxG : x ∈ sixGhat := hX hx
    have hx' : (⟨x, hxG⟩ : ↥sixGhat) ∈ X.subgroupOf sixGhat := hx
    have hmem : (M.subtype.comp Θ.toMonoidHom) ⟨x, hxG⟩ ∈
        (X.subgroupOf sixGhat).map (M.subtype.comp Θ.toMonoidHom) :=
      Subgroup.mem_map_of_mem _ hx'
    have h1 := hw _ hmem
    rw [hΘ ⟨x, hxG⟩ u]
    exact h1
  · intro hw
    obtain ⟨u, hu, rfl⟩ := (Set.mem_image Φ (sixFixMod K X) w).mp hw
    simp only [fixV, Set.mem_setOf_eq]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxX : (x : MulAut (SixE6 × SixE6)) ∈ X := hx
    have hxG : (x : MulAut (SixE6 × SixE6)) ∈ sixGhat := hX hxX
    change ((Θ x : ↥M) : MulAut W) (Φ u) = Φ u
    rw [← hΘ x u]
    exact (s1611e3_sixFixMod_mem_iff hker X u).mp hu (x : MulAut (SixE6 × SixE6)) hxX

private lemma s1611e3_sixFixMod_mul_mem {W : Type} [CommGroup W] {M : Subgroup (MulAut W)}
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {Θ : ↥sixGhat ≃* ↥M}
    (hker : Φ.ker = K)
    (hΘ : ∀ (g : ↥sixGhat) (u : SixE6 × SixE6),
      Φ ((g : MulAut (SixE6 × SixE6)) u) = ((Θ g : ↥M) : MulAut W) (Φ u))
    {X : Subgroup (MulAut (SixE6 × SixE6))} (hX : X ≤ sixGhat)
    {u k : SixE6 × SixE6} (hu : u ∈ sixFixMod K X) (hk : k ∈ K) :
    u * k ∈ sixFixMod K X := by
  have hu' : ∀ x ∈ X, Φ (x u) = Φ u := (s1611e3_sixFixMod_mem_iff hker X u).mp hu
  rw [s1611e3_sixFixMod_mem_iff hker X (u * k)]
  intro x hx
  have hxG : x ∈ sixGhat := hX hx
  have hk1 : Φ k = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hk)
  have h1 : Φ (x (u * k)) = Φ (x u) := by
    rw [map_mul, map_mul, hΘ ⟨x, hxG⟩ k, hk1, map_one, mul_one]
  have h2 : Φ (u * k) = Φ u := by
    rw [map_mul, hk1, mul_one]
  rw [h1, h2]
  exact hu' x hx

private lemma s1611e3_sixFixMod_eq_of_image_eq {W : Type} [CommGroup W] {M : Subgroup (MulAut W)}
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {Θ : ↥sixGhat ≃* ↥M}
    (hker : Φ.ker = K)
    (hΘ : ∀ (g : ↥sixGhat) (u : SixE6 × SixE6),
      Φ ((g : MulAut (SixE6 × SixE6)) u) = ((Θ g : ↥M) : MulAut W) (Φ u))
    {X Y : Subgroup (MulAut (SixE6 × SixE6))} (hX : X ≤ sixGhat) (hY : Y ≤ sixGhat)
    (h : Φ '' sixFixMod K X = Φ '' sixFixMod K Y) :
    sixFixMod K X = sixFixMod K Y := by
  apply Set.Subset.antisymm
  · intro u hu
    have hmem : Φ u ∈ Φ '' sixFixMod K Y := by
      rw [← h]
      exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hvu⟩ := hmem
    have hvk : v⁻¹ * u ∈ K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hvu]
      simp
    have hvu' : v * (v⁻¹ * u) = u := by group
    rw [← hvu']
    exact s1611e3_sixFixMod_mul_mem hker hΘ hY hv hvk
  · intro u hu
    have hmem : Φ u ∈ Φ '' sixFixMod K X := by
      rw [h]
      exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hvu⟩ := hmem
    have hvk : v⁻¹ * u ∈ K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hvu]
      simp
    have hvu' : v * (v⁻¹ * u) = u := by group
    rw [← hvu']
    exact s1611e3_sixFixMod_mul_mem hker hΘ hX hv hvk

theorem s1611e3_six_transport {W : Type} [CommGroup W] {M : Subgroup (MulAut W)}
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {Θ : ↥sixGhat ≃* ↥M}
    (hK : K = ⊥ ∨ K = sixDiag) (hΦ : Function.Surjective Φ) (hker : Φ.ker = K)
    (hΘ : ∀ (g : ↥sixGhat) (u : SixE6 × SixE6),
      Φ ((g : MulAut (SixE6 × SixE6)) u) = ((Θ g : ↥M) : MulAut W) (Φ u))
    (hfin : ∀ E : Subgroup (MulAut (SixE6 × SixE6)), E ≤ sixGhat → E ≠ ⊥ →
      IsElemAbelian2 (V := SixE6 × SixE6) E →
      ∃ B : Subgroup (MulAut (SixE6 × SixE6)), B ≤ E ∧ E3.mQuot E B < 2 ∧
        sixFixMod K B ≠ sixFixMod K E) :
    ∀ E ∈ E3.aSet 2 M, False := by
  intro E hE
  simp only [E3.aSet, Set.mem_setOf_eq] at hE
  obtain ⟨hEM, hEbot, hEab, hEfix⟩ := hE
  let g : ↥M →* MulAut (SixE6 × SixE6) := sixGhat.subtype.comp Θ.symm.toMonoidHom
  let f : ↥sixGhat →* MulAut W := M.subtype.comp Θ.toMonoidHom
  let Ehat : Subgroup (MulAut (SixE6 × SixE6)) := (E.subgroupOf M).map g
  have hginj : Function.Injective g := sixGhat.subtype_injective.comp Θ.symm.injective
  have hfinj : Function.Injective f := M.subtype_injective.comp Θ.injective
  have hEhatle : Ehat ≤ sixGhat := by
    intro x hx
    obtain ⟨m, -, hgmx⟩ := Subgroup.mem_map.mp hx
    rw [← hgmx]
    exact (Θ.symm m).2
  have hEhatbot : Ehat ≠ ⊥ := by
    intro h
    have h1 : E.subgroupOf M = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (E.subgroupOf M) hginj).1 h
    have hd : E ⊓ M = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h1)
    rw [inf_of_le_left hEM] at hd
    exact hEbot hd
  have hEhatab : IsElemAbelian2 (V := SixE6 × SixE6) Ehat := by
    have hEsub : IsElemAbelian2 ((E.subgroupOf M).map M.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hEM]
      exact hEab
    have hprops := (FixVLat.isElemAbelian2_map_iff M.subtype_injective
      (B := E.subgroupOf M)).1 hEsub
    exact (FixVLat.isElemAbelian2_map_iff hginj (B := E.subgroupOf M)).2 hprops
  obtain ⟨Bhat, hBhatE, hBhatm, hBhatS⟩ := hfin Ehat hEhatle hEhatbot hEhatab
  have hBhatle : Bhat ≤ sixGhat := le_trans hBhatE hEhatle
  let B : Subgroup (MulAut W) := (Bhat.subgroupOf sixGhat).map f
  have hEimg : (Ehat.subgroupOf sixGhat).map f = E := by
    ext e
    constructor
    · intro he
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
      have hyE : (y : MulAut (SixE6 × SixE6)) ∈ Ehat := hy
      obtain ⟨m, hm, hgmy⟩ := Subgroup.mem_map.mp hyE
      have hy_eq : y = Θ.symm m := Subtype.ext (by rw [← hgmy]; rfl)
      rw [hy_eq]
      change M.subtype (Θ (Θ.symm m)) ∈ E
      rw [MulEquiv.apply_symm_apply]
      exact hm
    · intro he
      refine Subgroup.mem_map.mpr ⟨Θ.symm ⟨e, hEM he⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨e, hEM he⟩, he, rfl⟩
      · change M.subtype (Θ (Θ.symm ⟨e, hEM he⟩)) = e
        simp
  have hBE : B ≤ E := by
    change (Bhat.subgroupOf sixGhat).map f ≤ E
    rw [← hEimg]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono sixGhat hBhatE)
  have hmQuot : E3.mQuot E B = E3.mQuot Ehat Bhat := by
    unfold E3.mQuot
    congr 1
    rw [show B = (Bhat.subgroupOf sixGhat).map f from rfl, ← hEimg]
    rw [Subgroup.relIndex_map_map_of_injective (Bhat.subgroupOf sixGhat)
        (Ehat.subgroupOf sixGhat) hfinj,
      Subgroup.relIndex_subgroupOf (H := Bhat) (K := Ehat) (L := sixGhat) hEhatle]
  have hfix : fixV B = fixV E := hEfix B hBE (by rw [hmQuot]; exact hBhatm)
  have hfixset : (fixV B : Set W) = (fixV E : Set W) :=
    congrArg (fun S : Subgroup W => (S : Set W)) hfix
  have hS_B : fixV B = Φ '' sixFixMod K Bhat := by
    ext w
    exact s1611e3_fixV_image hΦ hker hΘ hBhatle w
  have hS_E : fixV E = Φ '' sixFixMod K Ehat := by
    rw [← hEimg]
    ext w
    exact s1611e3_fixV_image hΦ hker hΘ hEhatle w
  have himg : Φ '' sixFixMod K Bhat = Φ '' sixFixMod K Ehat := by
    rw [← hS_B, ← hS_E]
    exact hfixset
  exact hBhatS (s1611e3_sixFixMod_eq_of_image_eq hker hΘ hBhatle hEhatle himg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
