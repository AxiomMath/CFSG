module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardASet
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSymExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.H13

theorem s16c11_v1_rkIdx_aSet_alt {n : ℕ} (hn : 7 ≤ n) {m : ℕ}
    (hconc : ∀ E ∈ E3.aSet 2 (G6.coreAct n).range, IsPGroup 2 ↥E → E ≠ ⊥ →
      m ≤ rkIdx (fixV E))
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X K L₀ L : Subgroup (MulAut W)} {J₀ : Subgroup W} (hM : S16C11Model X K J₀)
    (hK : IsSym ↥K 3) (hdir : IsInternalDirect K L₀ X) (hL₀ : IsSym ↥L₀ n)
    (hA : UC22.IsAlt ↥L n) (hLL₀ : L ≤ L₀) (φ : ↥L →* MulAut ↥J₀)
    (hφ : ∀ (x : ↥L) (j : ↥J₀), (((φ x : MulAut ↥J₀) j : ↥J₀) : W) = (x : MulAut W) (j : W))
    (hcomm : commV φ.range = ⊤) (hR : (altCoreModel n).Realizes φ.range ⊤ ⊥)
    {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    2 * m ≤ rkIdx (fixV E) := by
  classical
  have hEL : E ≤ L₀ := s16c11_v1_aSet_le_right hW hK hdir hE
  have hLX : L₀ ≤ X := by rw [← hdir.2.2]; exact le_sup_right
  have hLK : ∀ l ∈ L₀, ∀ k ∈ K, l * k = k * l :=
    fun l hl k hk => (s16c11_comm_of_isInternalDirect hdir k hk l hl).symm
  obtain ⟨hJ, -⟩ := s16c11_v1_model_pair hM hLX hLK
  let ρ : ↥L₀ →* MulAut ↥J₀ := CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ
  have hρinj : Function.Injective ρ := s16c11_v1_resHom_injective hM hLX hLK hJ
  let H₀ : Subgroup (MulAut ↥J₀) := ρ.range
  have hcover := s16c11_v1_aSet_cover hM hLX hLK hJ hEL hE
  have hĒmem : (E.subgroupOf L₀).map ρ ∈ E3.aSet 2 H₀ := hcover.1
  have hĒne : (E.subgroupOf L₀).map ρ ≠ ⊥ := hĒmem.2.1
  have hrkE : rkIdx (fixV E) = 2 * rkIdx (fixV ((E.subgroupOf L₀).map ρ)) := hcover.2
  have hH₀sym : IsSym ↥H₀ n := by
    obtain ⟨e⟩ := hL₀
    exact ⟨(MonoidHom.ofInjective hρinj).symm.trans e⟩
  have hφ_eq : ∀ x : ↥L,
      φ x = CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨x, hLL₀ x.2⟩ := by
    intro x
    apply MulEquiv.ext
    intro j
    apply Subtype.ext
    simp only [hφ x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply]
  have hφrange : φ.range ≤ H₀ := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨⟨x, hLL₀ x.2⟩, (hφ_eq x).symm⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨a, hLL₀ a.2⟩ =
        CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨b, hLL₀ b.2⟩ := by
      rw [← hφ_eq a, ← hφ_eq b, hab]
    exact Subtype.ext (congrArg (fun z : ↥L₀ => (z : MulAut W)) (hρinj h1))
  have hAlt : UC22.IsAlt ↥φ.range n := by
    obtain ⟨e⟩ := hA
    exact ⟨(MonoidHom.ofInjective hφinj).symm.trans e⟩
  have hReal : (G64.symCoreModel n).Realizes H₀ ⊤ ⊥ :=
    s16c11_v1_symCore_of_altCore hn hφrange hH₀sym hAlt hcomm hR
  obtain ⟨π, hπ⟩ := hReal
  obtain ⟨β, hβ⟩ :=
    G64.RealizesVia.exists_secEquiv (D := G64.symCoreModel n) rfl hπ
  have hcongr : ∀ γ : Equiv.Perm (Fin n), MulAut.congr β (π γ) = G6.coreAct n γ := by
    intro γ
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show Subtype.val (p := fun y => y ∈ (G64.symCoreModel n).sec)
        (β (((π γ : ↥H₀) : MulAut ↥J₀) (β.symm x))) =
      Subtype.val (p := fun y => y ∈ (G64.symCoreModel n).sec) (G6.coreAct n γ x)
    rw [hβ γ (β.symm x), MulEquiv.apply_symm_apply]
    rfl
  have hH₀eq : H₀.map (CFSG.Quasithin.H.congrHom β) = (G6.coreAct n).range := by
    apply le_antisymm
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf
      obtain ⟨γ, hγ⟩ := hπ.1 ⟨g, hg⟩
      have hgπ : g = (π γ : MulAut ↥J₀) := (congrArg Subtype.val hγ).symm
      rw [hgπ]
      exact MonoidHom.mem_range.mpr ⟨γ, (hcongr γ).symm⟩
    · intro f hf
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hf
      exact Subgroup.mem_map.mpr ⟨(π γ : MulAut ↥J₀), (π γ).2, hcongr γ⟩
  let Ē' : Subgroup (MulAut ↥(G6.coreMod n)) :=
    ((E.subgroupOf L₀).map ρ).map (CFSG.Quasithin.H.congrHom β)
  have hĒ'mem : Ē' ∈ E3.aSet 2 (G6.coreAct n).range := by
    have h := (CFSG.Quasithin.H.map_mem_aSet_iff β).mpr hĒmem
    rwa [hH₀eq] at h
  have hĒ'ne : Ē' ≠ ⊥ := by
    intro hbot
    exact hĒne ((Subgroup.map_eq_bot_iff_of_injective _
      (CFSG.Quasithin.H.congrHom_injective β)).mp hbot)
  have hĒ'pg : IsPGroup 2 ↥Ē' := E3.isPGroup_of_isElemAbelian2 hĒ'mem.2.2.1
  have hrk' : rkIdx (fixV Ē') = rkIdx (fixV ((E.subgroupOf L₀).map ρ)) := by
    change rkIdx (fixV (((E.subgroupOf L₀).map ρ).map
      (MulAut.congr β).toMonoidHom)) = rkIdx (fixV ((E.subgroupOf L₀).map ρ))
    rw [E3.fixV_map_congr β ((E.subgroupOf L₀).map ρ),
      E3.rkIdx_map_equiv β (fixV ((E.subgroupOf L₀).map ρ))]
  calc
    2 * m ≤ 2 * rkIdx (fixV Ē') :=
      Nat.mul_le_mul_left 2 (hconc Ē' hĒ'mem hĒ'pg hĒ'ne)
    _ = 2 * rkIdx (fixV ((E.subgroupOf L₀).map ρ)) := by rw [hrk']
    _ = rkIdx (fixV E) := hrkE.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
