module

public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

namespace KGA

private theorem f4w_ggHasLabel_of_mulEquiv {lab : LargeEvenLabel} {R R' : Type} [Group R]
    [Group R'] (e : R ≃* R') (h : GGHasLabel lab R) : GGHasLabel lab R' :=
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨e.symm.trans f⟩) h

theorem ggF4_fix_one_not_c3 (hRig : GGLabelRigidInput) {f : ℕ} (hf : 1 ≤ f) {R : Type} [Group R]
    [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) (hF4 : GGHasLabel ⟨.F4, 4, f⟩ R)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub (1 : MulAut L')))
    (hC3 : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) : False := by
  have hfix : ggFixSub (1 : MulAut L') = ⊤ := by
    ext l
    simp [mem_ggFixSub]
  have hJtop : IsComponentOf J ⊤ := by rwa [hfix] at hJ
  obtain ⟨_, hJsub, hJq⟩ := hJtop
  have hmap : IsSubnormal (J.map ψ) ((⊤ : Subgroup L').map ψ) := hJsub.map ψ
  have htopmap : (⊤ : Subgroup L').map ψ = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ]
  have hsub : IsSubnormal (J.map ψ) ⊤ := by rwa [htopmap] at hmap
  rcases CFSG.Assembly.IsSubnormal.eq_bot_or_top hsub with hbot | htop
  · exfalso
    have hJker : J ≤ ψ.ker := (Subgroup.map_eq_bot_iff J).mp hbot
    have hJcent : J ≤ Subgroup.center L' := hJker.trans hker
    have hJab : ∀ x y : J, x * y = y * x := by
      intro x y
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hJcent x.2) (y : L')).symm
    have hcenterJ : Subgroup.center J = ⊤ := by
      ext x
      simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
      intro y
      exact hJab y x
    haveI : Subsingleton (J ⧸ Subgroup.center J) := by
      rw [hcenterJ]
      exact QuotientGroup.subsingleton_iff.mpr rfl
    haveI : Nontrivial (J ⧸ Subgroup.center J) := hJq.2.toNontrivial
    exact (not_subsingleton (J ⧸ Subgroup.center J)) inferInstance
  · have hJtop' : J = ⊤ := by
      apply le_antisymm le_top
      rw [← hperf]
      rw [commutator_def]
      rw [Subgroup.commutator_le]
      intro l₁ _ l₂ _
      have hψl₁ : ψ l₁ ∈ J.map ψ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨j₁, hj₁, hψj₁⟩ := (Subgroup.mem_map).mp hψl₁
      have hψl₂ : ψ l₂ ∈ J.map ψ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨j₂, hj₂, hψj₂⟩ := (Subgroup.mem_map).mp hψl₂
      have hz₁ : j₁⁻¹ * l₁ ∈ Subgroup.center L' := by
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψj₁]
        exact inv_mul_cancel (ψ l₁)
      have hz₂ : j₂⁻¹ * l₂ ∈ Subgroup.center L' := by
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψj₂]
        exact inv_mul_cancel (ψ l₂)
      have hcomm_eq : ⁅l₁, l₂⁆ = ⁅j₁, j₂⁆ := by
        rw [show l₁ = j₁ * (j₁⁻¹ * l₁) by group,
          show l₂ = j₂ * (j₂⁻¹ * l₂) by group]
        exact ggComm_mul_central _ _ _ _ hz₁ hz₂
      rw [hcomm_eq]
      exact Subgroup.commutator_le_self J
        (Subgroup.commutator_mem_commutator hj₁ hj₂)
    have hZR : Subgroup.center R = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hker_center : ψ.ker = Subgroup.center L' := by
      apply le_antisymm hker
      intro x hx
      rw [MonoidHom.mem_ker]
      have hxR : ψ x ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨l, rfl⟩ := hψ y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp hx l
      rw [hZR] at hxR
      simpa using hxR
    have hL'R : L' ⧸ Subgroup.center L' ≃* R :=
      (QuotientGroup.quotientMulEquivOfEq hker_center.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    have hcenterJtop : Subgroup.map
        (Subgroup.topEquiv (G := L') : ↥(⊤ : Subgroup L') →* L')
        (Subgroup.center (⊤ : Subgroup L')) = Subgroup.center L' := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro z
        have h := hy (Subgroup.topEquiv.symm z)
        simpa using congrArg (Subgroup.topEquiv (G := L')) h
      · intro hx
        rw [Subgroup.mem_map]
        refine ⟨Subgroup.topEquiv.symm x, ?_, by simp⟩
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro z
        apply Subgroup.topEquiv.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hx (Subgroup.topEquiv z)
    have hJcenter : J ⧸ Subgroup.center J ≃* L' ⧸ Subgroup.center L' := by
      subst hJtop'
      exact QuotientGroup.congr (Subgroup.center (⊤ : Subgroup L'))
        (Subgroup.center L') (Subgroup.topEquiv (G := L')) hcenterJtop
    have h3' : GGHasLabel ⟨.C, 3, f⟩ (L' ⧸ Subgroup.center L') :=
      f4w_ggHasLabel_of_mulEquiv hJcenter hC3
    have h3R : GGHasLabel ⟨.C, 3, f⟩ R := f4w_ggHasLabel_of_mulEquiv hL'R h3'
    have h := hRig ⟨.F4, 0, f⟩ ⟨.C, 3, f⟩ R ⟨hf, rfl⟩
      ⟨hf, by norm_num, by norm_num⟩ hF4 h3R
    simp [GGLabelIso] at h

theorem kga_rank_label
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.C, 3, f⟩ fun R _ I _ => GGTorusSCRank p 3 R I := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hK
  have hKq : p ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact hpq
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hfac : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    obtain ⟨q, hq'⟩ : ∃ q, Nat.card K = q + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hq']
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rcases (Nat.Prime.dvd_mul hp).1 (hfac ▸ hKq) with h | h
  · exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusSCRank_sp (m := 3) (by norm_num) hp h⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ',
      kga_torusSCRank_split (m := 3) (by norm_num) hp hp2 h⟩

end KGA

end CFSG.StandardType

end
