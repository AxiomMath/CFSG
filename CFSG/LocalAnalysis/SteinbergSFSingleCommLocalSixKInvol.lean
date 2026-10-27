module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_k4b_exists_max {Q : Type} [Group Q] [Finite Q] (P : Subgroup Q → Prop)
    {S : Subgroup Q} (hS : P S) : ∃ M : Subgroup Q, S ≤ M ∧ Maximal P M := by
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun S : Subgroup Q => (S : Set Q)) SetLike.coe_injective
  exact Finite.exists_le_maximal hS

theorem sixK_k4b_aux_U_le_A : U φ i ≤ A φ i.swap :=
  pull_mono φ (le_trans (FullCenter.rootU_le_center i) (FullCenter.center_le_rootA i.swap))

theorem sixK_k4b_aux_U_le_Mhat (hH : SixHConclusion φ t i) : U φ i ≤ Mhat φ t i i := by
  rw [← hH.center_Mhat_i]
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem sixK_k4b_aux_U_le_Kc : U φ i ≤ Kc φ t i.swap :=
  le_trans sixK_k4b_aux_U_le_A le_sup_left

theorem sixK_k4b_aux_Kc_le_Mhat_j (hH : SixHConclusion φ t i) :
    Kc φ t i.swap ≤ Mhat φ t i i.swap := by
  rw [← hH.center_Mhat_j]
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem sixK_k4b_aux_Mc_le_Mhat_j : Mc φ t i ≤ Mhat φ t i i.swap :=
  le_sup_left

theorem sixK_k4b_aux_U_le_Mhat_j (hH : SixHConclusion φ t i) : U φ i ≤ Mhat φ t i i.swap :=
  le_trans sixK_k4b_aux_U_le_Kc (sixK_k4b_aux_Kc_le_Mhat_j hH)

theorem sixK_k4b (hH : SixHConclusion φ t i) : K4bConcl φ t i := by
  obtain ⟨hN, hmax⟩ := hH.maximal_Dstar
  intro x hxD hx2
  have hxsub : (⟨x, hxD⟩ : ↥(Dstar φ t i)) ∈ (Dstar φ t i).subgroupOf (Dstar φ t i) :=
    Subgroup.mem_subgroupOf.mpr hxD
  have hxd2 : (⟨x, hxD⟩ : ↥(Dstar φ t i)) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using hx2)
  have hq2 : QuotientGroup.mk' ((U φ i).subgroupOf (Dstar φ t i))
      (⟨x, hxD⟩ : ↥(Dstar φ t i)) ^ 2 = 1 := by
    rw [← map_pow, hxd2, map_one]
  obtain ⟨M, hqM, hMmax⟩ := sixK_k4b_exists_max
    (fun S : Subgroup (↥(Dstar φ t i) ⧸ (U φ i).subgroupOf (Dstar φ t i)) =>
      S ≤ ((Dstar φ t i).subgroupOf (Dstar φ t i)).map
          (QuotientGroup.mk' ((U φ i).subgroupOf (Dstar φ t i))) ∧
        IsElementaryAbelian 2 S)
    (S := Subgroup.zpowers (QuotientGroup.mk' ((U φ i).subgroupOf (Dstar φ t i))
      (⟨x, hxD⟩ : ↥(Dstar φ t i))))
    ⟨by
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_map_of_mem _ hxsub,
      IsElementaryAbelian.zpowers_of_pow_eq_one hq2⟩
  have hqmem : QuotientGroup.mk' ((U φ i).subgroupOf (Dstar φ t i))
      (⟨x, hxD⟩ : ↥(Dstar φ t i)) ∈ M :=
    hqM (Subgroup.mem_zpowers _)
  rcases (hmax M).mp hMmax with hMX | hMY
  · rw [hMX] at hqmem
    obtain ⟨z, hz, hzq⟩ := Subgroup.mem_map.mp hqmem
    simp only [QuotientGroup.mk'_apply] at hzq
    have h1 := QuotientGroup.eq.mp hzq
    have h3 : (z : G)⁻¹ * x ∈ U φ i := by simpa using Subgroup.mem_subgroupOf.mp h1
    have hz' : (z : G) ∈ Mhat φ t i i := Subgroup.mem_subgroupOf.mp hz
    have hmul := mul_mem hz' (sixK_k4b_aux_U_le_Mhat hH h3)
    left
    rwa [mul_inv_cancel_left] at hmul
  · rw [hMY] at hqmem
    obtain ⟨z, hz, hzq⟩ := Subgroup.mem_map.mp hqmem
    simp only [QuotientGroup.mk'_apply] at hzq
    have h1 := QuotientGroup.eq.mp hzq
    have h3 : (z : G)⁻¹ * x ∈ U φ i := by simpa using Subgroup.mem_subgroupOf.mp h1
    have hz' : (z : G) ∈ Mhat φ t i i.swap :=
      sup_le sixK_k4b_aux_Mc_le_Mhat_j (sixK_k4b_aux_Kc_le_Mhat_j hH)
        (Subgroup.mem_subgroupOf.mp hz)
    have hmul := mul_mem hz' (sixK_k4b_aux_U_le_Mhat_j hH h3)
    right
    rwa [mul_inv_cancel_left] at hmul

theorem sixK_k4_aux_norm (hE : EmbConclusion φ t i) {y : G} (hy : y ∈ Ytilde φ i) {m : G}
    (hm : m ∈ Mhat φ t i i) : y * m * y⁻¹ ∈ Mhat φ t i i :=
  (mem_normalizer_iff.mp (hE.Ytilde_le hy) m).mp hm

theorem sixK_k4_aux_norm' (hE : EmbConclusion φ t i) {y : G} (hy : y ∈ Ytilde φ i) {m : G}
    (hm : m ∈ Mhat φ t i i) : y⁻¹ * m * y ∈ Mhat φ t i i :=
  (mem_normalizer_iff''.mp (hE.Ytilde_le hy) m).mp hm

theorem sixK_k4_aux_dec (hE : EmbConclusion φ t i) {x : G}
    (hx : x ∈ Mhat φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom) :
    ∃ m ∈ Mhat φ t i i, ∃ v ∈ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom,
      x = m * v := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨m₁, hm₁, v₁, hv₁, rfl⟩ := ihx
    obtain ⟨m₂, hm₂, v₂, hv₂, rfl⟩ := ihy
    exact ⟨m₁ * (v₁ * m₂ * v₁⁻¹),
      mul_mem hm₁ (sixK_k4_aux_norm hE (hE.Vw_le_Ytilde hv₁) hm₂), v₁ * v₂, mul_mem hv₁ hv₂,
      by group⟩
  | inv x _ ihx =>
    obtain ⟨m, hm, v, hv, rfl⟩ := ihx
    exact ⟨v⁻¹ * m⁻¹ * v⁻¹⁻¹, sixK_k4_aux_norm hE (hE.Vw_le_Ytilde (inv_mem hv)) (inv_mem hm),
      v⁻¹, inv_mem hv, by group⟩

theorem sixK_k4_aux_inv_sq (hE : EmbConclusion φ t i) {m v : G} (hm : m ∈ Mhat φ t i i)
    (hv : v ∈ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom)
    (hx : m * v * (m * v) = 1) : v * v = 1 := by
  have hm' : m⁻¹ = v * m * v := by
    calc m⁻¹ = m⁻¹ * (m * v * (m * v)) := by rw [hx, mul_one]
      _ = v * m * v := by group
  have hc : v * m⁻¹ * v⁻¹ = v * v * m := by
    rw [hm']
    group
  have hsq : v * v ∈
      Mhat φ t i i ⊓ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem hv hv⟩
    have hmem : v * m⁻¹ * v⁻¹ ∈ Mhat φ t i i :=
      sixK_k4_aux_norm hE (hE.Vw_le_Ytilde hv) (inv_mem hm)
    have hv2 : v * v = (v * m⁻¹ * v⁻¹) * m⁻¹ := by
      rw [hc]
      group
    rw [hv2]
    exact mul_mem hmem (inv_mem hm)
  rw [hE.inf_Vw] at hsq
  exact Subgroup.mem_bot.mp hsq

theorem sixK_k4_aux_conj_Vw {v : G}
    (hv : v ∈ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom) :
    w φ i.swap * v * (w φ i.swap)⁻¹ ∈ Vtor φ t i i := by
  obtain ⟨u, hu, hvu⟩ := Subgroup.mem_map.mp hv
  have e : v = (w φ i.swap)⁻¹ * u * w φ i.swap := by
    rw [← hvu]
    simp [MulAut.conj_apply]
  have e' : w φ i.swap * v * (w φ i.swap)⁻¹ = u := by
    rw [e]
    group
  rw [e']
  exact hu

theorem sixK_k4_aux_conj_Y {y₀ : G} (hy₀ : y₀ ∈ Ytor φ i) :
    (w φ i.swap)⁻¹ * y₀ * w φ i.swap ∈ Ytilde φ i := by
  have e : (w φ i.swap)⁻¹ * y₀ * w φ i.swap = (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom y₀ := by
    simp [MulAut.conj_apply]
  rw [e]
  exact Subgroup.mem_map_of_mem _ hy₀

theorem sixK_k4_aux_conj_sq {a g : G} (ha : a * a = 1) : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
  calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    _ = 1 := by rw [ha]; group

theorem sixK_k4 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (k4a : K4aConcl φ i) (k4b : K4bConcl φ t i) :
    K4Concl φ t i := by
  intro x hx hx2
  have hxS : x ∈ Mhat φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom := by
    rw [hE.sup_Vw]
    exact hx
  obtain ⟨m, hm, v, hv, rfl⟩ := sixK_k4_aux_dec hE hxS
  have hv2 : v * v = 1 := sixK_k4_aux_inv_sq hE hm hv hx2
  have huV : w φ i.swap * v * (w φ i.swap)⁻¹ ∈ Vtor φ t i i := sixK_k4_aux_conj_Vw hv
  have huY : w φ i.swap * v * (w φ i.swap)⁻¹ ∈ Ytor φ i :=
    (RootStandard.V_le_Y hS.fc i hS.ne_bot hS.eq_bot i) huV
  have huu : w φ i.swap * v * (w φ i.swap)⁻¹ * (w φ i.swap * v * (w φ i.swap)⁻¹) = 1 :=
    sixK_k4_aux_conj_sq hv2
  obtain ⟨y₀, hy₀, hy₀U⟩ := k4a _ huY huu
  obtain ⟨g, hg⟩ : ∃ g : G, g = (w φ i.swap)⁻¹ * y₀ * w φ i.swap := ⟨_, rfl⟩
  have hyY : g ∈ Ytilde φ i := by
    rw [hg]
    exact sixK_k4_aux_conj_Y hy₀
  have hWN : w φ i.swap ∈ normalizer ((A φ i.swap : Subgroup G) : Set G) :=
    (FullCenterWeyl.w_facts hS.fc i.swap).2.1
  have hWA : (w φ i.swap)⁻¹ * (y₀⁻¹ * (w φ i.swap * v * (w φ i.swap)⁻¹) * y₀) * w φ i.swap
      ∈ A φ i.swap :=
    (mem_normalizer_iff''.mp hWN _).mp (sixK_k4b_aux_U_le_A hy₀U)
  have hM_D : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  have hK_D : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hA_D : A φ i.swap ≤ Dstar φ t i :=
    le_trans (le_sup_left : A φ i.swap ≤ Kc φ t i.swap) hK_D
  have hsplit : g⁻¹ * (m * v) * g = (g⁻¹ * m * g) *
      ((w φ i.swap)⁻¹ * (y₀⁻¹ * (w φ i.swap * v * (w φ i.swap)⁻¹) * y₀) * w φ i.swap) := by
    rw [hg]
    group
  have hgm : g⁻¹ * m * g ∈ Mhat φ t i i := sixK_k4_aux_norm' hE hyY hm
  have hgD : g⁻¹ * (m * v) * g ∈ Dstar φ t i := by
    rw [hsplit]
    exact mul_mem (hM_D hgm) (hA_D hWA)
  have hgD2 : g⁻¹ * (m * v) * g * (g⁻¹ * (m * v) * g) = 1 := by
    rw [show g⁻¹ * (m * v) * g * (g⁻¹ * (m * v) * g) = g⁻¹ * (m * v * (m * v)) * g by group,
      hx2]
    group
  rcases k4b _ hgD hgD2 with h | h
  · exact ⟨g, Or.inl h⟩
  · exact ⟨g, Or.inr h⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
