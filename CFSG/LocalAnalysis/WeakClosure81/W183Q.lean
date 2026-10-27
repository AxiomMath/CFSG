module

public import CFSG.LocalAnalysis.WeakClosure81.W183Ker182B
public import CFSG.LocalAnalysis.WeakClosure81.W183KernGen
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem centralizes_odd_of_mem_M (c : MinCex183 D V₀ V H i) (M : ModDataE H (eOmegaZ H D.T))
    {Kk : Subgroup ↥(M.img H)}
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {g : G} (hg : g ∈ D.M) {N : Subgroup ↥(M.img H)} (hN : N.Normal) (hNK : N ≤ Kk)
    (hodd : Odd (Nat.card ↥N)) :
    (M.img (vInH V H g)).subgroupOf (M.img H) ≤ Subgroup.centralizer (N : Set ↥(M.img H)) := by
  have hgM : g ∈ Subgroup.normalizer (V : Set G) := by
    rw [c.hyp.setting.normalizer_eq]
    exact hg
  have hconjV : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.mpr hgM
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hy' : (y : LGL 2 M.W) ∈ M.img (vInH V H g) := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨j, hjS, hjy⟩ := M.mem_img.mp hy'
  have hjH : (j : G) ∈ H := (Subgroup.mem_inf.mp hjS).2
  have hjV : (j : G) ∈ V := by
    have h : (j : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.mp hjS).1
    rwa [hconjV] at h
  have hnK : n ∈ Kk := hNK hn
  obtain ⟨k, -, hkn⟩ := M.mem_img.mp n.2
  have hkK : (k : G) ∈ kerMV V H := (hKk k n hkn.symm).1 hnK
  let zH : ↥H := ⁅k, j⁆
  have hzV : (zH : G) ∈ V := by
    have hkM : (k : G) ∈ Subgroup.normalizer (V : Set G) := kerMV_le_normalizer V H hkK
    have hconj : (k : G) * (j : G) * (k : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hkM (j : G)).1 hjV
    have hz : (zH : G) = ((k : G) * (j : G) * (k : G)⁻¹) * (j : G)⁻¹ := by
      change (⁅k, j⁆ : ↥H).1 = _
      rw [commutatorElement_def]
      rfl
    rw [hz]
    exact V.mul_mem hconj (V.inv_mem hjV)
  have hzK : (zH : G) ∈ kerMV V H := by
    have hkinv : (k : G)⁻¹ ∈ kerMV V H := (kerMV V H).inv_mem hkK
    have hconj : (j : G) * (k : G)⁻¹ * (j : G)⁻¹ ∈ kerMV V H := conj_mem_kerMV hjH hkinv
    have hz : (zH : G) = ((k : G) * (j : G) * (k : G)⁻¹) * (j : G)⁻¹ := by
      change (⁅k, j⁆ : ↥H).1 = _
      rw [commutatorElement_def]
      rfl
    rw [hz]
    simpa only [mul_assoc] using (kerMV V H).mul_mem hkK hconj
  let rz : ↥(M.img H) := ⟨M.ρ zH, M.mem_img.mpr ⟨zH, zH.2, rfl⟩⟩
  have hrz_eq : rz = ⁅n, y⁆ := by
    apply Subtype.ext
    show M.ρ zH = (Subgroup.subtype (M.img H)) ⁅n, y⁆
    have h1 : M.ρ zH = ⁅M.ρ k, M.ρ j⁆ := by
      change M.ρ ⁅k, j⁆ = _
      rw [map_commutatorElement]
    rw [h1, hkn, hjy, map_commutatorElement]
    rfl
  have hmem : rz ∈ N := by
    have hcomm : ⁅n, y⁆ ∈ N := by
      have h1 : y * n⁻¹ * y⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) y
      have h2 : n * y * n⁻¹ * y⁻¹ ∈ N := by
        simpa only [mul_assoc] using N.mul_mem hn h1
      simpa only [commutatorElement_def] using h2
    rwa [hrz_eq]
  have hodd_ord : Odd (orderOf rz) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmem)
  have hsq : rz ^ 2 = 1 := by
    apply Subtype.ext
    change (M.ρ zH) ^ 2 = (1 : LGL 2 M.W)
    have hzH2 : zH ^ 2 = 1 := by
      apply Subtype.ext
      change (zH : G) ^ 2 = 1
      exact c.hyp.setting.isElemAbelian.2 (zH : G) hzV
    rw [← map_pow, hzH2, map_one]
  have hord2 : orderOf rz ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hord1 : orderOf rz = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h | h
    · exact h
    · exact absurd (h ▸ hodd_ord) (Nat.not_odd_iff_even.mpr ⟨1, by norm_num⟩)
  have hcomm1 : ⁅n, y⁆ = 1 := by rw [← hrz_eq]; exact orderOf_eq_one_iff.mp hord1
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1

theorem kernel_182 (hB : ListBNonabelian) (h162 : W3Thm162Gt2 G) (h172 : W3Thm172Weak G)
    (h5_4 : Asch5_4) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hgT : vInH V H g ≤ D.T) :
    ∃ Kk F : Subgroup ↥(M.img H), PerfSocleMod Kk F ∧
      (∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
        (r ∈ Kk ↔ (j : G) ∈ kerMV V H)) ∧
      ⁅opResidual 2 (⊤ : Subgroup ↥(M.img H)), opResidual 2 (⊤ : Subgroup ↥(M.img H))⁆ =
        opResidual 2 (⊤ : Subgroup ↥(M.img H)) ∧
      opResidual 2 (⊤ : Subgroup ↥(M.img H)) = F ∧
      Kk ≤ opResidual 2 (⊤ : Subgroup ↥(M.img H)) ∧
      Kk = Subgroup.centralizer (opResidual 2 (⊤ : Subgroup ↥(M.img H)) : Set ↥(M.img H)) ∧
      Odd (Nat.card ↥Kk) := by
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨Kk, F, hsoc, hKk⟩ := c.exists_perfSocleMod_182 h172 h5_4 h5_11 h5_13 h2 M
  have hset := c.kernSetting_of_minCex_182 hB h2 x M hsoc
    (c.kerMV_isSolvable_182 h172 h5_4 h5_11 h5_13 h2) hKk
  refine ⟨Kk, F, hsoc, hKk, ?_⟩
  have hab : ∀ g' : G, IsElemAbelian 2 (vInH V H g') := fun g' =>
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g').mono inf_le_left
  by_cases hbig : ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')
  · obtain ⟨g', hg', hA⟩ := hbig
    obtain ⟨hA2, hA4⟩ := four_le_card_img M inf_le_right (hab g') hA
    exact hset.kern_eq_centralizer hA2 hA4 (x.index_le_two_of_gam183 M hg')
  · have hall : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
        (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') = 2 := by
      intro g' hg'
      have h0 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have h1 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') ≠ 1 := by
        intro h
        rw [Subgroup.relIndex_eq_one] at h
        exact hg'.2 (h.trans le_rfl)
      have h3 : ¬ 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') :=
        fun h => hbig ⟨g', hg', h⟩
      omega
    have hgM : g ∈ D.M := x.mem_M_of_relIndex_two M hall hg hgT
    refine hset.kern_eq_centralizer_of_ne_bot fun N hN hNK hodd => ?_
    refine ⟨(M.img (vInH V H g)).subgroupOf (M.img H), ?_, ?_,
      c.centralizes_odd_of_mem_M M hKk hgM hN hNK hodd⟩
    · have hSH' : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
      exact (M.isPGroup_img (CFSG.Open.IsElemAbelian.isPGroup (hab g))).of_equiv
        (Subgroup.subgroupOfEquivOfLe hSH').symm
    · intro hbot
      have hSH' : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
      have hcard : Nat.card ↥((M.img (vInH V H g)).subgroupOf (M.img H)) =
          Nat.card ↥(M.img (vInH V H g)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH').toEquiv
      rw [hbot, Subgroup.card_bot, M.card_img (S := vInH V H g) inf_le_right, hall g hg] at hcard
      omega

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
