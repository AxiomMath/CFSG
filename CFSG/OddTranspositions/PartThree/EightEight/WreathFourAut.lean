module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.PartThree.EightEight.WreathThreeAut
import CFSG.GroupTheory.CentralizerSwapMulEquiv
import CFSG.GroupTheory.MulAutCongr
import CFSG.Quasithin.Recognition.HSTypeOutS5
import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartThree.WreathEndgame

theorem perm4_commute_of_commute_swap {τ σ₁ σ₂ : Equiv.Perm (Fin 4)} (hτ : τ.IsSwap)
    (h₁ : Commute σ₁ τ) (h₂ : Commute σ₂ τ) : Commute σ₁ σ₂ := by
  obtain ⟨i, j, hij, rfl⟩ := hτ
  have hcard : Fintype.card {x : Fin 4 // x ≠ i ∧ x ≠ j} = 2 := by
    have hcompl : Fintype.card {x : Fin 4 // x ≠ i ∧ x ≠ j} =
        Fintype.card (Fin 4) - Fintype.card {x : Fin 4 // x = i ∨ x = j} := by
      simpa only [not_or] using
        (Fintype.card_subtype_compl (α := Fin 4) (p := fun x => x = i ∨ x = j))
    rw [hcompl, Fintype.card_fin, Fintype.card_subtype_eq_or_eq_of_ne hij]
  obtain ⟨e⟩ := CFSG.GroupTheory.nonempty_centralizer_swap_mulEquiv (m := 4) i j hij
  have hPermTwo : IsMulCommutative (Equiv.Perm (Fin 2)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (by simp)
  have hPermComp : IsMulCommutative (Equiv.Perm {x : Fin 4 // x ≠ i ∧ x ≠ j}) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (by
      rw [Nat.card_eq_fintype_card, hcard])
  have hProd : IsMulCommutative (Equiv.Perm (Fin 2) ×
      Equiv.Perm {x : Fin 4 // x ≠ i ∧ x ≠ j}) := by
    refine IsMulCommutative.of_comm ?_
    intro x y
    apply Prod.ext
    · exact hPermTwo.is_comm.comm x.1 y.1
    · exact hPermComp.is_comm.comm x.2 y.2
  have hCent : IsMulCommutative
      ↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 4)))) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    apply e.injective
    rw [map_mul, map_mul]
    exact hProd.is_comm.comm (e a) (e b)
  have hσ₁ : σ₁ ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 4))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h₁
  have hσ₂ : σ₂ ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 4))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h₂
  have h := hCent.is_comm.comm
    (⟨σ₁, hσ₁⟩ : ↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 4)))))
    (⟨σ₂, hσ₂⟩ : ↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 4)))))
  exact Subtype.ext_iff.mp h

private theorem conj_swap_ne_one_four_w4a {τ : Equiv.Perm (Fin 4)} (hτ : τ.IsSwap) :
    MulAut.conj τ ≠ 1 := by
  obtain ⟨i, j, hij, rfl⟩ := hτ
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt (i := i) (j := j) (by norm_num)
  have hnc : ¬ Commute (Equiv.swap i j) (Equiv.swap k j) := by
    intro hc
    have h := congrArg (fun σ : Equiv.Perm (Fin 4) => σ k) hc.eq
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hki hkj] at h
    exact hij h
  intro hconj
  apply hnc
  have hρ : (MulAut.conj (Equiv.swap i j)) (Equiv.swap k j) = Equiv.swap k j := by
    rw [hconj, MulAut.one_apply]
  rw [MulAut.conj_apply] at hρ
  show Equiv.swap i j * Equiv.swap k j = Equiv.swap k j * Equiv.swap i j
  calc
    Equiv.swap i j * Equiv.swap k j =
        (Equiv.swap i j * Equiv.swap k j * (Equiv.swap i j)⁻¹) * Equiv.swap i j := by group
    _ = Equiv.swap k j * Equiv.swap i j := by rw [hρ]

private theorem rightAut_mem_map_centralizer_w4a {f : ℕ} (hf : 2 ≤ f) {t : L2Wreath f 4}
    {ψ : MulAut (L2Wreath f 4)} (hψ : ψ t = t) :
    rightAut (f := f) (n := 4) hf (by norm_num) ψ ∈
      (Subgroup.centralizer ({t.right} : Set (Equiv.Perm (Fin 4)))).map
        (MulAut.conj : Equiv.Perm (Fin 4) →* MulAut (Equiv.Perm (Fin 4))) := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.HSType.perm_four_aut_inner
    (rightAut (f := f) (n := 4) hf (by norm_num) ψ)
  have hfix : rightAut (f := f) (n := 4) hf (by norm_num) ψ t.right = t.right :=
    rightAut_apply_right_of_fixed hf (by norm_num) hψ
  have hcomm : Commute g t.right := by
    show g * t.right = t.right * g
    calc
      g * t.right = (g * t.right * g⁻¹) * g := by group
      _ = t.right * g := by rw [← hg t.right, hfix]
  refine Subgroup.mem_map.mpr ⟨g, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  · apply MulEquiv.ext
    intro σ
    rw [MulAut.conj_apply]
    exact (hg σ).symm

private theorem map_centralizer_isMulCommutative_w4a {τ : Equiv.Perm (Fin 4)}
    (hτ : τ.IsSwap) :
    IsMulCommutative
      ((Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 4)))).map
        (MulAut.conj : Equiv.Perm (Fin 4) →* MulAut (Equiv.Perm (Fin 4)))) := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  obtain ⟨ga, hga, hgaeq⟩ := Subgroup.mem_map.mp a.2
  obtain ⟨gb, hgb, hgbeq⟩ := Subgroup.mem_map.mp b.2
  rw [← hgaeq, ← hgbeq]
  have hcomm : Commute ga gb :=
    perm4_commute_of_commute_swap hτ
      (Subgroup.mem_centralizer_singleton_iff.mp hga)
      (Subgroup.mem_centralizer_singleton_iff.mp hgb)
  calc
    MulAut.conj ga * MulAut.conj gb = MulAut.conj (ga * gb) := by rw [map_mul]
    _ = MulAut.conj (gb * ga) := by rw [hcomm.eq]
    _ = MulAut.conj gb * MulAut.conj ga := by rw [map_mul]

theorem conj_notMem_commutator_stabilizer_four {f : ℕ} (hf : 2 ≤ f) {t : L2Wreath f 4}
    (ht : t ∈ swapSet f 4) :
    MulAut.conj t ∉ ⁅MulAction.stabilizer (MulAut (L2Wreath f 4)) t,
      MulAction.stabilizer (MulAut (L2Wreath f 4)) t⁆ := by
  intro hmem
  obtain ⟨i, j, hij, hr, -, -⟩ := ht
  have hτ : t.right.IsSwap := by
    rw [hr]
    exact Equiv.Perm.swap_isSwap_iff.mpr hij
  let H : Subgroup (MulAut (L2Wreath f 4)) :=
    MulAction.stabilizer (MulAut (L2Wreath f 4)) t
  let K : Subgroup (MulAut (Equiv.Perm (Fin 4))) :=
    (Subgroup.centralizer ({t.right} : Set (Equiv.Perm (Fin 4)))).map
      (MulAut.conj : Equiv.Perm (Fin 4) →* MulAut (Equiv.Perm (Fin 4)))
  let rA : MulAut (L2Wreath f 4) →* MulAut (Equiv.Perm (Fin 4)) :=
    rightAut (f := f) (n := 4) hf (by norm_num)
  have hKcomm : ⁅K, K⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr (map_centralizer_isMulCommutative_w4a hτ)
  have hHK : H.map rA ≤ K := by
    rintro φ ⟨ψ, hψ, rfl⟩
    exact rightAut_mem_map_centralizer_w4a hf (MulAction.mem_stabilizer_iff.mp hψ)
  have hmap : ⁅H, H⁆.map rA ≤ ⁅K, K⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHK hHK
  have hmapmem : rA (MulAut.conj t) ∈ ⁅H, H⁆.map rA :=
    Subgroup.mem_map.mpr ⟨MulAut.conj t, hmem, rfl⟩
  have hmemK : rA (MulAut.conj t) ∈ ⁅K, K⁆ := hmap hmapmem
  rw [hKcomm, Subgroup.mem_bot] at hmemK
  rw [rightAut_conj (f := f) (n := 4) hf (by norm_num) t, hr] at hmemK
  exact conj_swap_ne_one_four_w4a (Equiv.Perm.swap_isSwap_iff.mpr hij) hmemK

theorem map_ne_conj_of_mem_commutator_four {f : ℕ} (hf : 2 ≤ f) {Γ : Type*} [Group Γ]
    (Φ : Γ →* MulAut (L2Wreath f 4)) {t : L2Wreath f 4} (ht : t ∈ swapSet f 4)
    {S : Subgroup Γ} (hS : ∀ γ ∈ S, Φ γ t = t) {γ₀ : Γ} (hγ₀ : γ₀ ∈ ⁅S, S⁆) :
    Φ γ₀ ≠ MulAut.conj t := by
  intro h
  let H : Subgroup (MulAut (L2Wreath f 4)) :=
    MulAction.stabilizer (MulAut (L2Wreath f 4)) t
  have hSH : S.map Φ ≤ H := by
    intro φ hφ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hφ
    rw [MulAction.mem_stabilizer_iff]
    simpa using hS γ hγ
  have hmem : Φ γ₀ ∈ ⁅H, H⁆ := by
    have hc : Φ γ₀ ∈ (⁅S, S⁆).map Φ :=
      Subgroup.mem_map.mpr ⟨γ₀, hγ₀, rfl⟩
    rw [Subgroup.map_commutator] at hc
    exact Subgroup.commutator_mono hSH hSH hc
  rw [h] at hmem
  exact conj_notMem_commutator_stabilizer_four hf ht hmem

private theorem conj_inv_mul_conj_eq_w4a {G : Type*} [Group G] {K : Subgroup G}
    {d z : G} (hz : z ∈ K) (hd : ∀ y ∈ K, Commute d y) (x : K) :
    (d⁻¹ * z) * (x : G) * (d⁻¹ * z)⁻¹ = z * (x : G) * z⁻¹ := by
  have hdz : Commute d z := hd z hz
  have hdx : Commute d (x : G) := hd x x.2
  have hy : Commute d (z * (x : G) * z⁻¹) :=
    (hdz.mul_right hdx).mul_right hdz.inv_right
  calc
    (d⁻¹ * z) * (x : G) * (d⁻¹ * z)⁻¹ = d⁻¹ * (z * (x : G) * z⁻¹) * d := by group
    _ = z * (x : G) * z⁻¹ := hy.inv_mul_cancel

private theorem mapQuotient_normalizerMonoidHom_eq_conj_w4a
    {G : Type*} [Group G] {K : Subgroup G} {N : Subgroup K} [N.Characteristic]
    {d z : G} (hz : z ∈ K) (hd : ∀ y ∈ K, Commute d y)
    (γ : Subgroup.normalizer (K : Set G)) (hγ : (γ : G) = d⁻¹ * z) :
    MulAut.mapQuotient N (Subgroup.normalizerMonoidHom (H := K) γ) =
      MulAut.conj (QuotientGroup.mk' N ⟨z, hz⟩) := by
  apply MulEquiv.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [QuotientGroup.mk'_apply, MulAut.mapQuotient_mk, MulAut.conj_apply]
  have hx : (Subgroup.normalizerMonoidHom (H := K) γ) x =
      ⟨z * (x : G) * z⁻¹, K.mul_mem (K.mul_mem hz x.2) (K.inv_mem hz)⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hγ]
    exact conj_inv_mul_conj_eq_w4a hz hd x
  rw [hx]
  change QuotientGroup.mk' N ⟨z * (x : G) * z⁻¹, _⟩ =
    QuotientGroup.mk' N ⟨z, hz⟩ * QuotientGroup.mk' N x *
      (QuotientGroup.mk' N ⟨z, hz⟩)⁻¹
  rw [← map_inv, ← map_mul]
  apply congrArg (QuotientGroup.mk' N)
  exact Subtype.ext rfl

private theorem normalizerMonoidHom_apply_fixed_of_commute_w4a
    {G : Type*} [Group G] {K : Subgroup G} {z : G} (hz : z ∈ K)
    {R : Subgroup G} {γ : Subgroup.normalizer (K : Set G)}
    (hγ : (γ : G) ∈ R) (hRz : ∀ r ∈ R, Commute r z) :
    (Subgroup.normalizerMonoidHom (H := K) γ) ⟨z, hz⟩ = ⟨z, hz⟩ := by
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hc : Commute (γ : G) z := hRz (γ : G) hγ
  calc
    (γ : G) * z * (γ : G)⁻¹ = z * (γ : G) * (γ : G)⁻¹ := by rw [hc.eq]
    _ = z := by group

theorem inv_mul_notMem_of_mem_swapSet {G : Type*} [Group G] {K : Subgroup G}
    {N : Subgroup K} [N.Characteristic] {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (K ⧸ N) ≃* L2Wreath f k)
    {R : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : ⁅R, R⁆ = R) {d : G}
    (hd : ∀ x ∈ K, Commute d x) {z : K} (hz : φ (QuotientGroup.mk' N z) ∈ swapSet f k)
    (hRz : ∀ r ∈ R, Commute r (z : G)) : d⁻¹ * (z : G) ∉ R := by
  intro hgR
  let Γ : Subgroup G := Subgroup.normalizer (K : Set G)
  let S : Subgroup Γ := R.subgroupOf Γ
  let t : L2Wreath f k := φ (QuotientGroup.mk' N z)
  let g : G := d⁻¹ * (z : G)
  have hgR' : g ∈ R := hgR
  have hgΓ : g ∈ Γ := hRK hgR'
  let gΓ : Γ := ⟨g, hgΓ⟩
  let Φ : Γ →* MulAut (L2Wreath f k) :=
    (MulAut.congr φ).toMonoidHom.comp
      ((MulAut.mapQuotient N).comp (Subgroup.normalizerMonoidHom (H := K)))
  have hS : ∀ γ ∈ S, Φ γ t = t := by
    intro γ hγ
    have hrR : (γ : G) ∈ R := Subgroup.mem_subgroupOf.mp hγ
    have hfix : (Subgroup.normalizerMonoidHom (H := K) γ) z = z :=
      normalizerMonoidHom_apply_fixed_of_commute_w4a z.2 hrR hRz
    have hαγ : (MulAut.mapQuotient N) (Subgroup.normalizerMonoidHom (H := K) γ)
        (QuotientGroup.mk' N z) = QuotientGroup.mk' N z := by
      rw [QuotientGroup.mk'_apply, MulAut.mapQuotient_mk, hfix]
    calc
      Φ γ t = (MulAut.congr φ) ((MulAut.mapQuotient N)
          (Subgroup.normalizerMonoidHom (H := K) γ)) (φ (QuotientGroup.mk' N z)) := rfl
      _ = φ ((MulAut.mapQuotient N) (Subgroup.normalizerMonoidHom (H := K) γ)
          (QuotientGroup.mk' N z)) := by simp [MulAut.congr_apply]
      _ = φ (QuotientGroup.mk' N z) := by rw [hαγ]
      _ = t := rfl
  have hperf : ⁅S, S⁆ = S := by
    refine Subgroup.map_injective (f := Γ.subtype) Γ.subtype_injective ?_
    rw [CFSG.commutator_subgroupOf_map_eq Γ R R hRK hRK, hR,
      Subgroup.map_subgroupOf_eq_of_le hRK]
  have hα : MulAut.mapQuotient N (Subgroup.normalizerMonoidHom (H := K) gΓ) =
      MulAut.conj (QuotientGroup.mk' N z) :=
    mapQuotient_normalizerMonoidHom_eq_conj_w4a z.2 hd gΓ rfl
  have hΦg : Φ gΓ = MulAut.conj t := by
    change (MulAut.congr φ) ((MulAut.mapQuotient N)
      (Subgroup.normalizerMonoidHom (H := K) gΓ)) = MulAut.conj t
    rw [hα, CFSG.mulAut_congr_conj]
  have hgS : gΓ ∈ S := Subgroup.mem_subgroupOf.mpr hgR'
  have hgComm : gΓ ∈ ⁅S, S⁆ := by
    rw [hperf]
    exact hgS
  rcases hk with rfl | rfl
  · exact (map_ne_conj_of_mem_commutator (f := f) hf Φ hz hS hgComm) hΦg
  · exact (map_ne_conj_of_mem_commutator_four (f := f) hf Φ hz hS hgComm) hΦg

end CFSG.OddTranspositions.PartThree.EightEight
