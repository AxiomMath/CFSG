module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.WreathBaseMinimal
import CFSG.Timmesfeld.Bridge.Asc72WreathConn
import CFSG.Quasithin.Background.G118S3
import CFSG.Quasithin.H13.GoldschmidtM22EndS3

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.Asc72.WreathConn
open CFSG.OddTranspositions.PartThree.WreathEndgame

theorem map_l2WreathBase {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) (ψ : MulAut (L2Wreath f n)) :
    (l2WreathBase f n).map ψ.toMonoidHom = l2WreathBase f n := by
  have hmin : CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal (l2WreathBase f n) := by
    simpa [l2WreathBase] using CFSG.OddTranspositions.base_isMinimalNormal f n hf hn
  refine eq_l2WreathBase_of_isMinimalNormal hf hn ?_
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact CFSG.OddTranspositions.IsMinimalNormal.comap_mulEquiv ψ.symm hmin

theorem right_apply_eq {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) (ψ : MulAut (L2Wreath f n))
    (g : L2Wreath f n) : (ψ g).right = (ψ (SemidirectProduct.inr g.right)).right := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  rw [map_mul, SemidirectProduct.mul_right]
  have hmem : ψ (SemidirectProduct.inl g.left) ∈ l2WreathBase f n := by
    have hmap : ψ (SemidirectProduct.inl g.left) ∈
        (l2WreathBase f n).map ψ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨SemidirectProduct.inl g.left, ⟨g.left, rfl⟩, rfl⟩
    rwa [map_l2WreathBase hf hn ψ] at hmap
  have hright : (ψ (SemidirectProduct.inl g.left)).right = 1 := by
    have hker : ψ (SemidirectProduct.inl g.left) ∈
        (SemidirectProduct.rightHom : L2Wreath f n →* Equiv.Perm (Fin n)).ker := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      simpa [l2WreathBase] using hmem
    simpa using MonoidHom.mem_ker.mp hker
  rw [hright, one_mul]

@[expose] noncomputable def rightAutFun {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n)
    (ψ : MulAut (L2Wreath f n)) : MulAut (Equiv.Perm (Fin n)) where
  toFun σ := (ψ (SemidirectProduct.inr σ)).right
  invFun σ := ((ψ⁻¹) (SemidirectProduct.inr σ)).right
  left_inv σ := by
    change ((ψ⁻¹) (SemidirectProduct.inr ((ψ (SemidirectProduct.inr σ)).right))).right = σ
    rw [← right_apply_eq hf hn ψ⁻¹ (ψ (SemidirectProduct.inr σ))]
    simp
  right_inv σ := by
    change ((ψ) (SemidirectProduct.inr (((ψ⁻¹) (SemidirectProduct.inr σ)).right))).right = σ
    rw [← right_apply_eq hf hn ψ (ψ⁻¹ (SemidirectProduct.inr σ))]
    simp
  map_mul' := by
    intro σ τ
    rw [map_mul (SemidirectProduct.inr : Equiv.Perm (Fin n) →* L2Wreath f n) σ τ,
      map_mul, SemidirectProduct.mul_right]

@[expose] noncomputable def rightAut {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) :
    MulAut (L2Wreath f n) →* MulAut (Equiv.Perm (Fin n)) where
  toFun := rightAutFun (f := f) (n := n) hf hn
  map_one' := by
    ext σ
    simp [rightAutFun]
  map_mul' := by
    intro ψ₁ ψ₂
    apply MulEquiv.ext
    intro σ
    change (ψ₁ (ψ₂ (SemidirectProduct.inr σ))).right =
      (ψ₁ (SemidirectProduct.inr ((ψ₂ (SemidirectProduct.inr σ)).right))).right
    exact right_apply_eq hf hn ψ₁ (ψ₂ (SemidirectProduct.inr σ))

@[simp] theorem rightAut_apply {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n)
    (ψ : MulAut (L2Wreath f n)) (σ : Equiv.Perm (Fin n)) :
    rightAut hf hn ψ σ = (ψ (SemidirectProduct.inr σ)).right := rfl

theorem right_apply_eq_rightAut {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n)
    (ψ : MulAut (L2Wreath f n)) (g : L2Wreath f n) :
    (ψ g).right = rightAut hf hn ψ g.right := by
  rw [right_apply_eq hf hn ψ g, rightAut_apply]

theorem rightAut_apply_right_of_fixed {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) {t : L2Wreath f n}
    {ψ : MulAut (L2Wreath f n)} (hψ : ψ t = t) : rightAut hf hn ψ t.right = t.right := by
  rw [← right_apply_eq_rightAut, hψ]

theorem conj_swap_ne_one {τ : Equiv.Perm (Fin 3)} (hτ : τ.IsSwap) :
    MulAut.conj τ ≠ 1 := by
  obtain ⟨ρ, hρ⟩ := CFSG.Quasithin.H13.GM22.perm3_exists_noncomm τ
    (Equiv.Perm.card_support_eq_two.mpr hτ)
  intro h
  apply hρ
  have h1 : τ * ρ * τ⁻¹ = ρ := by
    have := DFunLike.congr_fun h ρ
    rwa [MulAut.conj_apply, MulAut.one_apply] at this
  calc ρ * τ = τ * ρ * τ⁻¹ * τ := by rw [h1]
    _ = τ * ρ := inv_mul_cancel_right _ _

theorem perm3_aut_eq_one_or_conj_of_fixed {τ : Equiv.Perm (Fin 3)} (hτ : τ.IsSwap)
    {φ : MulAut (Equiv.Perm (Fin 3))} (hφ : φ τ = τ) :
    φ = 1 ∨ φ = MulAut.conj τ := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner φ
  have hgτ : g * τ * g⁻¹ = τ := by
    rw [← hg τ, hφ]
  have hcomm : g * τ = τ * g := by
    have h := congrArg (fun x : Equiv.Perm (Fin 3) => x * g) hgτ
    simpa [mul_assoc] using h
  have hgcase := CFSG.Quasithin.H13.GM22.perm3_centralizer_swap τ g
    (Equiv.Perm.card_support_eq_two.mpr hτ) hcomm
  rcases hgcase with rfl | rfl
  · left
    apply MulEquiv.ext
    intro x
    simpa using hg x
  · right
    apply MulEquiv.ext
    intro x
    simpa [MulAut.conj_apply] using hg x

theorem rightAut_eq_one_or_conj_of_fixed {f : ℕ} (hf : 2 ≤ f) {t : L2Wreath f 3}
    (ht : t ∈ swapSet f 3) {ψ : MulAut (L2Wreath f 3)} (hψ : ψ t = t) :
    rightAut (f := f) (n := 3) hf (by norm_num) ψ = 1 ∨
      rightAut (f := f) (n := 3) hf (by norm_num) ψ = MulAut.conj t.right := by
  obtain ⟨i, j, hij, hr, -, -⟩ := ht
  have hτ : t.right.IsSwap := by
    rw [hr]
    exact Equiv.Perm.swap_isSwap_iff.mpr hij
  exact perm3_aut_eq_one_or_conj_of_fixed hτ (rightAut_apply_right_of_fixed hf (by norm_num) hψ)

theorem rightAut_mem_zpowers_of_fixed {f : ℕ} (hf : 2 ≤ f) {t : L2Wreath f 3}
    (ht : t ∈ swapSet f 3) {ψ : MulAut (L2Wreath f 3)} (hψ : ψ t = t) :
    rightAut (f := f) (n := 3) hf (by norm_num) ψ ∈ Subgroup.zpowers (MulAut.conj t.right) := by
  rcases rightAut_eq_one_or_conj_of_fixed hf ht hψ with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _

theorem rightAut_conj {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n) (g : L2Wreath f n) :
    rightAut hf hn (MulAut.conj g) = MulAut.conj g.right := by
  apply MulEquiv.ext
  intro σ
  calc
    rightAut hf hn (MulAut.conj g) σ = ((MulAut.conj g) (SemidirectProduct.inr σ)).right :=
      rfl
    _ = (g * SemidirectProduct.inr σ * g⁻¹).right := by rw [MulAut.conj_apply]
    _ = g.right * σ * g.right⁻¹ := conj_inr_right g σ
    _ = (MulAut.conj g.right) σ := by rw [MulAut.conj_apply]

theorem conj_notMem_commutator_stabilizer {f : ℕ} (hf : 2 ≤ f) {t : L2Wreath f 3}
    (ht : t ∈ swapSet f 3) :
    MulAut.conj t ∉ ⁅MulAction.stabilizer (MulAut (L2Wreath f 3)) t,
      MulAction.stabilizer (MulAut (L2Wreath f 3)) t⁆ := by
  intro hmem
  let H : Subgroup (MulAut (L2Wreath f 3)) := MulAction.stabilizer (MulAut (L2Wreath f 3)) t
  let K : Subgroup (MulAut (Equiv.Perm (Fin 3))) :=
    Subgroup.zpowers (MulAut.conj t.right)
  have ht' : t ∈ swapSet f 3 := ht
  obtain ⟨i, j, hij, hr, -, -⟩ := ht
  have hτ : t.right.IsSwap := by
    rw [hr]
    exact Equiv.Perm.swap_isSwap_iff.mpr hij
  let rA : MulAut (L2Wreath f 3) →* MulAut (Equiv.Perm (Fin 3)) :=
    rightAut (f := f) (n := 3) hf (by norm_num)
  have hHK : H.map rA ≤ K := by
    rintro φ ⟨ψ, hψ, rfl⟩
    exact rightAut_mem_zpowers_of_fixed hf ht'
      (by simpa using MulAction.mem_stabilizer_iff.mp hψ)
  have hcommK : ⁅K, K⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr (Subgroup.zpowers_isMulCommutative _)
  have hmap : ⁅H, H⁆.map rA ≤ ⁅K, K⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHK hHK
  have hconjmem : MulAut.conj t ∈ ⁅H, H⁆ := hmem
  have hmapmem : rA (MulAut.conj t) ∈ ⁅H, H⁆.map rA :=
    Subgroup.mem_map.mpr ⟨MulAut.conj t, hconjmem, rfl⟩
  have hmemK : rA (MulAut.conj t) ∈ ⁅K, K⁆ := hmap hmapmem
  rw [hcommK, Subgroup.mem_bot] at hmemK
  rw [rightAut_conj (f := f) (n := 3) hf (by norm_num) t, hr] at hmemK
  exact (conj_swap_ne_one (Equiv.Perm.swap_isSwap_iff.mpr hij)) hmemK

theorem map_ne_conj_of_mem_commutator {f : ℕ} (hf : 2 ≤ f) {Γ : Type*} [Group Γ]
    (Φ : Γ →* MulAut (L2Wreath f 3)) {t : L2Wreath f 3} (ht : t ∈ swapSet f 3)
    {S : Subgroup Γ} (hS : ∀ γ ∈ S, Φ γ t = t) {γ₀ : Γ} (hγ₀ : γ₀ ∈ ⁅S, S⁆) :
    Φ γ₀ ≠ MulAut.conj t := by
  intro h
  let H : Subgroup (MulAut (L2Wreath f 3)) := MulAction.stabilizer (MulAut (L2Wreath f 3)) t
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
  exact conj_notMem_commutator_stabilizer hf ht hmem

end CFSG.OddTranspositions.PartThree.EightEight
