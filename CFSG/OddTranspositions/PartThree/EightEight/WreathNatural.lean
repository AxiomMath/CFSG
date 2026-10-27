module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.Timmesfeld.Bridge.Asc72Basic
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.Asc72BenderInvolution
import CFSG.GroupTheory.SmallSymmetric

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open Equiv SemidirectProduct
open CFSG.OddTranspositions.PartThree.WreathClass
open CFSG.OddTranspositions.PartThree.WreathEndgame

variable {f : ℕ}

theorem pow_three_left (P : L2Wreath f 3) (p : Fin 3) :
    (P ^ 3).left p = P.left p * P.left (P.right⁻¹ p) * P.left ((P.right ^ 2)⁻¹ p) := by
  rw [show P ^ 3 = (P * P) * P by rw [pow_succ, pow_two]]
  rw [CFSG.OddTranspositions.PartThree.WreathClass.mul_left_apply]
  rw [show (P * P).right = P.right ^ 2 by simp [pow_two]]
  rw [CFSG.OddTranspositions.PartThree.WreathClass.mul_left_apply]

theorem cube_eq_inl_of_three {P : L2Wreath f 3} {s t : PSL2Model f} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hPr : P.right = swap i j * swap j k)
    (hPi : P.left i = 1) (hPj : P.left j = t) (hPk : P.left k = s)
    (hst : s * t = t * s) : P ^ 3 = inl (fun _ => t * s) := by
  have hcyc : (swap i j * swap j k).IsThreeCycle := by
    simpa [Equiv.swap_comm] using
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := j) (b := i) (c := k)
        hij.symm hjk hik
  have hρ3 : (swap i j * swap j k : Perm (Fin 3)) ^ 3 = 1 := by
    simpa [hcyc.orderOf] using pow_orderOf_eq_one (swap i j * swap j k : Perm (Fin 3))
  have hQr : (P ^ 3).right = 1 := by
    change SemidirectProduct.rightHom (P ^ 3) = 1
    rw [map_pow]
    change P.right ^ 3 = 1
    rw [hPr, hρ3]
  obtain ⟨hρii, hρij, hρik, hρ2i, hρ2j, hρ2k⟩ :=
    CFSG.GroupTheory.swap_mul_swap_same_inv_apply_fin_three hij hik hjk
  have hQi : (P ^ 3).left i = t * s := by
    rw [pow_three_left, hPr, hρii, hρ2i, hPi, hPj, hPk]
    rw [one_mul, hst]
  have hQj : (P ^ 3).left j = t * s := by
    rw [pow_three_left, hPr, hρij, hρ2j, hPi, hPj, hPk]
    rw [mul_one]
  have hQk : (P ^ 3).left k = t * s := by
    rw [pow_three_left, hPr, hρik, hρ2k, hPi, hPj, hPk]
    rw [mul_one, hst]
  ext p
  · rcases CFSG.GroupTheory.eq_or_eq_or_eq_of_fin_three hij hik hjk p with rfl | rfl | rfl
    · exact hQi
    · exact hQj
    · exact hQk
  · rw [hQr]; rfl

theorem exists_conj_ne_commute_of_involution {f : ℕ} (hf : 2 ≤ f) {s : PSL2Model f}
    (hs : s * s = 1) (hs1 : s ≠ 1) :
    ∃ a : PSL2Model f, a * s * a⁻¹ ≠ s ∧ Commute (a * s * a⁻¹) s := by
  have hB : IsBenderGroup (PSL2Model f) := IsBenderGroup.isPSL2 f hf (MulEquiv.refl _)
  have hsord : orderOf s = 2 := orderOf_eq_prime (by rwa [pow_two]) hs1
  obtain ⟨t, htord, hts, hst⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_involution_commute_ne hB hsord
  obtain ⟨a, ha⟩ := isConj_iff.1
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB hsord htord)
  exact ⟨a, by rw [ha]; exact hts, by rw [ha]; exact hst.symm⟩

theorem conj_three_coords {c : L2Wreath f 3} {s : PSL2Model f}
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : c.right = swap i j) (hi : c.left i = 1) (hj : c.left j = 1)
    (hk : c.left k = s) (a : PSL2Model f) :
    let g : L2Wreath f 3 := inl (Pi.mulSingle i a) * inr (swap i k)
    let d : L2Wreath f 3 := g * c * g⁻¹
    d.right = swap j k ∧ d.left i = a * s * a⁻¹ ∧ d.left j = 1 ∧ d.left k = 1 := by
  dsimp only
  set σ : Perm (Fin 3) := swap i k with hσdef
  set y : Fin 3 → PSL2Model f := Pi.mulSingle i a with hydef
  set g : L2Wreath f 3 := inl y * inr σ with hgdef
  set d0 : L2Wreath f 3 := inr σ * c * (inr σ)⁻¹ with hd0def
  have hg : g * c * g⁻¹ = inl y * d0 * (inl y)⁻¹ := by
    rw [hgdef, hd0def]; group
  have hσi : σ i = k := by rw [hσdef]; exact swap_apply_left _ _
  have hσj : σ j = j := by rw [hσdef]; exact swap_apply_of_ne_of_ne hij.symm hjk
  have hσii : σ⁻¹ i = k := by rw [hσdef]; exact swap_apply_left _ _
  have hσij : σ⁻¹ j = j := by rw [hσdef]; exact swap_apply_of_ne_of_ne hij.symm hjk
  have hσik : σ⁻¹ k = i := by rw [hσdef]; exact swap_apply_right _ _
  have hd0r : d0.right = swap j k := by
    rw [hd0def, inr_conj_right, hr, ← Equiv.swap_apply_apply, hσi, hσj]
    exact Equiv.swap_comm _ _
  have hd0li : d0.left i = s := by
    rw [hd0def, inr_conj_left, hσii, hk]
  have hd0lj : d0.left j = 1 := by
    rw [hd0def, inr_conj_left, hσij, hj]
  have hd0lk : d0.left k = 1 := by
    rw [hd0def, inr_conj_left, hσik, hi]
  have hdi : (swap j k)⁻¹ i = i := by
    rw [swap_inv]; exact swap_apply_of_ne_of_ne hij hik
  have hdj : (swap j k)⁻¹ j = k := by
    rw [swap_inv]; exact swap_apply_left _ _
  have hdk : (swap j k)⁻¹ k = j := by
    rw [swap_inv]; exact swap_apply_right _ _
  have hyi : y i = a := by rw [hydef, Pi.mulSingle_eq_same]
  have hyj : y j = 1 := by rw [hydef, Pi.mulSingle_eq_of_ne hij.symm]
  have hyk : y k = 1 := by rw [hydef, Pi.mulSingle_eq_of_ne hik.symm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg, inl_conj_right, hd0r]
  · rw [hg, inl_conj_left, hd0li, hd0r, hdi, hyi]
  · rw [hg, inl_conj_left, hd0lj, hd0r, hdj, hyj, hyk, inv_one, mul_one, one_mul]
  · rw [hg, inl_conj_left, hd0lk, hd0r, hdk, hyk, hyj, inv_one, mul_one, one_mul]

theorem conj_mul_three_coords {c : L2Wreath f 3} {s : PSL2Model f} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hr : c.right = swap i j)
    (hi : c.left i = 1) (hj : c.left j = 1) (hk : c.left k = s) (a : PSL2Model f) :
    let g : L2Wreath f 3 := inl (Pi.mulSingle i a) * inr (swap i k)
    let d : L2Wreath f 3 := g * c * g⁻¹
    let P : L2Wreath f 3 := c * d
    d.right = swap j k ∧ d.left i = a * s * a⁻¹ ∧ d.left j = 1 ∧ d.left k = 1 ∧
      P.right = swap i j * swap j k ∧ P.left i = 1 ∧ P.left j = a * s * a⁻¹ ∧
        P.left k = s := by
  have hd := conj_three_coords hij hik hjk hr hi hj hk a
  dsimp only at hd ⊢
  obtain ⟨hdr, hdli, hdlj, hdlk⟩ := hd
  refine ⟨hdr, hdli, hdlj, hdlk, ?_, ?_, ?_, ?_⟩
  · rw [mul_right, hr, hdr]
  · rw [mul_left_apply, hr, swap_inv, swap_apply_left, hi, hdlj, one_mul]
  · rw [mul_left_apply, hr, swap_inv, swap_apply_right, hj, hdli, one_mul]
  · rw [mul_left_apply, hr, swap_inv, swap_apply_of_ne_of_ne hik.symm hjk.symm, hk,
      hdlk, mul_one]

theorem not_dvd_two_or_odd_of_cube_involution {G : Type*} [Group G] {P : G}
    (h3 : 3 ∣ orderOf P) (hQsq : P ^ 3 * P ^ 3 = 1) (hQne : P ^ 3 ≠ 1) :
    ¬ (orderOf P ∣ 2 ∨ Odd (orderOf P)) := by
  have hordQ : orderOf (P ^ 3) = 2 := orderOf_eq_prime (by rwa [pow_two]) hQne
  rintro (h2 | hodd)
  · exact absurd (h3.trans h2) (by decide : ¬ (3 ∣ 2))
  · have hodd3 : Odd (orderOf (P ^ 3)) := hodd.of_dvd_nat (orderOf_pow_dvd 3)
    rw [hordQ] at hodd3
    exact absurd hodd3 (by rintro ⟨k, hk⟩; omega)

theorem cube_involution_facts_of_three {P : L2Wreath f 3} {s a : PSL2Model f} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hPr : P.right = swap i j * swap j k) (hPi : P.left i = 1)
    (hPj : P.left j = a * s * a⁻¹) (hPk : P.left k = s)
    (hssq : s * s = 1) (ha : a * s * a⁻¹ ≠ s)
    (hcomm : Commute (a * s * a⁻¹) s) :
    P ^ 3 ≠ 1 ∧ P ^ 3 * P ^ 3 = 1 ∧ 3 ∣ orderOf P := by
  have hQ : P ^ 3 = inl (fun _ => (a * s * a⁻¹) * s) :=
    cube_eq_inl_of_three hij hik hjk hPr hPi hPj hPk hcomm.eq.symm
  have ht_sq : (a * s * a⁻¹) * (a * s * a⁻¹) = 1 := by
    rw [show (a * s * a⁻¹) * (a * s * a⁻¹) = a * (s * s) * a⁻¹ by group]
    rw [hssq, mul_one, mul_inv_cancel]
  have hv1 : (a * s * a⁻¹) * s ≠ 1 := by
    intro h
    apply ha
    have h' : (a * s * a⁻¹) * s = s * s := by rw [h, hssq]
    exact mul_right_cancel h'
  have hvsq : ((a * s * a⁻¹) * s) * ((a * s * a⁻¹) * s) = 1 := by
    calc
      ((a * s * a⁻¹) * s) * ((a * s * a⁻¹) * s)
          = (a * s * a⁻¹) * (s * (a * s * a⁻¹)) * s := by group
      _ = (a * s * a⁻¹) * ((a * s * a⁻¹) * s) * s := by rw [hcomm.eq]
      _ = ((a * s * a⁻¹) * (a * s * a⁻¹)) * (s * s) := by group
      _ = 1 := by rw [ht_sq, hssq, mul_one]
  have hQne : P ^ 3 ≠ 1 := by
    rw [hQ]
    intro h
    apply hv1
    have hleft := congrArg (fun z : L2Wreath f 3 => z.left i) h
    simpa using hleft
  have hQsq : P ^ 3 * P ^ 3 = 1 := by
    rw [hQ]
    rw [← map_mul, ← map_one (inl : (Fin 3 → PSL2Model f) →* L2Wreath f 3)]
    congr 1
    ext p
    exact hvsq
  refine ⟨hQne, hQsq, ?_⟩
  have h := orderOf_map_dvd (SemidirectProduct.rightHom : L2Wreath f 3 →* Perm (Fin 3)) P
  have hρ : orderOf P.right = 3 := by
    rw [hPr]
    have hcyc : (swap i j * swap j k).IsThreeCycle := by
      simpa [Equiv.swap_comm] using
        Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := j) (b := i) (c := k)
          hij.symm hjk hik
    exact hcyc.orderOf
  rwa [show SemidirectProduct.rightHom P = P.right from rfl, hρ] at h

theorem left_eq_one_of_normalized_three {f : ℕ} (hf : 2 ≤ f)
    {C : Set (L2Wreath f 3)} (hC : IsOddTransp C)
    (hconj : ∀ c ∈ C, ∀ g : L2Wreath f 3, g * c * g⁻¹ ∈ C)
    {c : L2Wreath f 3} (hc : c ∈ C) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hr : c.right = swap i j) (hi : c.left i = 1) (hj : c.left j = 1) :
    c.left k = 1 := by
  by_contra hne
  set s : PSL2Model f := c.left k with hsdef
  have hsne : s ≠ 1 := by rwa [hsdef]
  have hssq : s * s = 1 := by
    have h := CFSG.OddTranspositions.PartThree.WreathClass.left_mul_left_eq_one
      (CFSG.OddTranspositions.PartThree.WreathClass.mul_self_eq_one_of_mem hC hc) k
    rw [hr, swap_inv, swap_apply_of_ne_of_ne hik.symm hjk.symm] at h
    simpa [hsdef] using h
  obtain ⟨a, ha, hcomm⟩ := exists_conj_ne_commute_of_involution hf hssq hsne
  let y : Fin 3 → PSL2Model f := Pi.mulSingle i a
  let g : L2Wreath f 3 := inl y * inr (swap i k)
  let d : L2Wreath f 3 := g * c * g⁻¹
  let P : L2Wreath f 3 := c * d
  have hcoords := conj_mul_three_coords hij hik hjk hr hi hj hsdef.symm a
  dsimp only [g, d, P, y] at hcoords
  obtain ⟨hdr, hdli, hdlj, hdlk, hPr, hPi, hPj, hPk⟩ := hcoords
  have hdC : d ∈ C := hconj c hc g
  obtain ⟨hQne, hQsq, h3dvd⟩ :=
    cube_involution_facts_of_three hij hik hjk hPr hPi hPj hPk hssq ha hcomm
  exact not_dvd_two_or_odd_of_cube_involution h3dvd hQsq hQne (hC.2 c hc d hdC)

theorem mem_swapSet_of_isSwap_right_three_four {f m : ℕ} (hf : 2 ≤ f) (hm : m = 3 ∨ m = 4)
    {C : Set (L2Wreath f m)} (hC : IsOddTransp C)
    (hconj : ∀ c ∈ C, ∀ g : L2Wreath f m, g * c * g⁻¹ ∈ C)
    {c : L2Wreath f m} (hc : c ∈ C) (hsw : c.right.IsSwap) :
    c ∈ WreathEndgame.swapSet f m := by
  obtain ⟨i, j, hij, hr⟩ := hsw
  have hcc : c * c = 1 := WreathClass.mul_self_eq_one_of_mem hC hc
  have hinv : c.right⁻¹ = swap i j := by rw [hr, swap_inv]
  have hij1 : c.left i * c.left j = 1 := by
    have h := WreathClass.left_mul_left_eq_one hcc i
    rwa [hinv, swap_apply_left] at h
  set y₀ : Fin m → PSL2Model f := Pi.mulSingle j (c.left i) with hy₀
  set c₁ : L2Wreath f m := inl y₀ * c * (inl y₀)⁻¹ with hc₁def
  have hc₁C : c₁ ∈ C := hconj c hc _
  have hr₁ : c₁.right = swap i j := by rw [hc₁def, inl_conj_right, hr]
  have hl₁i : c₁.left i = 1 := by
    rw [hc₁def, inl_conj_left, hinv, swap_apply_left, hy₀, Pi.mulSingle_eq_of_ne hij,
      Pi.mulSingle_eq_same, one_mul, mul_inv_cancel]
  have hl₁j : c₁.left j = 1 := by
    rw [hc₁def, inl_conj_left, hinv, swap_apply_right, hy₀, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hij, inv_one, mul_one, hij1]
  have hl₁k : ∀ k, k ≠ i → k ≠ j → c₁.left k = c.left k := by
    intro k hki hkj
    rw [hc₁def, inl_conj_left, hinv, swap_apply_of_ne_of_ne hki hkj, hy₀,
      Pi.mulSingle_eq_of_ne hkj, inv_one, mul_one, one_mul]
  refine ⟨i, j, hij, hr, fun k hki hkj => ?_, eq_inv_of_mul_eq_one_right hij1⟩
  have h1 : c₁.left k = 1 := by
    rcases hm with rfl | rfl
    · exact left_eq_one_of_normalized_three hf hC hconj hc₁C hij hki.symm hkj.symm hr₁ hl₁i hl₁j
    · exact WreathClass.left_eq_one_of_normalized hf (by omega) hC hconj hc₁C hij hr₁ hl₁i hl₁j
        hki hkj
  rwa [hl₁k k hki hkj] at h1

theorem eq_swapSet_of_setup {f m : ℕ} (hf : 2 ≤ f) (hm : m = 3 ∨ m = 4)
    {C : Set (L2Wreath f m)} (hS : Setup (L2Wreath f m) C) :
    C = WreathEndgame.swapSet f m := by
  obtain ⟨d₀, hCclass⟩ := hS.isClass
  have hnt : Nontrivial (Fin m) :=
    Fin.nontrivial_iff_two_le.2 (by rcases hm with rfl | rfl <;> norm_num)
  have hgenClass : Subgroup.closure {g | IsConj d₀ g} = ⊤ := by
    rw [← hCclass]; exact hS.gen
  have hne : ∀ d ∈ C, (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) d ≠ 1 := by
    intro d hd
    have hd' : d ∈ {g | IsConj d₀ g} := by rwa [hCclass] at hd
    exact CentralSymSplit.map_ne_one_of_isConj SemidirectProduct.rightHom
      SemidirectProduct.rightHom_surjective hgenClass hd'
  have hS' : Setup (Perm (Fin m))
      ((SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) '' C) :=
    hS.map SemidirectProduct.rightHom SemidirectProduct.rightHom_surjective hne
  have hswap : ∀ σ ∈ (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) '' C,
      σ.IsSwap := by
    rcases hm with rfl | rfl
    · exact isSwap_of_isOddTransp_class_three hS'.oddT
    · exact isSwap_of_isOddTransp_class_four hS'.oddT hS'.isClass hS'.gen
  have hsub : C ⊆ WreathEndgame.swapSet f m := by
    intro c hc
    have hsw : c.right.IsSwap := hswap c.right ⟨c, hc, rfl⟩
    exact mem_swapSet_of_isSwap_right_three_four hf hm hS.oddT
      (fun c hc g => hS.conj_mem g hc) hc hsw
  have hsup : WreathEndgame.swapSet f m ⊆ C := by
    have hm2 : 2 ≤ m := by rcases hm with rfl | rfl <;> norm_num
    obtain ⟨c₀, hc₀⟩ := hS.nonempty
    have hc₀S : c₀ ∈ WreathEndgame.swapSet f m := hsub hc₀
    have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    intro x hx
    have hxconj : IsConj (SemidirectProduct.inr (swap ⟨0, by omega⟩ ⟨1, by omega⟩)) x :=
      WreathEndgame.isConj_of_mem_swapSet h01 hx
    have hc₀conj : IsConj (SemidirectProduct.inr (swap ⟨0, by omega⟩ ⟨1, by omega⟩)) c₀ :=
      WreathEndgame.isConj_of_mem_swapSet h01 hc₀S
    rw [hS.eq_setOf_isConj hc₀]
    exact hc₀conj.symm.trans hxconj
  exact Set.Subset.antisymm hsub hsup

theorem eq_preimage_swapSet_of_mulEquiv {X : Type*} [Group X] {E : Set X} (hS : Setup X E)
    {f m : ℕ} (hf : 2 ≤ f) (hm : m = 3 ∨ m = 4) (e : X ≃* L2Wreath f m) :
    E = e ⁻¹' WreathEndgame.swapSet f m := by
  have hne : ∀ d ∈ E, e d ≠ 1 := fun d hd h =>
    hS.oddT.ne_one hd (e.injective (by simpa using h))
  have hS' : Setup (L2Wreath f m) (e.toMonoidHom '' E) :=
    hS.map e.toMonoidHom e.surjective hne
  have hmap : e.toMonoidHom '' E = WreathEndgame.swapSet f m :=
    eq_swapSet_of_setup hf hm hS'
  ext x
  rw [Set.mem_preimage]
  constructor
  · intro hx
    rw [← hmap]
    exact Set.mem_image_of_mem _ hx
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hye⟩ := hx
    have hyx : y = x := e.injective hye
    rw [← hyx]
    exact hy

end CFSG.OddTranspositions.PartThree.EightEight

end
