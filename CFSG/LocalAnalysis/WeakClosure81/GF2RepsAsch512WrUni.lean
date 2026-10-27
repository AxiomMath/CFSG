module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrAbs
public import CFSG.GH74.KGroups.L3EpsUniSyl
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

open Subgroup

section Abstract

variable {S : Type*} [Group S] [Finite S]

theorem wrModel_quotient_of_wreath (D : Subgroup S) [D.Normal] {u v τ c : S} {s : ℕ}
    (hs : 4 ≤ s) (hvu : v = τ⁻¹ * u * τ) (huv : Commute u v) (hus : u ^ s = 1) (hvs : v ^ s = 1)
    (hτ2 : τ ^ 2 = 1)
    (hφ : Function.Injective fun x : Fin s × Fin s × Fin 2 =>
      u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ))
    (hnf : ∀ w ∈ closure ({u, v, τ} : Set S), ∃ i j e : ℕ, i < s ∧ j < s ∧ e < 2 ∧
      w = u ^ i * v ^ j * τ ^ e)
    (hinj : Set.InjOn (QuotientGroup.mk' D) (closure ({u, v, τ} : Set S) : Set S))
    (hW2 : IsPGroup 2 ((closure ({u, v, τ} : Set S)).map (QuotientGroup.mk' D)))
    (hWmax : Nat.card ((closure ({u, v, τ} : Set S)).map (QuotientGroup.mk' D)) =
      ordProj[2] (Nat.card (S ⧸ D)))
    (hWcard : Nat.card ((closure ({u, v, τ} : Set S)).map (QuotientGroup.mk' D)) = 2 * s ^ 2)
    {B : Subgroup S} (hB : B ≤ centralizer ({u * v} : Set S))
    (hcu : c * u * c⁻¹ ∈ closure ({u, v} : Set S)) (hcv : c * v * c⁻¹ ∈ closure ({u, v} : Set S))
    (hc3 : c ^ 3 = 1) (hcD : c ∉ D) (hBc : B ⊔ B.map (MulAut.conj c).toMonoidHom = ⊤) :
    WrModel (S ⧸ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' D with hπ
  set W := closure ({u, v, τ} : Set S) with hW
  set N := closure ({u, v} : Set S) with hN
  have huW : u ∈ W := subset_closure (by simp)
  have hvW : v ∈ W := subset_closure (by simp)
  have hτW : τ ∈ W := subset_closure (by simp)
  have huN : u ∈ N := subset_closure (by simp)
  have hvN : v ∈ N := subset_closure (by simp)
  have hNW : N ≤ W := closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ2])
  have hτu : τ * u = v * τ := by
    calc τ * u = τ⁻¹ * u := by rw [hτi]
      _ = τ⁻¹ * u * (τ * τ) := by rw [← sq, hτ2, mul_one]
      _ = (τ⁻¹ * u * τ) * τ := by group
      _ = v * τ := by rw [hvu]
  have hτuτ : τ * u * τ⁻¹ = v := by rw [hτu, mul_inv_cancel_right]
  have hτvτ : τ * v * τ⁻¹ = u := by rw [hvu]; group
  have hinj3 : ∀ {i j e i' j' e' : ℕ}, i < s → j < s → e < 2 → i' < s → j' < s → e' < 2 →
      u ^ i * v ^ j * τ ^ e = u ^ i' * v ^ j' * τ ^ e' → i = i' ∧ j = j' ∧ e = e' := by
    intro i j e i' j' e' hi hj he hi' hj' he' h
    have := @hφ (⟨i, hi⟩, ⟨j, hj⟩, ⟨e, he⟩) (⟨i', hi'⟩, ⟨j', hj'⟩, ⟨e', he'⟩) h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    exact this
  have huv_ne : u ≠ v := by
    intro h
    have := hinj3 (i := 1) (j := 0) (e := 0) (i' := 0) (j' := 1) (e' := 0) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by simp [h])
    exact absurd this.1 (by norm_num)
  have hNC : N ≤ centralizer ({u} : Set S) := by
    refine (closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact mem_centralizer_singleton_iff.mpr huv.eq.symm
  have hτN : τ ∉ N := by
    intro h
    have h1 := mem_centralizer_singleton_iff.mp (hNC h)
    apply huv_ne
    rw [hvu, mul_assoc, ← h1, inv_mul_cancel_left]
  set P := W.map π with hP
  set A := N.map π with hA
  have hAP : A ≤ P := map_mono hNW
  let P₀ : Sylow 2 (S ⧸ D) :=
    { toSubgroup := P
      isPGroup' := hW2
      is_maximal' := fun {Q} hQ hle =>
        le_antisymm (CFSG.GH74.KGroups.L3Eps.isMax_of_card hWmax Q hQ hle) hle }
  have hAcomm : IsMulCommutative ↥A := by
    have : IsMulCommutative ↥N := isMulCommutative_closure (by
      intro x hx y hy _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact huv
      · exact huv.symm
      · exact Commute.refl _)
    exact inferInstance
  have hZ : P ⊓ centralizer (P : Set (S ⧸ D)) ≤ zpowers (π (u * v)) := by
    intro z hz
    obtain ⟨hzP, hzC⟩ := mem_inf.mp hz
    obtain ⟨w, hwW, rfl⟩ := mem_map.mp hzP
    have hcomm : ∀ y ∈ W, y * w = w * y := by
      intro y hy
      have h1 := mem_centralizer_iff.mp hzC (π y) (mem_map_of_mem π hy)
      rw [← map_mul, ← map_mul] at h1
      exact hinj (mul_mem hy hwW) (mul_mem hwW hy) h1
    obtain ⟨i, j, e, hi, hj, he, rfl⟩ := hnf w hwW
    interval_cases e
    ·
      have h2 := hcomm τ hτW
      rw [pow_zero, mul_one] at h2
      have h3 : u ^ i * v ^ j = v ^ i * u ^ j := by
        calc u ^ i * v ^ j = τ * (u ^ i * v ^ j) * τ⁻¹ := by rw [h2, mul_inv_cancel_right]
          _ = (τ * u * τ⁻¹) ^ i * (τ * v * τ⁻¹) ^ j := by rw [conj_pow, conj_pow]; group
          _ = v ^ i * u ^ j := by rw [hτuτ, hτvτ]
      have h4 : u ^ j * v ^ i * τ ^ 0 = u ^ i * v ^ j * τ ^ 0 := by
        rw [h3, (huv.pow_pow j i).eq]
      obtain ⟨rfl, -, -⟩ := hinj3 hj hi (by norm_num) hi hj (by norm_num) h4
      rw [pow_zero, mul_one, ← huv.mul_pow, map_pow]
      exact npow_mem_zpowers _ _
    ·
      exfalso
      have h2 := hcomm u huW
      rw [pow_one] at h2
      have h3 : u * (u ^ i * v ^ j) * τ = u ^ i * v ^ j * v * τ := by
        calc u * (u ^ i * v ^ j) * τ = u * (u ^ i * v ^ j * τ) := by group
          _ = u ^ i * v ^ j * τ * u := h2
          _ = u ^ i * v ^ j * (τ * u) := by group
          _ = u ^ i * v ^ j * (v * τ) := by rw [hτu]
          _ = u ^ i * v ^ j * v * τ := by group
      have h4 : u ^ i * (u * v ^ j) = u ^ i * (v * v ^ j) := by
        calc u ^ i * (u * v ^ j) = u * (u ^ i * v ^ j) :=
              ((Commute.self_pow u i).symm.left_comm (v ^ j))
          _ = u ^ i * v ^ j * v := mul_right_cancel h3
          _ = u ^ i * (v * v ^ j) := by rw [mul_assoc, ← (Commute.self_pow v j).eq]
      exact huv_ne (mul_right_cancel (mul_left_cancel h4))
  have hcardZ : Nat.card ↥(P ⊓ centralizer (P : Set (S ⧸ D))) ≤ s := by
    refine (card_le_of_le hZ).trans ?_
    rw [Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one (by omega) ?_
    rw [← map_pow, huv.mul_pow, hus, hvs, one_mul, map_one]
  have hcardA : s ^ 2 ≤ Nat.card A := by
    let g : Fin s × Fin s → A := fun x => ⟨π (u ^ (x.1 : ℕ) * v ^ (x.2 : ℕ)),
      mem_map_of_mem π (mul_mem (pow_mem huN _) (pow_mem hvN _))⟩
    have hg : Function.Injective g := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h1 : π (u ^ (i : ℕ) * v ^ (j : ℕ)) = π (u ^ (i' : ℕ) * v ^ (j' : ℕ)) :=
        congrArg Subtype.val h
      have h2 := hinj (hNW (mul_mem (pow_mem huN _) (pow_mem hvN _)))
        (hNW (mul_mem (pow_mem huN _) (pow_mem hvN _))) h1
      have h3 : u ^ (i : ℕ) * v ^ (j : ℕ) * τ ^ 0 = u ^ (i' : ℕ) * v ^ (j' : ℕ) * τ ^ 0 := by
        rw [h2]
      obtain ⟨hii, hjj, -⟩ := hinj3 i.2 j.2 (by norm_num) i'.2 j'.2 (by norm_num) h3
      exact Prod.ext (Fin.ext hii) (Fin.ext hjj)
    have := Nat.card_le_card_of_injective g hg
    simpa [Nat.card_prod, sq] using this
  have hπτ : π τ ∉ A := by
    rintro ⟨n, hn, hnτ⟩
    exact hτN (hinj (hNW hn) hτW hnτ ▸ hn)
  have hrel : A.relIndex P = 2 := by
    have h := relIndex_mul_card (H := A) (K := P)
    rw [inf_of_le_left hAP, hWcard] at h
    have hR1 : A.relIndex P ≠ 1 := by
      intro h1
      exact hπτ (relIndex_eq_one.mp h1 (mem_map_of_mem π hτW))
    have hpos : 0 < s ^ 2 := by positivity
    set R := A.relIndex P with hR
    rcases Nat.lt_or_ge R 3 with h3 | h3
    · interval_cases R
      · rw [zero_mul] at h
        omega
      · exact absurd rfl hR1
      · rfl
    · nlinarith [Nat.mul_le_mul h3 hcardA]
  have hZP : 4 * Nat.card ↥(P ⊓ centralizer (P : Set (S ⧸ D))) < Nat.card P := by
    rw [hWcard]
    nlinarith [Nat.mul_le_mul hs (le_refl s)]
  have hgen : normalizer ((P ⊓ centralizer (P : Set (S ⧸ D)) : Subgroup (S ⧸ D)) :
      Set (S ⧸ D)) ⊔ normalizer (A : Set (S ⧸ D)) = ⊤ := by
    set H := normalizer ((P ⊓ centralizer (P : Set (S ⧸ D)) : Subgroup (S ⧸ D)) :
      Set (S ⧸ D)) ⊔ normalizer (A : Set (S ⧸ D)) with hH
    have hfwd : ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
      have hle : N ≤ N.comap (MulAut.conj c).toMonoidHom := by
        refine (closure_le _).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rcases hx with rfl | rfl
        · exact hcu
        · exact hcv
      intro x hx
      have := hle hx
      rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have hcN : c ∈ normalizer (N : Set S) := by
      rw [mem_normalizer_iff]
      intro x
      refine ⟨hfwd x, fun hx => ?_⟩
      have h2 := hfwd _ (hfwd _ hx)
      have hc3' : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
      have : x = c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ := by
        calc x = (c * c * c) * x * (c * c * c)⁻¹ := by rw [hc3', one_mul, inv_one, mul_one]
          _ = c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ := by
            simp only [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact h2
    have hcH : π c ∈ H := mem_sup_right (le_normalizer_map π (mem_map_of_mem π hcN))
    have hBH : ∀ g ∈ B, π g ∈ H := by
      intro g hg
      refine mem_sup_left (centralizer_le_normalizer _ (centralizer_le
        (SetLike.coe_subset_coe.mpr hZ) ?_))
      have hgc0 : Commute (u * v) g := (mem_centralizer_singleton_iff.mp (hB hg)).symm
      have hgc : Commute (π (u * v)) (π g) := hgc0.map π
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (hgc.zpow_left k).eq
    have hB1 : ∀ g ∈ B.map (MulAut.conj c).toMonoidHom, π g ∈ H := by
      rintro _ ⟨b, hb, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem hcH (hBH b hb)) (inv_mem hcH)
    have hle : B ⊔ B.map (MulAut.conj c).toMonoidHom ≤ H.comap π :=
      sup_le (fun g hg => hBH g hg) (fun g hg => hB1 g hg)
    rw [hBc] at hle
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
    exact hle (mem_top x)
  have hPtop : P ≠ ⊤ := by
    intro htop
    have hc1 : π c ≠ 1 := by
      intro h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact hcD h
    have hcP : π c ∈ P := htop ▸ mem_top _
    obtain ⟨k, hk⟩ := hW2 ⟨_, hcP⟩
    have hk' : π c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc3' : π c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have hg := pow_gcd_eq_one.2 ⟨hc3', hk'⟩
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, pow_one] at hg
    exact hc1 hg
  exact ⟨P₀, A, hAP, hAcomm, hrel, hZP, hgen, hPtop⟩

end Abstract

section Cycle

open Matrix CFSG.LieType.Steinberg

variable {K : Type} [Field K]

@[expose] def cycThreeGL : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_cycThreeGL :
    ((cycThreeGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
  rfl

theorem cycThreeGL_pow_three : (cycThreeGL : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThreeGL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycThreeGL_mul_diagGL_u (l : Kˣ) :
    (cycThreeGL : GL (Fin 3) K) * diagGL ![l, 1, l⁻¹] = (diagGL ![1, l, l⁻¹])⁻¹ * cycThreeGL := by
  apply Units.ext
  simp only [Units.val_mul, coe_cycThreeGL, coe_diagGL, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem cycThreeGL_mul_diagGL_v (l : Kˣ) :
    (cycThreeGL : GL (Fin 3) K) * diagGL ![1, l, l⁻¹] =
      (diagGL ![l, 1, l⁻¹] * (diagGL ![1, l, l⁻¹])⁻¹) * cycThreeGL := by
  apply Units.ext
  simp only [Units.val_mul, coe_cycThreeGL, coe_diagGL, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem cycThreeGL_mem_SUgram (σ : K →+* K) :
    (cycThreeGL : GL (Fin 3) K) ∈ SUgram σ (1 : Matrix (Fin 3) (Fin 3) K) := by
  refine mem_SUgram.mpr ⟨by simp [coe_cycThreeGL, Matrix.det_fin_three], ?_⟩
  rw [Matrix.mul_one, coe_cycThreeGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ctr, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycThreeGL_not_mem_scalars :
    (cycThreeGL : GL (Fin 3) K) ∉ CFSG.Open.StatedScalars (Fin 3) K := by
  rintro ⟨c, hc⟩
  have h := congrFun (congrFun (congrArg
    (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc) 0) 1
  simp [coe_cycThreeGL, Matrix.GeneralLinearGroup.coe_scalar] at h

theorem mul_diagonal_eq_of_fix_two {M : Matrix (Fin 3) (Fin 3) K}
    (hcol : ∀ i, M i 2 = if i = 2 then 1 else 0) (hrow : ∀ j, M 2 j = if 2 = j then 1 else 0)
    {d : Fin 3 → K} (hd : d 0 = d 1) : M * diagonal d = diagonal d * M := by
  have h02 := hcol 0
  have h12 := hcol 1
  have h20 := hrow 0
  have h21 := hrow 1
  have h22 := hrow 2
  simp at h02 h12 h20 h21 h22
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h22, hd] <;> ring

end Cycle

section Model

open Matrix CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {K : Type} [Field K] {p f : ℕ}

theorem wrModel_psu (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h3 : p ^ f % 4 = 3) :
    WrModel (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K) ⧸
      (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) := by
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP K p := hU.charP
  set S := SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K) with hS
  set D := (StatedScalars (Fin 3) K).subgroupOf S with hD
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  obtain ⟨-, -, -, ⟨-, hQ2⟩, h3part, -⟩ :=
    odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
      (CFSG.GH74.KGroups.L3Eps.bar_one_apply' hU) hdet D le_rfl
  obtain ⟨⟨l, hl, hlo⟩, hall⟩ := h3part h3
  have hP1 : ctr hU.bar ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * 1 *
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    simp [ctr_one]
  obtain ⟨u, v, τ, hu, hv, -, hvu, huv, hou, hov, hτ2, -, -, hφ, hnf, -, -, hinj, hW2, hWmax⟩ :=
    hall 1 hP1 l hl hlo
  simp only [one_mul, inv_one, mul_one] at hu hv
  set s := ordProj[2] (p ^ f + 1) with hs
  have hs4 : 4 ≤ s := by
    have h4 : 2 ^ 2 ∣ p ^ f + 1 := by omega
    rw [Nat.prime_two.pow_dvd_iff_dvd_ordProj (by omega)] at h4
    have := Nat.le_of_dvd (Nat.ordProj_pos _ 2) h4
    omega
  have hus : u ^ s = 1 := by rw [← hou]; exact pow_orderOf_eq_one u
  have hvs : v ^ s = 1 := by rw [← hov]; exact pow_orderOf_eq_one v
  have hWcard : Nat.card ((Subgroup.closure ({u, v, τ} : Set S)).map (QuotientGroup.mk' D)) =
      2 * s ^ 2 := by
    rw [hWmax, hQ2, ordProj_two_sub_one_of_mod_four_eq_three h3]
  have hF : Nat.card K = (p ^ f) ^ 2 := card_eq_sq_of_unitaryFieldData hU
  have hEq : S = CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 :=
    (SUgram_bar_one hU 3).trans (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3)
  let ι : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 := MulEquiv.subgroupCongr hEq
  set B := (CFSG.RankThree.Classical.coordBlock p f K 2).comap ι.toMonoidHom with hB
  have hBcent : B ≤ Subgroup.centralizer ({u * v} : Set S) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg2 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 =
        Pi.single 2 1 := hg
    have hcol := CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen.block_col hg2
    have hUnit : (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map hU.bar)ᵀ *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have := (mem_SUgram.mp g.2).2
      simpa [ctr] using this
    have hrow := CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen.block_row hU.bar hUnit hcol
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hu, hv, coe_diagGL]
    rw [Matrix.diagonal_mul_diagonal]
    exact mul_diagonal_eq_of_fix_two hcol hrow (by simp)
  set c : S := ⟨cycThreeGL, cycThreeGL_mem_SUgram hU.bar⟩ with hc
  have hcmat : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
    rfl
  have hcimat : (((c⁻¹ : S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
    rfl
  have hcuS : c * u = v⁻¹ * c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu, hv]
    exact cycThreeGL_mul_diagGL_u l
  have hcvS : c * v = (u * v⁻¹) * c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu, hv]
    exact cycThreeGL_mul_diagGL_v l
  have huN : u ∈ Subgroup.closure ({u, v} : Set S) := Subgroup.subset_closure (by simp)
  have hvN : v ∈ Subgroup.closure ({u, v} : Set S) := Subgroup.subset_closure (by simp)
  have hcu : c * u * c⁻¹ ∈ Subgroup.closure ({u, v} : Set S) := by
    rw [hcuS, mul_inv_cancel_right]
    exact inv_mem hvN
  have hcv : c * v * c⁻¹ ∈ Subgroup.closure ({u, v} : Set S) := by
    rw [hcvS, mul_inv_cancel_right]
    exact mul_mem huN (inv_mem hvN)
  have hc3 : c ^ 3 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact cycThreeGL_pow_three)
  have hcD : c ∉ D := fun h => cycThreeGL_not_mem_scalars (Subgroup.mem_subgroupOf.mp h)
  have hq2 : p ^ f ≠ 2 := by omega
  have hB1 : (CFSG.RankThree.Classical.coordBlock p f K 1).comap ι.toMonoidHom ≤
      B.map (MulAut.conj c).toMonoidHom := by
    intro g hg
    have hg1 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 1 1 =
        Pi.single 1 1 := hg
    refine ⟨c⁻¹ * g * c, ?_, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    show (((c⁻¹ * g * c : S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 =
      Pi.single 2 1
    have hce2 : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 =
        Pi.single 1 1 := by
      rw [hcmat, Matrix.mulVec_single_one]
      funext i
      fin_cases i <;> simp
    have hcie1 : (((c⁻¹ : S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 1 1 =
        Pi.single 2 1 := by
      rw [hcimat, Matrix.mulVec_single_one]
      funext i
      fin_cases i <;> simp
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hce2, hg1, ← hcie1]
  have hBc : B ⊔ B.map (MulAut.conj c).toMonoidHom = ⊤ := by
    have h21 : B ⊔ (CFSG.RankThree.Classical.coordBlock p f K 1).comap ι.toMonoidHom = ⊤ := by
      rw [hB, Subgroup.comap_sup_eq ι.toMonoidHom _ _ ι.surjective,
        CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen.coordBlock_sup_eq_top hU hq2, Subgroup.comap_top]
    rw [eq_top_iff, ← h21]
    exact sup_le_sup le_rfl hB1
  exact wrModel_quotient_of_wreath D hs4 hvu huv hus hvs hτ2 hφ hnf hinj hW2 hWmax hWcard hBcent
    hcu hcv hc3 hcD hBc

end Model

end CFSG.LocalAnalysis.WeakClosure81.Asch80Wr
