module

public import CFSG.Quasithin.Background.C24PfA
public import CFSG.Quasithin.Background.C24PfB
public import CFSG.Quasithin.Background.E6TwentyThreeF
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.EmptyFaithful.S146zVA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.C2Push

namespace C24Pf

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_commutator_eq {B J : Subgroup G} (h : ⁅B, J⁆ = B) :
    J ≤ Subgroup.normalizer (B : Set G) := by
  intro j hj
  refine C22Pf.mem_normalizer_of_conj_mem fun b hb => ?_
  have h1 : j * b * j⁻¹ * b⁻¹ ∈ B := by
    rw [← h, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hj hb
  have e : j * b * j⁻¹ = (j * b * j⁻¹ * b⁻¹) * b := by group
  rw [e]
  exact B.mul_mem h1 hb

theorem asc24One_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) (h129 : ASC129Statement G) :
    ASC24One G := by
  intro H R M L hyp hL hLc hLq hsyl
  by_cases hLM : L ≤ M
  · exact Or.inl hLM
  right
  have hR := hyp.radical
  have hRH : R ≤ H := hR.1
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hYH : Y ≤ H := conjClosure_sup_le hRH hLH
  have hRY : R ≤ Y := le_sup_right
  have hLY : L ≤ Y := (le_conjClosure L R).trans le_sup_left
  have hRM : R ≤ M := fun x hx =>
    hyp.cgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRH hx, Subgroup.le_normalizer hx⟩)
  have hYsyl : IsSylowTwoOf R Y := isSylowTwoOf_conjClosure_sup hR hL hLq hsyl
  have hYc : CharTwo Y := charTwo_conjClosure_sup hA37 hA38 hS hyp.sqtk hR hL hLc hLq
  have hYs : IsSQTKIn Y := hyp.sqtk.mono hYH
  have hcgsY : cgsIn Y R ≤ Y ⊓ M :=
    le_inf (cgsIn_le Y R) ((C2Nine.cgsIn_mono_left hYH R).trans hyp.cgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 Y R (Y ⊓ M) hYs hYc hYsyl hcgsY inf_le_left
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  swap
  · exfalso
    push Not at hq
    exact hLM (le_of_isBlock2_card_three hL hLq hRH hYsyl hRM Lb
      (fun i => ⟨(hLb i).1.1, hq i⟩) hprod)
  obtain ⟨i, hi⟩ := hq
  have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
    ((hLb i).1.1.1.2.2.2.1).resolve_right hi
  obtain ⟨x, hxR, hBx⟩ := exists_eq_conjByElt_of_isBlock2 hR hL hLq (hLb i).1.1 hBq
  have hxY : x⁻¹ ∈ Y := Y.inv_mem (hRY hxR)
  have hxM : x⁻¹ ∈ M := M.inv_mem (hRM hxR)
  have hLB : conjByElt x⁻¹ (Lb i) = L := by rw [hBx, conjByElt_inv_conjByElt]
  have hchi : IsChi0Block Y L := by
    have h1 := E6.A3Push.isChi0Block_map_conj (hLb i).1 hxY
    rwa [show (Lb i).map (MulAut.conj x⁻¹).toMonoidHom = L from hLB] at h1
  have hchiH : IsChi0Block H L :=
    ⟨⟨hchi.1.1, hLH, B113.subgroupOf_isSubnormal (subnormal_of_mem_cComp hL)⟩, hchi.2⟩
  have hYx : Y.map (MulAut.conj x⁻¹).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxY)
  have hMx : M.map (MulAut.conj x⁻¹).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxM)
  have hborel : IsBorelOfBlock L (L ⊓ M) := by
    have h1 := S146zV.isBorelOfBlock_map_conj (hLb i).2.1 x⁻¹
    have hinj : Function.Injective (MulAut.conj x⁻¹).toMonoidHom := (MulAut.conj x⁻¹).injective
    rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hYx, hMx,
      show (Lb i).map (MulAut.conj x⁻¹).toMonoidHom = L from hLB,
      ← inf_assoc, inf_eq_left.mpr hLY] at h1
    exact h1
  have hJB : thompsonJ R ≤ Subgroup.normalizer ((Lb i : Subgroup G) : Set G) :=
    le_normalizer_of_commutator_eq (hLb i).2.2
  have hRJ : R ≤ Subgroup.normalizer (thompsonJ R : Set G) := B6.le_normalizer_thompsonJ R
  have hJL : thompsonJ R ≤ Subgroup.normalizer (L : Set G) := by
    intro j hj
    refine C22Pf.mem_normalizer_of_conj_mem fun l hl => ?_
    have hj' : x * j * x⁻¹ ∈ thompsonJ R :=
      (Subgroup.mem_normalizer_iff.mp (hRJ hxR) j).mp hj
    have hxl : x * l * x⁻¹ ∈ Lb i := by
      rw [hBx, mem_conjByElt]
      simpa [mul_assoc] using hl
    have h1 := (Subgroup.mem_normalizer_iff.mp (hJB hj') _).mp hxl
    rw [hBx, mem_conjByElt] at h1
    have e : x⁻¹ * (x * j * x⁻¹ * (x * l * x⁻¹) * (x * j * x⁻¹)⁻¹) * x = j * l * j⁻¹ := by
      group
    rwa [e] at h1
  have hJx : (thompsonJ R).map (MulAut.conj x⁻¹).toMonoidHom = thompsonJ R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRJ (R.inv_mem hxR))
  have hLJ : ⁅L, thompsonJ R⁆ = L := by
    have h1 := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) (hLb i).2.2
    rw [Subgroup.map_commutator, hJx, show (Lb i).map (MulAut.conj x⁻¹).toMonoidHom = L from hLB]
      at h1
    exact h1
  set RL := R ⊓ Subgroup.normalizer (L : Set G) with hRL
  have hRL2 : IsPGroup 2 ↥RL := hR2.to_le inf_le_left
  have hJRL : thompsonJ R ≤ RL := le_inf (B6.thompsonJ_le R) hJL
  have hJeq : thompsonJ RL = thompsonJ R := B6.thompsonJ_eq_of_le hJRL inf_le_left
  have hsylL : IsSylowTwoOf (RL ⊓ L) L := by
    have e : RL ⊓ L = R ⊓ L := by
      rw [hRL, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
    rw [e]
    exact hsyl
  obtain ⟨hV, A, hA, hoff⟩ := exists_isFFOffender hchi.1.1 hRL2 inf_le_right hsylL
    (hJeq.symm ▸ hLJ)
  exact ⟨hchiH, ⟨blockU L, hV, A, hA, hoff⟩, hborel⟩

end C24Pf

end CFSG.Quasithin
