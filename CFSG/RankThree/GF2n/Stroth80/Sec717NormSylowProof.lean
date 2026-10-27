module

public import CFSG.RankThree.GF2n.Stroth80.Sec717NormProof
public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec717CRSylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75

section Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.conj_mem_Nb (F : MoveFrame B φ V L Nb Rb Tt q) {r n : X} (hr : r ∈ Rb)
    (hn : n ∈ Nb) : r * n * r⁻¹ ∈ Nb := by
  refine F.Rb_fix_Nb _ (Rb.mul_mem (Rb.mul_mem hr (F.Nb_le_Rb hn)) (Rb.inv_mem hr))
    fun w hw => ?_
  have hw' : φ r⁻¹ w ∈ Tt 1 := F.map_Tt_one_le (inv_mem (F.Rb_le_K r hr)) hw
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, F.Nb_fixes n hn _ hw',
    phi_apply_inv_apply φ r w]

theorem MoveFrame.mem_normalizer_L (F : MoveFrame B φ V L Nb Rb Tt q) {k : X}
    (hk : k ∈ normalizer (V : Set X)) : k ∈ normalizer (L : Set X) := by
  refine mem_normalizer_iff.mpr fun l => ⟨F.L_norm k hk l, fun hl => ?_⟩
  simpa [mul_assoc] using F.L_norm k⁻¹ (inv_mem hk) _ hl

theorem MoveFrame.exists_sylow_normSylow [Finite X] (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hR : ∃ S : Sylow 2 X, (S : Subgroup X) ≤ Rb) (T : Sylow 2 ↥(conjSubgroup h Rb))
    (hT : Subgroup.map (conjSubgroup h Rb).subtype T ≤ normalizer (L : Set X)) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ normalizer (L : Set X) ∧
      (S : Subgroup X) ≤ normalizer (conjSubgroup h L : Set X) ∧
      normalizer ((S : Subgroup X) : Set X) ≤ normalizer (conjSubgroup h V : Set X) := by
  obtain ⟨S₀, hS₀⟩ := hR
  set T' : Subgroup X := Subgroup.map (conjSubgroup h Rb).subtype T
  have hT'R : T' ≤ conjSubgroup h Rb := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hcard : Nat.card T' = 2 ^ (Nat.card X).factorization 2 := by
    have h3 : Nat.card T' = Nat.card T :=
      Subgroup.card_map_of_injective (conjSubgroup h Rb).subtype_injective
    refine le_antisymm ?_ ?_
    · obtain ⟨P, hP⟩ := (T.isPGroup'.map (conjSubgroup h Rb).subtype).exists_le_sylow
      exact (Subgroup.card_le_of_le hP).trans P.card_eq_multiplicity.le
    · have hS₀h : conjSubgroup h (S₀ : Subgroup X) ≤ conjSubgroup h Rb := fun x hx =>
        CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr
          (hS₀ (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hx))
      have hp : IsPGroup 2 ((conjSubgroup h (S₀ : Subgroup X)).subgroupOf (conjSubgroup h Rb)) :=
        (show IsPGroup 2 (conjSubgroup h (S₀ : Subgroup X)) from
          S₀.isPGroup'.map (MulAut.conj h).toMonoidHom).comap_subtype
      obtain ⟨P, hP⟩ := hp.exists_le_sylow
      have h1 : Nat.card ((conjSubgroup h (S₀ : Subgroup X)).subgroupOf (conjSubgroup h Rb)) =
          Nat.card S₀ := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀h).toEquiv, natCard_conjSubgroup]
      have h2 : Nat.card P = Nat.card T := by
        rw [P.card_eq_multiplicity, T.card_eq_multiplicity]
      calc 2 ^ (Nat.card X).factorization 2 = Nat.card S₀ := S₀.card_eq_multiplicity.symm
        _ = Nat.card ((conjSubgroup h (S₀ : Subgroup X)).subgroupOf (conjSubgroup h Rb)) := h1.symm
        _ ≤ Nat.card P := Subgroup.card_le_of_le hP
        _ = Nat.card T' := h2.trans h3.symm
  have hNb : conjSubgroup h Nb ≤ T' := by
    have hNR : conjSubgroup h Nb ≤ conjSubgroup h Rb := fun x hx =>
      CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr
        (F.Nb_le_Rb (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hx))
    haveI : ((conjSubgroup h Nb).subgroupOf (conjSubgroup h Rb)).Normal := ⟨fun n hn r => by
      rw [Subgroup.mem_subgroupOf, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hn ⊢
      have hr : h⁻¹ * (r : X) * h ∈ Rb := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp r.2
      convert F.conj_mem_Nb hr hn using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group⟩
    have hp : IsPGroup 2 ((conjSubgroup h Nb).subgroupOf (conjSubgroup h Rb)) :=
      (show IsPGroup 2 (conjSubgroup h Nb) from
        F.Nb_pgroup.map (MulAut.conj h).toMonoidHom).comap_subtype
    have hle := hp.le_sylow_of_normal T
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hNR hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hZ : ∀ z ∈ T', (∀ s ∈ T', z * s = s * z) → z ∈ conjSubgroup h V := by
    intro z hzT hzc
    have hzR : h⁻¹ * z * h ∈ Rb := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp (hT'R hzT)
    have hcomm : ∀ n ∈ Nb, (h⁻¹ * z * h) * n = n * (h⁻¹ * z * h) := by
      intro n hn
      have hn' : h * n * h⁻¹ ∈ T' :=
        hNb (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (by simpa [mul_assoc] using hn))
      have e := hzc _ hn'
      calc (h⁻¹ * z * h) * n = h⁻¹ * (z * (h * n * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * n * h⁻¹) * z) * h := by rw [e]
        _ = n * (h⁻¹ * z * h) := by group
    have hzL : h⁻¹ * z * h ∈ L := F.CL _ hzR fun l hl => hcomm l (F.L_le_Nb hl)
    exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (F.Nb_center _ (F.L_le_Nb hzL) hcomm)
  obtain ⟨z, hzT, hz1, hzc⟩ : ∃ z ∈ T', z ≠ 1 ∧ ∀ s ∈ T', z * s = s * z := by
    have hVh : conjSubgroup h V ≤ T' := fun x hx => hNb (by
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx ⊢
      exact F.L_le_Nb (F.V_le_L hx))
    haveI : Nontrivial ↥T' := by
      obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
      refine ⟨⟨⟨h * a * h⁻¹, hVh (mem_conjSubgroup_iff'.mpr ⟨a, ha, rfl⟩)⟩, 1, fun he => ha1 ?_⟩⟩
      have h2 : h * a * h⁻¹ = 1 := congrArg Subtype.val he
      calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
        _ = 1 := by rw [h2]; group
    have hpT : IsPGroup 2 ↥T' := T.isPGroup'.map (conjSubgroup h Rb).subtype
    obtain ⟨w, hw, hw1⟩ := SetLike.exists_of_lt hpT.bot_lt_center
    refine ⟨w, w.2, fun h1 => hw1 (Subgroup.mem_bot.mpr (Subtype.ext h1)), fun s hs => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨s, hs⟩)).symm
  refine ⟨Sylow.ofCard T' hcard, ?_, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact hT
  · rw [Sylow.coe_ofCard]
    intro x hx
    have hx' : h⁻¹ * x * h ∈ Rb := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp (hT'R hx)
    exact mem_normalizer_conjSubgroup_iff.mpr (F.mem_normalizer_L (F.Rb_le_K _ hx'))
  · rw [Sylow.coe_ofCard]
    intro n hn
    have hnz : n * z * n⁻¹ ∈ conjSubgroup h V := by
      refine hZ _ ((mem_normalizer_iff.mp hn z).mp hzT) fun s hs => ?_
      have e := hzc _ ((mem_normalizer_iff''.mp hn s).mp hs)
      calc (n * z * n⁻¹) * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [e]
        _ = s * (n * z * n⁻¹) := by group
    exact F.ti_conj h n (hZ z hzT hzc) hz1 hnz

end Frame


theorem sec717NormSylow_of_parts (hF : Sec717MoveFrameStatement) (hR : Sec717RSylowStatement)
    (hC : Sec717CRSylowStatement) : Sec717NormSylowStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 h hhz hhzV
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  obtain ⟨T, hT⟩ :=
    hC G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 h hhz hhzV
  exact F.exists_sylow_normSylow h (hR G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn) T hT

end CFSG.RankThree.GF2n.Stroth80
