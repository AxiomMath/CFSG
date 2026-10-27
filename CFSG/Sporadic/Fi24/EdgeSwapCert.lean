module

public import CFSG.Sporadic.Fi24.Edge
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Certificate1017
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import CFSG.Sporadic.Fi24.Ext
public import CFSG.Sporadic.Fi24.ExtOuter

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smul_a_eq_iff (k : Fin 306936) : a • k = k ↔ ap orb.alpha k.val = k.val := by
  rw [rep_alpha k.val k.isLt, Th.idx_of_lt a k.isLt, Fin.ext_iff]

theorem card_fixed_a : Nat.card {k : Fin 306936 // subLab k = 2 ∧ a • k = k} = 360 := by
  classical
  obtain ⟨Γ, hseed, hmain⟩ := Certificates.certificate1017
  have hJ : J ≤ Γ := by
    change Subgroup.closure {gA, gB} ≤ Γ
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hseed _ (Or.inl rfl)
    · exact hseed _ (Or.inr rfl)
  set P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3) := fun k => (pt k.val).sp with hPdef
  have hP : Function.Injective P := fun i j h =>
    Fin.ext (pt_inj (by rw [nPts_eq]; exact i.isLt) (by rw [nPts_eq]; exact j.isLt) (Sub781.ext' h))
  have hPs : ∀ (h : J) (k : Fin 306936),
      (P k).map (Matrix.mulVecLin (((h : GL (Fin 781) (ZMod 3))) : Matrix (Fin 781) (Fin 781) (ZMod 3))) =
        P (h • k) := by
    intro h k
    rw [hPdef]
    dsimp only
    rw [pt_smul, smul_sp]
  have hPg : ∀ k, ∃ g ∈ Γ, P k = (pt 0).sp.map
      (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) := by
    intro k
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq J root k
    refine ⟨h, hJ h.2, ?_⟩
    have := hPs h root
    rw [hh] at this
    exact this.symm
  obtain ⟨Ψ, hcard, hne, hstab, hcnt⟩ := hmain P hP hPg
  have hsub : Ψ ⊆ Finset.univ.filter (fun p : Fin 306936 => subLab p = 2) := by
    intro k hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hk0 : subLab k ≠ 0 := by
      intro h0
      exact hne k hk (by rw [subLab_eq_zero.1 h0])
    have hk1 : subLab k ≠ 1 := by
      intro h1
      have hall : Finset.univ.filter (fun p : Fin 306936 => subLab p = 1) ⊆ Ψ := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨h, hh, rfl⟩ := subLab_orb k q (by rw [h1, hq.2])
        have hfix : (pt 0).sp.map (Matrix.mulVecLin (((h : GL (Fin 781) (ZMod 3))) :
            Matrix (Fin 781) (Fin 781) (ZMod 3))) = (pt 0).sp := by
          have := hPs h root
          rw [lvl_one_fix hh] at this
          exact this
        obtain ⟨k', hk', e⟩ := hstab h (hJ h.2) hfix k hk
        rw [hPs] at e
        rw [hP e]
        exact hk'
      have := Finset.card_le_card hall
      rw [card_subLab_one, hcard] at this
      omega
    rcases hl : subLab k with ⟨_ | _ | _ | n, hn⟩
    · exact absurd hl hk0
    · exact absurd hl hk1
    · rfl
    · omega
  have hΨ : Ψ = Finset.univ.filter (fun p : Fin 306936 => subLab p = 2) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_subLab_two, hcard])
  have hfix : ∀ k : Fin 306936, a • k = k ↔ (P k).map (Matrix.mulVecLin mA) = P k := by
    intro k
    rw [← mat_a, hPs a k]
    exact ⟨fun h => by rw [h], fun h => hP h⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hcnt, hΨ, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun k _ => by rw [hfix k])

theorem a_mul_a : a * a = 1 := by
  rw [← sq]
  exact a_sq

theorem edgeSwap_a :
    EdgeSwap a where
  swap_tR := (cls_smul_root a).symm
  swap_xb := by
    rw [show xb = jR a * tR * (jR a)⁻¹ from cls_smul_root a]
    rw [show jR a * (jR a * tR * (jR a)⁻¹) * (jR a)⁻¹ = (jR a * jR a) * tR * (jR a * jR a)⁻¹ by
      group, ← map_mul, a_mul_a, map_one, one_mul, inv_one, mul_one]
  sq := a_mul_a
  fixed := by
    rw [← card_fixed_a]
    symm
    refine Nat.card_eq_of_bijective (fun k => ⟨⟨cls k.1, ?_⟩, ?_⟩) ⟨?_, ?_⟩
    ·
      have h1 : cls k.1 ∈ LocalClass D24 tR := (mem_localClass_iff k.1).2 k.2.1
      refine ⟨h1, ?_⟩
      have h2 : jR a * cls k.1 * (jR a)⁻¹ ∈ LocalClass D24 (jR a * tR * (jR a)⁻¹) :=
        (Pair.conj_mem_localClass_iff pair_R (jR a) (e := tR) (f := cls k.1)).2 h1
      rw [← cls_smul, k.2.2, show jR a * tR * (jR a)⁻¹ = xb from (cls_smul_root a).symm] at h2
      exact h2
    · show jR a * cls k.1 * (jR a)⁻¹ = cls k.1
      rw [← cls_smul, k.2.2]
    · intro k k' h
      have h' := congrArg (fun w : {w : ↥(LocalClass D24 tR ∩ LocalClass D24 xb) //
        jR a * (w : R) * (jR a)⁻¹ = w} => ((w : ↥(LocalClass D24 tR ∩ LocalClass D24 xb)) : R)) h
      exact Subtype.ext (cls_injective h')
    · rintro ⟨⟨w, hw⟩, hwf⟩
      obtain ⟨k, rfl⟩ := exists_cls hw.1.1
      refine ⟨⟨k, (mem_localClass_iff k).1 hw.1, ?_⟩, rfl⟩
      have : cls (a • k) = cls k := by rw [cls_smul]; exact hwf
      exact cls_injective this

end CFSG.Sporadic.Fi24
