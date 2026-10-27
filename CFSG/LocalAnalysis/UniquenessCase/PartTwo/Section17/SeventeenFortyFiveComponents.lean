module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cComp_conjClosure_eq_range {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.Quasithin.cComp (conjClosure M L) =
      Set.range (fun m : ↥M => L.map (MulAut.conj (m : G)).toMonoidHom) := by
  have hLc : L ∈ CFSG.Quasithin.cComp M :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22s.mem_cComp_of_mem_calC hL
  have h := uc22p20b_cComp_orb (T := M) (H := M) (K := L) hLc le_rfl
  have horb : uc22p20bOrb M L = conjClosure M L := by
    rw [uc22br4_conjClosure_eq]
    rfl
  rw [horb] at h
  exact h

theorem cCompSpan_conjClosure {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.Quasithin.cCompSpan (conjClosure M L) = conjClosure M L := by
  unfold CFSG.Quasithin.cCompSpan
  rw [cComp_conjClosure_eq_range hL]
  rw [sSup_range]
  exact (uc22br4_conjClosure_eq M L).symm

theorem component_normal_in_conjClosure {M L : Subgroup G} (hL : L ∈ calC M) :
    (L.subgroupOf (conjClosure M L)).Normal := by
  have hmem : L ∈ CFSG.Quasithin.cComp (conjClosure M L) := by
    rw [cComp_conjClosure_eq_range hL]
    refine ⟨⟨1, M.one_mem⟩, ?_⟩
    change L.map (MulAut.conj (1 : G)).toMonoidHom = L
    rw [show (MulAut.conj (1 : G)) = 1 by simp]
    exact Subgroup.map_id L
  have h := CFSG.Quasithin.cComp_normal_span_of_le hmem
  rw [cCompSpan_conjClosure hL] at h
  exact h.2

theorem conjSetOf_eq_of_sup {M X K L : Subgroup G} (hXM : X ≤ M) (hKM : K ≤ M)
    (hM : M ≤ X ⊔ K) (hXN : (X.subgroupOf M).Normal)
    (hXL : X ≤ normalizer (L : Set G)) :
    conjSetOf M L = conjSetOf K L := by
  classical
  apply Set.Subset.antisymm
  · rintro K' ⟨m, hm, rfl⟩
    have hsup : X ⊔ K = M := le_antisymm (sup_le hXM hKM) hM
    have htop : (K.subgroupOf M) ⊔ (X.subgroupOf M) = ⊤ := by
      rw [sup_comm, ← Subgroup.subgroupOf_sup hXM hKM, hsup]
      exact Subgroup.subgroupOf_self M
    have hm' : (⟨m, hm⟩ : ↥M) ∈ (K.subgroupOf M) ⊔ (X.subgroupOf M) := by
      rw [htop]; trivial
    obtain ⟨k, hk, x, hx, hkx⟩ := (Subgroup.mem_sup_of_normal_right).1 hm'
    have hxX : (x : G) ∈ X := hx
    have hkK : (k : G) ∈ K := hk
    have hmul : (k : G) * (x : G) = m := congrArg Subtype.val hkx
    refine ⟨(k : G), hkK, ?_⟩
    have hxL : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXL hxX)
    have hmap : L.map ((MulAut.conj (k : G) * MulAut.conj (x : G))).toMonoidHom =
        L.map (MulAut.conj (k : G)).toMonoidHom := by
      change L.map ((MulAut.conj (k : G)).toMonoidHom.comp
        (MulAut.conj (x : G)).toMonoidHom) = L.map (MulAut.conj (k : G)).toMonoidHom
      rw [← Subgroup.map_map, hxL]
    calc
      L.map (MulAut.conj m).toMonoidHom
          = L.map (MulAut.conj ((k : G) * (x : G))).toMonoidHom := by rw [hmul]
      _ = L.map ((MulAut.conj (k : G) * MulAut.conj (x : G))).toMonoidHom := by rw [map_mul]
      _ = L.map (MulAut.conj (k : G)).toMonoidHom := hmap
  · rintro K' ⟨k, hk, rfl⟩
    exact ⟨k, hKM hk, rfl⟩

theorem ncard_Gamma_eq_ncard_conjSetOf {H K L : Subgroup G} {Γ : Set G}
    (hreps : CIsCosetReps H K Γ) (hH : H = K ⊓ normalizer (L : Set G)) :
    Γ.ncard = (conjSetOf K L).ncard := by
  classical
  refine Set.ncard_congr (t := conjSetOf K L)
    (fun γ _ => L.map (MulAut.conj (γ⁻¹)).toMonoidHom) ?_ ?_ ?_
  · intro γ hγ
    exact ⟨γ⁻¹, K.inv_mem (hreps.1 hγ), rfl⟩
  · intro γ γ' hγ hγ' heq
    have hγK : γ ∈ K := hreps.1 hγ
    have hγ'K : γ' ∈ K := hreps.1 hγ'
    have hmap : L.map (MulAut.conj (γ * γ'⁻¹)).toMonoidHom = L := by
      have h1 : (L.map (MulAut.conj (γ'⁻¹)).toMonoidHom).map (MulAut.conj γ).toMonoidHom =
          (L.map (MulAut.conj (γ⁻¹)).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
        rw [heq]
      have hleft : (L.map (MulAut.conj (γ'⁻¹)).toMonoidHom).map (MulAut.conj γ).toMonoidHom =
          L.map (MulAut.conj (γ * γ'⁻¹)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, MulAut.mul_apply, MonoidHom.comp_apply, mul_assoc]
      have hright : (L.map (MulAut.conj (γ⁻¹)).toMonoidHom).map
          (MulAut.conj γ).toMonoidHom = L := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj γ).toMonoidHom.comp (MulAut.conj (γ⁻¹)).toMonoidHom =
            MonoidHom.id G := by
          ext x
          simp [MulAut.conj_apply]
          group
        rw [hcomp, Subgroup.map_id]
      rw [hleft] at h1
      rw [hright] at h1
      exact h1
    have hmemN : γ * γ'⁻¹ ∈ normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
    have hhH : γ * γ'⁻¹ ∈ H := by
      rw [hH]
      exact Subgroup.mem_inf.mpr ⟨K.mul_mem hγK (K.inv_mem hγ'K), hmemN⟩
    obtain ⟨γ₀, hP₀, huniq⟩ := hreps.2 γ hγK
    have hPγ : γ ∈ Γ ∧ ∃ h ∈ H, γ = h * γ :=
      ⟨hγ, ⟨1, H.one_mem, by group⟩⟩
    have hPγ' : γ' ∈ Γ ∧ ∃ h ∈ H, γ = h * γ' :=
      ⟨hγ', ⟨γ * γ'⁻¹, hhH, by group⟩⟩
    have h1 : γ = γ₀ := huniq γ hPγ
    have h2 : γ' = γ₀ := huniq γ' hPγ'
    exact h1.trans h2.symm
  · intro K' hK'
    obtain ⟨k, hk, rfl⟩ := hK'
    obtain ⟨γ, hP, -⟩ := hreps.2 k⁻¹ (K.inv_mem hk)
    obtain ⟨hh, hhh, hk'⟩ := hP.2
    refine ⟨γ, hP.1, ?_⟩
    have hhN : hh ∈ normalizer (L : Set G) := (hH ▸ hhh).2
    have hk_eq : k = γ⁻¹ * hh⁻¹ := by
      rw [show k = (k⁻¹)⁻¹ by group, hk']
      group
    have hhfix : L.map (MulAut.conj (hh⁻¹)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).inv_mem hhN)
    calc
      L.map (MulAut.conj (γ⁻¹)).toMonoidHom
          = (L.map (MulAut.conj (hh⁻¹)).toMonoidHom).map (MulAut.conj (γ⁻¹)).toMonoidHom := by
              rw [hhfix]
      _ = L.map (MulAut.conj (γ⁻¹ * hh⁻¹)).toMonoidHom := by
              rw [Subgroup.map_map]
              congr 1
              ext x
              simp [MulAut.conj_apply, MulAut.mul_apply, MonoidHom.comp_apply, mul_assoc]
      _ = L.map (MulAut.conj k).toMonoidHom := by rw [← hk_eq]

theorem Ctx17_42.ncard_Gamma_eq_card_conjSet {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    Gamma.ncard = (conjSetOf D.M L).ncard := by
  classical
  let X' : Subgroup G := conjClosure D.M L
  let K' : Subgroup G := D.M ⊓ normalizer ((D.T ⊓ X' : Subgroup G) : Set G)
  have hreps : CIsCosetReps
      ((D.M ⊓ normalizer ((D.T ⊓ X' : Subgroup G) : Set G)) ⊓ normalizer (L : Set G))
      K' Gamma := by
    simpa [X', K', ctx.X_eq] using ctx.reps
  have hH : ((D.M ⊓ normalizer ((D.T ⊓ X' : Subgroup G) : Set G)) ⊓
      normalizer (L : Set G)) = K' ⊓ normalizer (L : Set G) := rfl
  have hΓ : Gamma.ncard = (conjSetOf K' L).ncard :=
    ncard_Gamma_eq_ncard_conjSetOf hreps hH
  have hXM : X' ≤ D.M :=
    uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) ctx.mem_calC.1.le
  have hMX : D.M ≤ normalizer (X' : Set G) := by
    simpa [X'] using uc22p22v_le_normalizer_conjClosure D.M L
  have hXN : (X'.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := X') (K := D.M) hXM).mpr hMX
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ X') X' :=
    uc22p22r_fo_sylow_inf (p := 2) D.sylowM
      (CFSG.Open.IsSubnormal.step hXM hXN (CFSG.Open.IsSubnormal.refl D.M))
  have hM : D.M ≤ X' ⊔ K' := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simpa [K'] using uc22p22t_frattini_sup (q := 2) hXM hMX hS
  have hLX : L ≤ X' := by
    simpa [X'] using uc22p22v_le_conjClosure D.M L
  have hXL : X' ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := L) (K := X') hLX).mp
      (by simpa [X'] using component_normal_in_conjClosure ctx.mem_calC)
  have hEq : conjSetOf K' L = conjSetOf D.M L :=
    (conjSetOf_eq_of_sup (M := D.M) (X := X') (K := K') (L := L)
      hXM inf_le_left hM hXN hXL).symm
  rw [hΓ, hEq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
