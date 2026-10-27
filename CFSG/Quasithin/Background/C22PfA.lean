module

public import CFSG.Quasithin.Background.C2PushQuot
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.C2Push

namespace C22Pf

section Signalizer

variable {G : Type*} [Group G] [Finite G]

theorem le_of_signalizer {H R S : Subgroup G} (hRH : R ≤ H)
    (hRe : R = pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)))
    (hS : IsSignalizer H (H ⊓ Subgroup.normalizer (R : Set G)) S) : S ≤ R := by
  have hRp : IsPGroup 2 R := by rw [hRe]; exact pCoreOf_isPGroup 2 _
  have hXn : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (S : Set G) := hS.2.2
  have hRX : R ≤ H ⊓ Subgroup.normalizer (R : Set G) := le_inf hRH Subgroup.le_normalizer
  set P := S ⊔ R with hP
  have hRS : R ≤ Subgroup.normalizer (S : Set G) := hRX.trans hXn
  have hPp : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hS.2.1 hRp hRS
  have hPH : P ≤ H := sup_le hS.1 hRH
  have hXP : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup S R ⟨hXn hx, hx.2⟩
  have hPR : P ≤ R := by
    by_contra hnot
    have hlt : R < P := lt_of_le_of_ne le_sup_right (fun h => hnot (h ▸ le_rfl))
    obtain ⟨x, hxP, hxN, hxR⟩ := A4.exists_mem_normalizer_not_mem hPp hlt
    have hQ : (P ⊓ (H ⊓ Subgroup.normalizer (R : Set G))) ≤ R := by
      have hle : P ⊓ (H ⊓ Subgroup.normalizer (R : Set G)) ≤
          pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
        le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun g hg =>
            Subgroup.inf_normalizer_le_normalizer_inf ⟨hXP hg, Subgroup.le_normalizer hg⟩)
          (hPp.to_le inf_le_left)
      exact hle.trans hRe.symm.le
    exact hxR (hQ ⟨hxP, hPH hxP, hxN⟩)
  exact le_sup_left.trans hPR

end Signalizer

section Key

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_conj_map_conj (U : Subgroup X) (a b : X) :
    (U.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      U.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem map_conj_mem_cComp {L : Subgroup X} (hL : L ∈ cComp (⊤ : Subgroup X)) (g : X) :
    L.map (MulAut.conj g).toMonoidHom ∈ cComp (⊤ : Subgroup X) := by
  have h := cComp_map_mulEquiv (MulAut.conj g) hL
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h

theorem le_of_le_cComp (h37 : A37Statement X) {R L U : Subgroup X}
    (hRe : R = pCoreOf 2 (Subgroup.normalizer (R : Set X))) (hL : L ∈ cComp (⊤ : Subgroup X))
    (hUL : U ≤ L) (hU : IsPGroup 2 ↥U)
    (hN : Subgroup.normalizer (R : Set X) ⊓ Subgroup.normalizer (L : Set X) ≤
      Subgroup.normalizer (U : Set X)) : U ≤ R := by
  classical
  set K := Subgroup.normalizer (R : Set X) with hK
  let ι := {V : Subgroup X // ∃ k ∈ K, V = U.map (MulAut.conj k).toMonoidHom}
  let A : ι → Subgroup X := fun V => V.1
  have hA2 : ∀ V, IsPGroup 2 ↥(A V) := by
    rintro ⟨V, k, -, rfl⟩
    exact hU.map _
  have hcomm : ∀ V W, V ≠ W → ⁅A V, A W⁆ = ⊥ := by
    rintro ⟨V, k, hk, rfl⟩ ⟨W, k', hk', rfl⟩ hne
    have hLne : L.map (MulAut.conj k).toMonoidHom ≠ L.map (MulAut.conj k').toMonoidHom := by
      intro he
      apply hne
      apply Subtype.ext
      have h1 : L.map (MulAut.conj (k⁻¹ * k')).toMonoidHom = L := by
        rw [← map_conj_map_conj, ← he, map_conj_map_conj, inv_mul_cancel]
        ext x
        simp
      have hkk : k⁻¹ * k' ∈ K ⊓ Subgroup.normalizer (L : Set X) :=
        ⟨K.mul_mem (K.inv_mem hk) hk', Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1⟩
      have h2 : U.map (MulAut.conj (k⁻¹ * k')).toMonoidHom = U :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hkk)
      show U.map (MulAut.conj k).toMonoidHom = U.map (MulAut.conj k').toMonoidHom
      have e : U.map (MulAut.conj k').toMonoidHom =
          (U.map (MulAut.conj (k⁻¹ * k')).toMonoidHom).map (MulAut.conj k).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel_left]
      rw [e, h2]
    have h37' := h37 _ (map_conj_mem_cComp hL k) _ (map_conj_mem_cComp hL k') hLne
    exact le_bot_iff.mp (h37' ▸ Subgroup.commutator_mono (Subgroup.map_mono hUL)
      (Subgroup.map_mono hUL))
  set P : Subgroup X := ⨆ V, A V with hP
  have hP2 : IsPGroup 2 ↥P := isPGroup_iSup_of_pairwise_commute A hA2 hcomm
  have hKP : K ≤ Subgroup.normalizer (P : Set X) := by
    refine le_normalizer_of_forall_conj_mem fun k hk s hs => ?_
    have hle : P.map (MulAut.conj k).toMonoidHom ≤ P := by
      rw [hP, Subgroup.map_iSup]
      refine iSup_le fun V => ?_
      obtain ⟨V, k', hk', rfl⟩ := V
      show (U.map (MulAut.conj k').toMonoidHom).map (MulAut.conj k).toMonoidHom ≤ P
      rw [map_conj_map_conj]
      exact le_iSup A ⟨_, k * k', K.mul_mem hk hk', rfl⟩
    exact hle ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hUP : U ≤ P := by
    refine le_trans ?_ (le_iSup A ⟨U, 1, K.one_mem, ?_⟩)
    · exact le_rfl
    · ext x
      simp
  have hRe' : R = pCoreOf 2 ((⊤ : Subgroup X) ⊓ Subgroup.normalizer (R : Set X)) := by
    rw [top_inf_eq]
    exact hRe
  have hPR : P ≤ R := le_of_signalizer le_top hRe' ⟨le_top, hP2, by rw [top_inf_eq]; exact hKP⟩
  exact hUP.trans hPR

end Key

end C22Pf

end CFSG.Quasithin
