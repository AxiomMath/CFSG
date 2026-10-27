module

public import CFSG.Quasithin.EmptyFaithful.A38c5Model
public import CFSG.Quasithin.EmptyFaithful.A38c5Hom
public import CFSG.Quasithin.Background.B3Two
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5

open CFSG.Quasithin.B3

@[expose] def FiniteFactS8 : Prop :=
  ∀ T₁ : Subgroup (B3.Gp 8), IsSylowTwoOf T₁ ⊤ → B3.Dsub 8 ≤ T₁ →
    ∀ K : Subgroup (B3.Gp 8), K ≤ alternatingGroup (Fin 8) →
      IsMaxParabolic2 (alternatingGroup (Fin 8)) K → T₁ ≤ Subgroup.normalizer (K : Set (B3.Gp 8)) →
        rk ↥(B3.Dsub 8 ⊓ pCoreOf 2 (oPrimeResidualOf 3 K ⊔ T₁)) = 2

section Offender

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem isFFStarOffender_map_congrHom_iff (e : V ≃* W) {X A : Subgroup (MulAut V)} :
    IsFFStarOffender (X.map (H.congrHom e)) (A.map (H.congrHom e)) ↔ IsFFStarOffender X A :=
  isFFStarOffender_map_congr_equiv_iff e

theorem rAV_map_congrHom (e : V ≃* W) (A : Subgroup (MulAut V)) :
    rAV (A.map (H.congrHom e)) = rAV A := by
  unfold rAV
  rw [H.rkIdx_fixV_map_congrHom, H.rk_map_congrHom]

theorem isStrongFFStarOffender_map_congrHom_iff (e : V ≃* W) {X A : Subgroup (MulAut V)} :
    IsStrongFFStarOffender (X.map (H.congrHom e)) (A.map (H.congrHom e)) ↔
      IsStrongFFStarOffender X A := by
  unfold IsStrongFFStarOffender
  rw [isFFStarOffender_map_congrHom_iff, rAV_map_congrHom]

end Offender

section Omega

private theorem exists_conj_of_isSylowTwoOf_top {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

private theorem isSylowTwoOf_top_of_sylow {X : Type} [Group X] [Finite X] (T : Sylow 2 X) :
    IsSylowTwoOf (T : Subgroup X) ⊤ := by
  refine ⟨le_top, T.isPGroup', ?_⟩
  show ¬ 2 ∣ (T : Subgroup X).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

theorem eq_alternatingGroup_of_perfect_normal {K : Subgroup (Equiv.Perm (Fin 8))} (hn : K.Normal)
    (hperf : ⁅K, K⁆ = K) (hbot : K ≠ ⊥) : K = alternatingGroup (Fin 8) := by
  have hcomm : ⁅(⊤ : Subgroup (Equiv.Perm (Fin 8))), ⊤⁆ = alternatingGroup (Fin 8) :=
    alternatingGroup.commutator_perm_eq (by simp)
  have hle : K ≤ alternatingGroup (Fin 8) := by
    rw [← hcomm, ← hperf]
    exact Subgroup.commutator_mono le_top le_top
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) := hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem strong_offender_data (hFM : FiniteFactS8)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6)
    {S₀ L₀ K₀ A₀ : Subgroup (MulAut W)} (hS : IsSylowTwoOf S₀ (orthogonalGroupOf q))
    (hLΩ : L₀ ≤ orthogonalGroupOf q) (hLn : (L₀.subgroupOf (orthogonalGroupOf q)).Normal)
    (hLp : ⁅L₀, L₀⁆ = L₀) (hL1 : L₀ ≠ ⊥) (hK : IsMaxParabolic2 L₀ K₀)
    (hSK : S₀ ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    (hA : IsStrongFFStarOffender S₀ A₀) :
    rkIdx (fixV A₀) = 3 ∧ rk ↥(A₀ ⊓ pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) = 2 := by
  obtain ⟨ε, hε⟩ := exists_model_mulEquiv hW q hq hnd E hE hEq hcard
  have hactinj : Function.Injective (Mod.act 8 Mod.ut0) := B3.act_injective (by norm_num) _
  set ψ₀ : B3.Gp 8 →* MulAut W := (H.congrHom ε.symm).comp (Mod.act 8 Mod.ut0) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ := (H.congrHom_injective ε.symm).comp hactinj
  have hψ₀range : ψ₀.range = orthogonalGroupOf q := by
    rw [hψ₀, MonoidHom.range_comp, ← hε, Subgroup.map_map]
    have : (H.congrHom ε.symm).comp (H.congrHom ε) = MonoidHom.id (MulAut W) := by
      ext x v
      simp
    rw [this, Subgroup.map_id]
  obtain ⟨-, ⟨T, hTm, -, -, hTs⟩, -⟩ := B3.B3_2_6
  have hTD : B3.Dsub 8 ≤ (T : Subgroup (B3.Gp 8)) := hTm 4 (by norm_num)
  have hTsyl : IsSylowTwoOf (T : Subgroup (B3.Gp 8)) ⊤ := isSylowTwoOf_top_of_sylow T
  have hS₀le : S₀ ≤ ψ₀.range := hψ₀range ▸ hS.1
  have hT₀ : IsSylowTwoOf (S₀.comap ψ₀) ⊤ := by
    have h1 : IsSylowTwoOf ((S₀.comap ψ₀).map ψ₀) ((⊤ : Subgroup (B3.Gp 8)).map ψ₀) := by
      rw [Subgroup.map_comap_eq_self hS₀le, ← MonoidHom.range_eq_map, hψ₀range]
      exact hS
    exact (isSylowTwoOf_map_iff ψ₀ hψ₀inj _ _).1 h1
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hTsyl hT₀
  set cj : B3.Gp 8 →* B3.Gp 8 := (MulAut.conj g).toMonoidHom with hcj
  have hcjinj : Function.Injective cj := (MulAut.conj g).injective
  set ψ : B3.Gp 8 →* MulAut W := ψ₀.comp cj with hψ
  have hψinj : Function.Injective ψ := hψ₀inj.comp hcjinj
  have hcjsurj : Function.Surjective cj := (MulAut.conj g).surjective
  have hψrange : ψ.range = orthogonalGroupOf q := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hcjsurj, ← MonoidHom.range_eq_map,
      hψ₀range]
  have hSψ : (T : Subgroup (B3.Gp 8)).map ψ = S₀ := by
    rw [hψ, ← Subgroup.map_map, hg, Subgroup.map_comap_eq_self hS₀le]
  set η : Mod.V 8 Mod.ut0 ≃* W := (Mod.act 8 Mod.ut0 g).trans ε.symm with hη
  have hψη : ψ = (H.congrHom η).comp (Mod.act 8 Mod.ut0) := by
    ext σ v
    simp [hψ, hψ₀, hcj, hη]
  have hL₈ : L₀ = (alternatingGroup (Fin 8)).map ψ := by
    have hLrange : L₀ ≤ ψ.range := hψrange ▸ hLΩ
    have hLe : (L₀.comap ψ).map ψ = L₀ := Subgroup.map_comap_eq_self hLrange
    have hn : (L₀.comap ψ).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      have hxΩ : ψ x ∈ orthogonalGroupOf q := hψrange ▸ ⟨x, rfl⟩
      have hgΩ : ψ g ∈ orthogonalGroupOf q := hψrange ▸ ⟨g, rfl⟩
      have := hLn.conj_mem ⟨ψ x, hxΩ⟩ hx ⟨ψ g, hgΩ⟩
      exact this
    have hperf : ⁅L₀.comap ψ, L₀.comap ψ⁆ = L₀.comap ψ := by
      apply Subgroup.map_injective hψinj
      rw [Subgroup.map_commutator, hLe, hLp]
    have hbot : L₀.comap ψ ≠ ⊥ := by
      intro h
      apply hL1
      rw [← hLe, h, Subgroup.map_bot]
    rw [← hLe, eq_alternatingGroup_of_perfect_normal hn hperf hbot]
  have hA₀S : A₀ ≤ S₀ := hA.1.1
  have hrangeA : A₀ ≤ ψ.range := hψrange ▸ (hA₀S.trans hS.1)
  have hAstrong : IsStrongFFStarOffender ((T : Subgroup (B3.Gp 8)).map (Mod.act 8 Mod.ut0))
      ((A₀.comap ψ).map (Mod.act 8 Mod.ut0)) := by
    have h1 : S₀ = ((T : Subgroup (B3.Gp 8)).map (Mod.act 8 Mod.ut0)).map (H.congrHom η) := by
      rw [← hSψ, hψη, Subgroup.map_map]
    have h2 : A₀ = ((A₀.comap ψ).map (Mod.act 8 Mod.ut0)).map (H.congrHom η) := by
      rw [Subgroup.map_map, ← hψη, Subgroup.map_comap_eq_self hrangeA]
    refine (isStrongFFStarOffender_map_congrHom_iff η).1 ?_
    rw [← h1, ← h2]
    exact hA
  have hAle : A₀.comap ψ ≤ (T : Subgroup (B3.Gp 8)) := by
    have : A₀.comap ψ ≤ ((T : Subgroup (B3.Gp 8)).map ψ).comap ψ :=
      Subgroup.comap_mono (hSψ ▸ hA₀S)
    rwa [Subgroup.comap_map_eq_self_of_injective hψinj] at this
  have hDe : A₀.comap ψ = B3.Dsub 8 := (hTs _ hAle).1 hAstrong
  have hD : A₀ = (B3.Dsub 8).map ψ := by rw [← hDe, Subgroup.map_comap_eq_self hrangeA]
  refine ⟨?_, ?_⟩
  ·
    have h1 : A₀ = ((B3.Dsub 8).map (Mod.act 8 Mod.ut0)).map (H.congrHom η) := by
      rw [hD, hψη, Subgroup.map_map]
    rw [h1, H.rkIdx_fixV_map_congrHom]
    have hB := (B3.B3_2_1 (n := 8) (Or.inr (Or.inr (Or.inr rfl))) Mod.ut0 (m := 4) (by norm_num)
      (by norm_num)).2.2 ⟨⟨by norm_num, Or.inr rfl⟩, by norm_num⟩
    exact hB
  ·
    have hK₀le : K₀ ≤ (alternatingGroup (Fin 8)).map ψ := by
      have := hK.1.1
      rwa [hL₈] at this
    have hK₀range : K₀ ≤ ψ.range := hK₀le.trans (Subgroup.map_le_range _ _)
    have hK₀e : (K₀.comap ψ).map ψ = K₀ := Subgroup.map_comap_eq_self hK₀range
    have hK₈ : IsMaxParabolic2 (alternatingGroup (Fin 8)) (K₀.comap ψ) := by
      refine (isMaxParabolic2_map_iff ψ hψinj _ _).1 ?_
      rw [hK₀e, ← hL₈]
      exact hK
    have hK₈le : K₀.comap ψ ≤ alternatingGroup (Fin 8) := hK₈.1.1
    have hTN : (T : Subgroup (B3.Gp 8)) ≤ Subgroup.normalizer ((K₀.comap ψ : Subgroup (B3.Gp 8)) :
        Set (B3.Gp 8)) := by
      refine (map_le_normalizer_map_iff ψ hψinj _ _).1 ?_
      rw [hK₀e, hSψ]
      exact hSK
    have hfm := hFM T hTsyl hTD (K₀.comap ψ) hK₈le hK₈ hTN
    have hmap := map_inf_pCoreOf_oPrimeResidualOf_sup ψ hψinj (B3.Dsub 8) (K₀.comap ψ) T
    rw [← hD, hK₀e, hSψ] at hmap
    rw [← hmap, rk_map_of_injective ψ hψinj]
    exact hfm

end Omega

end CFSG.Quasithin.A38c5
