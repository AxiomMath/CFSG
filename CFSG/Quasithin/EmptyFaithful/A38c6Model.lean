module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmMain
public import CFSG.Quasithin.EmptyFaithful.A38c6Par
public import CFSG.Quasithin.EmptyFaithful.A38c6VSub
public import CFSG.Quasithin.EmptyFaithful.A38c6Classes
public import CFSG.Quasithin.EmptyFaithful.A38c6B3Classes
public import CFSG.Quasithin.EmptyFaithful.A38c6TStruct

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A38c5 CFSG.Quasithin.A38c5.Fm

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin.B3

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

theorem exists_s8_model
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6)
    {S₀ L₀ K₀ : Subgroup (MulAut W)} (hS : IsSylowTwoOf S₀ (orthogonalGroupOf q))
    (hLΩ : L₀ ≤ orthogonalGroupOf q) (hLn : (L₀.subgroupOf (orthogonalGroupOf q)).Normal)
    (hLp : ⁅L₀, L₀⁆ = L₀) (hL1 : L₀ ≠ ⊥) (hK : IsMaxParabolic2 L₀ K₀)
    (hSK : S₀ ≤ Subgroup.normalizer (K₀ : Set (MulAut W))) :
    ∃ (ψ : B3.Gp 8 →* MulAut W) (η : Mod.V 8 Mod.ut0 ≃* W) (T K₈ : Subgroup (B3.Gp 8)),
      Function.Injective ψ ∧ ψ = (H.congrHom η).comp (Mod.act 8 Mod.ut0) ∧
      ψ.range = orthogonalGroupOf q ∧ IsSylowTwoOf T ⊤ ∧ B3.Dsub 8 ≤ T ∧ T.map ψ = S₀ ∧
      L₀ = (alternatingGroup (Fin 8)).map ψ ∧ K₈ ≤ alternatingGroup (Fin 8) ∧
      IsMaxParabolic2 (alternatingGroup (Fin 8)) K₈ ∧
      T ≤ Subgroup.normalizer (K₈ : Set (B3.Gp 8)) ∧ K₀ = K₈.map ψ ∧
      (∀ A : Subgroup (B3.Gp 8), A ≤ T →
        (IsStrongFFStarOffender (T.map (Mod.act 8 Mod.ut0)) (A.map (Mod.act 8 Mod.ut0)) ↔
          A = B3.Dsub 8)) := by
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
  have hK₀le : K₀ ≤ (alternatingGroup (Fin 8)).map ψ := by
    have := hK.1.1
    rwa [hL₈] at this
  have hK₀range : K₀ ≤ ψ.range := hK₀le.trans (Subgroup.map_le_range _ _)
  have hK₀e : (K₀.comap ψ).map ψ = K₀ := Subgroup.map_comap_eq_self hK₀range
  have hK₈ : IsMaxParabolic2 (alternatingGroup (Fin 8)) (K₀.comap ψ) := by
    refine (isMaxParabolic2_map_iff ψ hψinj _ _).1 ?_
    rw [hK₀e, ← hL₈]
    exact hK
  have hTN : (T : Subgroup (B3.Gp 8)) ≤ Subgroup.normalizer ((K₀.comap ψ : Subgroup (B3.Gp 8)) :
      Set (B3.Gp 8)) := by
    refine (map_le_normalizer_map_iff ψ hψinj _ _).1 ?_
    rw [hK₀e, hSψ]
    exact hSK
  refine ⟨ψ, η, T, K₀.comap ψ, hψinj, hψη, hψrange, hTsyl, hTD, hSψ, hL₈, hK₈.1.1, hK₈, hTN,
    hK₀e.symm, ?_⟩
  intro A hAle
  exact hTs A hAle


theorem isFFStarOffender_psi_iff {W : Type} [CommGroup W] (η : Mod.V 8 Mod.ut0 ≃* W)
    {T A : Subgroup (B3.Gp 8)} (hAT : A ≤ T) :
    IsFFStarOffender (T.map ((H.congrHom η).comp (Mod.act 8 Mod.ut0)))
        (A.map ((H.congrHom η).comp (Mod.act 8 Mod.ut0))) ↔ IsOffG 8 Mod.ut0 A := by
  rw [← Subgroup.map_map, ← Subgroup.map_map, isFFStarOffender_map_congrHom_iff]
  unfold IsOffG
  constructor
  · intro h
    exact ⟨h.1.trans (Subgroup.map_mono le_top), h.2⟩
  · intro h
    exact ⟨Subgroup.map_mono hAT, h.2⟩


theorem nonstrong_data
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6)
    {S₀ L₀ K₀ A₀ : Subgroup (MulAut W)} (hS : IsSylowTwoOf S₀ (orthogonalGroupOf q))
    (hLΩ : L₀ ≤ orthogonalGroupOf q) (hLn : (L₀.subgroupOf (orthogonalGroupOf q)).Normal)
    (hLp : ⁅L₀, L₀⁆ = L₀) (hL1 : L₀ ≠ ⊥) (hK : IsMaxParabolic2 L₀ K₀)
    (hSK : S₀ ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    (hA : IsFFStarOffender S₀ A₀)
    (hmin : ∀ B₀ : Subgroup (MulAut W), B₀ ≤ A₀ → IsFFStarOffender S₀ B₀ → B₀ = A₀) :
    rk ↥A₀ = rk ↥(A₀ ⊓ pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) + 1 := by
  obtain ⟨ψ, η, T, K₈, hψinj, hψη, hψrange, hTsyl, hTD, hSψ, hL₈, hK₈A, hK₈max, hTN, hK₀e, -⟩ :=
    exists_s8_model hW q hq hnd E hE hEq hcard hS hLΩ hLn hLp hL1 hK hSK
  have hA₀S : A₀ ≤ S₀ := hA.1
  have hrangeA : A₀ ≤ ψ.range := hψrange ▸ (hA₀S.trans hS.1)
  set A := A₀.comap ψ with hAdef
  have hA₀eq : A.map ψ = A₀ := Subgroup.map_comap_eq_self hrangeA
  have hAT : A ≤ T := by
    have : A ≤ (T.map ψ).comap ψ := Subgroup.comap_mono (hSψ ▸ hA₀S)
    rwa [Subgroup.comap_map_eq_self_of_injective hψinj] at this
  have htr : ∀ B : Subgroup (B3.Gp 8), B ≤ T →
      (IsFFStarOffender S₀ (B.map ψ) ↔ IsOffG 8 Mod.ut0 B) := by
    intro B hBT
    rw [← hSψ, hψη]
    exact isFFStarOffender_psi_iff η hBT
  have hOff : IsOffG 8 Mod.ut0 A := (htr A hAT).1 (by rw [hA₀eq]; exact hA)
  have hminG : ∀ B : Subgroup (B3.Gp 8), B ≤ A → IsOffG 8 Mod.ut0 B → B = A := by
    intro B hBA hB
    have hBT : B ≤ T := hBA.trans hAT
    have h1 : B.map ψ ≤ A₀ := hA₀eq ▸ Subgroup.map_mono hBA
    have h2 := hmin (B.map ψ) h1 ((htr B hBT).2 hB)
    rw [← hA₀eq] at h2
    exact Subgroup.map_injective hψinj h2
  obtain ⟨B, hB, hKeq, hTB⟩ := parabolic_classification hTsyl (dsub_eq_D8 ▸ hTD) hK₈A hK₈max hTN
  have hAB : A ≤ PStab B := hAT.trans hTB
  have hsw : ∀ a b : Fin 8, a ≠ b → IsOffG 8 Mod.ut0 (Subgroup.zpowers (Equiv.swap a b)) :=
    fun a b hab => ((B3.B3_2_6).1 _).2
      (Or.inr (Or.inr (Or.inl ⟨1, le_rfl, by norm_num, zpowers_swap_mem_conjClass hab⟩)))
  have hnoswap : ∀ a b : Fin 8, a ≠ b → ¬ (Subgroup.zpowers (Equiv.swap a b) < A) :=
    fun a b hab hlt => (ne_of_lt hlt) (hminG _ hlt.le (hsw a b hab))
  have key : rk ↥A = rk ↥(A ⊓ Vsub B) + 1 := by
    rcases ((B3.B3_2_6).1 A).1 hOff with hDL | hA0 | ⟨m, hm1, hm4, hAm⟩ | hH | hR
    · obtain ⟨γ, hγ⟩ := exists_cjP_of_mem_conjClass_DL hDL
      have hle : cjP γ (D8 ⊓ alternatingGroup (Fin 8)) ≤ PStab B := hγ ▸ hAB
      have h := rk_cjP_DL hB γ hle
      rw [← hγ] at h
      exact h
    · exfalso
      obtain ⟨a, b, hab, hlt⟩ := exists_swap_lt_of_mem_conjClass_A0 hA0
      exact hnoswap a b hab hlt
    · rcases Nat.eq_or_lt_of_le hm1 with h1 | hm2
      · subst h1
        obtain ⟨a, b, hab, hA'⟩ := exists_swap_of_mem_conjClass_Am_one hAm
        have hle : Subgroup.zpowers (Equiv.swap a b) ≤ PStab B := hA' ▸ hAB
        have h := rk_zpowers_swap hB hab hle
        rw [← hA'] at h
        exact h
      · exfalso
        obtain ⟨a, b, hab, hlt⟩ := exists_swap_lt_of_mem_conjClass_Am hm2 hm4 hAm
        exact hnoswap a b hab hlt
    · exfalso
      obtain ⟨a, b, hab, hlt⟩ := exists_swap_lt_of_mem_Hset hH
      exact hnoswap a b hab hlt
    · exact rk_regE8 hB hR hAB
  have hmap := map_inf_pCoreOf_oPrimeResidualOf_sup ψ hψinj A K₈ T
  rw [hA₀eq, ← hK₀e, hSψ] at hmap
  rw [← hmap, rk_map_of_injective ψ hψinj, ← hA₀eq, rk_map_of_injective ψ hψinj, hKeq,
    pCoreOf_eq_Vsub hB hTB]
  exact key


theorem swap01_mem_D8_not_alt : Equiv.swap (0 : Fin 8) 1 ∈ D8 ∧
    Equiv.swap (0 : Fin 8) 1 ∉ alternatingGroup (Fin 8) := by
  refine ⟨Subgroup.subset_closure (by simp), ?_⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem strong_data'
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6)
    {S₀ L₀ K₀ A₀ : Subgroup (MulAut W)} (hS : IsSylowTwoOf S₀ (orthogonalGroupOf q))
    (hLΩ : L₀ ≤ orthogonalGroupOf q) (hLn : (L₀.subgroupOf (orthogonalGroupOf q)).Normal)
    (hLp : ⁅L₀, L₀⁆ = L₀) (hL1 : L₀ ≠ ⊥) (hK : IsMaxParabolic2 L₀ K₀)
    (hSK : S₀ ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    (hA : IsStrongFFStarOffender S₀ A₀) :
    rkIdx (fixV A₀) = 3 ∧ rk ↥(A₀ ⊓ pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) = 2 ∧
      rk ↥A₀ = 4 ∧ ¬ A₀ ≤ L₀ := by
  obtain ⟨hr3, hr2⟩ := strong_offender_data finiteFactS8 hW q hq hnd E hE hEq hcard hS hLΩ hLn hLp
    hL1 hK hSK hA
  obtain ⟨ψ, η, T, K₈, hψinj, hψη, hψrange, hTsyl, hTD, hSψ, hL₈, hK₈A, hK₈max, hTN, hK₀e, hTs⟩ :=
    exists_s8_model hW q hq hnd E hE hEq hcard hS hLΩ hLn hLp hL1 hK hSK
  have hA₀S : A₀ ≤ S₀ := hA.1.1
  have hrangeA : A₀ ≤ ψ.range := hψrange ▸ (hA₀S.trans hS.1)
  have hA₀eq : (A₀.comap ψ).map ψ = A₀ := Subgroup.map_comap_eq_self hrangeA
  have hAT : A₀.comap ψ ≤ T := by
    have : A₀.comap ψ ≤ (T.map ψ).comap ψ := Subgroup.comap_mono (hSψ ▸ hA₀S)
    rwa [Subgroup.comap_map_eq_self_of_injective hψinj] at this
  have hAstrong : IsStrongFFStarOffender (T.map (Mod.act 8 Mod.ut0))
      ((A₀.comap ψ).map (Mod.act 8 Mod.ut0)) := by
    refine (isStrongFFStarOffender_map_congrHom_iff η).1 ?_
    rw [Subgroup.map_map, Subgroup.map_map, ← hψη, hSψ, hA₀eq]
    exact hA
  have hDe : A₀.comap ψ = B3.Dsub 8 := (hTs _ hAT).1 hAstrong
  have hD : A₀ = (B3.Dsub 8).map ψ := by rw [← hDe, hA₀eq]
  refine ⟨hr3, hr2, ?_, ?_⟩
  · rw [hD, rk_map_of_injective ψ hψinj]
    exact (B3.B3_2_1 (n := 8) (Or.inr (Or.inr (Or.inr rfl))) Mod.ut0 (m := 4) (by norm_num)
      (by norm_num)).1
  · rw [hD, hL₈]
    intro hle
    have h := (Subgroup.map_le_map_iff_of_injective hψinj).1 hle
    rw [dsub_eq_D8] at h
    exact swap01_mem_D8_not_alt.2 (h swap01_mem_D8_not_alt.1)



theorem hat_facts
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6)
    {S₀ L₀ K₀ : Subgroup (MulAut W)} (hS : IsSylowTwoOf S₀ (orthogonalGroupOf q))
    (hLΩ : L₀ ≤ orthogonalGroupOf q) (hLn : (L₀.subgroupOf (orthogonalGroupOf q)).Normal)
    (hLp : ⁅L₀, L₀⁆ = L₀) (hL1 : L₀ ≠ ⊥) (hK : IsMaxParabolic2 L₀ K₀)
    (hSK : S₀ ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    (hPS : pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀) ≤ S₀) :
    pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀) ≤ S₀ ⊓ L₀ ∧
      Nat.card ↥S₀ = 8 * Nat.card ↥(pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) ∧
      Nat.card ↥S₀ = 2 * Nat.card ↥(S₀ ⊓ L₀) ∧
      (∀ x ∈ S₀ ⊓ L₀, x * x ∈ pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) ∧
      (∃ g ∈ S₀, ∃ h ∈ S₀, g * h * g⁻¹ * h⁻¹ ∉ pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) := by
  obtain ⟨ψ, η, T, K₈, hψinj, hψη, hψrange, hTsyl, hTD, hSψ, hL₈, hK₈A, hK₈max, hTN, hK₀e, -⟩ :=
    exists_s8_model hW q hq hnd E hE hEq hcard hS hLΩ hLn hLp hL1 hK hSK
  have hD8 : D8 ≤ T := dsub_eq_D8 ▸ hTD
  obtain ⟨B, hB, hKeq, hTB⟩ := parabolic_classification hTsyl hD8 hK₈A hK₈max hTN
  have hTSmu : T ≤ Smu := le_Smu_of_D8_le hTsyl.2.1 hD8
  have hTSP : T ≤ Smu ⊓ PStab B := le_inf hTSmu hTB
  have hP : pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀) = (Vsub B).map ψ := by
    rw [← hSψ, hK₀e, ← map_oPrimeResidualOf ψ 3 Nat.prime_three, ← Subgroup.map_sup,
      pCoreOf_map_of_injective 2 ψ hψinj, hKeq, pCoreOf_eq_Vsub hB hTB]
  have hcardT : Nat.card ↥T = 2 ^ 7 := card_isSylowTwoOf hTsyl
  have hcardS : Nat.card ↥S₀ = 2 ^ 7 := by
    rw [← hSψ, Subgroup.card_map_of_injective hψinj]
    exact hcardT
  have hcardP : Nat.card ↥(pCoreOf 2 (oPrimeResidualOf 3 K₀ ⊔ S₀)) = 16 := by
    rw [hP, Subgroup.card_map_of_injective hψinj]
    exact Vsub_card hB
  have hSL : S₀ ⊓ L₀ = (T ⊓ alternatingGroup (Fin 8)).map ψ := by
    rw [Subgroup.map_inf _ _ _ hψinj, hSψ, hL₈]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_inf hPS (by
      rw [hP, hL₈]
      exact Subgroup.map_mono (Vsub_le_alt hB))
  · rw [hcardS, hcardP]
    norm_num
  · rw [hSL, Subgroup.card_map_of_injective hψinj, hcardS, ← hcardT]
    have h2 := relIndex_inf_alt hD8
    have h3 := Subgroup.relIndex_mul_card (H := T ⊓ alternatingGroup (Fin 8)) (K := T)
    rw [h2, inf_eq_left.2 inf_le_left] at h3
    exact h3.symm
  · intro x hx
    rw [hSL] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hP, ← map_mul]
    exact Subgroup.mem_map_of_mem ψ (sq_mem_Vsub hB hTSP hy.1 hy.2)
  · obtain ⟨g, hg, h, hh, hgh⟩ := exists_comm_not_mem_Vsub hB hTSP hD8 (isSylowTwoOf_transitive hTsyl)
    refine ⟨ψ g, ?_, ψ h, ?_, ?_⟩
    · rw [← hSψ]; exact Subgroup.mem_map_of_mem ψ hg
    · rw [← hSψ]; exact Subgroup.mem_map_of_mem ψ hh
    · rw [hP]
      intro hmem
      apply hgh
      obtain ⟨z, hz, hzz⟩ := hmem
      have : z = g * h * g⁻¹ * h⁻¹ := hψinj (by rw [hzz]; simp [map_mul, map_inv])
      rwa [← this]

end CFSG.Quasithin.A38c6
