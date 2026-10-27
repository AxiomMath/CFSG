module

public import CFSG.Quasithin.MS93.S512NTop
public import CFSG.Quasithin.MS93.S512NChg
public import CFSG.Quasithin.MS93.S512NInn

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace NatHyp

variable {h : PUHyp M T L} {V E Z Y : Subgroup (puAmalgam h.le).Universal}
  (hn : NatHyp h k V E Z Y)
  {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)

include hn hs in
theorem rho_eq_of_mem_T (hk : k = 1) (t : ↥M) (ht : (t : G) ∈ T) (z : ↥V)
    (hz : (z : (puAmalgam h.le).Universal) ∈ Z) : ρ (eM h.le t) (p z) = p z := by
  have htst := (eM h.le t).2
  rw [hs.conj (eM h.le t) z (S36E.conj_mem hn.vn htst z.2), hs.eq_iff]
  refine ⟨V.mul_mem (S36E.conj_mem hn.vn htst z.2) (V.inv_mem z.2), ?_⟩
  have htQ : (eM h.le t : (puAmalgam h.le).Universal) ∈ Qv _ (baseB (puAmalgam h.le)) := by
    rw [puAmalgam.qv_baseB, coe_eM]
    exact ⟨t, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have h1 := (S5.bSub h.le L (baseA _)).inv_mem
    (hn.zt hk (Subgroup.commutator_mem_commutator hz htQ))
  rw [commutatorElement_inv, commutatorElement_def] at h1
  exact h1

include hn hs in
theorem eq_top_of_one (h51 : S51) (hpu : PUMin M T L) (hd : S5.IsSp4Data M T L k F a)
    (hk : k = 1) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] [Fintype F'] (hcard : Fintype.card F' = 2 ^ k)
    {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'} (ha' : Function.Surjective a')
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
        MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) : S₀ = ⊤ := by
  have hk1 : 1 ≤ k := by omega
  have hE := hn.le_kerMod_E hs hk1 hS₀ hne hmin hcard hθ hker
  have hL : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) → g ∈ kerMod ρ hS₀ :=
    fun g hg => hn.mem_kerMod_of_puTrans hk1 hS₀ hE hg
  have hZ := hn.map_Z_sup_eq_top hs hS₀ hL
  have hall : ∀ g, g ∈ kerMod ρ hS₀ := by
    intro g
    obtain ⟨m, rfl⟩ := eM_surjective h.le g
    have hLn : (L.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
    have hmem : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rw [map_mul]
    refine (kerMod ρ hS₀).mul_mem (hL _ ?_) fun s => ?_
    · rw [S5B.puTrans_L_baseA h]
      exact ⟨l, hl, rfl⟩
    · have hs' : s ∈ (Z.subgroupOf V).map p ⊔ S₀ := by
        rw [hZ]
        exact Subgroup.mem_top s
      obtain ⟨y, hy, s₀, hs₀, rfl⟩ := Subgroup.mem_sup.1 hs'
      obtain ⟨z, hz, rfl⟩ := hy
      rw [map_mul_mul_inv, hn.rho_eq_of_mem_T hs hk t (Subgroup.mem_subgroupOf.1 ht) z
        (Subgroup.mem_subgroupOf.1 hz), mul_inv_cancel, one_mul]
      exact S₀.mul_mem (hS₀ _ _ hs₀) (S₀.inv_mem hs₀)
  have hfix : ∀ s : S, (∀ g, ρ g s = s) → s = 1 := fun s hs' =>
    hn.toSecHyp.eq_one_of_fixed hs s fun l _ => hs' l
  subst hk
  have := hd.charP
  have hF : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have hF'2 : Nat.card F' = 2 := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
  obtain ⟨c₁⟩ := MSP.nonempty_ringEquiv_of_card_two hF'2
  obtain ⟨c₂⟩ := MSP.nonempty_ringEquiv_of_card_two hF
  set c : F' ≃+* F := c₁.symm.trans c₂ with hc
  set a'' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F := (chgSp c).toMonoidHom.comp a'
    with ha''def
  set θ'' : ↥S₀ ≃* Multiplicative (MSP.V4 F) := θ.trans (AddEquiv.toMultiplicative (chgV c))
    with hθ''def
  have hθ'' : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ'' (restrict ρ hS₀ g s)) =
        MSP.mat (a'' g) *ᵥ Multiplicative.toAdd (θ'' s) := by
    intro g s
    show chgV c (Multiplicative.toAdd (θ (restrict ρ hS₀ g s))) =
      MSP.mat (chgSp c (a' g)) *ᵥ chgV c (Multiplicative.toAdd (θ s))
    rw [hθ, mat_chgSp_mulVec]
  have ha'' : Function.Surjective a'' := (chgSp c).surjective.comp ha'
  have hker'' : ∀ g, a'' g = 1 ↔ restrict ρ hS₀ g = 1 := fun g => by
    rw [← hker g]
    exact (chgSp c).map_eq_one_iff
  have hρ1 : ∀ g, a'' g = 1 → ρ g = 1 := fun g hg =>
    hn.rho_eq_one_of_restrict hs hS₀ hne hmin hall ((hker'' g).1 hg)
  set ρM := (restrict ρ hS₀).comp (eM h.le) with hρM
  have hρ := hn.toSecHyp.isIrrRep_restrict hs hS₀ hne hmin
  have hKL : ⁅S38E.IsIrrRep.kerG ρM, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (Subgroup.map_subtype_le _) S38E.IsIrrRep.le_normalizer_kerG
      hρ.not_le_kerG
  have hLa := S5Q2.map_L_eq_commutator h hd
  have hkerle : ∀ m : ↥M, a'' (eM h.le m) = 1 → a m = 1 := by
    intro m hm
    have hρm : ρM m = 1 := (hker'' _).1 hm
    have hmK : (m : G) ∈ S38E.IsIrrRep.kerG ρM := ⟨m, hρm, rfl⟩
    apply eq_one_of_commute_commutator hF
    intro y hy
    rw [← hLa] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    have hc := hd.pCoreOf_le_kerG h
      (hKL (Subgroup.commutator_mem_commutator hmK (Subgroup.mem_subgroupOf.1 hl)))
    obtain ⟨hcM, hca⟩ := (S5.mem_kerG a).1 hc
    have e : (⟨⁅(m : G), (l : G)⁆, hcM⟩ : ↥M) = ⁅m, l⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hca
    exact hca
  set f : ↥M →* MSP.Sp4 F := a''.comp (eM h.le) with hfdef
  have hf : Function.Surjective f := ha''.comp (eM_surjective h.le)
  have hfa : f.ker ≤ a.ker := fun m hm => hkerle m hm
  set σ := (f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf))
    ⟨a, hfa⟩ with hσdef
  have hσ : ∀ m, σ (f m) = a m := fun m => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ m
  have hσs : Function.Surjective σ := fun y => by
    obtain ⟨m, rfl⟩ := hd.surj y
    exact ⟨f m, hσ m⟩
  have hσi : Function.Injective σ := Finite.injective_iff_surjective.2 hσs
  set τ : MSP.Sp4 F ≃* MSP.Sp4 F := MulEquiv.ofBijective σ ⟨hσi, hσs⟩ with hτdef
  obtain ⟨e, heE, heQ⟩ := hn.exists_mem_E le_rfl
  obtain ⟨m₀, rfl⟩ := eM_surjective h.le e
  have hm₂ : ∃ i : ℕ, (m₀ : G) ^ 2 ^ i = 1 := by
    refine ⟨1, ?_⟩
    have h1 : (eM h.le m₀ : (puAmalgam h.le).Universal) ^ 2 = 1 := hn.ee.2 _ heE
    have h2 : eM h.le (m₀ ^ 2) = 1 := by
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow]
      exact h1
    have h3 : m₀ ^ 2 = 1 := (eM_injective h.le) (h2.trans (map_one _).symm)
    simpa using congrArg Subtype.val h3
  obtain ⟨hd3, -⟩ := hn.exists_point hs le_rfl hS₀ hne hmin hd.card_eq hθ'' hker''
  have hx1'' : a'' (eM h.le m₀) ≠ 1 := by
    intro h1
    apply heQ
    refine hn.toSecHyp.mem_qv_of_restrict_eq_one hs hS₀ hne hmin ((hker'' _).1 h1) ⟨1, ?_⟩
    simpa using hn.ee.2 _ heE
  obtain ⟨v'', hv'', hve''⟩ := exists_eq_transv hF
    (A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map a'') (by rw [hd3])
    ⟨eM h.le m₀, Subgroup.mem_subgroupOf.2 heE, rfl⟩ hx1''
  have hEM : E ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact hn.es
  obtain ⟨E₀, -, hE₀M, hEE₀⟩ := S5.exists_eq_imM h.le hEM
  have hm₀E₀ : (m₀ : G) ∈ E₀ := by
    have : (puAmalgam h.le).ofA m₀ ∈ imM h.le E₀ := by
      rw [← hEE₀]
      exact heE
    exact (ofA_mem_imM_iff h.le m₀).1 this
  have hcent : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2 := by
    have h1 := hn.eu
    rw [hEE₀, S5.uSub_baseA h, S5.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at h1
    simpa using h1
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have h3 : 3 ≤ Module.finrank F (MSP.fixSp (S5.imSp a E₀)) := by
    have hfixA := nv.card_le_relIndex E₀
    rw [MSP.card_V4, MSP.card_fixSp, hF] at hfixA
    by_contra hlt
    push Not at hlt
    have h2 : 2 ^ Module.finrank F (MSP.fixSp (S5.imSp a E₀)) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hfixA.trans (Nat.mul_le_mul h2 hcent)
    norm_num at this
  have hx1 : a m₀ ≠ 1 := by
    intro h1
    have hmK : (m₀ : G) ∈ S5.kerG a := (S5.mem_kerG a).2 ⟨m₀.2, h1⟩
    have hO := h.mem_pCoreOf_of_rel (S5.le_normalizer_kerG a) (hd.not_le_kerG h) m₀.2 hm₂
      fun l hl => by
        have hlm : l * (m₀ : G)⁻¹ * l⁻¹ ∈ S5.kerG a :=
          (Subgroup.mem_normalizer_iff.1 (S5.le_normalizer_kerG a (h.L_le hl)) _).1
            ((S5.kerG a).inv_mem hmK)
        have e : ⁅(m₀ : G), l⁆ = (m₀ : G) * (l * (m₀ : G)⁻¹ * l⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (S5.kerG a).mul_mem hmK hlm
    apply heQ
    rw [coe_eM, S5B.qv_baseA_eq h]
    exact (ofA_mem_imM_iff h.le m₀).2 hO
  obtain ⟨v, -, hve⟩ := exists_eq_transv hF h3
    (⟨m₀, Subgroup.mem_subgroupOf.2 hm₀E₀, rfl⟩ : a m₀ ∈ S5.imSp a E₀) hx1
  have hτ : τ (MSP.transv v'' 1) = MSP.transv v 1 := by
    rw [← hve'', ← hve]
    exact hσ m₀
  obtain ⟨ψ, hψ⟩ := exists_eq_conj_of_transv hF τ hv'' hτ
  have hconj : ∀ m : ↥M, a'' (eM h.le m) = ψ⁻¹ * a m * ψ := by
    intro m
    have h1 : τ (f m) = ψ * f m * ψ⁻¹ := hψ (f m)
    have h2 : τ (f m) = a m := hσ m
    rw [h2] at h1
    show f m = ψ⁻¹ * a m * ψ
    rw [h1]
    group
  set J : Subgroup ↥(stab (puAmalgam h.le) (baseA _)) :=
    ((S5.jOffM M T L (2 ^ 1)).subgroupOf M).map (eM h.le) with hJdef
  have hJmap : J.map a'' =
      (S5.imSp a (S5.jOffM M T L (2 ^ 1))).map (MulAut.conj ψ⁻¹).toMonoidHom := by
    rw [hJdef, Subgroup.map_map, S5.imSp, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hconj m
  have hJ : Rigid (J.map a'') := by
    rw [hJmap]
    exact (rigid_jOffM h51 hd h hpu hn.b rfl).map_conj ψ⁻¹
  have hJT : S5.jOffM M T L (2 ^ 1) ≤ T := iSup₂_le fun E hE => hE.1.1
  rw [eq_top_iff]
  intro s _
  have hs' : s ∈ (Z.subgroupOf V).map p ⊔ S₀ := by
    rw [hZ]
    exact Subgroup.mem_top s
  obtain ⟨y, hy, s₀, hs₀, rfl⟩ := Subgroup.mem_sup.1 hs'
  refine S₀.mul_mem ?_ hs₀
  obtain ⟨z, hz, rfl⟩ := hy
  refine mem_of_rigid hS₀ hd.card_eq le_rfl ha'' hθ'' hfix (fun g => hall g (p z))
    (fun g hg => by rw [hρ1 g hg]; rfl) hJ ?_
  rintro _ ⟨t, ht, rfl⟩
  exact hn.rho_eq_of_mem_T hs rfl t (hJT (Subgroup.mem_subgroupOf.1 ht)) z
    (Subgroup.mem_subgroupOf.1 hz)

end NatHyp

end S512N

end CFSG.Quasithin.MS93
