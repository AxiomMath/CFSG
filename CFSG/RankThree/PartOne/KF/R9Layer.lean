module

public import CFSG.RankThree.PartOne.KF.R9Final
public import CFSG.RankThree.PartOne.KF.R9Levi
public import CFSG.RankThree.PartOne.KF.R9Plane
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G]

theorem exists_pair_eq [Finite G] {p : ℕ} {L F : Subgroup G} {f : ℕ} {K : Type} [Field K]
    (C : R9Ctx p L F f K) {A₀ S : Subgroup G} (hA₀F : A₀ ≤ F) (hSL : S ≤ L) (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hAS : A₀ ≤ Subgroup.normalizer (S : Set G)) :
    ∃ i j : Fin 4, i ≠ j ∧ ∀ m : ↥(unitarySU 2 f K 4), C.phi m ∈ A₀ →
      ∃ d : Fin 4 → Kˣ, (∀ k, d k ^ p = 1) ∧ ∏ k, d k = 1 ∧ d i = d j ∧
        diagU d = (m : GL (Fin 4) K) := by
  classical
  have hU := C.hU
  let St : Subgroup (GL (Fin 4) K) := (S.comap C.phi).map (unitarySU 2 f K 4).subtype
  let P : Subgroup (GL (Fin 4) K) := (A₀.comap C.phi).map (unitarySU 2 f K 4).subtype
  have hdiag : ∀ m : ↥(unitarySU 2 f K 4), C.phi m ∈ A₀ → ∃ d : Fin 4 → Kˣ,
      (∀ k, d k ^ p = 1) ∧ ∏ k, d k = 1 ∧ diagU d = (m : GL (Fin 4) K) := fun m hm =>
    mem_torusSU_iff.1 ((C.phi_mem_F_iff m).1 (hA₀F hm))
  have hbot : (∀ i j : Fin 4, i ≠ j → ∃ g ∈ P, ent g i i ≠ ent g j j) → St = ⊥ := by
    intro hsep
    refine eq_bot_of_two_group_separated hU St ?_ ?_ P ?_ ?_ hsep
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · rintro ⟨x, m, hm, rfl⟩
      obtain ⟨k, hk⟩ := hS2 ⟨C.phi m, hm⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : C.phi (m ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      have h2 : m ^ 2 ^ k = 1 := C.phi_injective (h1.trans (map_one C.phi).symm)
      simpa using congrArg (fun g : ↥(unitarySU 2 f K 4) => (g : GL (Fin 4) K)) h2
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨d, -, -, hd⟩ := hdiag m hm
      exact ⟨d, hd⟩
    · rintro _ ⟨m, hm, rfl⟩ _ ⟨y, hy, rfl⟩
      refine ⟨m * y * m⁻¹, ?_, rfl⟩
      show C.phi (m * y * m⁻¹) ∈ S
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hAS hm) (C.phi y)).1 hy
  have hne : St ≠ ⊥ := by
    intro hbot'
    obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS1
    obtain ⟨m, hm⟩ := C.exists_phi_eq (hSL s.2)
    have hmS : (m : GL (Fin 4) K) ∈ St :=
      ⟨m, show C.phi m ∈ S by rw [hm]; exact s.2, rfl⟩
    rw [hbot', Subgroup.mem_bot] at hmS
    have hm1 : m = 1 := Subtype.ext hmS
    apply hs1
    apply Subtype.ext
    rw [← hm, hm1, map_one]
    rfl
  by_contra hcon
  push Not at hcon
  apply hne
  apply hbot
  intro i j hij
  obtain ⟨m, hm, hmd⟩ := hcon i j hij
  refine ⟨(m : GL (Fin 4) K), ⟨m, hm, rfl⟩, ?_⟩
  obtain ⟨d, hd1, hd2, hd⟩ := hdiag m hm
  have hij' : d i ≠ d j := fun hdij => hmd d hd1 hd2 hdij hd
  intro hent
  apply hij'
  rw [← hd] at hent
  simp only [ent, diagU_apply_same] at hent
  exact Units.ext hent

theorem exists_perm_zero_one (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ i = 0 ∧ σ j = 1 := by
  refine ⟨Equiv.swap (Equiv.swap i 0 j) 1 * Equiv.swap i 0, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ (by decide)
    intro h0
    have h1 : Equiv.swap i 0 j = Equiv.swap i 0 i := by
      rw [Equiv.swap_apply_left]
      exact h0.symm
    exact hij ((Equiv.swap i 0).injective h1).symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

namespace KFU.R9Ctx

variable {p : ℕ} {L F : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite G]

@[expose] noncomputable def epsilon (C : R9Ctx p L F f K) (σ : Equiv.Perm (Fin 4)) :
    ↥L ≃* ↥(unitarySU 2 f K 4) :=
  C.ψ.symm.trans (MulAut.conj (C.permHom σ))

theorem coe_epsilon (C : R9Ctx p L F f K) (σ : Equiv.Perm (Fin 4))
    (m : ↥(unitarySU 2 f K 4)) :
    (((C.epsilon σ (C.ψ m) : ↥(unitarySU 2 f K 4))) : GL (Fin 4) K) =
      permGL σ * (m : GL (Fin 4) K) * (permGL σ)⁻¹ := by
  simp only [epsilon, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply]
  rfl

theorem epsilon_mem_T9 (C : R9Ctx p L F f K) {A₀ : Subgroup G} {i j : Fin 4}
    {σ : Equiv.Perm (Fin 4)} (hσi : σ i = 0) (hσj : σ j = 1)
    (hij : ∀ m : ↥(unitarySU 2 f K 4), C.phi m ∈ A₀ → ∃ d : Fin 4 → Kˣ, (∀ k, d k ^ p = 1) ∧
      ∏ k, d k = 1 ∧ d i = d j ∧ diagU d = (m : GL (Fin 4) K))
    {y : ↥L} (hy : (y : G) ∈ A₀) : C.epsilon σ y ∈ T9 p K f := by
  have hy' : y = C.ψ (C.ψ.symm y) := (MulEquiv.apply_symm_apply C.ψ y).symm
  have hφ : C.phi (C.ψ.symm y) ∈ A₀ := by
    rw [C.coe_phi, MulEquiv.apply_symm_apply]
    exact hy
  obtain ⟨d, hd1, hd2, hdij, hd⟩ := hij _ hφ
  rw [hy']
  refine mem_T9_iff.2 ⟨d ∘ σ.symm, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hd1 (σ.symm k)
  · rw [show (∏ k, (d ∘ σ.symm) k) = ∏ k, d (σ.symm k) from rfl, Equiv.prod_comp σ.symm d]
    exact hd2
  · show d (σ.symm 0) = d (σ.symm 1)
    rw [(Equiv.symm_apply_eq σ).2 hσi.symm, (Equiv.symm_apply_eq σ).2 hσj.symm]
    exact hdij
  · rw [C.coe_epsilon, ← hd, permGL_conj_diagU]

end KFU.R9Ctx

theorem kf1212LayerRow9 (hZ : PSUFourEvenCenterTrivial) : KF1212LayerRow 9 := by
  intro G _ _ p A c L E ctx hmodel _ hE
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hf1, hLmod, ⟨C⟩⟩ := exists_r9ctx_model hZ hcore hmodel
  have hU := C.hU
  have hf2 := C.hf2
  have hpq := C.hpq
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := hU.finite
  have : CharP K 2 := hU.charP
  obtain ⟨S, hSL, hS1, hS2, hAS, -⟩ := hcore.A₀_invariant
  obtain ⟨i, j, hij, hdij⟩ := exists_pair_eq C hcore.A₀_le_F hSL hS1 hS2 hAS
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_zero_one i j hij
  let ε : ↥L →* ↥(unitarySU 2 f K 4) := (C.epsilon σ).toMonoidHom
  have hεbij : Function.Bijective ε := (C.epsilon σ).bijective
  have hε : IsCentralPQuot p ε := SymCtx.isCentralPQuot_of_bijective _ hεbij p
  have hq : IsCentralPQuot p (MonoidHom.id ↥(unitarySU 2 f K 4)) :=
    SymCtx.isCentralPQuot_of_bijective _ Function.bijective_id p
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (T9 p K f).map (MonoidHom.id _) := by
    rw [Subgroup.map_id]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact C.epsilon_mem_T9 hσi hσj hdij (Subgroup.mem_subgroupOf.1 hy)
    · rw [Subgroup.card_map_of_injective hεbij.1,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
        hcore.A₀_card]
      exact card_T9_le hU hpq hp.pos
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζ4 : ζ ^ 4 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hb := diagU_dvec9_mem hU hpq hζp
  have hbT := b9_mem_T9 hU hpq hζp
  have hne := ne_inv_pow_three hζ4
  have hbMp : b9 hb ^ p = 1 := T9_pow_eq_one hbT
  have hKM := perfectResidual_centralizer_b9 hU hf2 hne hb
  have hbT' : b9 hb ∈ ((A ⊓ L).subgroupOf L).map ε := by
    rw [hAT, Subgroup.map_id]
    exact hbT
  obtain ⟨y, hy, hyb⟩ := hbT'
  have hxL : (y : G) ∈ L := y.2
  have hxA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.1 hy).1
  have hbb : ε ⟨(y : G), hxL⟩ = MonoidHom.id _ (b9 hb) := hyb
  have hb1 : (y : G) ≠ 1 := by
    intro h1
    have h2 : ε y = 1 := by
      have hy1 : y = 1 := Subtype.ext h1
      rw [hy1, map_one]
    exact b9_ne_one hU hpq hζp hζ1 (hyb.symm.trans h2)
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := (Sec12Three.A_eq_sup h ctx.generic).le
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε (MonoidHom.id _) hε hq hxA hxL
    hbMp hbb (T₀ := T9 p K f) (U := U9 K f) (fun t ht => T9_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_b9 hU hf2 hne hb)
    (by rw [hKM]; exact not_dvd_card_center_range_blk93 hU hf2 h5)
    (by rw [hKM]; exact card_T9_inf_range hU hpq hp.pos ⟨ζ, hζ⟩)
    (by rw [hKM]; exact U9_le_range hU) isPGroup_U9 T9_le_normalizer_U9
    (exists_noncomm_U9 hU hpq hζp hζ3)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  refine ⟨(y : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, f, hf1, hpq, hLmod,
    ⟨Nat.prime_two, hf1, by norm_num, ?_⟩, K, inferInstance, inferInstance, ?_, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · rw [hU.card, ← pow_mul, mul_comm]
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv
      (MonoidHom.ofInjective (blk93_injective hU)).symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans
      (QuotientGroup.quotientMulEquivOfEq (isQuasisimple_unitarySU_three hU hf2).2)))⟩

end CFSG.RankThree.PartOne
