module

public import CFSG.Quasithin.Background.RonanH143F4c
public import CFSG.Quasithin.Background.RonanH143F4d
public import CFSG.Quasithin.Background.RonanH143F4a

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def conjAut {X : Type*} [Group X] (G K : Subgroup X) (h : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    ↥G →* MulAut ↥K where
  toFun g :=
    { toFun := fun k => ⟨(g : X) * k * (g : X)⁻¹, h g g.2 k k.2⟩
      invFun := fun k => ⟨(g : X)⁻¹ * k * (g : X), by
        simpa using h (g : X)⁻¹ (G.inv_mem g.2) k k.2⟩
      left_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := fun k l => by
        apply Subtype.ext
        simp [mul_assoc] }
  map_one' := by
    ext k
    simp
  map_mul' g g' := by
    ext k
    simp [mul_assoc]

theorem conjAut_apply {X : Type*} [Group X] (G K : Subgroup X)
    (h : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (g : ↥G) (k : ↥K) :
    ((conjAut G K h g k : ↥K) : X) = (g : X) * k * (g : X)⁻¹ := rfl

theorem MQ_conj_NQ {g : P24}
    (hg : g ∈ MY mog22 Qstd) {k : P24} (hk : k ∈ NQ) : g * k * g⁻¹ ∈ NQ := by
  have hk' : (⟨k, NQ_le_MY_Q le_rfl hk⟩ : ↥(MY mog22 Qstd)) ∈ (piQ mog22).ker := by
    rw [ker_piQ_L]
    exact hk
  have h := (piQ mog22).normal_ker.conj_mem _ hk' ⟨g, hg⟩
  rw [ker_piQ_L] at h
  exact h

theorem Asgn_conj_NQ :
    ∀ g ∈ Asgn, ∀ k ∈ NQ, g * k * g⁻¹ ∈ NQ :=
  fun _ hg _ hk => MQ_conj_NQ (Asgn_le_MQ hg) hk

@[expose] noncomputable def psiA : ↥Asgn →* Equiv.Perm (Fin 5) :=
  (piQ mog22).comp (Subgroup.inclusion Asgn_le_MQ)

theorem psiA_apply (g : ↥Asgn) : psiA g = piQ mog22 ⟨g, Asgn_le_MQ g.2⟩ := rfl

theorem psiA_mem_alt (g : ↥Asgn) : psiA g ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  obtain ⟨h, hs⟩ := mem_Asgn_iff.1 g.2
  exact hs

theorem psiA_g1 : psiA ⟨g1Perm, g1_mem_Asgn⟩ = sig1 :=
  piQ_eq_of_smul _ _ g1_smul_Zq

theorem psiA_a2 : psiA ⟨a2Perm, a2_mem_Asgn⟩ = siga2 :=
  piQ_eq_of_smul _ _ a2_smul_Zq

theorem psiA_range :
    psiA.range = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact psiA_mem_alt g
  · intro σ hσ
    have htop := piQ_range_top (Γ := mog22) g1Perm_mem_mog22 g2Perm_mem_mog22
    have hmem : σ ∈ (piQ mog22).range := by
      rw [htop]
      exact Subgroup.mem_top σ
    obtain ⟨h, rfl⟩ := hmem
    have hAsgn : (h : P24) ∈ Asgn := by
      rw [mem_Asgn_iff]
      exact ⟨h.2, by simpa using Equiv.Perm.mem_alternatingGroup.1 hσ⟩
    exact ⟨⟨h, hAsgn⟩, rfl⟩

theorem psiA_ker :
    psiA.ker = NQ.subgroupOf Asgn := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, psiA_apply]
  have h : piQ mog22 ⟨g, Asgn_le_MQ g.2⟩ = 1 ↔ (⟨g, Asgn_le_MQ g.2⟩ : ↥(MY mog22 Qstd)) ∈
      (piQ mog22).ker := Iff.rfl
  rw [h, ker_piQ_L, Subgroup.mem_subgroupOf]

noncomputable def psiA' :
    ↥Asgn →* ↥(alternatingGroup (Fin 5)) :=
  psiA.codRestrict (alternatingGroup (Fin 5)) psiA_mem_alt

theorem psiA'_surjective :
    Function.Surjective psiA' := by
  rintro ⟨y, hy⟩
  have : y ∈ psiA.range := by rw [psiA_range]; exact hy
  obtain ⟨g, hg⟩ := this
  exact ⟨g, Subtype.ext hg⟩

theorem ker_psiA' :
    psiA'.ker = NQ.subgroupOf Asgn := by
  rw [← psiA_ker]
  ext g
  simp only [MonoidHom.mem_ker, psiA']
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa using this
  · intro h
    apply Subtype.ext
    simpa using h

theorem NQ_le_closure : NQ ≤ Subgroup.closure ((NQ : Set P24) ∪ {g1Perm, a2Perm}) :=
  fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem g1_mem_closure : g1Perm ∈ Subgroup.closure ((NQ : Set P24) ∪ {g1Perm, a2Perm}) :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem a2_mem_closure : a2Perm ∈ Subgroup.closure ((NQ : Set P24) ∪ {g1Perm, a2Perm}) :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem Asgn_le_closure :
    Asgn ≤ Subgroup.closure ((NQ : Set P24) ∪ {g1Perm, a2Perm}) := by
  set H : Subgroup P24 := Subgroup.closure ((NQ : Set P24) ∪ {g1Perm, a2Perm}) with hH
  set H' : Subgroup ↥Asgn := H.subgroupOf Asgn with hH'
  have hsig : Subgroup.closure ({sig1, siga2} : Set (Equiv.Perm (Fin 5))) ≤ H'.map psiA := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨⟨g1Perm, g1_mem_Asgn⟩, g1_mem_closure, psiA_g1⟩
    · exact ⟨⟨a2Perm, a2_mem_Asgn⟩, a2_mem_closure, psiA_a2⟩
  intro g hg
  have h1 : psiA ⟨g, hg⟩ ∈ H'.map psiA :=
    hsig (alt5_le_closure (psiA_mem_alt ⟨g, hg⟩))
  obtain ⟨h, hh, hgh⟩ := h1
  have h2 : (⟨g, hg⟩ : ↥Asgn) * h⁻¹ ∈ psiA.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
  rw [psiA_ker, Subgroup.mem_subgroupOf] at h2
  have h3 : (g : P24) * (h : P24)⁻¹ ∈ H := NQ_le_closure h2
  have h4 : (h : P24) ∈ H := hh
  have := H.mul_mem h3 h4
  simpa using this

noncomputable def phiNQ : ↥NQ ≃* Multiplicative (Fin 2 → F4) := Classical.choose exists_phiNQ

theorem phiNQ_spec (t : Fin 16) :
    phiNQ ⟨nqPerm t, ⟨t, rfl⟩⟩ = Multiplicative.ofAdd (vecOf t) :=
  Classical.choose_spec exists_phiNQ t

noncomputable def piA :
    ↥Asgn →* MulAut (Multiplicative (Fin 2 → F4)) :=
  (MulAut.congr phiNQ).toMonoidHom.comp (conjAut Asgn NQ Asgn_conj_NQ)

theorem piA_apply (g : ↥Asgn)
    (k : ↥NQ) :
    piA g (phiNQ k) = phiNQ (conjAut Asgn NQ Asgn_conj_NQ g k) := by
  simp [piA]

theorem piA_NQ {k : P24}
    (hk : k ∈ NQ) : piA ⟨k, NQ_le_Asgn hk⟩ = 1 := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨x, rfl⟩ := phiNQ.surjective a
  rw [piA_apply, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [conjAut_apply]
  show k * (x : P24) * k⁻¹ = x
  rw [NQ_comm k x hk x.2, mul_assoc, mul_inv_cancel, mul_one]

theorem piA_g1 {g : GL (Fin 2) F4}
    (hg : ∀ t : Fin 16, natHom 2 F4 g (Multiplicative.ofAdd (vecOf t)) =
      Multiplicative.ofAdd (vecOf (tab F1 t))) :
    piA ⟨g1Perm, g1_mem_Asgn⟩ = natHom 2 F4 g := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨x, rfl⟩ := phiNQ.surjective a
  obtain ⟨t, ht⟩ := mem_NQ_iff.1 x.2
  have hx : x = ⟨nqPerm t, ⟨t, rfl⟩⟩ := Subtype.ext ht
  subst hx
  rw [piA_apply, phiNQ_spec, hg]
  have : conjAut Asgn NQ Asgn_conj_NQ ⟨g1Perm, g1_mem_Asgn⟩ ⟨nqPerm t, ⟨t, rfl⟩⟩ =
      ⟨nqPerm (tab F1 t), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    rw [conjAut_apply]
    exact conj_g1_nq t
  rw [this, phiNQ_spec]

theorem piA_a2 {g : GL (Fin 2) F4}
    (hg : ∀ t : Fin 16, natHom 2 F4 g (Multiplicative.ofAdd (vecOf t)) =
      Multiplicative.ofAdd (vecOf (tab FA2 t))) :
    piA ⟨a2Perm, a2_mem_Asgn⟩ = natHom 2 F4 g := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨x, rfl⟩ := phiNQ.surjective a
  obtain ⟨t, ht⟩ := mem_NQ_iff.1 x.2
  have hx : x = ⟨nqPerm t, ⟨t, rfl⟩⟩ := Subtype.ext ht
  subst hx
  rw [piA_apply, phiNQ_spec, hg]
  have : conjAut Asgn NQ Asgn_conj_NQ ⟨a2Perm, a2_mem_Asgn⟩ ⟨nqPerm t, ⟨t, rfl⟩⟩ =
      ⟨nqPerm (tab FA2 t), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    rw [conjAut_apply]
    exact conj_a2_nq t
  rw [this, phiNQ_spec]

theorem piA_mem_natSub
    (g : ↥Asgn) : piA g ∈ natSub 2 F4 (CFSG.Open.StatedSL 2 F4) := by
  obtain ⟨g₁, g₂, hg₁, hg₂, h₁, h₂⟩ := exists_gl_mat
  set T : Subgroup P24 := ((natSub 2 F4 (CFSG.Open.StatedSL 2 F4)).comap piA).map Asgn.subtype
    with hT
  have hle : Asgn ≤ T := by
    refine Asgn_le_closure.trans ((Subgroup.closure_le _).2 ?_)
    rintro x (hx | hx)
    · refine ⟨⟨x, NQ_le_Asgn hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, piA_NQ hx]
      exact Subgroup.one_mem _
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · refine ⟨⟨g1Perm, g1_mem_Asgn⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, piA_g1 h₁]
        exact Subgroup.mem_map_of_mem _ hg₁
      · refine ⟨⟨a2Perm, a2_mem_Asgn⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, piA_a2 h₂]
        exact Subgroup.mem_map_of_mem _ hg₂
  obtain ⟨s, hs, hsg⟩ := hle g.2
  have : s = g := Subtype.ext hsg
  subst this
  exact hs

theorem NQ_le_ker_piA :
    NQ.subgroupOf Asgn ≤ (piA).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  have := piA_NQ (Subgroup.mem_subgroupOf.1 hg)
  exact this

theorem ker_piA :
    (piA).ker = NQ.subgroupOf Asgn := by
  apply le_antisymm _ NQ_le_ker_piA
  haveI : (piA).ker.Normal := MonoidHom.normal_ker piA
  haveI : ((piA).ker.map psiA').Normal := Subgroup.Normal.map this psiA' psiA'_surjective
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp)
    (N := (piA).ker.map psiA') with hb | ht
  · intro c hc
    have h1 : psiA' c ∈ (piA).ker.map psiA' := ⟨c, hc, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    rw [← ker_psiA', MonoidHom.mem_ker]
    exact h1
  · exfalso
    have hall : ∀ g : ↥Asgn, g ∈ (piA).ker := by
      intro g
      have h1 : psiA' g ∈ (piA).ker.map psiA' := by rw [ht]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hcg⟩ := h1
      have h2 : g * c⁻¹ ∈ psiA'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, mul_inv_cancel]
      rw [ker_psiA'] at h2
      have h3 : g * c⁻¹ ∈ (piA).ker := NQ_le_ker_piA h2
      have := (piA).ker.mul_mem h3 hc
      simpa using this
    have h1 := hall ⟨g1Perm, g1_mem_Asgn⟩
    rw [MonoidHom.mem_ker] at h1
    have h2 := piA_apply ⟨g1Perm, g1_mem_Asgn⟩ ⟨nqPerm 1, ⟨1, rfl⟩⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 := phiNQ.injective h2
    have h4 := congrArg Subtype.val h3
    rw [conjAut_apply] at h4
    have h5 : g1Perm * nqPerm 1 * g1Perm⁻¹ = nqPerm (tab F1 1) := conj_g1_nq 1
    have h6 : nqPerm 1 = nqPerm (tab F1 1) := by
      rw [← h5]
      exact h4
    have h7 := nqPerm_injective h6
    revert h7
    decide +kernel

theorem range_piA :
    (piA).range = natSub 2 F4 (CFSG.Open.StatedSL 2 F4) := by
  have hle : (piA).range ≤ natSub 2 F4 (CFSG.Open.StatedSL 2 F4) := by
    rintro _ ⟨g, rfl⟩
    exact piA_mem_natSub g
  have hcard : Nat.card (piA).ker * Nat.card (piA).range = Nat.card ↥Asgn :=
    Subgroup.card_ker_mul_card_range piA
  rw [ker_piA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe NQ_le_Asgn).toEquiv, card_NQ,
    card_Asgn] at hcard
  have h60 : Nat.card (piA).range = 60 := by omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h60]; exact card_natSub_SL_le)

theorem conjIsoModel_NQ :
    ConjIsoModel (perfectCore (MY mog22 Qstd)) NQ (Multiplicative (Fin 2 → F4))
      ((natSub 2 F4 (CFSG.Open.StatedSL 2 F4) :
          Subgroup (MulAut (Multiplicative (Fin 2 → F4)))) :
        Set (MulAut (Multiplicative (Fin 2 → F4)))) := by
  rw [perfectCore_MQ]
  refine ⟨phiNQ, piA, NQ_le_Asgn, fun g => piA_mem_natSub g, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [← range_piA] at hγ
    exact hγ
  · intro g
    rw [← MonoidHom.mem_ker, ker_piA]
    exact Subgroup.mem_subgroupOf
  · intro g k k' hk'
    have : k' = conjAut Asgn NQ Asgn_conj_NQ g k := Subtype.ext hk'
    rw [this, piA_apply]

end CFSG.Quasithin.RonanH143
