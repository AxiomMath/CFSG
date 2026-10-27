module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33t

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.LieType.BorelTits S126 S126P S126L1a S126L24
  F126 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem exists_lift_of (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h : HypF91 T V L F.V1 F.V5 H) {q : S126.HStar H} (hq : q ∈ S126.star H (Li L F.V1))
    (hq3 : q ^ 3 = 1) :
    ∃ y : ↥H, (y : G) ∈ Li L F.V1 ∧ (QuotientGroup.mk y : S126.HStar H) = q ∧
      ∃ σ : Perm (Fin 8), ActsAs F (y : G) σ ∧ σ ^ 3 = 1 ∧
        ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨z₀, hz₀L1, hz₀⟩ := hq
  have hz₀L1' : (z₀ : G) ∈ Li L F.V1 := hz₀L1
  have hz₀' : (QuotientGroup.mk z₀ : S126.HStar H) = q := hz₀
  have hz₀V : (z₀ : G) ∈ Subgroup.normalizer (V : Set G) := hLV (L1_le_L hz₀L1')
  set σ₀ : Perm (Fin 8) :=
    ((S126L19a.psi F hH ⟨z₀, L1_le_L hz₀L1'⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))
  have hσ₀ : ActsAs F (z₀ : G) σ₀ := S126L19a.actsAs_psi F hH ⟨z₀, L1_le_L hz₀L1'⟩
  have hz₀3 : ((z₀ ^ 3 : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← mkH_eq_one_iff, QuotientGroup.mk_pow, hz₀', hq3]
  have hA : ActEq (σ₀ ^ 3) 1 := by
    refine actEq_of_conj F (Subgroup.pow_mem _ hz₀V 3) (Subgroup.one_mem _) (hσ₀.pow hz₀V 3)
      (ActsAs.one F) fun v hv => ?_
    refine conj_inv_mul_conj_mem h (Subgroup.one_mem H) ?_ (le_conjClosure F.V5 H hv)
    rw [inv_one, one_mul, ← Subgroup.coe_pow]
    exact hz₀3
  have hσ₀3 : σ₀ ^ 3 ∈ S126E.E16 := S126L24.mem_E16_of_cent fun y hy => by
    have := hA y hy
    rwa [dAct_one] at this
  have hσ3 : (σ₀ ^ 16) ^ 3 = 1 := by
    rw [← pow_mul, show 16 * 3 = 3 * 2 * 8 from rfl, pow_mul, pow_mul, sq_of_mem_E16 hσ₀3,
      one_pow]
  have hyσ : ActsAs F ((z₀ ^ 16 : ↥H) : G) (σ₀ ^ 16) := by
    rw [Subgroup.coe_pow]
    exact hσ₀.pow hz₀V 16
  have hyL1 : ((z₀ ^ 16 : ↥H) : G) ∈ Li L F.V1 := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hz₀L1' 16
  refine ⟨z₀ ^ 16, hyL1, ?_, σ₀ ^ 16, hyσ, hσ3, ?_⟩
  · rw [QuotientGroup.mk_pow, hz₀', show 16 = 3 * 5 + 1 from rfl, pow_add, pow_mul, hq3, one_pow,
      one_mul, pow_one]
  · rcases S126L19a.blocks_of_mem_V1 F (L1_le_normalizer hyL1) hyσ with hb | hb
    · exact hb
    · exfalso
      set σ := σ₀ ^ 16
      have e3 : (σ ^ 3) 0 = σ (σ (σ 0)) := by rw [pow_three, Perm.mul_apply, Perm.mul_apply]
      rw [hσ3, Perm.one_apply] at e3
      have h0 := (hb 0).1 (by decide)
      have h1 : (σ (σ 0)).val < 4 := by
        by_contra hc
        exact absurd ((hb (σ 0)).2 (by omega)) (by omega)
      have h3 := (hb (σ (σ 0))).1 h1
      rw [← e3] at h3
      exact absurd h3 (by decide)

@[expose] def CNs (σ : Perm (Fin 8)) : Prop :=
  ∃ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x ∧
    (Finset.univ.filter fun i => x (σ⁻¹ i) - x i ≠ 0).card = 2

instance (σ : Perm (Fin 8)) : Decidable (CNs σ) := by
  unfold CNs; infer_instance

theorem check_nonsing : ∀ σ₁ : Perm (Fin 4), σ₁ ^ 3 = 1 → ∀ σ₂ : Perm (Fin 4), σ₂ ^ 3 = 1 →
    CHypB (blP (σ₁, σ₂)) → CNs (blP (σ₁, σ₂)) := by
  decide +kernel

omit [Finite G] in
theorem exists_nonsing (F : Frame126 T L V) {y : G} (hyV : y ∈ Subgroup.normalizer (V : Set G))
    {σ : Perm (Fin 8)} (hσ : ActsAs F y σ) (h3 : σ ^ 3 = 1)
    (hblock : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) (hnt : ¬ ActEq σ 1) :
    ∃ v ∈ F.V5, F.Nonsing (y * v * y⁻¹ * v⁻¹) := by
  obtain ⟨⟨σ₁, σ₂⟩, rfl⟩ := exists_blP hblock
  have h3' : blP (σ₁ ^ 3, σ₂ ^ 3) = blP 1 := by
    rw [← Prod.pow_mk, map_pow, h3, map_one]
  have h3'' := Prod.ext_iff.1 (blP_injective h3')
  have hB : CHypB (blP (σ₁, σ₂)) := by
    by_contra hno
    apply hnt
    rw [actEq_iff]
    intro x hx hev
    by_contra hbc
    exact hno ⟨x, hx, hev, by simpa using hbc⟩
  obtain ⟨x, hx, hev, hwt⟩ := check_nonsing σ₁ h3''.1 σ₂ h3''.2 hB
  set m := ofVec x hx
  obtain ⟨v, hv⟩ := F.β_surj (QuotientGroup.mk m)
  have hv5 : (v : G) ∈ F.V5 := (mem_V5_iff_beta F v).2 (by rw [hv]; exact (mem_W5_iff m).2 hev)
  set w : ↥V := ⟨y * v * y⁻¹, conj_mem hyV v⟩
  refine ⟨v, hv5, (w * v⁻¹ : ↥V).2, ?_⟩
  refine ⟨coreAct 8 (blP (σ₁, σ₂)) m * m⁻¹, ?_, ?_⟩
  · have e : F.β (w * v⁻¹) = QuotientGroup.mk (coreAct 8 (blP (σ₁, σ₂)) m * m⁻¹) := by
      rw [map_mul, map_inv, hσ v w rfl, hv, dAct_mk, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
    exact e.symm
  · show (Finset.univ.filter fun i => vx (coreAct 8 (blP (σ₁, σ₂)) m * m⁻¹) i ≠ 0).card = 2
    rw [vx_mul, vx_inv, vx_coreAct]
    convert hwt using 3
    rename_i i
    simp [m, vx_ofVec, sub_eq_add_neg]

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_centralizer_of_comm {V₁ K₂ : Subgroup G} (hV₁c : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a)
    (hcent : ∀ k ∈ K₂, ∀ z ∈ V₁, k * z = z * k) (hperf : ⁅K₂, K₂⁆ = K₂) {u : G}
    (hc : ∀ k ∈ K₂, k * u * k⁻¹ * u⁻¹ ∈ V₁) : K₂ ≤ Subgroup.centralizer ({u} : Set G) := by
  let f : ↥K₂ →* ↥V₁ :=
    { toFun := fun k => ⟨k * u * (k : G)⁻¹ * u⁻¹, hc k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hα := hc a a.2
        have hβ := hc b b.2
        set β := (b : G) * u * (b : G)⁻¹ * u⁻¹
        have hb : (b : G) * u * (b : G)⁻¹ = β * u := by simp [β]
        show (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹ =
          ((a : G) * u * (a : G)⁻¹ * u⁻¹) * ((b : G) * u * (b : G)⁻¹ * u⁻¹)
        calc (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹
            = (a : G) * ((b : G) * u * (b : G)⁻¹) * (a : G)⁻¹ * u⁻¹ := by group
          _ = ((a : G) * β) * u * (a : G)⁻¹ * u⁻¹ := by rw [hb]; group
          _ = (β * a) * u * (a : G)⁻¹ * u⁻¹ := by rw [hcent a a.2 β hβ]
          _ = β * ((a : G) * u * (a : G)⁻¹ * u⁻¹) := by group
          _ = ((a : G) * u * (a : G)⁻¹ * u⁻¹) * β := hV₁c _ hβ _ hα) }
  rw [← hperf, Subgroup.commutator_le]
  intro x hx y hy
  have h1 : f ⁅(⟨x, hx⟩ : ↥K₂), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hV₁c _ (f ⟨x, hx⟩).2 _ (f ⟨y, hy⟩).2)
  have h2 : ⁅x, y⁆ * u * ⁅x, y⁆⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  calc u * ⁅x, y⁆ = (⁅x, y⁆ * u * ⁅x, y⁆⁻¹ * u⁻¹)⁻¹ * (⁅x, y⁆ * u) := by group
    _ = ⁅x, y⁆ * u := by rw [h2, inv_one, one_mul]

theorem false_of_comm_le (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (h2 : Case2 T L H K)
    (h1262 : Theorem12_6_2) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hc : ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ F.V1) : False := by
  set h := h918.toHypF98.toHypF91 with hh
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTH : T ≤ H := le_sup_right.trans h.L₁T_le_H
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  obtain ⟨x, hxL, hxK, hx3, hxn⟩ := exists_three_elt F hH h918 h2 ht htK
  obtain ⟨y, hyL1, hy, σ, hσ, hσ3, hblock⟩ := exists_lift_of F hH h hxL hx3
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) := hLV (L1_le_L hyL1)
  have hnt : ¬ ActEq σ 1 := by
    intro hA
    apply hxn
    rw [← hy, psiH_mk, fix5_thetaH_iff h y hVN]
    intro v hv
    have := conj_of_actEq F hyV (Subgroup.one_mem _) hσ (ActsAs.one F) hA v hv
    simpa using this
  obtain ⟨v, hv5, hns⟩ := exists_nonsing F hyV hσ hσ3 hblock hnt
  have hvU : v ∈ conjClosure F.V5 H := le_conjClosure F.V5 H hv5
  obtain ⟨k, hkK, hk⟩ : ∃ k : ↥H, (k : G) ∈ K ∧
      (QuotientGroup.mk k : S126.HStar H) = QuotientGroup.mk y := by
    obtain ⟨k, hk, hkx⟩ := hxK
    exact ⟨k, hk, hkx.trans hy.symm⟩
  have hq : (k : G)⁻¹ * y ∈ pCoreOf 2 H := mem_pCoreOf_of_mk_eq hk
  set q := (k : G)⁻¹ * y with hqdef
  have hz' : q * v * q⁻¹ * v⁻¹ ∈ F.V1 := by
    rw [h.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 v hvU
  set z' := q * v * q⁻¹ * v⁻¹ with hz'def
  have hV₁c : ∀ a ∈ F.V1, ∀ b ∈ F.V1, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm h.elemAbelian (h.V₁_le_V ha) (h.V₁_le_V hb)
  have hcentH : ∀ g ∈ H, ∀ z ∈ F.V1, g * z = z * g := fun g hg z hz =>
    (Subgroup.mem_centralizer_iff.1 (h.H_le_centralizer hg) z hz).symm
  have hu : (y : G) * v * (y : G)⁻¹ * v⁻¹ = z' * ((k : G) * v * (k : G)⁻¹ * v⁻¹) := by
    have e1 : (y : G) = k * q := by rw [hqdef]; group
    calc (y : G) * v * (y : G)⁻¹ * v⁻¹ = (k : G) * (q * v * q⁻¹ * v⁻¹) * v * (k : G)⁻¹ * v⁻¹ := by
          rw [e1]; group
      _ = ((k : G) * z') * v * (k : G)⁻¹ * v⁻¹ := by rw [hz'def]
      _ = (z' * k) * v * (k : G)⁻¹ * v⁻¹ := by rw [hcentH k k.2 z' hz']
      _ = z' * ((k : G) * v * (k : G)⁻¹ * v⁻¹) := by group
  have hcK : ∀ k₂ ∈ conjSub t⁻¹ K, k₂ * ((y : G) * v * (y : G)⁻¹ * v⁻¹) * k₂⁻¹ *
      ((y : G) * v * (y : G)⁻¹ * v⁻¹)⁻¹ ∈ F.V1 := by
    intro k₂ hk₂
    have hk₂H : k₂ ∈ H := by
      obtain ⟨k', hk', rfl⟩ := hk₂
      exact H.mul_mem (H.mul_mem (H.inv_mem (hTH ht)) (le_of_mem_cComp h918.K_cComp hk'))
        (by simpa using hTH ht)
    set c := (k : G) * v * (k : G)⁻¹ * v⁻¹ with hcdef
    have hcU : c ∈ ⁅conjClosure F.V5 H, K⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hkK hvU
    have h1 : c * k₂ * c⁻¹ * k₂⁻¹ ∈ F.V1 := hc (Subgroup.commutator_mem_commutator hcU hk₂)
    have h2 : k₂ * c * k₂⁻¹ * c⁻¹ ∈ F.V1 := by
      have := F.V1.inv_mem h1
      rwa [show (c * k₂ * c⁻¹ * k₂⁻¹)⁻¹ = k₂ * c * k₂⁻¹ * c⁻¹ by group] at this
    rw [hu]
    have e : k₂ * (z' * c) * k₂⁻¹ * (z' * c)⁻¹ = (k₂ * z') * c * k₂⁻¹ * c⁻¹ * z'⁻¹ := by group
    rw [e, hcentH k₂ hk₂H z' hz',
      show z' * k₂ * c * k₂⁻¹ * c⁻¹ * z'⁻¹ = z' * (k₂ * c * k₂⁻¹ * c⁻¹) * z'⁻¹ by group,
      hV₁c z' hz' _ h2, mul_inv_cancel_right]
    exact h2
  have hK₂c : conjSub t⁻¹ K ∈ cComp H := conjSub_mem_cComp h918.K_cComp (H.inv_mem (hTH ht))
  have hle := le_centralizer_of_comm hV₁c
    (fun k₂ hk₂ z hz => hcentH k₂ (le_of_mem_cComp hK₂c hk₂) z hz)
    (perfect_of_mem_cComp hK₂c) hcK
  have hK₂M := hle.trans (h1262 G T L V F hH _ hns)
  apply hIs.2.1
  intro k' hk'
  have h1 : t⁻¹ * k' * t⁻¹⁻¹ ∈ conjSub t⁻¹ K := mul_mem_conjSub hk'
  have h2 := hK₂M h1
  have htM := hH.hyp.normalizes ht
  have e : k' = t * (t⁻¹ * k' * t⁻¹⁻¹) * t⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htM h2) (Subgroup.inv_mem _ htM)

end CFSG.Quasithin.H13.L1233
