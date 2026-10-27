module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Quasithin.Background.C1PackS15205E
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem pow_three_eq_one_of_rank_two {X : Type*} [Group X] (h : IsElemAbelianOfRank 3 2 X)
    (x : X) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  have key : ∀ f : Multiplicative (Fin 2 → ZMod 3), f ^ 3 = 1 := by decide
  exact key _

theorem card_mulAut_dvd_six_of_card_four {F : Type*} [Group F] (h : Nat.card F = 4) :
    Nat.card (MulAut F) ∣ 6 := by
  classical
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hS : Nat.card {x : F // x ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, h]
  let φ : MulAut F →* Equiv.Perm {x : F // x ≠ 1} :=
    { toFun := fun σ => σ.toEquiv.subtypeEquiv (fun a => by simp)
      map_one' := by ext; rfl
      map_mul' := fun σ τ => by ext; rfl }
  have hφ : Function.Injective φ := by
    intro σ τ hστ
    ext x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · have := congrArg (fun π : Equiv.Perm {x : F // x ≠ 1} => (π ⟨x, hx⟩ : F)) hστ
      simpa [φ] using this
  have h1 := Subgroup.card_dvd_of_injective φ hφ
  have hperm : Nat.card (Equiv.Perm {x : F // x ≠ 1}) = 6 := by
    have : Fintype {x : F // x ≠ 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hS]
    rfl
  rwa [hperm] at h1

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem two_power_mem_centralizer_VZ (r49 : Res15349 T Mc M V₁) {y : G} (hy : y ∈ Y153 Mc M)
    {k : ℕ} (hk : y ^ 2 ^ k = 1) : y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hp, hE⟩ := r49.case_one
  set yq : OTwoQuot (Y153 Mc M) := QuotientGroup.mk (⟨y, hy⟩ : ↥(Y153 Mc M)) with hyq
  have h3 : yq ^ 3 = 1 := pow_three_eq_one_of_rank_two hE yq
  have h2 : yq ^ 2 ^ k = 1 := by
    rw [hyq, ← QuotientGroup.mk_pow]
    have : (⟨y, hy⟩ : ↥(Y153 Mc M)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    rfl
  have hord : orderOf yq = 1 := by
    have d3 : orderOf yq ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have d2 : orderOf yq ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes hc d3 d2
  have h1 : yq = 1 := orderOf_eq_one_iff.mp hord
  rw [hyq, QuotientGroup.eq_one_iff] at h1
  have hmem : y ∈ pCoreOf 2 (Y153 Mc M) := ⟨⟨y, hy⟩, h1, rfl⟩
  rw [hp] at hmem
  exact hmem.2

theorem pCoreOf_YF_sup_pCoreOf_G0_le_centralizer (c : Ctx153 G T Mc M V₁ V₂ t)
    (r49 : Res15349 T Mc M V₁) (gl : GoldLine153 T V₁ E s) (r68 : Res15368 T Mc M E s) :
    pCoreOf 2 (YF153 Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) ≤
      Subgroup.centralizer (VZ T M : Set G) := by
  refine sup_le (fun x hx => ?_) r68.pCore_le_centralizer
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (YF153 Mc M E s) ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact two_power_mem_centralizer_VZ r49 (YF_le_Y c gl (pCoreOf_le 2 _ hx)) hk'

theorem commutator_VZ_YF (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) : ⁅VZ T M, YF153 Mc M E s⁆ = VZ T M := by
  have hs : s ∈ Subgroup.normalizer (VZ T M : Set G) :=
    c.hyp.le_normalizer (c.hyp.T_le gl.s_mem.1)
  have h1 := C5.conjSubgroup_commutator (VZ T M) (YE153 Mc M E) s
  rw [r66.V_comm, C5.conjSubgroup_eq_self hs] at h1
  exact h1.symm

theorem oTwoUpper_YF (Mc M E : Subgroup G) (s : G) :
    oTwoUpper (YF153 Mc M E s) = YF153 Mc M E s := by
  have hYE : oTwoUpper (YE153 Mc M E) = YE153 Mc M E := oTwoUpper_oTwoUpper _
  have h := oTwoUpper_map (MulAut.conj s⁻¹).toMonoidHom (YE153 Mc M E)
  rw [hYE] at h
  exact h

theorem YF_le_thompsonJ_sup_pCore (r68 : Res15368 T Mc M E s)
    (hO2 : oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤ Xdot153 T Mc M E s) :
    YF153 Mc M E s ≤ thompsonJ (G0_153 T Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) := by
  have hYFI : YF153 Mc M E s ≤ G0_153 T Mc M E s := le_sup_left.trans le_sup_left
  rw [← oTwoUpper_YF Mc M E s]
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  have hyI : y ∈ G0_153 T Mc M E s := hYFI hy.1
  have hodd : Odd (orderOf (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
      CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
    refine Odd.of_dvd_nat (n := orderOf y) hy.2 ?_
    have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
      (⟨y, hyI⟩ : ↥(G0_153 T Mc M E s))
    rwa [Subgroup.orderOf_mk] at this
  have hX := hO2 (mem_oTwoUpper_of_odd (Subgroup.mem_top _) hodd)
  obtain ⟨x, hxX, hxu⟩ := mem_barQ.mp hX
  have h1 : x⁻¹ * ⟨y, hyI⟩ ∈ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) := QuotientGroup.eq.mp hxu
  have h2 : (x : G)⁻¹ * y ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
    rw [r68.pCore_eq]
    exact ⟨x⁻¹ * ⟨y, hyI⟩, h1, by simp⟩
  have e : y = (x : G) * ((x : G)⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hxX h2

theorem not_pCoreOf_G1_le_centralizer (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    ¬ pCoreOf 2 (G1_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro hQ
  have hQ1 : pCoreOf 2 (G1_153 T Mc M E s) =
      G1_153 T Mc M E s ⊓ Subgroup.centralizer (FE153 E s : Set G) := by
    rw [G1_eq_conj r66 gl, ← C5.conjSubgroup_pCoreOf, r66.pCore_YETE, C5.conjSubgroup_inf,
      C5.conjSubgroup_centralizer]
  have hTEV : TE153 T E ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (c.hyp.T_le.trans c.hyp.le_normalizer)
  have hTEs : conjSubgroup (TE153 T E) s = TE153 T E :=
    conjSubgroup_eq_iff_mem_normalizer.2 (T_le_normalizer_TE r66 gl.s_mem.1)
  have hTEF : TE153 T E ≤ Subgroup.normalizer (FE153 E s : Set G) := by
    calc TE153 T E = conjSubgroup (TE153 T E) s := hTEs.symm
      _ ≤ conjSubgroup (Subgroup.normalizer (E : Set G)) s := C5.conjSubgroup_mono inf_le_right s
      _ = Subgroup.normalizer (FE153 E s : Set G) := C5.conjSubgroup_normalizer E s
  have hle : TE153 T E ⊓ Subgroup.centralizer (FE153 E s : Set G) ≤
      TE153 T E ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    intro x hx
    refine ⟨hx.1, hQ ?_⟩
    rw [hQ1]
    exact ⟨(le_sup_right : TE153 T E ≤ G1_153 T Mc M E s) hx.1, hx.2⟩
  have hdvd : Nat.card (autOn (TE153 T E) (VZ T M)) ∣ Nat.card (autOn (TE153 T E) (FE153 E s)) :=
    C1Pack5.card_autOn_dvd hTEF hTEV hle
  have h4 : Nat.card (autOn (TE153 T E) (VZ T M)) = 4 := r66.barTE_klein.1.1
  have hF4 : Nat.card (FE153 E s) = 4 := by rw [C5.card_conjSubgroup]; exact L.card_eq
  have h6 : Nat.card (MulAut ↥(FE153 E s)) ∣ 6 := card_mulAut_dvd_six_of_card_four hF4
  have hAF : Nat.card (autOn (TE153 T E) (FE153 E s)) ∣ 6 :=
    (Subgroup.card_subgroup_dvd_card _).trans h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2grp : IsPGroup 2 ↥(autOn (TE153 T E) (FE153 E s)) :=
    isPGroup_autOn (isPGroup_TE c) hTEF
  obtain ⟨n, hn⟩ := h2grp.exists_card_eq
  rw [hn] at hAF hdvd
  rw [h4] at hdvd
  have hn1 : n ≤ 1 := by
    by_contra hcon
    have h22 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h22.trans hAF
    omega
  interval_cases n <;> omega

end Setting

end CFSG.Quasithin
