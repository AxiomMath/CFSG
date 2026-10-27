module

public import CFSG.Quasithin.H13.U3P33Rep
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.H13.U3L15U
public import CFSG.Quasithin.H13.U3L14Producers
public import CFSG.Quasithin.H13.U3L14D6
public import CFSG.Quasithin.H13.L32NModule

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

@[expose] def xCodes : List (List ℕ × List ℕ) := [(u6c 3, u6ci 3), (u6ci 3, u6c 3)]

theorem xCodes_spec : ∀ e ∈ xCodes, vapp e.1 18 < 64 ∧ vapp e.1 53 < 64 ∧
    v1mask.testBit (vapp e.1 18 ^^^ 18) = false ∧ v2mask.testBit (vapp e.1 53) = false ∧
    vapp e.1 (vapp (u6c 0) (vapp e.1 (vapp (u6ci 0) (vapp e.2 (vapp (u6c 0) (vapp e.2
      (vapp (u6ci 0) 18))))))) = 29 := by
  decide +kernel

theorem sy_codes : v1mask.testBit (vapp (u6c 2) 18 ^^^ 18) = false ∧
    vapp (u6c 4) (vapp (u6c 4) 15) ≠ 15 ∧ dotB 18 (vapp b0c (vapp (u6c 4) 18)) = true ∧
    dotB 18 (vapp b0c (vapp (u6c 4) (vapp (u6c 4) 18))) = true := by
  decide +kernel

theorem exists_xCode {X : GL (Fin 6) (ZMod 2)} (hX : X = xGL ∨ X = xGL * xGL) :
    ∃ e ∈ xCodes, (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e.1 ∧
      ((X⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e.2 := by
  rcases hX with rfl | rfl
  · exact ⟨(u6c 3, u6ci 3), by simp [xCodes], coe_xGL, coe_xGL_inv⟩
  · exact ⟨(u6ci 3, u6c 3), by simp [xCodes], coe_xGL_sq,
      coe_inv_of_code coe_xGL_sq (u6c_mul_inv 3).1⟩

theorem pCoreOf_le_o2Z (L : Subgroup G) : pCoreOf 2 L ≤ A6.o2Z L := by
  intro x hx
  have hxL : x ∈ L := LieType.BorelTits.pCoreOf_le 2 L hx
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := coe_mem_pCoreOf_iff.1 hx
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈ Subgroup.center _
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 h1]
  exact Subgroup.one_mem _

theorem not_isHatA6_of_psu {L : Subgroup G}
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) : ¬ A6.IsHatA6 L := by
  rintro ⟨-, h3, ⟨e⟩⟩
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [card_of_lieModel_PSU_three_three hU3, h3, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  norm_num [Nat.factorial] at h2

section Transport

variable {V : Subgroup G} [IsElementaryAbelian 2 V] {Φ : Additive V ≃ₗ[ZMod 2] W6}

theorem conj_comm_mem_pullSub {n : G} (hn : n ∈ normalizer (V : Set G))
    {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {v : G} (hv : v ∈ V) (P : Submodule (ZMod 2) W6) :
    n * v * n⁻¹ * v⁻¹ ∈ pullSub Φ P ↔
      glLin k (Φ (Additive.ofMul (⟨v, hv⟩ : V))) - Φ (Additive.ofMul (⟨v, hv⟩ : V)) ∈ P := by
  have e : v * n * v⁻¹ * n⁻¹ = (n * v * n⁻¹ * v⁻¹)⁻¹ := by group
  rw [← comm_mem_pullSub hn hk hv P, e, inv_mem_iff]

end Transport

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem V₁_eq_pullSub
    (S : HullSetting G T L V z) : S.V₁ = pullSub S.Φ V1sub := by
  rw [S.V₁_eq]
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 (mem_pullSub.2 ⟨S.hzV, ?_⟩)) ?_
  · rw [S.phi_z]
    exact vecOf_fifteen_mem_V1sub
  · rw [card_pullSub, card_V1sub, Nat.card_zpowers, S.hz2]

theorem V₂_eq_pullSub
    (S : HullSetting G T L V z) : S.V₂ = pullSub S.Φ V2sub :=
  S.V2_eq S.isV2

theorem V₃_eq_pullSub
    (S : HullSetting G T L V z) : S.V₃ = pullSub S.Φ V3sub :=
  S.V3_eq (by rw [← S.V₂_eq_pullSub]; exact S.le23) S.le3 S.T_normalizes_V₃ S.card_V₃

theorem e18_mem
    (S : HullSetting G T L V z) : elOf S.Φ (vecOf 18) ∈ S.V₃ := by
  rw [S.V₃_eq_pullSub]
  exact elOf_mem_pullSub.2 ((hasMask_V3sub' 18 (by norm_num)).2 (by decide))

theorem e53_mem
    (S : HullSetting G T L V z) : elOf S.Φ (vecOf 53) ∈ S.V₂ := by
  rw [S.V₂_eq_pullSub]
  exact elOf_mem_pullSub.2 ((hasMask_V2sub 53 (by norm_num)).2 (by decide))

theorem isElemAbelian_V₃
    (S : HullSetting G T L V z) : IsElemAbelian 2 S.V₃ :=
  elemAb_of_le (isElemAbelian_of_isElementaryAbelian' V) S.le3

theorem inf_le_nX
    (S : HullSetting G T L V z) : L ⊓ normalizer (S.V₁ : Set G) ≤ U3P33.nX S.V₃ S.V₁ := by
  rintro l ⟨hl, hlN⟩
  refine ⟨?_, hlN⟩
  obtain ⟨j, hj, hlj⟩ := S.hL l hl
  have hlH : l ∈ S.H := by
    rw [← S.normalizer_V₁]
    exact hlN
  have hfix := (S.mem_H_iff (S.hLV hl) hlj).1 hlH
  rw [S.V₃_eq_pullSub]
  exact mem_normalizer_pullSub (S.hLV hl) hlj (map_V3sub_of_fix (J6_le_N6 hj) hfix)

theorem T_le_nX
    (S : HullSetting G T L V z) : T ≤ U3P33.nX S.V₃ S.V₁ := fun _ ht =>
  ⟨S.T_normalizes_V₃ ht, S.T_le_N_V₁ ht⟩

theorem T_le_N_L₁
    (S : HullSetting G T L V z) : T ≤ normalizer (L₁Of L S.V₁ : Set G) := by
  rw [← lOne_eq_L₁Of]
  exact le_normalizer_lOne S.hTL S.T_le_N_V₁

theorem isPGroup_sup_inf_centralizer
    (S : HullSetting G T L V z) : IsPGroup 2 ↥((L ⊔ T) ⊓ centralizer (S.V₃ : Set G)) := by
  have h23 : pullSub S.Φ V2sub ≤ S.V₃ := by
    rw [← S.V₂_eq_pullSub]
    exact S.le23
  refine isPGroup_two_of_forall' fun c hc => ?_
  obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_sup S.hH.sylow.1 S.hTL hc.1
  have hmem : c ^ 2 ^ k ∈ L ⊓ centralizer (pullSub S.Φ V2sub : Set G) :=
    ⟨hk, Subgroup.centralizer_le h23 (pow_mem hc.2 _)⟩
  obtain ⟨m, hm⟩ := exists_two_pow_eq_one S.isPGroup_CL_V2 hmem
  exact ⟨k + m, by rw [pow_add, pow_mul, hm]⟩

theorem isPGroup_L₁_sup_inf
    (S : HullSetting G T L V z) :
    IsPGroup 2 ↥((L₁Of L S.V₁ ⊔ T) ⊓ centralizer (S.V₃ : Set G)) :=
  S.isPGroup_sup_inf_centralizer.to_le
    (inf_le_inf_right _ (sup_le_sup_right ((oTwoRes_le _).trans inf_le_left) T))

theorem isPGroup_L₁_inf
    (S : HullSetting G T L V z) : IsPGroup 2 ↥(L₁Of L S.V₁ ⊓ centralizer (S.V₃ : Set G)) :=
  S.isPGroup_L₁_sup_inf.to_le (inf_le_inf_right _ le_sup_left)

theorem exists_c
    (S : HullSetting G T L V z) :
    ∃ c ∈ L₁Of L S.V₁, ∃ hc : c ∈ normalizer (V : Set G), ∃ e ∈ xCodes,
      ((S.rho ⟨c, hc⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e.1 ∧
        (((S.rho ⟨c, hc⟩)⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
          colMat e.2 := by
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos S.l₁).ne'
  have hl₀L : S.l₁ ^ 2 ^ a ∈ L ⊓ normalizer (S.V₁ : Set G) := by
    rw [S.normalizer_V₁]
    exact ⟨pow_mem S.l₁_mem _, pow_mem S.l₁_H _⟩
  have hl₀m : (S.l₁ ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← ham, pow_orderOf_eq_one]
  have hX : S.rho ⟨S.l₁ ^ 2 ^ a, pow_mem S.l₁_N _⟩ = xGL ∨
      S.rho ⟨S.l₁ ^ 2 ^ a, pow_mem S.l₁_N _⟩ = xGL * xGL := by
    rw [S.rho_pow S.l₁_N, S.rho_eq_of_spec _ S.l₁_spec]
    exact xGL_pow_two_pow a
  obtain ⟨e, he, h1, h2⟩ := exists_xCode hX
  exact ⟨S.l₁ ^ 2 ^ a, subset_closure ⟨hl₀L, m, hm, hl₀m⟩, pow_mem S.l₁_N _, e, he, h1, h2⟩

theorem not_mem_trivSub
    (S : HullSetting G T L V z) {n : G} (hn : n ∈ normalizer (V : Set G)) {e : List ℕ}
    (he : ((S.rho ⟨n, hn⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e)
    (hlt : vapp e 18 < 64) (hbit : v1mask.testBit (vapp e 18 ^^^ 18) = false) :
    n ∉ L32NSet14.trivSub S.V₃ S.V₁ := by
  intro h
  have h1 := h.2.2 _ S.e18_mem
  rw [S.V₁_eq_pullSub, conj_comm_mem_pullSub hn (S.rho_spec ⟨n, hn⟩) (elOf_mem (Φ := S.Φ) _),
    phi_elOf, glLin_vecOf_sub he,
    hasMask_V1sub _ (Nat.xor_lt_two_pow (n := 6) hlt (by norm_num)), hbit] at h1
  exact Bool.false_ne_true h1

theorem exists_T_not_triv
    (S : HullSetting G T L V z) : ∃ t ∈ T, t ∉ L32NSet14.trivSub S.V₃ S.V₁ := by
  obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT (i := 2) (by simp))
  have hu : ((u6GL 2 : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (u6c 2) :=
    rfl
  exact ⟨t, htTL.1, S.not_mem_trivSub ht (hrho ▸ hu) (vapp_u6c_lt 2 18) sy_codes.1⟩

theorem gen3
    (S : HullSetting G T L V z) : conjClosure S.V₂ (L₁Of L S.V₁) = S.V₃ := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c
  obtain ⟨-, h53, -, hb53, -⟩ := xCodes_spec e he
  have hLN : L₁Of L S.V₁ ≤ normalizer (S.V₃ : Set G) := le_sup_left.trans S.L₁T_normalizes_V₃
  have hV₂W : S.V₂ ≤ conjClosure S.V₂ (L₁Of L S.V₁) := le_conjClosure _ _
  have hWV : conjClosure S.V₂ (L₁Of L S.V₁) ≤ S.V₃ := conjClosure_le fun h hh v hv =>
    (mem_normalizer_iff.mp (hLN hh) v).mp (S.le23 hv)
  have hbW : c * elOf S.Φ (vecOf 53) * c⁻¹ ∈ conjClosure S.V₂ (L₁Of L S.V₁) :=
    mem_conjClosure hcL S.e53_mem
  have hbV : c * elOf S.Φ (vecOf 53) * c⁻¹ ∉ S.V₂ := by
    rw [S.V₂_eq_pullSub, conj_mem_pullSub hc (S.rho_spec ⟨c, hc⟩) (elOf_mem (Φ := S.Φ) _),
      phi_elOf, glLin_vecOf hX, hasMask_V2sub _ h53, hb53]
    exact Bool.false_ne_true
  have h1 := Subgroup.card_dvd_of_le hV₂W
  have h2 := Subgroup.card_dvd_of_le hWV
  rw [S.card_V₂] at h1
  rw [S.card_V₃] at h2
  have hne : Nat.card (conjClosure S.V₂ (L₁Of L S.V₁)) ≠ 4 := fun h => hbV (by
    rw [Subgroup.eq_of_le_of_card_ge hV₂W (by rw [h, S.card_V₂])]
    exact hbW)
  have h8 : Nat.card (conjClosure S.V₂ (L₁Of L S.V₁)) = 8 := by
    have hpos : 0 < Nat.card (conjClosure S.V₂ (L₁Of L S.V₁)) := Nat.card_pos
    have hle : Nat.card (conjClosure S.V₂ (L₁Of L S.V₁)) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨d, hd⟩ := h1
    rw [hd] at hle hpos hne ⊢
    have hd2 : d ≤ 2 := by omega
    have hd0 : 0 < d := by omega
    interval_cases d <;> omega
  exact Subgroup.eq_of_le_of_card_ge hWV (by rw [S.card_V₃, h8])

theorem comm3
    (S : HullSetting G T L V z) : ⁅S.V₃, pCoreOf 2 (L₁Of L S.V₁)⁆ = S.V₁ := by
  have hW := S.isElemAbelian_V₃
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv q hq
    have hq' := (U3P33.pCoreOf_le_trivSub hW S.card_V₃ S.card_V₁ S.V₁_le_V₃ S.inf_le_nX hq).2.2
      v hv
    have e : ⁅v, q⁆ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact inv_mem hq'
  · obtain ⟨c, hcL, hc, e, he, hX, hXi⟩ := S.exists_c
    obtain ⟨-, -, -, -, h29⟩ := xCodes_spec e he
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT (i := 0) (by simp))
    have hct : t * c * t⁻¹ ∈ L₁Of L S.V₁ :=
      (mem_normalizer_iff.mp (S.T_le_N_L₁ htTL.1) c).mp hcL
    set k := c * (t * c * t⁻¹) * c⁻¹ * (t * c * t⁻¹)⁻¹ with hk
    have hkQ : k ∈ pCoreOf 2 (L₁Of L S.V₁) :=
      U3P33.commutator_mem_pCoreOf hW S.card_V₃ S.card_V₁ S.V₁_le_V₃ S.inf_le_nX
        S.isPGroup_L₁_inf hcL hct
    have hkN : k ∈ normalizer (V : Set G) :=
      mul_mem (mul_mem (mul_mem hc (mul_mem (mul_mem ht hc) (inv_mem ht))) (inv_mem hc))
        (inv_mem (mul_mem (mul_mem ht hc) (inv_mem ht)))
    have hA : ((u6GL 0 : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        colMat (u6c 0) := rfl
    have hAi : (((u6GL 0)⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        colMat (u6ci 0) := rfl
    have e1 : (⟨k, hkN⟩ : normalizer (V : Set G)) = ⟨c, hc⟩ * (⟨t, ht⟩ * ⟨c, hc⟩ * ⟨t, ht⟩⁻¹) *
        ⟨c, hc⟩⁻¹ * (⟨t, ht⟩ * ⟨c, hc⟩ * ⟨t, ht⟩⁻¹)⁻¹ := rfl
    have e2 : S.rho ⟨k, hkN⟩ = S.rho ⟨c, hc⟩ * u6GL 0 * S.rho ⟨c, hc⟩ * (u6GL 0)⁻¹ *
        (S.rho ⟨c, hc⟩)⁻¹ * u6GL 0 * (S.rho ⟨c, hc⟩)⁻¹ * (u6GL 0)⁻¹ := by
      rw [e1]
      simp only [map_mul, map_inv, hrho]
      group
    have hk18 : glLin (S.rho ⟨k, hkN⟩) (vecOf 18) = vecOf 29 := by
      rw [e2]
      simp only [map_mul, LinearEquiv.mul_apply]
      rw [glLin_vecOf hAi, glLin_vecOf hXi, glLin_vecOf hA, glLin_vecOf hXi, glLin_vecOf hAi,
        glLin_vecOf hX, glLin_vecOf hA, glLin_vecOf hX, h29]
    have h15 : (18 : ℕ) ^^^ 15 = 29 := by decide
    have hkv : k * elOf S.Φ (vecOf 18) * k⁻¹ = elOf S.Φ (vecOf 18) * z := by
      refine phi_injective' (Φ := S.Φ) ((mem_normalizer_iff.1 hkN _).1 (elOf_mem _))
        (mul_mem (elOf_mem _) S.hzV) ?_
      rw [phi_conj' hkN (S.rho_spec ⟨k, hkN⟩) (elOf_mem _), phi_elOf, hk18,
        phi_mul' (elOf_mem _) S.hzV, phi_elOf, S.phi_z, ← vecOf_xor, h15]
    have hcomm : ⁅k, elOf S.Φ (vecOf 18)⁆ = z := by
      rw [commutatorElement_def, hkv,
        elemAb_comm (isElemAbelian_of_isElementaryAbelian' V) (elOf_mem _) S.hzV]
      group
    have hz : z ∈ ⁅S.V₃, pCoreOf 2 (L₁Of L S.V₁)⁆ := by
      have h1 := Subgroup.commutator_mem_commutator hkQ S.e18_mem
      rw [Subgroup.commutator_comm, hcomm] at h1
      exact h1
    calc S.V₁ = zpowers z := S.V₁_eq
      _ ≤ ⁅S.V₃, pCoreOf 2 (L₁Of L S.V₁)⁆ := zpowers_le.2 hz

theorem Lp3
    (S : HullSetting G T L V z) : (pCoreOf 2 (L₁Of L S.V₁)).relIndex (L₁Of L S.V₁) = 3 := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c
  obtain ⟨h18, -, hb18, -, -⟩ := xCodes_spec e he
  exact U3P33.relIndex_eq_three S.isElemAbelian_V₃ S.card_V₃ S.card_V₁ S.V₁_le_V₃ S.inf_le_nX
    S.isPGroup_L₁_inf hcL (S.not_mem_trivSub hc hX h18 hb18)

theorem index2
    (S : HullSetting G T L V z) : (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)).relIndex T = 2 := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c
  obtain ⟨h18, -, hb18, -, -⟩ := xCodes_spec e he
  obtain ⟨t, ht, htn⟩ := S.exists_T_not_triv
  exact U3P33.relIndex_eq_two S.isElemAbelian_V₃ S.card_V₃ S.card_V₁ S.V₁_le_V₃ S.inf_le_nX
    S.T_le_nX S.hH.sylow.1 S.isPGroup_L₁_sup_inf hcL (S.not_mem_trivSub hc hX h18 hb18) ht htn

theorem irredOn
    (S : HullSetting G T L V z) : IsIrredOnSection (L₁Of L S.V₁ ⊔ T) S.V₃ S.V₁ :=
  ⟨S.V₁_lt_V₃, S.L₁T_normalizes_V₃, sup_le ((oTwoRes_le _).trans inf_le_right) S.T_le_N_V₁,
    S.irred⟩

theorem cv3
    (S : HullSetting G T L V z) : ∀ y ∈ normalizer (V : Set G) ⊓ centralizer (S.V₃ : Set G),
      Odd (orderOf y) → y ∈ centralizer (V : Set G) := by
  rintro y ⟨hyN, hyC⟩ hodd
  have hk := S.rho_spec ⟨y, hyN⟩
  rw [S.V₃_eq_pullSub] at hyC
  have hfix := (mem_centralizer_pullSub_iff hyN hk V3sub).1 hyC
  have hsq := sq_eq_one_of_fixes (S.rho_mem_N6 _) hfix
  rw [mem_centralizer_V_iff hyN hk]
  have h1 : S.rho ⟨y, hyN⟩ ^ orderOf y = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : normalizer (V : Set G)) ^ orderOf y = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one y)
    rw [this, map_one]
  obtain ⟨j, hj⟩ := hodd
  rw [hj, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul] at h1
  exact h1

theorem bcase
    (S : HullSetting G T L V z) (hNL : U3NondegLineCentralizer) :
    ∃ g ∈ L ⊓ normalizer (S.V₂ : Set G), g ^ 3 = 1 ∧ g ∉ normalizer (S.V₁ : Set G) ∧
      centralizer ((S.V₃ ⊔ S.V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := by
  obtain ⟨g, hgX, hg3, -, hgN, hρg⟩ := S.exists_X_elem
  rw [← S.V₂_eq_pullSub] at hgX
  refine ⟨g, oTwoRes_le _ hgX, hg3, ?_, ?_⟩
  · rw [S.normalizer_V₁, S.mem_H_iff hgN (S.rho_spec ⟨g, hgN⟩)]
    rcases hρg with h | h
    · rw [h, glLin_vecOf coe_yGL]
      intro h'
      exact cert_y.2 (vecOf_injective (vapp_u6c_lt 4 15) (by norm_num) h')
    · rw [h, map_mul, LinearEquiv.mul_apply, glLin_vecOf coe_yGL, glLin_vecOf coe_yGL]
      intro h'
      exact sy_codes.2.1 (vecOf_injective (vapp_u6c_lt 4 _) (by norm_num) h')
  · set Γ := (u3ConjLin V (normalizer (V : Set G)) le_rfl).range
    have hle : Γ.map (linConj S.Φ).toMonoidHom ≤ N6L := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      obtain ⟨k, hk, hkn⟩ := S.hN n
      exact ⟨k, hk, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hkn]⟩
    have hprof := qtBinarySixProfile_of_map_linConj S.Φ b0 Γ (qtBinarySixProfile_of_le_N6L hle)
    have hu : elOf S.Φ (vecOf 18) ∈ V := elOf_mem _
    have hv : g * elOf S.Φ (vecOf 18) * g⁻¹ ∈ V := (mem_normalizer_iff.1 hgN _).1 hu
    have hC := hNL G T L V z S.hH S.hU3 S.hF _ hprof.2.1 hprof.2.2.1
      (fun n x y => hprof.2.2.2.1 _ ⟨n, rfl⟩ x y) _ _ hu hv (by
        rw [LinearMap.compl₁₂_apply]
        simp only [LinearEquiv.coe_coe]
        rw [phi_elOf, phi_conj' hgN (S.rho_spec ⟨g, hgN⟩) hu, phi_elOf]
        rcases hρg with h | h
        · rw [h, glLin_vecOf coe_yGL, b0_vecOf, sy_codes.2.2.1]
          decide
        · rw [h, map_mul, LinearEquiv.mul_apply, glLin_vecOf coe_yGL, glLin_vecOf coe_yGL,
            b0_vecOf, sy_codes.2.2.2]
          decide)
    refine le_trans (Subgroup.centralizer_le ?_) hC
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact mem_sup_left S.e18_mem
    · exact mem_sup_right ⟨_, S.e18_mem, rfl⟩

theorem exists_inv_mul_mem_centralizer
    (S : HullSetting G T L V z) {A : Subgroup G}
    (hTA : T ⊓ L ≤ A) (h1 : S.l₁ ∈ A)
    (hyA : ∃ x ∈ A, ∃ hx : x ∈ normalizer (V : Set G),
      S.rho ⟨x, hx⟩ = yGL ∨ S.rho ⟨x, hx⟩ = yGL * yGL) :
    ∀ l ∈ L, ∃ a ∈ A, a⁻¹ * l ∈ centralizer (V : Set G) := by
  set Ab : Subgroup (GL (Fin 6) (ZMod 2)) := (A.subgroupOf (normalizer (V : Set G))).map S.rho
  have hmem : ∀ {a : G} (ha : a ∈ A) (haN : a ∈ normalizer (V : Set G)),
      S.rho ⟨a, haN⟩ ∈ Ab := fun ha haN => mem_map_of_mem _ (mem_subgroupOf.2 ha)
  have h012 : ∀ i ∈ ([0, 1, 2] : List (Fin 5)), u6GL i ∈ Ab := by
    intro i hi
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT hi)
    rw [← hrho]
    exact hmem (hTA htTL) ht
  have h3 : u6GL 3 ∈ Ab := by
    rw [← xGL_eq_u6GL, ← S.rho_eq_of_spec _ S.l₁_spec]
    exact hmem h1 S.l₁_N
  have h4 : u6GL 4 ∈ Ab := by
    obtain ⟨x, hxA, hx, hrho⟩ := hyA
    have hx' := hmem hxA hx
    rw [← yGL_eq_u6GL]
    rcases hrho with h | h
    · rw [← h]
      exact hx'
    · rw [h] at hx'
      rw [← yGL_pow_four]
      exact mul_mem hx' hx'
  have hJ : J6 ≤ Ab := by
    rintro _ ⟨g, rfl⟩
    have hle : (⊤ : Subgroup U33G) ≤ Ab.comap rho6 := by
      rw [← u33Data.gen, closure_le]
      obtain ⟨ha, hb, hs, hx, hy⟩ := rho6_abs
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · show rho6 u33Data.a ∈ Ab
        rw [ha]
        exact h012 0 (by simp)
      · show rho6 u33Data.b ∈ Ab
        rw [hb]
        exact h012 1 (by simp)
      · show rho6 u33Data.s ∈ Ab
        rw [hs]
        exact h012 2 (by simp)
      · show rho6 u33Data.x ∈ Ab
        rw [hx]
        exact h3
      · show rho6 u33Data.y ∈ Ab
        rw [hy]
        exact h4
    exact hle (mem_top g)
  intro l hlL
  have hlJ : S.rho ⟨l, S.hLV hlL⟩ ∈ Ab := hJ (S.rho_L_mem hlL)
  obtain ⟨⟨a, haN⟩, ha, hae⟩ := mem_map.1 hlJ
  refine ⟨a, mem_subgroupOf.1 ha, ?_⟩
  have h1' : S.rho ((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV hlL⟩) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  have h2 : (((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV hlL⟩ :
      normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) :=
    (mem_centralizer_V_iff _ (S.rho_spec _)).2 h1'
  exact h2

theorem genL
    (S : HullSetting G T L V z) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    L ≤ A6.g1 T V ⊔ L₁Of L V₂ := by
  obtain ⟨x, hxX, -, -, hx, hrho⟩ := S.exists_X_elem
  rw [← S.V2_eq hV2] at hxX
  have hg1 : A6.g1 T V = S.H := S.g1_eq_H
  intro l hl
  obtain ⟨a, ha, hal⟩ := S.exists_inv_mul_mem_centralizer (A := L₁Of L V₂ ⊔ L ⊓ S.H)
    (fun t ht => mem_sup_right ⟨ht.2, S.T_le_H ht.1⟩) (mem_sup_right ⟨S.l₁_mem, S.l₁_H⟩)
    ⟨x, mem_sup_left hxX, hx, hrho⟩ l hl
  have haH : L₁Of L V₂ ⊔ L ⊓ S.H ≤ A6.g1 T V ⊔ L₁Of L V₂ := by
    rw [hg1]
    exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
  have hcH : a⁻¹ * l ∈ A6.g1 T V := by
    rw [hg1, S.H_eq]
    exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hal) z S.hzV).symm
  have := mul_mem (haH ha) (mem_sup_left hcH : a⁻¹ * l ∈ A6.g1 T V ⊔ L₁Of L V₂)
  rwa [mul_inv_cancel_left] at this

theorem set14
    (S : HullSetting G T L V z) (hNL : U3NondegLineCentralizer) {V₂ : Subgroup G}
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) (hV2 : A6.IsV2 T V V₂) :
    Set14 G T L V V₂ S.V₃ (L₁Of L S.V₁) := by
  have h1 := S.fsuV1_eq_V₁
  have h22 : V₂ = S.V₂ := (S.V2_eq hV2).trans S.V₂_eq_pullSub.symm
  have h1332 := S.h1332 G T L S.hH L S.hH.faithful
  obtain ⟨g, hg, hg3, hg1, hgC⟩ := S.bcase hNL
  exact
  { h13 := S.hH
    irr := hV
    zv := hZV
    v2 := hV2
    card1 := by rw [h1]; exact S.card_V₁
    le23 := by rw [h22]; exact S.le23
    le3V := S.le3
    T_V3 := S.T_normalizes_V₃
    card3 := S.card_V₃
    Lp_eq := (L32NSet14.oTwoUpper_oTwoRes _).symm
    Lp_L := (oTwoRes_le _).trans inf_le_left
    Lp_V1 := by rw [h1]; exact (oTwoRes_le _).trans inf_le_right
    T_Lp := S.T_le_N_L₁
    gen := by rw [h22]; exact S.gen3
    irred := by rw [h1]; exact S.irredOn
    comm3 := by rw [h1]; exact S.comm3
    index2 := S.index2
    Lp3 := S.Lp3
    Lp_def := ⟨fun h => absurd h (not_isHatA6_of_psu S.hU3), fun _ => by rw [h1]⟩
    cv3 := S.cv3
    clv := S.inf_centralizer_le.trans (pCoreOf_le_o2Z L)
    bcase := Or.inr ⟨g, by rw [h22]; exact hg, hg3, by rw [h1]; exact hg1, hgC⟩
    genL := S.genL hV2
    fsu := (h1332.2.2.1.2 V hV).2.2.1
    T_L := S.hTL
    V_T := S.hVT
    T_V := S.hTV
    Mmax := h1332.2.1.2.2.1
    uniq := h1332.2.1.2.2.2
    ti := fun U H hU hUV hHU =>
      (u3_selected_local_normalizer_and_TI_of_1332 S.h1332 S.hH S.hF).2.2.2.1 U hU hUV H hHU }

end HullSetting

theorem set14ProducerU33_of
    (h1332 : Stmt13_3_2) (hNL : U3NondegLineCentralizer) : Set14ProducerU33 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hU3 _
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  exact ⟨_, _, S.set14 hNL hV hZV hV2⟩

end CFSG.Quasithin.H13.U3
