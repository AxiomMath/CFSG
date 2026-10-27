module

public import CFSG.Quasithin.H13.A7Nat1238YCoord
public import CFSG.Quasithin.H13.A7Nat1238YSetup
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.H13.A7Nat1238YCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem commutator_Ue_Kv_eq
    (h56 : AsB56) (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) {y : V}
    (hyZ : (y : G) ∈ quasithinOmegaOneCenter T) (hy4 : hammingNorm (vec ψ y) = 4)
    (hTK : T ≤ normalizer (Kv hyp e : Set G))
    (hKn : ((Kv hyp e).subgroupOf (hyp.Gv e)).Normal)
    (hKJ : Kv hyp e = ⁅Kv hyp e, thompsonJ T⁆) :
    ⁅Ue hyp e, Kv hyp e⁆ = ⁅V, Kv hyp e⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.simple
  set H := hyp.Gv e with hH
  set K := Kv hyp e with hKdef
  set U := Ue hyp e with hUdef
  have he2 : orderOf (e : G) = 2 := orderOf_eq_two_of_vecFS he
  have hred : IsTwoReducedIn H U := isTwoReducedIn_Ue hyp he2 heZ
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hTe : T ≤ H := T_le_Gv hyp heZ
  have hKH : K ≤ H := Kv_le_centralizer hyp e
  have hHK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).1 hKn
  have hHU : H ≤ normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ normalizer (U : Set G) := hKH.trans hHU
  have hO2 : pCoreOf 2 K ≤ centralizer (U : Set G) :=
    pCoreOf_le_centralizer_of_isTwoReducedIn hred hKH hHK
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hVKU : ⁅V, K⁆ ≤ ⁅U, K⁆ := commutator_le_commutator_of_weight_four hyp h he (hZU hyZ) hy4
  have hVKUle : ⁅V, K⁆ ≤ U := hVKU.trans (le_normalizer_iff_commutator_le_left.mp hKU)
  have hnc : ¬ K ≤ centralizer (U : Set G) := by
    intro hc
    obtain ⟨k, hkK, hk⟩ := exists_commutator_ne_one_of_weight_four hyp h he hy4
    apply hk
    have h1 : (y : G) * k = k * y := mem_centralizer_iff.1 (hc hkK) y (hZU hyZ)
    rw [h1]
    group
  obtain ⟨eK⟩ := autOn_Kv_equiv hyp h he hKU hO2 hnc
  have hKs : IsSimpleGroup ↥(autOn K U) := eK.isSimpleGroup
  have h60 : Nat.card ↥(autOn K U) = 60 := by
    rw [Nat.card_congr eK.toEquiv, SteinbergCB.nat_card_alternating_five]
  have hna : ∃ a ∈ autOn K U, ∃ b ∈ autOn K U, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt5_noncomm
    refine ⟨eK.symm a, (eK.symm a).2, eK.symm b, (eK.symm b).2, fun h1 => hab ?_⟩
    have h2 : eK.symm a * eK.symm b = eK.symm b * eK.symm a := Subtype.ext h1
    simpa using congrArg eK h2
  obtain ⟨A, -, hA, hLA⟩ :=
    exists_offender_moving (isSylowTwoOf_of_le hyp.sylow hTe) hTK hred hKU hKs hKJ
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hH2 : pCoreOf 2 H ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer he2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  obtain ⟨hKJ', hn, -, -, hcases⟩ := b56Cases_ffJ_autOn h56 hred.2.2.1.2 hHU hKH hHK
    (sqtkGroup_of_localSQTK hLocal hH2) (Setup.pCoreOf_autOn_eq_bot hred) hA hLA
  have hmap : ⁅U, K⁆ ≤ (commV (autOn K U)).map U.subtype := commutator_le_map_commV hKU
  have hPX : (⁅V, K⁆ : Subgroup G).subgroupOf U ≤ commV (autOn K U) := by
    intro p hp
    obtain ⟨w, hw, hwp⟩ := hmap (hVKU (mem_subgroupOf.1 hp))
    have hwp' : w = p := Subtype.ext hwp
    rw [← hwp']
    exact hw
  have hfixK : ∀ x : V, (x : G) ∈ ⁅V, K⁆ → ∀ hxU : (x : G) ∈ U,
      (⟨x, hxU⟩ : ↥U) ∈ fixV (autOn K U) → x = 1 := by
    intro x hx hxU hxf
    refine eq_one_of_mem_commutator_of_centralizes hyp h he hx fun k hk => ?_
    have h1 := congrArg Subtype.val (hxf (conjAct U ⟨k, hKU hk⟩) (conjAct_mem_autOn hKU hk))
    rwa [coe_conjAct_apply] at h1
  have hPinv : ∀ x ∈ autOn K U, ∀ p ∈ (⁅V, K⁆ : Subgroup G).subgroupOf U,
      x p ∈ (⁅V, K⁆ : Subgroup G).subgroupOf U := by
    intro x hx p hp
    obtain ⟨g, hgK, rfl⟩ := Setup.mem_autOn_iff.1 hx
    rw [mem_subgroupOf, coe_conjAct_apply]
    exact (mem_normalizer_iff.1 (normalizer_commutator_ge_right V K hgK) _).1
      (mem_subgroupOf.1 hp)
  have hPfix : (⁅V, K⁆ : Subgroup G).subgroupOf U ⊓ fixV (autOn K U) = ⊥ := by
    rw [eq_bot_iff]
    rintro p ⟨hp, hpf⟩
    rw [mem_bot]
    have hpV : (p : G) ∈ V := commutator_V_Kv_le hyp (mem_subgroupOf.1 hp)
    have h1 := congrArg Subtype.val (hfixK ⟨p, hpV⟩ (mem_subgroupOf.1 hp) p.2 hpf)
    exact Subtype.ext h1
  have hP16 : Nat.card ↥((⁅V, K⁆ : Subgroup G).subgroupOf U) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVKUle).toEquiv, card_commutator_V_Kv hyp h he]
  have hfix : ∃ k ∈ autOn K U, ∃ w₁ ∈ commV (autOn K U), w₁ ∉ fixV (autOn K U) ∧ k w₁ = w₁ ∧
      ∃ w₂, (k * k) w₂ ≠ w₂ := by
    obtain ⟨k, hk, w₁, w₂, hw₁, hw₂, hw₁1, hkw₁, hkw₂⟩ := exists_fix_not_fix_sq hyp h he
    refine ⟨conjAct U ⟨k, hKU hk⟩, conjAct_mem_autOn hKU hk, ⟨w₁, hVKUle hw₁⟩,
      hPX (mem_subgroupOf.2 hw₁), fun hf => hw₁1 (hfixK w₁ hw₁ (hVKUle hw₁) hf), ?_,
      ⟨w₂, hVKUle hw₂⟩, ?_⟩
    · apply Subtype.ext
      rw [coe_conjAct_apply]
      exact hkw₁
    · intro h2
      apply hkw₂
      have h3 := congrArg Subtype.val h2
      rw [MulAut.mul_apply, coe_conjAct_apply, coe_conjAct_apply] at h3
      calc (k * k) * (w₂ : G) * (k * k)⁻¹ = k * (k * w₂ * k⁻¹) * k⁻¹ := by group
        _ = w₂ := h3
  have hC := commV_eq_of_b56 hKJ' hn hKs h60 hna hPX hPinv hPfix hP16 hfix hcases
  refine le_antisymm ?_ hVKU
  calc ⁅U, K⁆ ≤ (commV (autOn K U)).map U.subtype := hmap
    _ = ((⁅V, K⁆ : Subgroup G).subgroupOf U).map U.subtype := by rw [hC]
    _ = ⁅V, K⁆ := map_subgroupOf_eq_of_le hVKUle

theorem centralizerSection_le_of_b56
    (h56 : AsB56) (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) {y : V}
    (hyZ : (y : G) ∈ quasithinOmegaOneCenter T) (hy4 : hammingNorm (vec ψ y) = 4)
    (hTK : T ≤ normalizer (Kv hyp e : Set G))
    (hKn : ((Kv hyp e).subgroupOf (hyp.Gv e)).Normal)
    (hKJ : Kv hyp e = ⁅Kv hyp e, thompsonJ T⁆) :
    centralizerSection (hyp.Gv e) (Kv hyp e) (pCoreOf 2 (Kv hyp e)) ≤
      centralizer ((⁅V, Kv hyp e⁆ : Subgroup G) : Set G) := by
  have hUV := commutator_Ue_Kv_eq h56 hyp h he heZ hyZ hy4 hTK hKn hKJ
  set H := hyp.Gv e with hH
  set K := Kv hyp e with hKdef
  set U := Ue hyp e with hUdef
  have he2 : orderOf (e : G) = 2 := orderOf_eq_two_of_vecFS he
  have hred : IsTwoReducedIn H U := isTwoReducedIn_Ue hyp he2 heZ
  have hKH : K ≤ H := Kv_le_centralizer hyp e
  have hHK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).1 hKn
  have hHU : H ≤ normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ normalizer (U : Set G) := hKH.trans hHU
  have hO2 : pCoreOf 2 K ≤ centralizer (U : Set G) :=
    pCoreOf_le_centralizer_of_isTwoReducedIn hred hKH hHK
  have hVKU : ⁅V, K⁆ ≤ U := hUV ▸ le_normalizer_iff_commutator_le_left.mp hKU
  intro c hc
  obtain ⟨hcH, hcK, -, hcc⟩ := hc
  have hcN : c ∈ normalizer ((⁅V, K⁆ : Subgroup G) : Set G) := by
    rw [← hUV]
    exact mem_normalizer_commutator (hHU hcH) hcK
  refine centralizes_commutator_of_commutes hyp h he hcN fun k hk w hw => ?_
  have hx : c * (k * w * k⁻¹) * c⁻¹ ∈ U :=
    (mem_normalizer_iff.1 (hHU hcH) _).1 ((mem_normalizer_iff.1 (hKU hk) w).1 (hVKU hw))
  have hoc := mem_centralizer_iff.1 (hO2 (hcc k hk)) _ hx
  calc c * (k * w * k⁻¹) * c⁻¹ = (c * (k * w * k⁻¹) * c⁻¹) * (k * c * k⁻¹ * c⁻¹) *
        (k * c * k⁻¹ * c⁻¹)⁻¹ := by group
    _ = (k * c * k⁻¹ * c⁻¹) * (c * (k * w * k⁻¹) * c⁻¹) * (k * c * k⁻¹ * c⁻¹)⁻¹ := by
        rw [hoc]
    _ = k * (c * w * c⁻¹) * k⁻¹ := by group

end CFSG.Quasithin.H13.A7
