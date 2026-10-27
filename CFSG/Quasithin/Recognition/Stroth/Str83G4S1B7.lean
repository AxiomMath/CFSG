module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Vertex
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzQuadratic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section SectionRep

variable {H U L N : Subgroup G} {X : Type} [Group X]

theorem sectionRep_isIrreducible (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N) (e : oTwoQuot ↥H ≃* X) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    (sectionRep hHL hHN hNL hE hO e).IsIrreducible := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, ?_⟩
  · have hntE : Nontrivial (Ch3z.chiefMod L N) := by
      obtain ⟨n, hnN, hnL⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hstep.2.2.1)
      exact ⟨⟨Ch3z.chiefIota hNL ⟨n, hnN⟩, 1, fun h =>
        hnL ((Ch3z.chiefIota_eq_one_iff hNL ⟨n, hnN⟩).1 h)⟩⟩
    infer_instance
  · intro W hW
    let K : Subgroup (Ch3z.chiefMod L N) :=
      { carrier := {x | Additive.ofMul x ∈ W}
        mul_mem' := by
          intro x y hx hy
          change Additive.ofMul x + Additive.ofMul y ∈ W
          exact W.add_mem hx hy
        one_mem' := by
          change (0 : Additive (Ch3z.chiefMod L N)) ∈ W
          exact W.zero_mem
        inv_mem' := by
          intro x hx
          change -Additive.ofMul x ∈ W
          exact W.neg_mem hx }
    have hKinv : ∀ x ∈ Ch3z.chiefAut H L N, ∀ w ∈ K, x w ∈ K := by
      intro x hx w hw
      obtain ⟨h, hh⟩ := Ch3z.chiefHom_surjective hHL hHN ⟨x, hx⟩
      have hxeq : ((Ch3z.chiefHom hHL hHN h : Ch3z.chiefAut H L N) :
          MulAut (Ch3z.chiefMod L N)) = x := congrArg Subtype.val hh
      have h1 := hW (e (QuotientGroup.mk h)) (Additive.ofMul w) hw
      rw [sectionRep_apply, sectionAction_apply, hxeq] at h1
      exact h1
    rcases Ch3z.chiefMod_irr hstep hUH K hKinv with hK | hK
    · left
      ext x
      constructor
      · intro hx
        have hxK : x.toMul ∈ K := hx
        rw [hK, Subgroup.mem_bot] at hxK
        rw [Submodule.mem_bot]
        change x.toMul = 1
        exact hxK
      · intro hx
        rw [Submodule.mem_bot] at hx
        rw [hx]
        exact W.zero_mem
    · right
      rw [eq_top_iff]
      intro x _
      have hxK : x.toMul ∈ K := by rw [hK]; exact Subgroup.mem_top _
      change Additive.ofMul x.toMul ∈ W
      exact hxK

theorem sectionRep_chiefIota (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* X) (h : ↥H) (n : ↥N) (hhn : (h : G) * n * (h : G)⁻¹ ∈ N) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk h))
        (Additive.ofMul (Ch3z.chiefIota hNL n)) =
      Additive.ofMul (Ch3z.chiefIota hNL ⟨(h : G) * n * (h : G)⁻¹, hhn⟩) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  rw [sectionRep_apply, sectionAction_apply]
  exact congrArg Additive.ofMul (Ch3z.chiefPsi_iota hHL hHN hNL h n hhn)

theorem sectionRep_comp_sub_one_eq_zero {Y : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* X) (c s : ↥H)
    (hc : ∀ n ∈ N, (c : G) * n * (c : G)⁻¹ * n⁻¹ ∈ Y)
    (hs : ∀ y ∈ Y, (s : G) * y * (s : G)⁻¹ * y⁻¹ ∈ L) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    (sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk s)) - 1) ∘ₗ
      (sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk c)) - 1) = 0 := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  ext w
  obtain ⟨n, hn⟩ := Ch3z.chiefIota_surjective hNL w.toMul
  have hw : w = Additive.ofMul (Ch3z.chiefIota hNL n) := by rw [hn]; rfl
  have hcn : (c : G) * n * (c : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hHN c.2) n).mp n.2
  set y : ↥N := ⟨(c : G) * n * (c : G)⁻¹, hcn⟩ * n⁻¹ with hy
  have hyY : (y : G) ∈ Y := hc n n.2
  have hsy : (s : G) * y * (s : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hHN s.2) y).mp y.2
  have hyn : (⟨(c : G) * n * (c : G)⁻¹, hcn⟩ : ↥N) = y * n := by
    rw [hy, inv_mul_cancel_right]
  have hadd : (Additive.ofMul (Ch3z.chiefIota hNL (y * n)) : Additive (Ch3z.chiefMod L N)) =
      Additive.ofMul (Ch3z.chiefIota hNL y) + Additive.ofMul (Ch3z.chiefIota hNL n) := by
    rw [map_mul]
    rfl
  have hc1 : (sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk c)) - 1) w =
      Additive.ofMul (Ch3z.chiefIota hNL y) := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hw, sectionRep_chiefIota _ _ _ _ _ _ c n hcn,
      hyn, hadd, add_sub_cancel_right]
  have hs1 : (sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk s)) - 1)
      (Additive.ofMul (Ch3z.chiefIota hNL y)) = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, sectionRep_chiefIota _ _ _ _ _ _ s y hsy,
      sub_eq_zero]
    congr 1
    have h1 : Ch3z.chiefIota hNL (⟨(s : G) * y * (s : G)⁻¹, hsy⟩ * y⁻¹) = 1 :=
      (Ch3z.chiefIota_eq_one_iff hNL _).2 (hs y hyY)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  rw [LinearMap.comp_apply, hc1, hs1, LinearMap.zero_apply]

end SectionRep

section B7

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_q2_le_s (hfr : Str83G4Frame L1 L2 S a) :
    Q2 L1 L2 S ≤ S := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  rw [← (str83_caseI_basics hF hB ha hSz hL2 hZI).2.2.2.1]
  exact inf_le_left

theorem str83G4_q1_inf_q2_le_centralizerMod
    (hfr : Str83G4Frame L1 L2 S a) :
    Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤
      centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) := by
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
    exact (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  rintro x ⟨hx1, hx2⟩
  refine ⟨hx2, ((str83G4_q2_le_s hfr).trans ((le_sup_right : S ≤ bigB L1 L2 S).trans
    (bigB_le_normalizer_z2 L1 L2 S))) hx2, fun u hu => ?_⟩
  have h1 : ⁅x, u⁆ ∈ ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ := Subgroup.commutator_mem_commutator hx1 hu
  rw [Subgroup.commutator_comm] at h1
  exact hZ1Z2 (str83G4_commutator_x_q1_le hfr h1)

theorem str83G4_exists_image_suzukiZ0
    {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hfr : Str83G4Frame L1 L2 S a) (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K)
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K) {c₀ : G}
    (hc₀ : c₀ ∈ centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S))
    (hc₀Q : c₀ ∉ Q1 L1 L2 S) :
    ∀ z ∈ suzukiZ0 a K, ∃ c : ↥(L1 ⊔ S),
      (c : G) ∈ centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) ∧
        e (QuotientGroup.mk c) = z := by
  classical
  set C := centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) with hCdef
  have hCS : C ≤ L1 ⊔ S :=
    (centralizerMod_le_left _ _ _).trans ((str83G4_q2_le_s hfr).trans le_sup_right)
  have hpc := str83G4_pCoreOf_sup_left hfr
  let c₀' : ↥(L1 ⊔ S) := ⟨c₀, hCS hc₀⟩
  have hU : e (QuotientGroup.mk c₀') ∈ suzukiU a K := by
    rw [← he]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr ((centralizerMod_le_left _ _ _).trans
        (str83G4_q2_le_s hfr) hc₀)))
  have hne : e (QuotientGroup.mk c₀') ≠ 1 := by
    intro h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact hc₀Q (hpc ▸ Subgroup.mem_map_of_mem _ h1)
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).1 hU
  obtain ⟨c₁, hc₁, v₀, hv₀, hc₁e⟩ : ∃ c₁ : ↥(L1 ⊔ S), (c₁ : G) ∈ C ∧ ∃ v₀ : K, v₀ ≠ 0 ∧
      e (QuotientGroup.mk c₁) = suzukiSElt a K 0 v₀ := by
    by_cases hu : u = 0
    · subst hu
      refine ⟨c₀', hc₀, v, fun hv => hne ?_, huv.symm⟩
      rw [← huv, hv, suzukiSElt_zero_zero hK]
    · refine ⟨c₀' * c₀', C.mul_mem hc₀ hc₀, u ^ 2 ^ (a + 1) * u,
        mul_ne_zero (pow_ne_zero _ hu) hu, ?_⟩
      rw [QuotientGroup.mk_mul, map_mul, ← huv, suzukiSElt_mul hK, CharTwo.add_self_eq_zero,
        CharTwo.add_self_eq_zero, zero_add]
  intro z hz
  obtain ⟨b, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
  by_cases hb : b = 0
  · refine ⟨1, C.one_mem, ?_⟩
    rw [hb, suzukiSElt_zero_zero hK, QuotientGroup.mk_one, map_one]
  let m : Kˣ := Units.mk0 (b * v₀⁻¹) (mul_ne_zero hb (inv_ne_zero hv₀))
  let l : Kˣ := (m ^ (2 ^ (a + 1) - 1))⁻¹
  have hDN : suzukiDElt a K l ∈
      Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
    rw [CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK]
    exact (le_sup_right : suzukiT a K ≤ suzukiB a K) (suzukiDElt_mem_suzukiT a K l)
  obtain ⟨h, hhB, hhe⟩ := str83G4_exists_lift_bigB hfr e he hDN
  have hconj : (h : G) * c₁ * (h : G)⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_centralizerMod_bigB L1 L2 S hhB) _).mp hc₁
  refine ⟨h * c₁ * h⁻¹, hconj, ?_⟩
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [Fintype.card_eq_nat_card, hK]
  have hpow : ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) = b * v₀⁻¹ := by
    have hm1 : (m : K) ^ (2 ^ (2 * a + 1) - 1) = 1 := by
      rw [← hcard]
      exact FiniteField.pow_card_sub_one_eq_one (m : K) m.ne_zero
    have hexp : (2 ^ (a + 1) - 1) * (2 ^ (a + 1) + 1) = 2 * (2 ^ (2 * a + 1) - 1) + 1 := by
      have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have h3 : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
        rw [← pow_add, ← pow_succ']
        ring_nf
      zify [h1, h2]
      push_cast
      nlinarith [h3]
    simp only [l, inv_inv, Units.val_pow_eq_pow_val]
    rw [← pow_mul, hexp, pow_succ, pow_mul', hm1, one_pow, one_mul]
    rfl
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv,
    hhe, hc₁e, suzukiDElt_conj' hK, mul_zero, hpow, mul_assoc, inv_mul_cancel₀ hv₀, mul_one]

theorem str83G4_centralizerMod_le_q1
    (hfr : Str83G4Frame L1 L2 S a) :
    centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) ≤ Q1 L1 L2 S := by
  classical
  intro c₀ hc₀
  by_contra hc₀Q
  have ha : 1 ≤ a := hfr.2.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  have hZ0 := str83G4_exists_image_suzukiZ0 hK hfr e he hc₀ hc₀Q
  obtain ⟨L, N, hstep, hZ1L, hnc⟩ := str83G4_exists_chiefStep hfr
  have hQ1S := str83G4_q1_le_s hfr
  have hXQ1 := str83X_le_q1 hfr
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := hXQ1.trans (hQ1S.trans le_sup_right)
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hXH).trans hHL
  have hXp : IsPGroup 2 (str83X L1 L2 S) :=
    (str83G4_isSylowTwoOf_sup_left hfr).2.1.to_le (hXQ1.trans hQ1S)
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hXH hXp
  have hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
    rw [str83G4_pCoreOf_sup_left hfr]
    intro q hq
    have hqH : q ∈ L1 ⊔ S := (hQ1S.trans le_sup_right) hq
    refine ⟨hqH, hHL hqH, fun n hn => hZ1L ?_⟩
    have h1 : ⁅q, n⁆ ∈ ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ :=
      Subgroup.commutator_mem_commutator hq (hstep.1.1 hn)
    rw [Subgroup.commutator_comm] at h1
    exact str83G4_commutator_x_q1_le hfr h1
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  set ρ := sectionRep hHL hHN hNL hE hO e with hρ
  haveI : Fact ρ.IsIrreducible :=
    ⟨sectionRep_isIrreducible hstep hXH hHL hHN hNL hE hO e⟩
  have hnt : ∃ g, ρ g ≠ 1 := by
    obtain ⟨y, hyR, hyC⟩ := SetLike.not_le_iff_exists.mp hnc
    have hyH : y ∈ L1 ⊔ S := twoResidual_le _ hyR
    obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, y * n * y⁻¹ * n⁻¹ ∉ L := by
      by_contra hall
      push Not at hall
      exact hyC ⟨hyH, hHL hyH, hall⟩
    refine ⟨e (QuotientGroup.mk ⟨y, hyH⟩), fun h1 => hn ?_⟩
    have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hyH) n).mp hnN
    have h2 := LinearMap.congr_fun h1 (Additive.ofMul (Ch3z.chiefIota hNL ⟨n, hnN⟩))
    rw [hρ, sectionRep_chiefIota _ _ _ _ _ _ ⟨y, hyH⟩ ⟨n, hnN⟩ hyn, Module.End.one_apply] at h2
    have h3 : Ch3z.chiefIota hNL (⟨y * n * y⁻¹, hyn⟩ * (⟨n, hnN⟩ : ↥N)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Additive.ofMul.injective h2
    exact (Ch3z.chiefIota_eq_one_iff hNL _).1 h3
  have hquad : ∀ u ∈ suzukiU a K, ∀ z ∈ suzukiZ0 a K, (ρ u - 1) ∘ₗ (ρ z - 1) = 0 := by
    intro u hu z hz
    obtain ⟨c, hcC, rfl⟩ := hZ0 z hz
    rw [← he] at hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    refine sectionRep_comp_sub_one_eq_zero (Y := Z2 L1 L2 S) hHL hHN hNL hE hO e c s
      (fun n hn => hcC.2.2 n (hstep.1.1 hn)) fun y hy => hZ1L ?_
    have h1 : ⁅(s : G), y⁆ ∈ ⁅S, Z2 L1 L2 S⁆ := Subgroup.commutator_mem_commutator hsS hy
    rw [Subgroup.commutator_comm, str83G4_commutator_z2_s hfr] at h1
    exact h1
  have hquad' : CFSG.QuasithinUnique.Setup.X7.commSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) ≤
      CFSG.QuasithinUnique.Setup.X7.fixedSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) := by
    rw [conjSubgroup_weyl_szZ]
    exact CFSG.QuasithinUnique.Setup.X7.commSub_le_fixedSub
      fun z' hz' z hz => hquad z' (suzukiZ0_le_suzukiU hz') z hz
  obtain ⟨c, φ, hφ⟩ := isSzNatural_of_commSub_le_fixedSub hK ha ρ hnt (suzukiWElt a K) hquad'
  have h0 := LinearMap.congr_fun (hquad (suzukiSElt a K 1 0) (suzukiSElt_mem_suzukiU a K 1 0)
    (suzukiSElt a K 0 1) ((mem_suzukiZ0_iff hK).2 ⟨1, rfl⟩)) (φ.symm (Pi.single 0 1))
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.one_apply] at h0
  have h1 := congrArg φ h0
  simp only [map_sub, map_zero, hφ, AddEquiv.apply_symm_apply, coe_suzukiSElt] at h1
  have h3 := congrFun h1 3
  have hθ : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hθ1 : (0 : K) ^ (2 ^ (a + 1) + 1) = 0 := zero_pow (Nat.succ_ne_zero _)
  have hθ2 : (0 : K) ^ (2 ^ (a + 1) + 2) = 0 := zero_pow (by positivity)
  have hc0 : (0 : K) ^ 2 ^ c = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, suzukiS, suzukiN, Pi.single_apply, hθ, hθ1,
    hθ2, hc0, CharTwo.sub_eq_add, h11] at h3

theorem str83G4_q1_inf_q2_eq_centralizerMod
    (hfr : Str83G4Frame L1 L2 S a) :
    Q1 L1 L2 S ⊓ Q2 L1 L2 S =
      centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) :=
  le_antisymm (str83G4_q1_inf_q2_le_centralizerMod hfr) fun _ hc =>
    ⟨str83G4_centralizerMod_le_q1 hfr hc, centralizerMod_le_left _ _ _ hc⟩

end B7

end CFSG.Quasithin.Stroth

end
