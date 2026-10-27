module

public import CFSG.Quasithin.Recognition.SzR1CenterHolds

public section

namespace CFSG.Quasithin.Background.Harris.R1

open scoped commutatorElement

theorem vBeta_special_of_L28 :
    ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
      IsL2Quot 3 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
      IsSpecialPow 2 2 4 ↥(vBeta K1 L2 S Zs) := by
  intro G _ _ K1 L2 S Zs hset hL hne
  classical
  obtain ⟨Ω, hΩ, C, hodd, hcard, -⟩ :=
    famStmt_holds G K1 L2 S Zs hset 3 (by norm_num) (Or.inl hL) hne
  have hcb := centerBender_holds G K1 L2 S Zs hset ⟨3, by norm_num, Or.inl hL⟩ hne
  have hcard9 : Fintype.card Ω = 9 := (hcard hL).trans (by norm_num)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  have hG := C.gramRel hab
  have hz1 : C.zU a b ≠ 1 := fun h => C.cm_ne_one hab (congrArg Subtype.val h)
  have hzsq : C.zU a b * C.zU a b = 1 := hG.z_sq
  have hzU2 : C.zU a b ^ 2 = 1 := by rw [pow_two]; exact hzsq
  have hcomm_zs : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = Zs := commutator_vBeta_eq hset hne
  have hR : SzR1.GramRel (C.zU a b) (fun i : {ω : Ω // ω ≠ a} => C.wU i.1) :=
    ⟨hG.z_sq, hG.z_comm, fun i => hG.w_sq i.1,
      fun i j h => hG.w_comm i.1 j.1 (fun e => h (Subtype.ext e))⟩
  have hcard_ι : Fintype.card {ω : Ω // ω ≠ a} = 8 := by
    show Fintype.card {ω : Ω // ¬ ω = a} = 8
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard9]
  have heven : Even (Fintype.card {ω : Ω // ω ≠ a}) := by
    rw [hcard_ι]; decide
  have hwa : C.wU a ∈ Subgroup.closure
      (insert (C.zU a b) (Set.range fun i : {ω : Ω // ω ≠ a} => C.wU i.1)) := by
    obtain ⟨L', hL'⟩ : ∃ L' : List Ω, L' = (Finset.univ.erase a).toList := ⟨_, rfl⟩
    have hnd : (a :: L').Nodup := by
      rw [hL']; exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
    have hall : ∀ i : Ω, i ∈ a :: L' := by
      intro i
      rw [hL']
      by_cases h : i = a
      · simp [h]
      · simp [h]
    obtain ⟨y, hy⟩ : ∃ y : ↥(vBeta K1 L2 S Zs), y = SzR1.gprod C.wU (a :: L') := ⟨_, rfl⟩
    have hyc : ∀ u : ↥(vBeta K1 L2 S Zs), u * y = y * u := by
      intro u
      have hu : u ∈ Subgroup.closure (insert (C.zU a b) (Set.range C.wU)) := by
        rw [C.closure_wU hab]; exact Subgroup.mem_top u
      rw [hy]
      exact hG.commute_gprod_univ_closure hodd (a :: L') hnd hall hu
    have hyZ : (y : G) ∈ Zs := by
      apply hcb (y : G) y.2
      intro u hu
      exact congrArg Subtype.val (hyc ⟨u, hu⟩).symm
    have hyZ' : (y : G) ∈ Subgroup.zpowers (C.cm a b) := by
      rw [← C.Zs_eq_zpowers (C.cm_mem a b) (C.cm_ne_one hab)]
      exact hyZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyZ'
    have hyz : y = C.zU a b ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    have hyP : y ∈ Subgroup.closure
        (insert (C.zU a b) (Set.range fun i : {ω : Ω // ω ≠ a} => C.wU i.1)) := by
      rw [hyz]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) k
    have hL'P : SzR1.gprod C.wU L' ∈ Subgroup.closure
        (insert (C.zU a b) (Set.range fun i : {ω : Ω // ω ≠ a} => C.wU i.1)) := by
      show (L'.map C.wU).prod ∈ _
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hja : j ≠ a := by
        rw [hL'] at hj
        simpa using hj
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨⟨j, hja⟩, rfl⟩)
    have hsplit : C.wU a = y * (SzR1.gprod C.wU L')⁻¹ := by
      rw [hy, SzR1.gprod_cons, mul_inv_cancel_right]
    rw [hsplit]
    exact Subgroup.mul_mem _ hyP (Subgroup.inv_mem _ hL'P)
  have hPtop : Subgroup.closure
      (insert (C.zU a b) (Set.range fun i : {ω : Ω // ω ≠ a} => C.wU i.1)) = ⊤ := by
    rw [eq_top_iff, ← C.closure_wU hab, Subgroup.closure_le]
    rintro x (rfl | ⟨j, rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · by_cases hj : j = a
      · rw [hj]; exact hwa
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨⟨j, hj⟩, rfl⟩)
  have hinj := GramAbel.zz_mul_psi_injective hR hz1 (by rw [hcard_ι]; decide)
  have hsurj : Function.Surjective (fun p : ZMod 2 × ({ω : Ω // ω ≠ a} → ZMod 2) =>
      GramAbel.zz (C.zU a b) p.1 * GramAbel.psi (fun i : {ω : Ω // ω ≠ a} => C.wU i.1) p.2) := by
    intro g
    have hg : g ∈ Subgroup.closure
        (insert (C.zU a b) (Set.range fun i : {ω : Ω // ω ≠ a} => C.wU i.1)) := by
      rw [hPtop]; exact Subgroup.mem_top g
    obtain ⟨c, v, hv⟩ := GramAbel.exists_zz_mul_psi hR hg
    exact ⟨(c, v), hv.symm⟩
  have hbij : Function.Bijective (fun p : ZMod 2 × ({ω : Ω // ω ≠ a} → ZMod 2) =>
      GramAbel.zz (C.zU a b) p.1 * GramAbel.psi (fun i : {ω : Ω // ω ≠ a} => C.wU i.1) p.2) :=
    ⟨hinj, hsurj⟩
  have hcardP : Nat.card ↥(vBeta K1 L2 S Zs) = 2 ^ 9 := by
    have hc := Nat.card_eq_of_bijective _ hbij
    (rw [← hc, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, hcard_ι]; norm_num)
  have hpg : IsPGroup 2 ↥(vBeta K1 L2 S Zs) := IsPGroup.of_card hcardP
  have hZc : ∀ g : ↥(vBeta K1 L2 S Zs), (g : G) ∈ Zs →
      g ∈ Subgroup.center ↥(vBeta K1 L2 S Zs) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro u
    exact Subtype.ext (C.Zs_central u.2 hg)
  have hsq : ∀ g : ↥(vBeta K1 L2 S Zs), (g : G) * (g : G) ∈ Zs := by
    let Hsq : Subgroup ↥(vBeta K1 L2 S Zs) :=
      { carrier := {g | (g : G) * (g : G) ∈ Zs}
        mul_mem' := by
          intro x y hx hy
          have hx' : (x : G) * (x : G) ∈ Zs := hx
          have hy' : (y : G) * (y : G) ∈ Zs := hy
          have hc : ⁅(x : G), (y : G)⁆ ∈ Zs := by
            have h := Subgroup.commutator_mem_commutator x.2 y.2
            rw [hcomm_zs] at h
            exact h
          have hcomm' : (y : G) * ((x : G) * (x : G)) = ((x : G) * (x : G)) * (y : G) :=
            C.Zs_central y.2 hx'
          have key : ((x : G) * (y : G)) * ((x : G) * (y : G)) =
              ⁅(x : G), (y : G)⁆ * (((x : G) * (x : G)) * ((y : G) * (y : G))) := by
            calc ((x : G) * (y : G)) * ((x : G) * (y : G))
                = ⁅(x : G), (y : G)⁆ * ((y : G) * ((x : G) * (x : G))) * (y : G) := by
                  simp only [commutatorElement_def]; group
              _ = ⁅(x : G), (y : G)⁆ * (((x : G) * (x : G)) * (y : G)) * (y : G) := by
                  rw [hcomm']
              _ = ⁅(x : G), (y : G)⁆ * (((x : G) * (x : G)) * ((y : G) * (y : G))) := by
                  group
          show ((x : G) * (y : G)) * ((x : G) * (y : G)) ∈ Zs
          rw [key]
          exact Subgroup.mul_mem _ hc (Subgroup.mul_mem _ hx' hy')
        one_mem' := by
          show (1 : G) * 1 ∈ Zs
          rw [mul_one]
          exact Subgroup.one_mem _
        inv_mem' := by
          intro x hx
          have hx' : (x : G) * (x : G) ∈ Zs := hx
          show (x : G)⁻¹ * (x : G)⁻¹ ∈ Zs
          have e : (x : G)⁻¹ * (x : G)⁻¹ = ((x : G) * (x : G))⁻¹ := by rw [mul_inv_rev]
          rw [e]
          exact Subgroup.inv_mem _ hx' }
    have hHle : Subgroup.closure (insert (C.zU a b) (Set.range C.wU)) ≤ Hsq := by
      rw [Subgroup.closure_le]
      rintro x (rfl | ⟨j, rfl⟩)
      · show (C.cm a b) * (C.cm a b) ∈ Zs
        rw [C.Zs_sq (C.cm_mem a b)]
        exact Subgroup.one_mem _
      · show (C.zf j) * (C.zf j) ∈ Zs
        rw [C.Vf_sq (C.zf_mem j)]
        exact Subgroup.one_mem _
    intro g
    have hg : g ∈ Subgroup.closure (insert (C.zU a b) (Set.range C.wU)) := by
      rw [C.closure_wU hab]; exact Subgroup.mem_top g
    exact hHle hg
  have hzc : C.zU a b ∈ Subgroup.center ↥(vBeta K1 L2 S Zs) :=
    hZc _ (C.cm_mem a b)
  have hcenter : Subgroup.center ↥(vBeta K1 L2 S Zs) = Subgroup.zpowers (C.zU a b) := by
    apply le_antisymm
    · intro x hx
      have hxZ : (x : G) ∈ Zs := by
        apply hcb (x : G) x.2
        intro u hu
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨u, hu⟩).symm
      have hxZ' : (x : G) ∈ Subgroup.zpowers (C.cm a b) := by
        rw [← C.Zs_eq_zpowers (C.cm_mem a b) (C.cm_ne_one hab)]
        exact hxZ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ'
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.zpow_mem _ hzc k
  have hcenter_card : Nat.card (Subgroup.center ↥(vBeta K1 L2 S Zs)) = 2 := by
    rw [hcenter, Nat.card_zpowers, orderOf_eq_prime hzU2 hz1]
  have hcomm_eq : _root_.commutator ↥(vBeta K1 L2 S Zs) = Subgroup.center ↥(vBeta K1 L2 S Zs) := by
    apply le_antisymm
    · show ⁅(⊤ : Subgroup ↥(vBeta K1 L2 S Zs)), ⊤⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro x _ y _
      have hc : ⁅(x : G), (y : G)⁆ ∈ Zs := by
        have h := Subgroup.commutator_mem_commutator x.2 y.2
        rw [hcomm_zs] at h
        exact h
      exact hZc ⁅x, y⁆ hc
    · rw [hcenter]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.zpow_mem _ ?_ k
      have e : C.zU a b = ⁅C.wU a, C.wU b⁆ := Subtype.ext rfl
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have : Fact (IsPGroup 2 ↥(vBeta K1 L2 S Zs)) := ⟨hpg⟩
  have hfrat : frattini ↥(vBeta K1 L2 S Zs) = Subgroup.center ↥(vBeta K1 L2 S Zs) := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g (hg | ⟨x, rfl⟩)
      · have hg' : g ∈ _root_.commutator ↥(vBeta K1 L2 S Zs) := hg
        rw [hcomm_eq] at hg'
        exact hg'
      · show x ^ 2 ∈ Subgroup.center ↥(vBeta K1 L2 S Zs)
        refine hZc _ ?_
        rw [pow_two, Subgroup.coe_mul]
        exact hsq x
    · rw [← hcomm_eq]
      intro g hg
      exact Subgroup.subset_closure (Set.mem_union_left _ hg)
  have hcenz : ∀ z ∈ Subgroup.center ↥(vBeta K1 L2 S Zs), z ^ 2 = 1 := by
    intro z hz
    rw [hcenter] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzU2, one_zpow]
  unfold IsSpecialPow IsSpecialPGroup
  refine ⟨⟨hpg, Or.inr ⟨hcomm_eq, hfrat, hcenz⟩⟩, ?_, hcenter_card⟩
  rw [hcardP]

end CFSG.Quasithin.Background.Harris.R1

end
