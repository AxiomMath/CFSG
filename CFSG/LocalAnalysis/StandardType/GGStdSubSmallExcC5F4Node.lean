module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Trans
public import CFSG.LocalAnalysis.StandardType.GGF4TwoRootAsProof

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.TableBF4TwoInputs CFSG.StandardType.F4RootAs

theorem reflHom_eq_self {f : Fin 3 → Multiplicative (ZMod 3)} {k : Fin 3} (hk : f k = 1) :
    TableBF4Two.reflHom k f = f := by
  funext j
  rw [TableBF4Two.reflHom_apply]
  split_ifs with h
  · rw [h, hk]
    exact inv_one
  · rfl

theorem reflHom_mulSingle_mul_inv : ∀ k : Fin 3,
    TableBF4Two.reflHom k (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3))) *
        (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ =
      (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3)) : Fin 3 → Multiplicative (ZMod 3)) := by
  decide +kernel

variable
  {K : Type} [Field K] [CharP K 2]

theorem torusGen_mem_range (k : Fin 3) :
    TableBF4Two.torusGen K k ∈ (TableBF4Two.torus3 K).range := by
  rw [torusGen_eq_torus3]
  exact ⟨_, rfl⟩

theorem reflGen_commutator_torusGen (k : Fin 3) :
    TableBF4Two.reflGen K k * TableBF4Two.torusGen K k * (TableBF4Two.reflGen K k)⁻¹ *
      (TableBF4Two.torusGen K k)⁻¹ = TableBF4Two.torusGen K k := by
  rw [torusGen_eq_torus3, TableBF4Two.reflGen_conj_torus3, ← map_inv, ← map_mul]
  exact congrArg _ (reflHom_mulSingle_mul_inv k)

theorem range_torus3_le_centralizer_rootInv :
    (TableBF4Two.torus3 K).range ≤ Subgroup.centralizer {TableBF4Two.rootInv K} := by
  rw [TableBF4Two.torus3, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun i => ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, TableBF4Two.torusCoord_apply, TableBF4Two.rootInv]
  exact (TableBF4Two.commute_rho (TableBF4Two.castSucc_ne_three i) _ _).eq

variable [Finite K]

theorem eq_C3Levi_of_eltHyp (hK : Nat.card K = 2) {D : Subgroup (adjointGroup .F4 K)}
    (hD : EltHyp (nodeElt K) D) : D = C3Levi K := by
  obtain ⟨hDC, hDn, hDq⟩ := hD
  have hcyc := Subgroup.isCyclic_zpowers (nodeElt K)
  have hX := centralizer_nonsplit zpowers_nodeElt_le hcyc (card_zpowers_nodeElt hK)
  rw [centralizer_singleton_eq_zpowers] at hDC hDn
  have hDL : D ≤ C3Levi K := by
    rw [← Subgroup.isPerfect_iff.1 hDq.1, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact commutator_mem_C3Levi_of_mem_centralizer_nonsplit zpowers_nodeElt_le hcyc
      (card_zpowers_nodeElt hK) (hDC h₁) (hDC h₂)
  have hLC : C3Levi K ≤
      Subgroup.centralizer (Subgroup.zpowers (nodeElt K) : Set (adjointGroup .F4 K)) :=
    Subgroup.le_centralizer_iff.1 hX.2.2
  have hN : (D.subgroupOf (C3Levi K)).Normal := ⟨fun d hd g => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    exact hDn _ (hLC g.2) _ hd⟩
  have := isSimpleGroup_C3Levi (K := K)
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hDq
    have hD1 : ∀ x : D, x = 1 := fun x => by
      have hx : (⟨x, hDL x.2⟩ : C3Levi K) ∈ D.subgroupOf (C3Levi K) := x.2
      rw [h, Subgroup.mem_bot] at hx
      have h2 : ((⟨x, hDL x.2⟩ : C3Levi K) : adjointGroup .F4 K) =
          ((1 : C3Levi K) : adjointGroup .F4 K) := congrArg Subtype.val hx
      exact Subtype.ext h2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [hD1 a, hD1 b])
  · refine le_antisymm hDL fun x hx => ?_
    have h1 : (⟨x, hx⟩ : C3Levi K) ∈ D.subgroupOf (C3Levi K) := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1

theorem eq_map_C3Levi_of_eltHyp (hK : Nat.card K = 2)
    (α : adjointGroup .F4 K ≃* adjointGroup .F4 K) {D : Subgroup (adjointGroup .F4 K)}
    (hD : EltHyp (α (nodeElt K)) D) : D = (C3Levi K).map α.toMonoidHom := by
  have h := eltHyp_map α.symm hD
  rw [MulEquiv.symm_apply_apply] at h
  have h2 := eq_C3Levi_of_eltHyp hK h
  ext y
  rw [Subgroup.mem_map_equiv, ← h2, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]

theorem commutator_mem_of_eltHyp (hK : Nat.card K = 2)
    (α : adjointGroup .F4 K ≃* adjointGroup .F4 K) {D : Subgroup (adjointGroup .F4 K)}
    (hD : EltHyp (α (nodeElt K)) D) {c₁ c₂ : adjointGroup .F4 K}
    (h₁ : c₁ ∈ Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K)))
    (h₂ : c₂ ∈ Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K))) :
    c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ D := by
  rw [eq_map_C3Levi_of_eltHyp hK α hD, Subgroup.mem_map_equiv, map_mul, map_mul, map_mul,
    map_inv, map_inv]
  rw [mem_centralizer_map_iff, centralizer_singleton_eq_zpowers] at h₁ h₂
  exact commutator_mem_C3Levi_of_mem_centralizer_nonsplit zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK) h₁ h₂

theorem mem_of_eltHyp_of_sq_eq_one (hK : Nat.card K = 2)
    (α : adjointGroup .F4 K ≃* adjointGroup .F4 K) {D : Subgroup (adjointGroup .F4 K)}
    (hD : EltHyp (α (nodeElt K)) D) {w : adjointGroup .F4 K}
    (hw : w ∈ Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K)))
    (hw2 : w ^ 2 = 1) : w ∈ D := by
  rw [eq_map_C3Levi_of_eltHyp hK α hD, Subgroup.mem_map_equiv]
  rw [mem_centralizer_map_iff, Subgroup.mem_centralizer_singleton_iff] at hw
  exact mem_C3Levi_of_commute_nodeElt hK hw (by rw [← map_pow, hw2, map_one])

theorem exists_not_commute_of_eltHyp (hK : Nat.card K = 2)
    (α : adjointGroup .F4 K ≃* adjointGroup .F4 K) {D : Subgroup (adjointGroup .F4 K)}
    (hD : EltHyp (α (nodeElt K)) D) {t : adjointGroup .F4 K} (ht : t ∈ D) (ht1 : t ≠ 1) :
    ∃ j ∈ D, t * j ≠ j * t := by
  rw [eq_map_C3Levi_of_eltHyp hK α hD] at ht ⊢
  rw [Subgroup.mem_map_equiv] at ht
  by_contra hcon
  push Not at hcon
  have hc : (⟨α.symm t, ht⟩ : C3Levi K) ∈ Subgroup.center (C3Levi K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := hcon (α g) (Subgroup.mem_map_equiv.2 (by simpa using g.2))
    have h2 := congrArg α.symm h1
    simp only [map_mul, MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  rw [center_C3Levi_eq_bot, Subgroup.mem_bot] at hc
  apply ht1
  have h3 : α.symm t = 1 := congrArg Subtype.val hc
  simpa using congrArg α h3

theorem eltConcl_of_node (hK : Nat.card K = 2) (α : adjointGroup .F4 K ≃* adjointGroup .F4 K)
    {f : Fin 3 → Multiplicative (ZMod 3)} {k : Fin 3} (hf : α (nodeElt K) = TableBF4Two.torus3 K f)
    (hk : f k = 1) {D : Subgroup (adjointGroup .F4 K)} (hD : EltHyp (TableBF4Two.torus3 K f) D) :
    EltConcl 3 (TableBF4Two.torus3 K).range D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hf] at hD
  have hEu := range_torus3_le_centralizer_rootInv (K := K)
  have hxE : α (nodeElt K) ∈ (TableBF4Two.torus3 K).range := by
    rw [hf]
    exact ⟨f, rfl⟩
  have hEC : ∀ s ∈ (TableBF4Two.torus3 K).range,
      s ∈ Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K)) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hf, ← map_mul, ← map_mul, mul_comm]
  have hu : TableBF4Two.rootInv K ∈ D := by
    refine mem_of_eltHyp_of_sq_eq_one hK α hD ?_ TableBF4Two.rootInv_sq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hEu hxE)).symm
  have hn : TableBF4Two.reflGen K k ∈
      Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hf]
    have h1 := TableBF4Two.reflGen_conj_torus3 (K := K) k f
    rw [reflHom_eq_self hk] at h1
    calc TableBF4Two.reflGen K k * TableBF4Two.torus3 K f
        = TableBF4Two.reflGen K k * TableBF4Two.torus3 K f * (TableBF4Two.reflGen K k)⁻¹ *
            TableBF4Two.reflGen K k := by group
      _ = TableBF4Two.torus3 K f * TableBF4Two.reflGen K k := by rw [h1]
  have ht : TableBF4Two.torusGen K k ∈ D := by
    have h1 := commutator_mem_of_eltHyp hK α hD hn (hEC _ (torusGen_mem_range k))
    rwa [reflGen_commutator_torusGen] at h1
  refine ⟨Subgroup.zpowers (TableBF4Two.rootInv K), Subgroup.zpowers_le.2 hu,
    Subgroup.zpowers_ne_bot.2 TableBF4Two.rootInv_ne_one, IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime TableBF4Two.rootInv_sq TableBF4Two.rootInv_ne_one,
        pow_one]), fun s hs u hu' => ?_, TableBF4Two.torusGen K k, ht,
    TableBF4Two.torusGen_pow_three k, fun s hs => ?_, ?_,
    exists_not_commute_of_eltHyp hK α hD ht (TableBF4Two.torusGen_ne_one k)⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
    have hsu : Commute s (TableBF4Two.rootInv K) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hEu hs)
    rw [(hsu.zpow_right m).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  · obtain ⟨g, rfl⟩ := hs
    rw [torusGen_eq_torus3, ← map_mul, ← map_mul, mul_comm]
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [← centralizer_singleton_eq_zpowers]
    exact hEu (torusGen_mem_range k)

end CFSG.StandardType.SmallExc.F4Two

end
