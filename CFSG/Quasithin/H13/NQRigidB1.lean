module

public import CFSG.Quasithin.H13.NQRigidAsmPairData
public import CFSG.Quasithin.H13.NQTermComponentOrbits

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem solvable_quotient_escaping_component_normalization_and_action (N : Subgroup H) [N.Normal]
    (hN : Group.IsSolvable N) {X : Subgroup H} (hX : ∀ D : Subgroup X, D.Normal → D.index ≠ 2)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ N) ≤ 2) {K : Subgroup H}
    (hK : CFSG.IsCComponent K) (hJ : CFSG.IsComponent (K.map (QuotientGroup.mk' N))) :
    X ≤ normalizer (K : Set H) ∧
      (¬ K.map (QuotientGroup.mk' N) ≤
          normalizer ((X.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) →
        ⁅K, X⁆ = K) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set J := K.map π with hJdef
  set Y := X.map π with hYdef
  have hY : ∀ D : Subgroup Y, D.Normal → D.index ≠ 2 := by
    intro D hD h2
    have hf : Function.Surjective (π.subgroupMap X) := π.subgroupMap_surjective X
    have h1 : (D.comap (π.subgroupMap X)).index = D.index :=
      Subgroup.index_comap_of_surjective (H := D) hf
    exact hX _ (hD.comap _) (h1.trans h2)
  have hYJ : Y ≤ normalizer (J : Set (H ⧸ N)) :=
    (NQTerm.odd_rank_two_component_orbits_and_normalization hrk).2 Y hY J hJ
  have hXK : X ≤ normalizer (K : Set H) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    have hc : CFSG.IsCComponent (K.map (MulAut.conj x).toMonoidHom) := by
      have h1 := isCComponent_conjugate hK x⁻¹
      rwa [CFSG.conjugate, inv_inv] at h1
    apply eq_of_map_eq_of_isCComponent hN hc hK
    have hcomp : π.comp (MulAut.conj x).toMonoidHom = (MulAut.conj (π x)).toMonoidHom.comp π := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
    rw [map_map, hcomp, ← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hYJ ⟨x, hx, rfl⟩)
  refine ⟨hXK, fun hJY => ?_⟩
  have hle : ⁅J, Y⁆ ≤ J := by
    rw [commutator_le]
    intro j hj y hy
    rw [commutatorElement_def]
    have h1 : y * j⁻¹ * y⁻¹ ∈ J := (mem_normalizer_iff.mp (hYJ hy) j⁻¹).mp (J.inv_mem hj)
    rw [show j * y * j⁻¹ * y⁻¹ = j * (y * j⁻¹ * y⁻¹) by group]
    exact J.mul_mem hj h1
  have hJY' : ⁅J, Y⁆ = J := by
    set N' := ⁅J, Y⁆.subgroupOf J with hN'
    have hN'n : N'.Normal := ⟨fun n hn g => mem_subgroupOf.mpr
      (SteinbergCC.conj_mem_commutator_left g.2 (mem_subgroupOf.mp hn))⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ.1 hN'n with htop | hcen
    · apply le_antisymm hle
      intro j hj
      have h1 : (⟨j, hj⟩ : J) ∈ N' := htop ▸ mem_top _
      exact h1
    · exfalso
      apply hJY
      have h1 : ⁅⁅J, Y⁆, J⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro c hc
        rw [mem_centralizer_iff]
        intro j hj
        have h2 : (⟨c, hle hc⟩ : J) ∈ center J := hcen (mem_subgroupOf.mpr hc)
        exact congrArg Subtype.val (mem_center_iff.mp h2 ⟨j, hj⟩)
      have h2 := CFSG.LocalCores.perfect_double_commutator hJ.1.1 h1
      rw [commutator_eq_bot_iff_le_centralizer] at h2
      exact h2.trans (centralizer_le_normalizer _)
  have hKX : ⁅K, X⁆ ≤ K := by
    rw [commutator_le]
    intro k hk x hx
    rw [commutatorElement_def]
    have h1 : x * k⁻¹ * x⁻¹ ∈ K := (mem_normalizer_iff.mp (hXK hx) k⁻¹).mp (K.inv_mem hk)
    rw [show k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) by group]
    exact K.mul_mem hk h1
  set D := ⁅K, X⁆.subgroupOf K with hDdef
  have hDn : D.Normal := ⟨fun n hn g => mem_subgroupOf.mpr
    (SteinbergCC.conj_mem_commutator_left g.2 (mem_subgroupOf.mp hn))⟩
  have himage : ⁅K, X⁆.map π = K.map π := by
    rw [map_commutator]
    exact hJY'
  set f : N.subgroupOf K →* N :=
    { toFun := fun x => ⟨((x : K) : H), mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hf
  have hfinj : Function.Injective f := fun a b hab => by
    have h1 := congrArg (fun z : N => (z : H)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hNKs : Group.IsSolvable (N.subgroupOf K) := Group.isSolvable_of_isSolvable_injective hfinj
  set ψ : N.subgroupOf K →* K ⧸ D := (QuotientGroup.mk' D).comp (N.subgroupOf K).subtype with hψ
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective D z
    have hk : π (k : H) ∈ ⁅K, X⁆.map π := by
      rw [himage]
      exact ⟨k, k.2, rfl⟩
    obtain ⟨c, hc, hck⟩ := hk
    have hcK : c ∈ K := hKX hc
    have hcN : c⁻¹ * (k : H) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hck
    have hmem : (⟨c, hcK⟩ : K)⁻¹ * k ∈ N.subgroupOf K := mem_subgroupOf.mpr hcN
    refine ⟨⟨_, hmem⟩, ?_⟩
    change QuotientGroup.mk' D ((⟨c, hcK⟩ : K)⁻¹ * k) = QuotientGroup.mk' D k
    have hcD : (⟨c, hcK⟩ : K) ∈ D :=
      mem_subgroupOf.mpr (show ((⟨c, hcK⟩ : K) : H) ∈ ⁅K, X⁆ from hc)
    rw [map_mul, map_inv, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hcD, inv_one,
      one_mul]
  have hQs : Group.IsSolvable (K ⧸ D) := Group.isSolvable_of_surjective hψs
  have hKperf : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK.2.1
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (K ⧸ D)).mp hQs
  rw [Group.IsPerfect.derivedSeries_eq_top] at hn
  apply le_antisymm hKX
  intro k hk
  have h1 : ((⟨k, hk⟩ : K) : K ⧸ D) ∈ (⊤ : Subgroup (K ⧸ D)) := mem_top _
  rw [hn, mem_bot] at h1
  exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem stmtEscapingComponentAction_holds : StmtEscapingComponentAction :=
  fun _ _ _ N _ hN _ hX hrk _ hK hJ =>
    solvable_quotient_escaping_component_normalization_and_action N hN hX hrk hK hJ

end CFSG.Quasithin.H13.NQRigid
