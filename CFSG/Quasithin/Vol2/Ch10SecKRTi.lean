module

public import CFSG.Quasithin.Background.A3Structure36BSL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem eq_top_of_not_isSolvable {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hY : IsSL2 p (Y ⧸ CFSG.oddCore Y)) {N : Subgroup Y}
    (hN : N.Normal) (hns : ¬ Group.IsSolvable ↥N) : N = ⊤ := by
  obtain ⟨e⟩ := hY
  set O := CFSG.oddCore Y with hOdef
  have hOs : Group.IsSolvable ↥O := A312.oddCore_isSolvable Y
  set φ : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    e.toMonoidHom.comp (QuotientGroup.mk' O) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  have hφk : ∀ y, φ y = 1 ↔ y ∈ O := fun y => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hMn : (N.map φ).Normal := hN.map φ hφs
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (A36B.isQuasisimple_sl2 hp hp5) hMn with
    h | h
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp O.subtype) := by
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
      have hy : φ y ∈ N.map φ := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hny⟩ := hy
      have hO : n⁻¹ * y ∈ O := (hφk _).mp (by rw [map_mul, map_inv, hny, inv_mul_cancel])
      refine ⟨⟨n⁻¹ * y, hO⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have := hN.conj_mem n hn y⁻¹
      simpa [mul_assoc] using this
    have hYN : Group.IsSolvable (Y ⧸ N) := Group.isSolvable_of_surjective hsurj
    by_contra hne
    have : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsPerfect (Y ⧸ N) :=
      Group.IsPerfect.ofSurjective (G := Y) (G' := Y ⧸ N) (f := QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isSolvable (Y ⧸ N) hYN
  ·
    exfalso
    apply hns
    have hab : Group.IsSolvable ↥(N.map φ) := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (h a.2) b).symm
    have hOs' : Group.IsSolvable ↥(O.comap N.subtype) :=
      Group.isSolvable_of_isSolvable_injective (f := N.subtype.subgroupComap O)
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext h))
    refine Group.isSolvable_of_ker_le_range (O.comap N.subtype).subtype (φ.subgroupMap N) ?_
    intro n hn
    have h1 : φ (n : Y) = 1 := by simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    exact ⟨⟨n, (hφk _).mp h1⟩, rfl⟩

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

omit [Finite G] in
theorem le_sup_pCoreOf_of_le {X : Subgroup G} (hJM : J ≤ M₁)
    (h : modO2Image M₁ J ≤ modO2Image M₁ X) : J ≤ X ⊔ pCoreOf 2 M₁ := by
  intro j hj
  have hjM : j ∈ M₁ := hJM hj
  obtain ⟨k, hk, hkj⟩ := h ⟨⟨j, hjM⟩, hj, rfl⟩
  have hq : k⁻¹ * ⟨j, hjM⟩ ∈ CFSG.pCore 2 ↥M₁ := QuotientGroup.eq.mp hkj
  have hqG : ((k⁻¹ * ⟨j, hjM⟩ : ↥M₁) : G) ∈ pCoreOf 2 M₁ := by
    exact ⟨_, hq, rfl⟩
  have hj' : j = (k : G) * ((k⁻¹ * ⟨j, hjM⟩ : ↥M₁) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hj']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show (k : G) ∈ X from hk))
    (Subgroup.mem_sup_right hqG)

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
