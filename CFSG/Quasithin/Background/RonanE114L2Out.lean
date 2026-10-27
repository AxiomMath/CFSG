module

public import CFSG.Quasithin.Vol2.Ch11SecU1Out2

public section

namespace CFSG.Quasithin.RonanE114.L2

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Subgroup
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem psl2_fix_outer_involution_three (hodd : IsOddPrimePower (Nat.card F))
    (h4 : Nat.card F % 4 = 3) (h3 : 3 < Nat.card F) {t : PGL2 F} (ht : t * t = 1)
    (ht1 : t ≠ 1)
    (htr : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    Nonempty (↥(MonoidHom.eqLocus (pglAction F t).toMonoidHom (MonoidHom.id (PSL2 F))) ≃*
      DihedralGroup ((Nat.card F - 1) / 2)) := by
  classical
  set L := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hLdef
  have hL2 : L.index = 2 := index_psl2Range hodd
  have : L.Normal := Subgroup.normal_of_index_eq_two hL2
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, hwU, hww, hinv, hCs, hUr⟩ :=
    pgl2_split_torus_centralizer_data F hFodd
  have hUL : ¬ U ≤ L := hUr hFodd
  set m := (Nat.card F - 1) / 2 with hm
  have hm2 : Nat.card F - 1 = 2 * m := by omega
  have hmodd : Odd m := ⟨(Nat.card F - 3) / 4, by omega⟩
  have hsL : s ∉ L := by
    intro hsL
    apply hUL
    intro x hx
    have hxU : (⟨x, hx⟩ : U) ^ (2 * m) = 1 := by
      rw [← hm2, ← hUcard]
      exact pow_card_eq_one'
    have hy : ((⟨x, hx⟩ : U) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hxU]
    have hsU' : (⟨s, hsU⟩ : U) ^ 2 = 1 := Subtype.ext (by simp [pow_two, hss])
    have hsU1 : (⟨s, hsU⟩ : U) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
    have hxm : x ^ m ∈ L := by
      rcases eq_one_or_eq_of_sq_eq_one_cyclic hsU' hsU1 hy with h | h
      · have := congrArg Subtype.val h
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        rw [this]
        exact one_mem _
      · have := congrArg Subtype.val h
        simp only [SubgroupClass.coe_pow] at this
        rw [this]
        exact hsL
    obtain ⟨k, hk⟩ := hmodd
    have hx' : x = ((x ^ k) ^ 2)⁻¹ * x ^ m := by
      rw [hk, ← pow_mul, pow_succ, mul_comm k 2, inv_mul_cancel_left]
    rw [hx']
    exact mul_mem (inv_mem (sq_mem_psl2Range _)) hxm
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd h3
  obtain ⟨g, hg⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate F hodd h3
    ⟨ht1, by rw [pow_two]; exact ht⟩ ⟨hs1, by rw [pow_two]; exact hss⟩
    (by rw [hJ]; exact htr) (by rw [hJ]; exact hsL))
  set D := U ⊔ zpowers w with hDdef
  have hsD : s ∈ D := le_sup_left (b := zpowers w) hsU
  have hwD : w ∈ D := le_sup_right (a := U) (mem_zpowers w)
  have hDcard : Nat.card D = 2 * (Nat.card F - 1) := by
    have : IsCyclic U := hUc
    obtain ⟨d⟩ := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup U w hwU hww hinv
    rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card, hUcard]
  have hrel : ∀ H : Subgroup (PGL2 F), ¬ H ≤ L → (L ⊓ H).relIndex H = 2 := by
    intro H hH
    rw [inf_relIndex_right]
    have hd : L.relIndex H ∣ L.index := relIndex_dvd_index_of_normal L H
    rw [hL2] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (relIndex_eq_one.mp h) hH
    · exact h
  have hU0card : Nat.card (L ⊓ U : Subgroup (PGL2 F)) = m := by
    have := card_mul_relIndex (A := L ⊓ U) (B := U) inf_le_right
    rw [hrel U hUL, hUcard] at this
    exact Nat.eq_of_mul_eq_mul_right two_pos (this.trans (hm2.trans (mul_comm 2 m)))
  have hDL : ¬ D ≤ L := fun h => hsL (h hsD)
  have hD0card : Nat.card (L ⊓ D : Subgroup (PGL2 F)) = Nat.card F - 1 := by
    have := card_mul_relIndex (A := L ⊓ D) (B := D) inf_le_right
    rw [hrel D hDL, hDcard, mul_comm 2] at this
    exact Nat.eq_of_mul_eq_mul_right two_pos this
  have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    have : IsCyclic U := hUc
    intro x hx y hy
    have := (IsCyclic.isMulCommutative (α := ↥U)).is_comm.comm (⟨x, hx⟩ : U) ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨w', hw'L, hw'U, hw'w', hw'inv, hw'D⟩ : ∃ w' : PGL2 F, w' ∈ L ∧ w' ∉ U ∧
      w' * w' = 1 ∧ (∀ x ∈ U, w' * x * w'⁻¹ = x⁻¹) ∧ w' ∈ D := by
    by_cases hwL : w ∈ L
    · exact ⟨w, hwL, hwU, hww, hinv, hwD⟩
    · refine ⟨w * s, ?_, ?_, ?_, ?_, mul_mem hwD hsD⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hL2]
        exact iff_of_false hwL hsL
      · intro h
        apply hwU
        have := mul_mem h (inv_mem hsU)
        rwa [mul_inv_cancel_right] at this
      · have hw1 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
        have h1 := hinv s hsU
        rw [hw1] at h1
        have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
        calc w * s * (w * s) = (w * s * w) * s := by group
          _ = 1 := by rw [h1, hs', hss]
      · intro x hx
        have h1 := hinv x hx
        calc w * s * x * (w * s)⁻¹ = w * (s * x * s⁻¹) * w⁻¹ := by group
          _ = w * x * w⁻¹ := by rw [hcommU s hsU x hx, mul_inv_cancel_right]
          _ = x⁻¹ := h1
  set U₀ : Subgroup (PGL2 F) := L ⊓ U with hU₀
  have : IsCyclic U₀ := by
    have : IsCyclic U := hUc
    exact Subgroup.isCyclic_of_le inf_le_right
  have hw'U₀ : w' ∉ U₀ := fun h => hw'U h.2
  have hw'inv₀ : ∀ x ∈ U₀, w' * x * w'⁻¹ = x⁻¹ := fun x hx => hw'inv x hx.2
  have hd₀ := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup U₀ w' hw'U₀ hw'w' hw'inv₀
  rw [hU0card] at hd₀
  obtain ⟨d₀⟩ := hd₀
  have hle : U₀ ⊔ zpowers w' ≤ L ⊓ D := by
    apply sup_le
    · exact inf_le_inf_left L le_sup_left
    · rw [zpowers_le]
      exact ⟨hw'L, hw'D⟩
  have hcard0 : Nat.card (U₀ ⊔ zpowers w' : Subgroup (PGL2 F)) = Nat.card F - 1 := by
    rw [Nat.card_congr d₀.toEquiv, DihedralGroup.nat_card, hm2]
  have heq : U₀ ⊔ zpowers w' = L ⊓ D :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hD0card, hcard0])
  set Fix := fun u : PGL2 F => MonoidHom.eqLocus (pglAction F u).toMonoidHom
    (MonoidHom.id (PSL2 F)) with hFix
  have hmemFix : ∀ (u : PGL2 F) (x : PSL2 F), x ∈ Fix u ↔
      Matrix.ProjectiveSpecialLinearGroup.toPGL x ∈ centralizer {u} := by
    intro u x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change pglAction F u x = x ↔ _
    rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.eq_iff, toPGL_pglAction,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hmapFix : (Fix s).map Matrix.ProjectiveSpecialLinearGroup.toPGL = L ⊓ D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      rw [← hCs]
      exact (hmemFix s x).mp hx
    · rintro ⟨⟨x, rfl⟩, hy⟩
      refine ⟨x, (hmemFix s x).mpr ?_, rfl⟩
      rw [hCs]
      exact hy
  have e₁ : ↥(Fix s) ≃* ↥(L ⊓ D) :=
    ((Fix s).equivMapOfInjective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmapFix)
  have hmapT : (Fix t).map (pglAction F g).toMonoidHom = Fix s := by
    ext y
    rw [Subgroup.mem_map_equiv]
    show pglAction F t ((pglAction F g).symm y) = (pglAction F g).symm y ↔ pglAction F s y = y
    rw [← hg, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
    constructor
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
    · intro h
      have := congrArg (pglAction F g).symm h
      rwa [MulEquiv.symm_apply_apply] at this
  have e₂ : ↥(Fix t) ≃* ↥(Fix s) :=
    ((pglAction F g).subgroupMap (Fix t)).trans (MulEquiv.subgroupCongr hmapT)
  exact ⟨(e₂.trans e₁).trans ((MulEquiv.subgroupCongr heq.symm).trans d₀)⟩

end CFSG.Quasithin.RonanE114.L2

namespace CFSG.Quasithin.RonanE114.L2

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Quasithin.Vol2.Ch11.SecU1

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem oddTorus_of_fix_dihedral [Finite G] (hLn : L.Normal) {e : L ≃* PSL2 K} {b : G} {m : ℕ}
    [NeZero m] (hm : Odd m) (hm3 : 3 ≤ m) {Fix : Subgroup (PSL2 K)}
    (heq : L ⊓ Subgroup.centralizer {b} = Fix.map (embL e)) (d : ↥Fix ≃* DihedralGroup m) :
    OddTorus L b :=
  oddTorus_of_dihedral hLn hm hm3 ((MulEquiv.subgroupCongr heq).trans
    ((Fix.equivMapOfInjective _ (embL_injective e)).symm.trans d))

theorem oddTorus_of_adapted_three [Finite G] (hLn : L.Normal) {e : L ≃* PSL2 K}
    {ι : G →* PGammaL2 K} (h : Adapted e ι) (hK : IsOddPrimePower (Nat.card K))
    (h4 : Nat.card K % 4 = 3) (h7 : 7 ≤ Nat.card K) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) (hr : (ι b).right = 1) : OddTorus L b := by
  set t := (ι b).left with ht
  have hb : ι b = SemidirectProduct.inl t := by
    rw [← SemidirectProduct.inl_left_mul_inr_right (ι b), hr, map_one, mul_one]
  have htt : t * t = 1 := by
    have hbb : b * b = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one b
      rwa [hb2] at this
    have h1 : ι (b * b) = 1 := by rw [hbb, map_one]
    rw [map_mul, hb, ← map_mul] at h1
    exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
  have ht1 : t ≠ 1 := fun h1 => by
    have : ι b = ι 1 := by rw [hb, h1, map_one, map_one]
    rw [h.1 this, orderOf_one] at hb2
    omega
  have htr : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    rintro ⟨c, hc⟩
    apply hbL
    rw [mem_iff_of_adapted h, hb, ← hc]
    exact ⟨c, rfl⟩
  obtain ⟨d⟩ := psl2_fix_outer_involution_three hK h4 (by omega) htt ht1 htr
  set m := (Nat.card K - 1) / 2 with hm
  have hm3 : 3 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  have hmodd : Odd m := ⟨(Nat.card K - 3) / 4, by omega⟩
  have heq := inf_centralizer_eq_map_fix h hb
  exact oddTorus_of_fix_dihedral hLn hmodd hm3 heq d

end CFSG.Quasithin.RonanE114.L2
