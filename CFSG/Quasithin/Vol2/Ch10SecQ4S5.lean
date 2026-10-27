module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S1
public import CFSG.Quasithin.Vol2.Ch10SecEBlock

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_le_normalizer_of_char (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hbot : pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) = ⊥) :
    ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G) := by
  intro C hCS hC hch hHN
  apply hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Subgroup.normalizer (baum T : Set G) ⊔ H ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (normalizer_le_normalizer_of_characteristic hCS hch) hHN
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hCS.trans (Subgroup.le_normalizer.trans le_sup_left)) hN
    (hyp.fsu.sylow.1.to_le (hCS.trans inf_le_left))
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem exists_chi0Block_H (he234 : E2.E23FourStatement) (h1021 : Ch10.Stmt10_2_1)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) (hn3 : ¬ Ch10.Case10_1_1Three T L I)
    (hbot : pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) = ⊥) :
    ∃ K : Subgroup G, IsChi0Block H K ∧ H = K ⊔ T ∧ (¬ IsAltType K 3 → K ∈ cComp H) := by
  have hmp := SecB.minParabolic_of_isHStar h331 hyp hH
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hchar : CharTwo H := charTwo_of_inH hyp.fsu.qtke.2.1 S (hS ▸ hH.1)
  obtain ⟨-, -, hW⟩ := conjClosure_isTwoReducedIn_of_charTwo hmp.isSylow hchar
    (le_refl (quasithinOmegaOneCenter T))
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : SQTKGroup ↥H := InternalSec.sqtkGroup_of_localSQTK hK hH.1.2
  have hJW := (SecE.stmt10_2_2_two h1021 h331 hyp hH hZH hn3).2.1
  exact he234 G H T _ (VZ T H) hmp hSQ hchar hW hJW (not_le_normalizer_of_char hyp hbot)

theorem isSolvable_of_subnormal_sup {H K T : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hsol : Group.IsSolvable ↥K) (hT2 : IsPGroup 2 T)
    (heq : H = K ⊔ T) : Group.IsSolvable ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := heq ▸ le_sup_right
  have hsol' : Group.IsSolvable ↥(K.subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  set R := CFSG.solvableRadical ↥H with hR
  have hKR : K.subgroupOf H ≤ R := by
    rw [hR, A3.solvableRadical_eq_solvRad_top]
    exact le_solvRad_of_subnormal (A3.subnormal_top_iff.mpr hsub) hsol'
  have htop : R ⊔ T.subgroupOf H = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup ↥H) = (K ⊔ T).subgroupOf H := by rw [← heq, Subgroup.subgroupOf_self]
      _ = K.subgroupOf H ⊔ T.subgroupOf H := Subgroup.subgroupOf_sup hKH hTH
      _ ≤ R ⊔ T.subgroupOf H := sup_le_sup_right hKR _
  have hT2' : IsPGroup 2 ↥(T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp (T.subgroupOf H).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hx : x ∈ ((R ⊔ T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by rw [htop]; trivial
    rw [Subgroup.normal_mul] at hx
    obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := (A3.instNormalSolvableRadical ↥H).conj_mem r hr s⁻¹
    simpa [mul_assoc] using h1
  have hQ : IsPGroup 2 (↥H ⧸ R) := hT2'.of_surjective _ hsurj
  have : Group.IsNilpotent (↥H ⧸ R) := hQ.isNilpotent
  have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_block_H (he23 : E2.E23Statement) (he234 : E2.E23FourStatement)
    (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hn3 : ¬ Ch10.Case10_1_1Three T L I)
    (hsyl : ¬ IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T))
    (hbot : pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) = ⊥) :
    ∃ K ∈ cComp H, IsShort2 K ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 5) ∧
      H = K ⊔ T := by
  obtain ⟨K, hKb, hKT, hKC⟩ := exists_chi0Block_H he234 h1021 h331 hyp hH hZH hn3 hbot
  have hn3' : ¬ IsAltType K 3 := by
    intro h3
    have hsol := isSolvable_of_subnormal_sup hKb.1.2.1 hKb.1.2.2
      (SecE.isSolvable_of_isAltType_three h3) hyp.fsu.sylow.1 hKT
    obtain ⟨hel, hc⟩ := C10E4.e23Concl_H he23 h1021 h331 hyp hH hZH hn3
    obtain ⟨I', hcard, hJ, -, -, hA5⟩ := C10E4.isA5Module_of_not_isSylowTwoOf hc hsyl
    obtain ⟨K₀, hK₀⟩ := Finset.card_pos.mp (by omega : 0 < I'.card)
    obtain ⟨θ, -, -⟩ := hA5 K₀ hK₀
    have hHN : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
    have hsolA := B2F.isSolvable_autI hel hHN hsol
    have hK₀H : K₀ ≤ autI hel H :=
      (le_iSup₂_of_le (f := fun L (_ : L ∈ I') => L) K₀ hK₀ le_rfl).trans
        (hJ.symm.le.trans (autI_mono hel (thompsonJ_le_self H)))
    apply Equiv.Perm.not_isSolvable_fin_5
    have : Group.IsSolvable ↥K₀ := by
      have := subgroup_solvable_of_solvable (K₀.subgroupOf (autI hel H))
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hK₀H).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hK₀H).surjective
    exact Group.isSolvable_of_surjective (f := θ.toMonoidHom) θ.surjective
  refine ⟨K, hKC hn3', hKb.1.1, ?_, hKT⟩
  rcases hKb.2 with h | h | h
  · exact Or.inl h
  · exact absurd h hn3'
  · exact Or.inr h

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
