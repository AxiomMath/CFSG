module

public import CFSG.Quasithin.Vol2.Ch10SecA1012Six
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch10SecA1011C
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative commutatorElement

theorem isQuasisimple_of_simple {X : Type} [Group X] [hs : IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hcen : Subgroup.center X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hc : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).isSimpleGroup

theorem exists_ne_of_mulEquiv_slThree {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := Vol2Native.A312L.Seven.slThree_nonabelian
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

section Residual

variable {G' : Type} [Group G'] [Finite G'] {Y : Subgroup G'}

theorem not_three_dvd_card_of_twoResidual
    (h5 : Nonempty (↥(twoResidual Y) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(twoResidual Y) ≃* Multiplicative (ZMod 5 × ZMod 5))) :
    ¬ 3 ∣ Nat.card ↥Y := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy' : orderOf (y : G') = 3 := (Subgroup.orderOf_coe y).trans hy
  have hyR : (y : G') ∈ twoResidual Y := by
    rw [mem_twoResidual_iff]
    intro N _ _ h2
    obtain ⟨k, hk⟩ := h2 y y.2
    have hmod : (2 ^ k * 2 ^ k) % 3 = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    have hyy : ((y : G') ^ 2 ^ k) ^ 2 ^ k = (y : G') := by
      rw [← pow_mul, ← pow_mod_orderOf, hy', hmod, pow_one]
    rw [← hyy]
    exact N.pow_mem hk _
  have hdvd : orderOf (⟨y, hyR⟩ : ↥(twoResidual Y)) ∣ Nat.card ↥(twoResidual Y) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hy'] at hdvd
  rcases h5 with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv] at hdvd
    simp [Nat.card_eq_fintype_card] at hdvd
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv] at hdvd
    simp [Nat.card_eq_fintype_card] at hdvd

theorem isSolvable_of_twoResidual
    (h5 : Nonempty (↥(twoResidual Y) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(twoResidual Y) ≃* Multiplicative (ZMod 5 × ZMod 5))) :
    Group.IsSolvable ↥Y := by
  set N := twoResidual Y with hN
  have hNY : N ≤ Y := twoResidual_le Y
  have hn : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr (le_normalizer_twoResidual Y)
  have hcomm : ∀ a b : ↥N, a * b = b * a := by
    rcases h5 with h | h
    · obtain ⟨e⟩ := h
      intro a b
      exact e.injective (by rw [map_mul, map_mul, mul_comm])
    · obtain ⟨e⟩ := h
      intro a b
      exact e.injective (by rw [map_mul, map_mul, mul_comm])
  have hsN : Group.IsSolvable ↥(N.subgroupOf Y) := Group.isSolvable_of_comm fun a b => by
    apply (Subgroup.subgroupOfEquivOfLe hNY).injective
    rw [map_mul, map_mul]
    exact hcomm _ _
  have hsQ : Group.IsSolvable (↥Y ⧸ N.subgroupOf Y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (↥Y ⧸ N.subgroupOf Y) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient Y y y.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
    have := hp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf Y).subtype
    (QuotientGroup.mk' (N.subgroupOf Y)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Residual

section Internal

variable {G : Type} [Group G]

theorem autOn_le_normalizer_autOn {V H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    autOn H V ≤ Subgroup.normalizer (autOn K V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hHK

variable [Finite G]

theorem eq_bot_of_le_centralizer_autOn {V M L₀ : Subgroup G}
    (hM2 : pCoreOf 2 (autOn M V) = ⊥) (hML : M ≤ Subgroup.normalizer (L₀ : Set G))
    (Q : Subgroup (MulAut ↥V))
    (hQY : Q ≤ autOn M V ⊓ Subgroup.centralizer (autOn L₀ V : Set (MulAut ↥V)))
    (hQn : (Q.subgroupOf (autOn M V ⊓
      Subgroup.centralizer (autOn L₀ V : Set (MulAut ↥V)))).Normal)
    (hQ2 : IsPGroup 2 ↥Q) : Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYn : autOn M V ≤ Subgroup.normalizer
      ((autOn M V ⊓ Subgroup.centralizer (autOn L₀ V : Set (MulAut ↥V)) :
        Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    intro x hx
    have h1 : x ∈ Subgroup.normalizer (autOn M V : Set (MulAut ↥V)) := Subgroup.le_normalizer hx
    have h2 : x ∈ Subgroup.normalizer
        (Subgroup.centralizer (autOn L₀ V : Set (MulAut ↥V)) : Set (MulAut ↥V)) :=
      le_normalizer_centralizer (autOn_le_normalizer_autOn (V := V) hML) hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hQ1 := CFSG.LieType.BorelTits.le_pCoreOf 2 hQY hQn hQ2
  have hQ3 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    (fun x hx => normalizer_le_normalizer_pCoreOf _ (hYn hx))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (autOn M V ⊓ Subgroup.centralizer (autOn L₀ V : Set (MulAut ↥V))))
  rw [hM2] at hQ3
  exact le_bot_iff.mp (hQ1.trans hQ3)

omit [Finite G] in
theorem isSubnormal_sup {T L K : Subgroup G} (hK : K ≤ fsuL0 T L)
    (hKn : (K.subgroupOf (fsuL0 T L)).Normal) : IsSubnormal K (fsuL0 T L ⊔ T) := by
  have h1 : fsuL0 T L ≤ fsuL0 T L ⊔ T := le_sup_left
  have h2 : ((fsuL0 T L).subgroupOf (fsuL0 T L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h1).mpr
      (sup_le Subgroup.le_normalizer (le_fsuM T L))
  exact IsSubnormal.step hK hKn (IsSubnormal.step h1 h2 (IsSubnormal.refl _))

omit [Finite G] in
theorem subgroupOf_sup_sup {V A B C : Subgroup G} (hA : A ≤ V) (hB : B ≤ V) (hC : C ≤ V) :
    (A ⊔ B ⊔ C).subgroupOf V = A.subgroupOf V ⊔ B.subgroupOf V ⊔ C.subgroupOf V := by
  rw [Subgroup.subgroupOf_sup (sup_le hA hB) hC, Subgroup.subgroupOf_sup hA hB]

end Internal

section CaseSix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_isFFModule_of_case_six (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (hyp : Ch10.Hyp10 G T L I) [IsMulCommutative ↥(fsuVM T L I)]
    (he : Nonempty (↥(autOn L (fsuVM T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hsum : DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
      ((fsuUL T L I).subgroupOf (fsuVM T L I)) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (h5 : Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5)) ∨
        Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5 × ZMod 5))) :
    ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  have hloc := hyp.fsu.maximal.1
  have hel := isElemAbelian_fsuVM hyp
  have hV : ∀ v : ↥(fsuVM T L I), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hel.2 _ v.2)
  have hL0V := fsuL0_le_normalizer_fsuVM T L I
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) := (le_fsuL0 T L).trans hL0V
  have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (conjugate_le_fsuL0 ht).trans hL0V
  have htV : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) := le_normalizer_fsuVM T L I ht
  obtain ⟨e₁⟩ := he
  have hK₂ : autOn (CFSG.conjugate L t) (fsuVM T L I) = (autOn L (fsuVM T L I)).map
      (MulAut.conj (conjAct (fsuVM T L I) ⟨t, htV⟩)⁻¹).toMonoidHom :=
    autOn_conjugate htV
  set σ : MulAut ↥(fsuVM T L I) := (conjAct (fsuVM T L I) ⟨t, htV⟩)⁻¹ with hσ
  have e₂ : ↥(autOn (CFSG.conjugate L t) (fsuVM T L I)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((MulEquiv.subgroupCongr hK₂).trans (conjEquivMap _ σ).symm).trans e₁
  have hc₁ : commV (autOn L (fsuVM T L I)) = (fsuUL T L I).subgroupOf (fsuVM T L I) :=
    commV_autOn_eq hLV
  have hsum₁ : DirectSumOfCopies (autOn L (fsuVM T L I)) (commV (autOn L (fsuVM T L I))) ⊥
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4 := by
    rw [hc₁]
    exact hsum
  have hc₂ : commV (autOn (CFSG.conjugate L t) (fsuVM T L I)) =
      (commV (autOn L (fsuVM T L I))).map σ.toMonoidHom := by
    rw [hK₂, commV_map_conj]
  have hsum₂ : DirectSumOfCopies (autOn (CFSG.conjugate L t) (fsuVM T L I))
      (commV (autOn (CFSG.conjugate L t) (fsuVM T L I))) ⊥
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4 := by
    rw [hc₂, hK₂]
    exact directSumOfCopies_map_conj hsum₁ σ
  have := Vol2Native.A312L.Seven.slThree_isSimple
  have hs₁ : IsSimpleGroup ↥(autOn L (fsuVM T L I)) := e₁.isSimpleGroup
  have hs₂ : IsSimpleGroup ↥(autOn (CFSG.conjugate L t) (fsuVM T L I)) := e₂.isSimpleGroup
  have hK₁X : IsComponentOf (autOn L (fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) :=
    ⟨A4.autOn_mono ((le_fsuL0 T L).trans le_sup_left),
      A4.autOn_subnormal (isSubnormal_sup (le_fsuL0 T L) (normal_fsuL0 hloc)),
      isQuasisimple_of_simple (exists_ne_of_mulEquiv_slThree e₁)⟩
  have hK₂X : IsComponentOf (autOn (CFSG.conjugate L t) (fsuVM T L I))
      (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) :=
    ⟨A4.autOn_mono ((conjugate_le_fsuL0 ht).trans le_sup_left),
      A4.autOn_subnormal (isSubnormal_sup (conjugate_le_fsuL0 ht)
        (normal_fsuL0_conjugate hloc ht)),
      isQuasisimple_of_simple (exists_ne_of_mulEquiv_slThree e₂)⟩
  have hK₁₂ : autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I) =
      autOn (fsuL0 T L) (fsuVM T L I) := by
    rw [← autOn_sup_eq hLV hLtV, ← fsuL0_eq_sup h37 h38 hyp ht htn]
  have hC : fixV (autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I)) =
      (fsuCVM T L I).subgroupOf (fsuVM T L I) := by
    rw [hK₁₂]
    ext v
    rw [mem_fixV_autOn hL0V, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hc₂' : commV (autOn (CFSG.conjugate L t) (fsuVM T L I)) =
      (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) := by
    rw [hc₂, hc₁, subgroupOf_conjugate htV]
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  obtain ⟨hsupV, hinfV, -⟩ := ha t ht htn
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
    have h := conjugate_mono hUV t
    rwa [conjugate_fsuVM (le_fsuM T L ht)] at h
  have hCV : fsuCVM T L I ≤ fsuVM T L I := inf_le_left
  have hsup' : (fsuUL T L I).subgroupOf (fsuVM T L I) ⊔
      (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) ⊔
        (fsuCVM T L I).subgroupOf (fsuVM T L I) = ⊤ := by
    rw [← subgroupOf_sup_sup hUV hUtV hCV, hsupV, Subgroup.subgroupOf_self]
  have hinf' : ((fsuUL T L I).subgroupOf (fsuVM T L I) ⊔
      (fsuCVM T L I).subgroupOf (fsuVM T L I)) ⊓
        ((CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) ⊔
          (fsuCVM T L I).subgroupOf (fsuVM T L I)) =
      (fsuCVM T L I).subgroupOf (fsuVM T L I) := by
    rw [← Subgroup.subgroupOf_sup hUV hCV, ← Subgroup.subgroupOf_sup hUtV hCV]
    ext v
    simpa [Subgroup.mem_inf, Subgroup.mem_subgroupOf] using SetLike.ext_iff.mp hinfV (v : G)
  have hfix : ∀ {K : Subgroup (MulAut ↥(fsuVM T L I))},
      DirectSumOfCopies K (commV K) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 →
        commV K ⊓ fixV K = ⊥ := by
    intro K hs
    obtain ⟨I', π', -, -, hW, hreal⟩ := hs
    have h := (B5.homogeneous_of_nat_copies (by norm_num) hV I' hreal).1
    rw [← hW, bot_sup_eq, inf_comm]
    exact h
  have hfix₁ := hfix hsum₁
  have hfix₂ := hfix hsum₂
  have hCK₁ : fixV (autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I)) ≤
      fixV (autOn L (fsuVM T L I)) := B1.fixV_le_fixV le_sup_left
  have hCK₂ : fixV (autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I)) ≤
      fixV (autOn (CFSG.conjugate L t) (fsuVM T L I)) := B1.fixV_le_fixV le_sup_right
  rw [← hc₁, ← hc₂', ← hC] at hsup' hinf'
  set W₁ := commV (autOn L (fsuVM T L I))
  set W₂ := commV (autOn (CFSG.conjugate L t) (fsuVM T L I))
  set C := fixV (autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I))
  have hW₁C : W₁ ⊓ C = ⊥ := le_bot_iff.mp ((inf_le_inf_left W₁ hCK₁).trans hfix₁.le)
  have hW₂C : W₂ ⊓ C = ⊥ := le_bot_iff.mp ((inf_le_inf_left W₂ hCK₂).trans hfix₂.le)
  have htop : W₁ ⊔ (W₂ ⊔ C) = ⊤ := by rw [← sup_assoc]; exact hsup'
  have hinf₁ : W₁ ⊓ (W₂ ⊔ C) = ⊥ := by
    refine le_bot_iff.mp (le_trans (le_inf inf_le_left ?_) hW₁C.le)
    calc W₁ ⊓ (W₂ ⊔ C) ≤ (W₁ ⊔ C) ⊓ (W₂ ⊔ C) := inf_le_inf_right _ le_sup_left
      _ = C := hinf'
  have hinf₂ : W₂ ⊓ (W₁ ⊔ C) = ⊥ := by
    refine le_bot_iff.mp (le_trans (le_inf inf_le_left ?_) hW₂C.le)
    calc W₂ ⊓ (W₁ ⊔ C) ≤ (W₁ ⊔ C) ⊓ (W₂ ⊔ C) := by
          rw [inf_comm]; exact inf_le_inf_left _ le_sup_left
      _ = C := hinf'
  have hM2 : pCoreOf 2 (autOn (fsuM T L) (fsuVM T L I)) = ⊥ :=
    Setup.pCoreOf_autOn_eq_bot
      (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr (h322 G T L I hyp.fsu))
  have hXY : autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓ Subgroup.centralizer
      ((autOn L (fsuVM T L I) ⊔ autOn (CFSG.conjugate L t) (fsuVM T L I) :
        Subgroup (MulAut ↥(fsuVM T L I))) : Set (MulAut ↥(fsuVM T L I))) ≤
      autOn (fsuM T L) (fsuVM T L I) ⊓ Subgroup.centralizer
        (autOn (fsuL0 T L) (fsuVM T L I) : Set (MulAut ↥(fsuVM T L I))) := by
    rw [hK₁₂]
    exact inf_le_inf_right _ (A4.autOn_mono (sup_le (fsuL0_le_fsuM T L) (le_fsuM T L)))
  exact not_isFFModule_of_four_copies hV h154 hK₁X hK₂X e₁ e₂ hsum₁ hsum₂ htop hinf₁ hinf₂ hXY
    (isSolvable_of_twoResidual h5)
    (fun Q hQY hQn hQ2 => eq_bot_of_le_centralizer_autOn hM2 le_rfl Q hQY hQn hQ2)
    (not_three_dvd_card_of_twoResidual h5)

end CaseSix

end CFSG.Quasithin.Vol2.Ch10.SecA
