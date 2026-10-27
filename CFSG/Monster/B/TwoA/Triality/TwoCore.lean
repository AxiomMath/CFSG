
module

public import CFSG.Monster.B.TwoA.Triality.TwoCoreAux

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.B.Co2

attribute [local instance] vAction restAction

theorem center_eq_bot_of_two_pretransitive {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (h3 : ∀ x y : X, ∃ w, w ≠ x ∧ w ≠ y) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨x, hx⟩ : ∃ x : X, z • x ≠ x := by
    by_contra h
    push Not at h
    exact hz1 (FaithfulSMul.eq_of_smul_eq_smul fun x => (h x).trans (one_smul G x).symm)
  obtain ⟨w, hwx, hwy⟩ := h3 x (z • x)
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨g, gx, gy⟩ := h2 (a := x) (b := z • x) (c := x) (d := w) (Ne.symm hx) (Ne.symm hwx)
  have hc : g * z = z * g := Subgroup.mem_center_iff.1 hz g
  apply hwy
  calc w = g • (z • x) := gy.symm
    _ = (g * z) • x := (mul_smul g z x).symm
    _ = (z * g) • x := by rw [hc]
    _ = z • (g • x) := mul_smul z g x
    _ = z • x := by rw [gx]

theorem rest_three (x y : Rest) : ∃ w : Rest, w ≠ x ∧ w ≠ y := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset Rest) ⊆ insert x {y} := fun w _ => by
    by_cases hw : w = x
    · rw [hw]
      exact Finset.mem_insert_self _ _
    · rw [h w hw]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ : Finset Rest).card = 22 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_rest]
  have h3 := Finset.card_insert_le x ({y} : Finset Rest)
  rw [Finset.card_singleton] at h3
  omega

theorem center_Ppair : Subgroup.center Ppair = ⊥ :=
  center_eq_bot_of_two_pretransitive isMultiplyPretransitive_rest rest_three

theorem pow_two_eq_one_of_isPGroup {N : Subgroup (Equiv.Perm (Fin 3))} (hN : IsPGroup 2 N)
    {g : Equiv.Perm (Fin 3)} (hg : g ∈ N) : g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN) ⟨g, hg⟩
  have hk' : orderOf g = 2 ^ k := (Subgroup.orderOf_coe (⟨g, hg⟩ : N)).trans hk
  have h6 : orderOf g ∣ 6 := by
    have := orderOf_dvd_card (G := Equiv.Perm (Fin 3)) (x := g)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [hk'] at h6
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans h4 h6
    omega
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [hk']
  exact Nat.pow_dvd_pow 2 hk1 |>.trans (by norm_num)

theorem perm_three_key : ∀ g : Equiv.Perm (Fin 3), g ^ 2 = 1 →
    (∀ c : Equiv.Perm (Fin 3), (g * (c * g * c⁻¹)) ^ 2 = 1) → g = 1 := by
  decide +kernel

theorem pCore_perm_three : CFSG.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hP := CFSG.pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 3))
  have hn := CFSG.pCore_normal (p := 2) (G := Equiv.Perm (Fin 3))
  exact perm_three_key g (pow_two_eq_one_of_isPGroup hP hg) fun c =>
    pow_two_eq_one_of_isPGroup hP ((CFSG.pCore 2 _).mul_mem hg (hn.conj_mem g hg c))

theorem pCore_prod_eq_bot {G H : Type*} [Group G] [Group H] {p : ℕ}
    (hG : CFSG.pCore p G = ⊥) (hH : CFSG.pCore p H = ⊥) : CFSG.pCore p (G × H) = ⊥ := by
  have h1 : (CFSG.pCore p (G × H)).map (MonoidHom.fst G H) = ⊥ :=
    eq_bot_iff.2 ((le_pCore_of_normal (Subgroup.Normal.map CFSG.pCore_normal _
      Prod.fst_surjective) (CFSG.pCore_isPGroup.map _)).trans hG.le)
  have h2 : (CFSG.pCore p (G × H)).map (MonoidHom.snd G H) = ⊥ :=
    eq_bot_iff.2 ((le_pCore_of_normal (Subgroup.Normal.map CFSG.pCore_normal _
      Prod.snd_surjective) (CFSG.pCore_isPGroup.map _)).trans hH.le)
  rw [eq_bot_iff]
  intro x hx
  have a : x.1 = 1 := by
    have : x.1 ∈ (CFSG.pCore p (G × H)).map (MonoidHom.fst G H) := ⟨x, hx, rfl⟩
    rwa [h1, Subgroup.mem_bot] at this
  have b : x.2 = 1 := by
    have : x.2 ∈ (CFSG.pCore p (G × H)).map (MonoidHom.snd G H) := ⟨x, hx, rfl⟩
    rwa [h2, Subgroup.mem_bot] at this
  exact Prod.ext a b

theorem ker_thetaC_eq_pCore :
    thetaC.ker = CFSG.pCore 2 Ctwo :=
  ker_eq_pCore_of_surjective thetaC_surjective isPGroup_ker_thetaC pCore_Ppair

theorem R2_eq_map_pCore :
    R2 = (CFSG.pCore 2 Ctwo).map Ctwo.subtype := by
  rw [R2, R2C_eq_ker, ker_thetaC_eq_pCore]

theorem conj_mem_Ctwo {n : Dfull} (hn : n ∈ Ntwo) {c : Dfull} (hc : c ∈ Ctwo) :
    n * c * n⁻¹ ∈ Ctwo :=
  Ctwo_subgroupOf_normal.conj_mem ⟨c, Ctwo_le_Ntwo hc⟩ hc ⟨n, hn⟩

@[expose] def conjC (n : Ntwo) : Ctwo ≃* Ctwo where
  toFun c := ⟨(n : Dfull) * c * (n : Dfull)⁻¹, conj_mem_Ctwo n.2 c.2⟩
  invFun c := ⟨(n : Dfull)⁻¹ * c * n, by
    have := conj_mem_Ctwo (Ntwo.inv_mem n.2) c.2
    rwa [inv_inv] at this⟩
  left_inv c := Subtype.ext (by
    change (n : Dfull)⁻¹ * ((n : Dfull) * c * (n : Dfull)⁻¹) * n = c
    group)
  right_inv c := Subtype.ext (by
    change (n : Dfull) * ((n : Dfull)⁻¹ * c * n) * (n : Dfull)⁻¹ = c
    group)
  map_mul' a b := Subtype.ext (by
    change (n : Dfull) * (a * b) * (n : Dfull)⁻¹ =
      ((n : Dfull) * a * (n : Dfull)⁻¹) * ((n : Dfull) * b * (n : Dfull)⁻¹)
    group)

theorem conj_mem_R2
    {n : Dfull} (hn : n ∈ Ntwo) {g : Dfull} (hg : g ∈ R2) : n * g * n⁻¹ ∈ R2 := by
  rw [R2_eq_map_pCore] at hg ⊢
  obtain ⟨c, hc, rfl⟩ := hg
  have h := CFSG.pCore_map_iso 2 (conjC ⟨n, hn⟩)
  refine ⟨conjC ⟨n, hn⟩ c, ?_, rfl⟩
  rw [← h]
  exact ⟨c, hc, rfl⟩

theorem R2_le_Ntwo :
    R2 ≤ Ntwo := R2_le_Ctwo.trans Ctwo_le_Ntwo

instance R2_subgroupOf_normal :
    (R2.subgroupOf Ntwo).Normal :=
  ⟨fun _ hn g => conj_mem_R2 g.2 hn⟩

abbrev KN :
    Type := Ntwo ⧸ R2.subgroupOf Ntwo

@[expose] def mkK :
    Ntwo →* KN := QuotientGroup.mk' _

theorem mkK_surjective :
    Function.Surjective mkK := QuotientGroup.mk'_surjective _

theorem R2N_le_ker_sym3Hom :
    R2.subgroupOf Ntwo ≤ sym3Hom.ker := by
  rw [ker_sym3Hom]
  intro g hg
  exact R2_le_Ctwo hg

@[expose] def sym3K :

    KN →* Equiv.Perm (Fin 3) := QuotientGroup.lift _ sym3Hom R2N_le_ker_sym3Hom

theorem sym3K_mkK
    (g : Ntwo) : sym3K (mkK g) = sym3Hom g := rfl

@[expose] def inclCN : Ctwo →* Ntwo := Subgroup.inclusion Ctwo_le_Ntwo

theorem mkK_inclCN_eq_iff
    (c c' : Ctwo) :
    mkK (inclCN c) = mkK (inclCN c') ↔ thetaC c = thetaC c' := by
  rw [mkK, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  change (c : Dfull)⁻¹ * c' ∈ R2 ↔ _
  rw [mem_R2_iff (Ctwo.mul_mem (Ctwo.inv_mem c.2) c'.2)]
  have e : (⟨(c : Dfull)⁻¹ * c', Ctwo.mul_mem (Ctwo.inv_mem c.2) c'.2⟩ : Ctwo) = c⁻¹ * c' := rfl
  rw [e, map_mul, map_inv, inv_mul_eq_one]

theorem mkK_inclCN_eq
    (c : Ctwo) : mkK (inclCN c) = mkK (inclCN (ghatC (thetaC c))) :=
  (mkK_inclCN_eq_iff _ _).2 (thetaC_ghatC _).symm

@[expose] def alphaK :
    Ppair →* KN where
  toFun q := mkK (inclCN (ghatC q))
  map_one' := by
    change mkK (inclCN (ghatC 1)) = 1
    have h := (mkK_inclCN_eq_iff (ghatC 1) 1).2 (by rw [thetaC_ghatC, map_one])
    rw [h, map_one, map_one]
  map_mul' q q' := by
    change mkK (inclCN (ghatC (q * q'))) = mkK (inclCN (ghatC q)) * mkK (inclCN (ghatC q'))
    rw [← map_mul mkK, ← map_mul inclCN]
    exact (mkK_inclCN_eq_iff _ _).2 (by rw [map_mul thetaC, thetaC_ghatC, thetaC_ghatC,
      thetaC_ghatC])

theorem alphaK_apply
    (q : Ppair) : alphaK q = mkK (inclCN (ghatC q)) := rfl

theorem alphaK_injective :
    Function.Injective alphaK := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have h := (mkK_inclCN_eq_iff (ghatC q) 1).1 (by rw [← alphaK_apply, hq, map_one, map_one])
  rwa [thetaC_ghatC, map_one] at h

theorem sym3K_alphaK
    (q : Ppair) : sym3K (alphaK q) = 1 :=
  (mem_Ctwo_iff_sym3Hom (inclCN (ghatC q))).1 (ghatC q).2

theorem ker_sym3K_le
    {k : KN} (hk : sym3K k = 1) : k ∈ alphaK.range := by
  obtain ⟨g, rfl⟩ := mkK_surjective k
  have hC : (g : Dfull) ∈ Ctwo := (mem_Ctwo_iff_sym3Hom g).2 hk
  have e : g = inclCN ⟨g, hC⟩ := rfl
  rw [e, mkK_inclCN_eq]
  exact ⟨_, rfl⟩

@[expose] def Bsub :
    Subgroup KN := Subgroup.closure {mkK hhatN, mkK tauN}

theorem commute_mkK
    {a b : Ntwo} (h : (a : Dfull) * b = b * a) : mkK a * mkK b = mkK b * mkK a := by
  rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext h]

theorem Bsub_le_centralizer :
    Bsub ≤ Subgroup.centralizer (Set.range alphaK) := by
  rw [Bsub, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> refine Subgroup.mem_centralizer_iff.2 ?_ <;> rintro _ ⟨q, rfl⟩
  · exact commute_mkK (ghat_mul_hhat q)
  · exact commute_mkK (ghat_mul_tauhat q)

theorem alphaK_commute_of_mem
    {b : KN} (hb : b ∈ Bsub) (q : Ppair) :
    alphaK q * b = b * alphaK q :=
  Subgroup.mem_centralizer_iff.1 (Bsub_le_centralizer hb) _ ⟨q, rfl⟩

theorem Bsub_inf_range :
    Bsub ⊓ alphaK.range = ⊥ := by
  rw [eq_bot_iff]
  rintro b ⟨hb, q, rfl⟩
  rw [Subgroup.mem_bot]
  have hq : q ∈ Subgroup.center Ppair := by
    rw [Subgroup.mem_center_iff]
    intro q'
    apply alphaK_injective
    rw [map_mul, map_mul]
    exact alphaK_commute_of_mem hb q'
  rw [center_Ppair, Subgroup.mem_bot] at hq
  rw [hq, map_one]

theorem sym3K_restrict_injective :
    Function.Injective (sym3K.comp Bsub.subtype) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hb' : (b : KN) ∈ Bsub ⊓ alphaK.range := ⟨b.2, ker_sym3K_le hb⟩
  rw [Bsub_inf_range, Subgroup.mem_bot] at hb'
  exact OneMemClass.coe_eq_one.1 hb'

theorem sym3K_mkK_hhatN :
    sym3K (mkK hhatN) = Equiv.swap 1 2 := sym3Hom_hhatN

theorem sym3K_mkK_tauN :
    sym3K (mkK tauN) = List.formPerm [0, 1, 2] := sym3Hom_tauN

theorem sym3K_restrict_surjective :
    Function.Surjective (sym3K.comp Bsub.subtype) := by
  have h : Bsub.map sym3K = ⊤ := by
    rw [Bsub, MonoidHom.map_closure, Set.image_pair, sym3K_mkK_hhatN, sym3K_mkK_tauN,
      Set.pair_comm, closure_three]
  intro σ
  have hσ : σ ∈ Bsub.map sym3K := h ▸ Subgroup.mem_top σ
  obtain ⟨b, hb, rfl⟩ := hσ
  exact ⟨⟨b, hb⟩, rfl⟩

@[expose] def betaEquiv :
    Bsub ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (sym3K.comp Bsub.subtype)
    ⟨sym3K_restrict_injective, sym3K_restrict_surjective⟩

@[expose] def betaK :

    Equiv.Perm (Fin 3) →* KN := Bsub.subtype.comp betaEquiv.symm.toMonoidHom

theorem betaK_mem
    (σ : Equiv.Perm (Fin 3)) : betaK σ ∈ Bsub := (betaEquiv.symm σ).2

theorem sym3K_betaK
    (σ : Equiv.Perm (Fin 3)) : sym3K (betaK σ) = σ :=
  (rfl : sym3K (betaK σ) = betaEquiv (betaEquiv.symm σ)).trans (betaEquiv.apply_symm_apply σ)

@[expose] def psiK :
    Ppair × Equiv.Perm (Fin 3) →* KN :=
  alphaK.noncommCoprod betaK fun q σ => alphaK_commute_of_mem (betaK_mem σ) q

theorem psiK_apply
    (x : Ppair × Equiv.Perm (Fin 3)) : psiK x = alphaK x.1 * betaK x.2 := rfl

theorem sym3K_psiK
    (x : Ppair × Equiv.Perm (Fin 3)) : sym3K (psiK x) = x.2 := by
  rw [psiK_apply, map_mul, sym3K_alphaK, sym3K_betaK, one_mul]

theorem psiK_injective :
    Function.Injective psiK := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h2 : x.2 = 1 := by rw [← sym3K_psiK, hx, map_one]
  have h1 : alphaK x.1 = 1 := by
    have := hx
    rw [psiK_apply, h2, map_one, mul_one] at this
    exact this
  exact Prod.ext ((injective_iff_map_eq_one _).1 alphaK_injective _ h1) h2

theorem psiK_surjective :
    Function.Surjective psiK := by
  intro k
  have hk : sym3K (k * (betaK (sym3K k))⁻¹) = 1 := by
    rw [map_mul, map_inv, sym3K_betaK, mul_inv_cancel]
  obtain ⟨q, hq⟩ := ker_sym3K_le hk
  refine ⟨(q, sym3K k), ?_⟩
  rw [psiK_apply, hq, inv_mul_cancel_right]

@[expose] def twoCoreEquiv :
    KN ≃* Ppair × Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective psiK ⟨psiK_injective, psiK_surjective⟩).symm

theorem psiK_twoCoreEquiv
    (k : KN) : psiK (twoCoreEquiv k) = k :=
  (MulEquiv.ofBijective psiK ⟨psiK_injective, psiK_surjective⟩).apply_symm_apply k

theorem twoCoreEquiv_snd
    (g : Ntwo) : (twoCoreEquiv (mkK g)).2 = sym3Hom g := by
  rw [← sym3K_psiK, psiK_twoCoreEquiv, sym3K_mkK]

theorem twoCoreEquiv_inclCN
    (c : Ctwo) : twoCoreEquiv (mkK (inclCN c)) = (thetaC c, 1) := by
  rw [twoCoreEquiv, MulEquiv.symm_apply_eq]
  change mkK (inclCN c) = alphaK (thetaC c) * betaK 1
  rw [map_one, mul_one, alphaK_apply, mkK_inclCN_eq]

theorem ker_twoCore :

    (twoCoreEquiv.toMonoidHom.comp mkK).ker = R2.subgroupOf Ntwo := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, mkK, QuotientGroup.ker_mk']

theorem natCard_R2N :
    Nat.card (R2.subgroupOf Ntwo) = 2 ^ 32 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe R2_le_Ntwo).toEquiv, natCard_R2]

theorem R2_eq_map_pCore_Ntwo :
    R2 = (CFSG.pCore 2 Ntwo).map Ntwo.subtype := by
  have hsurj : Function.Surjective (twoCoreEquiv.toMonoidHom.comp mkK) :=
    twoCoreEquiv.surjective.comp mkK_surjective
  have hker := ker_eq_pCore_of_surjective (p := 2) hsurj
    (by rw [ker_twoCore]; exact IsPGroup.of_card natCard_R2N)
    (pCore_prod_eq_bot pCore_Ppair pCore_perm_three)
  rw [← hker, ker_twoCore, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 R2_le_Ntwo]

theorem index_Vhat_R2 :
    (Vhat.subgroupOf R2).index = 2 ^ 30 := by
  have h := (Vhat.subgroupOf R2).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Vhat_le_R2).toEquiv, isKleinFour_Vhat.card_four,
    natCard_R2] at h
  omega

theorem full_short_triality_normalizer_two_core_quotient :
    (∀ g : Ctwo, (((piC g : Mfr) : Kstab v0) : OLq) =
      ((jhatToKv ⟨g, Ctwo_le_Jhat g.2⟩ : Kstab (phi0 (coordOf rStar))) : OLq)) ∧
    Function.Surjective piC ∧
    Aeq = (SemidirectProduct.inl.range).map MfrEquiv.toMonoidHom ∧ Nat.card Aeq = 2 ^ 10 ∧
    R2 = (Aeq.comap piC).map Ctwo.subtype ∧
    R2 = (CFSG.pCore 2 Ctwo).map Ctwo.subtype ∧ R2 = (CFSG.pCore 2 Ntwo).map Ntwo.subtype ∧
    Nat.card R2 = 2 ^ 32 ∧ Vhat ≤ R2 ∧ (Vhat.subgroupOf R2).index = 2 ^ 30 ∧
    (R2.subgroupOf Ntwo).Normal ∧
    (∃ e : Ntwo ⧸ R2.subgroupOf Ntwo ≃* Ppair × Equiv.Perm (Fin 3),
      (∀ g : Ntwo, (e (QuotientGroup.mk g)).2 = sym3Hom g) ∧
      (∀ g : Ntwo, (g : Dfull) ∈ Ctwo ↔ (e (QuotientGroup.mk g)).2 = 1) ∧
      ∀ c : Ctwo, e (QuotientGroup.mk (Subgroup.inclusion Ctwo_le_Ntwo c)) = (projP (piC c), 1)) ∧
    IsKleinFour Vhat ∧ (Vhat.subgroupOf Ntwo).Normal ∧ Function.Surjective sym3Hom ∧
    sym3Hom.ker = Ctwo.subgroupOf Ntwo :=
  ⟨coe_piC, piC_surjective, rfl, natCard_Aeq, rfl, R2_eq_map_pCore, R2_eq_map_pCore_Ntwo,
    natCard_R2, Vhat_le_R2, index_Vhat_R2, R2_subgroupOf_normal,
    ⟨twoCoreEquiv, twoCoreEquiv_snd, fun g => by
      rw [mem_Ctwo_iff_sym3Hom]
      exact (twoCoreEquiv_snd g).symm ▸ Iff.rfl, twoCoreEquiv_inclCN⟩,
    isKleinFour_Vhat, Subgroup.normal_in_normalizer, sym3Hom_surjective, ker_sym3Hom⟩

end CFSG.Monster.B.TwoA
