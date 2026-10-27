module

public import CFSG.RankThree.PartTwo.Sec9.Hyp92NeverK
public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.RankThree.PartTwo.Sec14.Item1411

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def SLPiTrichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), 1 ≤ n →
    Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) →
    ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) → x ^ 3 = 1 →
      KFacts.InducesStdKind L x .inner ∨ KFacts.InducesStdKind L x .diagonal ∨
        KFacts.InducesStdKind L x .field

@[expose] def SLPiTorusCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsSLThreePiAt X (2 ^ (3 * n)) →
    ∀ w : X, w ^ 3 = 1 → w ∉ Subgroup.center X → ∀ y z : X, y * w = w * y → z * w = w * z →
      y * z = z * y

@[expose] def SLPiFieldCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), 2 ≤ n →
    Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) →
    ∀ a : G, a ∈ Subgroup.normalizer (L : Set G) → a ^ 3 = 1 →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) →
      IsQuasisimple (Sec8.barCentralizer (Subgroup.zpowers a) L) ∧
        Nat.card (Subgroup.center (Sec8.barCentralizer (Subgroup.zpowers a) L)) = 3 ∧
        ∃ z ∈ Sec8.barCentralizer (Subgroup.zpowers a) L, z ^ 3 = 1 ∧
          z ∉ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)

section General

variable {G : Type} [Group G] [Finite G]

theorem isSLThreePiAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) : Sec4.IsSLThreePiAt Y q := by
  obtain ⟨K, hK, hKf, h1 | h1⟩ := hX
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inl ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inr ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩

theorem isQuasisimple_sec11K_quot {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : ∀ z ∈ Subgroup.center
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))), z ^ 3 = 1) :
    IsQuasisimple (Sec11.sec11K L x ⧸ aschbacherSolvableCore 3 (Sec11.sec11K L x)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) with hF
  set K := Sec11.sec11K L x with hK
  have hrange : (Sec11.kMap L x).range = F := by
    rw [Sec11.range_kMap_eq hxN hx3 hQ.1, Sec11.range_cMap hxN hx3]
  have hmem : ∀ k, Sec11.kMap L x k ∈ F := fun k => hrange ▸ ⟨k, rfl⟩
  set ψ : K →* F := (Sec11.kMap L x).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    rw [← hrange] at hf
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, Subtype.ext hk⟩
  have hθ3 := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hker : ψ.ker = aschbacherSolvableCore 3 K := by
    apply le_antisymm
    ·
      have hkθ : ∀ k ∈ ψ.ker, ((k : G)) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
        intro k hk
        have h1 : Sec11.kMap L x k = 1 := congrArg Subtype.val hk
        rw [Sec11.kMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at h1
        exact ⟨_, h1, rfl⟩
      let f : ψ.ker →* inSubgroup (aschbacherSolvableCore 3) L :=
        ((K.subtype.comp ψ.ker.subtype).codRestrict _ fun k => hkθ k k.2)
      have hf : Function.Injective f := by
        intro k₁ k₂ h12
        apply Subtype.ext
        apply Subtype.ext
        have h13 := congrArg Subtype.val h12
        exact h13
      have hsol : Group.IsSolvable ψ.ker := by
        have := Sec11.isSolvable_inSubgroup_theta L
        exact Group.isSolvable_of_isSolvable_injective hf
      have hcard : ¬ 3 ∣ Nat.card ψ.ker := by
        intro h3
        apply Sec11.not_three_dvd_card_inSubgroup_theta L
        refine h3.trans ?_
        have h1 : Nat.card ψ.ker = Nat.card f.range :=
          Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
        rw [h1]
        exact Subgroup.card_subgroup_dvd_card _
      exact (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.2.1
        ψ.ker inferInstance hsol hcard
    ·
      have hN : ((aschbacherSolvableCore 3 K).map ψ).Normal :=
        Subgroup.Normal.map inferInstance ψ hψs
      have hNs : Group.IsSolvable ((aschbacherSolvableCore 3 K).map ψ) := by
        have := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).1
        exact Group.isSolvable_of_surjective (ψ.subgroupMap_surjective _)
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ
          ((aschbacherSolvableCore 3 K).map ψ) with hc | ht
      · intro k hk
        have h1 : ψ k ∈ Subgroup.center F := hc ⟨k, hk, rfl⟩
        have h2 : orderOf (ψ k) ∣ 3 := orderOf_dvd_of_pow_eq_one (hZ _ h1)
        have h3 : orderOf (ψ k) ∣ Nat.card (aschbacherSolvableCore 3 K) := by
          refine (orderOf_map_dvd ψ k).trans ?_
          rw [← Subgroup.orderOf_mk k hk]
          exact orderOf_dvd_natCard _
        have h4 : orderOf (ψ k) = 1 := Nat.eq_one_of_dvd_coprimes
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3) h2 h3
        rw [orderOf_eq_one_iff] at h4
        exact h4
      · exfalso
        have hFs : Group.IsSolvable F := by
          have e : ((aschbacherSolvableCore 3 K).map ψ : Subgroup F) ≃* F :=
            (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
          exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
        obtain ⟨-, hsimple, a', b', hab⟩ := hQ
        have : Group.IsSolvable (F ⧸ Subgroup.center F) := inferInstance
        exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a' b')
  have e : K ⧸ aschbacherSolvableCore 3 K ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ

end General

theorem item95_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hK7 : SLPiFieldCent)
    (hK8 : SLPiTrichotomy) (hK9 : SLPiTorusCent) : Item95 := by
  intro G _ _ A c L a R n h g hgR
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := h.one_le
  have hn2 : 2 ≤ n := item93_of_item45 h45 G A c L a R n h
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hc3 : c ^ 3 = 1 := hAel.2 c h.mem_A
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  have hHL := hyp92NormalizerL_of h45 G A c L a R n h
  obtain ⟨hcL, hcZ, hc1⟩ := h.exists_mem_center h45
  set b := g * c * g⁻¹ with hb
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hLC : L ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hCH : C ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c)
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hRC : R ≤ C := Sec11.le_centralizer_of_le_normalizer_zpowers hco h.isSylowOf.isPGroup hRH
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hHL (hRH hgR)
  have hb3 : b ^ 3 = 1 := by rw [hb, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hbc : b * c = c * b := Subgroup.mem_centralizer_singleton_iff.mp (hRC hgR)
  rcases hK8 G L n hn h.isSLThreePiAt b hbN hb3 with hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr hk
  exfalso
  obtain ⟨D, hDc, -, hDout⟩ := slPiInndiag G L n hn h.isSLThreePiAt
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have hbD : ρ ⟨b, hbN⟩ ∉ D := hDout b hbN (Or.inl hk)
  have hcommD : commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro σ _ τ _
    rw [commutatorElement_def]
    exact hDc σ τ
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hcL
  have hρc : ρ ⟨c, hcN⟩ = 1 :=
    KFacts.thetaQuotMulAut_compAction_eq_one hcN (fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hy)).symm)
  have hbc' : b ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hbD
    have e : (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk'.symm)
    rw [e, map_zpow, hρc, one_zpow]
    exact D.one_mem
  have hb1 : b ≠ 1 := fun h1 => hbc' (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hQ, hZ3, zb, hzbC, hzb3, hzbZ⟩ := hK7 G L n hn2 h.isSLThreePiAt b hbN hb3 (Or.inl hk)
  have hFeq : (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) =
        Sec8.barCentralizer (Subgroup.zpowers b) L := by
    ext y
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN]
    rfl
  have hQ' : IsQuasisimple
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) := hFeq ▸ hQ
  have hZ3' : Nat.card (Subgroup.center
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)))) = 3 := hFeq ▸ hZ3
  have hZexp : ∀ w ∈ Subgroup.center
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))), w ^ 3 = 1 := by
    intro w hw
    have h1 := orderOf_dvd_natCard (⟨w, hw⟩ : Subgroup.center _)
    rw [hZ3', Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  set X := Sec11.sec11K L b with hX
  have hXq := isQuasisimple_sec11K_quot hbN hb3 hQ' hZexp
  have hcX : c ∈ X := Sec11.mem_sec11K_of_pow_eq_one hbN hb3 hQ'.1
    ⟨hcL, Subgroup.mem_centralizer_singleton_iff.mpr hbc.symm⟩ (k := 1) (by simpa using hc3)
  have hLperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
  have hinnD : ∀ (y : G) (hy : y ∈ L), ρ ⟨y, Subgroup.le_normalizer hy⟩ ∈ D := by
    intro y hy
    apply hcommD
    rw [hρ, MonoidHom.comp_apply,
      KFacts.thetaQuotMulAut_compAction_of_mem hy (Subgroup.le_normalizer hy)]
    have h1 : π ⟨y, hy⟩ ∈ commutator (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [hLperf.commutator_eq_top]
      exact Subgroup.mem_top _
    have h2 : (commutator (L ⧸ aschbacherSolvableCore 3 L)).map MulAut.conj ≤
        commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 ⟨_, h1, rfl⟩
  have hρb3 : ρ ⟨b, hbN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hpowD : ∀ j : ℤ, ρ ⟨b, hbN⟩ ^ j ∈ D → ρ ⟨b, hbN⟩ ^ j = 1 := by
    intro j hj
    have h3' : ρ ⟨b, hbN⟩ ^ (3 : ℤ) = 1 := by exact_mod_cast hρb3
    rw [zpow_eq_zpow_emod j h3'] at hj ⊢
    have hk' : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hj ⊢
    · rfl
    · exact absurd (by simpa using hj) hbD
    · exfalso
      apply hbD
      have h1 : ρ ⟨b, hbN⟩ = (ρ ⟨b, hbN⟩ ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, h3', mul_one, zpow_one]
      rw [h1]
      exact D.zpow_mem hj 2
  have hzbP : IsPGroup 3 (Subgroup.zpowers zb) :=
    isPGroup_zpowers_of_pow (k := 1) (by simpa using hzb3)
  obtain ⟨E, -, hEb, -, hEim, -, hEinj⟩ := KFacts.exists_lift_of_le_barCentralizer hbN
    ⟨1, by simpa using hb3⟩ hzbP (Subgroup.zpowers_le.mpr hzbC)
  obtain ⟨z, hzE, hzz⟩ : ∃ z : L, (z : G) ∈ E ∧ π z = zb := by
    have h1 : zb ∈ Sec8.imageModTheta L E := by
      rw [hEim]
      exact Subgroup.mem_zpowers zb
    obtain ⟨w, hw, hwz⟩ := h1
    exact ⟨w, Subgroup.mem_subgroupOf.mp hw, hwz⟩
  have hz3 : z ^ 3 = 1 := hEinj _ (by rw [Subgroup.coe_pow]; exact E.pow_mem hzE 3)
    (by rw [map_pow, hzz, hzb3])
  have hz3G : (z : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
  have hzb : (z : G) * b = b * z := Subgroup.mem_centralizer_singleton_iff.mp (hEb hzE)
  have hzc : (z : G) * c = c * z := Subgroup.mem_centralizer_singleton_iff.mp (hLC z.2)
  have hcb' : Commute c b := hbc.symm
  set A₁ := Subgroup.zpowers c ⊔ Subgroup.zpowers b with hA₁
  set A' := A₁ ⊔ Subgroup.zpowers (z : G) with hA'
  have hA₁el : CFSG.Assembly.IsElemAbelian 3 A₁ :=
    isElemAbelian_sup (isElemAbelian_zpowers hc3) (isElemAbelian_zpowers hb3)
      (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hcb'.zpow_zpow i j).eq)
  have hA₁z : A₁ ≤ Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      rw [Subgroup.mem_centralizer_iff] <;> intro w hw <;>
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    · exact ((show Commute (z : G) c from hzc).zpow_left k).eq
    · exact ((show Commute (z : G) b from hzb).zpow_left k).eq
  have hA'el : CFSG.Assembly.IsElemAbelian 3 A' :=
    isElemAbelian_sup hA₁el (isElemAbelian_zpowers hz3G) (fun x hx y hy =>
      ((Subgroup.mem_centralizer_iff.mp (hA₁z hx)) y hy).symm)
  have hbO : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hbN' : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.zpowers_le.mpr (Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [hbc, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c))
  have hA₁card : Nat.card A₁ = 9 := by
    rw [hA₁, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hbN'
      (disjoint_zpowers_of_not_mem hb3 hbc'), Nat.card_zpowers, Nat.card_zpowers, hco, hbO]
  have hzA₁ : (z : G) ∉ A₁ := by
    intro hmem
    obtain ⟨y, hy, x, hx, hyx⟩ := exists_mul_of_mem_sup hbN' hmem
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hbjL : b ^ j ∈ L := by
      have e : b ^ j = (z : G) * (c ^ i)⁻¹ := by rw [← hyx]; group
      rw [e]
      exact L.mul_mem z.2 (L.inv_mem (L.zpow_mem hcL i))
    have e' : (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) ^ j =
        ⟨b ^ j, Subgroup.le_normalizer hbjL⟩ := Subtype.ext (by rw [Subgroup.coe_zpow])
    have hj : ρ ⟨b, hbN⟩ ^ j = 1 := hpowD j (by rw [← map_zpow, e']; exact hinnD _ hbjL)
    have hbjc : π ⟨b ^ j, hbjL⟩ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      have h1 : ρ ⟨b ^ j, Subgroup.le_normalizer hbjL⟩ = 1 := by rw [← e', map_zpow, hj]
      rw [hρ, MonoidHom.comp_apply,
        KFacts.thetaQuotMulAut_compAction_of_mem hbjL (Subgroup.le_normalizer hbjL)] at h1
      rw [Subgroup.mem_center_iff]
      intro w
      have h2 := DFunLike.congr_fun h1 w
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      calc w * π ⟨b ^ j, hbjL⟩ = π ⟨b ^ j, hbjL⟩ * w * (π ⟨b ^ j, hbjL⟩)⁻¹ * π ⟨b ^ j, hbjL⟩ := by
            rw [h2]
        _ = π ⟨b ^ j, hbjL⟩ * w := by group
    apply hzbZ
    rw [← hzz]
    have ez : z = ⟨b ^ j, hbjL⟩ * ⟨c, hcL⟩ ^ i :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow]; exact hyx.symm)
    rw [ez, map_mul, map_zpow]
    exact Subgroup.mul_mem _ hbjc (Subgroup.zpow_mem _ hcZ i)
  have hzO : orderOf (z : G) = 3 :=
    orderOf_eq_prime hz3G (fun h1 => hzA₁ (h1 ▸ Subgroup.one_mem _))
  have hzN : Subgroup.zpowers (z : G) ≤ Subgroup.normalizer (A₁ : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun e he =>
        ((Subgroup.mem_centralizer_iff.mp (hA₁z he)) _ (Subgroup.mem_zpowers _)).symm))
  have hA'card : Nat.card A' = 27 := by
    rw [hA', GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hzN
      (disjoint_zpowers_of_not_mem hz3G hzA₁), hA₁card, Nat.card_zpowers, hzO]
  have hcA' : c ∈ A' := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hbA' : b ∈ A' := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({b} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (Sec14.centralizer_singleton_ne_top h.toTheoremFourHyp.isSimpleGroup
        h.toTheoremFourHyp.nonabelian hb1)
  obtain ⟨J, hJ, hXJ⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4
    ⟨hA'el, hA'card⟩ hcA' hbA' h.ne_one h.mem_thetaComponentsAt hXq
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hL'b : L' ∈ thetaComponentsAt 3 b :=
    map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
  have hbL' : b ∈ L' := ⟨c, hcL, rfl⟩
  set π' := QuotientGroup.mk' (aschbacherSolvableCore 3 L') with hπ'
  set e : L ≃* L' := L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    with he
  have hL'SL : Sec4.IsSLThreePiAt (L' ⧸ aschbacherSolvableCore 3 L') (2 ^ (3 * n)) :=
    isSLThreePiAt_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e))
      h.isSLThreePiAt
  have hbZ' : π' ⟨b, hbL'⟩ ∈ Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L') w
    rw [hπ', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨l, hl, rfl⟩ := hl'
    change g * l * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * l * g⁻¹)
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
    calc g * l * g⁻¹ * (g * c * g⁻¹) = g * (l * c) * g⁻¹ := by group
      _ = g * (c * l) * g⁻¹ := by rw [hlc]
      _ = g * c * g⁻¹ * (g * l * g⁻¹) := by group
  have hb1' : π' ⟨b, hbL'⟩ ≠ 1 := by
    intro h1
    rw [hπ', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow h1 (j := 1)
      (Subtype.ext (by simpa using hb3))
    exact hb1 (congrArg Subtype.val h2)
  have hbL'3 : (⟨b, hbL'⟩ : L') ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbO' : orderOf (π' ⟨b, hbL'⟩) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hbL'3, map_one]) hb1'
  have hZ'eq : Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') =
      Subgroup.zpowers (π' ⟨b, hbL'⟩) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbZ')
      (by rw [KFacts.card_center_of_isSLThreePiAt hn hL'SL, Nat.card_zpowers, hbO'])).symm
  have hJne : J ≠ L' := by
    intro hJL
    have hXL' : X ≤ L' := hJL ▸ hXJ
    have hcL' : c ∈ L' := hXL' hcX
    set w := π' ⟨c, hcL'⟩ with hw
    have hcL'3 : (⟨c, hcL'⟩ : L') ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    have hw3 : w ^ 3 = 1 := by rw [hw, ← map_pow, hcL'3, map_one]
    have hwZ : w ∉ Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') := by
      rw [hZ'eq]
      intro hmem
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 : ((⟨b, hbL'⟩ : L') ^ k)⁻¹ * ⟨c, hcL'⟩ ∈ aschbacherSolvableCore 3 L' := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ', map_mul, map_inv,
          map_zpow, hk', hw, inv_mul_cancel]
      have hbc'' : Commute (⟨b, hbL'⟩ : L') ⟨c, hcL'⟩ := Subtype.ext hbc
      have h3 : (((⟨b, hbL'⟩ : L') ^ k)⁻¹ * ⟨c, hcL'⟩) ^ 3 ^ 1 = 1 := by
        rw [pow_one, ((hbc''.zpow_left k).inv_left).mul_pow, hcL'3, mul_one, inv_pow,
          ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbL'3, one_zpow, inv_one]
      have h4 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow h2 h3
      have h5 : (⟨b, hbL'⟩ : L') ^ k = ⟨c, hcL'⟩ := inv_mul_eq_one.mp h4
      have hcb : c ∈ Subgroup.zpowers b :=
        ⟨k, by simpa using congrArg Subtype.val h5⟩
      exact hbc' (mem_zpowers_of_mem_zpowers_of_ne_one hb3 hcb h.ne_one)
    have hXc : ∀ x ∈ X, x * c = c * x := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLC (Sec11.sec11K_le L b hx))
    have hXab : ∀ x ∈ X, ∀ x' ∈ X,
        x * x' * x⁻¹ * x'⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L' := by
      intro x hx x' hx'
      have hxw : ∀ y (hy : y ∈ X), π' ⟨y, hXL' hy⟩ * w = w * π' ⟨y, hXL' hy⟩ := by
        intro y hy
        rw [hw, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hXc y hy)
      have h1 := hK9 _ n hn hL'SL w hw3 hwZ _ _ (hxw x hx) (hxw x' hx')
      have h2 : π' (⟨x, hXL' hx⟩ * ⟨x', hXL' hx'⟩ * (⟨x, hXL' hx⟩ : L')⁻¹ *
          (⟨x', hXL' hx'⟩ : L')⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      rw [hπ', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨_, h2, rfl⟩
    have hXperf : Group.IsPerfect X :=
      PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
    have hXθ : X ≤ inSubgroup (aschbacherSolvableCore 3) L' := by
      intro x hx
      have h1 : (⟨x, hx⟩ : X) ∈ commutator X := by
        rw [hXperf.commutator_eq_top]
        exact Subgroup.mem_top _
      have h2 : commutator X ≤ (inSubgroup (aschbacherSolvableCore 3) L').comap X.subtype := by
        rw [commutator_def, Subgroup.commutator_le]
        intro p _ q _
        rw [Subgroup.mem_comap, commutatorElement_def]
        simpa using hXab p p.2 q q.2
      exact h2 h1
    have hXsol : Group.IsSolvable X := by
      have := Sec11.isSolvable_inSubgroup_theta L'
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXθ)
        (Subgroup.inclusion_injective hXθ)
    obtain ⟨-, hsimple, a', b', hab⟩ := hXq
    have : Group.IsSolvable ((↥X ⧸ aschbacherSolvableCore 3 ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a' b')
  have hcN' : c ∈ Subgroup.normalizer (L' : Set G) := by
    have h1 : g⁻¹ * c * g ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : c * (g * c * g⁻¹) = (g * c * g⁻¹) * c := hbc.symm
      calc g⁻¹ * c * g * c = g⁻¹ * (c * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * c) * g := by rw [h2]
        _ = c * (g⁻¹ * c * g) := by group
    have h2 : g⁻¹ * c * g ∈ Subgroup.normalizer (L : Set G) := hHL (hCH h1)
    rw [hL', ← Subgroup.map_equiv_normalizer_eq L (MulAut.conj g)]
    exact ⟨_, h2, by
      change g * (g⁻¹ * c * g) * g⁻¹ = c
      group⟩
  have hθL' := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL'b
  have hcJ : c ∈ J := hXJ hcX
  have hρ'c : Sec4.thetaQuotMulAut L' (Sec4.compAction L' ⟨c, hcN'⟩) = 1 := by
    apply KFacts.thetaQuotMulAut_compAction_eq_one_of_forall hcN'
    intro y hy
    have h1 := Sec10.commutator_mem_theta_of_ne hJ hL'b hJne hcJ hy
    have h2 : c * y * c⁻¹ * y⁻¹ ∈ L' :=
      L'.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN' y).mp hy) (L'.inv_mem hy)
    have h3 : c * y * c⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L' := by
      rw [hθL']
      exact ⟨h2, h1⟩
    exact h3
  have hperf' : Group.IsPerfect
      ((Sec4.thetaQuotMulAut L' (Sec4.compAction L' ⟨c, hcN'⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L' ⧸ aschbacherSolvableCore 3 L'))) := by
    have htop : (Sec4.thetaQuotMulAut L' (Sec4.compAction L' ⟨c, hcN'⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L' ⧸ aschbacherSolvableCore 3 L')) = ⊤ := by
      rw [hρ'c]
      exact eq_top_iff.mpr fun y _ => rfl
    rw [htop]
    exact Group.IsPerfect.top_iff.mpr (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'b).1
  have hbY : b ∈ Sec11.sec11K L' c :=
    Sec11.mem_sec11K_of_pow_eq_one hcN' hc3 hperf'
      ⟨hbL', Subgroup.mem_centralizer_singleton_iff.mpr hbc⟩ (k := 1) (by simpa using hb3)
  set Y := Sec11.sec11K L' c with hY
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := fun y hy =>
    hHL (hCH (((Subgroup.map_subtype_le _).trans inf_le_right) hy))
  have hYperf : Group.IsPerfect Y :=
    PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hρY : ρ ⟨b, hbN⟩ ∈ commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
    set φ : Y →* MulAut (L ⧸ aschbacherSolvableCore 3 L) := ρ.comp (Subgroup.inclusion hYN)
      with hφ
    have h1 : (⟨b, hbY⟩ : Y) ∈ commutator Y := by
      rw [hYperf.commutator_eq_top]
      exact Subgroup.mem_top _
    have h2 : (commutator Y).map φ ≤ commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 ⟨_, h1, rfl⟩
  exact hbD (hcommD hρY)

end CFSG.RankThree.PartTwo.Sec9
