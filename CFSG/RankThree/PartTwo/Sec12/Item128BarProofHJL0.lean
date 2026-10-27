module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofHJ
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofBar
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofSetup

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (lBarA omegaA)

section General

variable {G : Type} [Group G] [Finite G]

theorem eq_residual_sup_theta {X : Subgroup G}
    (hXp : Group.IsPerfect (X ⧸ aschbacherSolvableCore 3 X)) {a : G} {k : ℕ}
    (ha3 : a ^ 3 ^ k = 1) (haX : a ∈ Sec4.thetaQuotCentralizer X) :
    X = inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := inSubgroup (aschbacherSolvableCore 3) X with hN
  set Y := X ⊓ Subgroup.centralizer ({a} : Set G) with hY
  set J := inSubgroup perfectResidual Y with hJ
  have hθp := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hN, inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
    exact hθp
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hD3 : IsPGroup 3 (Subgroup.zpowers a) := isPGroup_zpowers_of_pow ha3
  have hDC : Subgroup.zpowers a ≤ Sec4.thetaQuotCentralizer X := Subgroup.zpowers_le.mpr haX
  have hfix : ∀ l ∈ X, ∃ n ∈ N, l * n ∈ Y := by
    intro l hl
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset hD3 hN3 l fun d hd n hn => by
      obtain ⟨hdN, hdl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hDC hd)
      refine ⟨l⁻¹ * (d * l * d⁻¹) * (d * n * d⁻¹),
        N.mul_mem (hdl l hl) (conj_mem_inSubgroup_theta hdN hn), by group⟩
    refine ⟨n, hn, Subgroup.mem_inf.mpr ⟨X.mul_mem hl (hNX hn), ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hfix a (Subgroup.mem_zpowers a)
    calc l * n * a = (a * (l * n) * a⁻¹) * a := by rw [h1]
      _ = a * (l * n) := by group
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hπ
  let ψ : Y →* X ⧸ aschbacherSolvableCore 3 X :=
    π.comp (Subgroup.inclusion (inf_le_left : Y ≤ X))
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 X) q
    obtain ⟨n, hn, hlnY⟩ := hfix l hl
    refine ⟨⟨l * n, hlnY⟩, ?_⟩
    obtain ⟨t, ht, rfl⟩ := hn
    change π ⟨l * t, _⟩ = π ⟨l, hl⟩
    have e : (⟨l * t, hlnY.1⟩ : X) = ⟨l, hl⟩ * t := Subtype.ext rfl
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) t = 1 :=
      (QuotientGroup.eq_one_iff t).mpr ht
    rw [e, map_mul, hπ, h1, mul_one]
  have hres : (perfectResidual Y).map ψ = ⊤ := by
    have h : (perfectResidual Y).map ψ = perfectResidual (X ⧸ aschbacherSolvableCore 3 X) :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [h]
    exact top_le_iff.mp ((perfect_residual_transport (MonoidHom.id _)).2.2 ⊤
      (Group.IsPerfect.top_iff.mpr hXp))
  refine le_antisymm (fun l hl => ?_) (sup_le ((Subgroup.map_subtype_le _).trans inf_le_left) hNX)
  have hq : π ⟨l, hl⟩ ∈ (perfectResidual Y).map ψ := hres ▸ Subgroup.mem_top _
  obtain ⟨r, hr, hrl⟩ := hq
  have hθ : (Subgroup.inclusion (inf_le_left : Y ≤ X) r)⁻¹ * ⟨l, hl⟩ ∈
      aschbacherSolvableCore 3 X := QuotientGroup.eq.mp hrl
  have hrJ : ((r : Y) : G) ∈ J := ⟨r, hr, rfl⟩
  have hlr :
      l = (r : G) * (((Subgroup.inclusion (inf_le_left : Y ≤ X) r)⁻¹ * ⟨l, hl⟩ : X) : G) := by
    simp
  rw [hlr]
  exact Subgroup.mul_mem_sup hrJ ⟨_, hθ, rfl⟩

theorem residual_mem_thetaComponents {b d : G} (hbd : b * d = d * b) {W : Subgroup G}
    (hW : W ∈ thetaComponentsAt 3 b)
    (hJ : IsQuasisimple (↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
      aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))))) :
    ((inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))).subgroupOf
        (Subgroup.centralizer ({b} : Set G))).subgroupOf
      (Subgroup.centralizer ({(⟨d, Subgroup.mem_centralizer_singleton_iff.mpr hbd.symm⟩ :
        ↥(Subgroup.centralizer ({b} : Set G)))} : Set ↥(Subgroup.centralizer ({b} : Set G)))) ∈
      thetaComponents 3 ↥(Subgroup.centralizer ({(⟨d,
        Subgroup.mem_centralizer_singleton_iff.mpr hbd.symm⟩ :
          ↥(Subgroup.centralizer ({b} : Set G)))} :
            Set ↥(Subgroup.centralizer ({b} : Set G)))) := by
  set J := inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  set C₁ := Subgroup.centralizer ({b} : Set G) with hC₁
  set C₂ := Subgroup.centralizer ({d} : Set G) with hC₂
  set d₁ : ↥C₁ := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr hbd.symm⟩ with hd₁
  set Z₁ := Subgroup.centralizer ({d₁} : Set ↥C₁) with hZ₁
  obtain ⟨hWC, hW₀⟩ := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hW
  have hJW : J ≤ W ⊓ C₂ := Subgroup.map_subtype_le _
  have hJC₁ : J ≤ C₁ := hJW.trans (inf_le_left.trans hWC)
  have hJZ : J.subgroupOf C₁ ≤ Z₁ := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [hZ₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hJW hy).2)
  set T₁ := (J.subgroupOf C₁).subgroupOf Z₁ with hT₁
  have hmemT₁ : ∀ z : ↥Z₁, z ∈ T₁ ↔ ((z : ↥C₁) : G) ∈ J := fun z => by
    rw [hT₁, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  let e : ↥T₁ ≃* ↥J := (Subgroup.subgroupOfEquivOfLe hJZ).trans
    (Subgroup.subgroupOfEquivOfLe hJC₁)
  have hJperf : Group.IsPerfect ↥J := by
    have h := (perfect_residual_characterization
      (G := ↥(W ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(W ⊓ C₂)).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Sec14.quotThetaEquiv e.symm) hJ⟩
  set V := (W.subgroupOf C₁).subgroupOf Z₁ with hV
  have hVsn : V.IsSubnormal := hW₀.2.1.subgroupOf
  have hTV : T₁ ≤ V := fun z hz => by
    rw [hV, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (hJW ((hmemT₁ z).mp hz)).1
  have hNJ : W ⊓ C₂ ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (W ⊓ C₂))
  have hVN : V ≤ Subgroup.normalizer (T₁ : Set ↥Z₁) := by
    intro v hv
    have hvW : ((v : ↥C₁) : G) ∈ W := by
      rw [hV, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hv
      exact hv
    have hvC : ((v : ↥C₁) : G) ∈ C₂ := by
      have h1 : (v : ↥C₁) * d₁ = d₁ * (v : ↥C₁) :=
        Subgroup.mem_centralizer_singleton_iff.mp v.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)
    have hvN := hNJ ⟨hvW, hvC⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hmemT₁, hmemT₁]
    simpa using (Subgroup.mem_normalizer_iff.mp hvN ((z : ↥C₁) : G))
  have hTVn : (T₁.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTV).mpr hVN
  exact Subgroup.IsSubnormal.trans hTV hTVn.isSubnormal hVsn

end General

section Step5

variable {G : Type} [Group G] [Finite G]

theorem step5 (h415 : Sec4.Item4_15) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hK2 : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A a)
    (hφ : Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2))
    (hS3 : Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3))) (hcK : c ∈ K) :
    a ∈ L ∧ A ⊓ L = Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧
      ∃ L₀ ∈ thetaComponentsAt 3 c, L₀ ≠ L ∧
        Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6)) ∧
        c ∈ L₀ ∧ a ∈ Sec4.thetaQuotCentralizer L₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := h.toPartTwoStanding
  have hFE := h.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨haA, ha3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have ha3' : a ^ 3 = 1 := hAe.2 a haA
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central h.mem_L hLc
  have hac : a ∉ Subgroup.zpowers c := fun h' => haB ((Subgroup.zpowers_le.mpr hcB) h')
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hAH := le_normalizer_zpowers_of_isElemAbelian hAe haA
  obtain ⟨hJp, -⟩ := Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
    (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  obtain ⟨φ⟩ := hφ
  have hKθ : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hJp φ
  have h9 : Nat.card (A ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hAe h27 hK.1 hK.2.1 hAH hJp φ
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_j2 h415 hKθ
  have haK : a ∉ K := not_mem_of_center_eq_bot hK.1 hZK ha3' ha1
  have hAa : A = Subgroup.zpowers a ⊔ (A ⊓ K) :=
    (eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left) le_sup_right h9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h' => haK h'.2)).symm
  obtain ⟨eS3⟩ := hS3
  obtain ⟨y, hy1, hy3⟩ := exists_ne_one_pow_three_of_perm3 eS3
  have hy'3 : (y : MulAut A) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hy'1 : (y : MulAut A) ≠ 1 := fun h' => hy1 (Subtype.ext h')
  have hyT : (y : MulAut A) ∈ transvectionGroup A ⟨c, hcA⟩ :=
    mem_transvectionGroup_of_mem_wStar h45 hK2 h hty (Sec13.Holds134.autIn_le_wStar K y.2)
      (k := 1) (by simpa using hy'3)
  obtain ⟨g, hgN, hgK, hgy⟩ := Sec4.mem_autIn_iff.mp y.2
  obtain ⟨k, m, hm, hgm, -⟩ := exists_threePart g
  have hnK : g ^ m ∈ K := K.pow_mem hgK m
  have hnA : g ^ m ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hgN m
  have hσn : A.normalizerMonoidHom ⟨g ^ m, hnA⟩ = (y : MulAut A) ^ m := by
    have e : (⟨g ^ m, hnA⟩ : Subgroup.normalizer (A : Set G)) = ⟨g, hgN⟩ ^ m :=
      Subtype.ext (by simp)
    rw [e, map_pow, hgy]
  have hσn1 : (y : MulAut A) ^ m ≠ 1 := by
    intro h'
    have hord : orderOf (y : MulAut A) = 3 := orderOf_eq_prime hy'3 hy'1
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hord] at this
    exact hm this
  have hσnT : (y : MulAut A) ^ m ∈ transvectionGroup A ⟨c, hcA⟩ := pow_mem hyT m
  have hnc : g ^ m * c = c * g ^ m := by
    have h1 := hσnT.1
    rw [← hσn] at h1
    have h2 : g ^ m * c * (g ^ m)⁻¹ = c := by
      have := congrArg Subtype.val h1
      rwa [Sec4.normalizerMonoidHom_apply_coe] at this
    calc g ^ m * c = g ^ m * c * (g ^ m)⁻¹ * g ^ m := by group
      _ = c * g ^ m := by rw [h2]
  have hnmove : ∃ x ∈ A, g ^ m * x * (g ^ m)⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hσn1
    rw [← hσn]
    ext x
    rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
    exact hcon x x.2
  have hSyl := exists_sylow_le_centralizer hAe hKθ h9 hcA hcK hnK hnA hgm hnc hnmove
  obtain ⟨hq, htc, hcI, -⟩ := Sec13.residual_facts h415 hKθ hcK hc1 hSyl
  set I := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) with hI
  have hG4c : SectionFourHyp (Subgroup.centralizer ({c} : Set G)) :=
    (centralizer_setup hst hAF h27 hcA hc1).1
  obtain ⟨L₀, hL₀, hIL₀⟩ :=
    Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4c h.isE27 haA hcA ha1 hK.1 hq
  have hcL₀ : c ∈ L₀ := hIL₀ hcI
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)
  have hAN₀ : A ≤ Subgroup.normalizer (L₀ : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp
      (orderOf_eq_prime hc3 hc1) hL₀ hA3 (le_normalizer_zpowers_of_isElemAbelian hAe hcA)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L₀ ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    intro x hx
    obtain ⟨i, -, y₀, hy₀, hxy⟩ := Sec13.exists_pow_mul_of_mem hAe haA hAa hx.1
    have hθ : ∀ j ∈ I, j⁻¹ * (y₀ * j * y₀⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L₀ := by
      intro j hj
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hx.2).2 j (hIL₀ hj)
      have hjK : j ∈ K := ((Subgroup.map_subtype_le _ : I ≤ K ⊓ _) hj).1
      have hxjK : x * j * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK.2.1 hx.1) j).mp hjK
      have haw : Commute a (x * j * x⁻¹) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hKa hxjK)).symm
      have e : y₀ * j * y₀⁻¹ = x * j * x⁻¹ := by
        have hy₀x : y₀ = (a ^ i)⁻¹ * x := by rw [hxy]; group
        rw [hy₀x]
        calc (a ^ i)⁻¹ * x * j * ((a ^ i)⁻¹ * x)⁻¹ = (a ^ i)⁻¹ * ((x * j * x⁻¹) * a ^ i) := by
              group
          _ = x * j * x⁻¹ := by rw [← (haw.pow_left i).eq, inv_mul_cancel_left]
      rw [e]
      exact h1
    have hy₀c := mem_zpowers_of_forall_mem_theta h415 hcK hc1 hKθ hSyl hIL₀ hy₀.2
      (hcomm _ hy₀.1 _ hcA) (hAe.2 _ hy₀.1) hθ
    rw [hxy]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i) hy₀c
  have hD9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    card_zpowers_sup_eq_nine hAe hcA haA hc1 ha1 hac
  have hLL₀ : L₀ ≠ L := by
    intro heq
    apply haB
    have hle : A ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      heq ▸ hCA
    have heqB : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hD9, h.card_B])
    have : a ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
      heqB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    exact this.2
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hALC : A ⊓ L ≤ A ⊓ Sec4.thetaQuotCentralizer L₀ := fun x hx =>
    ⟨hx.1, mem_thetaQuotCentralizer_of_ne h.mem_thetaComponentsAt hL₀ (Ne.symm hLL₀) hx.2
      (hAN₀ hx.1)⟩
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine_bar h.isE27 hcA hc1 h.mem_L hLc hZ h.card_B h.sup_eq
  have hAL : A ⊓ L = Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (hALC.trans hCA) (by rw [hD9, hAL9])
  have haL : a ∈ L := (hAL ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a) : a ∈ A ⊓ L).2
  have haC₀ : a ∈ Sec4.thetaQuotCentralizer L₀ := (hALC ⟨haA, haL⟩).2
  refine ⟨haL, hAL, L₀, hL₀, hLL₀, ?_, hcL₀, haC₀⟩
  have hL₀q := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL₀
  have hL₀eq := eq_residual_sup_theta hL₀q.1 (k := 1) (by simpa using ha3') haC₀
  set J := inSubgroup perfectResidual (L₀ ⊓ Subgroup.centralizer ({a} : Set G)) with hJ
  have hJL₀ : J ≤ L₀ := (Subgroup.map_subtype_le _).trans inf_le_left
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hJL₀ hL₀eq
  have hJq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hL₀q
  have hIJ : I ≤ J := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _)
    (le_inf hIL₀ ((Subgroup.map_subtype_le _).trans (inf_le_left.trans hKa)))
  have hac' : a * c = c * a := hcomm a haA c hcA
  obtain ⟨T, hT, hTI⟩ := Sec14.exists_mem_thetaComponentsAt_of_residual hac' hK.1 hq
  obtain ⟨T'', hT'', rfl⟩ := hT
  rw [← hI] at hTI
  have hTJ := residual_mem_thetaComponents hac'.symm hL₀ hJq
  have hT''le : T'' ≤ (J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (Subgroup.centralizer ({(⟨a, Subgroup.mem_centralizer_singleton_iff.mpr hac'⟩ :
        ↥(Subgroup.centralizer ({c} : Set G)))} : Set ↥(Subgroup.centralizer ({c} : Set G)))) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    apply hIJ
    rw [← hTI]
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hT''1 : T'' ≠ ⊥ := by
    intro hb
    have hc' := hcI
    rw [← hTI, hb] at hc'
    obtain ⟨_, ⟨z, hz, rfl⟩, hzc⟩ := hc'
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hz
    apply hc1
    rw [← hzc, hz]
    rfl
  have heqT := theta_component_eq_of_perfect_le Nat.prime_three hT'' hTJ hT''1 hT''.1 le_rfl hT''le
  have hJI : J ≤ I := by
    intro j hj
    rw [← hTI, heqT]
    have hjC : j ∈ Subgroup.centralizer ({c} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt hL₀ (hJL₀ hj)
    have hja : j * a = a * j :=
      Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _ hj).2)
    have hjZ : (⟨j, hjC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        Subgroup.centralizer ({(⟨a, Subgroup.mem_centralizer_singleton_iff.mpr hac'⟩ :
          ↥(Subgroup.centralizer ({c} : Set G)))} : Set ↥(Subgroup.centralizer ({c} : Set G))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hja
    exact ⟨⟨j, hjC⟩, ⟨⟨⟨j, hjC⟩, hjZ⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hj),
      rfl⟩, rfl⟩
  have hIJeq : I = J := le_antisymm hIJ hJI
  exact Sec13.isTripleCover_of_mulEquiv
    ((Sec14.quotThetaEquiv (MulEquiv.subgroupCongr hIJeq)).trans eJ) htc

end Step5

end CFSG.RankThree.PartTwo.Sec12.Proof128
