module

public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
public import CFSG.RankThree.PartTwo.Sec11.DataExistsAct
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.Skeleton

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

namespace Item1115Bypass

theorem isPGroup_closure_pair {M : Type*} [Group M] {σ τ : M} (hστ : σ * τ = τ * σ)
    (hσ3 : σ ^ 3 = 1) (hτ3 : τ ^ 3 = 1) : IsPGroup 3 (Subgroup.closure ({σ, τ} : Set M)) := by
  intro g
  obtain ⟨m, n, hg⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hστ g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hc : Commute (σ ^ m) (τ ^ n) := Commute.zpow_zpow hστ m n
  have h1 : (σ ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow]
  have h2 : (τ ^ n) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτ3, one_zpow]
  rw [Subgroup.coe_pow, pow_one, hg, hc.mul_pow, h1, h2, mul_one, Subgroup.coe_one]

theorem exists_pow_mul_isInnerAut_of_classical {X : Type} [Group X]
    (hX : IsFieldCentClassical X) {σ τ : MulAut X} (hσ3 : σ ^ 3 = 1) (hσ : ¬ IsInnerAut σ)
    (hτ3 : τ ^ 3 = 1) (hστ : σ * τ = τ * σ) : ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  rcases hX with ⟨K, _, _, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨p, f, K, _, h, hq, hq2, ⟨e⟩⟩
  · exact exists_pow_mul_isInnerAut_of_mulEquiv_psl2 e (isPGroup_closure_pair hστ hσ3 hτ3)
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hσ3 hσ hτ3
  · by_cases hτ : IsInnerAut τ
    · exact ⟨0, by rwa [pow_zero, one_mul]⟩
    · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
      exact exists_pow_mul_isInnerAut_of_mulEquiv_projSL hK (e.trans φ.symm) hσ3 hσ hτ3 hτ
  · by_cases hτ : IsInnerAut τ
    · exact ⟨0, by rwa [pow_zero, one_mul]⟩
    · exact exists_pow_mul_isInnerAut_of_mulEquiv_unitaryPSU h hq hq2 e hσ3 hσ hτ3 hτ

theorem center_eq_bot_of_classical {X : Type} [Group X] (hX : IsFieldCentClassical X) :
    Subgroup.center X = ⊥ := by
  rcases hX with ⟨K, _, _, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨p, f, K, _, h, hq, hq2, ⟨e⟩⟩
  · exact center_eq_bot_of_mulEquiv_of_center_eq_bot e (CFSG.GorensteinWalter.psl2_center_eq_bot K)
  · exact center_eq_bot_of_mulEquiv_of_center_eq_bot e (center_projectiveSL_three_eq_bot hK)
  · exact center_eq_bot_of_mulEquiv_of_center_eq_bot e (center_unitaryPSU_three_eq_bot h hq2)

theorem eq_of_conj_eq {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {a b : X}
    (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have hc : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : a * z * a⁻¹ = b * z * b⁻¹ := by
      simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut X => φ z) h
    calc z * (b⁻¹ * a) = b⁻¹ * (b * z * b⁻¹) * a := by group
      _ = b⁻¹ * (a * z * a⁻¹) * a := by rw [hz]
      _ = b⁻¹ * a * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem conj_apply_eq {X : Type*} [Group X] (α : MulAut X) (y : X) :
    MulAut.conj (α y) = α * MulAut.conj y * α⁻¹ := by
  ext z
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem false_of_mem_zpowers_of_pow_three {X N : Type*} [Group X] [Group N] (τ : N →* MulAut X)
    {E T W : N} (hT3 : T ^ 3 = E) (hEW : E * W = W * E) (hE3 : E ^ 3 = 1)
    (hEout : ¬ IsInnerAut (τ E)) (hW : IsInnerAut (τ W))
    (hmem : τ (T * W⁻¹) ∈ Subgroup.zpowers (τ E)) : False := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hT : τ T = τ E ^ m * τ W := by
    rw [hm, map_mul, map_inv, inv_mul_cancel_right]
  have hc : Commute (τ E ^ m) (τ W) := by
    have h1 : Commute (τ E) (τ W) := by
      change τ E * τ W = τ W * τ E
      rw [← map_mul, hEW, map_mul]
    exact h1.zpow_left m
  have hE3' : τ E ^ 3 = 1 := by rw [← map_pow, hE3, map_one]
  have hEm : (τ E ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hE3', one_zpow]
  have hEW3 : τ E = τ W ^ 3 := by
    rw [← hT3, map_pow, hT, hc.mul_pow, hEm, one_mul]
  apply hEout
  rw [hEW3]
  exact pow_mem hW 3

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_of_eq_one {Y : Subgroup G} (y : Subgroup.normalizer (Y : Set G))
    (hy : Sec4.thetaQuotMulAut Y (Sec4.compAction Y y) = 1) :
    (y : G) ∈ Sec4.thetaQuotCentralizer Y :=
  ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩

theorem thetaQuotMulAut_eq_one_of_mem {Y : Subgroup G} {x : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer Y) (hxN : x ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨x, hxN⟩) = 1 := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl : y = ⟨x, hxN⟩ := Subtype.ext hyx
  exact hy

theorem commutator_mem_theta_of_mem_thetaQuotCentralizer {Y K : Subgroup G} (hKY : K ≤ Y)
    {u : G} (huY : u ∈ Sec4.thetaQuotCentralizer Y)
    (huK : u ∈ Subgroup.normalizer (K : Set G)) :
    ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  intro k hk
  have h1 : u * k * u⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp huK k).mp hk) (K.inv_mem hk)
  have h2 : u * k * u⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    have h3 := (Sec6.mem_thetaQuotCentralizer_iff.mp huY).2 k (hKY hk)
    have e : u * k * u⁻¹ * k⁻¹ = k * (k⁻¹ * (u * k * u⁻¹)) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y (hKY hk)) _).mp h3
  exact Sec13.inf_inSubgroup_theta_le hKY ⟨h1, h2⟩

theorem exists_mul_mem_thetaQuotCentralizer {Y K : Subgroup G} {c t : G}
    (hY : IsFieldCentClassical (Y ⧸ aschbacherSolvableCore 3 Y))
    (hout : Sec4.InducesOuterTheta c Y) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htc : t * c = c * t)
    (ht3 : t ^ 3 ∈ Sec4.thetaQuotCentralizer Y) :
    ∃ k₀ ∈ K, ∃ i : ℕ, c ^ i * t * k₀⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
  obtain ⟨hcN, hαout⟩ := hout
  set N := Subgroup.normalizer (Y : Set G) with hNdef
  set τ : N →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y) with hτ
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hα
  have hτC : τ ⟨c, hcN⟩ = α := rfl
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [← hτC, ← map_pow, h1, map_one]
  have hβ3 : τ ⟨t, htN⟩ ^ 3 = 1 := by
    have h1 : (⟨t, htN⟩ : N) ^ 3 = ⟨t ^ 3, pow_mem htN 3⟩ := Subtype.ext (by simp)
    rw [← map_pow, h1]
    exact thetaQuotMulAut_eq_one_of_mem ht3 _
  have hαβ : α * τ ⟨t, htN⟩ = τ ⟨t, htN⟩ * α := by
    have h1 : (⟨c, hcN⟩ : N) * ⟨t, htN⟩ = ⟨t, htN⟩ * ⟨c, hcN⟩ := Subtype.ext htc.symm
    rw [← hτC, ← map_mul, h1, map_mul]
  obtain ⟨i, yb, hyb⟩ := exists_pow_mul_isInnerAut_of_classical hY hα3 hαout hβ3 hαβ
  have hybα : α yb = yb := by
    apply eq_of_conj_eq (center_eq_bot_of_classical hY)
    have h1 : Commute α (α ^ i * τ ⟨t, htN⟩) := (Commute.self_pow α i).mul_right hαβ
    rw [conj_apply_eq, hyb, h1.eq, mul_inv_cancel_right]
  obtain ⟨hF, -⟩ := fieldCent_facts_of_classical hY hα3 hαout
  rcases hF with ⟨hQ, hZF⟩ | hsol
  swap
  · exact (fieldCent_false_of_isSolvable hcN hc3 hK hsol).elim
  set F := α.toMonoidHom.eqLocus (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)) with hF
  set M := (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) with hM
  obtain ⟨K', hK', rfl⟩ := hK
  have hrange : (cMap Y c).range = F := range_cMap hcN hc3
  have hmem : ∀ m, cMap Y c m ∈ F := fun m => hrange ▸ ⟨m, rfl⟩
  set ψ : M →* F := (cMap Y c).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hrange] at hz
    obtain ⟨m, rfl⟩ := hz
    exact ⟨m, rfl⟩
  have hsimple : IsSimpleGroup F := by
    have := hQ.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZF).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have htop : K'.map ψ = ⊤ := by
    rcases (hK'.2.1.map hψs).eq_bot_or_top_of_isSimpleGroup hsimple with h | h
    · refine absurd ?_ (fieldCent_map_cMap_ne_bot hK')
      rw [Subgroup.eq_bot_iff_forall]
      rintro _ ⟨k, hk, rfl⟩
      have h1 : ψ k ∈ K'.map ψ := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exact h
  have hybF : yb ∈ F := hybα
  obtain ⟨k, hk, hkyb⟩ : ∃ k ∈ K', ψ k = ⟨yb, hybF⟩ := by
    have h1 : (⟨yb, hybF⟩ : F) ∈ K'.map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkeq⟩ := h1
    exact ⟨k, hk, hkeq⟩
  have hkY : ((k : M) : G) ∈ Y := (k : M).2.1
  have hkyb' : ((⟨(k : G), hkY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = yb :=
    congrArg Subtype.val hkyb
  refine ⟨(k : G), ⟨k, hk, rfl⟩, i, ?_⟩
  have hτW : τ ⟨(k : G), Subgroup.le_normalizer hkY⟩ = MulAut.conj yb := by
    rw [← hkyb']
    exact thetaQuotMulAut_compAction_of_mem Y hkY
  have h1 : τ ((⟨c, hcN⟩ : N) ^ i * ⟨t, htN⟩ * (⟨(k : G), Subgroup.le_normalizer hkY⟩ : N)⁻¹) =
      1 := by
    rw [map_mul, map_mul, map_inv, map_pow, hτC, hτW, hyb, mul_inv_cancel]
  have h2 : (((⟨c, hcN⟩ : N) ^ i * ⟨t, htN⟩ *
      (⟨(k : G), Subgroup.le_normalizer hkY⟩ : N)⁻¹ : N) : G) = c ^ i * t * (k : G)⁻¹ := by
    simp
  rw [← h2]
  exact mem_thetaQuotCentralizer_of_eq_one _ h1

theorem mem_zpowers_of_commutator_mem_theta {L : Subgroup G} {e u : G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L))
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    (heout : ¬ IsInnerAut (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, heN⟩)))
    (he3 : e ^ 3 = 1) (huN : u ∈ Subgroup.normalizer (L : Set G))
    (huK : ∀ k ∈ sec11K L e, u * k * u⁻¹ * k⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (sec11K L e)) :
    Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨u, huN⟩) ∈
      Subgroup.zpowers (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, heN⟩)) := by
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, heN⟩) with hα
  set β := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨u, huN⟩) with hβ
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨hZ, hQ, -⟩ := fixedPoints_facts_of_isList1016 hL hα3 heout
  have hfix : ∀ z, α z = z → β z = z := by
    intro z hz
    have hz' : z ∈ (kMap L e).range := by
      rw [range_kMap_eq heN he3 hQ.1, range_cMap heN he3]
      exact hz
    obtain ⟨k, rfl⟩ := hz'
    obtain ⟨y, hy, hyk⟩ := huK k k.2
    have hyk' : (y : G) = u * (k : G) * u⁻¹ * (k : G)⁻¹ := hyk
    have hθs := (solvable_prime_complement_core_characterization
      (H := sec11K L e) Nat.prime_three).1
    have hker := le_ker_kMap_of_normal_solvable heN he3 hQ hZ _ hθs hy
    rw [MonoidHom.mem_ker] at hker
    have hukL : u * (k : G) * u⁻¹ ∈ L := by
      have hkL : (k : G) ∈ L := sec11K_le L e k.2
      exact (Subgroup.mem_normalizer_iff.mp huN _).mp hkL
    have e1 : (⟨u * (k : G) * u⁻¹, hukL⟩ : L) =
        Subgroup.inclusion (sec11K_le L e) y * Subgroup.inclusion (sec11K_le L e) k :=
      Subtype.ext (by
        change u * (k : G) * u⁻¹ = (y : G) * (k : G)
        rw [hyk']
        group)
    change β ((Subgroup.inclusion (sec11K_le L e) k : L) :
      L ⧸ aschbacherSolvableCore 3 L) = _
    rw [hβ, Sec4.thetaQuotMulAut_mk]
    have e2 : Sec4.compAction L ⟨u, huN⟩ (Subgroup.inclusion (sec11K_le L e) k) =
        ⟨u * (k : G) * u⁻¹, hukL⟩ := Subtype.ext rfl
    rw [e2, e1, QuotientGroup.mk_mul]
    have e3 : ((Subgroup.inclusion (sec11K_le L e) y : L) :
        L ⧸ aschbacherSolvableCore 3 L) = 1 := hker
    rw [e3, one_mul]
    rfl
  exact mem_zpowers_of_fixes_of_isList1016 hL hα3 heout hfix

theorem not_mem_closure_of_mem_closure_pair {M : Type*} [Group M] {a c d e : M}
    (hac : a * c = c * a) (ha3 : a ^ 3 = 1) (hacd : a ∉ Subgroup.closure ({c, d} : Set M))
    (he : e ∈ Subgroup.closure ({a, c} : Set M)) (hec : e ∉ Subgroup.zpowers c) :
    e ∉ Subgroup.closure ({c, d} : Set M) := by
  obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hac he
  intro hcd
  by_cases h3 : (3 : ℤ) ∣ m
  · apply hec
    rw [ActOnA.zpow_eq_one_of_dvd ha3 h3, one_mul]
    exact Subgroup.zpow_mem_zpowers c n
  · apply hacd
    refine ActOnA.mem_of_zpow_mem ha3 ?_ h3
    have e1 : a ^ m = a ^ m * c ^ n * (c ^ n)⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ hcd
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n))

end Item1115Bypass

section Main


variable {G : Type} [Group G] [Finite G]

theorem Item1115Bypass.hyp81_swap_of_std (h118 : Item118) {A : Subgroup G} {c : G}
    {L : Subgroup G} {e : G} {R Ye : Subgroup G} (h : Sec11Std G A c L e R Ye) {d g : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, e, d})
    (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgH : g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hgc : g * c * g⁻¹ ∈ Subgroup.closure {c, d})
    (hf : KFacts.InducesStdKind Ye c .field) : Sec8.Hyp81 G A e Ye c where
  toPartTwoStanding := h.toPartTwoStanding
  mem_partTwoF := h.mem_partTwoF
  mem_A := h.a_mem
  ne_one := h.a_ne_one
  mem_thetaComponentsAt := h.mem_thetaComponentsAt_Y
  sectionCentralizer_eq := (h118 G A c L e R Ye h d g hdL hA hgA hgH hgc).2.2
  a_mem := h.mem_A
  a_ne_one := h.ne_one
  inducesStdKind := Or.inl hf
  exists_invariant_two := fun h27 => absurd h.card_eq (Nat.ne_of_gt h27)
  partTwoE_eq := h.partTwoE_eq

theorem Item1115Bypass.false_of_field_of_pow_three (h82 : Sec8.Item82One) (h118 : Item118)
    {A : Subgroup G} {c : G} {L : Subgroup G} {e : G} {R Ye : Subgroup G}
    (h : Sec11Std G A c L e R Ye) {d g : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, e, d}) (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgH : g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hgc : g * c * g⁻¹ ∈ Subgroup.closure {c, d})
    (hf : KFacts.InducesStdKind Ye c .field) {t : G}
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (htc : t * c = c * t) (hte : t * e = e * t)
    (ht3 : t ^ 3 = e) : False := by
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have he3 : e ^ 3 = 1 := h.mem_partTwoF.1.2 e h.a_mem
  have hK := mem_thetaComponentsIn_sec11K_inf h
  have hT := kType119 G A c L e R Ye h d hdL hA
  have hlist := h82 G A e Ye c (hyp81_swap_of_std h118 h hdL hA hgA hgH hgc hf) h.card_eq
  have hcl : IsFieldCentClassical (Ye ⧸ aschbacherSolvableCore 3 Ye) := by
    rcases hlist with ⟨⟨e'⟩⟩ | ⟨p, n, hp, -, -, ⟨e'⟩⟩ | ⟨m, hm, ⟨⟨e'⟩⟩ | hL | hL⟩
    · exact FieldCentRigid82.isFieldCentClassical_of_projSL_two e'
    · exact FieldCentRigid82.isFieldCentClassical_of_projSL_two e'
    · exact FieldCentRigid82.isFieldCentClassical_of_projSL_two e'
    · exact FieldCentRigid82.isFieldCentClassical_of_isoLThreeMinusPi (by omega) hL
    · exact (FieldCentRigid82.false_of_isSLThreePiAt hm hL hf hc3 hK hT).elim
  obtain ⟨-, -, hd1⟩ := h.not_mem_facts hdL hA
  have hdK := h.d_mem_sec11K hdL
  have hK1 : sec11K L e ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have htY := h.mem_normalizer_Y hK1 htN hte
  have ht3Y : t ^ 3 ∈ Sec4.thetaQuotCentralizer Ye := by
    rw [ht3]
    exact c_mem_thetaQuotCentralizer h.mem_thetaComponentsAt_Y
  obtain ⟨k₀, hk₀K, i, hu⟩ := exists_mul_mem_thetaQuotCentralizer hcl
    (KFacts.InducesStdKind.inducesOuterTheta Ye hf (by decide)) hc3 hK htY htc ht3Y
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hk₀L : k₀ ∈ L := sec11K_le L e hk₀K
  have hk₀e : k₀ * e = e * k₀ := Subgroup.mem_centralizer_singleton_iff.mp
    (((Subgroup.map_subtype_le _).trans inf_le_right : sec11K L e ≤ _) hk₀K)
  have hcK : c ∈ Subgroup.normalizer (sec11K L e : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp
      (hLc (sec11K_le L e hy)))
  have hcL : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  have htK : t ∈ Subgroup.normalizer (sec11K L e : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Item1116Proof.mem_normalizer_inf htN
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hte)))
  have huK : c ^ i * t * k₀⁻¹ ∈ Subgroup.normalizer (sec11K L e : Set G) :=
    mul_mem (mul_mem (pow_mem hcK i) htK) (inv_mem (Subgroup.le_normalizer hk₀K))
  have huN : c ^ i * t * k₀⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (mul_mem (pow_mem hcL i) htN) (inv_mem (Subgroup.le_normalizer hk₀L))
  have hcomm := commutator_mem_theta_of_mem_thetaQuotCentralizer h.sec11K_le hu huK
  have heN := h.toHyp81.a_mem_normalizer
  have heout := h.toHyp81.not_isInnerAut_induced
  have hz := mem_zpowers_of_commutator_mem_theta h.isList1016 heN heout he3 huN hcomm
  set NL := Subgroup.normalizer (L : Set G) with hNL
  set τL : NL →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hτL
  change τL ⟨_, huN⟩ ∈ Subgroup.zpowers (τL ⟨e, heN⟩) at hz
  have hτc : τL ⟨c, hcL⟩ = 1 :=
    thetaQuotMulAut_eq_one_of_mem (c_mem_thetaQuotCentralizer h.mem_thetaComponentsAt) hcL
  have hU : (⟨c ^ i * t * k₀⁻¹, huN⟩ : NL) =
      (⟨c, hcL⟩ : NL) ^ i * ((⟨t, htN⟩ : NL) * (⟨k₀, Subgroup.le_normalizer hk₀L⟩ : NL)⁻¹) :=
    Subtype.ext (by simp [mul_assoc])
  rw [hU, map_mul, map_pow, hτc, one_pow, one_mul] at hz
  refine false_of_mem_zpowers_of_pow_three τL (E := ⟨e, heN⟩) (T := ⟨t, htN⟩)
    (W := ⟨k₀, Subgroup.le_normalizer hk₀L⟩) (Subtype.ext ?_) (Subtype.ext ?_) (Subtype.ext ?_)
    heout ⟨_, (thetaQuotMulAut_compAction_of_mem L hk₀L).symm⟩ hz
  · simpa using ht3
  · exact hk₀e.symm
  · simpa using he3

theorem item11133Field_of_item82 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h82 : Sec8.Item82One) (h118 : Item118) : Item11133Field := by
  intro G _ _ A c L a R Y d x s r g h _hf _hra hrs e he hec
  have hAe := h.mem_partTwoF.1
  have hac : a * c = c * a :=
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, h.a_mem⟩ ⟨c, h.mem_A⟩)
  obtain ⟨-, hacd, -⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have heA : e ∈ A := by
    refine (Subgroup.closure_le A).mpr ?_ he.2
    rintro y (rfl | rfl)
    exacts [h.a_mem, h.mem_A]
  have hecd := Item1115Bypass.not_mem_closure_of_mem_closure_pair hac (hAe.2 a h.a_mem) hacd
    he.2 hec
  obtain ⟨Ye, hYe, hKYe⟩ := exists_mem_thetaComponentsAt_sec11K_le h45 h48 h.toSec11Std h.inf_eq
    h.closure_eq heA hecd
  refine ⟨Ye, hYe, hKYe, fun hfe => ?_⟩
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hYe hKYe
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp he.1
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hr3 := Item1116Proof.exists_pow_eq_one_of_mem h hrR
  have h3n : (3 : ℤ) ∣ n := by
    by_contra h3
    apply hrs
    have hre : r ∈ Subgroup.zpowers e := by
      rw [← hn]
      exact Item1116Proof.mem_zpowers_zpow_of_not_dvd hr3 h3
    have hacs : Subgroup.closure ({a, c} : Set G) ≤ Subgroup.closure {a, s} := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h.c_mem_zpowers_s
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact hacs (Subgroup.zpowers_le.mpr he.2 hre)
      · exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact h.a_mem_closure
      · exact Subgroup.subset_closure (by simp)
  obtain ⟨m, rfl⟩ := h3n
  have ht3 : (r ^ m) ^ 3 = e := by
    rw [← hn, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  obtain ⟨hRc, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  have htR : r ^ m ∈ R := R.zpow_mem hrR m
  have htc : r ^ m * c = c * r ^ m := Subgroup.mem_centralizer_singleton_iff.mp (hRc htR)
  have hte : r ^ m * e = e * r ^ m := by
    rw [← ht3]
    exact (Commute.self_pow (r ^ m) 3).eq
  exact Item1115Bypass.false_of_field_of_pow_three h82 h118 hstd h.inf_eq hA' h.g_mem.2
    h.g_not_mem h.conj_mem hfe (hRL htR) htc hte ht3

end Main

end CFSG.RankThree.PartTwo.Sec11
