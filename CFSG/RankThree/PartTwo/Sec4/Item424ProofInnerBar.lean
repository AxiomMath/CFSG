module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensus
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Proof

section ThetaLift

variable {H : Type*} [Group H] [Finite H]

theorem card_comap_mk (K : Subgroup (H ⧸ aschbacherSolvableCore 3 H)) :
    Nat.card (K.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) =
      Nat.card K * Nat.card (aschbacherSolvableCore 3 H) := by
  set θ := aschbacherSolvableCore 3 H
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' θ))
  have h2 : (K.comap (QuotientGroup.mk' θ)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective θ)
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [h2] at h1
  have h5 : Nat.card (K.comap (QuotientGroup.mk' θ)) * K.index =
      (Nat.card K * Nat.card θ) * K.index := by
    rw [h1, h4, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem card_map_mk_of_isPGroup {P : Subgroup H} (hP : IsPGroup 3 P) :
    Nat.card (P.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) = Nat.card P := by
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hP
  have h1 : Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 H) '' (P : Set H)) =
      Nat.card (P : Set H) := Nat.card_image_of_injOn hinj
  have e1 : Nat.card (P.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) =
      Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 H) '' (P : Set H)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e1, h1]
  rfl

theorem exists_pGroup_cover {P : Subgroup H} (hP : IsPGroup 3 P)
    {F : Subgroup (H ⧸ aschbacherSolvableCore 3 H)} (hF : IsPGroup 3 F)
    (hPF : P.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤ F) :
    ∃ F₃ : Subgroup H, P ≤ F₃ ∧ IsPGroup 3 F₃ ∧
      F₃.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = F := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set F₁ : Subgroup H := F.comap π with hF₁
  have hPF₁ : P ≤ F₁ := fun x hx => hPF (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow (hP.comap_subtype (K := F₁))
  set F₃ : Subgroup H := (S : Subgroup F₁).map F₁.subtype with hF₃
  have hF₃F₁ : F₃ ≤ F₁ := Subgroup.map_subtype_le _
  have hPF₃ : P ≤ F₃ := fun x hx =>
    ⟨⟨x, hPF₁ hx⟩, hPS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hF₃p : IsPGroup 3 F₃ := S.2.map F₁.subtype
  refine ⟨F₃, hPF₃, hF₃p, ?_⟩
  have hle : F₃.map π ≤ F := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact hF₃F₁ hx
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hF
  have hcardF₁ : Nat.card F₁ = Nat.card F * Nat.card θ := card_comap_mk F
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hfac : (Nat.card F₁).factorization 3 = j := by
    rw [hcardF₁, hj, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hθ3]
    simp [Nat.prime_three.factorization_pow]
  have hSc : Nat.card S = 3 ^ j := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hF₃c : Nat.card F₃ = 3 ^ j := by
    rw [hF₃, Subgroup.card_map_of_injective F₁.subtype_injective]
    exact hSc
  have hmapc : Nat.card (F₃.map π) = Nat.card F₃ := card_map_mk_of_isPGroup hF₃p
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmapc, hF₃c, hj])

theorem exists_normalizer_lift {P : Subgroup H} (hP : IsPGroup 3 P) {n : H}
    (hy : (n : H ⧸ aschbacherSolvableCore 3 H) ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) :
        Subgroup (H ⧸ aschbacherSolvableCore 3 H)) : Set (H ⧸ aschbacherSolvableCore 3 H))) :
    ∃ w ∈ Subgroup.normalizer (P : Set H),
      ∃ e ∈ P.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)),
        (n : H ⧸ aschbacherSolvableCore 3 H) = e * (w : H ⧸ aschbacherSolvableCore 3 H) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ē : Subgroup (H ⧸ θ) := P.map π with hĒ
  set Ph : Subgroup H := Ē.comap π with hPh
  have hAPh : P ≤ Ph := fun x hx => Subgroup.mem_map_of_mem _ hx
  set S₂ : Subgroup H := P.map (MulAut.conj n).toMonoidHom with hS₂
  have hnorm := Subgroup.mem_normalizer_iff.1 hy
  have hS₂Ph : S₂ ≤ Ph := by
    rintro _ ⟨z, hz, rfl⟩
    show π (n * z * n⁻¹) ∈ Ē
    rw [map_mul, map_mul, map_inv]
    exact (hnorm (π z)).1 (Subgroup.mem_map_of_mem _ hz)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hcardPh : Nat.card Ph = 3 ^ k * Nat.card θ := by
    rw [hPh, card_comap_mk, hĒ, card_map_mk_of_isPGroup hP, hk]
  have hfac : (Nat.card Ph).factorization 3 = k := by
    rw [hcardPh, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hθ3]
    simp [Nat.prime_three.factorization_pow]
  have hcardS₂ : Nat.card S₂ = 3 ^ k := by
    rw [hS₂, Subgroup.card_map_of_injective (MulAut.conj n).injective, hk]
  have hA₁ : Nat.card (P.subgroupOf Ph) = 3 ^ (Nat.card ↥Ph).factorization 3 := by
    rw [hfac, ← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPh).toEquiv
  have hA₂ : Nat.card (S₂.subgroupOf Ph) = 3 ^ (Nat.card ↥Ph).factorization 3 := by
    rw [hfac, ← hcardS₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂Ph).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Ph) (Sylow.ofCard (S₂.subgroupOf Ph) hA₂)
    (Sylow.ofCard (P.subgroupOf Ph) hA₁)
  have hconj : ∀ z ∈ S₂, (g : H) * z * (g : H)⁻¹ ∈ P := by
    intro z hz
    have hz' : (⟨z, hS₂Ph hz⟩ : ↥Ph) ∈ S₂.subgroupOf Ph := Subgroup.mem_subgroupOf.2 hz
    have h3 : ((g • (Sylow.ofCard (S₂.subgroupOf Ph) hA₂) : Sylow 3 ↥Ph) : Subgroup ↥Ph) =
        P.subgroupOf Ph := by
      rw [hg]
      rfl
    have h2 : (g : ↥Ph) * ⟨z, hS₂Ph hz⟩ * g⁻¹ ∈ (P.subgroupOf Ph) := by
      rw [← h3, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨z, hS₂Ph hz⟩ : ↥Ph) (MulAut.conj g) _ hz'
    exact Subgroup.mem_subgroupOf.1 h2
  set w₀ : H := (g : H) * n with hw₀
  have hmap : P.map (MulAut.conj w₀).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have : w₀ * a * w₀⁻¹ = (g : H) * (n * a * n⁻¹) * (g : H)⁻¹ := by rw [hw₀]; group
    show w₀ * a * w₀⁻¹ ∈ P
    rw [this]
    exact hconj _ ⟨a, ha, rfl⟩
  have hw₀N : w₀ ∈ Subgroup.normalizer (P : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj w₀).injective])
  refine ⟨w₀, hw₀N, ((g : H) : H ⧸ θ)⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ g.2
  · show (n : H ⧸ θ) = ((g : H) : H ⧸ θ)⁻¹ * ((g * n : H) : H ⧸ θ)
    rw [QuotientGroup.mk_mul]
    group

end ThetaLift

end Item424Proof

open Item424Proof

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

theorem isPGroup_inf_subgroupOf (h : Config424 G A L a c K) :
    IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x =>
  ⟨1, Subtype.ext (Subtype.ext (by simpa using h.pow_three _ (Subgroup.mem_subgroupOf.mp x.2).1))⟩

theorem isElemAbelian_inf_subgroupOf (h : Config424 G A L a c K) :
    CFSG.Assembly.IsElemAbelian 3 ((A ⊓ L).subgroupOf L) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
  · exact h.comm _ (Subgroup.mem_subgroupOf.mp x.2).1 _ (Subgroup.mem_subgroupOf.mp y.2).1
  · exact Subtype.ext (by simpa using h.pow_three _ (Subgroup.mem_subgroupOf.mp hy).1)

theorem isElemAbelian_imageModTheta_inf (h : Config424 G A L a c K) :
    CFSG.Assembly.IsElemAbelian 3 (Sec8.imageModTheta L (A ⊓ L)) :=
  isElemAbelian_map _ h.isElemAbelian_inf_subgroupOf

theorem card_imageModTheta_inf (h : Config424 G A L a c K) :
    Nat.card (Sec8.imageModTheta L (A ⊓ L)) = Nat.card (A ⊓ L : Subgroup G) := by
  rw [Sec8.imageModTheta, card_map_mk_of_isPGroup h.isPGroup_inf_subgroupOf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem eq_of_mk_eq (h : Config424 G A L a c K) {x y : L} (hx : (x : G) ∈ A) (hy : (y : G) ∈ A)
    (hxy : (x : L ⧸ aschbacherSolvableCore 3 L) = (y : L ⧸ aschbacherSolvableCore 3 L)) :
    x = y :=
  injOn_mk_of_isPGroup Nat.prime_three h.isPGroup_inf_subgroupOf
    (Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩) (Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩) hxy

theorem commute_of_closure (h : Config424 G A L a c K) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) {f : G} (hc₀ : c₀ * f = f * c₀) (hd : d * f = f * d) :
    ∀ y ∈ A, y * f = f * y := by
  have hle : A ≤ Subgroup.centralizer ({f} : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl
    · exact (h.a_comm f).symm
    · exact hc₀
    · exact hd
  exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem maximal_imageModTheta_inf (h : Config424 G A L a c K) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) :
    Maximal (fun B : Subgroup (L ⧸ aschbacherSolvableCore 3 L) =>
      CFSG.Assembly.IsElemAbelian 3 B) (Sec8.imageModTheta L (A ⊓ L)) := by
  refine ⟨h.isElemAbelian_imageModTheta_inf, fun B hB hDB => ?_⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  obtain ⟨F₃, hDF, hF₃, hF₃B⟩ := exists_pGroup_cover h.isPGroup_inf_subgroupOf
    (Sec5.isPGroup_of_isElemAbelian hB) hDB
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hF₃
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFB : ∀ f ∈ F₃, π f ∈ B := fun f hf => hF₃B ▸ Subgroup.mem_map_of_mem π hf
  have hFD : F₃ ≤ (A ⊓ L).subgroupOf L := by
    intro f hf
    have hcomm : ∀ x ∈ F₃, x * f = f * x := fun x hx =>
      hinj (F₃.mul_mem hx hf) (F₃.mul_mem hf hx) (by
        rw [map_mul, map_mul, hBc _ (hFB x hx) _ (hFB f hf)])
    have hc₀F : (⟨c₀, hc₀.2⟩ : L) ∈ F₃ := hDF (Subgroup.mem_subgroupOf.mpr hc₀)
    have hdF : (⟨d, hd.2⟩ : L) ∈ F₃ := hDF (Subgroup.mem_subgroupOf.mpr hd)
    have hf3 : (f : G) ^ 3 = 1 := by
      have h1 : f ^ 3 = 1 := hinj (F₃.pow_mem hf 3) F₃.one_mem (by
        rw [map_pow, map_one]
        exact hB.2 _ (hFB f hf))
      simpa using congrArg Subtype.val h1
    have hfA : (f : G) ∈ A := mem_of_maximal_of_commute h.maximal hf3
      (h.commute_of_closure hA (congrArg Subtype.val (hcomm _ hc₀F))
        (congrArg Subtype.val (hcomm _ hdF)))
    exact Subgroup.mem_subgroupOf.mpr ⟨hfA, f.2⟩
  rw [← hF₃B]
  exact Subgroup.map_mono hFD

theorem inf_centralizer_eq (h : Config424 G A L a c K) {c₀ : G} {i : ℤ}
    (hci : c = c₀ * a ^ i) :
    L ⊓ Subgroup.centralizer ({c₀} : Set G) = L ⊓ Subgroup.centralizer ({c} : Set G) := by
  have hai : ∀ x : G, x * a ^ i = a ^ i * x := fun x =>
    (Commute.zpow_right (show Commute x a from h.a_comm x) i).eq
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hci]
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, ?_⟩
    calc x * (c₀ * a ^ i) = (x * c₀) * a ^ i := by group
      _ = (c₀ * x) * a ^ i := by rw [hxc]
      _ = c₀ * a ^ i * x := by rw [mul_assoc, hai x, ← mul_assoc]
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, ?_⟩
    have e : x * c₀ * a ^ i = c₀ * x * a ^ i := by
      calc x * c₀ * a ^ i = x * (c₀ * a ^ i) := by group
        _ = c₀ * a ^ i * x := hxc
        _ = c₀ * x * a ^ i := by rw [mul_assoc, ← hai x, ← mul_assoc]
    exact mul_right_cancel e

theorem imageModTheta_centralizer_eq_centralizer {c₀ : G} (hc₀L : c₀ ∈ L) (hc₀3 : c₀ ^ 3 = 1) :
    Sec8.imageModTheta L (L ⊓ Subgroup.centralizer ({c₀} : Set G)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c₀, hc₀L⟩} : Set _) := by
  have hc₀N : c₀ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hc₀L
  rw [KFacts.imageModTheta_centralizer_eq hc₀N ⟨1, by simpa using hc₀3⟩]
  ext y
  rw [KFacts.mem_barCentralizer_zpowers_iff hc₀N, KFacts.thetaQuotMulAut_compAction_of_mem hc₀L,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc y * QuotientGroup.mk' _ ⟨c₀, hc₀L⟩ =
        (QuotientGroup.mk' _ ⟨c₀, hc₀L⟩ * y * (QuotientGroup.mk' _ ⟨c₀, hc₀L⟩)⁻¹) *
          QuotientGroup.mk' _ ⟨c₀, hc₀L⟩ := by rw [hy]
      _ = QuotientGroup.mk' _ ⟨c₀, hc₀L⟩ * y := by group
  · intro hy
    rw [← hy, mul_inv_cancel_right]

theorem imageModTheta_K_facts (h : Config424 G A L a c K) {c₀ : G} {i : ℤ}
    (hci : c = c₀ * a ^ i) (hc₀L : c₀ ∈ L) (hc₀3 : c₀ ^ 3 = 1) :
    Sec8.imageModTheta L K ∈ thetaComponentsIn (Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c₀, hc₀L⟩} : Set _)) ∧
      Nonempty (Sec8.imageModTheta L K ⧸ aschbacherSolvableCore 3 (Sec8.imageModTheta L K) ≃*
        K ⧸ aschbacherSolvableCore 3 K) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set W := L ⊓ Subgroup.centralizer ({c₀} : Set G) with hW
  have hK : K ∈ thetaComponentsIn W := by
    rw [hW, h.inf_centralizer_eq hci]
    exact h.mem_thetaComponentsIn
  obtain ⟨hKW, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hWL : W ≤ L := inf_le_left
  have hKL : K ≤ L := hKW.trans hWL
  set C := Subgroup.centralizer ({π ⟨c₀, hc₀L⟩} : Set (L ⧸ aschbacherSolvableCore 3 L)) with hC
  have hCW : Sec8.imageModTheta L W = C := imageModTheta_centralizer_eq_centralizer hc₀L hc₀3
  set Kb := Sec8.imageModTheta L K with hKb
  have hKbC : Kb ≤ C := by
    rw [← hCW]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hKW)
  have hsn : (Kb.subgroupOf C).IsSubnormal := by
    let ρ : W →* C := ((π.comp (Subgroup.inclusion hWL)).codRestrict C fun w => by
      rw [← hCW]
      exact ⟨Subgroup.inclusion hWL w, w.2, rfl⟩)
    have hρ : Function.Surjective ρ := by
      rintro ⟨z, hz⟩
      rw [← hCW] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    have hmap : (K.subgroupOf W).map ρ = Kb.subgroupOf C := by
      ext ⟨z, hz⟩
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, hwc⟩
        refine ⟨Subgroup.inclusion hWL w, hw, ?_⟩
        exact congrArg Subtype.val hwc
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hKW hx⟩, hx, Subtype.ext rfl⟩
    rw [← hmap]
    exact hK'.2.1.map hρ
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn h.mem_thetaComponentsIn
  have hKbp : Group.IsPerfect Kb := by
    have := hKp
    rw [hKb, Sec8.imageModTheta, ← Subgroup.inclusion_range hKL, MonoidHom.map_range]
    exact Group.IsPerfect.range _
  set Rb := Sec8.imageModTheta L (inSubgroup (aschbacherSolvableCore 3) K) with hRb
  have hRK : Rb ≤ Kb := Subgroup.map_mono (Subgroup.subgroupOf_mono L (Sec6.theta_le K))
  have hRn : (Rb.subgroupOf Kb).Normal := Sec6.BThreeCensus.normal_imageModTheta_theta hKL
  obtain ⟨e⟩ := Sec6.BThreeCensus.nonempty_quotientThetaEquiv hKL
  have hθle : inSubgroup (aschbacherSolvableCore 3) K ≤ L := (Sec6.theta_le K).trans hKL
  let ι : (inSubgroup (aschbacherSolvableCore 3) K) →* Rb :=
    ((π.comp (Subgroup.inclusion hθle)).codRestrict Rb fun t =>
      ⟨Subgroup.inclusion hθle t, t.2, rfl⟩)
  have hι : Function.Surjective ι := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hRs : Group.IsSolvable (Rb.subgroupOf Kb) := by
    have := (Sec6.theta_solvable_and_not_dvd K).1
    have : Group.IsSolvable Rb := Group.isSolvable_of_surjective (f := ι) hι
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hRK).symm.toMonoidHom) (MulEquiv.surjective _)
  have hR3 : ¬ 3 ∣ Nat.card (Rb.subgroupOf Kb) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv]
    exact fun h3 => (Sec6.theta_solvable_and_not_dvd K).2
      (h3.trans (Subgroup.card_dvd_of_surjective (f := ι) hι))
  have hθQ : aschbacherSolvableCore 3 (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple h.isQuasisimple_K
      (by rw [h.center_K]; exact IsPGroup.of_bot)
  let f : Kb →* K ⧸ aschbacherSolvableCore 3 K :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (Rb.subgroupOf Kb))
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Rb.subgroupOf Kb := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hθKb : aschbacherSolvableCore 3 Kb = Rb.subgroupOf Kb := by
    rw [← hker]
    exact Sec13.aschbacherSolvableCore_eq_ker f hf (hker ▸ hRs) (hker ▸ hR3) hθQ
  have e' : Kb ⧸ aschbacherSolvableCore 3 Kb ≃* K ⧸ aschbacherSolvableCore 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hθKb).trans e.symm
  refine ⟨Sec6.mem_thetaComponentsIn_of hKbC hKbp hsn
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm h.isQuasisimple_K), ⟨e'⟩⟩

theorem mem_normalizer_A (h : Config424 G A L a c K) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) {w : G}
    (hw : w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)) :
    w ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A ≤ A.comap (MulAut.conj w).toMonoidHom := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show w * y * w⁻¹ ∈ A
    rcases hy with rfl | rfl | rfl
    · rw [h.a_comm w, mul_inv_cancel_right]
      exact h.a_mem
    · exact ((Subgroup.mem_normalizer_iff.mp hw _).mp hc₀).1
    · exact ((Subgroup.mem_normalizer_iff.mp hw _).mp hd).1
  exact Subgroup.mem_normalizer_fintype fun y hy => hle hy

theorem exists_lift_of_mem_normalizer (h : Config424 G A L a c K)
    {xb : L ⧸ aschbacherSolvableCore 3 L}
    (hxb : xb ∈ Subgroup.normalizer
      ((Sec8.imageModTheta L (A ⊓ L) : Subgroup _) : Set (L ⧸ aschbacherSolvableCore 3 L))) :
    ∃ w : L, (w : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      ∃ e ∈ Sec8.imageModTheta L (A ⊓ L),
        xb = e * QuotientGroup.mk' (aschbacherSolvableCore 3 L) w := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) xb
  obtain ⟨w, hw, e, he, hne⟩ := exists_normalizer_lift h.isPGroup_inf_subgroupOf (n := n) hxb
  refine ⟨w, Subgroup.mem_normalizer_fintype fun y hy => ?_, e, he, hne⟩
  have hyL : y ∈ L := hy.2
  have h1 := (Subgroup.mem_normalizer_iff.mp hw ⟨y, hyL⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp h1

theorem normalizer_imageModTheta_le (h : Config424 G A L a c K) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L)
    (hdK : A ⊓ K = Subgroup.zpowers d) :
    Subgroup.normalizer
        ((Sec8.imageModTheta L (A ⊓ L) : Subgroup _) : Set (L ⧸ aschbacherSolvableCore 3 L)) ≤
      Subgroup.normalizer ((Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        ⟨d, hd.2⟩) : Subgroup _) : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  intro xb hxb
  obtain ⟨w, hwN, e, he, rfl⟩ := h.exists_lift_of_mem_normalizer hxb
  have hwA := h.mem_normalizer_A hA hc₀ hd hwN
  have hwK := h.normalizer_le hwA
  rw [hdK] at hwK
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hwK d).mp (Subgroup.mem_zpowers d))
  set db := π ⟨d, hd.2⟩ with hdb
  have hwd : π w * db * (π w)⁻¹ = db ^ j := by
    have e1 : w * ⟨d, hd.2⟩ * w⁻¹ = (⟨d, hd.2⟩ : L) ^ j := Subtype.ext (by simpa using hj.symm)
    rw [hdb, ← map_mul, ← map_inv, ← map_mul, e1, map_zpow]
  have hdD : db ∈ Sec8.imageModTheta L (A ⊓ L) :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
  have hed : e * db = db * e := congrArg Subtype.val
    (h.isElemAbelian_imageModTheta_inf.1.is_comm.comm ⟨e, he⟩ ⟨db, hdD⟩)
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have e2 : e * π w * db ^ k * (e * π w)⁻¹ = e * (π w * db * (π w)⁻¹) ^ k * e⁻¹ := by
    rw [conj_zpow]
    group
  rw [e2, hwd, ← zpow_mul]
  have hed' : e * db ^ (j * k) * e⁻¹ = db ^ (j * k) := by
    rw [(Commute.zpow_right (show Commute e db from hed) (j * k)).eq, mul_inv_cancel_right]
  rw [hed']
  exact Subgroup.zpow_mem_zpowers db _

theorem innerConfig (h : Config424 G A L a c K) {c₀ d : G} {i : ℤ} (hci : c = c₀ * a ^ i)
    (hdK : A ⊓ K = Subgroup.zpowers d) (hc₀A : c₀ ∈ A) (hc₀L : c₀ ∈ L)
    (hc₀1 : c₀ ≠ 1) (hdc₀ : d ∉ Subgroup.zpowers c₀) (hAL : A ⊓ L = Subgroup.closure {c₀, d})
    (h9 : Nat.card (Subgroup.closure ({c₀, d} : Set G)) = 9)
    (hA : A = Subgroup.closure {a, c₀, d}) (hdL : d ∈ L) :
    InnerConfig424 (L ⧸ aschbacherSolvableCore 3 L) (Sec8.imageModTheta L (A ⊓ L))
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c₀, hc₀L⟩)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) (Sec8.imageModTheta L K) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hc₀AL : c₀ ∈ A ⊓ L := ⟨hc₀A, hc₀L⟩
  have hdAL : d ∈ A ⊓ L := ⟨hdA, hdL⟩
  have hc₀3 : c₀ ^ 3 = 1 := h.pow_three c₀ hc₀A
  obtain ⟨hKmem, -⟩ := h.imageModTheta_K_facts hci hc₀L hc₀3
  obtain ⟨-, ⟨eK⟩⟩ := h.imageModTheta_K_facts hci hc₀L hc₀3
  refine ⟨h.maximal_imageModTheta_inf hA hc₀AL hdAL, ?_, ?_, ?_, ?_, ?_, hKmem, ?_, ?_, ?_⟩
  · rw [h.card_imageModTheta_inf, hAL, h9]
  · exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hc₀AL)
  · intro h1
    apply hc₀1
    have := h.eq_of_mk_eq (x := ⟨c₀, hc₀L⟩) (y := 1) hc₀A A.one_mem (by
      rw [← QuotientGroup.mk'_apply, h1, QuotientGroup.mk_one])
    exact congrArg Subtype.val this
  · exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hdAL)
  · intro hd'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd'
    apply hdc₀
    have hc₀m : (⟨c₀, hc₀L⟩ : L) ^ m = ⟨c₀ ^ m, L.zpow_mem hc₀L m⟩ := Subtype.ext (by simp)
    have := h.eq_of_mk_eq (x := ⟨c₀ ^ m, L.zpow_mem hc₀L m⟩) (y := ⟨d, hdL⟩)
      (A.zpow_mem hc₀A m) hdA (by
        rw [← hc₀m]
        change π (⟨c₀, hc₀L⟩ ^ m) = π ⟨d, hdL⟩
        rw [map_zpow]
        exact hm)
    have hdm : c₀ ^ m = d := congrArg Subtype.val this
    rw [← hdm]
    exact Subgroup.zpow_mem_zpowers c₀ m
  · exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hdAK.2)
  · exact Sec11.isType424_of_mulEquiv eK h.isType424
  · exact h.normalizer_imageModTheta_le hA hc₀AL hdAL hdK

end Config424

end CFSG.RankThree.PartTwo.Sec4
