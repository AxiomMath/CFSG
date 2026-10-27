module

public import CFSG.Quasithin.Vol2.Ch11SecS12YE
public import CFSG.Quasithin.Vol2.Ch11SecS12YF
public import CFSG.Quasithin.Vol2.Ch11SecS12T
public import CFSG.Quasithin.Vol2.Ch11SecSXCard
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem card_map_of_injOn {H R : Type} [Group H] [Group R] (f : H →* R) (A : Subgroup H)
    (hA : ∀ x ∈ A, f x = 1 → x = 1) : Nat.card ↥(A.map f) = Nat.card ↥A := by
  have hinj : Function.Injective (f.domRestrict A) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hA x x.2 hx)
  rw [← MonoidHom.domRestrict_range, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

theorem eq_zpowers_of_card_three {A : Subgroup G} (hA : Nat.card ↥A = 3) {x : G} (hx : x ∈ A)
    (hx1 : x ≠ 1) : A = Subgroup.zpowers x ∧ orderOf x = 3 := by
  have h3 : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥A)
      rwa [hA, Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine ⟨(Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_).symm, h3⟩
  rw [Nat.card_zpowers, h3, hA]

omit [Finite G] in
theorem eq_one_of_odd {A P : Subgroup G} (hA : Odd (Nat.card ↥A)) (hP : IsPGroup 2 ↥P) {x : G}
    (hx : x ∈ A) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ Nat.card ↥A := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥A)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (Nat.card ↥A) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hA)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

variable {T L I V₁ V₂ X K : Subgroup G}

theorem exists_weyl_aux (hC : SecS.CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : SecS.StarHyp G T L I V₁ V₂ X K)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Γ : Subgroup G} (hΓ : Γ = K ⊔ SecA.xOne X (LOf L V₁))
    (α : ↥Γ →* PGL3 F) (hαs : Function.Surjective α)
    (hα1 : ∀ γ, α γ = 1 ↔ (γ : G) ∈ pCoreOf 2 Γ)
    (hperf : ⁅((LOf L V₁).subgroupOf Γ).map α, ((LOf L V₁).subgroupOf Γ).map α⁆ =
      ((LOf L V₁).subgroupOf Γ).map α)
    (hne : ((LOf L V₁).subgroupOf Γ).map α ≠ ⊥)
    (hneR : ((LOf L V₁).subgroupOf Γ).map α ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆)
    (hS : ∃ S : Subgroup (PGL3 F), QuasithinUnique.IsSylowTwoOf S ⊤ ∧
      S ≤ Subgroup.normalizer ((((LOf L V₁).subgroupOf Γ).map α : Subgroup (PGL3 F)) :
        Set (PGL3 F)))
    (hKR : (K.subgroupOf Γ).map α ≤ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆)
    (hOK : pCoreOf 2 Γ ≤ K) {x₁ : G} (hx₁ : x₁ ∈ SecA.xOne X (LOf L V₁)) (hx₁1 : x₁ ≠ 1) :
    ∃ w ∈ K, w ∈ Subgroup.normalizer (X : Set G) ∧ w * x₁ * w⁻¹ ∉ SecA.xOne X (LOf L V₁) := by
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    SecS.cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hX9 : Nat.card ↥X = 9 := SecS.card_cartan hc hXN
    (SecS.cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hXodd : Odd (Nat.card ↥X) := by rw [hX9]; decide
  obtain ⟨hX₁z, hx₁3⟩ := eq_zpowers_of_card_three hc.cardX₁ hx₁ hx₁1
  obtain ⟨y, hyK, hy1⟩ : ∃ y ∈ X ⊓ LOf L V₁, y ≠ 1 := by
    have : Nontrivial ↥(X ⊓ LOf L V₁) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc.card₁]
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ↥(X ⊓ LOf L V₁))
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  obtain ⟨hXKz, hy3⟩ := eq_zpowers_of_card_three hc.card₁ hyK hy1
  have hXsup : X = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers y := by
    refine le_antisymm (hX₁z ▸ hXKz ▸ hc.a) (sup_le ?_ ?_)
    · exact Subgroup.zpowers_le.mpr hx₁.1
    · exact Subgroup.zpowers_le.mpr hyK.1
  have hKΓ : K ≤ Γ := hΓ ▸ le_sup_left
  have hL₁Γ : LOf L V₁ ≤ Γ := h.L₁_le_K.trans hKΓ
  have hX₁Γ : SecA.xOne X (LOf L V₁) ≤ Γ := hΓ ▸ le_sup_right
  have hx₁Γ : x₁ ∈ Γ := hX₁Γ hx₁
  have hyΓ : y ∈ Γ := hL₁Γ hyK.2
  have hXΓ : X ≤ Γ := hXsup ▸ sup_le (Subgroup.zpowers_le.mpr hx₁Γ) (Subgroup.zpowers_le.mpr hyΓ)
  obtain ⟨S, hS, hSA⟩ := hS
  obtain ⟨c, j₀, -, hcj⟩ := exists_conj_Ptheta hF hS hSA hne hperf hneR
  obtain ⟨α', hα'⟩ : ∃ α' : ↥Γ →* PGL3 F, α' = (MulAut.conj c).toMonoidHom.comp α := ⟨_, rfl⟩
  have hα'L : ((LOf L V₁).subgroupOf Γ).map α' = Ptheta F j₀ := by
    rw [hα', ← Subgroup.map_map]
    exact hcj
  have hα'1 : ∀ γ : ↥Γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 Γ := fun γ => by
    rw [hα', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hα1 γ
  have hα's : Function.Surjective α' := by
    rw [hα']
    exact (MulAut.conj c).surjective.comp hαs
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hX9]; norm_num)
  have hxy : x₁ * y = y * x₁ := by
    have := hcomm.is_comm.comm (⟨x₁, hx₁.1⟩ : ↥X) ⟨y, hyK.1⟩
    simpa using congrArg Subtype.val this
  have h2Γ : IsPGroup 2 ↥(pCoreOf 2 Γ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Γ
  have hsc := map_mem_sectionCentralizer α' hL₁Γ (y := ⟨x₁, hx₁Γ⟩) hx₁.2.1 hx₁.2.2.2
  rw [hα'L] at hsc
  have ha3 : α' ⟨x₁, hx₁Γ⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨x₁, hx₁Γ⟩ : ↥Γ) ^ 3 = 1 from Subtype.ext (by
      simp [← hx₁3]), map_one]
  have hb3 : α' ⟨y, hyΓ⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨y, hyΓ⟩ : ↥Γ) ^ 3 = 1 from Subtype.ext (by
      simp [← hy3]), map_one]
  have ha1 : α' ⟨x₁, hx₁Γ⟩ ≠ 1 := fun h1 =>
    hx₁1 (eq_one_of_odd hXodd h2Γ hx₁.1 ((hα'1 _).mp h1))
  have hab : α' ⟨y, hyΓ⟩ * α' ⟨x₁, hx₁Γ⟩ = α' ⟨x₁, hx₁Γ⟩ * α' ⟨y, hyΓ⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy.symm
  have hAX : (X.subgroupOf Γ).map α' =
      Subgroup.zpowers (α' ⟨x₁, hx₁Γ⟩) ⊔ Subgroup.zpowers (α' ⟨y, hyΓ⟩) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      have hle : X ≤ ((Subgroup.zpowers (α' ⟨x₁, hx₁Γ⟩) ⊔
          Subgroup.zpowers (α' ⟨y, hyΓ⟩)).comap α').map Γ.subtype := by
        rw [hXsup]
        refine sup_le (Subgroup.zpowers_le.mpr ⟨⟨x₁, hx₁Γ⟩, ?_, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨⟨y, hyΓ⟩, ?_, rfl⟩)
        · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      obtain ⟨z', hz', hzz⟩ := hle hz
      rw [show z = z' from Subtype.ext hzz.symm]
      exact hz'
    · exact sup_le (Subgroup.zpowers_le.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hx₁.1, rfl⟩)
        (Subgroup.zpowers_le.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hyK.1, rfl⟩)
  have hcardAX : Nat.card ↥((X.subgroupOf Γ).map α') = 9 := by
    rw [card_map_of_injOn α' _ fun z hz h1 => Subtype.ext
      (eq_one_of_odd hXodd h2Γ (Subgroup.mem_subgroupOf.mp hz) ((hα'1 z).mp h1)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv, hX9]
  have h9 : 9 ≤ Nat.card ↥(Subgroup.zpowers (α' ⟨x₁, hx₁Γ⟩) ⊔ Subgroup.zpowers (α' ⟨y, hyΓ⟩)) :=
    by rw [← hAX, hcardAX]
  obtain ⟨g₁, hg₁⟩ := ProjGenLinGroup.mk_surjective (α' ⟨x₁, hx₁Γ⟩)
  obtain ⟨h₀, hh₀⟩ := ProjGenLinGroup.mk_surjective (α' ⟨y, hyΓ⟩)
  rw [← hg₁] at hsc ha3 ha1
  rw [← hg₁, ← hh₀] at hab h9
  rw [← hh₀] at hb3
  obtain ⟨w', hw'R, hw'N, hw'm⟩ := exists_weyl_pgl hF hsc.2.1 hsc ha3 ha1 hab hb3 h9
  rw [hg₁, hh₀, ← hAX] at hw'N
  rw [hg₁] at hw'm
  have hR : ((thetaP F).range).Normal := by
    rw [range_thetaP_eq hF]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hα'K : (thetaP F).range ≤ (K.subgroupOf Γ).map α' := by
    have hΓK : Γ ≤ Subgroup.normalizer (K : Set G) := hΓ ▸ sup_le Subgroup.le_normalizer
      (inf_le_left.trans (h.cartan_le_normalizer_K hN h1102))
    have hKn : (K.subgroupOf Γ).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKΓ).mpr hΓK
    have hAn : ((K.subgroupOf Γ).map α').Normal := hKn.map α' hα's
    have hAle : (K.subgroupOf Γ).map α' ≤ (thetaP F).range := by
      rw [hα', ← Subgroup.map_map, range_thetaP_eq hF]
      refine (Subgroup.map_mono hKR).trans ?_
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective]
    have hAne : (K.subgroupOf Γ).map α' ≠ ⊥ := by
      intro hb
      apply Ptheta_ne_bot hF j₀
      rw [← hα'L, eq_bot_iff, ← hb]
      exact Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.mpr
        (h.L₁_le_K (Subgroup.mem_subgroupOf.mp hz))
    have hsimp := isSimpleGroup_projectiveSL_four hF
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((K.subgroupOf Γ).map α').comap (thetaP F)) with hb | ht
    · exact absurd (by rw [← Subgroup.map_comap_eq_self hAle, hb, Subgroup.map_bot]) hAne
    · rintro _ ⟨u, rfl⟩
      exact Subgroup.mem_comap.mp (ht ▸ Subgroup.mem_top u)
  obtain ⟨w₀, hw₀K, hw₀⟩ := hα'K hw'R
  have hN2 : ¬ 3 ∣ Nat.card ↥α'.ker := by
    have hp : IsPGroup 2 ↥α'.ker := by
      intro n
      obtain ⟨k, hk⟩ := h2Γ ⟨n, (hα'1 n).mp n.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hX3 : IsPGroup 3 ↥(X.subgroupOf Γ) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv, hX9]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw : (X.subgroupOf Γ).map (MulAut.conj w₀).toMonoidHom ≤ X.subgroupOf Γ ⊔ α'.ker := by
    rw [← Subgroup.comap_map_eq]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hw₀]
    exact (Subgroup.mem_normalizer_iff.mp hw'N _).mp ⟨z, hz, rfl⟩
  obtain ⟨n, hn, hnw⟩ := exists_mul_mem_normalizer hX3 hN2 hw
  refine ⟨((n * w₀ : ↥Γ) : G), K.mul_mem (hOK ((hα'1 n).mp hn)) hw₀K, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hnw ⟨z, hXΓ hz⟩).mp
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hz
      have hzΓ : z ∈ Γ := by
        have := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (n * w₀).2) (hXΓ hz)) (n * w₀).2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.mp hnw ⟨z, hzΓ⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h1
  · intro hmem
    rw [hX₁z] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hw'm
    have e1 : ((n * w₀ * ⟨x₁, hx₁Γ⟩ * (n * w₀)⁻¹ : ↥Γ)) = ⟨x₁, hx₁Γ⟩ ^ k :=
      Subtype.ext (by simpa using hk.symm)
    have e2 := congrArg α' e1
    rw [map_mul, map_mul, map_inv, map_mul, (hα'1 n).mpr ((hα'1 n).mp hn), one_mul, hw₀,
      map_zpow] at e2
    · rw [e2]
      exact Subgroup.zpow_mem_zpowers _ k

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
