module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4315
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Two

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

namespace L4316

theorem isSimpleGroup_SL2 {F : Type} [Field F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup SL(2, F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center SL(2, F) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

theorem subgroupOf_le_normalizer {G : Type} [Group G] {A B C : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf C ≤ Subgroup.normalizer ((B.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h hg) x

theorem subgroupOf_perfect {G : Type} [Group G] {A C : Subgroup G} (hAC : A ≤ C)
    (hA : ⁅A, A⁆ = A) : ⁅A.subgroupOf C, A.subgroupOf C⁆ = A.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAC]
  exact hA

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

@[expose] noncomputable def star (A : Subgroup G) : Subgroup ↥s.rho.range :=
  (A.subgroupOf s.G₀).map s.rho.rangeRestrict

theorem map_star (A : Subgroup G) :
    (s.star A).map s.rho.range.subtype = (A.subgroupOf s.G₀).map s.rho := by
  rw [star, Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]

theorem mem_normalizer_star_iff (A : Subgroup G) (x : ↥s.rho.range) :
    x ∈ Subgroup.normalizer ((s.star A : Subgroup ↥s.rho.range) : Set ↥s.rho.range) ↔
      (x : MulAut (ModO2 KZ)) ∈
        Subgroup.normalizer (((A.subgroupOf s.G₀).map s.rho : Subgroup _) : Set _) := by
  have hle : (s.star A).map s.rho.range.subtype ≤ s.rho.range.subtype.range :=
    Subgroup.map_le_range _ _
  have h := Subgroup.comap_normalizer_eq_of_le_range hle
  rw [Subgroup.comap_map_eq_self_of_injective s.rho.range.subtype_injective] at h
  rw [← h, Subgroup.mem_comap, s.map_star]
  rfl

@[expose] noncomputable def starHom {A : Subgroup G} (hA : A ≤ s.G₀) : ↥A →* ↥(s.star A) :=
  (s.rho.rangeRestrict.comp (Subgroup.inclusion hA)).codRestrict (s.star A)
    fun a => ⟨Subgroup.inclusion hA a, a.2, rfl⟩

theorem coe_starHom {A : Subgroup G} (hA : A ≤ s.G₀) (a : ↥A) :
    (((s.starHom hA a : ↥(s.star A)) : ↥s.rho.range) : MulAut (ModO2 KZ)) =
      s.rho ⟨a, hA a.2⟩ := rfl

theorem starHom_surjective {A : Subgroup G} (hA : A ≤ s.G₀) :
    Function.Surjective (s.starHom hA) := by
  rintro ⟨x, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem rho_eq_one_of_mem_C₀ {g : G} (hg : g ∈ s.G₀) (hgC : g ∈ s.C₀) : s.rho ⟨g, hg⟩ = 1 := by
  obtain ⟨g', hg', rfl⟩ := hgC
  exact hg'

theorem mem_C₀_of_rho_eq_one {g : G} (hg : g ∈ s.G₀) (h1 : s.rho ⟨g, hg⟩ = 1) : g ∈ s.C₀ :=
  ⟨⟨g, hg⟩, h1, rfl⟩

@[expose] noncomputable def mulEquiv_star_KZ :
    ↥(s.star KZ) ≃* ↥(MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range :=
  ((s.star KZ).equivMapOfInjective _ s.rho.range.subtype_injective).trans
    (MulEquiv.subgroupCongr ((s.map_star KZ).trans s.map_KZ))

theorem coe_mulEquiv_star_KZ (x : ↥(s.star KZ)) :
    ((s.mulEquiv_star_KZ x : ↥(MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range) :
      MulAut (ModO2 KZ)) = ((x : ↥s.rho.range) : MulAut (ModO2 KZ)) := rfl

theorem star_KZ_normal : (s.star KZ).Normal := by
  have hn : (KZ.subgroupOf s.G₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer s.KZ_le_G₀).mpr s.G₀_le_normalizer_KZ
  exact hn.map _ s.rho.rangeRestrict_surjective

theorem isSimpleGroup_star_KZ (hq : CFSG.IsQuasisimple (ModO2 KZ)) :
    IsSimpleGroup ↥(s.star KZ) := by
  have := L4315.isSimpleGroup_inn hq.2.1
  exact s.mulEquiv_star_KZ.isSimpleGroup

theorem exists_not_comm_star_KZ (hq : CFSG.IsQuasisimple (ModO2 KZ)) :
    ∃ a b : ↥(s.star KZ), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := L4315.exists_not_comm_inn hq.2.2
  refine ⟨s.mulEquiv_star_KZ.symm a, s.mulEquiv_star_KZ.symm b, fun h => hab ?_⟩
  apply s.mulEquiv_star_KZ.symm.injective
  rw [map_mul, map_mul, h]

theorem centralizer_star_KZ (hq : CFSG.IsQuasisimple (ModO2 KZ)) :
    Subgroup.centralizer ((s.star KZ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine L4315.eq_one_of_commute_conj hq.1.commutator_eq_top _ fun q => ?_
  obtain ⟨z, hz⟩ := s.mulEquiv_star_KZ.surjective ⟨MulAut.conj q, q, rfl⟩
  have h1 := congrArg (fun w : ↥s.rho.range => (w : MulAut (ModO2 KZ))) (hx _ z.2)
  have hz' : ((z : ↥s.rho.range) : MulAut (ModO2 KZ)) = MulAut.conj q := by
    rw [← s.coe_mulEquiv_star_KZ, hz]
  simp only [Subgroup.coe_mul] at h1
  rw [hz'] at h1
  exact h1.symm

theorem starHom_KZ_eq_one_iff (k : ↥KZ) :
    s.starHom s.KZ_le_G₀ k = 1 ↔
      (QuotientGroup.mk k : ModO2 KZ) ∈ Subgroup.center (ModO2 KZ) := by
  rw [← L4315.ker_conj, MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 := congrArg (fun w : ↥(s.star KZ) => ((w : ↥s.rho.range) : MulAut (ModO2 KZ))) h
    simp only [coe_starHom] at h1
    rw [← s.rho_KZ k.2]
    exact h1
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_starHom]
    rw [← s.rho_KZ k.2] at h
    exact h

theorem a23List_star_KZ (hL : A23SQTKListFact) (hq : CFSG.IsQuasisimple (ModO2 KZ)) :
    A23List ↥(s.star KZ) := by
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  set H₀ : Subgroup ↥GZ := KZ.subgroupOf GZ with hH₀
  let f : ↥H₀ →* ↥(s.star KZ) :=
    (s.starHom s.KZ_le_G₀).comp (Subgroup.subgroupOfEquivOfLe hKZGZ).toMonoidHom
  have hf : Function.Surjective f :=
    (s.starHom_surjective s.KZ_le_G₀).comp (Subgroup.subgroupOfEquivOfLe hKZGZ).surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have := s.isSimpleGroup_star_KZ hq
  have hsimple : IsSimpleGroup (↥H₀ ⧸ f.ker) := e.isSimpleGroup
  have hnc : ∃ a b : ↥H₀ ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := s.exists_not_comm_star_KZ hq
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  exact CFSG.Quasithin.A36A.a23List_of_mulEquiv e.symm
    (hL ↥GZ s.sqtkGroup_GZ H₀ f.ker hsimple hnc)

theorem star_R₂_ne_bot (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    s.star R₂ ≠ ⊥ := by
  intro h
  apply s.map_R₂_ne_bot h135 hR hC h36 h37 h38 h39
  rw [← s.map_star, h, Subgroup.map_bot]

theorem isPGroup_star_R₂ : IsPGroup 2 ↥(s.star R₂) :=
  (s.isPGroup_R₂.of_equiv (Subgroup.subgroupOfEquivOfLe s.R₂_le_G₀).symm).map _

theorem star_K₂_le : s.star K₂ ≤ s.star KZ :=
  Subgroup.map_mono fun _ hx => s.K₂_le_KZ hx

theorem star_K₂_perfect : ⁅s.star K₂, s.star K₂⁆ = s.star K₂ := by
  rw [star, ← Subgroup.map_commutator, L4316.subgroupOf_perfect s.K₂_le_G₀ s.K₂_perfect]

theorem star_K₂_le_normalizer :
    s.star K₂ ≤ Subgroup.normalizer ((s.star R₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) :=
  (Subgroup.map_mono (L4316.subgroupOf_le_normalizer fun _ hk =>
    s.le_normalizer_R₂ (Subgroup.mem_sup_left hk))).trans (Subgroup.le_normalizer_map _)

theorem normalizer_star_R₂_le (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Subgroup.normalizer ((s.star R₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) ≤
      Subgroup.normalizer ((s.star K₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) := by
  intro x hx
  obtain ⟨g, rfl⟩ := s.rho.rangeRestrict_surjective x
  rw [s.mem_normalizer_star_iff] at hx ⊢
  exact s.rho_mem_normalizer_K₂ h135 hR hC h37 h38 h39 g hx

theorem levi_eq_one_of_mem_C₀ {k : G} (hk : k ∈ K₂) (hkC : k ∈ s.C₀) : s.levi ⟨k, hk⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  set N : Subgroup ↥K₂ := s.C₀.subgroupOf K₂ with hN
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr fun g hg =>
      mem_normalizer_inf (s.le_normalizer_C₀ (s.K₂_le_G₀ hg)) (Subgroup.le_normalizer hg)
  have hmapN : (N.map s.levi).Normal := hNn.map _ s.levi_surjective
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, s.card_F]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
  have := L4316.isSimpleGroup_SL2 h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map s.levi) with h | h
  · have hmem : s.levi ⟨k, hk⟩ ∈ N.map s.levi := ⟨⟨k, hk⟩, hkC, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hle : K₂ ≤ (K₂ ⊓ s.C₀) ⊔ pCoreOf 2 K₂ := by
      intro x hx
      obtain ⟨w, hw, hwx⟩ := h ▸ Subgroup.mem_top (s.levi ⟨x, hx⟩)
      have hq : w⁻¹ * ⟨x, hx⟩ ∈ s.levi.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, inv_mul_cancel]
      rw [s.ker_levi] at hq
      have e : x = (w : G) * ((w⁻¹ * ⟨x, hx⟩ : ↥K₂) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨w.2, hw⟩)
        (Subgroup.mem_sup_right ((mem_pCoreOf_iff' _).mpr hq))
    have hsolv : Group.IsSolvable ↥(pCoreOf 2 K₂) := by
      have := (pCoreOf_isPGroup 2 K₂).isNilpotent
      infer_instance
    have hOn : pCoreOf 2 K₂ ≤ Subgroup.normalizer ((K₂ ⊓ s.C₀ : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf (Subgroup.le_normalizer (pCoreOf_le 2 K₂ hx))
        (s.le_normalizer_C₀ (s.K₂_le_G₀ (pCoreOf_le 2 K₂ hx)))
    have hK₂C : K₂ ≤ K₂ ⊓ s.C₀ :=
      L4315.le_of_perfect_of_le_sup s.K₂_perfect inf_le_left hsolv hOn hle
    apply s.not_K₂_le_pCoreOf_KZ
    refine L4315.le_pCoreOf_of_central s.K₂_le_KZ s.K₂_perfect fun x hx => ?_
    rw [← L4315.ker_conj, MonoidHom.mem_ker, ← s.rho_KZ (s.K₂_le_KZ hx)]
    exact s.rho_eq_one_of_mem_C₀ _ (hK₂C hx).2

theorem exists_chi :
    ∃ χ : ↥(s.star K₂) →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker := by
  set ψ := s.starHom s.K₂_le_G₀ with hψdef
  have hψ : Function.Surjective ψ := s.starHom_surjective s.K₂_le_G₀
  have hker : ψ.ker ≤ s.levi.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have h1 : s.rho ⟨k, s.K₂_le_G₀ k.2⟩ = 1 := by
      have := congrArg (fun w : ↥(s.star K₂) => ((w : ↥s.rho.range) : MulAut (ModO2 KZ))) hk
      exact this
    exact s.levi_eq_one_of_mem_C₀ k.2 (s.mem_C₀_of_rho_eq_one _ h1)
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let χ : ↥(s.star K₂) →* SL(2, F) := (QuotientGroup.lift _ s.levi hker).comp e₀.symm.toMonoidHom
  have hχ : ∀ k : ↥K₂, χ (ψ k) = s.levi k := by
    intro k
    show QuotientGroup.lift _ s.levi hker (e₀.symm (ψ k)) = s.levi k
    have : e₀.symm (ψ k) = (QuotientGroup.mk k : ↥K₂ ⧸ ψ.ker) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [this, QuotientGroup.lift_mk]
  refine ⟨χ, fun z => ?_, fun x => ?_⟩
  · obtain ⟨k, rfl⟩ := s.levi_surjective z
    exact ⟨ψ k, hχ k⟩
  · obtain ⟨k, hk⟩ := hψ x
    have hk1 : s.levi k = 1 := by
      rw [← hχ, hk]
      exact x.2
    have hkO : k ∈ CFSG.pCore 2 ↥K₂ := by
      rw [← s.ker_levi]
      exact hk1
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₂)) ⟨k, hkO⟩
    refine ⟨a, Subtype.ext ?_⟩
    have ha' : k ^ 2 ^ a = 1 := congrArg Subtype.val ha
    rw [SubgroupClass.coe_pow, ← hk, ← map_pow, ha', map_one]
    rfl

theorem prime_cond (hF : A318Facts) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ m - 1) :
    CFSG.Open.pRank p (s.star KZ) ≤ 1 ∨
      (p = 3 ∧ ∃ (s' : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s' then 1 else -1) ∧
        IsPSLEps3q s' q ↥(s.star KZ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  have hKZc : KZ ∈ cComp (Subgroup.centralizer (ZS : Set G)) :=
    cComp_mem_of_le s.KZ_mem s.KZ_cent (Subgroup.centralizer_le_normalizer _)
  have hKZn : (KZ.subgroupOf GZ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).mpr s.KZ_normal
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  rcases s.pRank_KZ_le_one hF h135 hR hC h36 h37 h38 h39 hKZc s.K₂_le_KZ hKZn hp hp2 hpn with
    hr | ⟨hp3, h2⟩
  · left
    have hM : CFSG.pRank p ↥KZ ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype]
      exact hr
    have h' := L436.pRank_le_one_of_surjective' hp hp2 (s.starHom s.KZ_le_G₀)
      (s.starHom_surjective s.KZ_le_G₀) hM
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype] at h'
    exact h'
  · right
    refine ⟨hp3, ?_⟩
    obtain ⟨s', q, hcong, hpslq, -⟩ := h2
    refine ⟨s', q, hcong, ?_⟩
    set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
    set SK := starImage 3 (KZ.subgroupOf GZ) with hSK
    have := L436.isSimpleGroup_of_isPSLEps3q hpslq
    let ψ₀ : ↥KZ →* PStar 3 ↥GZ := π.comp (Subgroup.inclusion hKZGZ)
    have hrange : ψ₀.range = SK := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    let ψ : ↥KZ →* ↥SK := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict
    have hψ : Function.Surjective ψ :=
      (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective
    have hψv : ∀ k : ↥KZ, ((ψ k : ↥SK) : PStar 3 ↥GZ) = π ⟨k, hKZGZ k.2⟩ := fun k => rfl
    have hperf : Group.IsPerfect ↥SK := by
      have : Group.IsPerfect ↥KZ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp s.KZ_mem)
      exact Group.IsPerfect.ofSurjective hψ
    have hO₂3 : ∀ k : ↥KZ, (k : G) ∈ pCoreOf 2 KZ → π ⟨k, hKZGZ k.2⟩ = 1 := by
      intro k hk
      exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥GZ)
        (⟨k, hKZGZ k.2⟩ : ↥GZ)).mpr
        (Setting436Sp4.pCoreOf_subgroupOf_le_pPrimeCore (x := ⟨k, hKZGZ k.2⟩) hKZGZ s.KZ_normal hk)
    have hker : (s.starHom s.KZ_le_G₀).ker ≤ ψ.ker := by
      intro c hc
      rw [MonoidHom.mem_ker, s.starHom_KZ_eq_one_iff] at hc
      rw [MonoidHom.mem_ker]
      apply L436.eq_one_of_forall_commute hperf
      intro w
      obtain ⟨k, rfl⟩ := hψ w
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hψv, hψv, ← map_mul, ← map_mul]
      have hck : (c : G) * k * (c : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 KZ := by
        have hz := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk k)
        have h1 : (QuotientGroup.mk (c * k * c⁻¹ * k⁻¹) : ModO2 KZ) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hz]
          group
        rw [QuotientGroup.eq_one_iff] at h1
        exact (mem_pCoreOf_iff' _).mpr h1
      have hmem : (c : G) * k * (c : G)⁻¹ * (k : G)⁻¹ ∈ KZ :=
        mul_mem (mul_mem (mul_mem c.2 k.2) (inv_mem c.2)) (inv_mem k.2)
      have h1 : π ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ hmem⟩ = 1 := hO₂3 ⟨_, hmem⟩ hck
      have e : (⟨(c : G), hKZGZ c.2⟩ * ⟨(k : G), hKZGZ k.2⟩ : ↥GZ) =
          ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ hmem⟩ *
            (⟨(k : G), hKZGZ k.2⟩ * ⟨(c : G), hKZGZ c.2⟩) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
      rw [e, map_mul, h1, one_mul, map_mul]
    let e₀ := QuotientGroup.quotientKerEquivOfSurjective (s.starHom s.KZ_le_G₀)
      (s.starHom_surjective s.KZ_le_G₀)
    let φ : ↥(s.star KZ) →* ↥SK := (QuotientGroup.lift _ ψ hker).comp e₀.symm.toMonoidHom
    have hφ : ∀ k : ↥KZ, φ (s.starHom s.KZ_le_G₀ k) = ψ k := by
      intro k
      show QuotientGroup.lift _ ψ hker (e₀.symm (s.starHom s.KZ_le_G₀ k)) = ψ k
      have : e₀.symm (s.starHom s.KZ_le_G₀ k) = (QuotientGroup.mk k : ↥KZ ⧸ _) := by
        apply e₀.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [this, QuotientGroup.lift_mk]
    have hφs : Function.Surjective φ := by
      intro w
      obtain ⟨k, rfl⟩ := hψ w
      exact ⟨_, hφ k⟩
    have := s.isSimpleGroup_star_KZ hq
    have hφi : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := exists_pair_ne ↥SK
        obtain ⟨a', rfl⟩ := hφs a
        obtain ⟨b', rfl⟩ := hφs b
        apply hab
        rw [MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top a'),
          MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top b')]
    obtain ⟨p', e', hp', he', hq', hY⟩ := hpslq
    exact ⟨p', e', hp', he', hq', IsPSLEps3.of_mulEquiv (MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm hY⟩

end Setting4315

end CFSG.Quasithin.H13.Ch4
