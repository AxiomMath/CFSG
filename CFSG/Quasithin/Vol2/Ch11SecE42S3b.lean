module

public import CFSG.Quasithin.Vol2.Ch11SecE42S3a
public import CFSG.Quasithin.Vol2.Ch11SecE42S1f

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem fsuV_spec (h701 : Stmt7_0_1) {T Kp I : Subgroup G} (hfsu : FSU G T Kp I)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G)) :
    Kp ≤ Subgroup.normalizer (fsuV T I : Set G) ∧ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      pCoreOf 2 Kp ≤ Subgroup.centralizer (fsuV T I : Set G) ∧
      ¬ Kp ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL0 : conjClosure Kp T = Kp := conjClosure_eq_self hTKp
  obtain ⟨-, -, hNV, -⟩ := h701 G T Kp I hfsu
  have hNV' : Kp ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) := hL0 ▸ hNV
  have hVR : fsuV T I ≤ reducedAggregate (Kp ⊔ T) := by
    have hN := (SecA.reducedAggregate_props (Kp ⊔ T)).2.2.2
    refine conjClosure_le fun t ht x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) x).mp
      (hfsu.irrPlus.1 hx)
  have hOKM : pCoreOf 2 Kp ≤ pCoreOf 2 (Kp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Kp).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hTKp).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Kp))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kp)
  have hVC : fsuV T I ≤ Subgroup.centralizer (pCoreOf 2 Kp : Set G) :=
    (hVR.trans (SecA.reducedAggregate_le_centralizer _)).trans (Subgroup.centralizer_le hOKM)
  refine ⟨le_sup_left.trans hNV', le_sup_right.trans hNV', Subgroup.le_centralizer_iff.mp hVC, ?_⟩
  intro hle
  have h1 := hfsu.irrPlus.2.2.2.1
  rw [hL0] at h1
  have h2 : ⁅I, Kp⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp (hle.trans (Subgroup.centralizer_le (le_conjClosure I T))))
  exact hfsu.irrPlus.2.1 (h1.symm.trans h2)

theorem list701Excl_autOn_of_fsu (hM24 : IsSimpleGroup ↥NativeSporadic.M24) (h701 : Stmt7_0_1)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) {T Kp I : Subgroup G} (hfsu : FSU G T Kp I)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G)) (hne1 : autOn Kp (fsuV T I) ≠ ⊥) :
    List701Excl ↥(autOn Kp (fsuV T I)) := by
  have hL0 : fsuL0 T Kp = Kp := conjClosure_eq_self hTKp
  have hL0' : conjClosure Kp T = Kp := hL0
  obtain ⟨hcomm, -, -, hcases⟩ := h701 G T Kp I hfsu
  have hTV := (fsuV_spec h701 hfsu hTKp).2.1
  rcases hcases with hFF | hJ | hO | h4
  · obtain ⟨A, hA⟩ := hFF
    rw [hL0] at hA
    obtain ⟨-, -, h3⟩ := h325 G T Kp I hfsu hL0'.symm
    rcases h3 with ⟨hI, -⟩ | ⟨hI, -⟩ | ⟨-, hlist, -⟩
    · exact list701Excl_of_ff h328 hfsu hTKp hTV hI hA hne1
    · exact list701Excl_of_ff h328 hfsu hTKp hTV hI hA hne1
    · rcases hlist with ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact List701Excl.sl3 hK e
      · exact List701Excl.sp4 hK e
      · exact List701Excl.a6 e
      · exact List701Excl.sl4 e
      · exact List701Excl.sl5 e
      · exact List701Excl.a7 e
  · obtain ⟨-, -, -, -, ⟨π, hπs, -⟩, -⟩ := hJ
    have hKH : Kp ≤ fsuM T Kp := by
      show Kp ≤ Subgroup.normalizer (fsuL0 T Kp : Set G)
      rw [hL0]
      exact Subgroup.le_normalizer
    have hHK : fsuM T Kp ≤ Subgroup.normalizer (Kp : Set G) := by
      show Subgroup.normalizer (fsuL0 T Kp : Set G) ≤ _
      rw [hL0]
    let π' : ↥NativeSporadic.M24 →* ↥(autOn (fsuM T Kp) (fsuV T I)) := π
    have hπi : Function.Injective π' := by
      rcases hM24.eq_bot_or_eq_top_of_normal π'.ker with h0 | h0
      · exact (MonoidHom.ker_eq_bot_iff π').mp h0
      · exfalso
        apply hne1
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨y, hy⟩ := hπs ⟨x, InternalSec.autOn_le_autOn_of_le hKH hx⟩
        have h1 : π' y = 1 := (MonoidHom.mem_ker).mp (h0 ▸ Subgroup.mem_top y)
        have h2 : π y = 1 := h1
        rw [h2] at hy
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy).symm
    let f : ↥NativeSporadic.M24 ≃* ↥(autOn (fsuM T Kp) (fsuV T I)) :=
      MulEquiv.ofBijective π' ⟨hπi, hπs⟩
    obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup hKH hHK f.symm hne1
    exact List701Excl.m24 e'
  · obtain ⟨n, -, K, _, _, _, hK, π, hπs, -⟩ := hO
    have heq : autOn (fsuL0 T Kp) (fsuV T I) = autOn Kp (fsuV T I) := by rw [hL0]
    exact List701Excl.sl2 hK ((MulEquiv.subgroupCongr heq).toMonoidHom.comp π)
      ((MulEquiv.subgroupCongr heq).surjective.comp hπs)
  · have h41 := h4.1
    rw [hL0] at h41
    exact absurd h41 (lt_irrefl _)

omit [Finite G] in
theorem exists_central_epi_autOn {K W : Subgroup G}
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    ∃ π : ↥K ⧸ CFSG.pCore 2 ↥K →* ↥(autOn K W), Function.Surjective π ∧
      π.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  set ψ : ↥K →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hKN) with hψ
  have hrange : ψ.range = autOn K W := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKN k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  set ψ' : ↥K →* ↥(autOn K W) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict with hψ'
  have hψ's : Function.Surjective ψ' :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hψk : ∀ k : ↥K, ψ' k = 1 ↔ ψ k = 1 := by
    intro k
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      simpa [hψ'] using this
    · intro h1
      apply Subtype.ext
      simpa [hψ'] using h1
  have hle : CFSG.pCore 2 ↥K ≤ ψ'.ker := by
    intro k hk
    have hkO : (k : G) ∈ pCoreOf 2 K := by
      rw [← SecD.pCoreOf_subgroupOf] at hk
      exact hk
    rw [MonoidHom.mem_ker, hψk]
    exact conjV_eq_one_of_mem_centralizer (hKN k.2) (hO hkO)
  set φ := QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ' hle with hφ
  have hφs : Function.Surjective φ := by
    intro a
    obtain ⟨k, rfl⟩ := hψ's a
    exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk _ _ _⟩
  refine ⟨φ, hφs, ?_⟩
  have hnt : φ.ker ≠ ⊤ := by
    intro h0
    apply hne
    intro k hk
    have h1 : φ (QuotientGroup.mk ⟨k, hk⟩) = 1 := (MonoidHom.mem_ker).mp (h0 ▸ Subgroup.mem_top _)
    rw [hφ, QuotientGroup.lift_mk, hψk] at h1
    exact SecD.mem_centralizer_of_conjV_eq_one (hKN hk) h1
  exact SecA.le_center_of_normal_ne_top hQ hnt

theorem kz_type (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hP : SecB.PointFacts)
    (hM24 : IsSimpleGroup ↥NativeSporadic.M24) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8)
    (h701 : Stmt7_0_1) (hFSU : Ch10.StmtFSUChoice) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}
    {z : G} (hc : Conf11_4_2 T L I n V₁ z) (hmax : quasithinIsMaximalLocal T (kz L V₁ z)) :
    (IsSL3 (2 ^ n) (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
        IsPSL 3 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
        IsPSp4 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
        IsG2 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z))) ∨
      (n = 2 ∧ (IsAlt 7 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
        IsHat (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) (alternatingGroup (Fin 7)))) := by
  obtain ⟨hTK, -, -, -, -, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨I', hfsu⟩ := exists_fsu_kz hF hS hF43 hP h1102 h1110 h1111 h1141 h37 h39 hFSU hc hmax
  have hQ := isQuasisimple_kz hF hS hc
  obtain ⟨hKV, -, hO, hne⟩ := fsuV_spec h701 hfsu hTK
  obtain ⟨π, hπs, hπk⟩ := exists_central_epi_autOn hQ hKV hO hne
  have hne1 : autOn (kz L V₁ z) (fsuV T I') ≠ ⊥ := by
    intro h0
    apply hne
    intro k hk
    have hmem : conjAct (fsuV T I') ⟨k, hKV hk⟩ ∈ autOn (kz L V₁ z) (fsuV T I') :=
      ⟨⟨k, hKV hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact SecD.mem_centralizer_of_conjV_eq_one (hKV hk) hmem
  exact hS.list701 _ n hc.hyp.one_lt hc.list hc.not_a36 hc.not_sl2pE _ π hπs hπk
    (list701Excl_autOn_of_fsu hM24 h701 h325 h328 hfsu hTK hne1)

end CFSG.Quasithin.Vol2.Ch11.SecE
