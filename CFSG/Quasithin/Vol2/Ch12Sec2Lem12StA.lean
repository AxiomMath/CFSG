module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Quasithin.Vol2.Ch12Sec1Swap
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace Lem12St

variable {V : Type} [CommGroup V]

theorem card_orbitIn_mul_card_stab [Finite V] (H : Subgroup (MulAut V)) (a : V) :
    Nat.card (Orbit.orbitIn H a) * Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut V) a) =
      Nat.card H := by
  classical
  have horb : Orbit.orbitIn H a = MulAction.orbit ↥H a := by
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, rfl⟩
  have hstab : MulAction.stabilizer ↥H a =
      (H ⊓ MulAction.stabilizer (MulAut V) a).subgroupOf H := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    exact ⟨fun h1 => ⟨h.2, h1⟩, fun h1 => h1.2⟩
  have hcard : Nat.card (MulAction.stabilizer ↥H a) =
      Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut V) a) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [horb, ← hcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥H a), mul_comm]
  exact (MulAction.stabilizer ↥H a).card_mul_index

theorem false_of_isSolvable {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hKS : K ≤ S)
    (hS : Group.IsSolvable ↥S) (hK : K = perfectCore K) (hK1 : K ≠ ⊥) : False := by
  have hKs : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKS)
      (Subgroup.inclusion_injective hKS)
  have h0 := (isSolvable_iff_perfectCore_eq_bot K).mp hKs
  exact hK1 (hK.trans h0)

theorem isSimpleGroup_of_card_sixty {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hKS : K ≤ S) (hS : Nat.card S = 60) (hK : K = perfectCore K) (hK1 : K ≠ ⊥) :
    IsSimpleGroup ↥K := by
  have hdvd : Nat.card K ∣ 60 := hS ▸ Subgroup.card_dvd_of_le hKS
  have hperf : Group.IsPerfect ↥K :=
    Subgroup.isPerfect_iff.mpr ((perfectCore_eq_self_iff K).mp hK.symm)
  have h60 : Nat.card K = 60 := by
    by_contra hne
    have hlt : Nat.card K < 60 := lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hdvd) hne
    have := A312J2.isSolvable_of_card_dvd_sixty hdvd hlt
    have h0 := (isSolvable_iff_perfectCore_eq_bot K).mp this
    exact hK1 (hK.trans h0)
  exact A312J2.isSimpleGroup_of_perfect_card_sixty hperf h60

theorem isSimpleGroup_of_card_168 {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hKS : K ≤ S) (hS : Nat.card S = 168) (hK : K = perfectCore K) (hK1 : K ≠ ⊥) :
    IsSimpleGroup ↥K := by
  have hdvd : Nat.card K ∣ 168 := hS ▸ Subgroup.card_dvd_of_le hKS
  have hns : ¬ Group.IsSolvable ↥K := fun hs => hK1 (hK.trans
    ((isSolvable_iff_perfectCore_eq_bot K).mp hs))
  have h168 : Nat.card K = 168 := by
    by_contra hne
    have hlt : Nat.card K < 168 := lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hdvd) hne
    exact hns (A312Ru.isSolvable_of_card_dvd_168 hdvd hlt)
  exact A312Ru.isSimpleGroup_of_card_168 h168 hns

section Ambient

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G}

omit [Finite G] in
theorem autOn_le_stab (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V ≤
      autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) := by
  have hle : oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) ≤ L :=
    (oTwoUpper_le _).trans inf_le_left
  have hNV := hle.trans hLV
  refine le_inf (A4.autOn_mono hle) fun a ha => ?_
  obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hNV).mp ha
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  change ((A4.actionOn V _ hNV ⟨l, hl⟩ ⟨v, hv⟩ : ↥V) : G) = v
  rw [A4.actionOn_apply_coe]
  have hc : l * v = v * l :=
    Subgroup.mem_centralizer_singleton_iff.mp (((oTwoUpper_le _) hl).2)
  calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [hc]
    _ = v := by group

omit [Finite G] in
theorem autOn_ne_bot {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hVX : V = ⁅V, X⁆) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : autOn X V ≠ ⊥ := by
  intro h0
  have hXC : X ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have h1 : A4.actionOn V X hXV ⟨x, hx⟩ ∈ autOn X V := (A4.mem_autOn_iff hXV).mpr ⟨_, rfl⟩
    rw [h0, Subgroup.mem_bot] at h1
    exact (A4.actionOn_eq_one_iff hXV ⟨x, hx⟩).mp h1
  have hbot : ⁅V, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hXC
  rw [← hVX] at hbot
  apply hv1
  rw [hbot] at hv
  exact Subgroup.mem_bot.mp hv

end Ambient

section Central

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G}

theorem isSimpleGroup_of_mem_centralizer [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hirr : ∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) →
        J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hvL : v ∈ Subgroup.centralizer (L : Set G))
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : L ⊓ Subgroup.centralizer ({v} : Set G) = L := by
    refine inf_eq_left.mpr fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact (Subgroup.mem_centralizer_iff.mp hvL) l hl
  rw [hLC] at hK2 hVL ⊢
  set K := autOn (oTwoUpper L) V with hK
  set Lb := autOn L V with hLb
  have hOL : oTwoUpper L ≤ L := oTwoUpper_le L
  have hOLV : oTwoUpper L ≤ Subgroup.normalizer (V : Set G) := hOL.trans hLV
  have hnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    refine autOn_ne_bot hOLV hVL hv hv1 ?_
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hOLV).mp ha
    rw [Subgroup.mem_bot]
    exact (A4.actionOn_eq_one_iff hOLV _).mpr (hle (hOL hl))
  have hqb : CFSG.IsQuasisimple ↥Lb := isQuasisimple_autOn_of_pCoreOf_le hLV hq hO2 hnc
  have hLbperf : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp hqb.1
  have hKeq : K = Lb := by
    refine le_antisymm (A4.autOn_mono hOL) ?_
    rw [eq_oTwoUpper_of_perfect hLbperf]
    refine oTwoUpper_le_of_pow_mem fun a ha => ?_
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
    obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper L hl
    refine ⟨j, ?_⟩
    have h1 : A4.actionOn V (oTwoUpper L) hOLV ⟨l ^ 2 ^ j, hj⟩ ∈ K :=
      (A4.mem_autOn_iff hOLV).mpr ⟨_, rfl⟩
    have h2 : A4.actionOn V (oTwoUpper L) hOLV ⟨l ^ 2 ^ j, hj⟩ =
        (A4.actionOn V L hLV ⟨l, hl⟩) ^ 2 ^ j := by
      rw [← map_pow]
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]
      rfl
    rw [← h2]
    exact h1
  rw [hKeq] at hK2 ⊢
  set Z := Subgroup.center ↥Lb with hZ
  have hZinv : ∀ c : ↥Z, ((c : ↥Lb) : MulAut ↥V) ^ 2 = 1 → c = 1 := by
    intro c hc2
    set c₀ : MulAut ↥V := ((c : ↥Lb) : MulAut ↥V) with hc₀
    have hc₀Lb : c₀ ∈ Lb := (c : ↥Lb).2
    have hzle : Subgroup.zpowers c₀ ≤ Lb := (Subgroup.zpowers_le).mpr hc₀Lb
    have hzN : Lb ≤ Subgroup.normalizer ((Subgroup.zpowers c₀ : Subgroup (MulAut ↥V)) :
        Set (MulAut ↥V)) := by
      intro a ha
      have hca : a * c₀ * a⁻¹ = c₀ := by
        have := Subgroup.mem_center_iff.mp c.2 ⟨a, ha⟩
        have h' : a * c₀ = c₀ * a := congrArg Subtype.val this
        rw [h', mul_inv_cancel_right]
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← conj_zpow, hca]
        exact Subgroup.zpow_mem_zpowers c₀ k
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hy' : y = a⁻¹ * c₀ ^ k * a := by rw [hk]; group
        have hca' : a⁻¹ * c₀ * a = c₀ := by
          calc a⁻¹ * c₀ * a = a⁻¹ * (a * c₀ * a⁻¹) * a := by rw [hca]
            _ = c₀ := by group
        rw [hy']
        have : a⁻¹ * c₀ ^ k * a = (a⁻¹ * c₀ * a) ^ k := by
          rw [show a⁻¹ * c₀ * a = a⁻¹ * c₀ * a⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
        rw [this, hca']
        exact Subgroup.zpow_mem_zpowers c₀ k
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers c₀) := by
      rintro ⟨y, hy⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc2, one_zpow]
    have hle := le_pCoreOf_of_le_normalizer 2 hzle hzN hz2
    rw [hK2] at hle
    have h1 : c₀ = 1 := by
      have := hle (Subgroup.mem_zpowers c₀)
      exact Subgroup.mem_bot.mp this
    exact Subtype.ext (Subtype.ext h1)
  have hZodd : ¬ 2 ∣ Nat.card Z := by
    intro h2
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have h1 := hZinv c (by
      have : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
      have := congrArg (fun y : ↥Z => ((y : ↥Lb) : MulAut ↥V)) this
      simpa using this)
    rw [h1, orderOf_one] at hc
    norm_num at hc
  set Zm : Subgroup (MulAut ↥V) := Z.map Lb.subtype with hZm
  have hcl : ∀ c : ↥Z, ∀ l : ↥L, ((c : ↥Lb) : MulAut ↥V) * A4.actionOn V L hLV l =
      A4.actionOn V L hLV l * ((c : ↥Lb) : MulAut ↥V) := by
    intro c l
    have := Subgroup.mem_center_iff.mp c.2 ⟨_, (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩⟩
    exact (congrArg Subtype.val this).symm
  set J : Subgroup G := (fixV Zm).map V.subtype with hJ
  have hCJ : V ⊓ Subgroup.centralizer (L : Set G) ≤ J := by
    rintro x ⟨hxV, hxL⟩
    refine ⟨⟨x, hxV⟩, fun c hc => ?_, rfl⟩
    obtain ⟨c', -, rfl⟩ := hc
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (c' : ↥Lb).2
    change ((c' : ↥Lb) : MulAut ↥V) ⟨x, hxV⟩ = ⟨x, hxV⟩
    rw [← hl]
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    have hc := (Subgroup.mem_centralizer_iff.mp hxL) l l.2
    rw [hc, mul_inv_cancel_right]
  have hJV : J ≤ V := Subgroup.map_subtype_le _
  have hLJ : L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨A4.actionOn V L hLV ⟨l, hl⟩ w, fun c hc => ?_, ?_⟩
    · obtain ⟨c', hc', rfl⟩ := hc
      change ((c' : ↥Lb) : MulAut ↥V) (A4.actionOn V L hLV ⟨l, hl⟩ w) =
        A4.actionOn V L hLV ⟨l, hl⟩ w
      rw [← MulAut.mul_apply, hcl ⟨c', hc'⟩ ⟨l, hl⟩, MulAut.mul_apply]
      exact congrArg _ (hw _ ⟨c', hc', rfl⟩)
    · exact A4.actionOn_apply_coe hLV ⟨l, hl⟩ w
  have hZbot : Z = ⊥ := by
    rcases hirr J hCJ hJV hLJ with hJC | hJV'
    ·
      exfalso
      let _ : Fintype ↥Z := Fintype.ofFinite _
      let Nm : ↥V → ↥V := fun x => ∏ c : ↥Z, ((c : ↥Lb) : MulAut ↥V) x
      have hNmul : ∀ x y : ↥V, Nm (x * y) = Nm x * Nm y := by
        intro x y
        simp only [Nm, map_mul, Finset.prod_mul_distrib]
      let NmHom : ↥V →* ↥V :=
        { toFun := Nm
          map_one' := by simp [Nm]
          map_mul' := hNmul }
      have hfix : ∀ x : ↥V, Nm x ∈ fixV Zm := by
        intro x c hc
        obtain ⟨d, hd, rfl⟩ := hc
        change ((d : ↥Lb) : MulAut ↥V) (∏ c : ↥Z, ((c : ↥Lb) : MulAut ↥V) x) = Nm x
        rw [map_prod]
        refine Fintype.prod_equiv (Equiv.mulLeft (⟨d, hd⟩ : ↥Z)) _ _ fun c => ?_
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, MulAut.mul_apply]
      have hNmJ : ∀ x : ↥V, ((Nm x : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
        intro x
        rw [← hJC]
        exact ⟨Nm x, hfix x, rfl⟩
      have hNml : ∀ (l : ↥L) (x : ↥V), Nm (A4.actionOn V L hLV l x) = Nm x := by
        intro l x
        have h1 : Nm (A4.actionOn V L hLV l x) = A4.actionOn V L hLV l (Nm x) := by
          simp only [Nm, map_prod]
          refine Finset.prod_congr rfl fun c _ => ?_
          rw [← MulAut.mul_apply, hcl c l, MulAut.mul_apply]
        rw [h1]
        apply Subtype.ext
        rw [A4.actionOn_apply_coe]
        have hc := (Subgroup.mem_centralizer_iff.mp (hNmJ x).2) l l.2
        rw [hc, mul_inv_cancel_right]
      have hker' : ⁅V, oTwoUpper L⁆ ≤ (NmHom.ker).map V.subtype := by
        rw [Subgroup.commutator_le]
        intro x hx l hl
        refine ⟨⟨x, hx⟩ * (A4.actionOn V L hLV ⟨l, hOL hl⟩ ⟨x, hx⟩)⁻¹, ?_, ?_⟩
        · rw [SetLike.mem_coe, MonoidHom.mem_ker]
          change Nm _ = 1
          have hNinv : ∀ y : ↥V, Nm y⁻¹ = (Nm y)⁻¹ := fun y => by
            simp only [Nm, map_inv, Finset.prod_inv_distrib]
          rw [hNmul, hNinv, hNml, mul_inv_cancel]
        · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv,
            A4.actionOn_apply_coe, commutatorElement_def]
          group
      have hker : V ≤ (NmHom.ker).map V.subtype := hVL.le.trans hker'
      obtain ⟨y, hy, hyv⟩ := hker hv
      have hyv' : y = ⟨v, hv⟩ := Subtype.ext hyv
      subst hyv'
      have h1 : Nm ⟨v, hv⟩ = 1 := hy
      have hvfix : (⟨v, hv⟩ : ↥V) ∈ fixV Zm := by
        obtain ⟨w, hw, hwv⟩ := hCJ ⟨hv, hvL⟩
        rwa [show w = ⟨v, hv⟩ from Subtype.ext hwv] at hw
      have h2 : Nm ⟨v, hv⟩ = ⟨v, hv⟩ ^ Fintype.card ↥Z := by
        have hc : ∀ c : ↥Z, ((c : ↥Lb) : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ :=
          fun c => hvfix _ ⟨(c : ↥Lb), c.2, rfl⟩
        simp only [Nm, hc, Finset.prod_const, Finset.card_univ]
      have hodd : Odd (Fintype.card ↥Z) := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hZodd)
      obtain ⟨k, hk⟩ := hodd
      have hv2 : (⟨v, hv⟩ : ↥V) ^ 2 = 1 := Subtype.ext (by simpa using hV2 v hv)
      rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul] at h2
      rw [h2] at h1
      exact hv1 (congrArg Subtype.val h1)
    ·
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      refine MulEquiv.ext fun w => ?_
      have hw : (w : G) ∈ J := by rw [hJV']; exact w.2
      obtain ⟨w', hw', hww⟩ := hw
      rw [show w' = w from Subtype.ext hww] at hw'
      exact hw' _ ⟨c, hc, rfl⟩
  have hs : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hqb.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZbot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

end Central

end Lem12St

end CFSG.Quasithin.H13
