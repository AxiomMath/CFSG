module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zg
public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zd

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Lift3

theorem card_map_eq_of_ker_eq {X Y Z : Type*} [Group X] [Group Y] [Group Z] [Finite X]
    (f : X →* Y) (g : X →* Z) (h : f.ker = g.ker) (E : Subgroup X) :
    Nat.card ↥(E.map f) = Nat.card ↥(E.map g) := by
  have hf := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp E.subtype).ker
  have hg := Subgroup.card_eq_card_quotient_mul_card_subgroup (g.comp E.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    MonoidHom.range_comp, Subgroup.range_subtype] at hf hg
  have hk : (f.comp E.subtype).ker = (g.comp E.subtype).ker := by
    rw [← MonoidHom.comap_ker, ← MonoidHom.comap_ker, h]
  rw [hk] at hf
  have hpos : 0 < Nat.card ↥(g.comp E.subtype).ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (hf.symm.trans hg)

theorem ker_conj (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have := congrArg (fun φ : MulAut X => φ y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  · intro h
    refine MulEquiv.ext fun y => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← h y, mul_inv_cancel_right]

theorem pow_three_of_mem_closure {Y : Type*} [Group Y] {S : Set Y}
    (hS : S.Pairwise Commute) (h3 : ∀ s ∈ S, s ^ 3 = 1) :
    ∀ a ∈ Subgroup.closure S, a ^ 3 = 1 := by
  have : IsMulCommutative ↥(Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    have hcomm : a * b = b * a := congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [Commute.mul_pow hcomm 3, iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

theorem ker_eq_center {J M : Type*} [Group J] [Group M] [IsSimpleGroup M]
    (hq : CFSG.IsQuasisimple J) (ρ : J →* M) (hρ : Function.Surjective ρ)
    (hnab : ∃ a b : M, a * b ≠ b * a) : ρ.ker = Subgroup.center J := by
  obtain ⟨a, b, hab⟩ := hnab
  refine le_antisymm ?_ fun c hc => ?_
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ρ) with h | h
    · exfalso
      obtain ⟨a', rfl⟩ := hρ a
      obtain ⟨b', rfl⟩ := hρ b
      have ha : a' ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top a'
      have hb : b' ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top b'
      rw [MonoidHom.mem_ker] at ha hb
      exact hab (by rw [ha, hb])
    · exact h
  · have hcen : ρ c ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro m
      obtain ⟨m', rfl⟩ := hρ m
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc m']
    have hbot : Subgroup.center M = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
      · exact h
      · exfalso
        have hb : b ∈ Subgroup.center M := by rw [h]; exact Subgroup.mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
    rw [hbot, Subgroup.mem_bot] at hcen
    exact hcen

theorem pCore_le_ker {X M : Type*} [Group X] [Finite X] [Group M] [IsSimpleGroup M]
    (ρ : X →* M) (hρ : Function.Surjective ρ) {y : M} (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) :
    CFSG.pCore 2 X ≤ ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((CFSG.pCore 2 X).map ρ).Normal := CFSG.pCore_normal.map ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 X).map ρ) with h | h
  · rwa [Subgroup.map_eq_bot_iff] at h
  · exfalso
    have hm : y ∈ (CFSG.pCore 2 X).map ρ := by rw [h]; exact Subgroup.mem_top y
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨n, hn2⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨p, hp⟩
    have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn2
    have h2 : ρ p ^ 2 ^ n = 1 := by rw [← map_pow, hpn, map_one]
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num))] at hd
    exact hy1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))

theorem exists_centralizing {Q : Type*} [Group Q] {J : Subgroup Q} [J.Normal] [Finite J]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) ∣ 2) {x : Q}
    (hx3 : x ^ 3 = 1) : ∃ c : Q, x⁻¹ * c ∈ J ∧ ∀ j ∈ J, c * j = j * c := by
  have hα : (MulAut.conjNormal x : MulAut ↥J) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨j, hj⟩ := exists_conj_of_pow_three hout hα
  refine ⟨x * (j : Q)⁻¹, ?_, fun i hi => ?_⟩
  · rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact J.inv_mem j.2
  · have hi' : (j : Q)⁻¹ * i * j ∈ J := J.mul_mem (J.mul_mem (J.inv_mem j.2) hi) j.2
    have h1 : x * ((j : Q)⁻¹ * i * j) * x⁻¹ = (j : Q) * ((j : Q)⁻¹ * i * j) * (j : Q)⁻¹ := by
      have := congrArg (fun φ : MulAut ↥J => ((φ ⟨_, hi'⟩ : ↥J) : Q)) hj
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at this
      exact this
    calc x * (j : Q)⁻¹ * i = x * ((j : Q)⁻¹ * i * j) * x⁻¹ * (x * (j : Q)⁻¹) := by group
      _ = (j : Q) * ((j : Q)⁻¹ * i * j) * (j : Q)⁻¹ * (x * (j : Q)⁻¹) := by rw [h1]
      _ = i * (x * (j : Q)⁻¹) := by group

theorem three_le_pRank {Q : Type*} [Group Q] [Finite Q] {J : Subgroup Q} [J.Normal]
    {y₀ y₁ : ↥J} (hy : y₀ * y₁ = y₁ * y₀) (hy₀ : y₀ ^ 3 ∈ Subgroup.center ↥J)
    (hy₁ : y₁ ^ 3 ∈ Subgroup.center ↥J)
    (hcard : 9 ≤ Nat.card ↥(Subgroup.closure
      ({MulAut.conj y₀, MulAut.conj y₁} : Set (MulAut ↥J))))
    {c : Q} (hcJ : ∀ j ∈ J, c * j = j * c) (hc3 : c ^ 3 ∈ J) (hcJ' : c ∉ J) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hπ⟩ : ∃ π : Q →* MulAut ↥J × (Q ⧸ J),
      π = (MulAut.conjNormal).prod (QuotientGroup.mk' J) := ⟨_, rfl⟩
  have hπy : ∀ y : ↥J, π (y : Q) = (MulAut.conj y, 1) := fun y => by
    rw [hπ, MonoidHom.prod_apply, MulAut.conjNormal_val, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr y.2]
  have hπc : π c = (1, QuotientGroup.mk' J c) := by
    have h1 : (MulAut.conjNormal c : MulAut ↥J) = 1 := MulEquiv.ext fun j => Subtype.ext (by
      rw [MulAut.conjNormal_apply, MulAut.one_apply, hcJ j j.2, mul_inv_cancel_right])
    rw [hπ, MonoidHom.prod_apply, h1]
  have hconj : ∀ y : ↥J, y ^ 3 ∈ Subgroup.center ↥J → MulAut.conj (y ^ 3) = 1 := fun y hy => by
    rw [← MonoidHom.mem_ker, ker_conj]
    exact hy
  obtain ⟨S, hS⟩ : ∃ S : Set Q, S = {(y₀ : Q), (y₁ : Q), c} := ⟨_, rfl⟩
  have hcomm : ∀ u ∈ S, ∀ v ∈ S, Commute u v := by
    have h01 : Commute (y₀ : Q) (y₁ : Q) := congrArg Subtype.val hy
    have hc0 : Commute c (y₀ : Q) := hcJ _ y₀.2
    have hc1 : Commute c (y₁ : Q) := hcJ _ y₁.2
    intro u hu v hv
    rw [hS] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact h01 | exact h01.symm | exact hc0 | exact hc0.symm | exact hc1 | exact hc1.symm
  have hFc : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    have := Subgroup.isMulCommutative_closure (fun u hu v hv _ => hcomm u hu v hv)
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmap : (Subgroup.closure S).map π = Subgroup.closure (π '' S) := MonoidHom.map_closure _ _
  have h3 : ∀ a ∈ Subgroup.closure S, π a ^ 3 = 1 := by
    intro a ha
    have hmem : π a ∈ Subgroup.closure (π '' S) := hmap ▸ Subgroup.mem_map_of_mem π ha
    refine pow_three_of_mem_closure ?_ ?_ _ hmem
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _
      exact (hcomm u hu v hv).map π
    · rintro _ ⟨u, hu, rfl⟩
      rw [hS] at hu
      rcases hu with rfl | rfl | rfl
      · rw [hπy, Prod.pow_mk, one_pow, ← map_pow, hconj _ hy₀]
        rfl
      · rw [hπy, Prod.pow_mk, one_pow, ← map_pow, hconj _ hy₁]
        rfl
      · rw [hπc, Prod.pow_mk, one_pow, ← map_pow, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff _).mpr hc3]
        rfl
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Subgroup (MulAut ↥J),
      A₁ = Subgroup.closure {MulAut.conj y₀, MulAut.conj y₁} := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : Subgroup (Q ⧸ J),
      A₂ = Subgroup.zpowers (QuotientGroup.mk' J c) := ⟨_, rfl⟩
  have hle : A₁.prod A₂ ≤ (Subgroup.closure S).map π := by
    rw [Subgroup.prod_le_iff, hA₁, hA₂, MonoidHom.map_closure, MonoidHom.map_zpowers,
      Subgroup.closure_le, Subgroup.zpowers_le]
    refine ⟨?_, ⟨c, Subgroup.subset_closure (by rw [hS]; simp), by rw [hπc]; rfl⟩⟩
    rintro _ ⟨u, hu, rfl⟩
    rcases hu with rfl | rfl
    · exact ⟨(y₀ : Q), Subgroup.subset_closure (by rw [hS]; simp), by rw [hπy]; rfl⟩
    · exact ⟨(y₁ : Q), Subgroup.subset_closure (by rw [hS]; simp), by rw [hπy]; rfl⟩
  have hA₂c : Nat.card ↥A₂ = 3 := by
    rw [hA₂, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hc3
    · rw [QuotientGroup.mk'_apply]
      exact fun h => hcJ' ((QuotientGroup.eq_one_iff _).mp h)
  have hk : 3 ^ 3 ≤ Nat.card ↥((Subgroup.closure S).map π) := by
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr (Subgroup.prodEquiv A₁ A₂).toEquiv, Nat.card_prod, hA₂c] at h1
    rw [← hA₁] at hcard
    calc 3 ^ 3 = 9 * 3 := by norm_num
      _ ≤ Nat.card ↥A₁ * 3 := Nat.mul_le_mul_right 3 hcard
      _ ≤ _ := h1
  exact (le_pRank_of_image π hFc h3 hk).trans
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top)

theorem three_le_pRank_of_quasisimple {Q : Type*} [Group Q] [Finite Q] {J : Subgroup Q}
    [J.Normal] (hq : CFSG.IsQuasisimple ↥J) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hd : Nat.card W = 2 ^ 4) (ρ : ↥J →* MulAut W)
    (hρ : Function.Surjective ρ) (e : MulAut W ≃* alternatingGroup (Fin 8)) {x : Q}
    (hx3 : x ^ 3 = 1) (hxJ : x ∉ J) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have : IsSimpleGroup (MulAut W) := G31.isSimpleGroup_mulAut hW hd (by norm_num)
  have hker := ker_eq_center hq ρ hρ (G31.nonabelian_mulAut hW hd (by norm_num))
  have : Group.IsPerfect ↥J := hq.1
  have hout := card_outer_dvd_two ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).trans e))
  obtain ⟨c, hxc, hcJ⟩ := exists_centralizing hout hx3
  have hcx : QuotientGroup.mk' J c = QuotientGroup.mk' J x := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr hxc).symm
  have hc3 : c ^ 3 ∈ J := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hcx, ← map_pow, hx3,
      map_one]
  have hcJ' : c ∉ J := fun hc => hxJ (by
    have : x = c * (x⁻¹ * c)⁻¹ := by group
    rw [this]
    exact J.mul_mem hc (J.inv_mem hxc))
  obtain ⟨Y, Tau, hY3, hYc, hT, hT', hcard⟩ := exists_mulAut hW hd (k := 2) (by norm_num)
  obtain ⟨a, ha⟩ := hρ (Y 0)
  obtain ⟨b, hb⟩ := hρ (Y 1)
  obtain ⟨t, ht⟩ := hρ (Tau 0)
  have hkerc : ∀ g ∈ ρ.ker, ∀ h : ↥J, g * h = h * g := fun g hg h => by
    rw [hker] at hg
    exact (Subgroup.mem_center_iff.mp hg h).symm
  have hab := commute_of_central ρ hkerc (a := a) (b := b) (t := t)
    (by rw [map_pow, ha, hY3 0]) (by rw [ha, hb, hYc 0 1])
    (by rw [map_mul, map_mul, map_inv, ht, ha, hT 0])
    (by rw [map_mul, map_mul, map_inv, ht, hb, hT' 0 1 (by decide)])
  have hcen : ∀ (y : ↥J) (i : Fin 2), ρ y = Y i → y ^ 3 ∈ Subgroup.center ↥J :=
    fun y i hy => by rw [← hker, MonoidHom.mem_ker, map_pow, hy, hY3 i]
  have hcard9 : 9 ≤ Nat.card ↥(Subgroup.closure
      ({MulAut.conj a, MulAut.conj b} : Set (MulAut ↥J))) := by
    have h := card_map_eq_of_ker_eq MulAut.conj ρ (by rw [ker_conj, hker])
      (Subgroup.closure {a, b})
    rw [MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair, ha,
      hb] at h
    have hr : Set.range Y = {Y 0, Y 1} := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hr] at hcard
    rw [h]
    exact (by norm_num : (9 : ℕ) = 3 ^ 2).trans_le hcard
  exact three_le_pRank hab (hcen a 0 ha) (hcen b 1 hb) hcard9 hcJ hc3 hcJ'

end CFSG.Quasithin.Lift3

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

theorem exists_bar_surj {H L' : Subgroup G} (hL : L' ∈ cComp H) {M : Type*} [Group M]
    (ρ : ↥L' →* M) (hρ : Function.Surjective ρ) (hp : CFSG.pCore 2 ↥L' ≤ ρ.ker) :
    ∃ ρ' : ↥(modO2Image H L') →* M, Function.Surjective ρ' := by
  obtain ⟨e⟩ := modO2_mulEquiv hL
  refine ⟨(QuotientGroup.lift _ ρ hp).comp e.symm.toMonoidHom, fun m => ?_⟩
  obtain ⟨l, rfl⟩ := hρ m
  refine ⟨e (QuotientGroup.mk' _ l), ?_⟩
  show QuotientGroup.lift _ ρ hp (e.symm (e (QuotientGroup.mk' _ l))) = ρ l
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem pRank_modO2Image {H L' : Subgroup G} (hL : L' ∈ cComp H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup ↥(modO2Image H L')) = CFSG.Open.pRank p L' := by
  obtain ⟨e⟩ := modO2_mulEquiv hL
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e, pRank_modO2_eq L' hp hp2]

theorem mk_x_not_mem {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (V1 T L V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V1 T L V : Set G)) {I : Subgroup G}
    (hIC : I ≤ Subgroup.centralizer (V1 T L V : Set G)) (hxNx : x ∈ Nx T L V x) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(Nx T L V x)) ⟨x, hxNx⟩ ∉ modO2Image (Nx T L V x) I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨i, hi, hix⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hix
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Nx T L V x))) ⟨_, QuotientGroup.eq.mp hix⟩
  have hC1 := mem_C_of_two_pow hx3 hxN hxC (i⁻¹ * ⟨x, hxNx⟩ : ↥(Nx T L V x)).2 (m := m)
    (by simpa using congrArg Subtype.val (congrArg Subtype.val hm))
  have hiC : (i : G) ∈ Subgroup.centralizer (V1 T L V : Set G) :=
    hIC (Subgroup.mem_subgroupOf.mp hi)
  apply hxC
  have e : x = (i : G) * ((i⁻¹ * ⟨x, hxNx⟩ : ↥(Nx T L V x)) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ hiC hC1

variable (s : Set714 G T L V t z)
include s

theorem mulAut_quot_equiv
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    Nonempty (MulAut (↥(Ut T L V z) ⧸ X1 T L V z) ≃* alternatingGroup (Fin 8)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq2, hq4⟩ := s.quot_facts h1222 hd
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : ↥(Ut T L V z) ⧸ X1 T L V z => mul_comm a b) hq2 hq4
  exact ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

theorem exists_I
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h39 : A39ForSQTK)
    (hHs : Hs T L V z = ⊤) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    ∃ I ∈ cComp (Subgroup.centralizer (V1 T L V : Set G)), ∃ hID : I ≤ D0 T L V z,
      Function.Surjective (rho1.comp (Subgroup.inclusion hID)) := by
  obtain ⟨I', hI', htop⟩ := s.exists_cComp_C h1222 h39 hHs hd
  have hID : I'.map (Subgroup.centralizer (V1 T L V : Set G)).subtype ≤ D0 T L V z :=
    (Subgroup.map_subtype_le I').trans s.C_le_D0
  refine ⟨_, map_subtype_mem_cComp hI', hID, fun φ => ?_⟩
  have hφ : φ ∈ I'.map (rho1.comp (Subgroup.inclusion s.C_le_D0)) := by
    rw [htop]
    exact Subgroup.mem_top φ
  obtain ⟨i, hi, rfl⟩ := hφ
  exact ⟨⟨i, Subgroup.mem_map_of_mem _ hi⟩, rfl⟩

theorem dim_ne_five
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2)
    (h36 : CFSG.QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hrank : Lemma122Rank)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy := s.setting.hyp.hyp
  have hHs := (s.Hs_eq_top h1222 h37 h38 h39 hU).1
  obtain ⟨hq2, hq4⟩ := s.quot_facts h1222 hd
  obtain ⟨-, hnab⟩ := s.mulAut_quot_simple h1222 hd
  have := (s.mulAut_quot_simple h1222 hd).1
  obtain ⟨eA⟩ := s.mulAut_quot_equiv h1222 hd
  obtain ⟨Y, -, hY3, hYc, -, -, hcard⟩ := Lift3.exists_mulAut hq2 hq4 (k := 2) (by norm_num)
  obtain ⟨ha1, hba⟩ := lift3_pair hY3 hcard
  obtain ⟨x, -, hx3, hxN, hxC⟩ := s.exists_x h1222
  have hN2 := s.pCoreOf_Nx_ne_bot h1222 hxN
  obtain ⟨I, hIC, hID, hρI⟩ := s.exists_I h1222 h39 hHs hd
  have hIN : I ∈ cComp (Nx T L V x) :=
    cComp_mem_of_subnormal (A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (Nx_le_normalizer_C hxN))) hIC
  obtain ⟨ρJ, hρJ⟩ := exists_bar_surj hIN _ hρI (Lift3.pCore_le_ker _ hρI ha1 (hY3 0))
  have hQ := CFSG.Quasithin.sqtkHyp_quotient_of_pCoreOf_ne_bot hy.qtke hy.simple hy.nonabelian
    hN2
  have hcore := h36 _ hQ.toCat _ (modO2Image_mem_cComp hIN)
  have hnot := Lift3.not_threeRankLeOne ρJ hρJ (hY3 0) (hY3 1) (hYc 0 1) ha1 hba
  have hq : CFSG.IsQuasisimple ↥(modO2Image (Nx T L V x) I) := by
    rcases hcore.1 with hcomp | h3 | h4
    · exact hcomp.1
    · exact absurd (Lift3.threeRankLeOne_of_case3' h3) hnot
    · exact absurd (Lift3.threeRankLeOne_of_case4' h4) hnot
  have hkerJ := Lift3.ker_eq_center hq ρJ hρJ hnab
  have hlow := Lift3.le_pRank_of_surjective hq2 hq4 (k := 2) (by norm_num) ρJ hρJ
    (fun c hc g => by
      rw [hkerJ] at hc
      exact (Subgroup.mem_center_iff.mp hc g).symm)
  have hm3 : CFSG.Open.pRank 3 I = 2 := by
    have e1 := pRank_modO2Image hIN Nat.prime_three (by norm_num)
    have e2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_of_mem_cComp hIN)
    have e3 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hy.qtke hN2 Nat.prime_three
      (by norm_num)
    omega
  have hIn := CFSG.Quasithin.lemma_1_2_2_b hy.qtke hy.simple hy.nonabelian h37 h38 hrank hN2
    hIN Nat.prime_three (by norm_num) hm3
  have hJn : (modO2Image (Nx T L V x) I).Normal :=
    hIn.map _ (QuotientGroup.mk'_surjective _)
  have hxNx : x ∈ Nx T L V x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hx3' : (QuotientGroup.mk' (CFSG.pCore 2 ↥(Nx T L V x)) ⟨x, hxNx⟩) ^ 3 = 1 := by
    have : (⟨x, hxNx⟩ : ↥(Nx T L V x)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, this, map_one]
  have h3 := Lift3.three_le_pRank_of_quasisimple hq hq2 hq4 ρJ hρJ eA hx3'
    (mk_x_not_mem hx3 hxN hxC (le_of_mem_cComp hIC) hxNx)
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥(Nx T L V x)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥(Nx T L V x)))
    rw [hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have e3 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥(Nx T L V x)) hN3
  have e4 := CFSG.Quasithin.pRank_top_subtype (p := 3) (Nx T L V x)
  have e5 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hy.qtke hN2 Nat.prime_three
    (by norm_num)
  omega

end CFSG.Quasithin.H13.S127.L715.Set714
