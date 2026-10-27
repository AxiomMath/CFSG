module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56C
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57Defs
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS1
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Matrix
open Sp6Over (GL6 M6 V7)

variable {G : Type} [Group G] [Finite G]

namespace S57

theorem frattini {C K : Type*} [Group C] [Finite C] [Group K] (ψ : C →* K)
    (hker : IsPGroup 2 ψ.ker) {u : C} (hu : orderOf u = 3) {g : C}
    (hg : ψ g * ψ u = ψ u * ψ g) : ∃ d : C, d * u = u * d ∧ ψ d = ψ g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk3 : ∀ y : C, ψ y = 1 → y ^ 3 = 1 → y = 1 := by
    intro y hy h3
    obtain ⟨n, hn⟩ := hker ⟨y, hy⟩
    have h1 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd : orderOf y ∣ Nat.gcd (2 ^ n) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h3)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : ψ u ≠ 1 := fun h => by
    have := hk3 u h hu3
    rw [this, orderOf_one] at hu
    omega
  have hψu : orderOf (ψ u) = 3 := orderOf_eq_prime (by rw [← map_pow, hu3, map_one]) hu1
  set N := (Subgroup.zpowers (ψ u)).comap ψ with hN
  have huN : u ∈ N := Subgroup.mem_zpowers _
  set x := g * u * g⁻¹ with hx
  have hψx : ψ x = ψ u := by rw [hx, map_mul, map_mul, hg, map_inv, mul_inv_cancel_right]
  have hxN : x ∈ N := by
    change ψ x ∈ Subgroup.zpowers (ψ u)
    rw [hψx]; exact Subgroup.mem_zpowers _
  set ψN := ψ.comp N.subtype with hψN
  have hkerN : IsPGroup 2 ψN.ker := fun k => by
    obtain ⟨n, hn⟩ := hker ⟨((k : N) : C), k.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkerN
  have hrange : ψN.range = Subgroup.zpowers (ψ u) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨⟨u, huN⟩, rfl⟩)
    rintro _ ⟨k, rfl⟩
    exact k.2
  have hNc : Nat.card N = 2 ^ n * 3 := by
    rw [← Subgroup.card_ker_mul_card_range ψN, hn, hrange, Nat.card_zpowers, hψu]
  have hsyl : ∀ y : N, orderOf y = 3 →
      ∃ P : Sylow 3 N, (P : Subgroup N) = Subgroup.zpowers y := by
    intro y hy
    have hP : IsPGroup 3 (Subgroup.zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
    have hidx : ¬ 3 ∣ (Subgroup.zpowers y).index := by
      have h := (Subgroup.zpowers y).index_mul_card
      rw [Nat.card_zpowers, hy, hNc] at h
      have h' : (Subgroup.zpowers y).index = 2 ^ n := by omega
      rw [h']
      exact fun h3 => by
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
        omega
    exact ⟨hP.toSylow hidx, IsPGroup.toSylow_coe hP hidx⟩
  have hoN : orderOf (⟨u, huN⟩ : N) = 3 := by rw [Subgroup.orderOf_mk, hu]
  have hoX : orderOf (⟨x, hxN⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    change orderOf ((MulAut.conj g).toMonoidHom u) = 3
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u).trans hu
  obtain ⟨P, hP⟩ := hsyl _ hoN
  obtain ⟨Q, hQ⟩ := hsyl _ hoX
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq N Q P
  have hmx : m * ⟨x, hxN⟩ * m⁻¹ ∈ Subgroup.zpowers (⟨u, huN⟩ : N) := by
    rw [← hP, ← hm, Sylow.coe_subgroup_smul]
    have : (⟨x, hxN⟩ : N) ∈ (Q : Subgroup N) := by rw [hQ]; exact Subgroup.mem_zpowers _
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj m) _ this
    simpa [MulAut.smul_def, MulAut.conj_apply] using h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmx
  have hk' : u ^ k = (m : C) * x * (m : C)⁻¹ := by
    simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (m.2 : ψ (m : C) ∈ Subgroup.zpowers (ψ u))
  set d₀ := (m : C) * g with hd₀
  have hcomm : ψ (m : C) * ψ u = ψ u * ψ (m : C) := by
    rw [← hj]; exact (Commute.zpow_self (ψ u) j).eq
  have hd₀u : d₀ * u * d₀⁻¹ = u := by
    have h1 : d₀ * u * d₀⁻¹ = u ^ k := by rw [hk', hd₀, hx]; group
    have e1 : ψ (d₀ * u * d₀⁻¹) = ψ u := by
      have : ψ (d₀ * u * d₀⁻¹) = ψ (m : C) * (ψ g * ψ u) * (ψ g)⁻¹ * (ψ (m : C))⁻¹ := by
        rw [hd₀]; simp only [map_mul, map_inv, _root_.mul_inv_rev]; group
      rw [this, hg, ← mul_assoc, hcomm]; group
    have h2 : ψ (u ^ (k - 1)) = 1 := by
      rw [_root_.zpow_sub_one, map_mul, map_inv, ← h1, e1, mul_inv_cancel]
    have h3 : (u ^ (k - 1)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu3,
        _root_.one_zpow]
    have h4 := hk3 _ h2 h3
    rw [h1, show k = (k - 1) + 1 by ring, _root_.zpow_add_one, h4, one_mul]
  refine ⟨u ^ (-j) * d₀, ?_, ?_⟩
  · have hd : d₀ * u = u * d₀ := by
      calc d₀ * u = d₀ * u * d₀⁻¹ * d₀ := by group
        _ = u * d₀ := by rw [hd₀u]
    calc u ^ (-j) * d₀ * u = u ^ (-j) * (u * d₀) := by rw [mul_assoc, hd]
      _ = u * (u ^ (-j) * d₀) := by
        simp only [← mul_assoc, (Commute.zpow_self u (-j)).eq]
  · rw [map_mul, map_zpow, hd₀, map_mul, ← mul_assoc, ← hj, ← _root_.zpow_add, neg_add_cancel,
      zpow_zero, one_mul]

theorem cenS_pair_le_right (a c : G) : CenS (Subgroup.closure {a, c}) ≤ Cen c := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_cenS_pair_iff.mp hx).2

theorem cenS_pair_le_left (a c : G) : CenS (Subgroup.closure {a, c}) ≤ Cen a := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_cenS_pair_iff.mp hx).1

end S57

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section MBasic

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)

theorem S57.J_le_cenS (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀) :
    OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ CenS (Subgroup.closure {β' b₂ b₃, s₀}) :=
  fun j hj => by
  have hj' : j ∈ CenS (Subgroup.closure {b₂, b₃}) := Subgroup.map_subtype_le _ hj
  obtain ⟨h2, h3⟩ := mem_cenS_pair_iff.mp hj'
  exact mem_cenS_pair_iff.mpr ⟨(Commute.mul_right (show Commute j b₂ from h2)
    (Commute.pow_right (show Commute j b₃ from h3) 2)).eq,
    Subgroup.mem_centralizer_singleton_iff.mp (hJs hj)⟩

theorem S57.M_le_cenS (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀) :
    M₅₇ b b₁ b₂ b₃ s₀ ≤ CenS (Subgroup.closure {β' b₂ b₃, s₀}) :=
  sup_le (S57.J_le_cenS hJs) inf_le_left

theorem S57.M_le_cen (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀) :
    M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen s₀ :=
  (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_right _ _)

include h5

theorem FF81Sec5.u_mem_M : b₂ * b₃ ∈ M₅₇ b b₁ b₂ b₃ s₀ :=
  Subgroup.mem_sup_right ⟨mem_cenS_pair_iff.mpr ⟨h5.β_comm_A₁ h5.u_mem_A₁, h5.s₀_comm h5.u_mem_A₁⟩,
    Subgroup.le_normalizer h5.u_mem_A₁⟩

include hJs in
theorem FF81Sec5.zpowers_β_inf_M :
    Subgroup.zpowers (β' b₂ b₃) ⊓ M₅₇ b b₁ b₂ b₃ s₀ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨hxβ, hxM⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hxβ)
  have hcube : (β' b₂ b₃ ^ n) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h5.β_cube, one_pow]
  have hc : β' b₂ b₃ ^ n * s₀ = s₀ * β' b₂ b₃ ^ n :=
    Subgroup.mem_centralizer_singleton_iff.mp (S57.M_le_cen hJs hxM)
  have hinv := h5.s₀_β_pow n
  rw [← hc, mul_inv_cancel_right] at hinv
  have h2 : (β' b₂ b₃ ^ n) ^ 2 = 1 := by
    rw [sq]; nth_rw 2 [hinv]; exact mul_inv_cancel _
  calc β' b₂ b₃ ^ n = (β' b₂ b₃ ^ n) ^ 3 * ((β' b₂ b₃ ^ n) ^ 2)⁻¹ := by group
    _ = 1 := by rw [hcube, h2, inv_one, one_mul]

theorem FF81Sec5.dvd_card_M (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀) :
    81 ∣ Nat.card (M₅₇ b b₁ b₂ b₃ s₀) := by
  obtain ⟨-, hA₁H, hrel, -, -⟩ := c2
  have hr := Subgroup.relIndex_mul_card (H := CenS (A₁sub b b₁ b₂ b₃)) (K := H₅₂ b b₁ b₂ b₃ s₀)
  rw [hrel] at hr
  have h27 : 27 ∣ Nat.card ↥(CenS (A₁sub b b₁ b₂ b₃) ⊓ H₅₂ b b₁ b₂ b₃ s₀) := by
    rw [← h5.coordA.card]
    exact Subgroup.card_dvd_of_le (le_inf (fun a ha => Subgroup.mem_centralizer_iff.mpr
      fun c hc => h5.A₁_comm hc ha) hA₁H)
  have hH : 81 ∣ Nat.card (H₅₂ b b₁ b₂ b₃ s₀) := by
    rw [← hr]
    exact Dvd.dvd.trans (by norm_num : (81 : ℕ) ∣ 48 * 27) (Nat.mul_dvd_mul_left 48 h27)
  exact hH.trans (Subgroup.card_dvd_of_le le_sup_right)

include hJs in
theorem FF81Sec5.M_inf_S : M₅₇ b b₁ b₂ b₃ s₀ ⊓ Op 2 (Cen s₀) = ⊥ := by
  by_contra hne
  have hA₁M : ∀ {a : G}, a ∈ A₁sub b b₁ b₂ b₃ → a ∈ M₅₇ b b₁ b₂ b₃ s₀ := fun ha =>
    Subgroup.mem_sup_right ⟨mem_cenS_pair_iff.mpr ⟨h5.β_comm_A₁ ha, h5.s₀_comm ha⟩,
      Subgroup.le_normalizer ha⟩
  have hle :
      B ≤ Subgroup.normalizer ((M₅₇ b b₁ b₂ b₃ s₀ ⊓ Op 2 (Cen s₀) : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨v, rfl⟩ := h5.ε_surj hx
    have hv : v = ![v 0, v 1, v 2 - (v 3 - v 2), v 2 - (v 3 - v 2)] +
        (v 3 - v 2) • ![0, 0, 1, 2] := by
      ext j; fin_cases j <;> simp <;> ring
    rw [hv, h5.ε_add, h5.ε_smul, h5.ε_β]
    refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ ?_ _)
    · have ha := h5.mem_A₁_of (v := ![v 0, v 1, v 2 - (v 3 - v 2), v 2 - (v 3 - v 2)]) rfl
      have haM := hA₁M ha
      have has := h5.A₁_le_cen_s₀ ha
      exact Subgroup.mem_normalizer_fintype fun y hy => Subgroup.mem_inf.mpr
        ⟨(M₅₇ b b₁ b₂ b₃ s₀).mul_mem ((M₅₇ b b₁ b₂ b₃ s₀).mul_mem haM hy.1)
          ((M₅₇ b b₁ b₂ b₃ s₀).inv_mem haM), op_two_conj has hy.2⟩
    · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have hc : y * β' b₂ b₃ = β' b₂ b₃ * y := (mem_cenS_pair_iff.mp (S57.M_le_cenS hJs hy.1)).1
      rw [← hc, mul_inv_cancel_right]; exact hy
  have := FF79.AS.four_le_localRank_of hne ((op_two_isPGroup s₀).to_le inf_le_right) h5.hE hle
  rw [h5.basis.rank3] at this
  omega

end MBasic

section PartA

variable (hKF : KF_Sp6Levi) (hKC : KF_Sp6ShortRootCen)
  (hGL : KF_Sp4CenGL6) (hS6 : KF_Sp6GL6Cen) (hMcL : KF_McLaughlin6)
  (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (hbig : h5.Big)
  (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀) (c4 : FF81Conc5_4 b b₁ b₂ b₃ s₀)
include hKF hKC hGL hS6 hMcL h5 hbig c2 c4

theorem FF81Sec5.ff81_5_7a :
    StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1 ∧
      setMul (Op 2 (Cen s₀)) (M₅₇ b b₁ b₂ b₃ s₀) = Cen s₀ := by
  obtain ⟨⟨e⟩, hJs, -, -⟩ := c4
  obtain ⟨κ, hκ⟩ := h5.exists_coord hbig
  have hcen := h5.cenS_center hKF hKC hbig c2
  obtain ⟨hu'3, h16, hφ1, hD⟩ := h5.rhoD_facts hKF hKC hGL hbig c2 e hJs κ hκ
  set ρ := S56.rhoBar h5.hs₀ κ hκ with hρ
  have hker : ∀ {g : G} (hg : g ∈ Cen s₀), ρ ⟨g, hg⟩ = 1 → g ∈ Op 2 (Cen s₀) :=
    fun hg h1 => S56.mem_S_of_rhoBar_eq_one h5.hs₀ κ hκ hcen hg h1
  have hkerp : IsPGroup 2 ρ.ker := fun k => by
    obtain ⟨n, hn⟩ := op_two_isPGroup s₀ ⟨_, hker (k : ↥(Cen s₀)).2 k.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hMs := S57.M_le_cen (b := b) (b₁ := b₁) hJs
  have hDs : Cen s₀ ⊓ Cen (b₂ * b₃) ≤ Cen s₀ := inf_le_left
  set ρM : ↥(M₅₇ b b₁ b₂ b₃ s₀) →* GL6 := ρ.comp (Subgroup.inclusion hMs) with hρM
  have hinj : Function.Injective ρM := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : (m : G) ∈ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Op 2 (Cen s₀) :=
      Subgroup.mem_inf.mpr ⟨m.2, hker (hMs m.2) hm⟩
    rw [h5.M_inf_S hJs, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  set X := ρM.range with hX
  set Y := ρ.range with hY
  set ψ := S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) with hψ
  set φ := S56.rhoJ h5.hs₀ κ hκ (FF81Sec5.J_le_D hJs) e with hφ
  set u' := ψ ⟨b₂ * b₃, h5.u_mem_D⟩ with hu'
  have hXY : X ≤ Y := by
    rintro _ ⟨m, rfl⟩
    exact ⟨_, rfl⟩
  have hfr : Y ⊓ Subgroup.centralizer {u'} ≤ ψ.range := by
    intro y hy
    obtain ⟨⟨g, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    obtain ⟨d, hdu, hdg⟩ := S57.frattini ρ hkerp (u := ⟨b₂ * b₃, hDs h5.u_mem_D⟩)
      (by rw [Subgroup.orderOf_mk, h5.orderOf_u]) hc
    refine ⟨⟨d, Subgroup.mem_inf.mpr ⟨d.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg Subtype.val hdu)⟩⟩, ?_⟩
    exact hdg
  have hφX : φ.range ≤ X := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨⟨(e.symm σ : G), Subgroup.mem_sup_left (e.symm σ).2⟩, rfl⟩
  have hu'X : u' ∈ X := ⟨⟨b₂ * b₃, h5.u_mem_M⟩, rfl⟩
  have hψc : ψ.range ≤ Subgroup.centralizer {u'} := by
    rintro _ ⟨d, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hu', ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).2))
  have hXc : X ⊓ Subgroup.centralizer {u'} = φ.range ⊔ Subgroup.zpowers u' := by
    rw [← hD]
    refine le_antisymm ((inf_le_inf_right _ hXY).trans hfr) (le_inf ?_ hψc)
    rw [hD]; exact sup_le hφX (Subgroup.zpowers_le.mpr hu'X)
  have hYc : Y ⊓ Subgroup.centralizer {u'} = φ.range ⊔ Subgroup.zpowers u' := by
    rw [← hD]
    refine le_antisymm hfr (le_inf ?_ hψc)
    rintro _ ⟨d, rfl⟩
    exact ⟨_, rfl⟩
  have hMc : Nat.card X = Nat.card (M₅₇ b b₁ b₂ b₃ s₀) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h81X : 81 ∣ Nat.card X := by rw [hMc]; exact h5.dvd_card_M c2
  have h81Y : 81 ∣ Nat.card Y := h81X.trans (Subgroup.card_dvd_of_le hXY)
  obtain ⟨hXcard, hXtr, hXirr⟩ := hS6 X u' φ hu'3 h16 hφ1 hXc h81X
  obtain ⟨hYcard, -, -⟩ := hS6 Y u' φ hu'3 h16 hφ1 hYc h81Y
  have hXY' : X = Y := Subgroup.eq_of_le_of_card_ge hXY (by rw [hXcard, hYcard])
  refine ⟨?_, ?_⟩
  · rcases hMcL X hXirr hXtr with htop | hmod | h1 | h1 | h1
    · exfalso
      have := hXcard
      rw [htop, Subgroup.card_top, Matrix.card_GL_field, ZMod.card] at this
      norm_num [Fin.prod_univ_succ] at this
    · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (MonoidHom.ofInjective hinj).symm hmod
    all_goals (rw [hXcard] at h1; norm_num at h1)
  · ext g
    simp only [setMul, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨s, hs, m, hm, rfl⟩
      exact (Cen s₀).mul_mem (op_two_le s₀ hs) (hMs hm)
    · intro hg
      have hy : ρ ⟨g, hg⟩ ∈ X := by rw [hXY']; exact ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨m, hm⟩ := hy
      refine ⟨g * (m : G)⁻¹, hker ((Cen s₀).mul_mem hg ((Cen s₀).inv_mem (hMs m.2))) ?_, m, m.2,
        by group⟩
      have : (⟨g * (m : G)⁻¹, (Cen s₀).mul_mem hg ((Cen s₀).inv_mem (hMs m.2))⟩ : ↥(Cen s₀)) =
          ⟨g, hg⟩ * (Subgroup.inclusion hMs m)⁻¹ := rfl
      rw [this, map_mul, map_inv]
      change ρ ⟨g, hg⟩ * (ρM m)⁻¹ = 1
      rw [hm, mul_inv_cancel]

end PartA

end CFSG.RankThree.PartTwo.Sec21.FF81
