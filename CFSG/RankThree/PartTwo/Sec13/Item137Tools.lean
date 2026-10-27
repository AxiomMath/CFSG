module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section AutIn

variable {G : Type*} [Group G]

theorem autIn_eq_range (H X : Subgroup G) :
    Sec4.autIn H X = (X.normalizerMonoidHom.comp
      (Subgroup.inclusion (inf_le_right : H ⊓ Subgroup.normalizer (X : Set G) ≤ _))).range := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem nonempty_autIn_equiv_of_normalizer_eq {H X Y : Subgroup G}
    (hN : H ⊓ Subgroup.normalizer (X : Set G) = H ⊓ Subgroup.normalizer (Y : Set G))
    (hC : ∀ h ∈ H ⊓ Subgroup.normalizer (X : Set G),
      (∀ x ∈ X, h * x * h⁻¹ = x) ↔ (∀ y ∈ Y, h * y * h⁻¹ = y)) :
    Nonempty (Sec4.autIn H X ≃* Sec4.autIn H Y) := by
  set D := H ⊓ Subgroup.normalizer (X : Set G) with hD
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := hN ▸ inf_le_right
  let fX : D →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  let fY : D →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hDY)
  have hX : Sec4.autIn H X = fX.range := autIn_eq_range H X
  have hY : Sec4.autIn H Y = fY.range := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, Sec4.autIn]
    congr 1
    ext g
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      rw [← hN] at hg
      exact hg
    · intro hg
      rw [← hN]
      exact hg
  have hker : fX.ker = fY.ker := by
    ext d
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hd
      have h1 : ∀ x ∈ X, (d : G) * x * (d : G)⁻¹ = x := fun x hx =>
        congrArg (fun σ : MulAut X => ((σ ⟨x, hx⟩ : X) : G)) hd
      have h2 := (hC d d.2).mp h1
      ext y
      exact h2 y y.2
    · intro hd
      have h1 : ∀ y ∈ Y, (d : G) * y * (d : G)⁻¹ = y := fun y hy =>
        congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : G)) hd
      have h2 := (hC d d.2).mpr h1
      ext x
      exact h2 x x.2
  exact ⟨(MulEquiv.subgroupCongr hX).trans ((QuotientGroup.quotientKerEquivRange fX).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange fY).trans (MulEquiv.subgroupCongr hY.symm))))⟩

theorem inf_normalizer_zpowers_sup {H Y : Subgroup G} {c : G}
    (hcH : ∀ h ∈ H, h * c = c * h) (hY : (Subgroup.zpowers c ⊔ Y) ⊓ H = Y) :
    H ⊓ Subgroup.normalizer ((Subgroup.zpowers c ⊔ Y : Subgroup G) : Set G) =
      H ⊓ Subgroup.normalizer (Y : Set G) := by
  have hconjc : ∀ h ∈ H, (Subgroup.zpowers c).map (MulAut.conj h : G →* G) =
      Subgroup.zpowers c := fun h hh => by
    rw [MonoidHom.map_zpowers]
    congr 1
    change h * c * h⁻¹ = c
    rw [hcH h hh, mul_inv_cancel_right]
  ext h
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hh, hN⟩
    refine ⟨hh, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hN ⊢
    rw [← hY, Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective, hN]
    congr 1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
  · rintro ⟨hh, hN⟩
    refine ⟨hh, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hN ⊢
    rw [Subgroup.map_sup, hconjc h hh, hN]

theorem nonempty_autIn_sup_equiv {H Y : Subgroup G} {c : G}
    (hcH : ∀ h ∈ H, h * c = c * h) (hY : (Subgroup.zpowers c ⊔ Y) ⊓ H = Y) :
    Nonempty (Sec4.autIn H (Subgroup.zpowers c ⊔ Y) ≃* Sec4.autIn H Y) := by
  set X := Subgroup.zpowers c ⊔ Y with hXdef
  refine nonempty_autIn_equiv_of_normalizer_eq (inf_normalizer_zpowers_sup hcH hY) ?_
  intro h hh
  constructor
  · intro hx y hy
    exact hx y ((le_sup_right : Y ≤ X) hy)
  · intro hy x hx
    have hle : X ≤ Subgroup.centralizer ({h} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hcH h hh.1).symm
      · intro y hyY
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hy y hyY
        calc y * h = h * y * h⁻¹ * h := by rw [this]
          _ = h * y := by group
    have hxc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    rw [← hxc, mul_inv_cancel_right]

theorem autIn_inf_normalizer_eq {H Y : Subgroup G} {c : G}
    (hcH : ∀ h ∈ H, h * c = c * h) (hY : (Subgroup.zpowers c ⊔ Y) ⊓ H = Y) :
    Sec4.autIn (H ⊓ Subgroup.normalizer ((Subgroup.zpowers c ⊔ Y : Subgroup G) : Set G)) Y =
      Sec4.autIn H Y := by
  rw [Sec4.autIn, Sec4.autIn, inf_normalizer_zpowers_sup hcH hY, inf_assoc, inf_idem]

end AutIn

section Quot

variable {Λ : Type*} [Group Λ] [Finite Λ]

@[expose] noncomputable def mkEquivOfIsPGroup {X : Subgroup Λ} (hX : IsPGroup 3 X) :
    X ≃* X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) :=
  (MonoidHom.ofInjective (f := (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)).comp X.subtype)
    (fun a b hab => Subtype.ext (injOn_mk_of_isPGroup Nat.prime_three hX a.2 b.2 hab))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem mkEquivOfIsPGroup_apply {X : Subgroup Λ} (hX : IsPGroup 3 X) (x : X) :
    ((mkEquivOfIsPGroup hX x : X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) :
      Λ ⧸ aschbacherSolvableCore 3 Λ) = QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) x :=
  rfl

theorem map_autIn_top_mk {X : Subgroup Λ} (hX : IsPGroup 3 X) :
    (Sec4.autIn ⊤ X).map (MulAut.congr (mkEquivOfIsPGroup hX)).toMonoidHom =
      Sec4.autIn ⊤ (X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 X) := ⟨hX⟩
  set N := aschbacherSolvableCore 3 Λ with hNdef
  set π := QuotientGroup.mk' N with hπ
  set e := mkEquivOfIsPGroup hX with he
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
  have hNorm : Subgroup.normalizer ((X.map π : Subgroup _) : Set _) =
      (Subgroup.normalizer (X : Set Λ)).map π :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 X N inferInstance hcop
  have hcongr : ∀ (h : Λ) (hh : h ∈ Subgroup.normalizer (X : Set Λ))
      (hh' : π h ∈ Subgroup.normalizer ((X.map π : Subgroup _) : Set _)),
      MulAut.congr e (X.normalizerMonoidHom ⟨h, hh⟩) =
        (X.map π).normalizerMonoidHom ⟨π h, hh'⟩ := by
    intro h hh hh'
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change ((e (X.normalizerMonoidHom ⟨h, hh⟩ (e.symm (e x))) : _) : Λ ⧸ N) =
      π h * (e x : Λ ⧸ N) * (π h)⁻¹
    rw [MulEquiv.symm_apply_apply, he, mkEquivOfIsPGroup_apply, mkEquivOfIsPGroup_apply,
      Sec4.normalizerMonoidHom_apply_coe, map_mul, map_mul, map_inv]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h, hh, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    have hh' : π h ∈ Subgroup.normalizer ((X.map π : Subgroup _) : Set _) := by
      rw [hNorm]
      exact Subgroup.mem_map_of_mem π hh
    exact Sec4.mem_autIn_iff.mpr ⟨π h, hh', Subgroup.mem_top _, (hcongr h hh hh').symm⟩
  · intro hσ
    obtain ⟨g, hg, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hg' := hg
    rw [hNorm] at hg'
    obtain ⟨h, hh, rfl⟩ := hg'
    exact ⟨X.normalizerMonoidHom ⟨h, hh⟩,
      Sec4.mem_autIn_iff.mpr ⟨h, hh, Subgroup.mem_top _, rfl⟩, hcongr h hh hg⟩

theorem nonempty_autIn_top_mk_equiv {X : Subgroup Λ} (hX : IsPGroup 3 X) :
    Nonempty (Sec4.autIn ⊤ X ≃*
      Sec4.autIn ⊤ (X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)))) :=
  ⟨((Sec4.autIn ⊤ X).equivMapOfInjective _
    (MulAut.congr (mkEquivOfIsPGroup hX)).injective).trans
    (MulEquiv.subgroupCongr (map_autIn_top_mk hX))⟩

end Quot

section E27

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zpow_eq_one_of_zpow_mem {c : G} (hc3 : c ^ 3 = 1) {M : Subgroup G} (hcM : c ∉ M) {k : ℤ}
    (hk : c ^ k ∈ M) : c ^ k = 1 := by
  have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hck : c ^ k = c ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show (c ^ (3 : ℤ)) = 1 by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hc3], one_zpow, one_mul]
  have h3 : 0 ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg k (by norm_num), Int.emod_lt_of_pos k
    (by norm_num)⟩
  rw [hck] at hk ⊢
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hk
    exact absurd hk hcM
  · exfalso
    rw [h] at hk
    have h4 : c ^ (2 : ℤ) * c ^ (2 : ℤ) ∈ M := M.mul_mem hk hk
    rw [← zpow_add, show (2 : ℤ) + 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
      show (c ^ (3 : ℤ)) = 1 by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hc3], one_mul] at h4
    exact hcM h4

omit [Finite G] in
theorem zpowers_inf_eq_bot {c : G} (hc3 : c ^ 3 = 1) {M : Subgroup G} (hcM : c ∉ M) :
    Subgroup.zpowers c ⊓ M = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxM⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Subgroup.mem_bot).mpr (zpow_eq_one_of_zpow_mem hc3 hcM hxM)

omit [Finite G] in
theorem card_zpowers_of_pow_three {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Nat.card (Subgroup.zpowers c) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]

theorem zpowers_sup_inf_eq {c : G} (hc3 : c ^ 3 = 1) {M Y : Subgroup G} (hcM : c ∉ M)
    (hYM : Y ≤ M) (hcY : ∀ y ∈ Y, c * y = y * c) :
    (Subgroup.zpowers c ⊔ Y) ⊓ M = Y := by
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hcY y hy) k).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  refine le_antisymm ?_ (le_inf le_sup_right hYM)
  rintro g ⟨hg, hgM⟩
  have hg' : g ∈ ((Subgroup.zpowers c ⊔ Y : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hck : c ^ k ∈ M := by
    have := M.mul_mem hgM (M.inv_mem (hYM hb))
    simpa using this
  have h1 := zpow_eq_one_of_zpow_mem hc3 hcM hck
  show c ^ k * b ∈ Y
  rw [h1, one_mul]
  exact hb

theorem isElemAbelian_zpowers_sup_of_card_nine {c : G} (hc3 : c ^ 3 = 1) {S Y : Subgroup G}
    (hcS : c ∉ S) (hYS : Y ≤ S) (hY9 : Nat.card Y = 9) (hS3 : ∀ s ∈ S, s ^ 3 = 1)
    (hcY : ∀ y ∈ Y, c * y = y * c) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c ⊔ Y) ∧
      Nat.card (Subgroup.zpowers c ⊔ Y : Subgroup G) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hcY y hy) k).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hc1 : c ≠ 1 := fun h => hcS (h ▸ S.one_mem)
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hY9).is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  set T := Subgroup.zpowers c ⊔ Y with hT
  have hTC : T ≤ Subgroup.centralizer (T : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro x hx y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow_self c j i).eq
      · intro x hx y hy
        exact (hcomm y hy x hx)
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro x hx y hy
        exact (hcomm x hx y hy).symm
      · intro x hx y hy
        exact hYcomm y hy x hx
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (hTC a.2) b b.2).symm
  · have hx' : x ∈ ((T : Subgroup G) : Set G) := hx
    rw [hT, hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [(Commute.zpow_left (hcY b hb) k).mul_pow, hS3 b (hYS hb), mul_one, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, show (c ^ ((3 : ℕ) : ℤ)) = 1 by rw [zpow_natCast, hc3],
      one_zpow]
  · have hinf : Subgroup.zpowers c ⊓ Y = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left _ hYS).trans (zpowers_inf_eq_bot hc3 hcS).le)
    rw [hinf, Subgroup.card_bot, mul_one, card_zpowers_of_pow_three hc3 hc1, hY9] at hcard
    exact hcard



omit [Finite G] in
theorem commutatorElement_mul_mul {x y s₁ s₂ : G} (h1 : Commute x s₁) (h2 : Commute x y)
    (h3 : Commute x s₂) (h4 : Commute y s₁) (h5 : Commute y s₂) :
    ⁅x * s₁, y * s₂⁆ = ⁅s₁, s₂⁆ := by
  have hx : Commute x (s₁ * y * s₂ * s₁⁻¹) :=
    ((h1.mul_right h2).mul_right h3).mul_right h1.inv_right
  have hy : Commute y (s₂ * s₁⁻¹ * s₂⁻¹) := (h5.mul_right h4.inv_right).mul_right h5.inv_right
  calc ⁅x * s₁, y * s₂⁆ = x * (s₁ * y * s₂ * s₁⁻¹) * x⁻¹ * (s₂⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]; group
    _ = (s₁ * y * s₂ * s₁⁻¹) * (s₂⁻¹ * y⁻¹) := by rw [hx.eq, mul_inv_cancel_right]
    _ = s₁ * (y * (s₂ * s₁⁻¹ * s₂⁻¹)) * y⁻¹ := by group
    _ = s₁ * ((s₂ * s₁⁻¹ * s₂⁻¹) * y) * y⁻¹ := by rw [hy.eq]
    _ = ⁅s₁, s₂⁆ := by rw [commutatorElement_def]; group

theorem commutator_zpowers_sup_le {c : G} {S : Subgroup G} (hcS : ∀ s ∈ S, c * s = s * c) :
    ⁅Subgroup.zpowers c ⊔ S, Subgroup.zpowers c ⊔ S⁆ ≤ ⁅S, S⁆ := by
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ s ∈ S, x * s = s * x := by
    intro x hx s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hcS s hs) k).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ ((Subgroup.zpowers c ⊔ S : Subgroup G) : Set G) := hg₁
  have hg₂' : g₂ ∈ ((Subgroup.zpowers c ⊔ S : Subgroup G) : Set G) := hg₂
  rw [hset] at hg₁' hg₂'
  obtain ⟨x, hx, s₁, hs₁, rfl⟩ := hg₁'
  obtain ⟨y, hy, s₂, hs₂, rfl⟩ := hg₂'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  show ⁅c ^ i * s₁, c ^ j * s₂⁆ ∈ ⁅S, S⁆
  rw [commutatorElement_mul_mul (Commute.zpow_left (hcS s₁ hs₁) i) (Commute.zpow_zpow_self c i j)
    (Commute.zpow_left (hcS s₂ hs₂) i) (Commute.zpow_left (hcS s₁ hs₁) j)
    (Commute.zpow_left (hcS s₂ hs₂) j)]
  exact Subgroup.commutator_mem_commutator hs₁ hs₂

theorem eq_zpowers_sup_inf_of_elemAbelian {c : G} (hc3 : c ^ 3 = 1) {S : Subgroup G}
    (hcS : c ∉ S) (hcom : ∀ s ∈ S, c * s = s * c) (hS27 : Nat.card S = 27)
    (hSZ : Nat.card (S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) = 3)
    (hS3 : ∀ s ∈ S, s ^ 3 = 1) {X : Subgroup G} (hXP : X ≤ Subgroup.zpowers c ⊔ S)
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hX27 : Nat.card X = 27) :
    X = Subgroup.zpowers c ⊔ (X ⊓ S) ∧ Nat.card (X ⊓ S : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h => hcS (h ▸ S.one_mem)
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ s ∈ S, x * s = s * x := by
    intro x hx s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hcom s hs) k).eq
  obtain ⟨hcardP, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot hc3 hcS, Subgroup.card_bot, mul_one, card_zpowers_of_pow_three hc3 hc1,
    hS27] at hcardP
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hX.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPN : Subgroup.zpowers c ⊔ S ≤ Subgroup.normalizer (S : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun s hs => (hcom s hs).symm)
  set Y := X ⊓ S with hYdef
  have hprod := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf (hXP.trans hPN)
  rw [hX27, hS27] at hprod
  have hsup : Nat.card (X ⊔ S : Subgroup G) ≤ 81 := by
    have := Subgroup.card_le_of_le (sup_le hXP (le_sup_right : S ≤ Subgroup.zpowers c ⊔ S))
    rw [hcardP] at this
    omega
  have hdvd : Nat.card Y ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hS27]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hS_nonab : ¬ S ≤ X := by
    intro hSX
    have hSC : S ≤ S ⊓ Subgroup.centralizer (S : Set G) := le_inf le_rfl fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hXcomm b (hSX hb) a (hSX ha)
    have := Subgroup.card_le_of_le hSC
    rw [hS27, hSZ] at this
    norm_num at this
  have hY9 : Nat.card Y = 9 := by
    have hpos : 0 < Nat.card (X ⊔ S : Subgroup G) := Nat.card_pos
    interval_cases k
    · rw [hk] at hprod; norm_num at hprod; omega
    · rw [hk] at hprod; norm_num at hprod; omega
    · rw [hk]; norm_num
    · exfalso
      apply hS_nonab
      have hYS : Y = S := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hS27]; norm_num)
      exact hYS ▸ inf_le_left
  refine ⟨?_, hY9⟩
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb => hXcomm a ha.1 b hb.1
  have hCY : S ⊓ Subgroup.centralizer (Y : Set G) = Y := by
    have hle : Y ≤ S ⊓ Subgroup.centralizer (Y : Set G) :=
      le_inf inf_le_right fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hYcomm b hb a ha
    have hdvd' : Nat.card (S ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hS27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
    have hge : 9 ≤ Nat.card (S ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) :=
      hY9 ▸ Subgroup.card_le_of_le hle
    interval_cases m
    · rw [hm] at hge; norm_num at hge
    · rw [hm] at hge; norm_num at hge
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, hY9]; norm_num)).symm
    · exfalso
      have hS : S ⊓ Subgroup.centralizer (Y : Set G) = S :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, hS27]; norm_num)
      have hYZ : Y ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
        refine le_inf inf_le_right ?_
        rw [Subgroup.le_centralizer_iff, ← hS]
        exact inf_le_right
      have := Subgroup.card_le_of_le hYZ
      rw [hY9, hSZ] at this
      norm_num at this
  have hXle : X ≤ Subgroup.zpowers c ⊔ Y := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers c ⊔ S : Subgroup G) : Set G) := hXP hx
    rw [hset] at hx'
    obtain ⟨a, ha, s, hs, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hsY : s ∈ Y := by
      rw [← hCY]
      refine ⟨hs, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hxy := hXcomm (c ^ i * s) hx y hy.1
      have hcy : c ^ i * y = y * c ^ i := (Commute.zpow_left (hcom y hy.2) i).eq
      have h1 : c ^ i * (y * s) = c ^ i * (s * y) :=
        calc c ^ i * (y * s) = c ^ i * y * s := (mul_assoc _ _ _).symm
          _ = y * c ^ i * s := by rw [hcy]
          _ = y * (c ^ i * s) := mul_assoc _ _ _
          _ = c ^ i * s * y := hxy.symm
          _ = c ^ i * (s * y) := mul_assoc _ _ _
      exact mul_left_cancel h1
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩) hsY
  have hcardY := (isElemAbelian_zpowers_sup_of_card_nine hc3 hcS inf_le_right hY9 hS3
    (fun y hy => hcom y hy.2)).2
  exact Subgroup.eq_of_le_of_card_ge hXle (by rw [hcardY, hX27])

theorem setOf_elemAbelian_eq_image {c : G} (hc3 : c ^ 3 = 1) {S : Subgroup G}
    (hcS : c ∉ S) (hcom : ∀ s ∈ S, c * s = s * c) (hS27 : Nat.card S = 27)
    (hSZ : Nat.card (S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) = 3)
    (hS3 : ∀ s ∈ S, s ^ 3 = 1) :
    {X : Subgroup G | X ≤ Subgroup.zpowers c ⊔ S ∧ CFSG.Assembly.IsElemAbelian 3 X ∧
        Nat.card X = 27} =
      (fun Y => Subgroup.zpowers c ⊔ Y) '' {Y : Subgroup G | Y ≤ S ∧ Nat.card Y = 9} := by
  ext X
  constructor
  · rintro ⟨hXP, hX, hX27⟩
    obtain ⟨heq, h9⟩ := eq_zpowers_sup_inf_of_elemAbelian hc3 hcS hcom hS27 hSZ hS3 hXP hX hX27
    exact ⟨X ⊓ S, ⟨inf_le_right, h9⟩, heq.symm⟩
  · rintro ⟨Y, ⟨hYS, hY9⟩, rfl⟩
    obtain ⟨hE, h27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc3 hcS hYS hY9 hS3
      (fun y hy => hcom y (hYS hy))
    exact ⟨sup_le_sup_left hYS _, hE, h27⟩

end E27

section Conj

variable {G H : Type*} [Group G] [Group H]

theorem map_conjugate_hom (f : G →* H) (X : Subgroup G) (t : G) :
    (conjugate X t).map f = conjugate (X.map f) (f t) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [map_mul, map_inv]

theorem conjugate_le_of_le {X S : Subgroup G} (hXS : X ≤ S) {t : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) : conjugate X t ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) x).mp (hXS hx)
  simpa [MulAut.conj_apply] using this

end Conj

section Lift

variable {Λ : Type*} [Group Λ] [Finite Λ]

@[expose] noncomputable def liftIn (S : Subgroup Λ)
    (Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)) : Subgroup Λ :=
  Y.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) ⊓ S

omit [Finite Λ] in
theorem liftIn_le (S : Subgroup Λ) (Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)) :
    liftIn S Y ≤ S :=
  inf_le_right

omit [Finite Λ] in
theorem map_liftIn {S : Subgroup Λ} {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)}
    (hY : Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) :
    (liftIn S Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) = Y := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left) fun y hy => ?_
  obtain ⟨s, hs, rfl⟩ := hY hy
  exact ⟨s, ⟨hy, hs⟩, rfl⟩

theorem liftIn_map {S X : Subgroup Λ} (hS : IsPGroup 3 S) (hXS : X ≤ S) :
    liftIn S (X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) = X := by
  refine le_antisymm (fun s hs => ?_) (le_inf (Subgroup.le_comap_map _ _) hXS)
  obtain ⟨⟨x, hx, hxs⟩, hsS⟩ := hs
  have := injOn_mk_of_isPGroup Nat.prime_three hS (hXS hx) hsS hxs
  exact this ▸ hx

theorem card_liftIn {S : Subgroup Λ} (hS : IsPGroup 3 S)
    {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)}
    (hY : Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) :
    Nat.card (liftIn S Y) = Nat.card Y := by
  conv_rhs => rw [← map_liftIn hY]
  exact (card_map_eq_of_injOn _ ((injOn_mk_of_isPGroup Nat.prime_three hS).mono
    (liftIn_le S Y))).symm

theorem liftIn_conjugate {S : Subgroup Λ} (hS : IsPGroup 3 S)
    {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)}
    (hY : Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) {t : Λ}
    (ht : t ∈ Subgroup.normalizer (S : Set Λ)) :
    liftIn S (conjugate Y (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) t)) =
      conjugate (liftIn S Y) t := by
  rw [← map_liftIn hY, ← map_conjugate_hom, liftIn_map hS (conjugate_le_of_le (liftIn_le S Y) ht),
    map_liftIn hY]

theorem setOf_le_card_eq_image_liftIn {S : Subgroup Λ} (hS : IsPGroup 3 S) (n : ℕ) :
    {X : Subgroup Λ | X ≤ S ∧ Nat.card X = n} =
      liftIn S '' {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ) |
        Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) ∧ Nat.card Y = n} := by
  ext X
  constructor
  · rintro ⟨hXS, hX⟩
    refine ⟨X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)), ⟨Subgroup.map_mono hXS, ?_⟩,
      liftIn_map hS hXS⟩
    rw [card_map_eq_of_injOn _ ((injOn_mk_of_isPGroup Nat.prime_three hS).mono hXS), hX]
  · rintro ⟨Y, ⟨hY, hYn⟩, rfl⟩
    exact ⟨liftIn_le S Y, by rw [card_liftIn hS hY, hYn]⟩

theorem normalizer_map_mk_eq {S : Subgroup Λ} (hS : IsPGroup 3 S) :
    Subgroup.normalizer ((S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) :
        Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)) : Set (Λ ⧸ aschbacherSolvableCore 3 Λ)) =
      (Subgroup.normalizer (S : Set Λ)).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 S) := ⟨hS⟩
  exact CFSG.normalizer_map_quotient_eq_map_normalizer 3 S (aschbacherSolvableCore 3 Λ)
    inferInstance ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1)

end Lift

end CFSG.RankThree.PartTwo.Sec13
