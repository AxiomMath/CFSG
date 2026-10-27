module

public import CFSG.Quasithin.H13.A6S13833e
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6F4
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin.Vol2.KGHat CFSG.Quasithin.H13.A6
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem nu_eq_relIndex (c : G) (X : Subgroup G) :
    A6.nu c X = (centralizer ({c} : Set G)).relIndex X := by
  rw [A6.nu, A6.cfix, inf_relIndex_left]

theorem nu_le_nu_of_le [Finite G] (c : G) {X Y : Subgroup G} (hXY : X ≤ Y) :
    A6.nu c X ≤ A6.nu c Y := by
  rw [nu_eq_relIndex, nu_eq_relIndex]
  refine relIndex_le_of_le_right hXY ?_
  show ((centralizer ({c} : Set G)).subgroupOf Y).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem four_pow_three_le_nu [Finite G] {L O Y : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hO : IsPGroup 2 ↥O) (hOL : O ≤ L) (hLO : L ≤ normalizer (O : Set G)) {c : G}
    (hcL : c ∈ L) (hc3 : c ^ 3 = 1) (hcO : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ O)
    (hY : IsPGroup 2 ↥Y) (hLY : L ≤ normalizer (Y : Set G)) (hcY : ∃ y ∈ Y, c * y ≠ y * c) :
    4 ^ 3 ≤ A6.nu c Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := L ⊔ Y with hNdef
  have hNY : N ≤ normalizer (Y : Set G) := sup_le hLY le_normalizer
  have hcN : c ∈ N := mem_sup_left hcL
  obtain ⟨U, ⟨hUY, hNU, u₀, hu₀U, hu₀c⟩, hUmin⟩ := (Set.toFinite {U : Subgroup G |
    U ≤ Y ∧ N ≤ normalizer (U : Set G) ∧ ∃ u ∈ U, c * u ≠ u * c}).exists_minimal
      ⟨Y, le_rfl, hNY, hcY⟩
  have hcent : ∀ X : Subgroup G, X < U → N ≤ normalizer (X : Set G) →
      ∀ x ∈ X, c * x = x * c := by
    intro X hXU hNX x hx
    by_contra hxc
    exact hXU.not_ge (@hUmin X ⟨hXU.le.trans hUY, hNX, x, hx, hxc⟩ hXU.le)
  have hU2 : IsPGroup 2 ↥U := hY.to_le hUY
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    rw [mem_bot] at hu₀U
    exact hu₀c (by rw [hu₀U, mul_one, one_mul])
  set F := (frattini U).map U.subtype with hF
  obtain ⟨-, hcommU, hpowU, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hU2
  have hFU : F ≤ U := map_subtype_le _
  have hFne : F ≠ U := by
    intro hFU'
    apply hU1
    have htop : frattini U = ⊤ := by
      apply map_injective U.subtype_injective
      have h1 : (⊤ : Subgroup U).map U.subtype = U := by
        rw [← MonoidHom.range_eq_map, range_subtype]
      rw [h1, ← hF, hFU']
    have h := frattini_nongenerating (K := (⊥ : Subgroup U)) (by rw [htop, sup_top_eq])
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hq⟩ : U) ∈ (⊥ : Subgroup U) := by rw [h]; exact mem_top _
    rw [mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  have hFN : N ≤ normalizer (F : Set G) :=
    hNU.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hcommF : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ F := by
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : U), ⟨y, hy⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini U) ⁅_, _⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcommU.is_comm.comm _ _
  have hpowF : ∀ x ∈ U, x ^ 2 ∈ F := by
    intro x hx
    refine ⟨(⟨x, hx⟩ : U) ^ 2, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpowU _
  obtain ⟨W, hFW, hmax⟩ := Finite.exists_le_maximal
    (p := fun X : Subgroup G => F ≤ X ∧ X ≤ U ∧ X ≠ U ∧ N ≤ normalizer (X : Set G))
    ⟨le_rfl, hFU, hFne, hFN⟩
  obtain ⟨-, hWU, hWne, hNW⟩ := hmax.prop
  have hlt : W < U := lt_of_le_of_ne hWU hWne
  have hmaxW : ∀ X : Subgroup G, W ≤ X → X ≤ U → N ≤ normalizer (X : Set G) →
      X = W ∨ X = U := by
    intro X hWX hXU hNX
    by_cases hXU' : X = U
    · exact Or.inr hXU'
    · exact Or.inl (hmax.eq_of_le ⟨hFW.trans hWX, hXU, hXU', hNX⟩ hWX).symm
  have hUN : U ≤ N := hUY.trans le_sup_right
  have hUW : ∀ x ∈ U, ∀ y ∈ W, x * y * x⁻¹ ∈ W := fun x hx y hy =>
    (mem_normalizer_iff.mp (hNW (hUN hx)) y).mp hy
  have hchief : IsChiefFactorUnder 2 N U W :=
    ⟨hlt, hNU, hNW, hUW, fun x hx y hy => hFW (hcommF x hx y hy), fun x hx => hFW (hpowF x hx),
      hmaxW⟩
  have hcW : ∀ w ∈ W, c * w = w * c := hcent W hlt hNW
  set Q := O ⊔ Y with hQdef
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.to_sup_of_normal_right' hO hY (hOL.trans hLY)
  have hQN : Q ≤ N := sup_le (hOL.trans le_sup_left) le_sup_right
  have hNQ : N ≤ normalizer (Q : Set G) := by
    refine sup_le ?_ (le_sup_right.trans le_normalizer)
    refine fun l hl => mem_normalizer_of_conj_mem_fin fun x hx => ?_
    have hle : Q ≤ Q.comap (MulAut.conj l).toMonoidHom := sup_le
      (fun o ho => mem_comap.2 (mem_sup_left ((mem_normalizer_iff.mp (hLO hl) o).mp ho)))
      (fun y hy => mem_comap.2 (mem_sup_right ((mem_normalizer_iff.mp (hLY hl) y).mp hy)))
    exact mem_comap.1 (hle hx)
  have hQU := comm_mem_of_maximal hQ2 (hUY.trans le_sup_right) hlt hQN hNQ hNU hNW hmaxW
  have hWn : (W.subgroupOf U).Normal := hchief.normal
  have hEl : CFSG.IsElementaryAbelian 2 (↥U ⧸ W.subgroupOf U) := hchief.isElementaryAbelian
  set ρ := chiefRep (p := 2) hNU hNW with hρ
  set z := (ρ ⟨c, hcN⟩).val with hz
  have htriv : ∀ n : ↥N, (n : G) ∈ Q → ρ n = 1 := by
    intro n hn
    refine (chiefRep_eq_one_iff (p := 2) hNU hNW n).2 fun w hw => ?_
    have h := W.inv_mem (hQU n hn w hw)
    have e : ((n : G) * w * (n : G)⁻¹ * w⁻¹)⁻¹ = ⁅w, (n : G)⁆ := by
      rw [commutatorElement_def]
      group
    rwa [e] at h
  have hcomm : ∀ n : ↥N, (n : G) ∈ L → ρ n * ρ ⟨c, hcN⟩ = ρ ⟨c, hcN⟩ * ρ n := by
    intro n hn
    have ho : ((n * ⟨c, hcN⟩ * n⁻¹ * (⟨c, hcN⟩ : ↥N)⁻¹ : ↥N) : G) ∈ Q :=
      mem_sup_left (hcO n hn)
    have h1 := htriv _ ho
    calc ρ n * ρ ⟨c, hcN⟩ = ρ (n * ⟨c, hcN⟩) := (map_mul ρ _ _).symm
      _ = ρ ((n * ⟨c, hcN⟩ * n⁻¹ * (⟨c, hcN⟩ : ↥N)⁻¹) * (⟨c, hcN⟩ * n)) := by
          congr 1
          group
      _ = ρ (n * ⟨c, hcN⟩ * n⁻¹ * (⟨c, hcN⟩ : ↥N)⁻¹) * ρ (⟨c, hcN⟩ * n) := map_mul ρ _ _
      _ = ρ ⟨c, hcN⟩ * ρ n := by rw [h1, one_mul, map_mul]
  have hcommN : ∀ n : ↥N, ρ n * ρ ⟨c, hcN⟩ = ρ ⟨c, hcN⟩ * ρ n := by
    set C' : Subgroup ↥N := (Subgroup.centralizer {ρ ⟨c, hcN⟩}).comap ρ with hC'
    have hmem : ∀ n : ↥N, n ∈ C' ↔ ρ n * ρ ⟨c, hcN⟩ = ρ ⟨c, hcN⟩ * ρ n := fun n => by
      rw [hC', mem_comap, mem_centralizer_singleton_iff]
    have hle : N ≤ C'.map N.subtype := by
      refine sup_le (fun l hl => ⟨⟨l, mem_sup_left hl⟩, (hmem _).2 (hcomm _ hl), rfl⟩)
        (fun y hy => ⟨⟨y, mem_sup_right hy⟩, (hmem _).2 ?_, rfl⟩)
      rw [htriv _ (mem_sup_right hy), one_mul, mul_one]
    intro n
    obtain ⟨n', hn', hnn'⟩ := hle n.2
    have : n' = n := Subtype.ext hnn'
    rw [← this]
    exact (hmem n').1 hn'
  set K : Submodule (ZMod 2) (Additive (↥U ⧸ W.subgroupOf U)) :=
    LinearMap.ker (z - LinearMap.id) with hK
  have hKmem : ∀ v, v ∈ K ↔ z v = v := fun v => by
    rw [hK, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hKinv : ∀ n : ↥N, ∀ v ∈ K, (ρ n).val v ∈ K := by
    intro n v hv
    rw [hKmem] at hv ⊢
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (↥U ⧸ W.subgroupOf U)) => g.val v) (hcommN n)
    have h' : (ρ n).val (z v) = z ((ρ n).val v) := h
    rw [hv] at h'
    exact h'.symm
  rcases chiefRep_irreducible hchief K hKinv with hK0 | hK0
  swap
  ·
    exfalso
    have hz1 : ρ ⟨c, hcN⟩ = 1 := by
      refine Units.ext (LinearMap.ext fun v => ?_)
      have hv : v ∈ K := by rw [hK0]; exact Submodule.mem_top
      exact (hKmem v).1 hv
    have hcU := (chiefRep_eq_one_iff (p := 2) hNU hNW ⟨c, hcN⟩).1 hz1
    have h3W : ¬ 3 ∣ Nat.card ↥W := by
      obtain ⟨k, hk⟩ := (hU2.to_le hlt.le).exists_card_eq
      rw [hk]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have h1 := relIndex_cfix_sup_eq_one hc3 hlt.le h3W
      (fun y hy => (mem_normalizer_iff.mp (hNW hcN) y).mp hy)
      (fun x hx => by
        have e : x⁻¹ * (c * x * c⁻¹) = ⁅x⁻¹, c⁆ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact hcU _ (inv_mem hx))
    have hle : U ≤ cfix c U := (relIndex_eq_one.1 h1).trans
      (sup_le le_rfl fun w hw => mem_cfix.2 ⟨hlt.le hw, hcW w hw⟩)
    exact hu₀c (mem_cfix.1 (hle hu₀U)).2
  have hfix0 : ∀ v, z v = v → v = 0 := fun v hv => by
    have h : v ∈ K := (hKmem v).2 hv
    rw [hK0] at h
    exact (Submodule.mem_bot _).1 h
  have hz3 : ∀ w, z (z (z w)) = w := by
    intro w
    have h : ρ ⟨c, hcN⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
      rw [this, map_one]
    rw [pow_three] at h
    exact congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (↥U ⧸ W.subgroupOf U)) => g.val w) h
  have h2 : ∀ x : Additive (↥U ⧸ W.subgroupOf U), x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hzz : ∀ w, z (z w) = z w + w := by
    intro w
    have hv0 : z (z w) + z w + w = 0 := by
      refine hfix0 _ ?_
      rw [map_add, map_add, hz3]
      abel
    calc z (z w) = z (z w) + (z w + z w) + (w + w) := by rw [h2, h2, add_zero, add_zero]
      _ = (z (z w) + z w + w) + (z w + w) := by abel
      _ = z w + w := by rw [hv0, zero_add]
  set α : ↥L →* (Additive (↥U ⧸ W.subgroupOf U) →ₗ[ZMod 2] Additive (↥U ⧸ W.subgroupOf U)) :=
    (Units.coeHom _).comp (ρ.comp (Subgroup.inclusion (le_sup_left : L ≤ N))) with hα
  have hαz : ∀ γ x, α γ (z x) = z (α γ x) := by
    intro γ x
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (↥U ⧸ W.subgroupOf U)) => g.val x)
        (hcomm (Subgroup.inclusion (le_sup_left : L ≤ N) γ) γ.2)
    exact h
  have hd := three_dvd_finrank z hzz (Subgroup.isPerfect_iff.2 hLp) α hαz ⟨c, hcL⟩
    (fun x => rfl)
  have hcard := natCard_F4Space z hzz
  obtain ⟨k, hk⟩ := hd
  rw [hk] at hcard
  have hcard' : W.relIndex U = 4 ^ (3 * k) := hcard
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero, pow_zero] at hcard'
    exact hlt.not_ge (relIndex_eq_one.1 hcard')
  have h64 : 4 ^ 3 ≤ W.relIndex U := by
    rw [hcard']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfp : ∀ x ∈ U, c * x * c⁻¹ * x⁻¹ ∈ W → x ∈ W := by
    intro x hx hxW
    have hv : z (Additive.ofMul ((⟨x, hx⟩ : ↥U) : ↥U ⧸ W.subgroupOf U)) =
        Additive.ofMul ((⟨x, hx⟩ : ↥U) : ↥U ⧸ W.subgroupOf U) := by
      rw [hz, hρ, chiefRep_apply_mk (p := 2) hNU hNW]
      congr 1
      rw [QuotientGroup.eq, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        chiefConj_apply_coe]
      show (c * x * c⁻¹)⁻¹ * x ∈ W
      have h1 : x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ W :=
        (mem_normalizer_iff.mp (hNW (hUN (inv_mem hx))) _).mp (inv_mem hxW)
      have e : (c * x * c⁻¹)⁻¹ * x = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact h1
    have h0 := hfix0 _ hv
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, mem_subgroupOf] at h0
    exact h0
  have hcfixW : cfix c W = W := le_antisymm inf_le_left fun w hw => mem_cfix.2 ⟨hw, hcW w hw⟩
  have hnuW : A6.nu c W = 1 := by rw [A6.nu, hcfixW, relIndex_self]
  have hnuU : A6.nu c U = W.relIndex U := by
    rw [nu_mul c hlt.le (inf_le_left.trans (hUN.trans hNW)), cfix_sup_eq_of_fpf hfp, hnuW,
      mul_one]
  calc 4 ^ 3 ≤ W.relIndex U := h64
    _ = A6.nu c U := hnuU.symm
    _ ≤ A6.nu c Y := nu_le_nu_of_le c hUY

theorem four_pow_three_le_nu_pCoreOf [Finite G] {L Y : Subgroup G} (hLp : ⁅L, L⁆ = L) {c : G}
    (hcL : c ∈ L) (hc3 : c ^ 3 = 1) (hcO : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ pCoreOf 2 L)
    (hY : IsPGroup 2 ↥Y) (hLY : L ≤ normalizer (Y : Set G)) (hcY : ∃ y ∈ Y, c * y ≠ y * c) :
    4 ^ 3 ≤ A6.nu c Y :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  four_pow_three_le_nu hLp (LieType.BorelTits.pCoreOf_isPGroup 2 L)
    (LieType.BorelTits.pCoreOf_le 2 L) (LieType.BorelTits.le_normalizer_pCoreOf 2 L) hcL hc3
    hcO hY hLY hcY

end CFSG.Quasithin.H13.NQS134
