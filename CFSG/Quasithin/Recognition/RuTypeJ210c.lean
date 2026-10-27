module

public import CFSG.Quasithin.Recognition.RuTypeJ210b
public import CFSG.Quasithin.Background.A1bHyperplane

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem S0_le_centralizer
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {Y : Subgroup G}
    (hYL : Y ≤ Ls s) : M.S0 ≤ Subgroup.centralizer (Y : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (M.comm_S0_Ls hs hs1 ha (hYL hy)).symm

theorem eq_one_of_two_elt {p : ℕ} (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hY : Nat.card Y = p)
    {a y : G} (ha : a ∈ M.S0) (hy : y ∈ Y) (hay : a * y = y * a) {k : ℕ}
    (hk : (a * y) ^ 2 ^ k = 1) : y = 1 := by
  have h2 : (a * y) ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  rw [Commute.mul_pow hay] at h2
  have ha2 : a ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, M.S0_elem.2 a ha, one_pow]
  rw [ha2, one_mul] at h2
  have h1 : orderOf y ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one h2
  have h3 : orderOf y ∣ p := hY ▸ Subgroup.orderOf_dvd_natCard Y hy
  have hcop : Nat.Coprime (2 ^ (k + 1)) p :=
    Nat.Coprime.pow_left _ (by rcases hp with rfl | rfl <;> norm_num)
  have h4 : orderOf y ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

theorem eq_one_of_odd_elt {p : ℕ} (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hY : Nat.card Y = p)
    {a y : G} (ha : a ∈ M.S0) (hy : y ∈ Y) (hay : a * y = y * a) {n : ℕ} (hn : Odd n)
    (h : (a * y) ^ n = 1) : a = 1 := by
  rw [Commute.mul_pow hay] at h
  obtain ⟨m, rfl⟩ := hn
  have ha2 : a ^ 2 = 1 := M.S0_elem.2 a ha
  rw [pow_succ, pow_mul, ha2, one_pow, one_mul] at h
  have haY : a ∈ Y := by
    have : a = (y ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_mem (pow_mem hy _)
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
  have h3 : orderOf a ∣ p := hY ▸ Subgroup.orderOf_dvd_natCard Y haY
  have hcop : Nat.Coprime 2 p := by rcases hp with rfl | rfl <;> norm_num
  have h4 : orderOf a ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

theorem exists_sylow_S0
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    ∃ P : Sylow 2 (Subgroup.centralizer (Y : Set G)),
      (P : Subgroup (Subgroup.centralizer (Y : Set G))) =
        M.S0.subgroupOf (Subgroup.centralizer (Y : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.centralizer (Y : Set G) with hXdef
  have hS0X : M.S0 ≤ X := M.S0_le_centralizer hs hs1 hYL
  have hpg : IsPGroup 2 (M.S0.subgroupOf X) := by
    rw [IsPGroup.iff_card, card_subgroupOf_of_le hS0X, M.card_S0]
    exact ⟨2, by norm_num⟩
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  by_contra hne
  set S := (M.S0.subgroupOf X).subgroupOf (P : Subgroup X) with hSdef
  have hlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne fun x hx => ?_
    have : (⟨x, hx⟩ : (P : Subgroup X)) ∈ S := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
  obtain ⟨q, hqN, hqS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent S hlt)
  have hqS0 : ∀ a ∈ M.S0, ((q : X) : G) * a * ((q : X) : G)⁻¹ ∈ M.S0 := by
    intro a ha
    have haP : (⟨a, hS0X ha⟩ : X) ∈ (P : Subgroup X) := hP (Subgroup.mem_subgroupOf.mpr ha)
    have haS : (⟨⟨a, hS0X ha⟩, haP⟩ : (P : Subgroup X)) ∈ S := by
      rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ha
    have h := (Subgroup.mem_normalizer_iff.mp hqN _).mp haS
    rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hqY : ∀ y ∈ Y, ((q : X) : G) * y = y * ((q : X) : G) := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (q : X).2 y hy).symm
  have hqC := M.mem_Cen_of_centralizes hs hs1 hp hYL hY hqY hqS0
  obtain ⟨a, ha, y, hy, hqa⟩ := M.exists_S0_mul_Y hs hs1 hp hYL hY hqC hqY
  obtain ⟨k, hk⟩ := P.isPGroup' q
  have hk' : ((q : X) : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : (P : Subgroup X) => ((x : X) : G)) hk
    simpa using this
  rw [hqa] at hk'
  have hy1 := M.eq_one_of_two_elt hp hY ha hy (M.comm_S0_Ls hs hs1 ha (hYL hy)) hk'
  apply hqS
  rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hqa, hy1, mul_one]
  exact ha

theorem normalizer_le_centralizer_S0
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p)
    (P : Sylow 2 (Subgroup.centralizer (Y : Set G)))
    (hPc : (P : Subgroup (Subgroup.centralizer (Y : Set G))) =
      M.S0.subgroupOf (Subgroup.centralizer (Y : Set G))) :
    Subgroup.normalizer (P : Set (Subgroup.centralizer (Y : Set G))) ≤
      Subgroup.centralizer (P : Set (Subgroup.centralizer (Y : Set G))) := by
  have hS0X : M.S0 ≤ Subgroup.centralizer (Y : Set G) := M.S0_le_centralizer hs hs1 hYL
  intro x hx
  have hxS0 : ∀ a ∈ M.S0, (x : G) * a * (x : G)⁻¹ ∈ M.S0 := by
    intro a ha
    have haP : (⟨a, hS0X ha⟩ : Subgroup.centralizer (Y : Set G)) ∈
        (P : Subgroup (Subgroup.centralizer (Y : Set G))) := by
      rw [hPc]
      exact Subgroup.mem_subgroupOf.mpr ha
    have h := (Subgroup.mem_normalizer_iff.mp hx _).mp haP
    rw [hPc, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hxY : ∀ y ∈ Y, (x : G) * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp x.2 y hy).symm
  have hxC := M.mem_Cen_of_centralizes hs hs1 hp hYL hY hxY hxS0
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : (h : G) ∈ M.S0 := by
    have : h ∈ (P : Subgroup (Subgroup.centralizer (Y : Set G))) := hh
    rw [hPc, Subgroup.mem_subgroupOf] at this
    exact this
  have := mem_Cen.mp (M.Cen_le hs hs1 hh' hxC)
  exact Subtype.ext this.symm

theorem not_isCyclic_S0 {A : Type*} [Group A] (e : A ≃* M.S0) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  rw [Nat.card_congr e.toEquiv, M.card_S0] at hg
  have h2 : g ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (M.S0_elem.2 _ (e g).2)
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at this
  norm_num at this

theorem exists_S0_mul_of_centralizes
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) {x : G}
    (hxY : ∀ y ∈ Y, x * y = y * x) : ∃ a ∈ M.S0, ∃ y ∈ Y, x = a * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.centralizer (Y : Set G) with hXdef
  obtain ⟨P, hPc⟩ := M.exists_sylow_S0 hs hs1 hp hYL hY
  have hNC := M.normalizer_le_centralizer_S0 hs hs1 hp hYL hY P hPc
  set O := (MonoidHom.transferSylow P hNC).ker with hOdef
  have hc : Subgroup.IsComplement' O P := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hOodd : ¬ 2 ∣ Nat.card O := MonoidHom.not_dvd_card_ker_transferSylow P hNC
  have hPS0 : ∀ b : X, b ∈ (P : Subgroup X) ↔ (b : G) ∈ M.S0 := fun b => by
    rw [hPc, Subgroup.mem_subgroupOf]
  have : IsMulCommutative (P : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hNC (Subgroup.le_normalizer b.2) a a.2)⟩⟩
  let _ : MulDistribMulAction (P : Subgroup X) O :=
    MulDistribMulAction.compHom O ((MulAut.conjNormal (H := O)).comp (P : Subgroup X).subtype)
  have hsmul : ∀ (b : (P : Subgroup X)) (o : O),
      (((b • o : O) : X) : G) = ((b : X) : G) * ((o : X) : G) * ((b : X) : G)⁻¹ :=
    fun b o => by
      show (((MulAut.conjNormal (b : X) o : O) : X) : G) = _
      rw [MulAut.conjNormal_apply]
      simp
  have hfix : ∀ B : Subgroup (P : Subgroup X), IsCyclic ((P : Subgroup X) ⧸ B) →
      fixedPointSubgroup B O ≤ (Y.subgroupOf X).subgroupOf O := by
    intro B hB o ho
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      have hB0 : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr fun b hb =>
        by_contra fun h => hcon ⟨b, hb, h⟩
      rw [hB0] at hB
      exact M.not_isCyclic_S0
        ((QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hPc)).trans
          (Subgroup.subgroupOfEquivOfLe (M.S0_le_centralizer hs hs1 hYL)))
        hB
    set s' : G := ((b : X) : G) with hs'
    have hs'S : s' ∈ M.S0 := (hPS0 b).mp b.2
    have hs'1 : s' ≠ 1 := fun h => hb1 (Subtype.ext (Subtype.ext h))
    have hbo : (⟨b, hbB⟩ : B) • o = o := ho ⟨b, hbB⟩
    have hbo' : s' * ((o : X) : G) * s'⁻¹ = ((o : X) : G) := by
      rw [hs', ← hsmul]
      exact congrArg (fun o : O => ((o : X) : G)) hbo
    have hoC : ((o : X) : G) ∈ Cen s := by
      rw [M.Cen_eq hs hs1 hs'S hs'1, mem_Cen]
      calc ((o : X) : G) * s' = (s' * ((o : X) : G) * s'⁻¹) * s' := by rw [hbo']
        _ = s' * ((o : X) : G) := by group
    have hoY : ∀ y ∈ Y, ((o : X) : G) * y = y * ((o : X) : G) := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (o : X).2 y hy).symm
    obtain ⟨a, ha, y, hy, hoa⟩ := M.exists_S0_mul_Y hs hs1 hp hYL hY hoC hoY
    have hodd : Odd (Nat.card O) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hOodd)
    have hpow : ((o : X) : G) ^ Nat.card O = 1 := by
      have := congrArg (fun o : O => ((o : X) : G)) (pow_card_eq_one' (G := O) (x := o))
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      exact this
    rw [hoa] at hpow
    have ha1 := M.eq_one_of_odd_elt hp hY ha hy (M.comm_S0_Ls hs hs1 ha (hYL hy)) hodd hpow
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hoa, ha1, one_mul]
    exact hy
  have hgen := a117_generation (A := (P : Subgroup X)) P.isPGroup' (G := O) hOodd
  have htop : (⊤ : Subgroup O) ≤ (Y.subgroupOf X).subgroupOf O :=
    hgen.symm.le.trans (iSup₂_le fun B hB => hfix B hB.1)
  have hOY : ∀ o : O, ((o : X) : G) ∈ Y := fun o => by
    have := htop (Subgroup.mem_top o)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  have hxX : x ∈ X := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hxY y hy).symm
  obtain ⟨⟨⟨o, ho⟩, ⟨b, hb⟩⟩, hob⟩ := (hc.existsUnique ⟨x, hxX⟩).exists
  have hoY' : (o : G) ∈ Y := hOY ⟨o, ho⟩
  have hbS : (b : G) ∈ M.S0 := (hPS0 b).mp hb
  refine ⟨b, hbS, o, hoY', ?_⟩
  have h := congrArg Subtype.val hob
  simp only [Subgroup.coe_mul] at h
  rw [← h]
  exact (M.comm_S0_Ls hs hs1 hbS (hYL hoY')).symm

end RuDataM

end CFSG.Quasithin.RuType
