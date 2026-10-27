module

public import CFSG.Quasithin.Vol2.KGFact3312Base
public import CFSG.Quasithin.Vol2.KGFact3312A5
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Walter.J1Props.Factor
public import CFSG.Walter.Models
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.KG3312

open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem exists_conj_of_mulEquiv {X Γ : Type} [Group X] [Group Γ] (e : X ≃* Γ)
    (h : ∀ φ : MulAut Γ, ∃ g : Γ, φ = MulAut.conj g) (α : MulAut X) :
    ∃ g : X, α = MulAut.conj g := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e α)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 : e (α x) = g * e x * g⁻¹ := by
    have := congrArg (fun φ : MulAut Γ => φ (e x)) hg
    simpa [MulAut.congr_apply] using this
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem card_centralizer_equiv {X Γ : Type} [Group X] [Group Γ] (e : X ≃* Γ) (x : X) :
    Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (Subgroup.centralizer ({e x} : Set Γ)) := by
  have h : (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Γ) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg e h
      simpa using this
    · intro h
      apply e.injective
      simpa using h
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem comm_of_isSylowTwoOf_of_mulEquiv {X Γ : Type} [Group X] [Finite X] [Group Γ]
    (e : X ≃* Γ) (hΓ : ∀ P : Sylow 2 Γ, IsMulCommutative (P : Subgroup Γ)) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Γ := Finite.of_equiv X e.toEquiv
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp (isSylowTwoOf_map_equiv e hT)
  have hcomm := isMulCommutative_iff.mp (hΓ (hp.toSylow hi))
  intro x hx y hy
  apply e.injective
  have h := hcomm ⟨e x, ⟨x, hx, rfl⟩⟩ ⟨e y, ⟨y, hy, rfl⟩⟩
  have h' : e x * e y = e y * e x := congrArg Subtype.val h
  rw [map_mul, map_mul]
  exact h'

theorem card_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {k m : ℕ} (hX : Nat.card X = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card T = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp
  have hmul := Subgroup.card_mul_index T
  rw [hj, hX] at hmul
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have hidx0 : T.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact (mul_ne_zero (pow_ne_zero k two_ne_zero) hm0) hmul.symm
  have hv : (2 ^ j * T.index).factorization 2 = (2 ^ k * m).factorization 2 := by rw [hmul]
  rw [Nat.factorization_mul (pow_ne_zero j two_ne_zero) hidx0,
    Nat.factorization_mul (pow_ne_zero k two_ne_zero) hm0, Finsupp.add_apply, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hi,
    Nat.factorization_eq_zero_of_not_dvd hm] at hv
  rw [hj, show j = k by omega]

open CFSG.Blueprint in
theorem j1_card_centralizer
    (t : NativeSporadic.J1) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.J1)) = 120 := by
  set u : Equiv.Perm (Fin 3080) :=
    ((CFSG.Sporadic.Schreier.j1PermEquiv t : CFSG.Sporadic.Schreier.j1P) :
      Equiv.Perm (Fin 3080)) with hu
  have huP : u ∈ CFSG.Sporadic.Schreier.j1P := (CFSG.Sporadic.Schreier.j1PermEquiv t).2
  have hou : orderOf u = 2 := by
    rw [hu, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨hC, -⟩ := CFSG.Sporadic.Schreier.j1P_involution_centralizer u huP hou
  rw [Nat.card_congr (CFSG.Sporadic.Schreier.j1CentEquiv t).toEquiv]
  exact hC

open CFSG.Blueprint in
theorem j1_facts
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J1) :
    Nat.card Q = 175560 ∧ Subgroup.center Q = ⊥ ∧
      (∀ α : MulAut Q, ∃ g : Q, α = MulAut.conj g) ∧
      (∀ u : Q, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set Q)) = 120) ∧
      (∀ T : Subgroup Q, IsSylowTwoOf T ⊤ → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) := by
  have hcard : Nat.card Q = 175560 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J1.card_J1]
  have : IsSimpleGroup Q :=
    @MulEquiv.isSimpleGroup Q _ NativeSporadic.J1 _ CFSG.Sporadic.J1.isSimpleGroup_J1 e
  refine ⟨hcard, center_eq_bot_of_isSimpleGroup (by rw [hcard]; norm_num),
    exists_conj_of_mulEquiv e CFSG.Sporadic.Schreier.at_j1_schreier.2.1, fun u hu => ?_,
    fun T hT => ?_⟩
  · rw [card_centralizer_equiv e u]
    exact j1_card_centralizer (e u) (by rw [MulEquiv.orderOf_eq]; exact hu)
  · let e' : Q ≃* ↥CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
    exact @comm_of_isSylowTwoOf_of_mulEquiv Q ↥CFSG.Open.walterJ1 _ _ (Subgroup.toGroup _) e'
      CFSG.Walter.J1Props.hasAbelianSylowTwo T hT

theorem alt5_facts {B : Type} [Group B] (f : B ≃* alternatingGroup (Fin 5)) :
    Nat.card B = 60 ∧ Subgroup.center B = ⊥ := by
  have hcard : Nat.card B = 60 := by rw [Nat.card_congr f.toEquiv, card_alt5']
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup B := MulEquiv.isSimpleGroup f
  exact ⟨hcard, center_eq_bot_of_isSimpleGroup (by rw [hcard]; norm_num)⟩

theorem j1_odd_centralizing
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* CFSG.Blueprint.NativeSporadic.J1) {B : Subgroup Q} (hB : IsAlt 5 ↥B)
    {α : MulAut Q} (hα : Odd (orderOf α)) (hαB : ∀ y ∈ B, α y = y) : α = 1 := by
  obtain ⟨hcard, hZ, hinn, hcent, -⟩ := j1_facts e
  obtain ⟨f⟩ := hB
  obtain ⟨hB60, hZB⟩ := alt5_facts f
  obtain ⟨g, rfl⟩ := hinn α
  have hog : orderOf (MulAut.conj g) = orderOf g := orderOf_injective _ (conj_injective hZ) g
  rw [hog] at hα
  have hgB : ∀ y ∈ B, g * y = y * g := by
    intro y hy
    have h := hαB y hy
    rw [MulAut.conj_apply] at h
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 2 (by rw [hB60]; norm_num)
  have hou : orderOf (u : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hgC : g ∈ Subgroup.centralizer ({(u : Q)} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hgB u u.2)
  have h120 : orderOf g ∣ 120 := by
    have := orderOf_dvd_natCard (⟨g, hgC⟩ : Subgroup.centralizer ({(u : Q)} : Set Q))
    rwa [Subgroup.orderOf_mk, hcent _ hou] at this
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (B : Set Q) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      rw [hgB y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hz := hgB _ hy
      have h2 : g * (g * y * g⁻¹) = g * y := by
        rw [hz]
        group
      rw [← mul_left_cancel h2]
      exact hy
  have hinf : B ⊓ Subgroup.zpowers g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxg⟩ := Subgroup.mem_inf.mp hx
    have hcx : (⟨x, hxB⟩ : ↥B) ∈ Subgroup.center ↥B := by
      refine Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxg
      have hcomm : Commute g (z : Q) := hgB z z.2
      exact ((hcomm.zpow_left k).eq).symm
    rw [hZB] at hcx
    have := congrArg Subtype.val (Subgroup.mem_bot.mp hcx)
    exact Subgroup.mem_bot.mpr this
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, hB60, Nat.card_zpowers] at hprod
  have h2926 : orderOf g ∣ 2926 := by
    have h1 : 60 * orderOf g ∣ 60 * 2926 := by
      rw [← hprod, show 60 * 2926 = Nat.card Q by rw [hcard]]
      exact Subgroup.card_subgroup_dvd_card _
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have h2 : orderOf g ∣ 2 := by
    have := Nat.dvd_gcd h120 h2926
    rwa [show Nat.gcd 120 2926 = 2 by norm_num] at this
  have h1 : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hα
      exact absurd hα (by decide)
  rw [orderOf_eq_one_iff.mp h1, map_one]

theorem j1_inner_on
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* CFSG.Blueprint.NativeSporadic.J1) {A S : Subgroup (MulAut Q)} {B : Subgroup Q}
    (hA : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) (hB : IsAlt 5 ↥B)
    (hSB : S ≤ MulAction.stabilizer (MulAut Q) B) :
    ∀ s ∈ S, ∃ b ∈ B, ∀ y ∈ B, (s : MulAut Q) y = b * y * b⁻¹ := by
  obtain ⟨hcard, hZ, hinn, -, hab⟩ := j1_facts e
  obtain ⟨f⟩ := hB
  obtain ⟨hB60, -⟩ := alt5_facts f
  set T : Subgroup Q := S.comap (MulAut.conj : Q →* MulAut Q) with hTdef
  have hT : IsSylowTwoOf T ⊤ := isSylowTwoOf_comap_conj (conj_injective hZ) hA hS
  have hT8 : Nat.card T = 8 :=
    card_of_isSylowTwoOf hT (k := 3) (m := 21945) (by rw [hcard]; norm_num) (by norm_num)
  have hTN : T ≤ Subgroup.normalizer (B : Set Q) := comap_conj_le_normalizer hSB
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTN
  rw [hB60, hT8] at hprod
  have hc4 : Nat.card ↥(B ⊓ T) = 4 := by
    have hc60 : Nat.card ↥(B ⊓ T) ∣ 60 := hB60 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hc8 : Nat.card ↥(B ⊓ T) ∣ 8 := hT8 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hc : Nat.card ↥(B ⊓ T) ∣ 4 := by
      have := Nat.dvd_gcd hc60 hc8
      rwa [show Nat.gcd 60 8 = 4 by norm_num] at this
    have hm : Nat.card ↥(B ⊔ T) ∣ 175560 := hcard ▸ Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card ↥(B ⊓ T) ≤ 4 := Nat.le_of_dvd (by norm_num) hc
    have hpos : 0 < Nat.card ↥(B ⊓ T) := Nat.card_pos
    interval_cases h : Nat.card ↥(B ⊓ T)
    · have h1 : Nat.card ↥(B ⊔ T) = 480 := by omega
      rw [h1] at hm
      norm_num at hm
    · have h1 : Nat.card ↥(B ⊔ T) = 240 := by omega
      rw [h1] at hm
      norm_num at hm
    · norm_num at hc
    · rfl
  intro s hs
  obtain ⟨t, rfl⟩ := hinn s
  have htT : t ∈ T := hs
  have hmap : B.map (MulAut.conj t).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN htT)
  let φ : MulAut ↥B :=
    (MulEquiv.subgroupMap (MulAut.conj t) B).trans (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ y : ↥B, ((φ y : ↥B) : Q) = t * y * t⁻¹ := fun y => rfl
  set W : Subgroup ↥B := (B ⊓ T).subgroupOf B with hW
  have hW4 : Nat.card W = 4 := by
    rw [hW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hc4]
  have hφW : ∀ w ∈ W, φ w = w := by
    intro w hw
    apply Subtype.ext
    rw [hφ]
    have hwT : (w : Q) ∈ T := (Subgroup.mem_inf.mp hw).2
    rw [hab T hT t htT _ hwT, mul_inv_cancel_right]
  obtain ⟨w, -, hw⟩ := aut_alt5_fix_four f hW4 φ hφW
  refine ⟨w, w.2, fun y hy => ?_⟩
  have h := congrArg Subtype.val (hw ⟨y, hy⟩)
  rw [hφ] at h
  rw [MulAut.conj_apply]
  exact h

theorem factJ1Norm3312_holds :
    FactJ1Norm3312 := by
  intro Q _ _ hQ A S B hA hS hB hSB
  obtain ⟨e⟩ := hQ
  exact ⟨j1_inner_on e hA hS hB hSB, fun α _ hα hαB => j1_odd_centralizing e hB hα hαB⟩

end CFSG.Quasithin.H13.KG3312
