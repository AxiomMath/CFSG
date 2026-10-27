module

public import CFSG.Quasithin.Recognition.RuTypeJ29e
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Aut

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem nonempty_Ls_sz
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Nonempty (Ls s ≃* CFSG.Open.Sz 1) := by
  obtain ⟨hEq, ⟨φ⟩, -⟩ := M.Ls_eq_L0G_and_sz hs hs1
  exact ⟨(MulEquiv.subgroupCongr hEq).trans
    ((Subgroup.equivMapOfInjective _ _ (Ls s).subtype_injective).symm.trans φ)⟩

theorem card_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : Nat.card (Ls s) = 29120 :=
  (M.Ls_eq_L0G_and_sz hs hs1).2.2

omit M in
theorem conj_mem_Ls {s g x : G} (hg : g ∈ Cen s) (hx : x ∈ Ls s) : g * x * g⁻¹ ∈ Ls s := by
  have hn := CFSG.GorensteinWalter.pResidualOf_subgroupOf_normal (Cen s) 2
  have := hn.conj_mem ⟨x, Ls_le_Cen s hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using Subgroup.mem_subgroupOf.mp this

theorem cel_mem_Cen {s : G} (hs : s ∈ M.S0) : (M.cel : G) ∈ Cen s :=
  mem_Cen.mpr (M.mem_S0.mp hs).2

theorem cel_mem_Ls {s : G} (hs : s ∈ M.S0) : (M.cel : G) ∈ Ls s :=
  mem_Ls_of_odd (M.cel_mem_Cen hs) (by simpa using M.odd_orderOf_cel_pow 1)

theorem comm_S0_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {s' : G} (hs' : s' ∈ M.S0) {x : G}
    (hx : x ∈ Ls s) : s' * x = x * s' := by
  obtain ⟨φ⟩ := M.nonempty_Ls_sz hs hs1
  have hs'C : s' ∈ Cen s := M.S3_le_Cen hs hs1 (M.S0_le_S3 hs')
  have hs'2 : s' * s' = 1 := by rw [← pow_two]; exact M.S0_elem.2 _ hs'
  let α : MulAut (Ls s) :=
    { toFun := fun y => ⟨s' * y * s'⁻¹, conj_mem_Ls hs'C y.2⟩
      invFun := fun y => ⟨s'⁻¹ * y * s', by simpa using conj_mem_Ls (inv_mem hs'C) y.2⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y y' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hα2 : α * α = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    show s' * (s' * (y : G) * s'⁻¹) * s'⁻¹ = y
    calc s' * (s' * (y : G) * s'⁻¹) * s'⁻¹ = (s' * s') * y * (s' * s')⁻¹ := by group
      _ = y := by rw [hs'2]; group
  set α' : MulAut (CFSG.Open.Sz 1) := MulAut.congr φ α
  have hα'2 : α' ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hα2, map_one]
  have hcop : Nat.Coprime (2 * 1 + 1) (orderOf α') :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hα'2) (by norm_num)
  obtain ⟨x0, hx0⟩ := CFSG.SignalizerFunctorTheorem.McBride.SzModel.exists_conj_of_coprime_orderOf
    le_rfl α' hcop
  set l := φ.symm x0 with hldef
  have hαl : ∀ y : Ls s, α y = l * y * l⁻¹ := by
    intro y
    apply φ.injective
    have h := congrArg (fun f : MulAut (CFSG.Open.Sz 1) => f (φ y)) hx0
    simp only [α', MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    rw [h, map_mul, map_mul, map_inv, hldef, MulEquiv.apply_symm_apply]
  have hcomm : ∀ y : Ls s, s' * (y : G) = y * s' → (l : G) * y = y * l := by
    intro y hy
    have h := congrArg Subtype.val (hαl y)
    simp only [α, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul, Subgroup.coe_inv] at h
    have h2 : s' * (y : G) * s'⁻¹ = y := by rw [hy, mul_inv_cancel_right]
    rw [h2] at h
    calc (l : G) * y = ((l : G) * y * (l : G)⁻¹) * l := by group
      _ = y * l := by rw [← h]
  have hzLs : M.z ∈ Ls s := M.S1_le_Ls hs hs1 (M.V_le_S1 M.z_mem_V)
  have hlz : (l : G) * M.z = M.z * l :=
    hcomm ⟨M.z, hzLs⟩ ((M.comm_S0_S1 hs' (M.V_le_S1 M.z_mem_V)))
  have hlS1 : (l : G) ∈ M.S1 := M.mem_S1_of_comm_V hs hs1 M.z_mem_V M.z_ne_one l.2 hlz
  have hlc : (l : G) * M.cel = M.cel * l :=
    hcomm ⟨M.cel, M.cel_mem_Ls hs⟩ ((M.mem_S0.mp hs').2).symm
  have hlS0 : (l : G) ∈ M.S0 := M.mem_S0.mpr ⟨M.S1_le_S hlS1, hlc.symm⟩
  have hl1 : (l : G) = 1 := by
    have : (l : G) ∈ M.S0 ⊓ M.S1 := ⟨hlS0, hlS1⟩
    rw [M.S0_inf_S1] at this
    exact this
  have h := congrArg Subtype.val (hαl ⟨x, hx⟩)
  simp only [α, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [hl1, one_mul, inv_one, mul_one] at h
  calc s' * x = (s' * x * s'⁻¹) * s' := by group
    _ = x * s' := by rw [h]

theorem exists_S0_mul_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {k : G} (hk : k ∈ Cen s) :
    ∃ a ∈ M.S0, ∃ l ∈ Ls s, k = a * l := by
  obtain ⟨l, hl, t, ht, rfl⟩ := M.exists_Ls_mul hs hs1 hk
  obtain ⟨a, ha, b, hb, rfl⟩ := M.exists_S0_S1 ht
  refine ⟨a, ha, l * b, mul_mem hl (M.S1_le_Ls hs hs1 hb), ?_⟩
  rw [← mul_assoc, ← mul_assoc, (M.comm_S0_Ls hs hs1 ha hl).symm]

theorem Cen_le
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {s' : G} (hs' : s' ∈ M.S0) :
    Cen s ≤ Cen s' := by
  intro k hk
  obtain ⟨a, ha, l, hl, rfl⟩ := M.exists_S0_mul_Ls hs hs1 hk
  rw [mem_Cen]
  have h1 : a * s' = s' * a := M.S0_elem.1.is_comm.comm ⟨a, ha⟩ ⟨s', hs'⟩ |> congrArg Subtype.val
  have h2 : l * s' = s' * l := (M.comm_S0_Ls hs hs1 hs' hl).symm
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem Cen_eq
    {s s' : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (hs' : s' ∈ M.S0) (hs'1 : s' ≠ 1) :
    Cen s = Cen s' :=
  le_antisymm (M.Cen_le hs hs1 hs') (M.Cen_le hs' hs'1 hs)

theorem bel_pow_conj_S0 (k : ℕ) {x : G} (hx : x ∈ M.S0) :
    (M.bel : G) ^ k * x * ((M.bel : G) ^ k)⁻¹ ∈ M.S0 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h := M.bel_conj_S0 ih
    have e : (M.bel : G) ^ (k + 1) * x * ((M.bel : G) ^ (k + 1))⁻¹ =
        (M.bel : G) * ((M.bel : G) ^ k * x * ((M.bel : G) ^ k)⁻¹) * (M.bel : G)⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact h

theorem exists_bel_conj_S0 {s s' : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (hs' : s' ∈ M.S0)
    (hs'1 : s' ≠ 1) : ∃ k : ℕ, (M.bel : G) ^ k * s * ((M.bel : G) ^ k)⁻¹ = s' := by
  set s1 := (M.bel : G) * s * (M.bel : G)⁻¹ with hs1def
  set s2 := (M.bel : G) ^ 2 * s * ((M.bel : G) ^ 2)⁻¹ with hs2def
  have hs1S : s1 ∈ M.S0 := M.bel_conj_S0 hs
  have hs2S : s2 ∈ M.S0 := M.bel_pow_conj_S0 2 hs
  have hss1 : s ≠ s1 := fun h => hs1 (M.eq_one_of_bel_fix hs h.symm)
  have hs1s2 : s1 ≠ s2 := by
    intro h
    apply hs1
    refine M.eq_one_of_bel_fix hs ?_
    calc (M.bel : G) * s * (M.bel : G)⁻¹ = (M.bel : G)⁻¹ * s1 * (M.bel : G) := by
          rw [h, hs2def]; group
      _ = s := by rw [hs1def]; group
  have hss2 : s ≠ s2 := by
    intro h
    apply hs1
    refine M.eq_one_of_bel_fix hs ?_
    have h3 := M.bel_pow_three
    calc (M.bel : G) * s * (M.bel : G)⁻¹ = (M.bel : G) * s2 * (M.bel : G)⁻¹ := by rw [← h]
      _ = (M.bel : G) ^ 3 * s * ((M.bel : G) ^ 3)⁻¹ := by rw [hs2def]; group
      _ = s := by rw [h3]; group
  have hs11 : s1 ≠ 1 := fun h => hs1 (by
    have : s = (M.bel : G)⁻¹ * s1 * M.bel := by rw [hs1def]; group
    rw [this, h]; group)
  have hs21 : s2 ≠ 1 := fun h => hs1 (by
    have : s = ((M.bel : G) ^ 2)⁻¹ * s2 * (M.bel : G) ^ 2 := by rw [hs2def]; group
    rw [this, h]; group)
  have hss : s * s = 1 := by rw [← pow_two]; exact M.S0_elem.2 _ hs
  have hs1s : s1 * s1 = 1 := by rw [← pow_two]; exact M.S0_elem.2 _ hs1S
  have hcomm : s * s1 = s1 * s := M.S0_elem.1.is_comm.comm ⟨s, hs⟩ ⟨s1, hs1S⟩ |>
    congrArg Subtype.val
  have hF : fourSub s s1 hss hs1s hcomm = M.S0 := by
    have := isKleinFour_fourSub hss hs1s hcomm hs1 hs11 hss1
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [M.card_S0, IsKleinFour.card_four])
    rcases mem_fourSub.mp hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hs
    · exact hs1S
    · exact mul_mem hs hs1S
  have hmem : ∀ x ∈ M.S0, x = 1 ∨ x = s ∨ x = s1 ∨ x = s * s1 := fun x hx =>
    mem_fourSub.mp (hF ▸ hx)
  have hs2eq : s2 = s * s1 := by
    rcases hmem s2 hs2S with h | h | h | h
    · exact absurd h hs21
    · exact absurd h.symm hss2
    · exact absurd h.symm hs1s2
    · exact h
  rcases hmem s' hs' with h | h | h | h
  · exact absurd h hs'1
  · exact ⟨0, by rw [h]; group⟩
  · exact ⟨1, by rw [h, pow_one]⟩
  · exact ⟨2, by rw [h, ← hs2eq]⟩

theorem mem_normalizer_S0
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {g : G}
    (hg : ∀ x ∈ M.S0, g * x * g⁻¹ ∈ M.S0) : ∃ c ∈ Cen s, ∃ k : ℕ, g = c * (M.bel : G) ^ k := by
  have hgs : g * s * g⁻¹ ∈ M.S0 := hg s hs
  have hgs1 : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
    have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
    rw [this, h]; group)
  obtain ⟨k, hk⟩ := M.exists_bel_conj_S0 hgs hgs1 hs hs1
  have hc' : (M.bel : G) ^ k * g ∈ Cen s := by
    rw [mem_Cen]
    calc (M.bel : G) ^ k * g * s = ((M.bel : G) ^ k * (g * s * g⁻¹) * ((M.bel : G) ^ k)⁻¹) *
        ((M.bel : G) ^ k * g) := by group
      _ = s * ((M.bel : G) ^ k * g) := by rw [hk]
  set s'' := ((M.bel : G) ^ k)⁻¹ * s * (M.bel : G) ^ k with hs''
  have hs''S : s'' ∈ M.S0 := by
    have h := M.bel_pow_conj_S0 (2 * k) hs
    have h3 := M.bel_pow_three
    have e : ((M.bel : G) ^ k)⁻¹ = (M.bel : G) ^ (2 * k) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3,
        one_pow]
    rw [hs'', e]
    have e2 : (M.bel : G) ^ k = ((M.bel : G) ^ (2 * k))⁻¹ := by rw [← e, inv_inv]
    rw [e2]
    exact h
  have hs''1 : s'' ≠ 1 := fun h => hs1 (by
    have : s = (M.bel : G) ^ k * s'' * ((M.bel : G) ^ k)⁻¹ := by rw [hs'']; group
    rw [this, h]; group)
  have hCen := M.Cen_eq hs hs1 hs''S hs''1
  have hcC : ((M.bel : G) ^ k)⁻¹ * ((M.bel : G) ^ k * g) * (M.bel : G) ^ k ∈ Cen s := by
    rw [hCen, mem_Cen]
    have h1 := mem_Cen.mp hc'
    calc ((M.bel : G) ^ k)⁻¹ * ((M.bel : G) ^ k * g) * (M.bel : G) ^ k * s'' =
        ((M.bel : G) ^ k)⁻¹ * ((M.bel : G) ^ k * g * s) * (M.bel : G) ^ k := by rw [hs'']; group
      _ = ((M.bel : G) ^ k)⁻¹ * (s * ((M.bel : G) ^ k * g)) * (M.bel : G) ^ k := by rw [h1]
      _ = s'' * (((M.bel : G) ^ k)⁻¹ * ((M.bel : G) ^ k * g) * (M.bel : G) ^ k) := by
        rw [hs'']; group
  refine ⟨_, hcC, 2 * k, ?_⟩
  have h3 := M.bel_pow_three
  have e : ((M.bel : G) ^ k)⁻¹ = (M.bel : G) ^ (2 * k) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3, one_pow]
  rw [← e]
  group

theorem Ls_eq_closure (s : G) :
    Ls s = Subgroup.closure {x | x ∈ Cen s ∧ Odd (orderOf x)} := by
  set N := Subgroup.closure {x | x ∈ Cen s ∧ Odd (orderOf x)} with hN
  refine le_antisymm ?_ ?_
  · have hNC : N ≤ Cen s := by
      rw [hN, Subgroup.closure_le]
      exact fun x hx => hx.1
    have hNn : (N.subgroupOf (Cen s)).Normal := by
      refine ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr ?_⟩
      have hx' := Subgroup.mem_subgroupOf.mp hx
      have hmap : N.map (MulAut.conj (g : G)).toMonoidHom ≤ N := by
        rw [hN, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨y, ⟨hyC, hyo⟩, rfl⟩
        refine Subgroup.subset_closure ⟨?_, ?_⟩
        · exact mul_mem (mul_mem g.2 hyC) (inv_mem g.2)
        · simpa [MulAut.conj_apply, orderOf_conj_eq] using hyo
      have := hmap ⟨x, hx', rfl⟩
      simpa [MulAut.conj_apply] using this
    refine CFSG.GorensteinWalter.pResidualOf_le_of_quotient_isPGroup (Cen s) N 2 Nat.prime_two
      hNC hNn ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h0 : orderOf (y : G) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd h0
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨by simpa using pow_mem y.2 _, ?_⟩
    simp only [SubgroupClass.coe_pow]
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hom]; exact dvd_mul_right _ _), hom,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxC, hxo⟩
    exact mem_Ls_of_odd hxC hxo

theorem bel_conj_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hx : x ∈ Ls s) :
    (M.bel : G) * x * (M.bel : G)⁻¹ ∈ Ls s := by
  set s' := (M.bel : G)⁻¹ * s * M.bel with hs'
  have hs'S : s' ∈ M.S0 := by
    have h := M.bel_pow_conj_S0 2 hs
    have e : (M.bel : G)⁻¹ = (M.bel : G) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', M.bel_pow_three]
    rw [hs', e]
    have e2 : (M.bel : G) = ((M.bel : G) ^ 2)⁻¹ := by rw [← e, inv_inv]
    nth_rewrite 2 [e2]
    exact h
  have hs'1 : s' ≠ 1 := fun h => hs1 (by
    have : s = (M.bel : G) * s' * (M.bel : G)⁻¹ := by rw [hs']; group
    rw [this, h]; group)
  have hCen := M.Cen_eq hs hs1 hs'S hs'1
  rw [Ls_eq_closure] at hx ⊢
  have hmap : (Subgroup.closure {x | x ∈ Cen s ∧ Odd (orderOf x)}).map
      (MulAut.conj (M.bel : G)).toMonoidHom ≤
        Subgroup.closure {x | x ∈ Cen s ∧ Odd (orderOf x)} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨hyC, hyo⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hCen] at hyC
      rw [mem_Cen] at hyC ⊢
      calc (M.bel : G) * y * (M.bel : G)⁻¹ * s =
          (M.bel : G) * (y * s') * (M.bel : G)⁻¹ := by rw [hs']; group
        _ = (M.bel : G) * (s' * y) * (M.bel : G)⁻¹ := by rw [hyC]
        _ = s * ((M.bel : G) * y * (M.bel : G)⁻¹) := by rw [hs']; group
    · simpa [MulAut.conj_apply, orderOf_conj_eq] using hyo
  have := hmap ⟨x, hx, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem bel_outer
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {l : G} (hl : l ∈ Ls s) :
    ∃ x ∈ Ls s, (M.bel : G) * x * (M.bel : G)⁻¹ ≠ l * x * l⁻¹ := by
  by_contra h
  push Not at h
  set c := l⁻¹ * M.bel with hc
  have hcx : ∀ x ∈ Ls s, c * x = x * c := by
    intro x hx
    have h1 := h x hx
    calc c * x = l⁻¹ * ((M.bel : G) * x * (M.bel : G)⁻¹) * M.bel := by rw [hc]; group
      _ = l⁻¹ * (l * x * l⁻¹) * M.bel := by rw [h1]
      _ = x * c := by rw [hc]; group
  have hVLs : ∀ v ∈ ruV M.L, v ∈ Ls s := fun v hv => M.S1_le_Ls hs hs1 (M.V_le_S1 hv)
  have hcL : c ∈ M.L := by
    rw [M.one.eq_normalizer]
    refine mem_normalizer_of_conj_mem fun v hv => ?_
    rw [hcx v (hVLs v hv), mul_inv_cancel_right]
    exact hv
  have hcS : c ∈ ruS M.L :=
    M.toRuData.mem_S_of_centralizes hcL fun v hv => hcx v (hVLs v hv)
  have hcS0 : c ∈ M.S0 := M.mem_S0.mpr ⟨hcS, (hcx _ (M.cel_mem_Ls hs)).symm⟩
  have hbel : (M.bel : G) = l * c := by rw [hc]; group
  have hbC : (M.bel : G) ∈ Cen s := by
    rw [hbel]
    exact mul_mem (Ls_le_Cen s hl) (M.S3_le_Cen hs hs1 (M.S0_le_S3 hcS0))
  apply hs1
  refine M.eq_one_of_bel_fix hs ?_
  rw [mem_Cen.mp hbC, mul_inv_cancel_right]

theorem isConj_z_iff
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hx : x ∈ Cen s) :
    IsConj M.z x ↔ x ∈ Ls s ∧ x ^ 2 = 1 ∧ x ≠ 1 := by
  have hzLs : M.z ∈ Ls s := M.S1_le_Ls hs hs1 (M.V_le_S1 M.z_mem_V)
  constructor
  · intro hzx
    obtain ⟨l, hl, rfl⟩ := M.exists_Ls_conj_z hs hs1 hzx (mem_Cen.mp hx)
    refine ⟨mul_mem (mul_mem hl hzLs) (inv_mem hl), by rw [conj_pow, M.z_sq]; group, ?_⟩
    intro h
    apply M.z_ne_one
    have : M.z = l⁻¹ * (l * M.z * l⁻¹) * l := by group
    rw [this, h]; group
  · rintro ⟨hxLs, hx2, hx1⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, P, hP⟩ := M.lemma_J27_10 hs hs1
    have hp : IsPGroup 2 (Subgroup.zpowers (⟨x, hx⟩ : Cen s)) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      have h := orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : Cen s) ^ 2 = 1 from Subtype.ext hx2)
      rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    obtain ⟨PS, hPS⟩ := hp.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (Cen s) PS P
    have hmem : k * ⟨x, hx⟩ * k⁻¹ ∈ (P : Subgroup (Cen s)) := by
      rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hPS (Subgroup.mem_zpowers _), by simp [MulAut.conj_apply]⟩
    rw [hP] at hmem
    have hS3 : (k : G) * x * (k : G)⁻¹ ∈ M.S3 := by
      rw [← M.centralizer_H_eq_S3 hs hs1]
      simpa using Subgroup.mem_subgroupOf.mp hmem
    have hkLs : (k : G) * x * (k : G)⁻¹ ∈ Ls s := conj_mem_Ls k.2 hxLs
    have hV : (k : G) * x * (k : G)⁻¹ ∈ ruV M.L :=
      M.mem_V_of_S1_sq (M.mem_S1_of_mem_Ls hs hs1 hS3 hkLs) (by rw [conj_pow, hx2]; group)
    have hne : (k : G) * x * (k : G)⁻¹ ≠ 1 := fun h => hx1 (by
      have : x = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * k := by group
      rw [this, h]; group)
    exact (M.isConj_z_of_V hV hne).trans (isConj_iff.mpr ⟨(k : G)⁻¹, by group⟩)

theorem lemma_J29
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    (Nonempty (Ls s ≃* CFSG.Open.Sz 1) ∧ M.S0 ⊓ Ls s = ⊥ ∧ M.S0 ⊔ Ls s = Cen s ∧
      ∀ x ∈ M.S0, ∀ y ∈ Ls s, x * y = y * x) ∧
    ((∀ g : G, (∀ x ∈ M.S0, g * x * g⁻¹ ∈ M.S0) → ∃ c ∈ Cen s, ∃ b ∈ M.B, g = c * b) ∧
      (∀ b ∈ M.B, ∀ y ∈ Ls s, b * y * b⁻¹ ∈ Ls s) ∧
      ∀ l ∈ Ls s, ∃ x ∈ Ls s, (M.bel : G) * x * (M.bel : G)⁻¹ ≠ l * x * l⁻¹) ∧
    ∀ x ∈ Cen s, (IsConj M.z x ↔ x ∈ Ls s ∧ x ^ 2 = 1 ∧ x ≠ 1) := by
  refine ⟨⟨M.nonempty_Ls_sz hs hs1, ?_, ?_, fun x hx y hy => M.comm_S0_Ls hs hs1 hx hy⟩,
    ⟨fun g hg => ?_, fun b hb y hy => ?_, fun l hl => M.bel_outer hs hs1 hl⟩,
    fun x hx => M.isConj_z_iff hs hs1 hx⟩
  · rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (M.S0_inf_Ls hs hs1 hx.1 hx.2)
  · refine le_antisymm (sup_le (M.S0_le_S3.trans (M.S3_le_Cen hs hs1)) (Ls_le_Cen s))
      fun k hk => ?_
    obtain ⟨a, ha, l, hl, rfl⟩ := M.exists_S0_mul_Ls hs hs1 hk
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hl)
  · obtain ⟨c, hc, k, rfl⟩ := M.mem_normalizer_S0 hs hs1 hg
    exact ⟨c, hc, _, Subgroup.npow_mem_zpowers _ k, rfl⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h3 := M.bel_pow_three
    have hnat : ∀ n : ℕ, ∀ y ∈ Ls s, (M.bel : G) ^ n * y * ((M.bel : G) ^ n)⁻¹ ∈ Ls s := by
      intro n
      induction n with
      | zero => intro y hy; simpa using hy
      | succ n ih =>
        intro y hy
        have := M.bel_conj_Ls hs hs1 (ih y hy)
        have e : (M.bel : G) ^ (n + 1) * y * ((M.bel : G) ^ (n + 1))⁻¹ =
            (M.bel : G) * ((M.bel : G) ^ n * y * ((M.bel : G) ^ n)⁻¹) * (M.bel : G)⁻¹ := by
          rw [pow_succ']; group
        rw [e]
        exact this
    have e : (M.bel : G) ^ k = (M.bel : G) ^ (k % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact zpow_eq_zpow_emod' k h3
    rw [e]
    exact hnat _ y hy

end RuDataM

end CFSG.Quasithin.RuType
