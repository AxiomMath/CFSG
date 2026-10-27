module

public import CFSG.Quasithin.H13.L32AKG1468d
public import CFSG.Quasithin.Background.A312SporE8

public noncomputable section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix

@[expose] def ruEPos : Fin 3 → ℕ := ![0, 1, 3]

@[expose] def ruEBasis (i : Fin 3) : Equiv.Perm (Fin 4060) := ruEElt (ruEPos i)

@[expose] def ruEIdx (i : Fin 3) : ℕ := ruU1Tau.getD (ruEPos i) 0

theorem ruEPos_lt (i : Fin 3) : ruEPos i < 7 := by fin_cases i <;> decide

theorem ruEBasis_eq
    (i : Fin 3) : ruEBasis i = ruU1Elt (ruEIdx i) :=
  ruEElt_eq_ruU1Elt (ruEPos_lt i)

theorem ruEIdx_zero : ruEIdx 0 = 1 := rfl

theorem ruEIdx_one : ruEIdx 1 = 25 := rfl

theorem ruEIdx_two : ruEIdx 2 = 2 := rfl

theorem ruU1Elt_pow {t a : ℕ} (ha : a < 2) : ruU1Elt t ^ a = ruU1Elt (t * a) := by
  interval_cases a <;> simp [ruU1Elt_zero]

theorem e8Elt_ruEBasis
    (c : Fin 3 → ZMod 2) :
    A312S.e8Elt ruEBasis c =
      ruU1Elt ((1 * (c 0).val) ^^^ (25 * (c 1).val) ^^^ (2 * (c 2).val)) := by
  have h0 := ZMod.val_lt (c 0)
  have h1 := ZMod.val_lt (c 1)
  have h2 := ZMod.val_lt (c 2)
  have b0 : 1 * (c 0).val < 32 := by omega
  have b1 : 25 * (c 1).val < 32 := by omega
  have b2 : 2 * (c 2).val < 32 := by omega
  rw [A312S.e8Elt, ruEBasis_eq, ruEBasis_eq, ruEBasis_eq, ruEIdx_zero, ruEIdx_one, ruEIdx_two,
    ruU1Elt_pow h0, ruU1Elt_pow h1, ruU1Elt_pow h2, ruU1Elt_mul b0 b1,
    ruU1Elt_mul (xor_lt_32 b0 b1) b2]

theorem e8_index_eq_zero : ∀ a b c : ZMod 2,
    (1 * a.val) ^^^ (25 * b.val) ^^^ (2 * c.val) = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by decide

theorem ruE8 :
    A312S.E8Basis ruEBasis where
  sq i := ruEElt_sq (ruEPos_lt i)
  comm i j := ruEElt_comm (ruEPos_lt i) (ruEPos_lt j)
  ne_one c hc := by
    rw [e8Elt_ruEBasis] at hc
    have h0 := ZMod.val_lt (c 0)
    have h1 := ZMod.val_lt (c 1)
    have h2 := ZMod.val_lt (c 2)
    have hlt : (1 * (c 0).val) ^^^ (25 * (c 1).val) ^^^ (2 * (c 2).val) < 32 :=
      xor_lt_32 (xor_lt_32 (by omega) (by omega)) (by omega)
    have hz : (1 * (c 0).val) ^^^ (25 * (c 1).val) ^^^ (2 * (c 2).val) = 0 := by
      by_contra hne
      exact ruU1Elt_ne_one hlt (Nat.pos_of_ne_zero hne) hc
    obtain ⟨e0, e1, e2⟩ := e8_index_eq_zero _ _ _ hz
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

theorem ruEBasis_mem
    (i : Fin 3) : ruEBasis i ∈ ruESub :=
  mem_ruESub.2 (Or.inr ⟨ruEPos i, ruEPos_lt i, rfl⟩)

theorem ruE8Sub_eq :
    A312S.e8Sub ruE8 = ruESub := by
  have hle : A312S.e8Sub ruE8 ≤ ruESub := by
    intro x hx
    obtain ⟨c, rfl⟩ := (A312S.mem_e8Sub_iff ruE8 x).mp hx
    exact mul_mem (mul_mem (pow_mem (ruEBasis_mem 0) _) (pow_mem (ruEBasis_mem 1) _))
      (pow_mem (ruEBasis_mem 2) _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hinj : Function.Injective (A312S.e8Hom ruE8) := fun a b hab =>
    Multiplicative.toAdd.injective (A312S.e8Elt_injective ruE8 hab)
  rw [card_ruESub, A312S.e8Sub, ← SetLike.coe_sort_coe, MonoidHom.coe_range,
    Nat.card_range_of_injective hinj]
  simp [Nat.card_eq_fintype_card]

theorem ruESub_le_ruP :
    ruESub ≤ ruP := fun _ hx => ruE_subset hx

abbrev ruEP : Subgroup ↥ruP :=
  ruESub.subgroupOf ruP

theorem mem_e8Norm_of_normalizer
    {x : ↥ruP}
    (hx : x ∈ Subgroup.normalizer (ruEP : Set ↥ruP)) :
    (x : Equiv.Perm (Fin 4060)) ∈ A312S.e8Norm ruE8 := by
  change (x : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer
    ((A312S.e8Sub ruE8 : Subgroup (Equiv.Perm (Fin 4060))) : Set (Equiv.Perm (Fin 4060)))
  rw [ruE8Sub_eq, Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨g, ruESub_le_ruP hg⟩).mp
      (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hg
    have hgP : g ∈ ruP := by
      have h1 := ruESub_le_ruP hg
      have e : g = (x : Equiv.Perm (Fin 4060))⁻¹ * ((x : Equiv.Perm (Fin 4060)) * g *
          (x : Equiv.Perm (Fin 4060))⁻¹) * (x : Equiv.Perm (Fin 4060)) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
    have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨g, hgP⟩).mpr
      (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp h1

@[expose] def ruNE :
    ↥(Subgroup.normalizer (ruEP : Set ↥ruP)) →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (A312S.e8SL ruE8).comp
    { toFun := fun x => ⟨((x : ↥ruP) : Equiv.Perm (Fin 4060)), mem_e8Norm_of_normalizer x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[expose] def ruM0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 0, 1, 1]

@[expose] def ruM1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem ruM0_det : ruM0.det = 1 := by decide +kernel

theorem ruM1_det : ruM1.det = 1 := by decide +kernel

@[expose] def ruSL0 : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨ruM0, ruM0_det⟩

@[expose] def ruSL1 : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨ruM1, ruM1_det⟩

theorem ruM_index (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (k : ℕ)
    (h : ∀ i : Fin 3, (1 * (M 0 i).val) ^^^ (25 * (M 1 i).val) ^^^ (2 * (M 2 i).val) =
      ruU1Tau.getD ((ruEPi.getD k []).getD (ruEPos i) 0) 0)
    (hk : k < 2) (i : Fin 3) :
    [ruNs0, ruNs1].getD k 1 * ruEBasis i * ([ruNs0, ruNs1].getD k 1)⁻¹ =
      A312S.e8Elt ruEBasis fun r => M r i := by
  have hpos : ruEPos i < 7 := ruEPos_lt i
  have hπ : (ruEPi.getD k []).getD (ruEPos i) 0 < 7 := by
    interval_cases k <;> fin_cases i <;> decide
  rw [ruEBasis, ruNs_conj_ruEElt hk hpos, ruEElt_eq_ruU1Elt hπ, e8Elt_ruEBasis, h i]

theorem ruM0_index : ∀ i : Fin 3, (1 * (ruM0 0 i).val) ^^^ (25 * (ruM0 1 i).val) ^^^
    (2 * (ruM0 2 i).val) = ruU1Tau.getD ((ruEPi.getD 0 []).getD (ruEPos i) 0) 0 := by decide

theorem ruM1_index : ∀ i : Fin 3, (1 * (ruM1 0 i).val) ^^^ (25 * (ruM1 1 i).val) ^^^
    (2 * (ruM1 2 i).val) = ruU1Tau.getD ((ruEPi.getD 1 []).getD (ruEPos i) 0) 0 := by decide

theorem ruN_le_normalizer :
    ruN ≤ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) := by
  intro m hm
  have hmap : ∀ g ∈ ruESub, m * g * m⁻¹ ∈ ruESub := by
    intro g hg
    change m * g * m⁻¹ ∈ ruE
    change g ∈ ruE at hg
    rcases hg with hg | ⟨n, hn, rfl⟩
    · rw [Set.mem_singleton_iff.mp hg, mul_one, mul_inv_cancel]
      exact Or.inl rfl
    · exact Or.inr ⟨m * n, mul_mem hm hn, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hmap g, fun hg => ?_⟩
  have hinj : Set.InjOn (fun x => m * x * m⁻¹) (ruESub : Set (Equiv.Perm (Fin 4060))) :=
    fun x _ y _ hxy => by simpa using hxy
  have hsurj := ((Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite _)
    (fun x hx => hmap x hx)).mp hinj).surjOn hg
  obtain ⟨x, hx, hxe⟩ := hsurj
  have : x = g := by simpa using hxe
  rw [← this]
  exact hx

theorem mem_normalizer_subgroupOf {Γ : Type} [Group Γ] {P H : Subgroup Γ} {x : ↥P}
    (hx : (x : Γ) ∈ Subgroup.normalizer (H : Set Γ)) :
    x ∈ Subgroup.normalizer ((H.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_normalizer_iff.mp hx) g

theorem mem_normalizer_ruEP
    {x : ↥ruP} (hx : (x : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060)))) :
    x ∈ Subgroup.normalizer (ruEP : Set ↥ruP) :=
  mem_normalizer_subgroupOf hx

theorem ruNs_mem_normalizer
    {k : ℕ} (hk : k < 2) :
    (⟨[ruNs0, ruNs1].getD k 1, by interval_cases k <;> simp [ruNs0_mem, ruNs1_mem]⟩ : ↥ruP) ∈
      Subgroup.normalizer (ruEP : Set ↥ruP) := by
  have hN : [ruNs0, ruNs1].getD k 1 ∈ ruN := by
    interval_cases k
    · exact ruNs0_memN
    · exact ruNs1_memN
  exact mem_normalizer_ruEP (ruN_le_normalizer hN)

@[expose] def ruNsNE (k : ℕ)
    (hk : k < 2) : ↥(Subgroup.normalizer (ruEP : Set ↥ruP)) :=
  ⟨_, ruNs_mem_normalizer hk⟩

theorem ruNE_ruNs0 :
    ruNE (ruNsNE 0 (by norm_num)) = ruSL0 :=
  A312S.e8SL_eq ruE8 _ ruSL0 (ruM_index ruM0 0 ruM0_index (by norm_num))

theorem ruNE_ruNs1 :
    ruNE (ruNsNE 1 (by norm_num)) = ruSL1 :=
  A312S.e8SL_eq ruE8 _ ruSL1 (ruM_index ruM1 1 ruM1_index (by norm_num))

theorem ruNE_surjective :
    Function.Surjective ruNE := by
  have h0 : ruSL0 ∈ ruNE.range := ⟨_, ruNE_ruNs0⟩
  have h1 : ruSL1 ∈ ruNE.range := ⟨_, ruNE_ruNs1⟩
  have o3 : orderOf ruSL1 = 3 := by
    apply orderOf_eq_prime (hp := ⟨Nat.prime_three⟩)
    · exact Subtype.ext (show ruM1 ^ 3 = 1 by decide +kernel)
    · intro h
      have h' : ruM1 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  have o7 : orderOf (ruSL0 * ruSL1) = 7 := by
    apply orderOf_eq_prime (hp := ⟨by norm_num⟩)
    · exact Subtype.ext (show (ruM0 * ruM1) ^ 7 = 1 by decide +kernel)
    · intro h
      have h' : ruM0 * ruM1 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  have o4 : orderOf (ruSL0 * ruSL1 * ruSL0 * ruSL1 * ruSL1) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ruSL0 * ruSL1 * ruSL0 * ruSL1 * ruSL1)
      (hp := ⟨Nat.prime_two⟩) ?_ ?_
    · rw [h]
      norm_num
    · intro h
      have h' : (ruM0 * ruM1 * ruM0 * ruM1 * ruM1) ^ 2 ^ 1 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
    · exact Subtype.ext (show (ruM0 * ruM1 * ruM0 * ruM1 * ruM1) ^ 2 ^ (1 + 1) = 1 by
        decide +kernel)
  exact MonoidHom.range_eq_top.mp (A312S.eq_top_of_orders_sl32 h1
    (mul_mem (mul_mem (mul_mem (mul_mem h0 h1) h0) h1) h1) (mul_mem h0 h1) o3 o4 o7)

theorem isPGroup_ker_ruNE :
    IsPGroup 2 ruNE.ker := by
  have hK : IsPGroup 2 ruK := IsPGroup.of_card (n := 11) (by rw [card_ruK]; norm_num)
  have hmemK : ∀ x : ↥ruNE.ker, ((x : ↥(Subgroup.normalizer (ruEP : Set ↥ruP))) :
      Equiv.Perm (Fin 4060)) ∈ ruK := by
    intro x
    set g : Equiv.Perm (Fin 4060) :=
      (((x : ↥(Subgroup.normalizer (ruEP : Set ↥ruP))) : ↥ruP) : Equiv.Perm (Fin 4060))
    have hx : ruNE (x : ↥(Subgroup.normalizer (ruEP : Set ↥ruP))) = 1 := x.2
    have hmat : A312S.e8Mat ruE8 ⟨g, mem_e8Norm_of_normalizer (x : ↥(Subgroup.normalizer
        (ruEP : Set ↥ruP))).2⟩ = 1 := congrArg Subtype.val hx
    have hcen : ∀ c, g * A312S.e8Elt ruEBasis c * g⁻¹ = A312S.e8Elt ruEBasis c := by
      intro c
      have h1 := A312S.e8Elt_e8Co ruE8 ⟨g, mem_e8Norm_of_normalizer (x :
        ↥(Subgroup.normalizer (ruEP : Set ↥ruP))).2⟩ c
      rw [← A312S.e8Mat_mulVec, hmat, Matrix.one_mulVec] at h1
      exact h1.symm
    have hgE : g ∈ Subgroup.centralizer (ruESub : Set (Equiv.Perm (Fin 4060))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      rw [← ruE8Sub_eq] at he
      obtain ⟨c, rfl⟩ := (A312S.mem_e8Sub_iff ruE8 e).mp he
      have h1 := hcen c
      calc A312S.e8Elt ruEBasis c * g = (g * A312S.e8Elt ruEBasis c * g⁻¹) * g := by rw [h1]
        _ = g * A312S.e8Elt ruEBasis c := by group
    have hgC : g ∈ ruC := by
      rw [ruC_eq_centralizer]
      refine Subgroup.mem_inf.mpr ⟨((x : ↥(Subgroup.normalizer (ruEP : Set ↥ruP))) : ↥ruP).2,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hgE ruZ ruZ_mem_ruESub
      exact this.symm
    rw [← ruCentralizer_E]
    exact Subgroup.mem_inf.mpr ⟨hgC, hgE⟩
  let ι : ↥ruNE.ker →* ↥ruK :=
    { toFun := fun x => ⟨_, hmemK x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine hK.of_injective ι fun x y hxy => ?_
  have := congrArg (fun w : ↥ruK => (w : Equiv.Perm (Fin 4060))) hxy
  exact Subtype.ext (Subtype.ext (Subtype.ext this))

theorem ruJ_le_oTwoUpper :
    ruJ ≤ oTwoUpper ruC := by
  rw [ruJ, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  have hk6 : k < 6 := by rw [ruJGens_length] at hk; exact hk
  rw [← List.getD_eq_getElem ruJGens 1 hk]
  obtain ⟨hm, hma, hmb, hx1, ha1, hb1⟩ := ruOdd_pow hk6
  have haC : evalSigned [ruC0, ruC1] (ruOddA k) ∈ ruC :=
    evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _
  have hbC : evalSigned [ruC0, ruC1] (ruOddB k) ∈ ruC :=
    evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _
  have hjC : ruJGens.getD k 1 ∈ ruC := ruJ_leC (ruJGens_getD_mem k)
  have hxO := mem_oTwoUpper_of_odd (mul_mem (mul_mem hjC haC) hbC) (odd_orderOf_of_pow hm hx1)
  have haO := mem_oTwoUpper_of_odd haC (odd_orderOf_of_pow hma ha1)
  have hbO := mem_oTwoUpper_of_odd hbC (odd_orderOf_of_pow hmb hb1)
  have e : ruJGens.getD k 1 = (ruJGens.getD k 1 * evalSigned [ruC0, ruC1] (ruOddA k) *
      evalSigned [ruC0, ruC1] (ruOddB k)) * (evalSigned [ruC0, ruC1] (ruOddB k))⁻¹ *
        (evalSigned [ruC0, ruC1] (ruOddA k))⁻¹ := by group
  rw [SetLike.mem_coe, e]
  exact mul_mem (mul_mem hxO (inv_mem hbO)) (inv_mem haO)

theorem ruJ_le_pCoreOf_oTwoUpper :
    ruJ.subgroupOf ruP ≤ pCoreOf 2 (oTwoUpper (ruC.subgroupOf ruP)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (oTwoUpper (ruC.subgroupOf ruP)).map ruP.subtype = oTwoUpper ruC := by
    rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le ruC_le]
  have hJK : ruJ.subgroupOf ruP ≤ oTwoUpper (ruC.subgroupOf ruP) := by
    intro x hx
    have h1 : (x : Equiv.Perm (Fin 4060)) ∈ (oTwoUpper (ruC.subgroupOf ruP)).map ruP.subtype := by
      rw [hmap]
      exact ruJ_le_oTwoUpper (Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← Subtype.ext hyx]
    exact hy
  have hJN : ruC ≤ Subgroup.normalizer (ruJ : Set (Equiv.Perm (Fin 4060))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ruJ_leC).mp ruJ_normal
  have hKN : oTwoUpper (ruC.subgroupOf ruP) ≤
      Subgroup.normalizer ((ruJ.subgroupOf ruP : Subgroup ↥ruP) : Set ↥ruP) := fun c hc =>
    mem_normalizer_subgroupOf (hJN (Subgroup.mem_subgroupOf.mp (oTwoUpper_le _ hc)))
  have hJp : IsPGroup 2 (ruJ.subgroupOf ruP) := IsPGroup.of_card (n := 11) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ruJ_leC.trans ruC_le)).toEquiv, card_ruJ]
    norm_num)
  exact le_pCoreOf_of_le_normalizer 2 hJK hKN hJp

end CFSG.Quasithin.H13.KGRu
