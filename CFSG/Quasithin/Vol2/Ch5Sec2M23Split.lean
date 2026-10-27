module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Fus
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Mod
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.A7Fano CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)

theorem mem_normalizer_zpowers_iff_of_order_three {X : Type*} [Group X] {σ g : X}
    (hσ : orderOf σ = 3) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set X) ↔
      g * σ * g⁻¹ = σ ∨ g * σ * g⁻¹ = σ⁻¹ := by
  constructor
  · intro hg
    have h1 : g * σ * g⁻¹ ∈ Subgroup.zpowers σ :=
      (Subgroup.mem_normalizer_iff.mp hg σ).mp (Subgroup.mem_zpowers σ)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← zpow_mod_orderOf, hσ] at hj
    have hj3 : j % ((3 : ℕ) : ℤ) = 0 ∨ j % ((3 : ℕ) : ℤ) = 1 ∨ j % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hj3 with h | h | h
    · exfalso
      rw [h, zpow_zero] at hj
      rw [conj_eq_one_iff.mp hj.symm, orderOf_one] at hσ
      norm_num at hσ
    · left
      rw [h, zpow_one] at hj
      exact hj.symm
    · right
      rw [h] at hj
      have h3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
      have e : σ ^ ((2 : ℕ) : ℤ) = σ⁻¹ := by
        rw [zpow_natCast, eq_inv_iff_mul_eq_one, ← pow_succ, h3]
      rw [← e]
      exact hj.symm
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    rcases h with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]

theorem card_normalizer_zpowers_three_cycle {σ : A7}
    (hσ : (σ : Perm (Fin 7)).cycleType = {3}) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers σ : Set A7)) = 72 := by
  have hσ3 : orderOf σ = 3 := by
    rw [← Subgroup.orderOf_coe, ← Equiv.Perm.lcm_cycleType, hσ]
    decide
  have e : Nat.card (Subgroup.normalizer (Subgroup.zpowers σ : Set A7)) =
      Nat.card {g : Perm (Fin 7) // Perm.sign g = 1 ∧
        (g * σ * g⁻¹ = σ ∨ g * σ * g⁻¹ = (σ : Perm (Fin 7))⁻¹)} := by
    refine Nat.card_congr
      { toFun := fun g => ⟨((g : A7) : Perm (Fin 7)),
          Equiv.Perm.mem_alternatingGroup.mp (g : A7).2, ?_⟩
        invFun := fun g => ⟨⟨g.1, Equiv.Perm.mem_alternatingGroup.mpr g.2.1⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · rcases (mem_normalizer_zpowers_iff_of_order_three hσ3).mp g.2 with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rw [mem_normalizer_zpowers_iff_of_order_three hσ3]
      rcases g.2.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact normCount_eq hσ

theorem eq_one_of_mem_normalizer_of_fpf {X : Type*} [Group X] {Y : Subgroup X} [hYn : Y.Normal]
    (hY2 : IsPGroup 2 Y) {k u : X} (hk3 : orderOf k = 3)
    (hfpf : ∀ v ∈ Y, k * v * k⁻¹ = v → v = 1) (hu : u ∈ Y)
    (hun : u ∈ Subgroup.normalizer (Subgroup.zpowers k : Set X)) : u = 1 := by
  have hcY : u * k * u⁻¹ * k⁻¹ ∈ Y := by
    have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [e]
    exact Y.mul_mem hu (hYn.conj_mem _ (Y.inv_mem hu) k)
  have hcK : u * k * u⁻¹ * k⁻¹ ∈ Subgroup.zpowers k :=
    (Subgroup.zpowers k).mul_mem ((Subgroup.mem_normalizer_iff.mp hun k).mp
      (Subgroup.mem_zpowers k)) ((Subgroup.zpowers k).inv_mem (Subgroup.mem_zpowers k))
  have h3 : orderOf (u * k * u⁻¹ * k⁻¹) ∣ 3 := by
    rw [← hk3]
    exact orderOf_dvd_of_mem_zpowers hcK
  obtain ⟨n, hn⟩ := hY2 ⟨_, hcY⟩
  have h2 : orderOf (u * k * u⁻¹ * k⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hn
    simpa using this)
  have h1 : orderOf (u * k * u⁻¹ * k⁻¹) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3
      (Nat.Coprime.pow_right n (by norm_num))) h2
  rw [orderOf_eq_one_iff] at h1
  have e : u * k = k * u := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  exact hfpf u hu (mul_inv_eq_iff_eq_mul.mpr e.symm)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_map_eq {M2 U : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hker : π.ker = U.subgroupOf M2) (hU2 : IsPGroup 2 U) (hUM2 : U ≤ M2) {k : ↥M2}
    (hk3 : orderOf k = 3) (m : ↥M2)
    (hm : π m * π k * (π m)⁻¹ = π k ∨ π m * π k * (π m)⁻¹ = (π k)⁻¹) :
    ∃ n ∈ Subgroup.normalizer (Subgroup.zpowers k : Set ↥M2), π n = π m := by
  have hk3' : orderOf (k : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hk3
  set y : ↥M2 := m * k * m⁻¹ with hy
  have hy3 : orderOf (y : G) = 3 := by
    rw [Subgroup.orderOf_coe, hy, ← MulAut.conj_apply]
    rw [← hk3]
    exact orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective k
  obtain ⟨ε, hε3, hεπ, hεk⟩ :
      ∃ ε : ↥M2, orderOf (ε : G) = 3 ∧ π ε = π y ∧ (ε = k ∨ ε = k⁻¹) := by
    rcases hm with h | h
    · exact ⟨k, hk3', by rw [hy, map_mul, map_mul, map_inv, h], Or.inl rfl⟩
    · refine ⟨k⁻¹, by rw [Subgroup.coe_inv, orderOf_inv]; exact hk3', ?_, Or.inr rfl⟩
      rw [hy, map_mul, map_mul, map_inv, map_inv, h]
  obtain ⟨g, hg, hgε⟩ := exists_conj_mem_sup_of_map_eq_three hker hU2 hUM2 ε.2 y.2 hε3 hy3 hεπ
  have hgM : g ∈ M2 := sup_le hUM2 (Subgroup.zpowers_le.mpr ε.2) hg
  have hgπ : π ⟨g, hgM⟩ ∈ Subgroup.zpowers (π k) := by
    have hle : U ⊔ Subgroup.zpowers (ε : G) ≤
        ((Subgroup.zpowers (π k)).comap π).map M2.subtype := by
      refine sup_le (fun u hu => ⟨⟨u, hUM2 hu⟩, ?_, rfl⟩) (Subgroup.zpowers_le.mpr ⟨ε, ?_, rfl⟩)
      · have : (⟨u, hUM2 hu⟩ : ↥M2) ∈ π.ker := by
          rw [hker]
          exact hu
        rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_ker.mp this]
        exact (Subgroup.zpowers (π k)).one_mem
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        rcases hεk with rfl | rfl
        · exact Subgroup.mem_zpowers _
        · rw [map_inv]
          exact (Subgroup.zpowers (π k)).inv_mem (Subgroup.mem_zpowers _)
    obtain ⟨g', hg', hgg'⟩ := hle hg
    have : g' = ⟨g, hgM⟩ := Subtype.ext hgg'
    rw [← this]
    exact hg'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgπ
  set gₘ : ↥M2 := ⟨g, hgM⟩ with hgₘ
  have hgε' : gₘ * ε * gₘ⁻¹ = y := Subtype.ext hgε
  have hconj : (gₘ⁻¹ * m) * k * (gₘ⁻¹ * m)⁻¹ = ε := by
    calc (gₘ⁻¹ * m) * k * (gₘ⁻¹ * m)⁻¹ = gₘ⁻¹ * (m * k * m⁻¹) * gₘ := by group
      _ = gₘ⁻¹ * (gₘ * ε * gₘ⁻¹) * gₘ := by rw [← hy, hgε']
      _ = ε := by group
  have hgm : gₘ⁻¹ * m ∈ Subgroup.normalizer (Subgroup.zpowers k : Set ↥M2) := by
    rw [mem_normalizer_zpowers_iff_of_order_three hk3, hconj]
    exact hεk
  refine ⟨k ^ j * (gₘ⁻¹ * m), Subgroup.mul_mem _
    (Subgroup.le_normalizer (Subgroup.zpow_mem_zpowers k j)) hgm, ?_⟩
  rw [map_mul, map_mul, map_zpow, map_inv, hj, mul_inv_cancel_left]

theorem card_normalizer_fpf_three {M2 U : Subgroup G}
    {π' : ↥M2 →* A7} (hsurj : Function.Surjective π') (hker : π'.ker = U.subgroupOf M2)
    (hU2 : IsPGroup 2 U) (hUM2 : U ≤ M2) {k : ↥M2} (hk3 : orderOf k = 3)
    (hct : ((π' k : A7) : Perm (Fin 7)).cycleType = {3})
    (hfpf : ∀ u ∈ U, (k : G) * u * (k : G)⁻¹ = u → u = 1) :
    U.subgroupOf M2 ⊓ Subgroup.normalizer (Subgroup.zpowers k : Set ↥M2) = ⊥ ∧
      Nat.card (Subgroup.normalizer (Subgroup.zpowers k : Set ↥M2)) = 72 := by
  set N := Subgroup.normalizer (Subgroup.zpowers k : Set ↥M2) with hN
  have hYn : (U.subgroupOf M2).Normal := hker ▸ π'.normal_ker
  have hY2 : IsPGroup 2 ↥(U.subgroupOf M2) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM2).symm
  have hdisj : U.subgroupOf M2 ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huU, huN⟩
    rw [Subgroup.mem_bot]
    refine eq_one_of_mem_normalizer_of_fpf hY2 hk3 (fun v hv hkv => ?_) huU huN
    exact Subtype.ext (hfpf v (Subgroup.mem_subgroupOf.mp hv) (congrArg Subtype.val hkv))
  refine ⟨hdisj, ?_⟩
  have hk3' : orderOf (π' k) = 3 :=
    orderOf_map_eq_three hker hU2 k.2 (by rw [Subgroup.orderOf_coe]; exact hk3)
  set f : ↥N →* A7 := π'.comp N.subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker] at hn
    have : (n : ↥M2) ∈ U.subgroupOf M2 ⊓ N := ⟨hn, n.2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hkerπ : ((alternatingGroup (Fin 7)).subtype.comp π').ker = U.subgroupOf M2 := by
    rw [← hker]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one]
  have hrange : f.range = Subgroup.normalizer (Subgroup.zpowers (π' k) : Set A7) := by
    apply le_antisymm
    · rintro _ ⟨n, rfl⟩
      rw [mem_normalizer_zpowers_iff_of_order_three hk3']
      rcases (mem_normalizer_zpowers_iff_of_order_three hk3).mp n.2 with h | h
      · left
        rw [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_inv, ← map_mul, ← map_mul, h]
      · right
        rw [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_inv, ← map_mul, ← map_mul, h,
          map_inv]
    · intro σ hσ
      obtain ⟨m, rfl⟩ := hsurj σ
      have hm : ((alternatingGroup (Fin 7)).subtype.comp π') m *
          ((alternatingGroup (Fin 7)).subtype.comp π') k *
            (((alternatingGroup (Fin 7)).subtype.comp π') m)⁻¹ =
              ((alternatingGroup (Fin 7)).subtype.comp π') k ∨
          ((alternatingGroup (Fin 7)).subtype.comp π') m *
            ((alternatingGroup (Fin 7)).subtype.comp π') k *
              (((alternatingGroup (Fin 7)).subtype.comp π') m)⁻¹ =
                (((alternatingGroup (Fin 7)).subtype.comp π') k)⁻¹ := by
        rcases (mem_normalizer_zpowers_iff_of_order_three hk3').mp hσ with h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
      obtain ⟨n, hnN, hnm⟩ := exists_mem_normalizer_map_eq hkerπ hU2 hUM2 hk3 m hm
      exact ⟨⟨n, hnN⟩, Subtype.ext hnm⟩
  rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hrange]
  exact card_normalizer_zpowers_three_cycle hct

theorem exists_isComplement_of_setting
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ A : Subgroup ↥M2, ((pCoreOf 2 M2).subgroupOf M2).IsComplement' A := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', -, hsurj, hker, -, -, hU16, hU2', -, -, hπ'⟩ := exists_rho_of_setting hQ hyp hM23 hS
  obtain ⟨k, hkK, hk3, hfpf⟩ := exists_fpf_three_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkM2 : k ∈ M2 := hS.K_lt.le hkK
  have hct := cycleType_map_eq_three_of_mem_oTwoUpper h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hkK
    hk3 hkM2
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hk3' : orderOf (⟨k, hkM2⟩ : ↥M2) = 3 := by rw [← Subgroup.orderOf_coe]; exact hk3
  obtain ⟨hdisj, hcardN⟩ := card_normalizer_fpf_three hsurj hker hU2 hUM2 hk3'
    (by rw [hπ']; exact hct) hfpf
  set N := Subgroup.normalizer (Subgroup.zpowers (⟨k, hkM2⟩ : ↥M2) : Set ↥M2) with hN
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 2 (n := 3)
    (by rw [hcardN]; norm_num)
  set P := P₀.map N.subtype with hP
  have hPN : P ≤ N := Subgroup.map_subtype_le P₀
  have hcardP : Nat.card P = 8 := by
    rw [hP, Subgroup.card_map_of_injective N.subtype_injective, hP₀]
    norm_num
  set Y := (pCoreOf 2 M2).subgroupOf M2 with hY
  have hYn : Y.Normal := hker ▸ π'.normal_ker
  have hcardY : Nat.card Y = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM2).toEquiv).trans hU16
  have hYP : Disjoint Y P :=
    disjoint_iff.mpr (eq_bot_iff.mpr ((inf_le_inf_left Y hPN).trans hdisj.le))
  have hcardW : Nat.card ↥(Y ⊔ P) = 128 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y P
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hYP, hcardY, hcardP]
  have hcardM2 : Nat.card M2 = 40320 := by
    have h1 := card_map_mul_card_inf hS.ker_eq (le_refl M2)
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hS.range_eq,
      CFSG.Quasithin.H13.card_alternatingGroup_seven, inf_of_le_right hUM2, hU16] at h1
    exact h1.symm
  have hW2 : IsPGroup 2 ↥(Y ⊔ P) := IsPGroup.of_card (n := 7) (by rw [hcardW]; norm_num)
  have hidx : ¬ 2 ∣ (Y ⊔ P).index := by
    have h := Subgroup.index_mul_card (Y ⊔ P)
    rw [hcardW, hcardM2] at h
    have h315 : (Y ⊔ P).index = 315 := by omega
    rw [h315]
    norm_num
  have hcU : ∀ a b : ↥(pCoreOf 2 M2), a * b = b * a := fun a b => by
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    have ea : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    have eb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    calc a * b = (a * b)⁻¹ := e1.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ea, eb]
  have hYc : IsMulCommutative Y := ⟨⟨fun a b => by
    have h := congrArg Subtype.val (hcU ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hYp : IsPGroup 2 Y := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM2).symm
  obtain ⟨A, hA1, hA2⟩ := (gaschutz hYp (hW2.toSylow hidx)).mpr
    ⟨P, by rw [IsPGroup.toSylow_coe]; exact le_sup_right, disjoint_iff.mp hYP,
      by rw [IsPGroup.toSylow_coe]⟩
  refine ⟨A, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hA1) ?_⟩
  rw [← Subgroup.normal_mul, hA2, Subgroup.coe_top]

end CFSG.Quasithin.H13
