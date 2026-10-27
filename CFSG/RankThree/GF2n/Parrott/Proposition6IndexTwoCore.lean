module

public import CFSG.RankThree.GF2n.Parrott.Proposition6Structure
public import CFSG.RankThree.GF2n.Parrott.Proposition6D8SquareOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNSL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParS1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQA4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.OddStandard.SmallF3.Omega
open CFSG.ComponentClassification.HarrisLit.T1.F3FG

theorem mem_inf_of_commute_sup_of_sl23 {G : Type*} [Group G] {L1 L2 : Subgroup G}
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype) {x : G} (hx : x ∈ L1 ⊔ L2)
    (hc : ∀ y ∈ L1 ⊔ L2, x * y = y * x) : x ∈ L1 ⊓ L2 := by
  classical
  have hdecomp : ∀ y : G, y ∈ L1 ⊔ L2 ↔ ∃ a ∈ L1, ∃ b ∈ L2, a * b = y := by
    intro y
    constructor
    · intro hy
      rw [Subgroup.sup_eq_closure] at hy
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · rintro z (hz | hz)
        · exact ⟨z, hz, 1, L2.one_mem, by simp⟩
        · exact ⟨1, L1.one_mem, z, hz, by simp⟩
      · exact ⟨1, L1.one_mem, 1, L2.one_mem, by simp⟩
      · rintro _ _ _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, L1.mul_mem ha1 ha2, b1 * b2, L2.mul_mem hb1 hb2, ?_⟩
        calc
          a1 * a2 * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
          _ = a1 * (b1 * a2) * b2 := by rw [hcomm a2 ha2 b1 hb1]
          _ = a1 * b1 * (a2 * b2) := by group
      · rintro _ _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, L1.inv_mem ha, b⁻¹, L2.inv_mem hb, ?_⟩
        calc
          a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hcomm a ha b hb]
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem_sup ha hb
  obtain ⟨a, ha, b, hb, hab⟩ := hdecomp x |>.mp hx
  have ha_cent : a ∈ (Subgroup.center L1).map L1.subtype := by
    rw [Subgroup.mem_map]
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * a = a * (g : G)
    have hgy : (g : G) * b = b * (g : G) := hcomm (g : G) g.2 b hb
    have hxy : x * (g : G) = (g : G) * x := hc (g : G) (Subgroup.mem_sup_left g.2)
    have hby : (b : G)⁻¹ * (g : G) = (g : G) * (b : G)⁻¹ :=
      ((commute_iff_eq (g : G) b).mpr hgy).inv_right.symm.eq
    calc
      (g : G) * a = (g : G) * (x * (b : G)⁻¹) := by
        rw [show a = x * (b : G)⁻¹ by rw [← hab]; group]
      _ = ((g : G) * x) * (b : G)⁻¹ := by group
      _ = (x * (g : G)) * (b : G)⁻¹ := by rw [hxy]
      _ = x * ((g : G) * (b : G)⁻¹) := by group
      _ = x * ((b : G)⁻¹ * (g : G)) := by rw [hby]
      _ = (x * (b : G)⁻¹) * (g : G) := by group
      _ = a * (g : G) := by
        rw [show a = x * (b : G)⁻¹ by rw [← hab]; group]
  have ha_inf : a ∈ L1 ⊓ L2 := by
    rw [hinf]
    exact ha_cent
  have hb_cent : b ∈ (Subgroup.center L2).map L2.subtype := by
    rw [Subgroup.mem_map]
    refine ⟨⟨b, hb⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * b = b * (g : G)
    have hgy : a * (g : G) = (g : G) * a := hcomm a ha (g : G) g.2
    have hxy : x * (g : G) = (g : G) * x := hc (g : G) (Subgroup.mem_sup_right g.2)
    have hay : a⁻¹ * (g : G) = (g : G) * a⁻¹ :=
      ((commute_iff_eq a (g : G)).mpr hgy).inv_left.eq
    calc
      (g : G) * b = (g : G) * (a⁻¹ * x) := by
        rw [show b = a⁻¹ * x by rw [← hab]; group]
      _ = ((g : G) * a⁻¹) * x := by group
      _ = (a⁻¹ * (g : G)) * x := by rw [hay]
      _ = a⁻¹ * ((g : G) * x) := by group
      _ = a⁻¹ * (x * (g : G)) := by rw [hxy]
      _ = (a⁻¹ * x) * (g : G) := by group
      _ = b * (g : G) := by
        rw [show b = a⁻¹ * x by rw [← hab]; group]
  have hcardInf : Nat.card ↥(L1 ⊓ L2) = 2 := by
    rw [hinf]
    obtain ⟨e⟩ := hL1
    rw [Subgroup.card_subtype L1 (Subgroup.center L1)]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6
  have hcardZ2 : Nat.card ↥((Subgroup.center L2).map L2.subtype) = 2 := by
    obtain ⟨e⟩ := hL2
    rw [Subgroup.card_subtype L2 (Subgroup.center L2)]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6
  have hleZ2 : L1 ⊓ L2 ≤ (Subgroup.center L2).map L2.subtype := by
    intro y hy
    rw [Subgroup.mem_map]
    refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * y = y * (g : G)
    exact (hcomm y hy.1 (g : G) g.2).symm
  obtain ⟨e2⟩ := hL2
  have hfinK : Finite ↥((Subgroup.center L2).map L2.subtype) :=
    Finite.of_injective
      (fun x => e2 (Subgroup.inclusion (Subgroup.map_subtype_le _) x))
      (e2.injective.comp (Subgroup.inclusion_injective _))
  have hZ2eq : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype :=
    @Subgroup.eq_of_le_of_card_ge G _ (L1 ⊓ L2) ((Subgroup.center L2).map L2.subtype)
      hfinK hleZ2 (by rw [hcardInf, hcardZ2])
  have hb_inf : b ∈ L1 ⊓ L2 := hZ2eq ▸ hb_cent
  rw [← hab]
  exact mul_mem ha_inf hb_inf

theorem inf_eq_zpowers_of_sup_eq_twoThreeCore {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) {L1 L2 : Subgroup G}
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (Subgroup.centralizer ({z} : Set G))) :
    L1 ⊓ L2 = Subgroup.zpowers z := by
  classical
  let Hc : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hzH : z ∈ Hc := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzH_center : (⟨z, hzH⟩ : ↥Hc) ∈ Subgroup.center ↥Hc := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp m.2
  let N : Subgroup ↥Hc := Subgroup.zpowers (⟨z, hzH⟩ : ↥Hc)
  have hNle : N ≤ Subgroup.center ↥Hc := by
    rw [Subgroup.zpowers_le]
    exact hzH_center
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcen := hNle hn
    rw [Subgroup.mem_center_iff] at hcen
    have h : g * n * g⁻¹ = n := by rw [hcen g]; group
    rw [h]; exact hn
  have hNcard : Nat.card N = 2 := by
    change Nat.card (Subgroup.zpowers (⟨z, hzH⟩ : ↥Hc)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz]
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using hNcard)
  have hz_pcore : (⟨z, hzH⟩ : ↥Hc) ∈ CFSG.pCore 2 ↥Hc :=
    Subgroup.mem_sSup_of_mem (S := {K : Subgroup ↥Hc | K.Normal ∧ IsPGroup 2 K})
      ⟨hNnorm, hNp⟩ (Subgroup.mem_zpowers (⟨z, hzH⟩ : ↥Hc))
  have hz_inSub : z ∈ CFSG.inSubgroup (CFSG.pCore 2) Hc := by
    rw [CFSG.inSubgroup]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzH⟩, hz_pcore, rfl⟩
  have hzM : z ∈ twoThreeCore Hc := inSubgroup_pCore_two_le_twoThreeCore Hc hz_inSub
  have hz_sup : z ∈ L1 ⊔ L2 := hsup.symm ▸ hzM
  have hz_comm : ∀ y ∈ L1 ⊔ L2, z * y = y * z := by
    intro y hy
    have hyM : y ∈ twoThreeCore Hc := hsup ▸ hy
    have hyM' : y ∈ ((CFSG.pCore 3 (↥Hc ⧸ CFSG.pCore 2 ↥Hc)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Hc))).map Hc.subtype := hyM
    have hyH : y ∈ Hc := Subgroup.map_subtype_le _ hyM'
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm
  have hz_inf : z ∈ L1 ⊓ L2 :=
    mem_inf_of_commute_sup_of_sl23 hL1 hL2 hcomm hinf hz_sup hz_comm
  have hcardInf : Nat.card ↥(L1 ⊓ L2) = 2 := by
    rw [hinf]
    obtain ⟨e⟩ := hL1
    rw [Subgroup.card_subtype L1 (Subgroup.center L1)]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6
  have hle : Subgroup.zpowers z ≤ L1 ⊓ L2 := Subgroup.zpowers_le.mpr hz_inf
  have hcardzp : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz]
  have heq : Subgroup.zpowers z = L1 ⊓ L2 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardInf, hcardzp])
  exact heq.symm

theorem exists_quaternion_core_of_sl23_pair {G : Type*} [Group G] {L1 L2 : Subgroup G}
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    {z : G} (hz : L1 ⊓ L2 = Subgroup.zpowers z) :
    ∃ U : Subgroup G,
      (∀ x, x ∈ U ↔ x ∈ L1 ⊔ L2 ∧ x ^ 4 = 1) ∧ Nat.card U = 32 ∧
      (∀ x ∈ L1 ⊔ L2, orderOf x = 2 → x ∈ U) ∧
      (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z) ∧
      (∀ a ∈ U, ∀ b ∈ U, orderOf a = 2 → orderOf b = 2 → a ≠ z → b ≠ z →
        ∃ k ∈ L1 ⊔ L2, k * a * k⁻¹ = b) ∧
      (∀ y ∈ U, orderOf y = 2 → y ≠ z → ∃ a ∈ U, ∃ b ∈ U, orderOf a = 2 ∧ orderOf b = 2 ∧
        a * y = y * a ∧ b * y = y * b ∧ a * b ≠ b * a) ∧
      (∀ x ∈ L1 ⊔ L2, (∀ u ∈ U, x * u = u * x) → x ∈ Subgroup.zpowers z) ∧
      (∃ q ∈ L1, q ∈ U ∧ q ∉ Subgroup.zpowers z) := by
  classical
  obtain ⟨e1⟩ := hL1
  obtain ⟨e2⟩ := hL2
  let Ψ : SL23 × SL23 →* G :=
    MonoidHom.noncommCoprod (L1.subtype.comp e1.symm.toMonoidHom)
      (L2.subtype.comp e2.symm.toMonoidHom)
      (fun A B => (commute_iff_eq _ _).mpr
        (hcomm _ (e1.symm A).2 _ (e2.symm B).2))
  have hPsi : ∀ A B : SL23, Ψ (A, B) = (e1.symm A : G) * (e2.symm B : G) :=
    fun A B => rfl
  have hr1 : (L1.subtype.comp e1.symm.toMonoidHom).range = L1 := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact (e1.symm A).2
    · intro hx
      exact ⟨e1 ⟨x, hx⟩, by simp⟩
  have hr2 : (L2.subtype.comp e2.symm.toMonoidHom).range = L2 := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact (e2.symm A).2
    · intro hx
      exact ⟨e2 ⟨x, hx⟩, by simp⟩
  have hrange : Ψ.range = L1 ⊔ L2 := by
    rw [MonoidHom.noncommCoprod_range, hr1, hr2]
  have hcardInf : Nat.card ↥(L1 ⊓ L2) = 2 := by
    rw [hinf]
    rw [Subgroup.card_subtype L1 (Subgroup.center L1)]
    exact (Nat.card_congr (Subgroup.centerCongr e1).toEquiv).trans card_center_sl23_p6
  have hzmem : z ∈ L1 ⊓ L2 := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hz_ne : z ≠ 1 := by
    intro h
    have h1 : Nat.card ↥(L1 ⊓ L2) = 1 := by
      rw [hz, h]
      simp
    omega
  have hzord : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := by
      rw [← hcardInf]
      exact Subgroup.orderOf_dvd_natCard (L1 ⊓ L2) hzmem
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz_ne
    · exact h
  have hz_sq : z ^ 2 = 1 := by simpa [hzord] using pow_orderOf_eq_one z
  have hneg_center : (-1 : SL23) ∈ Subgroup.center SL23 := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [neg_one_mul, mul_neg_one]
  have he1neg_center : e1.symm (-1) ∈ Subgroup.center L1 := by
    refine Subgroup.comap_center_le_center (f := e1.toMonoidHom) e1.injective ?_
    simpa using hneg_center
  have he2neg_center : e2.symm (-1) ∈ Subgroup.center L2 := by
    refine Subgroup.comap_center_le_center (f := e2.toMonoidHom) e2.injective ?_
    simpa using hneg_center
  have he1neg_inf : (e1.symm (-1) : G) ∈ L1 ⊓ L2 := by
    rw [hinf]
    exact Subgroup.mem_map_of_mem L1.subtype he1neg_center
  have hcardZ2 : Nat.card ↥((Subgroup.center L2).map L2.subtype) = 2 := by
    rw [Subgroup.card_subtype L2 (Subgroup.center L2)]
    exact (Nat.card_congr (Subgroup.centerCongr e2).toEquiv).trans card_center_sl23_p6
  have hleZ2 : L1 ⊓ L2 ≤ (Subgroup.center L2).map L2.subtype := by
    intro y hy
    rw [Subgroup.mem_map]
    refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hcomm y hy.1 (g : G) g.2).symm
  have hfinK : Finite ↥((Subgroup.center L2).map L2.subtype) :=
    Finite.of_injective
      (fun x => e2 (Subgroup.inclusion (Subgroup.map_subtype_le _) x))
      (e2.injective.comp (Subgroup.inclusion_injective _))
  have hinf2 : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype :=
    @Subgroup.eq_of_le_of_card_ge G _ (L1 ⊓ L2) ((Subgroup.center L2).map L2.subtype)
      hfinK hleZ2 (by rw [hcardInf, hcardZ2])
  have he2neg_inf : (e2.symm (-1) : G) ∈ L1 ⊓ L2 := by
    rw [hinf2]
    exact Subgroup.mem_map_of_mem L2.subtype he2neg_center
  have he1neg_ne : (e1.symm (-1) : G) ≠ 1 := by
    intro h
    have h1 : e1.symm (-1) = 1 := Subtype.ext h
    have h2 : (-1 : SL23) = 1 := by
      simpa using congrArg (fun x : ↥L1 => (e1 x : SL23)) h1
    exact (by decide : (-1 : SL23) ≠ 1) h2
  have he2neg_ne : (e2.symm (-1) : G) ≠ 1 := by
    intro h
    have h1 : e2.symm (-1) = 1 := Subtype.ext h
    have h2 : (-1 : SL23) = 1 := by
      simpa using congrArg (fun x : ↥L2 => (e2 x : SL23)) h1
    exact (by decide : (-1 : SL23) ≠ 1) h2
  have he1neg_eq_z : (e1.symm (-1) : G) = z := by
    have hmem : (e1.symm (-1) : G) ∈ Subgroup.zpowers z := by
      rw [← hz]
      exact he1neg_inf
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hmod : z ^ (k % 2) = (e1.symm (-1) : G) := by
      calc z ^ (k % 2) = z ^ (k % (2 : ℤ)) := by norm_num
        _ = z ^ k := (zpow_eq_zpow_emod' k hz_sq).symm
        _ = (e1.symm (-1) : G) := hk
    have hk0 : k % 2 = 0 ∨ k % 2 = 1 := by
      have h0 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
      omega
    rcases hk0 with h | h
    · rw [h, zpow_zero] at hmod
      exact absurd hmod.symm he1neg_ne
    · rw [h, zpow_one] at hmod
      exact hmod.symm
  have he2neg_eq_z : (e2.symm (-1) : G) = z := by
    have hmem : (e2.symm (-1) : G) ∈ Subgroup.zpowers z := by
      rw [← hz]
      exact he2neg_inf
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hmod : z ^ (k % 2) = (e2.symm (-1) : G) := by
      calc z ^ (k % 2) = z ^ (k % (2 : ℤ)) := by norm_num
        _ = z ^ k := (zpow_eq_zpow_emod' k hz_sq).symm
        _ = (e2.symm (-1) : G) := hk
    have hk0 : k % 2 = 0 ∨ k % 2 = 1 := by
      have h0 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
      omega
    rcases hk0 with h | h
    · rw [h, zpow_zero] at hmod
      exact absurd hmod.symm he2neg_ne
    · rw [h, zpow_one] at hmod
      exact hmod.symm
  have hPsi_one_one : Ψ (1, 1) = 1 := map_one Ψ
  have hPsi_neg_neg : Ψ (-1, -1) = 1 := by
    rw [hPsi, he1neg_eq_z, he2neg_eq_z]
    simpa [pow_two] using hz_sq
  have hPsi_neg_one : Ψ (-1, 1) = z := by
    rw [hPsi, he1neg_eq_z, map_one, Subgroup.coe_one, mul_one]
  have hPsi_one_neg : Ψ (1, -1) = z := by
    rw [hPsi, map_one, Subgroup.coe_one, one_mul, he2neg_eq_z]
  have hker : ∀ A B : SL23, Ψ (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1) := by
    intro A B
    constructor
    · intro h
      have heq : (e1.symm A : G) * (e2.symm B : G) = 1 := by
        rw [← hPsi A B]
        exact h
      have h2 : (e1.symm A : G) = ((e2.symm B : G))⁻¹ := eq_inv_of_mul_eq_one_left heq
      have hA_inf : (e1.symm A : G) ∈ L1 ⊓ L2 := by
        refine ⟨(e1.symm A).2, ?_⟩
        rw [h2]
        exact L2.inv_mem (e2.symm B).2
      have hA_c : (e1.symm A : G) ∈ (Subgroup.center L1).map L1.subtype := by
        rwa [← hinf]
      obtain ⟨c, hc, hcA⟩ := Subgroup.mem_map.mp hA_c
      have hAc : e1 c = A := by
        have hceq : c = e1.symm A := Subtype.ext hcA
        simpa using congrArg (fun x : ↥L1 => (e1 x : SL23)) hceq
      have hA_center : A ∈ Subgroup.center SL23 := by
        rw [← hAc, ← Subgroup.map_center_eq e1]
        exact Subgroup.mem_map_of_mem e1.toMonoidHom hc
      have hB_inf : (e2.symm B : G) ∈ L1 ⊓ L2 := by
        refine ⟨?_, (e2.symm B).2⟩
        rw [show (e2.symm B : G) = ((e1.symm A : G))⁻¹ by rw [h2, inv_inv]]
        exact L1.inv_mem (e1.symm A).2
      have hB_c : e2.symm B ∈ Subgroup.center L2 := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact (hcomm (e2.symm B : G) hB_inf.1 (g : G) g.2).symm
      have hB_center : B ∈ Subgroup.center SL23 := by
        rw [← Subgroup.map_center_eq e2]
        simpa using Subgroup.mem_map_of_mem e2.toMonoidHom hB_c
      have hA := eq_one_or_eq_neg_one_of_mem_center_sl23 hA_center
      have hB := eq_one_or_eq_neg_one_of_mem_center_sl23 hB_center
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · rw [hPsi_one_neg] at h
        exact absurd h hz_ne
      · rw [hPsi_neg_one] at h
        exact absurd h hz_ne
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hPsi_one_one
      · exact hPsi_neg_neg
  have hQ8card : Nat.card sl23Q8 = 8 := by
    rw [← sl23_pCore_eq_Q8]
    exact sl23_card_pCore
  have hneg_mem_Q8 : (-1 : SL23) ∈ sl23Q8 := by
    rw [← sl23_pCore_eq_Q8]
    exact sl23_neg_one_mem_pCore
  let Q : Subgroup (SL23 × SL23) := sl23Q8.prod sl23Q8
  let U : Subgroup G := Q.map Ψ
  have hQmk : Q = sl23Q8.prod sl23Q8 := rfl
  have hUmem : ∀ x, x ∈ U ↔ x ∈ L1 ⊔ L2 ∧ x ^ 4 = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      have hq1 : q.1 ^ 4 = 1 := (Subgroup.mem_prod.mp hq).1
      have hq2 : q.2 ^ 4 = 1 := (Subgroup.mem_prod.mp hq).2
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact ⟨q, rfl⟩
      · have hq4 : q ^ 4 = 1 := by
          apply Prod.ext
          · simpa using hq1
          · simpa using hq2
        rw [← map_pow, hq4, map_one]
    · intro ⟨hxsup, hx4⟩
      rw [← hrange] at hxsup
      obtain ⟨q, hq⟩ := hxsup
      obtain ⟨A, B⟩ := q
      have hAB : Ψ (A, B) = x := hq
      have h4 : Ψ (A ^ 4, B ^ 4) = 1 := by
        have h := map_pow Ψ (A, B) 4
        rw [hAB, hx4] at h
        simpa using h
      rcases (hker (A ^ 4) (B ^ 4)).mp h4 with ⟨hA4, hB4⟩ | ⟨hA4, hB4⟩
      · exact Subgroup.mem_map.mpr ⟨(A, B), Subgroup.mem_prod.mpr ⟨hA4, hB4⟩, hAB⟩
      · exact absurd hA4 (sec5cn_pow4_ne_neg A)
  have hcardU : Nat.card U = 32 := by
    let φ : ↥Q →* G := Ψ.comp Q.subtype
    have hφrange : φ.range = U := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact Subgroup.mem_map.mpr ⟨q, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    have hkerφ : Nat.card ↥φ.ker = 2 := by
      have hmem_neg : ((-1, -1) : SL23 × SL23) ∈ Q := by
        rw [hQmk, Subgroup.mem_prod]
        exact ⟨hneg_mem_Q8, hneg_mem_Q8⟩
      have hker_eq : φ.ker = Subgroup.zpowers (⟨(-1, -1), hmem_neg⟩ : ↥Q) := by
        apply le_antisymm
        · intro u hu
          have hu1 : Ψ (u.1.1, u.1.2) = 1 := by
            have h : Ψ (u.1 : SL23 × SL23) = 1 := hu
            simpa using h
          rcases (hker u.1.1 u.1.2).mp hu1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hu_eq : u = 1 := by
              apply Subtype.ext
              exact Prod.ext h1 h2
            rw [hu_eq]
            exact Subgroup.one_mem _
          · have hu_eq : u = ⟨(-1, -1), hmem_neg⟩ := by
              apply Subtype.ext
              exact Prod.ext h1 h2
            rw [hu_eq]
            exact Subgroup.mem_zpowers _
        · rw [Subgroup.zpowers_le]
          exact (hker (-1) (-1)).mpr (Or.inr ⟨rfl, rfl⟩)
      rw [hker_eq]
      change Nat.card (Subgroup.zpowers (⟨(-1, -1), hmem_neg⟩ : ↥Q)) = 2
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, Prod.orderOf_mk]
      have hneg : orderOf (-1 : SL23) = 2 :=
        orderOf_eq_prime (p := 2) (by decide) (by decide)
      rw [hneg]
      norm_num
    have hcardQ : Nat.card ↥Q = 64 := by
      rw [hQmk]
      rw [Nat.card_congr (Subgroup.prodEquiv sl23Q8 sl23Q8).toEquiv, Nat.card_prod, hQ8card]
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hkerφ, hcardQ, hφrange] at hmul
    omega
  have hinv_mem : ∀ x ∈ L1 ⊔ L2, orderOf x = 2 → x ∈ U := by
    intro x hx hxord
    have hx2 : x ^ 2 = 1 := by simpa [hxord] using pow_orderOf_eq_one x
    have hx4 : x ^ 4 = 1 := by
      calc x ^ 4 = x ^ (2 * 2) := by norm_num
        _ = (x ^ 2) ^ 2 := pow_mul x 2 2
        _ = 1 := by rw [hx2, one_pow]
    exact (hUmem x).mpr ⟨hx, hx4⟩
  have hcommU : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro a ha b hb
    obtain ⟨qa, hqa, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨qb, hqb, rfl⟩ := Subgroup.mem_map.mp hb
    have hqa1 : qa.1 ^ 4 = 1 := (Subgroup.mem_prod.mp hqa).1
    have hqa2 : qa.2 ^ 4 = 1 := (Subgroup.mem_prod.mp hqa).2
    have hqb1 : qb.1 ^ 4 = 1 := (Subgroup.mem_prod.mp hqb).1
    have hqb2 : qb.2 ^ 4 = 1 := (Subgroup.mem_prod.mp hqb).2
    have hca : qa.1 * qb.1 * qa.1⁻¹ * qb.1⁻¹ = 1 ∨
        qa.1 * qb.1 * qa.1⁻¹ * qb.1⁻¹ = -1 :=
      (sl23_q8_comm_sq qa.1 qb.1 hqa1 hqb1).1
    have hcb : qa.2 * qb.2 * qa.2⁻¹ * qb.2⁻¹ = 1 ∨
        qa.2 * qb.2 * qa.2⁻¹ * qb.2⁻¹ = -1 :=
      (sl23_q8_comm_sq qa.2 qb.2 hqa2 hqb2).1
    have hcommpair : Ψ (qa * qb * qa⁻¹ * qb⁻¹) =
        Ψ qa * Ψ qb * (Ψ qa)⁻¹ * (Ψ qb)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← hcommpair]
    change Ψ (qa.1 * qb.1 * qa.1⁻¹ * qb.1⁻¹, qa.2 * qb.2 * qa.2⁻¹ * qb.2⁻¹) ∈
      Subgroup.zpowers z
    rcases hca with h1 | h1 <;> rcases hcb with h2 | h2
    · rw [h1, h2, hPsi_one_one]
      exact Subgroup.one_mem _
    · rw [h1, h2, hPsi_one_neg]
      exact Subgroup.mem_zpowers z
    · rw [h1, h2, hPsi_neg_one]
      exact Subgroup.mem_zpowers z
    · rw [h1, h2, hPsi_neg_neg]
      exact Subgroup.one_mem _
  have hpair_comm : ∀ (a1 a2 b1 b2 : SL23),
      Ψ (a1, a2) * Ψ (b1, b2) * (Ψ (a1, a2))⁻¹ * (Ψ (b1, b2))⁻¹ =
        Ψ (a1 * b1 * a1⁻¹ * b1⁻¹, a2 * b2 * a2⁻¹ * b2⁻¹) := by
    intro a1 a2 b1 b2
    calc
      Ψ (a1, a2) * Ψ (b1, b2) * (Ψ (a1, a2))⁻¹ * (Ψ (b1, b2))⁻¹
          = Ψ ((a1, a2) * (b1, b2)) * (Ψ (a1, a2))⁻¹ * (Ψ (b1, b2))⁻¹ := by
            rw [map_mul]
      _ = Ψ ((a1, a2) * (b1, b2)) * Ψ ((a1, a2)⁻¹) * (Ψ (b1, b2))⁻¹ := by
            rw [← map_inv]
      _ = Ψ ((a1, a2) * (b1, b2)) * Ψ ((a1, a2)⁻¹) * Ψ ((b1, b2)⁻¹) := by
            rw [← map_inv]
      _ = Ψ (a1 * b1 * a1⁻¹ * b1⁻¹, a2 * b2 * a2⁻¹ * b2⁻¹) := by
            rw [← map_mul, ← map_mul]
            congr 1
  have conj_neg : ∀ x t : SL23, t⁻¹ * x * t = -x → t * x * t⁻¹ = -x := by
    intro x t ht
    have h1 : x * t = t * (-x) := by
      have := congrArg (fun w => t * w) ht
      simpa [mul_assoc] using this
    have h2 : x = t * (-x) * t⁻¹ := by
      calc x = (x * t) * t⁻¹ := by group
        _ = (t * (-x)) * t⁻¹ := by rw [h1]
    have h3 : t * (-x) * t⁻¹ = -(t * x * t⁻¹) := by rw [mul_neg, neg_mul]
    rw [h3] at h2
    have := congrArg Neg.neg h2
    simpa using this.symm
  have anti_sq : ∀ x t : SL23, x * x = -1 → t ^ 4 = 1 → t⁻¹ * x * t = -x →
      t * t = -1 := by
    intro x t hx ht4 ht
    have ht2 : t * t = 1 ∨ t * t = -1 := (sl23_q8_comm_sq t t ht4 ht4).2
    rcases ht2 with h | h
    · exfalso
      have htinv : t = 1 ∨ t = -1 := sl23_unique_involution t h
      rcases htinv with rfl | rfl
      · rw [inv_one, one_mul, mul_one] at ht
        exact sec5cn_neg_ne x ht.symm
      · have hneg : (-1 : SL23)⁻¹ = -1 := by
          rw [inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])]
        rw [hneg, neg_one_mul, mul_neg_one, neg_neg] at ht
        exact sec5cn_neg_ne x ht.symm
    · exact h
  have hrepr : ∀ y ∈ U, orderOf y = 2 → y ≠ z →
      ∃ y1 y2 : SL23, y1 * y1 = -1 ∧ y2 * y2 = -1 ∧ y = Ψ (y1, y2) := by
    intro y hyU hyord hyne
    have hy2 : y ^ 2 = 1 := by simpa [hyord] using pow_orderOf_eq_one y
    have hysup : y ∈ L1 ⊔ L2 := ((hUmem y).mp hyU).1
    rw [← hrange] at hysup
    obtain ⟨q, hq⟩ := hysup
    obtain ⟨A, B⟩ := q
    have hAB : Ψ (A, B) = y := hq
    have hker2 : Ψ (A ^ 2, B ^ 2) = 1 := by
      have h := map_pow Ψ (A, B) 2
      rw [hAB, hy2] at h
      simpa using h
    rcases (hker (A ^ 2) (B ^ 2)).mp hker2 with ⟨hA2, hB2⟩ | ⟨hA2, hB2⟩
    · have hA : A = 1 ∨ A = -1 := sl23_unique_involution A (by simpa [pow_two] using hA2)
      have hB : B = 1 ∨ B = -1 := sl23_unique_involution B (by simpa [pow_two] using hB2)
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · have hy1 : y = 1 := by rw [← hAB]; exact hPsi_one_one
        rw [hy1] at hyord
        simp at hyord
      · have hyz : y = z := by rw [← hAB]; exact hPsi_one_neg
        exact (hyne hyz).elim
      · have hyz : y = z := by rw [← hAB]; exact hPsi_neg_one
        exact (hyne hyz).elim
      · have hy1 : y = 1 := by rw [← hAB]; exact hPsi_neg_neg
        rw [hy1] at hyord
        simp at hyord
    · exact ⟨A, B, by rwa [pow_two] at hA2, by rwa [pow_two] at hB2, hAB.symm⟩
  have htrans : ∀ a ∈ U, ∀ b ∈ U, orderOf a = 2 → orderOf b = 2 → a ≠ z → b ≠ z →
      ∃ k ∈ L1 ⊔ L2, k * a * k⁻¹ = b := by
    intro a haU b hbU haord hbord hane hbne
    obtain ⟨a1, a2, ha1, ha2, rfl⟩ := hrepr a haU haord hane
    obtain ⟨b1, b2, hb1, hb2, rfl⟩ := hrepr b hbU hbord hbne
    have adjust : ∀ x y : SL23, x * x = -1 → y * y = -1 →
        ∃ c' : SL23, c' * x * c'⁻¹ = y := by
      intro x y hx hy
      obtain ⟨c, h | h⟩ := par_sl23_trans x y hx hy
      · exact ⟨c, h⟩
      · obtain ⟨t, -, ht⟩ := sec5cn_exists_anti x hx
        have ht' : t * x * t⁻¹ = -x := conj_neg x t ht
        refine ⟨c * t, ?_⟩
        calc
          (c * t) * x * (c * t)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ := by group
          _ = c * (-x) * c⁻¹ := by rw [ht']
          _ = -(c * x * c⁻¹) := by rw [mul_neg, neg_mul]
          _ = -(-y) := by rw [h]
          _ = y := neg_neg y
    obtain ⟨c1', hc1'⟩ := adjust a1 b1 ha1 hb1
    obtain ⟨c2', hc2'⟩ := adjust a2 b2 ha2 hb2
    refine ⟨Ψ (c1', c2'), ?_, ?_⟩
    · rw [← hrange]
      exact ⟨(c1', c2'), rfl⟩
    · calc
        Ψ (c1', c2') * Ψ (a1, a2) * (Ψ (c1', c2'))⁻¹
            = Ψ ((c1', c2') * (a1, a2) * (c1', c2')⁻¹) := by
              simp only [map_mul, map_inv]
        _ = Ψ (b1, b2) := by
              congr 1
              apply Prod.ext
              · simpa using hc1'
              · simpa using hc2'
  have hpair : ∀ y ∈ U, orderOf y = 2 → y ≠ z →
      ∃ a ∈ U, ∃ b ∈ U, orderOf a = 2 ∧ orderOf b = 2 ∧
        a * y = y * a ∧ b * y = y * b ∧ a * b ≠ b * a := by
    intro y hyU hyord hyne
    obtain ⟨y1, y2, hy1, hy2, hy_eq⟩ := hrepr y hyU hyord hyne
    obtain ⟨c, hc4, hcanti⟩ := sec5cn_exists_anti y1 hy1
    obtain ⟨d, hd4, hdanti⟩ := sec5cn_exists_anti y2 hy2
    have hc2 : c * c = -1 := anti_sq y1 c hy1 hc4 hcanti
    have hd2 : d * d = -1 := anti_sq y2 d hy2 hd4 hdanti
    have hcy : c * y1 * c⁻¹ = -y1 := conj_neg y1 c hcanti
    have hdy : d * y2 * d⁻¹ = -y2 := conj_neg y2 d hdanti
    have hy1_4 : y1 ^ 4 = 1 := sec5cn_pow4_of_sq y1 (Or.inr hy1)
    have hy2_4 : y2 ^ 4 = 1 := sec5cn_pow4_of_sq y2 (Or.inr hy2)
    have hcy4 : (c * y1) ^ 4 = 1 := sec5cn_q8_mul c y1 hc4 hy1_4
    have hcy_anti : c * y1 = -(y1 * c) := by
      calc c * y1 = (c * y1 * c⁻¹) * c := by group
        _ = (-y1) * c := by rw [hcy]
        _ = -(y1 * c) := by rw [neg_mul]
    have hy1_inv : y1⁻¹ = -y1 := by
      rw [inv_eq_of_mul_eq_one_right (by rw [mul_neg, hy1, neg_neg])]
    have hcy_sq_ne : (c * y1) * (c * y1) ≠ 1 := by
      intro h
      have hp : c * y1 = 1 ∨ c * y1 = -1 := sl23_unique_involution (c * y1) h
      have hpy : (c * y1) * y1 = -c := by
        calc (c * y1) * y1 = c * (y1 * y1) := by group
          _ = c * (-1) := by rw [hy1]
          _ = -c := mul_neg_one c
      have hyp : y1 * (c * y1) = c := by
        calc y1 * (c * y1) = y1 * (-(y1 * c)) := by rw [hcy_anti]
          _ = -(y1 * (y1 * c)) := by rw [mul_neg]
          _ = -((y1 * y1) * c) := by rw [mul_assoc]
          _ = -((-1) * c) := by rw [hy1]
          _ = -(-c) := by rw [neg_one_mul]
          _ = c := neg_neg c
      have hne : (c * y1) * y1 ≠ y1 * (c * y1) := by
        rw [hpy, hyp]
        exact sec5cn_neg_ne c
      rcases hp with hp | hp
      · exact hne (by rw [hp, one_mul, mul_one])
      · exact hne (by rw [hp, neg_one_mul, mul_neg_one])
    have hcy_sq : (c * y1) * (c * y1) = -1 := by
      rcases (sl23_q8_comm_sq (c * y1) (c * y1) hcy4 hcy4).2 with h | h
      · exact absurd h hcy_sq_ne
      · exact h
    let a : G := Ψ (c, d)
    let b : G := Ψ (c * y1, d)
    have ha2 : a ^ 2 = 1 := by
      change (Ψ (c, d)) ^ 2 = 1
      rw [← map_pow]
      have hcd2 : ((c, d) : SL23 × SL23) ^ 2 = (-1, -1) := by
        apply Prod.ext
        · simpa [pow_two] using hc2
        · simpa [pow_two] using hd2
      rw [hcd2, hPsi_neg_neg]
    have hb2 : b ^ 2 = 1 := by
      change (Ψ (c * y1, d)) ^ 2 = 1
      rw [← map_pow]
      have hcd2 : ((c * y1, d) : SL23 × SL23) ^ 2 = (-1, -1) := by
        apply Prod.ext
        · simpa [pow_two] using hcy_sq
        · simpa [pow_two] using hd2
      rw [hcd2, hPsi_neg_neg]
    have haU : a ∈ U := by
      rw [hUmem]
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact ⟨(c, d), rfl⟩
      · calc a ^ 4 = (a ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          _ = 1 := by rw [ha2, one_pow]
    have hbU : b ∈ U := by
      rw [hUmem]
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact ⟨(c * y1, d), rfl⟩
      · calc b ^ 4 = (b ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          _ = 1 := by rw [hb2, one_pow]
    have ha_ne : a ≠ 1 := by
      intro h
      have hker1 : Ψ (c, d) = 1 := h
      rcases (hker c d).mp hker1 with ⟨hc1, hd1⟩ | ⟨hc1, hd1⟩
      · rw [hc1, mul_one] at hc2
        exact (by decide : (1 : SL23) ≠ -1) hc2
      · rw [hc1, neg_mul_neg, one_mul] at hc2
        exact (by decide : (1 : SL23) ≠ -1) hc2
    have hb_ne : b ≠ 1 := by
      intro h
      have hker1 : Ψ (c * y1, d) = 1 := h
      rcases (hker (c * y1) d).mp hker1 with ⟨hcd1, hd1⟩ | ⟨hcd1, hd1⟩
      · rw [hcd1, mul_one] at hcy_sq
        exact (by decide : (1 : SL23) ≠ -1) hcy_sq
      · rw [hcd1, neg_mul_neg, one_mul] at hcy_sq
        exact (by decide : (1 : SL23) ≠ -1) hcy_sq
    have haord : orderOf a = 2 := orderOf_eq_prime ha2 ha_ne
    have hbord : orderOf b = 2 := orderOf_eq_prime hb2 hb_ne
    have hay : a * y = y * a := by
      have hcom : a * y * a⁻¹ * y⁻¹ = 1 := by
        have hp : a * y * a⁻¹ * y⁻¹ =
            Ψ (c * y1 * c⁻¹ * y1⁻¹, d * y2 * d⁻¹ * y2⁻¹) := by
          rw [hy_eq]
          exact hpair_comm c d y1 y2
        rw [hp]
        have h1 : c * y1 * c⁻¹ * y1⁻¹ = -1 := by
          rw [hcy, neg_mul, mul_inv_cancel]
        have h2 : d * y2 * d⁻¹ * y2⁻¹ = -1 := by
          rw [hdy, neg_mul, mul_inv_cancel]
        rw [h1, h2, hPsi_neg_neg]
      calc a * y = (a * y * a⁻¹ * y⁻¹) * (y * a) := by group
        _ = 1 * (y * a) := by rw [hcom]
        _ = y * a := one_mul _
    have hby : b * y = y * b := by
      have hcom : b * y * b⁻¹ * y⁻¹ = 1 := by
        have hp : b * y * b⁻¹ * y⁻¹ =
            Ψ ((c * y1) * y1 * (c * y1)⁻¹ * y1⁻¹, d * y2 * d⁻¹ * y2⁻¹) := by
          rw [hy_eq]
          exact hpair_comm (c * y1) d y1 y2
        rw [hp]
        have h1 : (c * y1) * y1 * (c * y1)⁻¹ * y1⁻¹ = -1 := by
          have heq : (c * y1) * y1 * (c * y1)⁻¹ * y1⁻¹ =
              c * y1 * c⁻¹ * y1⁻¹ := by group
          rw [heq, hcy, neg_mul, mul_inv_cancel]
        have h2 : d * y2 * d⁻¹ * y2⁻¹ = -1 := by
          rw [hdy, neg_mul, mul_inv_cancel]
        rw [h1, h2, hPsi_neg_neg]
      calc b * y = (b * y * b⁻¹ * y⁻¹) * (y * b) := by group
        _ = 1 * (y * b) := by rw [hcom]
        _ = y * b := one_mul _
    have hab_ne : a * b ≠ b * a := by
      have h1 : c * (c * y1) * c⁻¹ * (c * y1)⁻¹ = -1 := by
        have hcinv : c⁻¹ = -c := by
          rw [inv_eq_of_mul_eq_one_right (by rw [mul_neg, hc2, neg_neg])]
        have hanti : y1 * c = -(c * y1) := by
          have := congrArg Neg.neg hcy_anti
          simpa using this.symm
        have hconj : c * (c * y1) * c⁻¹ = -(c * y1) := by
          calc
            c * (c * y1) * c⁻¹ = c * c * y1 * c⁻¹ := by group
            _ = (-1) * y1 * c⁻¹ := by rw [hc2]
            _ = -(y1 * c⁻¹) := by rw [neg_one_mul, neg_mul]
            _ = -(y1 * (-c)) := by rw [hcinv]
            _ = -(-(y1 * c)) := by rw [mul_neg]
            _ = y1 * c := neg_neg _
            _ = -(c * y1) := hanti
        rw [hconj, neg_mul, mul_inv_cancel]
      have hcom : a * b * a⁻¹ * b⁻¹ = z := by
        have hp : a * b * a⁻¹ * b⁻¹ =
            Ψ (c * (c * y1) * c⁻¹ * (c * y1)⁻¹, d * d * d⁻¹ * d⁻¹) :=
          hpair_comm c d (c * y1) d
        rw [h1, show d * d * d⁻¹ * d⁻¹ = 1 by group, hPsi_neg_one] at hp
        exact hp
      intro h
      have hone : a * b * a⁻¹ * b⁻¹ = 1 := by rw [h]; group
      rw [hcom] at hone
      exact hz_ne hone
    exact ⟨a, haU, b, hbU, haord, hbord, hay, hby, hab_ne⟩
  have hcent : ∀ x ∈ L1 ⊔ L2, (∀ u ∈ U, x * u = u * x) → x ∈ Subgroup.zpowers z := by
    intro x hx hcentx
    rw [← hrange] at hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨A, B⟩ := q
    have hAB : Ψ (A, B) = x := hq
    have hAq : ∀ p : SL23, p ^ 4 = 1 → A * p = p * A := by
      intro p hp
      have huQ : (p, (1 : SL23)) ∈ Q := Subgroup.mem_prod.mpr ⟨hp, sl23Q8.one_mem⟩
      have hu : Ψ (p, 1) ∈ U := Subgroup.mem_map.mpr ⟨(p, 1), huQ, rfl⟩
      have h := hcentx (Ψ (p, 1)) hu
      have hc : Ψ (A, B) * Ψ (p, 1) * (Ψ (A, B))⁻¹ * (Ψ (p, 1))⁻¹ = 1 := by
        rw [hAB, h]
        group
      have hpcomm := hpair_comm A B p 1
      rw [hpcomm] at hc
      have hsecond : B * 1 * B⁻¹ * 1⁻¹ = 1 := by group
      rw [hsecond] at hc
      rcases (hker (A * p * A⁻¹ * p⁻¹) 1).mp hc with ⟨h1, -⟩ | ⟨h1, h2⟩
      · calc A * p = (A * p * A⁻¹ * p⁻¹) * (p * A) := by group
          _ = 1 * (p * A) := by rw [h1]
          _ = p * A := one_mul _
      · exfalso
        have : (1 : SL23) = -1 := by simpa using h2
        exact (by decide : (1 : SL23) ≠ -1) this
    have hBq : ∀ p : SL23, p ^ 4 = 1 → B * p = p * B := by
      intro p hp
      have huQ : ((1 : SL23), p) ∈ Q := Subgroup.mem_prod.mpr ⟨sl23Q8.one_mem, hp⟩
      have hu : Ψ (1, p) ∈ U := Subgroup.mem_map.mpr ⟨(1, p), huQ, rfl⟩
      have h := hcentx (Ψ (1, p)) hu
      have hc : Ψ (A, B) * Ψ (1, p) * (Ψ (A, B))⁻¹ * (Ψ (1, p))⁻¹ = 1 := by
        rw [hAB, h]
        group
      have hpcomm := hpair_comm A B 1 p
      rw [hpcomm] at hc
      have hfirst : A * 1 * A⁻¹ * 1⁻¹ = 1 := by group
      rw [hfirst] at hc
      rcases (hker 1 (B * p * B⁻¹ * p⁻¹)).mp hc with ⟨-, h2⟩ | ⟨h1, h2⟩
      · calc B * p = (B * p * B⁻¹ * p⁻¹) * (p * B) := by group
          _ = 1 * (p * B) := by rw [h2]
          _ = p * B := one_mul _
      · exfalso
        have : (1 : SL23) = -1 := by simpa using h1
        exact (by decide : (1 : SL23) ≠ -1) this
    have hA := sec5cn_centralizer_q8 A hAq
    have hB := sec5cn_centralizer_q8 B hBq
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · rw [← hAB, hPsi_one_one]
      exact Subgroup.one_mem _
    · rw [← hAB, hPsi_one_neg]
      exact Subgroup.mem_zpowers z
    · rw [← hAB, hPsi_neg_one]
      exact Subgroup.mem_zpowers z
    · rw [← hAB, hPsi_neg_neg]
      exact Subgroup.one_mem _
  have hex : ∃ q ∈ L1, q ∈ U ∧ q ∉ Subgroup.zpowers z := by
    refine ⟨(e1.symm P6Model.alpha : G), (e1.symm P6Model.alpha).2, ?_, ?_⟩
    · have hq4 : (e1.symm P6Model.alpha : G) ^ 4 = 1 := by
        have h : ((e1.symm P6Model.alpha : ↥L1) ^ 4 : ↥L1) = 1 := by
          apply e1.injective
          rw [map_pow, MulEquiv.apply_symm_apply, P6Model.alpha_pow_four, map_one]
        simpa using congrArg (fun x : ↥L1 => (x : G)) h
      exact (hUmem _).mpr ⟨Subgroup.mem_sup_left (e1.symm P6Model.alpha).2, hq4⟩
    · intro hmem
      have hq2 : (e1.symm P6Model.alpha : G) ^ 2 = z := by
        have h : ((e1.symm P6Model.alpha : ↥L1) ^ 2 : ↥L1) = e1.symm (-1) := by
          apply e1.injective
          rw [map_pow, MulEquiv.apply_symm_apply, P6Model.alpha_sq]
          simp
        calc (e1.symm P6Model.alpha : G) ^ 2
            = ((e1.symm P6Model.alpha : ↥L1) ^ 2 : G) := rfl
          _ = (e1.symm (-1) : G) := congrArg (fun x : ↥L1 => (x : G)) h
          _ = z := he1neg_eq_z
      have hdvd : orderOf (e1.symm P6Model.alpha : G) ∣ 2 := by
        have h := orderOf_dvd_of_mem_zpowers hmem
        rwa [hzord] at h
      have hq1 : (e1.symm P6Model.alpha : G) ^ 2 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hdvd
      have : z = 1 := by rw [← hq2, hq1]
      exact hz_ne this
  exact ⟨U, hUmem, hcardU, hinv_mem, hcommU, htrans, hpair, hcent, hex⟩

end CFSG.RankThree.GF2n.Parrott
