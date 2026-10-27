module

public import CFSG.Quasithin.MS93.S38G2Rep
public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.Background.SmithC27RTypeU33

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.MS93
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem isSimpleGroup_g2Derived' :
    IsSimpleGroup ↥(g2Derived (ZMod 2)) := by
  have := SmithC27.isSimpleGroup_g2Derived (Nat.card_zmod 2)
  exact (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)).isSimpleGroup

theorem card_g2Derived :
    Nat.card ↥(g2Derived (ZMod 2)) = 6048 :=
  B42U33.card_of_b42TypeU33 (SmithC27.b42TypeU33_of_equiv (Nat.card_zmod 2)
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)))

theorem eq_one_of_central
    (c : ↥(g2Derived (ZMod 2))) (hc : ∀ d, d * c = c * d) :
    c = 1 := by
  have hDs := isSimpleGroup_g2Derived'
  rcases hDs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(g2Derived (ZMod 2))) with h1 | h1
  · have hmem : c ∈ Subgroup.center ↥(g2Derived (ZMod 2)) := Subgroup.mem_center_iff.mpr hc
    rw [h1, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hcomm : ∀ a b : ↥(g2Derived (ZMod 2)), a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a
    let _ : CommGroup ↥(g2Derived (ZMod 2)) := { (inferInstance : Group _) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := ↥(g2Derived (ZMod 2)))
    rw [card_g2Derived] at hp
    norm_num at hp

theorem mem_pCoreOf_of_mem_L
    (hR : G2Rep h f φ) (l : ↥L) (hl : φ (Subgroup.inclusion h.L_le l) = 1) :
    (l : G) ∈ pCoreOf 2 M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φL : ↥L →* ↥(quasithinG2 (ZMod 2)) := φ.comp (Subgroup.inclusion h.L_le) with hφL
  have hO : CFSG.pCore 2 ↥L ≤ φL.ker := by
    intro o ho
    rw [MonoidHom.mem_ker]
    exact hR.map_pCoreOf (pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
      (mem_pCoreOf_of_mem_pCore_two ho))
  set φb : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(quasithinG2 (ZMod 2)) := QuotientGroup.lift _ φL hO
    with hφbdef
  have hφb : ∀ l : ↥L, φb (QuotientGroup.mk l) = φL l := fun _ => rfl
  have hq := h.quasisimple
  have hmemD : ∀ x, φb x ∈ g2Derived (ZMod 2) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H l => exact hR.L_le _ l.2
  have hontoD : ∀ δ ∈ g2Derived (ZMod 2), ∃ x, φb x = δ := by
    intro δ hδ
    obtain ⟨l, hl, rfl⟩ := hR.L_onto δ hδ
    exact ⟨QuotientGroup.mk ⟨l, hl⟩, rfl⟩
  have hne : ∃ x, φb x ≠ 1 := by
    have hnt : Nontrivial ↥(g2Derived (ZMod 2)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, card_g2Derived]
      norm_num
    obtain ⟨δ, hδ⟩ := exists_ne (1 : ↥(g2Derived (ZMod 2)))
    obtain ⟨x, hx⟩ := hontoD δ.1 δ.2
    refine ⟨x, fun h1 => hδ (Subtype.ext ?_)⟩
    rw [← hx, h1]
    rfl
  have hker : φb.ker ≤ Subgroup.center _ :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hne
  have hcen : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≤ φb.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have h1 := eq_one_of_central ⟨φb z, hmemD z⟩ fun d => by
      obtain ⟨x, hx⟩ := hontoD d.1 d.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hx, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    exact congrArg Subtype.val h1
  have hkerZ : φb.ker = Subgroup.center _ := le_antisymm hker hcen
  have hS : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    H13.A5.sqtkGroup_of_surjective_quasisimple (h.sqtk.mono h.L_le) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) hq
  have hLO : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 M → l ∈ CFSG.pCore 2 ↥L := by
    intro l hlO
    have hN : ((pCoreOf 2 M).subgroupOf L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf M (h.L_le g.2)) _).mp hn
    have hp : IsPGroup 2 ↥((pCoreOf 2 M).subgroupOf L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).comap_of_injective L.subtype
        L.subtype_injective
    exact CFSG.LieType.BorelTits.le_pCore 2 hN hp (Subgroup.mem_subgroupOf.mpr hlO)
  have hodd : Odd (Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) := by
    rw [Nat.odd_iff]
    by_contra h2
    have hdvd : 2 ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Nat.dvd_of_mod_eq_zero (by omega)
    have : Fintype ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    obtain ⟨l, hlz⟩ := QuotientGroup.mk_surjective (z : ↥L ⧸ CFSG.pCore 2 ↥L)
    have hz2 : (z : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 = 1 := by
      have h1 : z ^ orderOf z = 1 := pow_orderOf_eq_one z
      rw [hz] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hl2 : l ^ 2 ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hlz, hz2]
    have hφl : φL l = 1 := by
      have := hcen z.2
      rw [MonoidHom.mem_ker, ← hlz, hφb] at this
      exact this
    obtain ⟨k, hk⟩ := isPGroup_pCore_two L ⟨l ^ 2, hl2⟩
    have hl2e : ∃ e : ℕ, ((Subgroup.inclusion h.L_le l : ↥M) : G) ^ 2 ^ e = 1 := by
      refine ⟨k + 1, ?_⟩
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      rw [Subgroup.coe_inclusion, pow_succ', pow_mul]
      exact this
    have hlO := hR.mem_pCoreOf hl2e hφl
    have hlP := hLO l hlO
    have : (z : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [← hlz, QuotientGroup.eq_one_iff]
      exact hlP
    have hz1 : z = 1 := Subtype.ext this
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hpsu : StatedClassicalModel ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) .PSU 3 3 1 := by
    let φc : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(g2Derived (ZMod 2)) := φb.codRestrict _ hmemD
    have hs : Function.Surjective φc := by
      intro δ
      obtain ⟨x, hx⟩ := hontoD δ.1 δ.2
      exact ⟨x, Subtype.ext hx⟩
    have hk : φc.ker = Subgroup.center _ := by
      rw [← hkerZ]
      ext x
      simp only [MonoidHom.mem_ker]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    let e : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φc hs)).trans
        (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _))
    exact SmithC27.isPSU_of_equiv_g2Derived (Nat.card_zmod 2) e
  have hZ := B42Dispatch.center_eq_bot_of_psu_three_three hS hq hodd hpsu
  have hl' : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ φb.ker := hl
  rw [hkerZ, hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hl'
  exact pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
    (mem_pCoreOf_of_mem_pCore_two hl')

omit [Finite G] in
theorem relIndex_sup_of_le_normalizer'' {H K : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  set P := Subgroup.normalizer (K : Set G)
  have hK : K ≤ P := Subgroup.le_normalizer
  have : (K.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  rw [← Subgroup.relIndex_subgroupOf (sup_le hH hK), ← Subgroup.relIndex_subgroupOf hH,
    Subgroup.subgroupOf_sup hH hK, Subgroup.relIndex_sup_right]

theorem mem_pCoreOf_of_eq_one
    (hR : G2Rep h f φ) (m : ↥M) (hm : φ m = 1) : (m : G) ∈ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ : Subgroup G := φ.ker.map M.subtype with hN₀def
  have hN₀M : N₀ ≤ M := Subgroup.map_subtype_le _
  have hNL : N₀ ⊓ L ≤ pCoreOf 2 M := by
    rintro x ⟨⟨y, hy, rfl⟩, hxL⟩
    refine hR.mem_pCoreOf_of_mem_L ⟨y, hxL⟩ ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
    have e : Subgroup.inclusion h.L_le ⟨(y : G), hxL⟩ = y := Subtype.ext rfl
    rw [e]
    exact hy
  have hLn : M ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer
  have h1 : L.relIndex (N₀ ⊔ L) = L.relIndex N₀ := relIndex_sup_of_le_normalizer'' (hN₀M.trans hLn)
  have h2 : L.relIndex (T ⊔ L) = L.relIndex T := relIndex_sup_of_le_normalizer'' (h.le.trans hLn)
  have hTL : T ⊔ L = M := by rw [sup_comm, ← h.eq_sup]
  rw [hTL] at h2
  have h3 : L.relIndex (N₀ ⊔ L) ∣ L.relIndex M :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex L (N₀ ⊔ L) M le_sup_right (sup_le hN₀M h.L_le))
  have h4 : L.relIndex T ∣ Nat.card T := Subgroup.index_dvd_card (L.subgroupOf T)
  obtain ⟨n, hn⟩ := h.isPGroup.exists_card_eq
  have h5 : L.relIndex N₀ ∣ 2 ^ n := by
    rw [← h1, ← hn]
    exact h3.trans (h2 ▸ h4)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h5
  have hp1 : IsPGroup 2 ↥(N₀ ⊓ L) := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hNL
  have hp2 : IsPGroup 2 ↥(L.subgroupOf N₀) := by
    intro g
    obtain ⟨k, hk⟩ := hp1 ⟨((g : ↥N₀) : G), ⟨(g : ↥N₀).2, Subgroup.mem_subgroupOf.mp g.2⟩⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a, ha⟩ := hp2.exists_card_eq
  have hcard : Nat.card ↥N₀ = 2 ^ (a + j) := by
    rw [← Subgroup.card_mul_index (L.subgroupOf N₀), ha, pow_add]
    congr 1
  have hN₀2 : IsPGroup 2 ↥N₀ := IsPGroup.of_card hcard
  have hmN : (m : G) ∈ N₀ := ⟨m, hm, rfl⟩
  obtain ⟨k, hk⟩ := hN₀2 ⟨m, hmN⟩
  exact hR.mem_pCoreOf ⟨k, by simpa using congrArg Subtype.val hk⟩ hm

theorem le_of_le_map
    (hR : G2Rep h f φ) {P : Subgroup G} (hQP : pCoreOf 2 M ≤ P)
    (hD : g2Derived (ZMod 2) ≤ (P.subgroupOf M).map φ) : L ≤ P := by
  intro l hl
  obtain ⟨p, hp, hpl⟩ := hD (hR.L_le ⟨l, h.L_le hl⟩ hl)
  have h1 : φ (p⁻¹ * ⟨l, h.L_le hl⟩) = 1 := by rw [map_mul, map_inv, hpl, inv_mul_cancel]
  have hq := hR.mem_pCoreOf_of_eq_one _ h1
  have e : l = (p : G) * ((p⁻¹ * ⟨l, h.L_le hl⟩ : ↥M) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact P.mul_mem (Subgroup.mem_subgroupOf.mp hp) (hQP hq)

end G2Rep

end CFSG.Quasithin.MS93.S38G
