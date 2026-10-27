module

public import CFSG.Quasithin.Recognition.St84.Sp44Frame
public import CFSG.Quasithin.Recognition.Stroth.BenderFrame
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSAA6
public import CFSG.ClassicalInvolution.LBalance.Glauberman.CoprimeAction
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement IsMulCommutative Pointwise

variable {G : Type} [Group G]

namespace Sp44

theorem le_normalizer_pCoreOf_of_le_normalizer {L P : Subgroup G}
    (h : P ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
  h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem inf_dsCentMod [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    dsCentMod P L (pCoreOf 2 L) ⊓ L = pCoreOf 2 L := by
  have hPQ := le_normalizer_pCoreOf_of_le_normalizer h.norm
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.mp hx
    exact dsa6_K_inf h.quot inf_le_left hxL (dsa6_mem_K.mp hxC).2.2
  · exact le_inf (dsa6_le_K h.le ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.le) hPQ)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)

theorem le_normalizer_dsCentMod [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    L ≤ Subgroup.normalizer (dsCentMod P L (pCoreOf 2 L) : Set G) := by
  have hPQ := le_normalizer_pCoreOf_of_le_normalizer h.norm
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact dsa6_K_conj h.norm hPQ (h.le hl) hx
  · intro hx
    have h1 := dsa6_K_conj h.norm hPQ (h.le (L.inv_mem hl)) hx
    simpa [mul_assoc] using h1

theorem card_vertex [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    Nat.card ↥L = 3840 := by
  have hquot60 : Nat.card (oTwoQuot ↥L) = 60 := by
    have h1 := CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) h.quot
    norm_num at h1 ⊢
    exact h1
  have hpCorecard : Nat.card (pCore 2 ↥L) = Nat.card (pCoreOf 2 L) := by
    rw [CFSG.Open.pCoreOf]
    exact (Subgroup.card_map_of_injective L.subtype_injective).symm
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  rw [hquot60, hpCorecard, h.card] at h1
  norm_num at h1 ⊢
  omega

theorem card_parabolic [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    Nat.card ↥P = 11520 := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := P)
  rw [inf_eq_left.mpr h.le, h.idx, card_vertex h] at h1
  norm_num at h1 ⊢
  omega

theorem ne_dsCentMod [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    dsCentMod P L (pCoreOf 2 L) ≠ pCoreOf 2 L := by
  classical
  intro hCeq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  set C := dsCentMod P L Q with hCdef
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf_of_le_normalizer h.norm
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h.quot
  let ρ : ↥P →* MulAut (oTwoQuot ↥L) :=
    (CFSG.Quasithin.Stroth.oTwoQuotConj L).comp (Subgroup.inclusion h.norm)
  have hcomm_iff : ∀ p : ↥P, ∀ l ∈ L,
      (p : G) * l⁻¹ * (p : G)⁻¹ * l ∈ Q ↔ ⁅(p : G), l⁆ ∈ Q := by
    intro p l hl
    have hlN : l⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hl)
    have hA : (p : G) * l⁻¹ * (p : G)⁻¹ * l = l⁻¹ * ⁅(p : G), l⁆⁻¹ * l := by
      simp only [commutatorElement_def]
      group
    rw [hA]
    have h1 := (Subgroup.mem_normalizer_iff.mp hlN ⁅(p : G), l⁆⁻¹).symm.trans
      (Subgroup.inv_mem_iff (H := Q))
    simpa using h1
  have hρker : ρ.ker = C.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show CFSG.Quasithin.Stroth.oTwoQuotConj L ⟨(p : G), h.norm p.2⟩ = 1 ↔ (p : G) ∈ C
    rw [CFSG.Quasithin.Stroth.oTwoQuotConj_eq_one_iff, dsa6_mem_K]
    constructor
    · intro hh
      exact ⟨p.2, hPQ p.2, fun l hl => (hcomm_iff p l hl).mp (hh l hl)⟩
    · rintro ⟨-, -, hh⟩ l hl
      exact (hcomm_iff p l hl).mpr (hh l hl)
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hcardAut : Nat.card (MulAut (oTwoQuot ↥L)) = 120 := by
    have h1 : Nat.card (MulAut (oTwoQuot ↥L)) =
        Nat.card (MulAut (alternatingGroup (Fin 5))) :=
      Nat.card_congr
        ⟨fun f => e.symm.trans (f.trans e), fun g => e.trans (g.trans e.symm),
          by intro f; ext x; simp [MulEquiv.trans_apply],
          by intro g; ext x; simp [MulEquiv.trans_apply]⟩
    rw [h1]
    have hbij :=
      CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num)
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact hcardPerm
  have hkerCard : Nat.card ρ.ker = 64 := by
    have hsub : Q ≤ P := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.le
    have h1 : ρ.ker = Q.subgroupOf P := by rw [hρker, hCeq]
    rw [h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv).trans h.card
  have hfr := Subgroup.card_ker_mul_card_range ρ
  rw [hkerCard, card_parabolic h] at hfr
  have hle : Nat.card ρ.range ≤ 120 := by
    rw [← hcardAut]
    exact Subgroup.card_le_card_group (H := ρ.range)
  omega

theorem sup_dsCentMod_eq [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    dsCentMod P L (pCoreOf 2 L) ⊔ L = P := by
  set Q := pCoreOf 2 L
  set C := dsCentMod P L Q
  have hCne : C ≠ Q := ne_dsCentMod h
  have hnotle : ¬ C ≤ L := by
    intro hle
    exact hCne ((inf_eq_left.mpr hle).symm.trans (inf_dsCentMod h))
  have h1 : C ⊔ L ≤ P := sup_le (fun x hx => (dsa6_mem_K.mp hx).1) h.le
  have h2 : L ≤ C ⊔ L := le_sup_right
  have h3 : L.relIndex P = L.relIndex (C ⊔ L) * (C ⊔ L).relIndex P :=
    (Subgroup.relIndex_mul_relIndex L (C ⊔ L) P h2 h1).symm
  rw [h.idx] at h3
  have hne1 : L.relIndex (C ⊔ L) ≠ 1 := by
    intro hh
    exact hnotle (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hh))
  have hdvd : L.relIndex (C ⊔ L) ∣ 3 := ⟨(C ⊔ L).relIndex P, h3⟩
  have h4 : L.relIndex (C ⊔ L) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
    · exact absurd h' hne1
    · exact h'
  have h5 : (C ⊔ L).relIndex P = 1 := by
    rw [h4] at h3
    omega
  exact le_antisymm h1 (Subgroup.relIndex_eq_one.mp h5)

theorem exists_order_three [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    ∃ τ ∈ dsCentMod P L (pCoreOf 2 L), orderOf τ = 3 ∧ τ ∉ L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  set C := dsCentMod P L Q with hCdef
  have hsup : C ⊔ L = P := sup_dsCentMod_eq h
  have hinf : C ⊓ L = Q := inf_dsCentMod h
  have hCcard : Nat.card C = 192 := by
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := L) (K := C) (le_normalizer_dsCentMod h)
    rw [sup_comm, hsup, inf_comm, hinf, card_parabolic h, card_vertex h, h.card] at h1
    norm_num at h1 ⊢
    omega
  have h3dvd : 3 ∣ Nat.card C := by rw [hCcard]; norm_num
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hx3
  · intro hxL
    have hxQ : (x : G) ∈ Q := by
      have hmem : (x : G) ∈ C ⊓ L := Subgroup.mem_inf.mpr ⟨x.2, hxL⟩
      rwa [hinf] at hmem
    have hdvd : orderOf (x : G) ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hxQ
    rw [Subgroup.orderOf_coe, hx3, h.card] at hdvd
    norm_num at hdvd

theorem centralizer_pCoreOf_eq_bot [Finite G]
    {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') {τ : G}
    (hτC : τ ∈ dsCentMod P L (pCoreOf 2 L)) (hτ3 : orderOf τ = 3) :
    pCoreOf 2 L ⊓ Subgroup.centralizer ({τ} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hQcomm : IsMulCommutative ↥(pCoreOf 2 L) := h.elem.1
  set Q := pCoreOf 2 L with hQdef
  have hQleL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf_of_le_normalizer h.norm
  have hτP : τ ∈ P := (dsa6_mem_K.mp hτC).1
  have hτN : τ ∈ Subgroup.normalizer (Q : Set G) := hPQ hτP
  have hQn : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  obtain ⟨α, β, hframe⟩ :=
    natFrame_of_natSec h.quot h.elem h.center_le h.relIndex_center h.nat
  let φ : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨τ, hτN⟩
  have hφapp : ∀ a : ↥Q, ((φ a : ↥Q) : G) = τ * (a : G) * τ⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨τ, hτN⟩ a
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨τ, hτN⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      show τ ^ 3 = 1
      rw [← hτ3]
      exact pow_orderOf_eq_one τ
    calc φ ^ 3 = Subgroup.normalizerMonoidHom Q
          ((⟨τ, hτN⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ 3) := by rw [map_pow]
      _ = 1 := by rw [h1, map_one]
  have hcop : Nat.Coprime 3 (Nat.card ↥Q) := by
    rw [h.card]
    norm_num
  have hsup :=
    CFSG.ClassicalInvolution.GlaubermanAut.fixedSubgroup_sup_commutatorSubgroup (φ := φ) hφ3 hcop
  have hinf :=
    CFSG.ClassicalInvolution.GlaubermanAut.fixedSubgroup_inf_commutatorSubgroup (φ := φ) hφ3 hcop
  let Cf : Subgroup G :=
    (CFSG.ClassicalInvolution.GlaubermanAut.fixedSubgroup φ).map Q.subtype
  let Cc : Subgroup G :=
    (CFSG.ClassicalInvolution.GlaubermanAut.commutatorSubgroup φ).map Q.subtype
  have hCfQ : Cf ≤ Q := Subgroup.map_subtype_le _
  have hCcQ : Cc ≤ Q := Subgroup.map_subtype_le _
  have hCf_mem : ∀ y : G, y ∈ Cf ↔ y ∈ Q ∧ τ * y * τ⁻¹ = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      have h1 : φ a = a :=
        (CFSG.ClassicalInvolution.GlaubermanAut.mem_fixedSubgroup (φ := φ)).mp ha
      refine ⟨a.2, ?_⟩
      show τ * (a : G) * τ⁻¹ = (a : G)
      rw [← hφapp a]
      exact congrArg Subtype.val h1
    · rintro ⟨hyQ, hyfix⟩
      refine Subgroup.mem_map.mpr ⟨⟨y, hyQ⟩, ?_, rfl⟩
      rw [CFSG.ClassicalInvolution.GlaubermanAut.mem_fixedSubgroup (φ := φ)]
      apply Subtype.ext
      rw [hφapp]
      exact hyfix
  have hCc_mem : ∀ y : G, y ∈ Cc ↔ y ∈ Q ∧ ∃ a ∈ Q, y = a * (τ * a * τ⁻¹)⁻¹ := by
    intro y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨b, hb⟩ :=
        (CFSG.ClassicalInvolution.GlaubermanAut.mem_commutatorSubgroup (φ := φ)).mp ha
      refine ⟨a.2, b, b.2, ?_⟩
      rw [← hb]
      show (((b * (φ b)⁻¹ : ↥Q)) : G) = (b : G) * (τ * (b : G) * τ⁻¹)⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
    · rintro ⟨hyQ, b, hbQ, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨b, hbQ⟩ * (φ ⟨b, hbQ⟩)⁻¹, ?_, ?_⟩
      · rw [CFSG.ClassicalInvolution.GlaubermanAut.mem_commutatorSubgroup (φ := φ)]
        exact ⟨⟨b, hbQ⟩, rfl⟩
      · show (((⟨b, hbQ⟩ * (φ ⟨b, hbQ⟩)⁻¹ : ↥Q)) : G) = b * (τ * b * τ⁻¹)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
  have htopmap : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hy
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hsupQ : Cf ⊔ Cc = Q := by
    have h1 : Cf ⊔ Cc =
        ((CFSG.ClassicalInvolution.GlaubermanAut.fixedSubgroup φ) ⊔
          (CFSG.ClassicalInvolution.GlaubermanAut.commutatorSubgroup φ)).map Q.subtype := by
      rw [Subgroup.map_sup]
    rw [h1, hsup, htopmap]
  have hinfQ : Cf ⊓ Cc = ⊥ := by
    have h1 : Cf ⊓ Cc =
        ((CFSG.ClassicalInvolution.GlaubermanAut.fixedSubgroup φ) ⊓
          (CFSG.ClassicalInvolution.GlaubermanAut.commutatorSubgroup φ)).map Q.subtype := by
      rw [Subgroup.map_inf_eq _ _ _ Q.subtype_injective]
    rw [h1, hinf, Subgroup.map_bot]
  have hconjτ : ∀ g ∈ L, g * τ * g⁻¹ = τ * ⁅τ⁻¹, g⁆ := by
    intro g hg
    have h2 : τ⁻¹ * g * τ * g⁻¹ = ⁅τ⁻¹, g⁆ := by
      simp only [commutatorElement_def, inv_inv]
    calc g * τ * g⁻¹ = τ * (τ⁻¹ * g * τ * g⁻¹) := by group
      _ = τ * ⁅τ⁻¹, g⁆ := by rw [h2]
  have hconjτinv : ∀ g ∈ L, g * τ⁻¹ * g⁻¹ = (τ * ⁅τ⁻¹, g⁆)⁻¹ := by
    intro g hg
    have h := congrArg Inv.inv (hconjτ g hg)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hq1Q : ∀ g ∈ L, ⁅τ⁻¹, g⁆ ∈ Q := fun g hg =>
    (dsa6_mem_K.mp ((dsCentMod P L Q).inv_mem hτC)).2.2 g hg
  have hconjτ' : ∀ g ∈ L, τ * g * τ⁻¹ = ⁅τ, g⁆ * g := by
    intro g hg
    simp only [commutatorElement_def]
    group
  have hconjτ'inv : ∀ g ∈ L, τ * g⁻¹ * τ⁻¹ = g⁻¹ * ⁅τ, g⁆⁻¹ := by
    intro g hg
    have h := congrArg Inv.inv (hconjτ' g hg)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hqQ : ∀ g ∈ L, ⁅τ, g⁆ ∈ Q := fun g hg => (dsa6_mem_K.mp hτC).2.2 g hg
  have hCf_step : ∀ g ∈ L, ∀ y ∈ Cf, g * y * g⁻¹ ∈ Cf := by
    intro g hg y hy
    obtain ⟨hyQ, hyfix⟩ := (hCf_mem y).mp hy
    have hgyQ : g * y * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hg) y).mp hyQ
    refine (hCf_mem _).mpr ⟨hgyQ, ?_⟩
    have hcomm : ⁅τ, g⁆ * (g * y * g⁻¹) = (g * y * g⁻¹) * ⁅τ, g⁆ :=
      congrArg Subtype.val (hQcomm.is_comm.comm ⟨⁅τ, g⁆, hqQ g hg⟩ ⟨g * y * g⁻¹, hgyQ⟩)
    calc τ * (g * y * g⁻¹) * τ⁻¹
        = (τ * g * τ⁻¹) * (τ * y * τ⁻¹) * (τ * g⁻¹ * τ⁻¹) := by group
      _ = (⁅τ, g⁆ * g) * y * (g⁻¹ * ⁅τ, g⁆⁻¹) := by
            rw [hconjτ' g hg, hconjτ'inv g hg, hyfix]
      _ = ⁅τ, g⁆ * (g * y * g⁻¹) * ⁅τ, g⁆⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [hcomm]; group
  have hCf_step' : ∀ g ∈ L, ∀ y : G, g * y * g⁻¹ ∈ Cf → y ∈ Cf := by
    intro g hg y hy
    obtain ⟨hyQ', hyfix⟩ := (hCf_mem (g * y * g⁻¹)).mp hy
    have hgN : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem (hQn hg)
    have hyQ : y ∈ Q := by
      have h' := (Subgroup.mem_normalizer_iff.mp hgN (g * y * g⁻¹)).mp hyQ'
      simpa [mul_assoc] using h'
    refine (hCf_mem y).mpr ⟨hyQ, ?_⟩
    have hcomm : ⁅τ, g⁆⁻¹ * (g * y * g⁻¹) = (g * y * g⁻¹) * ⁅τ, g⁆⁻¹ :=
      congrArg Subtype.val
        (hQcomm.is_comm.comm ⟨⁅τ, g⁆⁻¹, Q.inv_mem (hqQ g hg)⟩ ⟨g * y * g⁻¹, hyQ'⟩)
    have hcancel : ⁅τ, g⁆⁻¹ * (g * y * g⁻¹) * ⁅τ, g⁆ = g * y * g⁻¹ := by
      rw [hcomm]; group
    calc τ * y * τ⁻¹
        = (τ * g⁻¹ * τ⁻¹) * (τ * (g * y * g⁻¹) * τ⁻¹) * (τ * g * τ⁻¹) := by group
      _ = (g⁻¹ * ⁅τ, g⁆⁻¹) * (g * y * g⁻¹) * (⁅τ, g⁆ * g) := by
            rw [hconjτ'inv g hg, hyfix, hconjτ' g hg]
      _ = g⁻¹ * (⁅τ, g⁆⁻¹ * (g * y * g⁻¹) * ⁅τ, g⁆) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hcancel]
      _ = y := by group
  have hCf_inv : L ≤ Subgroup.normalizer (Cf : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hCf_step l hl y, hCf_step' l hl y⟩
  have hstep : ∀ g ∈ L, ∀ (a : G), a ∈ Q →
      g * (τ * a * τ⁻¹) * g⁻¹ = τ * (g * a * g⁻¹) * τ⁻¹ := by
    intro g hg a ha
    have hgaQ : g * a * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hg) a).mp ha
    have hcomm : ⁅τ⁻¹, g⁆ * (g * a * g⁻¹) = (g * a * g⁻¹) * ⁅τ⁻¹, g⁆ :=
      congrArg Subtype.val (hQcomm.is_comm.comm ⟨⁅τ⁻¹, g⁆, hq1Q g hg⟩ ⟨g * a * g⁻¹, hgaQ⟩)
    calc g * (τ * a * τ⁻¹) * g⁻¹
        = (g * τ * g⁻¹) * (g * a * g⁻¹) * (g * τ⁻¹ * g⁻¹) := by group
      _ = (τ * ⁅τ⁻¹, g⁆) * (g * a * g⁻¹) * (τ * ⁅τ⁻¹, g⁆)⁻¹ := by
            rw [hconjτ g hg, hconjτinv g hg]
      _ = τ * (⁅τ⁻¹, g⁆ * (g * a * g⁻¹) * ⁅τ⁻¹, g⁆⁻¹) * τ⁻¹ := by group
      _ = τ * (g * a * g⁻¹) * τ⁻¹ := by rw [hcomm]; group
  have hCc_step : ∀ g ∈ L, ∀ y ∈ Cc, g * y * g⁻¹ ∈ Cc := by
    intro g hg y hy
    obtain ⟨hyQ, a, haQ, rfl⟩ := (hCc_mem y).mp hy
    have h1 : g * (a * (τ * a * τ⁻¹)⁻¹) * g⁻¹ =
        (g * a * g⁻¹) * (τ * (g * a * g⁻¹) * τ⁻¹)⁻¹ := by
      calc g * (a * (τ * a * τ⁻¹)⁻¹) * g⁻¹
          = (g * a * g⁻¹) * (g * (τ * a * τ⁻¹) * g⁻¹)⁻¹ := by group
        _ = (g * a * g⁻¹) * (τ * (g * a * g⁻¹) * τ⁻¹)⁻¹ := by rw [hstep g hg a haQ]
    have hgaQ : g * a * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hg) a).mp haQ
    have hzQ : τ * (g * a * g⁻¹) * τ⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hτN _).mp hgaQ
    refine (hCc_mem _).mpr ⟨?_, g * a * g⁻¹, hgaQ, h1⟩
    rw [h1]
    exact Q.mul_mem hgaQ (Q.inv_mem hzQ)
  have hCc_inv : L ≤ Subgroup.normalizer (Cc : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hCc_step l hl y
    · intro hy
      have h := hCc_step l⁻¹ (L.inv_mem hl) (l * y * l⁻¹) hy
      simpa [mul_assoc] using h
  have hCf_le : Cf ≤ centerOf L ∨ Cf = Q :=
    invariant_le_center_or_eq hframe h.indec hCfQ hCf_inv
  have hCc_le : Cc ≤ centerOf L ∨ Cc = Q :=
    invariant_le_center_or_eq hframe h.indec hCcQ hCc_inv
  have hCf_ne : Cf ≠ Q := by
    intro hCfQ
    have hcentQ : ∀ q ∈ Q, τ * q * τ⁻¹ = q := by
      intro q hq
      exact ((hCf_mem q).mp (by rw [hCfQ]; exact hq)).2
    have hτQ : τ ∈ Q := by
      have hmem : τ ∈ P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hτP, ?_⟩
        rw [h.oTwo, Subgroup.mem_centralizer_iff]
        intro q hq
        have h1 := hcentQ q hq
        calc q * τ = (τ * q * τ⁻¹) * τ := by rw [h1]
          _ = τ * q := by group
      have h2 := h.charTwo hmem
      rwa [h.oTwo] at h2
    have hdvd : orderOf τ ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hτQ
    rw [hτ3, h.card] at hdvd
    norm_num at hdvd
  have hCf_le_Z : Cf ≤ centerOf L := hCf_le.resolve_right hCf_ne
  have hCc_eq : Cc = Q := by
    rcases hCc_le with hh | hh
    · exfalso
      have hsub : Q ≤ centerOf L := by
        rw [← hsupQ]
        exact sup_le hCf_le_Z hh
      have hcard : Nat.card Q ≤ Nat.card ↥(centerOf L) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hsub)
      rw [h.card, h.center] at hcard
      norm_num at hcard
    · exact hh
  have hCf_bot : Cf = ⊥ := by
    rw [← hinfQ, hCc_eq, inf_eq_left.mpr hCfQ]
  rw [← hCf_bot]
  ext y
  rw [hCf_mem]
  constructor
  · rintro ⟨hyQ, hyC⟩
    refine ⟨hyQ, ?_⟩
    have h : y * τ = τ * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    calc τ * y * τ⁻¹ = (y * τ) * τ⁻¹ := by rw [h]
      _ = y := by group
  · rintro ⟨hyQ, hyfix⟩
    refine ⟨hyQ, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc y * τ = (τ * y * τ⁻¹) * τ := by rw [hyfix]
        _ = τ * y := by group)

theorem exists_pCoreOf_mul_centralizer [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') {τ : G}
    (hτC : τ ∈ dsCentMod P L (pCoreOf 2 L)) (hτ3 : orderOf τ = 3)
    (hff : ∀ q ∈ pCoreOf 2 L, τ * q * τ⁻¹ = q → q = 1) :
    ∀ x ∈ L, ∃ q ∈ pCoreOf 2 L, ∃ k ∈ L ⊓ Subgroup.centralizer ({τ} : Set G), q * k = x := by
  classical
  haveI hQcomm : IsMulCommutative ↥(pCoreOf 2 L) := h.elem.1
  set Q := pCoreOf 2 L with hQdef
  have hQleL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf_of_le_normalizer h.norm
  have hτP : τ ∈ P := (dsa6_mem_K.mp hτC).1
  have hτN : τ ∈ Subgroup.normalizer (Q : Set G) := hPQ hτP
  let φ : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨τ, hτN⟩
  have hφapp : ∀ a : ↥Q, ((φ a : ↥Q) : G) = τ * (a : G) * τ⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨τ, hτN⟩ a
  let ψ : ↥Q →* ↥Q :=
    { toFun := fun a => a⁻¹ * φ a
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hψker : ∀ a : ↥Q, ψ a = 1 ↔ a = 1 := by
    intro a
    constructor
    · intro hh
      have h1 : φ a = a := by
        have h' := congrArg (fun x => a * x) hh
        simpa [ψ, mul_assoc] using h'
      apply Subtype.ext
      have h2 : τ * (a : G) * τ⁻¹ = (a : G) := by
        rw [← hφapp a]
        exact congrArg Subtype.val h1
      exact hff a a.2 h2
    · intro hh
      rw [hh, map_one]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    exact fun a ha => (hψker a).mp ha
  have hψsurj : Function.Surjective ψ := Finite.surjective_of_injective hψinj
  intro x hxL
  have hq1Q : ⁅τ⁻¹, x⁆ ∈ Q :=
    (dsa6_mem_K.mp ((dsCentMod P L Q).inv_mem hτC)).2.2 x hxL
  have hq1' : τ⁻¹ * x * τ * x⁻¹ = ⁅τ⁻¹, x⁆ := by
    simp only [commutatorElement_def, inv_inv]
  have hlx : x * τ * x⁻¹ = τ * ⁅τ⁻¹, x⁆ := by
    calc x * τ * x⁻¹ = τ * (τ⁻¹ * x * τ * x⁻¹) := by group
      _ = τ * ⁅τ⁻¹, x⁆ := by rw [hq1']
  have hq2Q : τ * ⁅τ⁻¹, x⁆ * τ⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hτN ⁅τ⁻¹, x⁆).mp hq1Q
  obtain ⟨a, ha⟩ := hψsurj ⟨(τ * ⁅τ⁻¹, x⁆ * τ⁻¹)⁻¹, Q.inv_mem hq2Q⟩
  have hψa : ((ψ a : ↥Q) : G) = (τ * ⁅τ⁻¹, x⁆ * τ⁻¹)⁻¹ := by
    rw [ha]
  have hact : (a : G)⁻¹ * τ * (a : G) = ((ψ a : ↥Q) : G) * τ := by
    have h2 : ((ψ a : ↥Q) : G) = (a : G)⁻¹ * τ * (a : G) * τ⁻¹ := by
      rw [show (ψ a : ↥Q) = a⁻¹ * φ a from rfl, Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
      group
    rw [h2]
    group
  have hk : ((a : G)⁻¹ * x) * τ * ((a : G)⁻¹ * x)⁻¹ = τ := by
    have hqa : ⁅τ⁻¹, x⁆ * (a : G) = (a : G) * ⁅τ⁻¹, x⁆ :=
      congrArg Subtype.val (hQcomm.is_comm.comm ⟨⁅τ⁻¹, x⁆, hq1Q⟩ ⟨(a : G), a.2⟩)
    have hq2eq : τ * ⁅τ⁻¹, x⁆ = (τ * ⁅τ⁻¹, x⁆ * τ⁻¹) * τ := by group
    calc ((a : G)⁻¹ * x) * τ * ((a : G)⁻¹ * x)⁻¹
        = (a : G)⁻¹ * (x * τ * x⁻¹) * (a : G) := by group
      _ = (a : G)⁻¹ * (τ * ⁅τ⁻¹, x⁆) * (a : G) := by rw [hlx]
      _ = (a : G)⁻¹ * τ * (a : G) * ⁅τ⁻¹, x⁆ := by
            rw [show (a : G)⁻¹ * (τ * ⁅τ⁻¹, x⁆) * (a : G) =
              (a : G)⁻¹ * τ * (⁅τ⁻¹, x⁆ * (a : G)) from by group, hqa]
            group
      _ = ((ψ a : ↥Q) : G) * τ * ⁅τ⁻¹, x⁆ := by rw [hact]
      _ = ((ψ a : ↥Q) : G) * (τ * ⁅τ⁻¹, x⁆) := by group
      _ = ((ψ a : ↥Q) : G) * ((τ * ⁅τ⁻¹, x⁆ * τ⁻¹) * τ) := by group
      _ = τ := by
            rw [hψa]
            group
  refine ⟨(a : G), a.2, (a : G)⁻¹ * x, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (hQleL a.2)) hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((a : G)⁻¹ * x) * τ
        = (((a : G)⁻¹ * x) * τ * ((a : G)⁻¹ * x)⁻¹) * ((a : G)⁻¹ * x) := by group
      _ = τ * ((a : G)⁻¹ * x) := by rw [hk]
  · group

theorem Sp44Side.exists_torus [Finite G]
    {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    ∃ τ ∈ P, orderOf τ = 3 ∧ τ ∉ L ∧
      (∀ q ∈ pCoreOf 2 L, τ * q * τ⁻¹ ∈ pCoreOf 2 L) ∧
      (∀ q ∈ pCoreOf 2 L, τ * q * τ⁻¹ = q → q = 1) ∧
      (L ⊓ Subgroup.centralizer {τ}) ⊓ pCoreOf 2 L = ⊥ ∧
      (∀ x ∈ L, ∃ q ∈ pCoreOf 2 L, ∃ k ∈ L ⊓ Subgroup.centralizer {τ}, q * k = x) ∧
      (∀ p ∈ P, ∃ x ∈ L, ∃ i : ℕ, i < 3 ∧ x * τ ^ i = p) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  obtain ⟨τ, hτC, hτ3, hτL⟩ := exists_order_three h
  have hτP : τ ∈ P := (dsa6_mem_K.mp hτC).1
  have hτN : τ ∈ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_pCoreOf_of_le_normalizer h.norm hτP
  have hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q := by
    intro q hq
    exact (Subgroup.mem_normalizer_iff.mp hτN q).mp hq
  have hQinf : Q ⊓ Subgroup.centralizer ({τ} : Set G) = ⊥ :=
    centralizer_pCoreOf_eq_bot h hτC hτ3
  have hff : ∀ q ∈ Q, τ * q * τ⁻¹ = q → q = 1 := by
    intro q hq hfix
    have hmem : q ∈ Q ⊓ Subgroup.centralizer ({τ} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hq, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc q * τ = (τ * q * τ⁻¹) * τ := by rw [hfix]
          _ = τ * q := by group)
    rw [hQinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hdec := exists_pCoreOf_mul_centralizer h hτC hτ3 hff
  have hQleL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hzpN : Subgroup.zpowers τ ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (h.norm hτP)
  have hzpleP : Subgroup.zpowers τ ≤ P := Subgroup.zpowers_le.mpr hτP
  have hzpcard : Nat.card ↥(Subgroup.zpowers τ) = 3 := by
    rw [Nat.card_zpowers]
    exact hτ3
  have hinfzp : Subgroup.zpowers τ ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyz, hyL⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyz
    rw [Subgroup.mem_bot]
    have hz3 : τ ^ k = τ ^ (k % 3) := by
      rw [← zpow_mod_orderOf τ k, show (orderOf τ : ℤ) = 3 from by rw [hτ3]; norm_num]
    have hmem : τ ^ (k % 3) ∈ L := by rw [← hz3]; exact hyL
    have h1 : k % 3 ≠ 1 := by
      intro h
      apply hτL
      have h' : τ ^ (k % 3) = τ := by rw [h]; simp
      rwa [h'] at hmem
    have h2 : k % 3 ≠ 2 := by
      intro h
      apply hτL
      have h' : τ ^ (k % 3) = τ ^ (2 : ℤ) := by rw [h]
      rw [h'] at hmem
      have h3 : (τ ^ (2 : ℤ)) ^ 2 ∈ L := L.pow_mem hmem 2
      have h4 : (τ ^ (2 : ℤ)) ^ 2 = τ := by
        have h0 : τ ^ 3 = 1 := by rw [← hτ3]; exact pow_orderOf_eq_one τ
        have h2' : τ ^ (2 : ℤ) = τ ^ 2 := by simp
        rw [h2', ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, pow_one, h0, one_mul]
      rwa [h4] at h3
    have hkm : k % 3 = 0 := by omega
    rw [hz3, hkm]
    simp
  have hPL : P = L ⊔ Subgroup.zpowers τ := by
    have hle : L ⊔ Subgroup.zpowers τ ≤ P := sup_le h.le hzpleP
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers τ) (K := L) hzpN
    rw [hinfzp, hzpcard, card_vertex h, Subgroup.card_bot] at h1
    have hcard : Nat.card ↥(L ⊔ Subgroup.zpowers τ) = Nat.card ↥P := by
      rw [card_parabolic h]
      have h1' : Nat.card ↥(L ⊔ Subgroup.zpowers τ) = 11520 := by
        rw [sup_comm]
        simpa using h1
      rw [h1']
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm
  have hmem_le : ∀ p ∈ P, ∃ x ∈ L, ∃ i : ℕ, i < 3 ∧ x * τ ^ i = p := by
    intro p hp
    have hp' : p ∈ (↑(L ⊔ Subgroup.zpowers τ) : Set G) := by rw [← hPL]; exact hp
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L (Subgroup.zpowers τ) hzpN] at hp'
    rw [Set.mem_mul] at hp'
    obtain ⟨l, hlL, z, hz, hlz⟩ := hp'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hnonneg : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    set i := (k % 3).toNat with hidef
    have hik : (i : ℤ) = k % 3 := Int.toNat_of_nonneg hnonneg
    have hi3 : i < 3 := by omega
    have hτk : τ ^ k = τ ^ i := by
      rw [← zpow_mod_orderOf τ k]
      rw [show (orderOf τ : ℤ) = 3 from by rw [hτ3]; norm_num]
      rw [← hik, zpow_natCast]
    refine ⟨l, hlL, i, hi3, ?_⟩
    rw [← hτk]
    exact hlz
  have hKQ : (L ⊓ Subgroup.centralizer ({τ} : Set G)) ⊓ Q = ⊥ := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hQleL, hQinf]
  exact ⟨τ, hτP, hτ3, hτL, hτQ, hff, hKQ, hdec, hmem_le⟩

theorem Sp44Side.inf_sylow [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q')
    {τ : G} (hτP : τ ∈ P) (hτ3 : orderOf τ = 3) (hτL : τ ∉ L)
    (hff : ∀ q ∈ pCoreOf 2 L, τ * q * τ⁻¹ = q → q = 1)
    (hdec : ∀ x ∈ L, ∃ q ∈ pCoreOf 2 L,
      ∃ k ∈ L ⊓ Subgroup.centralizer ({τ} : Set G), q * k = x) :
    IsSylowTwoOf (S ⊓ (L ⊓ Subgroup.centralizer ({τ} : Set G)))
        (L ⊓ Subgroup.centralizer ({τ} : Set G)) ∧
      pCoreOf 2 L ⊓ Q' ≤ Subgroup.centralizer
        ((S ⊓ (L ⊓ Subgroup.centralizer ({τ} : Set G)) : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hQcomm : IsMulCommutative ↥(pCoreOf 2 L) := h.elem.1
  haveI hQ'comm : IsMulCommutative ↥Q' := h.other_elem.1
  set Q := pCoreOf 2 L with hQdef
  set K := L ⊓ Subgroup.centralizer ({τ} : Set G) with hKdef
  have hQleL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hKL : K ≤ L := inf_le_left
  have hQn : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQS : Q ≤ S := F7.isSylowTwoOf_pCoreOf_le h.sylL
  have hKQ : K ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyK, hyQ⟩ := Subgroup.mem_inf.mp hy
    have hyC : y ∈ Subgroup.centralizer ({τ} : Set G) := (Subgroup.mem_inf.mp hyK).2
    have hc := (Subgroup.mem_centralizer_iff.mp hyC) τ (by simp)
    rw [Subgroup.mem_bot]
    exact hff y hyQ (by
      calc τ * y * τ⁻¹ = (y * τ) * τ⁻¹ := by rw [hc]
        _ = y := by group)
  have hLQK : L = Q ⊔ K := by
    refine le_antisymm ?_ (sup_le hQleL hKL)
    intro x hx
    obtain ⟨q, hq, k, hk, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem_sup hq hk
  have hKcard : Nat.card ↥K = 60 := by
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := K) (K := Q) (hKL.trans hQn)
    rw [sup_comm, ← hLQK, hKQ, card_vertex h, h.card] at h1
    norm_num at h1 ⊢
    omega
  have hSD : S = Q ⊔ (S ⊓ K) := by
    refine le_antisymm ?_ (sup_le hQS inf_le_left)
    intro s hs
    have hs' : s ∈ (Q : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q K (hKL.trans hQn), ← hLQK]
      exact h.sylL.1 hs
    rw [Set.mem_mul] at hs'
    obtain ⟨q, hq, k, hk, rfl⟩ := hs'
    have hkS : k ∈ S := by
      have h1 : k = q⁻¹ * (q * k) := by group
      rw [h1]
      exact S.mul_mem (S.inv_mem (hQS hq)) hs
    exact Subgroup.mul_mem_sup hq (Subgroup.mem_inf.mpr ⟨hkS, hk⟩)
  have hSKcard : Nat.card ↥(S ⊓ K) = 4 := by
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := S ⊓ K) (K := Q) (inf_le_left.trans (h.sylL.1.trans hQn))
    have h2 : Q ⊓ (S ⊓ K) = ⊥ := by
      rw [← inf_assoc, inf_eq_left.mpr hQS, inf_comm, hKQ]
    rw [sup_comm, ← hSD, inf_comm, h2, h.card_S, h.card] at h1
    norm_num at h1 ⊢
    omega
  have hSKle : S ⊓ K ≤ K := inf_le_right
  have hSKp : IsPGroup 2 ↥(S ⊓ K) := by
    intro x
    obtain ⟨m, hm⟩ := h.sylP.2.1 ⟨x.1, x.2.1⟩
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  have hidx : ¬ 2 ∣ ((S ⊓ K).subgroupOf K).index := by
    have h1 := Subgroup.card_mul_index ((S ⊓ K).subgroupOf K)
    have h2 : Nat.card ↥((S ⊓ K).subgroupOf K) = Nat.card ↥(S ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ K ≤ K)).toEquiv
    rw [h2, hSKcard, hKcard] at h1
    have h3 : ((S ⊓ K).subgroupOf K).index = 15 := by omega
    rw [h3]
    norm_num
  refine ⟨⟨hSKle, hSKp, hidx⟩, ?_⟩
  have hQ'N : Q' ≤ Subgroup.normalizer (Q : Set G) :=
    h.other_le.trans (h.sylL.1.trans hQn)
  have hSQ' : Q ⊔ Q' = S := Sp44Side.sup_eq h
  have hprod : (↑(Q ⊔ Q') : Set G) = (Q : Set G) * (Q' : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q Q' hQ'N
  intro y hy
  obtain ⟨hyQ, hyQ'⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro s hs
  obtain ⟨hsS, hsK⟩ := Subgroup.mem_inf.mp hs
  have hs' : s ∈ (Q : Set G) * (Q' : Set G) := by
    rw [← hprod, hSQ']
    exact hsS
  rw [Set.mem_mul] at hs'
  obtain ⟨q, hq, q', hq', rfl⟩ := hs'
  have h1 : q' * y * q'⁻¹ = y := by
    have h := hQ'comm.is_comm.comm ⟨q', hq'⟩ ⟨y, hyQ'⟩
    have h2 : q' * y = y * q' := congrArg Subtype.val h
    calc q' * y * q'⁻¹ = (y * q') * q'⁻¹ := by rw [h2]
      _ = y := by group
  have h2 : q * y * q⁻¹ = y := by
    have h := hQcomm.is_comm.comm ⟨q, hq⟩ ⟨y, hyQ⟩
    have h3 : q * y = y * q := congrArg Subtype.val h
    calc q * y * q⁻¹ = (y * q) * q⁻¹ := by rw [h3]
      _ = y := by group
  calc (q * q') * y = q * (q' * y * q'⁻¹) * q' := by group
    _ = q * y * q' := by rw [h1]
    _ = (q * y * q⁻¹) * q * q' := by group
    _ = y * (q * q') := by rw [h2]; group

end Sp44

end CFSG.Quasithin.F112R.St84
