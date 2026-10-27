module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.ClassicalGroups.Symplectic.Simple

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem FF81Basis.inf_cenS_self (hB : FF81Basis b L B b₁ b₂ b₃) : L ⊓ CenS L = ⊥ := by
  have h := hB.hyp
  have : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1 h.model
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h0 | h0
    · exact h0
    · exfalso
      have hcomm : commutator L = ⊥ := by
        rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
        intro x _ y _
        have hx : x ∈ Subgroup.center L := by rw [h0]; exact Subgroup.mem_top x
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hx y).symm
      have htop : (⊤ : Subgroup L) = ⊥ := by
        rw [← h.quasi.1.commutator_eq_top, hcomm]
      have h1 : Nat.card L = 1 := by
        rw [← Subgroup.card_top (G := L), htop, Subgroup.card_bot]
      have hle : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L := by
        refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        rcases hx with rfl | rfl | rfl
        exacts [hB.hb₁, hB.hb₂, hB.hb₃]
      have := Subgroup.card_le_of_le hle
      rw [hB.elem.2, h1] at this
      norm_num at this
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxZ : (⟨x, hx.1⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)

theorem FF81Basis.inf_cenS_eq (hB : FF81Basis b L B b₁ b₂ b₃) :
    B ⊓ CenS L = Subgroup.zpowers b := by
  have hbB := hB.mem.1
  have hbL : b ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hy))
  have hle : Subgroup.zpowers b ≤ B ⊓ CenS L :=
    (Subgroup.zpowers_le).mpr ⟨hbB, hbL⟩
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hB₁L : B₁ ≤ L := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [hB.hb₁, hB.hb₂, hB.hb₃]
  obtain ⟨hb1, hb2, hb3⟩ := hB.mem.2
  have hB₁B : B₁ ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [hb1, hb2, hb3]
  have hinf : (B ⊓ CenS L) ⊓ B₁ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← hB.inf_cenS_self]
    exact ⟨hB₁L hx.2, hx.1.2⟩
  have hN : B ⊓ CenS L ≤ Subgroup.normalizer (B₁ : Set G) := fun g hg =>
    mem_normalizer_of_comm (comm_of_isElemAb hB.mono.1) hB₁B hg.1
  have e := card_sup_mul_card_inf (B ⊓ CenS L) B₁ hN
  rw [hinf, Subgroup.card_bot, mul_one, hB.elem.2] at e
  have hsup : Nat.card ↥((B ⊓ CenS L) ⊔ B₁) ≤ 81 := by
    have := Subgroup.card_le_of_le (sup_le (inf_le_left : B ⊓ CenS L ≤ B) hB₁B)
    rwa [hB.mono.1.2] at this
  have hcard : Nat.card ↥(B ⊓ CenS L) ≤ 3 := by omega
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hB.hyp.ord]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hb3]; exact hcard)).symm

theorem FF81Basis.mem_zpowers_of_isPGroup (hB : FF81Basis b L B b₁ b₂ b₃) {y : G}
    (hyb : y ∈ Cen b) (hyL : y ∈ CenS L) (hy : IsPGroup 3 (Subgroup.zpowers y)) :
    y ∈ Subgroup.zpowers b := by
  have hc : ∀ x ∈ L, y * x * y⁻¹ = x := fun x hx => by
    rw [(Subgroup.mem_centralizer_iff.mp hyL x hx).symm]; group
  have hyb' : y * b * y⁻¹ = b := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hyb)]; group
  have hyB : y ∈ B :=
    hB.cenSyl y (hB.mem_cenS hyb' (hc _ hB.hb₁) (hc _ hB.hb₂) (hc _ hB.hb₃)) hy
  rw [← hB.inf_cenS_eq]
  exact ⟨hyB, hyL⟩

theorem FF81Basis.cen_inf_cenS_eq (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    Cen b ⊓ CenS L = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Cen b ⊓ CenS L with hD
  have hbD : b ∈ D := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hy))⟩
  have h3 : ∀ y ∈ D, IsPGroup 3 (Subgroup.zpowers y) → y ∈ Subgroup.zpowers b := fun y hy hp =>
    hB.mem_zpowers_of_isPGroup hy.1 hy.2 hp
  have hcentral : ∀ y ∈ D, ∀ z ∈ D, IsPGroup 3 (Subgroup.zpowers y) → y * z = z * y := by
    intro y hy z hz hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h3 y hy hp)
    exact ((Commute.zpow_left
      (Subgroup.mem_centralizer_singleton_iff.mp hz.1).symm k)).eq
  obtain ⟨P⟩ : Nonempty (Sylow 3 D) := inferInstance
  have hpow : ∀ z : D, (∃ k : ℕ, z ^ (3 ^ k) = 1) → IsPGroup 3 (Subgroup.zpowers (z : G)) := by
    rintro z ⟨k, hk⟩
    exact isPGroup_zpowers_of_pow (e := k) (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
  have hPc : Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) := by
    intro g _
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hp := hpow h (by
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨h, hh⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
    exact Subtype.ext (hcentral h h.2 g g.2 hp)
  set φ := MonoidHom.transferSylow P hPc
  have hcop : Nat.Coprime 3 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hPc)
  have hker : ∀ d : D, d ∈ φ.ker ↔ Nat.Coprime 3 (orderOf d) := by
    intro d
    constructor
    · intro hd
      rw [← Subgroup.orderOf_mk (H := φ.ker) d hd]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hcop
    · intro hd
      have hpd : orderOf (φ d) ∣ orderOf d := orderOf_map_dvd φ d
      obtain ⟨k, hk⟩ := P.isPGroup' (φ d)
      have hpk : orderOf (φ d) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hc : Nat.Coprime (orderOf (φ d)) (orderOf d) :=
        (Nat.Coprime.pow_left k hd).coprime_dvd_left hpk
      exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (hc.eq_one_of_dvd hpd))
  set N : Subgroup G := φ.ker.map D.subtype with hN
  have hDn : ∀ g ∈ Cen b, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    refine ⟨?_, ?_⟩
    · exact (Cen b).mul_mem ((Cen b).mul_mem hg hd.1) ((Cen b).inv_mem hg)
    · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hgN := hB.hyp.hLN hg
      have hx' : g⁻¹ * x * g ∈ L := by
        exact (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * x * g)).mpr
          (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
      have hc := Subgroup.mem_centralizer_iff.mp hd.2 _ hx'
      calc x * (g * d * g⁻¹) = g * ((g⁻¹ * x * g) * d) * g⁻¹ := by group
        _ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
        _ = g * d * g⁻¹ * x := by group
  have hNnorm : (N.subgroupOf (Cen b)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hd, hdn⟩ := hn
    have hgd := hDn g g.2 (n : G) (hdn ▸ d.2)
    refine ⟨⟨_, hgd⟩, (hker _).mpr ?_, by simp⟩
    rw [Subgroup.orderOf_mk, show (g : G) * n * (g : G)⁻¹ = MulAut.conj (g : G) n from rfl,
      MulEquiv.orderOf_eq, ← hdn]
    have := (hker d).mp hd
    rwa [← Subgroup.orderOf_coe] at this⟩
  have hNbot : N.subgroupOf (Cen b) = ⊥ := by
    have hp : CFSG.pPrimeCore 3 ↥(Cen b) = ⊥ := by
      have := h0
      rw [Opp, CFSG.inSubgroup] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Cen b).subtype_injective).mp this
    refine (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := ↥(Cen b))).mp hp _ hNnorm ?_
    have hle : N ≤ Cen b := (Subgroup.map_subtype_le _).trans inf_le_left
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective D.subtype_injective]
    exact hcop
  have hkerbot : φ.ker = ⊥ := by
    refine eq_bot_iff.mpr fun d hd => ?_
    have hdN : (d : G) ∈ N := ⟨d, hd, rfl⟩
    have hle : N ≤ Cen b := (Subgroup.map_subtype_le _).trans inf_le_left
    have : (⟨d, hle hdN⟩ : Cen b) ∈ N.subgroupOf (Cen b) := Subgroup.mem_subgroupOf.mpr hdN
    rw [hNbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using congrArg Subtype.val this))
  have hDp : IsPGroup 3 D :=
    P.isPGroup'.of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp hkerbot)
  refine le_antisymm (fun y hy => h3 y hy (hpow ⟨y, hy⟩ (hDp ⟨y, hy⟩))) ((Subgroup.zpowers_le).mpr hbD)

theorem FF81Basis.cenS_eq (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    CenS B = B := by
  have hcomm := comm_of_isElemAb hB.mono.1
  have hBC : B ≤ CenS B := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    hcomm y hy x hx
  refine le_antisymm (fun x hx => ?_) hBC
  have hbB := hB.mem.1
  have hxb : x ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hx b hbB).symm
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L hB.hyp.model x (hB.hyp.hLN hxb)
  set d := l⁻¹ * x with hd
  have hdL : d ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := hl y hy
    calc y * d = l⁻¹ * (l * y * l⁻¹) * x := by rw [hd]; group
      _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = d * y := by rw [hd]; group
  have hdb : d ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (hB.hyp.hLC hlL)) hxb
  have hdB : d ∈ B := by
    have h1 : d ∈ Cen b ⊓ CenS L := ⟨hdb, hdL⟩
    rw [hB.cen_inf_cenS_eq h0] at h1
    exact (Subgroup.zpowers_le.mpr hbB) h1
  have hlC : l ∈ CenS B := by
    have : l = x * d⁻¹ := by rw [hd]; group
    rw [this]
    exact (CenS B).mul_mem hx ((CenS B).inv_mem (hBC hdB))
  obtain ⟨hb1, hb2, hb3⟩ := hB.mem.2
  have hlB₁ : l ∈ L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) := by
    refine ⟨hlL, Subgroup.centralizer_le ?_ hlC⟩
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hb1, hb2, hb3]
  rw [hB.selfcen] at hlB₁
  have hlB : l ∈ B := by
    refine (Subgroup.closure_le B).mpr ?_ hlB₁
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hb1, hb2, hb3]
  have : x = l * d := by rw [hd]; group
  rw [this]
  exact B.mul_mem hlB hdB

end CFSG.RankThree.PartTwo.Sec21.FF81
