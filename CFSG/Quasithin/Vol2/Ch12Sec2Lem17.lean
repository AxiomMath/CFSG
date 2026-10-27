module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.SteinbergBMTIPairCalculus
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conjugate_eq_conjSub_inv (H : Subgroup G) (x : G) :
    CFSG.conjugate H x = conjSub x⁻¹ H := rfl

theorem conjSub_isTI {V : Subgroup G}
    (hTI : ∀ y : G, conjSub y V = V ∨ V ⊓ conjSub y V = ⊥) (g : G) :
    ∀ x : G, conjSub g V ⊓ CFSG.conjugate (conjSub g V) x = ⊥ ∨
      CFSG.conjugate (conjSub g V) x = conjSub g V := by
  intro x
  rw [conjugate_eq_conjSub_inv, ← conjSub_mul]
  have hx : x⁻¹ * g = g * (g⁻¹ * x⁻¹ * g) := by group
  rw [hx, conjSub_mul]
  rcases hTI (g⁻¹ * x⁻¹ * g) with h | h
  · right
    rw [h]
  · left
    rw [← conjSub_inf, h, conjSub_bot]

theorem conjSub_comm_sq {V : Subgroup G} (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hs : ∀ x ∈ V, x * x = 1) (g : G) :
    (∀ x ∈ conjSub g V, ∀ y ∈ conjSub g V, x * y = y * x) ∧ ∀ x ∈ conjSub g V, x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [mem_conjSub] at hx hy
    have := hc _ hx _ hy
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  · rw [mem_conjSub] at hx
    have := hs _ hx
    calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem conjSub_le_centralizer_of_le_normalizer [Finite G] {V : Subgroup G}
    (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hs : ∀ x ∈ V, x * x = 1)
    (hTI : ∀ y : G, conjSub y V = V ∨ V ⊓ conjSub y V = ⊥) {g : G}
    (hN : conjSub g V ≤ Subgroup.normalizer (V : Set G)) :
    conjSub g V ≤ Subgroup.centralizer (V : Set G) := by
  rcases hTI g with heq | hinf
  · rw [heq]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hc y hy x hx
  obtain ⟨hcA, hsA⟩ := conjSub_comm_sq hc hs g
  have hpair : SteinbergBM.ElementaryTIPair V (conjSub g V) :=
    { comm_left := hc
      sq_left := hs
      comm_right := hcA
      sq_right := hsA
      disjoint := hinf
      ti_left := fun x => by
        rw [conjugate_eq_conjSub_inv]
        rcases hTI x⁻¹ with h | h
        · exact Or.inr h
        · exact Or.inl h
      ti_right := conjSub_isTI hTI g }
  have hcard : Nat.card ↥(conjSub g V) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.equivMapOfInjective V (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm
  have hB : conjSub g V ⊓ Subgroup.normalizer (V : Set G) = conjSub g V := inf_eq_left.mpr hN
  have hU := hpair.symm.eq_of_eq hcard hB
  have hcomm := hpair.commutator_eq_bot hU hB
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hcomm hv) a ha).symm

theorem stmt12_2_17_of
    (h1216 : Stmt12_2_16) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) :
    Stmt12_2_17 := by
  intro G _ _ T L V hH hNE
  have hTIV := h1216 G T L V hH hNE
  have hTI : ∀ y : G, conjSub y V = V ∨ V ⊓ conjSub y V = ⊥ := fun y => by
    have := hTIV y⁻¹
    rwa [conjugate_eq_conjSub_inv, inv_inv] at this
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hs : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, hVLT hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    rw [← pow_two]
    simpa using congrArg Subtype.val h2
  have hL0 := hH.conjClosure_eq
  have hV0 : conjClosure V T = V := conjClosure_eq_self_of_normalizes hTV
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (stmt3_2_2_eight_proved G T L V hH.fsu).2.2
    rwa [hL0, hV0] at this
  have hW : weakClosureW0 T V ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine iSup₂_le fun g hg => le_inf hg ?_
    exact conjSub_le_centralizer_of_le_normalizer hc hs hTI (hg.trans hTV)
  refine ⟨hW, hQ.symm, ?_⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hWQ : weakClosureW0 T V ≤ Q := by rw [hQ]; exact hW
  have hQT : Q ≤ T := by rw [hQ]; exact inf_le_left
  have hconj : ∀ x ∈ Subgroup.normalizer (Q : Set G),
      conjSub x (weakClosureW0 T V) ≤ weakClosureW0 T V := by
    intro x hx
    rw [weakClosureW0, conjSub_iSup]
    refine iSup_le fun g => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hg => ?_
    rw [← conjSub_mul]
    have hle : conjSub (x * g) V ≤ T := by
      rw [conjSub_mul]
      have h1 : conjSub g V ≤ Q := (conjSub_le_weakClosureW0 hg).trans hWQ
      refine (conjSub_mono x h1).trans (le_trans ?_ hQT)
      intro y hy
      rw [mem_conjSub] at hy
      have := (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * y * x)).mp hy
      simpa [mul_assoc] using this
    exact conjSub_le_weakClosureW0 hle
  have hNQ : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (weakClosureW0 T V : Set G) := by
    intro x hx
    have h1 := hconj x hx
    have h2 := hconj x⁻¹ (inv_mem hx)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact h1 (mul_mem_conjSub hw)
    · intro hw
      have := h2 (mul_mem_conjSub hw)
      simpa [mul_assoc] using this
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ T) |>.trans' Subgroup.le_normalizer
  have h2W : IsPGroup 2 ↥(weakClosureW0 T V) :=
    (CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hH.sylow).elim fun S hS =>
      (hS ▸ S.isPGroup').to_le (hWQ.trans hQT)
  have hW1 : weakClosureW0 T V ≠ ⊥ := by
    intro h
    apply hH.irrPlus.2.1
    rw [eq_bot_iff, ← h]
    have := conjSub_le_weakClosureW0 (T := T) (V := V) (g := 1) (by rw [conjSub_one]; exact hVT)
    rwa [conjSub_one] at this
  obtain ⟨M', hM', hWM'⟩ :=
    CFSG.Quasithin.exists_maxTwoLocal_ge (L := Subgroup.normalizer (weakClosureW0 T V : Set G))
      ⟨weakClosureW0 T V, hW1, h2W, rfl⟩
  obtain ⟨-, ⟨-, huniq⟩, -⟩ :=
    h323 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful hH.quasisimple
  rw [hL0] at huniq
  have hM'eq := huniq M' hM' ((hLTQ.trans hNQ).trans hWM')
  rw [← hM'eq]
  exact hWM'

end CFSG.Quasithin.H13
