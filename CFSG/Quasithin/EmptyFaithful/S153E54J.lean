module

public import CFSG.Quasithin.EmptyFaithful.S153E54I
public import CFSG.Quasithin.Background.G2Omega4PlusFive
public import CFSG.Quasithin.EmptyFaithful.S153E54H

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

theorem sl2_three_surj : ∀ R : SL(2, ZMod 2), R ≠ 1 → R ^ 3 = 1 → ∀ w : Fin 2 → ZMod 2,
    ∃ w' : Fin 2 → ZMod 2, R • w' - w' = w := by
  decide +kernel

abbrev S54 {G : Type} [Group G] (T Mc M V₁ : Subgroup G) : Subgroup G :=
  pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc)

structure G26Out54 {G : Type} [Group G] (T Mc M V₁ : Subgroup G) (M₁ M₂ Sa Sb : Subgroup G)
    (s₁ s₂ : ℕ) : Prop where
  SM₁ : S54 T Mc M V₁ ≤ M₁
  SM₂ : S54 T Mc M V₁ ≤ M₂
  M₁I : M₁ ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc
  M₂I : M₂ ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc
  sup : M₁ ⊔ M₂ = Y153 Mc M ⊔ UH153 T M V₁ Mc
  inf : M₁ ⊓ M₂ = S54 T Mc M V₁
  comm : ⁅M₁, M₂⁆ ≤ S54 T Mc M V₁
  VSa : VZ T M ≤ Sa
  SaS : Sa ≤ S54 T Mc M V₁
  VSb : VZ T M ≤ Sb
  SbS : Sb ≤ S54 T Mc M V₁
  supS : Sa ⊔ Sb = S54 T Mc M V₁
  infS : Sa ⊓ Sb = VZ T M
  commS : ⁅Sa, Sb⁆ ≤ VZ T M
  eqa : Sa = ⁅S54 T Mc M V₁, M₁⁆ ⊔ VZ T M
  eqb : Sb = ⁅S54 T Mc M V₁, M₂⁆ ⊔ VZ T M
  chara : ∀ s ∈ S54 T Mc M V₁, s ∈ Sa ↔ ∀ m ∈ M₂, ⁅m, s⁆ ∈ VZ T M
  charb : ∀ s ∈ S54 T Mc M V₁, s ∈ Sb ↔ ∀ m ∈ M₁, ⁅m, s⁆ ∈ VZ T M
  nat₁ : IsSumOfNatSL2ModulesN153 s₁ M₁ Sa (S54 T Mc M V₁) (VZ T M)
  nat₂ : IsSumOfNatSL2ModulesN153 s₂ M₂ Sb (S54 T Mc M V₁) (VZ T M)

section Out

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem g26Out_exists (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    ∃ (M₁ M₂ Sa Sb : Subgroup G) (s₁ s₂ : ℕ), G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂ := by
  have hyp := hyp54 h113 cx c
  have hU : UH153 T M V₁ Mc = conjClosure (Zp54 T M V₁ Mc) Mc := (conjClosure_Zp_eq cx).symm
  have hgV := hgV_of_notOrth cx c hgZ
  have hVL := conjClosure_Z_Y h113 cx c
  have hXV := inf_le_V h113 cx c hg hgZ
  have hI := I_eq_54 h113 cx c hg hgZ
  have hS₂ : VZ T M = conjClosure (quasithinOmegaOneCenter T) (Y153 Mc M) ⊔
      (UH153 T M V₁ Mc ⊓ rconj (UH153 T M V₁ Mc) g) := by
    rw [hVL]
    exact (sup_eq_left.2 hXV).symm
  obtain ⟨M₁, M₂, Sa, Sb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20⟩ := hyp.G26_five (U := UH153 T M V₁ Mc) (I := Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (S := pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc)) (S₂ := VZ T M) hU hg hgV hI.symm rfl hS₂
  obtain ⟨s₁, hn₁⟩ := h19
  obtain ⟨s₂, hn₂⟩ := h20
  exact ⟨M₁, M₂, Sa, Sb, s₁, s₂, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, hn₁, hn₂⟩⟩

omit [Finite G] in
theorem Yi_le_Ni (N : Subgroup (MulAut ↥(VZ T M))) :
    Yi153 T Mc M V₁ N ≤ Ni153 T Mc M V₁ N := (oTwoUpper_le _).trans inf_le_right

theorem exists_Yi_elem (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {N : Subgroup (MulAut ↥(VZ T M))} (hNΩ : N ≤ N₁ ⊔ N₂)
    (hr : ∃ r ∈ N, r ≠ 1 ∧ r ^ 3 = 1) :
    ∃ (y₁ : G) (hy₁N : y₁ ∈ Subgroup.normalizer (VZ T M : Set G)),
      y₁ ∈ Yi153 T Mc M V₁ N ∧ convI cx.c.hyp.elemAbelian ⟨y₁, hy₁N⟩ ≠ 1 ∧
        (convI cx.c.hyp.elemAbelian ⟨y₁, hy₁N⟩) ^ 3 = 1 := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨r, hrN, hr1, hr3⟩ := hr
  have hrΩ : r ∈ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    have := hNΩ hrN
    rw [← autOn_YU_eq cx c] at this
    exact this
  have hYU_M : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ M :=
    sup_le (Y153_le Mc M) ((U_le_T cx).trans (T_le_M cx))
  have hrM : r ∈ autI hV M := autI_mono hV hYU_M hrΩ
  have hodd : Odd (orderOf r) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hr3)
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hrY : r ∈ autI hV (Y153 Mc M) := by
    rw [hYbar]
    exact mem_oTwoUpper_of_odd hrM hodd
  obtain ⟨y'', hy''Y, hy''⟩ := (mem_autI hV).1 hrY
  have hn : orderOf y'' ≠ 0 := (orderOf_pos y'').ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  set y₁' : ↥(Subgroup.normalizer (VZ T M : Set G)) := y'' ^ (2 ^ a) with hy₁'
  have hy₁'G : (y₁' : G) = (y'' : G) ^ (2 ^ a) := rfl
  have hy₁Y : (y₁' : G) ∈ Y153 Mc M := by
    rw [hy₁'G]
    exact (Y153 Mc M).pow_mem hy''Y _
  have hconv : convI hV y₁' = r ^ (2 ^ a) := by
    rw [hy₁', map_pow, hy'']
    rfl
  have hr3' : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  have hne : r ^ (2 ^ a) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hr3'] at this
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hmo : orderOf y₁' ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hy₁', ← pow_mul, ← hnm]
    exact pow_orderOf_eq_one y''
  have hodd' : Odd (orderOf (y₁' : G)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hm hmo
  have hy₁N : (y₁' : G) ∈ Ni153 T Mc M V₁ N := by
    refine mem_preAut153.2 ⟨Subgroup.mem_sup_left hy₁Y, y₁'.2, ?_⟩
    have : convI hV ⟨(y₁' : G), y₁'.2⟩ ∈ N := by
      have e : (⟨(y₁' : G), y₁'.2⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) = y₁' := rfl
      rw [e, hconv]
      exact N.pow_mem hrN _
    exact this
  refine ⟨(y₁' : G), y₁'.2, mem_oTwoUpper_of_odd ⟨hy₁Y, hy₁N⟩ hodd', ?_, ?_⟩
  · have e : (⟨(y₁' : G), y₁'.2⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) = y₁' := rfl
    rw [e, hconv]
    exact hne
  · have e : (⟨(y₁' : G), y₁'.2⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) = y₁' := rfl
    rw [e, hconv]
    calc (r ^ (2 ^ a)) ^ 3 = (r ^ 3) ^ (2 ^ a) := pow_right_comm r (2 ^ a) 3
      _ = 1 := by rw [hr3, one_pow]

theorem Pi_eq (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂)
    {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g)
    {N : Subgroup (MulAut ↥(VZ T M))} (hNΩ : N ≤ N₁ ⊔ N₂) (hr : ∃ r ∈ N, r ≠ 1 ∧ r ^ 3 = 1)
    {M' Sa' : Subgroup G} {s : ℕ} (hM' : M' = Ni153 T Mc M V₁ N)
    (hSaS : Sa' ≤ S54 T Mc M V₁) (hVSa : VZ T M ≤ Sa')
    (heq : Sa' = ⁅S54 T Mc M V₁, M'⁆ ⊔ VZ T M)
    (hnorm : ∀ y ∈ M', ∀ x ∈ Sa', y * x * y⁻¹ ∈ Sa')
    (hnat : IsSumOfNatSL2ModulesN153 s M' Sa' (S54 T Mc M V₁) (VZ T M)) :
    Pi153 T Mc M V₁ N g = Sa' := by
  have hV := cx.c.hyp.elemAbelian
  have hP : Pgp153 T M V₁ Mc g = S54 T Mc M V₁ := by
    show pCoreOf 2 (Igp153 T M V₁ Mc g) = _
    rw [I_eq_54 h113 cx c hg hgZ]
  show ⁅Pgp153 T M V₁ Mc g, Yi153 T Mc M V₁ N⁆ ⊔ VZ T M = Sa'
  rw [hP]
  have hYiM' : Yi153 T Mc M V₁ N ≤ M' := hM' ▸ Yi_le_Ni N
  apply le_antisymm
  · refine sup_le ?_ hVSa
    rw [heq]
    exact le_trans (Subgroup.commutator_mono le_rfl hYiM') le_sup_left
  · obtain ⟨β, φ, hβs, hβk, hφs, hφk, hrel⟩ := hnat
    obtain ⟨y₁, hy₁N, hy₁Yi, hconv1, hconv3⟩ := exists_Yi_elem h113 cx c hNΩ hr
    have hy₁M' : y₁ ∈ M' := hYiM' hy₁Yi
    have hS := pCoreOf_YU_eq h113 cx c
    have hM'I : M' ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := hM' ▸ preAut153_le
    have hy₁I : y₁ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := hM'I hy₁M'
    have hR1 : β ⟨y₁, hy₁M'⟩ ≠ 1 := fun h => hconv1 (by
      have h1 := (hβk _).1 h
      have h2 : y₁ ∈ Subgroup.centralizer (VZ T M : Set G) := by
        have h3 : y₁ ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) := h1
        rw [hS] at h3
        exact h3.2
      exact (convI_eq_one_iff hV _).2 h2)
    have hR3 : β ⟨y₁, hy₁M'⟩ ^ 3 = 1 := by
      rw [← map_pow]
      refine (hβk _).2 ?_
      show y₁ ^ 3 ∈ pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc)
      rw [hS]
      refine ⟨(Y153 Mc M ⊔ UH153 T M V₁ Mc).pow_mem hy₁I 3,
        (convI_eq_one_iff hV ⟨y₁ ^ 3, (Subgroup.normalizer (VZ T M : Set G)).pow_mem hy₁N 3⟩).1 ?_⟩
      have e : (⟨y₁ ^ 3, (Subgroup.normalizer (VZ T M : Set G)).pow_mem hy₁N 3⟩ :
          ↥(Subgroup.normalizer (VZ T M : Set G))) = ⟨y₁, hy₁N⟩ ^ 3 := rfl
      rw [e, map_pow]
      exact hconv3
    intro x hx
    have hw' : ∀ j : Fin s, ∃ w' : Fin 2 → ZMod 2,
        β ⟨y₁, hy₁M'⟩ • w' - w' = Multiplicative.toAdd (φ ⟨x, hx⟩) j := fun j =>
      sl2_three_surj _ hR1 hR3 _
    choose w' hw'eq using hw'
    obtain ⟨x', hx'⟩ := hφs (Multiplicative.ofAdd w')
    have hmem : y₁ * (x' : G) * y₁⁻¹ ∈ Sa' := hnorm y₁ hy₁M' _ x'.2
    have hrel' := hrel ⟨y₁, hy₁M'⟩ x' ⟨y₁ * (x' : G) * y₁⁻¹, hmem⟩ rfl
    have hφx : φ ⟨x, hx⟩ = Multiplicative.ofAdd (fun j => β ⟨y₁, hy₁M'⟩ • w' j - w' j) := by
      apply Multiplicative.toAdd.injective
      funext j
      exact (hw'eq j).symm
    have hker : φ (⟨y₁ * (x' : G) * y₁⁻¹, hmem⟩ * x'⁻¹ * (⟨x, hx⟩ : ↥Sa')⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, hrel', hx', hφx]
      rw [← ofAdd_neg, ← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
      rw [ofAdd_eq_one]
      funext j
      simp only [toAdd_ofAdd, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      abel
    have hv : y₁ * (x' : G) * y₁⁻¹ * (x' : G)⁻¹ * x⁻¹ ∈ VZ T M := (hφk _).1 hker
    have hc : y₁ * (x' : G) * y₁⁻¹ * (x' : G)⁻¹ ∈ ⁅S54 T Mc M V₁, Yi153 T Mc M V₁ N⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy₁Yi (hSaS x'.2)
    have e : x = (y₁ * (x' : G) * y₁⁻¹ * (x' : G)⁻¹ * x⁻¹)⁻¹ *
        (y₁ * (x' : G) * y₁⁻¹ * (x' : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hv))
      (Subgroup.mem_sup_left hc)

end Out

end S153E54

end CFSG.Quasithin
