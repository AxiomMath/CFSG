module

public import CFSG.RankThree.GF2n.Smith81.S81QBridge
public import CFSG.RankThree.GF2n.Smith81.S81KSylow
public import CFSG.RankThree.GF2n.Smith81.S81QStepD6

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X


section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem chi_eq_prod (α : Rt) (t : Tt K) :
    chi α t = ∏ i : Fin (Tag.rank .E7), t i ^ MinData.toWeight α i := by
  rw [Fin.prod_univ_def]
  rfl

theorem torus_reduce (t : Tt K) :
    ∃ t' : Tt K, t' node1 = 1 ∧ ∀ α : Rt, α node1 = 0 → chi α t' = chi α t := by
  haveI : Fintype K := Fintype.ofFinite K
  have hmod : Fintype.card K % 2 = 0 :=
    FiniteField.even_card_iff_char_two.1 (ringChar.eq K 2)
  obtain ⟨h, hh⟩ : ∃ h : ℕ, Fintype.card K = 2 * h := ⟨Fintype.card K / 2, by omega⟩
  have hpow : ∀ u : Kˣ, u ^ Fintype.card K = u := by
    intro u
    ext
    rw [Units.val_pow_eq_pow_val, FiniteField.pow_card]
  have hint : (h : ℤ) * 2 = ((Fintype.card K : ℕ) : ℤ) := by omega
  have hzsum : ∀ (S : Finset (Fin (Tag.rank .E7))) (s : Kˣ) (c : Fin (Tag.rank .E7) → ℤ),
      ∏ i ∈ S, s ^ c i = s ^ (∑ i ∈ S, c i) := by
    intro S s c
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  refine ⟨fun i => t i * (t node1) ^ (-((h : ℤ) * E7Model.theta i)), ?_, ?_⟩
  · have hθ : E7Model.theta node1 = 2 := rfl
    have e1 : (t node1) ^ (-((h : ℤ) * 2)) = (t node1)⁻¹ := by
      rw [zpow_neg, hint, zpow_natCast, hpow]
    dsimp only
    rw [hθ, e1, mul_inv_cancel]
  · intro α hα
    have hsum0 : ∑ i, MinData.toWeight α i * E7Model.theta i = 0 := by
      have h1 := pair_theta α
      rw [hα] at h1
      exact h1
    have hsum' : ∑ i, -((h : ℤ) * E7Model.theta i) * MinData.toWeight α i = 0 := by
      have e : ∑ i, -((h : ℤ) * E7Model.theta i) * MinData.toWeight α i
          = -(h : ℤ) * ∑ i, MinData.toWeight α i * E7Model.theta i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, hsum0, mul_zero]
    have key : ∏ i, ((t node1) ^ (-((h : ℤ) * E7Model.theta i))) ^ MinData.toWeight α i = 1 := by
      simp only [← zpow_mul]
      rw [hzsum Finset.univ (t node1), hsum', zpow_zero]
    simp only [chi_eq_prod, mul_zpow, Finset.prod_mul_distrib, key, mul_one]


theorem tau_conj_eq {t t' : Tt K} (h : ∀ α ∈ Rd6, chi α t' = chi α t) {e : Gp K}
    (he : e ∈ URge K Rd6 1) : tau t * e * (tau t)⁻¹ = tau t' * e * (tau t')⁻¹ := by
  refine URge_induction (C := fun e => tau t * e * (tau t)⁻¹ = tau t' * e * (tau t')⁻¹) he ?_ ?_ ?_
  · intro α hα _ c
    rw [tau_conj_xE (closed_Rd6.root α hα), tau_conj_xE (closed_Rd6.root α hα), h α hα]
  · simp
  · intro x y hx hy
    have e1 : tau t * (x * y) * (tau t)⁻¹ = (tau t * x * (tau t)⁻¹) * (tau t * y * (tau t)⁻¹) := by
      group
    have e2 : tau t' * (x * y) * (tau t')⁻¹ =
        (tau t' * x * (tau t')⁻¹) * (tau t' * y * (tau t')⁻¹) := by group
    rw [e1, e2, hx, hy]

end Torus

@[expose] def T0g (K : Type) [Field K] : Subgroup (Gp K) :=
  ⨆ i : {i : Fin (Tag.rank .E7) // i ≠ node1}, e7Data_valid.torus K i

section Torus2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem hm_mem_Lam {i : Fin (Tag.rank .E7)} (hi : i ≠ node1) (c : Kˣ) :
    (e7Data_valid.hm K i c : (Module.End K (V K))ˣ) ∈ Lam K := by
  have hα : (Pi.single i (1 : ℤ) : Fin (Tag.rank .E7) → ℤ) ∈ Perp := by
    rw [perp_iff]
    refine ⟨IsRoot.basis (τ := .E7) i, ?_⟩
    rw [Pi.single_eq_of_ne (show node1 ≠ i from fun h => hi h.symm)]
  have hle : CFSG.LieType.CurtisTits.rankOne (e7Data_valid.rootGroup K) i ≤
      (Lam K).comap (e7Data_valid.minGroup K).subtype := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hg
      exact xu_mem_Lam hα u
    · intro g hg
      obtain ⟨u, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hg
      exact xu_mem_Lam (neg_mem_Perp hα) u
  exact hle (e7Data_valid.torus_le_rankOne K i (e7Data_valid.hm_mem_torus K i c))

theorem T0g_le_LamG : T0g K ≤ LamG K := by
  refine iSup_le fun i => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (e7Data_valid.mem_torus K).1 hg
  exact hm_mem_Lam i.2 c

theorem tau_mem_T0g {t' : Tt K} (h : t' node1 = 1) : tau t' ∈ T0g K := by
  unfold tau
  refine Subgroup.list_prod_mem _ ?_
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  by_cases hi : i = node1
  · subst hi
    rw [h]
    simp [e7Data_valid.hm_one]
  · have hmem : e7Data_valid.hm K i (t' i) ∈ e7Data_valid.torus K i :=
      e7Data_valid.hm_mem_torus K i (t' i)
    exact Subgroup.mem_iSup_of_mem (S := fun j : {i : Fin (Tag.rank .E7) // i ≠ node1} =>
      e7Data_valid.torus K j.1) ⟨i, hi⟩ hmem

end Torus2

section Final

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def T0 (K : Type) [Field K] [CharP K 2] : Subgroup (W K ≃ₗ[K] W K) :=
  ((T0g K).subgroupOf (LamG K)).map (lamGHom K)

@[expose] def Eg (A : Subgroup (W K ≃ₗ[K] W K)) : Subgroup (Gp K) :=
  (A.comap (lamGHom K)).map (LamG K).subtype

theorem mem_Eg {A : Subgroup (W K ≃ₗ[K] W K)} {x : Gp K} :
    x ∈ Eg A ↔ ∃ h : x ∈ LamG K, lamGHom K ⟨x, h⟩ ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem Eg_le_LamG (A : Subgroup (W K ≃ₗ[K] W K)) : Eg A ≤ LamG K := fun _ hx => (mem_Eg.1 hx).1

theorem card_Eg {A : Subgroup (W K ≃ₗ[K] W K)} (hA : A ≤ EAut0 K) : Nat.card ↥(Eg A) = Nat.card ↥A := by
  have h1 : Nat.card ↥(Eg A) = Nat.card ↥(A.comap (lamGHom K)) :=
    Subgroup.card_map_of_injective (LamG K).subtype_injective
  have h2 : (A.comap (lamGHom K)).map (lamGHom K) = A := by
    rw [Subgroup.map_comap_eq, range_lamGHom, inf_eq_right.2 hA]
  rw [h1, ← Subgroup.card_map_of_injective lamGHom_injective, h2]

theorem Eg_le_URge {A : Subgroup (W K ≃ₗ[K] W K)} (hA : A ≤ posU0 K) : Eg A ≤ URge K Rd6 1 := by
  intro x hx
  obtain ⟨h, hxA⟩ := mem_Eg.1 hx
  have h1 := hA hxA
  rw [posU0_eq_map] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = ⟨x, h⟩ := lamGHom_injective hyx
  have hy' := Subgroup.mem_subgroupOf.1 hy
  rw [this] at hy'
  exact hy'

theorem conj_mem_Eg_T0g {A : Subgroup (W K ≃ₗ[K] W K)}
    (hT : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K))) {s : Gp K} (hs : s ∈ T0g K)
    {e : Gp K} (he : e ∈ Eg A) : s * e * s⁻¹ ∈ Eg A := by
  obtain ⟨he1, heA⟩ := mem_Eg.1 he
  have hs1 : s ∈ LamG K := T0g_le_LamG hs
  have hse : s * e * s⁻¹ ∈ LamG K := mul_mem (mul_mem hs1 he1) (inv_mem hs1)
  refine mem_Eg.2 ⟨hse, ?_⟩
  have hsT : lamGHom K ⟨s, hs1⟩ ∈ T0 K := ⟨⟨s, hs1⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hnorm := (Subgroup.mem_normalizer_iff.1 (hT _ hsT) (lamGHom K ⟨e, he1⟩)).1 heA
  have : lamGHom K ⟨s * e * s⁻¹, hse⟩ =
      lamGHom K ⟨s, hs1⟩ * lamGHom K ⟨e, he1⟩ * (lamGHom K ⟨s, hs1⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact hnorm

theorem conj_mem_Eg_URge {A : Subgroup (W K ≃ₗ[K] W K)}
    (hU : ∀ u ∈ posU0 K, u ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K))) {u : Gp K}
    (hu : u ∈ URge K Rd6 1) {e : Gp K} (he : e ∈ Eg A) : u * e * u⁻¹ ∈ Eg A := by
  obtain ⟨he1, heA⟩ := mem_Eg.1 he
  have hu1 : u ∈ LamG K := URge_Rd6_le_LamG hu
  have hue : u * e * u⁻¹ ∈ LamG K := mul_mem (mul_mem hu1 he1) (inv_mem hu1)
  refine mem_Eg.2 ⟨hue, ?_⟩
  have huU : lamGHom K ⟨u, hu1⟩ ∈ posU0 K := by
    rw [posU0_eq_map]
    exact ⟨⟨u, hu1⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
  have hnorm := (Subgroup.mem_normalizer_iff.1 (hU _ huU) (lamGHom K ⟨e, he1⟩)).1 heA
  have : lamGHom K ⟨u * e * u⁻¹, hue⟩ =
      lamGHom K ⟨u, hu1⟩ * lamGHom K ⟨e, he1⟩ * (lamGHom K ⟨u, hu1⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact hnorm

theorem isStab_Eg {A : Subgroup (W K ≃ₗ[K] W K)} (hAU : A ≤ posU0 K)
    (hel : CFSG.Open.IsElemAbelian 2 A)
    (hT : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K)))
    (hU : ∀ u ∈ posU0 K, u ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K))) :
    IsStab Rd6 (Eg A) where
  le := Eg_le_URge hAU
  tau t e he := by
    obtain ⟨t', ht'1, ht'⟩ := torus_reduce t
    have hchar : ∀ α ∈ Rd6, chi α t' = chi α t := fun α hα =>
      ht' α (perp_iff.1 (Rd6_subset_Perp hα)).2
    rw [tau_conj_eq hchar (Eg_le_URge hAU he)]
    exact conj_mem_Eg_T0g hT (tau_mem_T0g ht'1) he
  norm u hu e he := conj_mem_Eg_URge hU hu he
  comm e he e' he' := by
    obtain ⟨he1, heA⟩ := mem_Eg.1 he
    obtain ⟨he1', heA'⟩ := mem_Eg.1 he'
    have hc : lamGHom K ⟨e, he1⟩ * lamGHom K ⟨e', he1'⟩ = lamGHom K ⟨e', he1'⟩ * lamGHom K ⟨e, he1⟩ :=
      Subtype.ext_iff.1 (hel.1.1.comm ⟨_, heA⟩ ⟨_, heA'⟩)
    rw [← map_mul, ← map_mul] at hc
    have := congrArg Subtype.val (lamGHom_injective hc)
    exact this

theorem eq_rootRad0_or_rootRadν_of_torus (hq : 4 ≤ Nat.card K) {A : Subgroup (W K ≃ₗ[K] W K)}
    (hAU : A ≤ posU0 K) (hel : CFSG.Open.IsElemAbelian 2 A) (hcard : Nat.card K ^ 15 ≤ Nat.card ↥A)
    (hT : ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K)))
    (hU : ∀ u ∈ posU0 K, u ∈ Subgroup.normalizer (A : Set (W K ≃ₗ[K] W K))) :
    A = rootRad0 K ∨ A = rootRadν K := by
  have hAE : A ≤ EAut0 K := hAU.trans posU0_le_EAut0
  have hstab := isStab_Eg hAU hel hT hU
  have hcardE : Nat.card K ^ 15 ≤ Nat.card ↥(Eg A) := by rw [card_Eg hAE]; exact hcard
  have hAeq : A = ((Eg A).subgroupOf (LamG K)).map (lamGHom K) := by
    have h1 : (Eg A).subgroupOf (LamG K) = A.comap (lamGHom K) := by
      ext x
      rw [Subgroup.mem_subgroupOf, mem_Eg, Subgroup.mem_comap]
      constructor
      · rintro ⟨h, hx⟩
        exact hx
      · intro hx
        exact ⟨x.2, hx⟩
    rw [h1, Subgroup.map_comap_eq, range_lamGHom, inf_eq_right.2 hAE]
  rcases step1_D6 hq hstab hcardE with h | h
  · left
    rw [hAeq, h, map_lamGHom_URge_A2]
  · right
    rw [hAeq, h, map_lamGHom_URge_Nu]

end Final

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_le_posU0 {A : Subgroup (W K ≃ₗ[K] W K)} (hA : A ≤ EAut0 K) (h2 : IsPGroup 2 A) :
    ∃ g ∈ EAut0 K, A.map (MulAut.conj g).toMonoidHom ≤ posU0 K := by
  have h1 : IsPGroup 2 (A.comap (lamGHom K)) :=
    h2.of_injective ((lamGHom K).subgroupComap A)
      (fun x y hxy => Subtype.ext (lamGHom_injective (congrArg Subtype.val hxy)))
  have hE2 : IsPGroup 2 (Eg A) := h1.map (LamG K).subtype
  obtain ⟨g, hgL, hg⟩ := SK.lam_conj_into_ULG (Eg A) (Eg_le_LamG A) hE2
  refine ⟨lamGHom K ⟨g, hgL⟩, ?_, ?_⟩
  · rw [← range_lamGHom]
    exact ⟨_, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ (lamGHom K).range := by
      rw [range_lamGHom]
      exact hA hy
    have hxE : (x : Gp K) ∈ Eg A := mem_Eg.2 ⟨x.2, hy⟩
    have hcx : g * (x : Gp K) * g⁻¹ ∈ URge K Rd6 1 := by
      rw [← ULG_eq_URge]
      exact hg ⟨x, hxE, rfl⟩
    have hmem : (⟨g * (x : Gp K) * g⁻¹, mul_mem (mul_mem hgL x.2) (inv_mem hgL)⟩ : ↥(LamG K)) ∈
        (URge K Rd6 1).subgroupOf (LamG K) := hcx
    rw [posU0_eq_map]
    refine ⟨_, hmem, ?_⟩
    show lamGHom K ⟨g * (x : Gp K) * g⁻¹, _⟩ = lamGHom K ⟨g, hgL⟩ * lamGHom K x * (lamGHom K ⟨g, hgL⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

end Sylow

end CFSG.RankThree.GF2n.Smith81.D6Spin
