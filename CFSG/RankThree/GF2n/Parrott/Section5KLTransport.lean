module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.CentralizerJoinH

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def lemma54KLBranches (z σ x : G) (W K : Subgroup G) : Prop :=
  (∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
      (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W) ∧
      (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * (a * z) * c⁻¹ ∈ W) ∧
      ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
    (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
      Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)

omit [Finite G] in
private theorem conj_toMonoidHom_apply_kl (c y : G) :
    (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := MulAut.conj_apply c y

omit [Finite G] in
private theorem mem_centerIn_map_conj_iff_kl {K : Subgroup G} {c e : G} :
    e ∈ centerIn (K.map (MulAut.conj c).toMonoidHom) ↔ c⁻¹ * e * c ∈ centerIn K := by
  rw [centerIn, centerIn, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨heK', hcent⟩
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp heK'
    have hye' : c * y * c⁻¹ = e := by rw [← hye, conj_toMonoidHom_apply_kl]
    have hce : c⁻¹ * e * c = y := by rw [← hye']; group
    refine ⟨hce ▸ hy, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (MulAut.conj c).toMonoidHom k ∈ K.map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have h1 : (MulAut.conj c).toMonoidHom k * e = e * (MulAut.conj c).toMonoidHom k :=
      hcent ((MulAut.conj c).toMonoidHom k) hk'
    rw [conj_toMonoidHom_apply_kl] at h1
    calc k * (c⁻¹ * e * c) = c⁻¹ * ((c * k * c⁻¹) * e) * c := by group
      _ = c⁻¹ * (e * (c * k * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * e * c) * k := by group
  · rintro ⟨heK, hcent⟩
    have heq : c * (c⁻¹ * e * c) * c⁻¹ = e := by group
    have hmem : (MulAut.conj c).toMonoidHom (c⁻¹ * e * c) ∈
        K.map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨c⁻¹ * e * c, heK, rfl⟩
    have hmem' : e ∈ K.map (MulAut.conj c).toMonoidHom := by
      rw [← heq, ← conj_toMonoidHom_apply_kl]
      exact hmem
    refine ⟨hmem', ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hk'
    rw [conj_toMonoidHom_apply_kl] at hke
    rw [Subgroup.mem_centralizer_iff] at hcent
    have h1 : k * (c⁻¹ * e * c) = (c⁻¹ * e * c) * k := hcent k hk
    calc k' * e = (c * k * c⁻¹) * e := by rw [hke]
      _ = (c * k * c⁻¹) * (c * (c⁻¹ * e * c) * c⁻¹) := by rw [heq]
      _ = c * (k * (c⁻¹ * e * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * e * c) * k) * c⁻¹ := by rw [h1]
      _ = (c * (c⁻¹ * e * c) * c⁻¹) * (c * k * c⁻¹) := by group
      _ = e * k' := by rw [heq, hke]

private theorem conj_mem_H_kl {z c y : G} (hc : c ∈ H z) (hy : y ∈ H z) : c * y * c⁻¹ ∈ H z := by
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  have hc' : c * z = z * c := by
    rw [H_eq_centralizer] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hci' : c⁻¹ * z = z * c⁻¹ := (show Commute c z from hc').inv_left.eq
  calc (c * y * c⁻¹) * z = c * y * (c⁻¹ * z) := by group
    _ = c * y * (z * c⁻¹) := by rw [hci']
    _ = c * (y * z) * c⁻¹ := by group
    _ = c * (z * y) * c⁻¹ := by rw [hy]
    _ = (c * z) * y * c⁻¹ := by group
    _ = (z * c) * y * c⁻¹ := by rw [hc']
    _ = z * (c * y * c⁻¹) := by group

omit [Finite G] in
private theorem map_conj_centralizer_kl {u c : G} :
    (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * u * c⁻¹} : Set G) := by
  apply le_antisymm
  · rintro y ⟨m, hm, rfl⟩
    have hm' : m * u = u * m := Subgroup.mem_centralizer_singleton_iff.mp hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c * m * c⁻¹) * (c * u * c⁻¹) = c * (m * u) * c⁻¹ := by group
      _ = c * (u * m) * c⁻¹ := by rw [hm']
      _ = (c * u * c⁻¹) * (c * m * c⁻¹) := by group
  · intro y hy
    have hy' : y * (c * u * c⁻¹) = (c * u * c⁻¹) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * y * c, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * y * c) * u = c⁻¹ * (y * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * y) * c := by rw [hy']
        _ = u * (c⁻¹ * y * c) := by group
    · rw [conj_toMonoidHom_apply_kl]; group

private theorem map_conj_H_kl {z c : G} (hc : c ∈ H z) :
    (H z).map (MulAut.conj c).toMonoidHom = H z := by
  apply le_antisymm
  · rintro y ⟨m, hm, rfl⟩
    exact conj_mem_H_kl hc hm
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * y * c, ?_, ?_⟩
    · simpa using conj_mem_H_kl (z := z) (Subgroup.inv_mem _ hc) hy
    · rw [conj_toMonoidHom_apply_kl]; group

omit [Finite G] in
private theorem map_conj_centralizer_singleton_self_kl {σ c : G} (hc : c * σ = σ * c) :
    (Subgroup.centralizer ({σ} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({σ} : Set G) := by
  rw [map_conj_centralizer_kl]
  have h : c * σ * c⁻¹ = σ := by
    calc c * σ * c⁻¹ = (σ * c) * c⁻¹ := by rw [hc]
      _ = σ := by group
  rw [h]

theorem lemma54KLBranches_conj (h : Tim79a.ParrottHyp z) {σ x c : G} {W K : Subgroup G}
    (hc : c ∈ H z ⊓ centralizer ({σ} : Set G)) (hB : lemma54KLBranches z σ x W K) :
    lemma54KLBranches z σ (c * x * c⁻¹) W (K.map (MulAut.conj c).toMonoidHom) := by
  have _ := h
  obtain ⟨hcH, hcσ⟩ := Subgroup.mem_inf.mp hc
  have hcσ' : c * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.mp hcσ
  have hcz : c * z * c⁻¹ = z := by
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hcH]
      _ = z := by group
  have hcHinv : c⁻¹ * z = z * c⁻¹ :=
    (show Commute c z from Subgroup.mem_centralizer_singleton_iff.mp hcH).inv_left.eq
  have hJmap : (J z).map (MulAut.conj c).toMonoidHom = J z := by
    apply le_antisymm
    · rintro y ⟨j, hj, rfl⟩
      exact conj_mem_J_of_mem_H hcH hj
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨c⁻¹ * y * c, ?_, ?_⟩
      · simpa using conj_mem_J_of_mem_H (Subgroup.inv_mem _ hcH) hy
      · rw [conj_toMonoidHom_apply_kl]; group
  have haeq : ∀ a : G, c⁻¹ * (c * a * c⁻¹) * c = a := fun a => by group
  rw [lemma54KLBranches] at hB ⊢
  rcases hB with ⟨a, haK, ha1, haz, ⟨d₁, hd₁, hd₁W⟩, ⟨d₂, hd₂, hd₂W⟩, hcov⟩ | ⟨hzsq, hleK⟩
  · refine Or.inl ⟨c * a * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_centerIn_map_conj_iff_kl, haeq]; exact haK
    · intro h1
      exact ha1 (by rw [← haeq a]; rw [h1]; group)
    · intro h1
      exact haz (by rw [← haeq a]; rw [h1, hcHinv]; group)
    · refine ⟨d₁ * c⁻¹, Subgroup.mul_mem _ hd₁ (Subgroup.inv_mem _ hc), ?_⟩
      have heq : (d₁ * c⁻¹) * (c * a * c⁻¹) * (d₁ * c⁻¹)⁻¹ = d₁ * a * d₁⁻¹ := by group
      rw [heq]; exact hd₁W
    · refine ⟨d₂ * c⁻¹, Subgroup.mul_mem _ hd₂ (Subgroup.inv_mem _ hc), ?_⟩
      have heq : (d₂ * c⁻¹) * ((c * a * c⁻¹) * z) * (d₂ * c⁻¹)⁻¹ = d₂ * (a * z) * d₂⁻¹ := by
        calc (d₂ * c⁻¹) * ((c * a * c⁻¹) * z) * (d₂ * c⁻¹)⁻¹
            = d₂ * a * (c⁻¹ * z) * c * d₂⁻¹ := by group
          _ = d₂ * a * (z * c⁻¹) * c * d₂⁻¹ := by rw [hcHinv]
          _ = d₂ * (a * z) * d₂⁻¹ := by group
      rw [heq]; exact hd₂W
    · intro e' he'
      have he : c⁻¹ * e' * c ∈ centerIn K := mem_centerIn_map_conj_iff_kl.mp he'
      have hkey : e' = c * (c⁻¹ * e' * c) * c⁻¹ := by group
      rcases hcov (c⁻¹ * e' * c) he with h1 | h1 | h1 | h1 | ⟨d, hd, hdx⟩
      · exact Or.inl (by rw [hkey, h1]; group)
      · exact Or.inr (Or.inl (by rw [hkey, h1, hcz]))
      · exact Or.inr (Or.inr (Or.inl (by rw [hkey, h1])))
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        have hstep : c * (a * z) * c⁻¹ = (c * a * c⁻¹) * z := by
          rw [mul_assoc c (a * z) c⁻¹, mul_assoc a z c⁻¹, ← hcHinv]
          group
        rw [hkey, h1, hstep]
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        refine ⟨c * d * c⁻¹, conj_mem_H_kl hcH hd, ?_⟩
        rw [hkey, ← hdx]
        group
  · have hmap : (Subgroup.closure ((fun k => k * k) '' (K : Set G))).map
        (MulAut.conj c).toMonoidHom =
        Subgroup.closure ((fun k => k * k) ''
          ((K.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨m, ⟨k, hk, rfl⟩, rfl⟩
        exact ⟨(MulAut.conj c) k, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, (map_mul _ k k).symm⟩
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
        exact ⟨k * k, ⟨k, hk, rfl⟩, by rw [map_mul]⟩
    refine Or.inr ⟨?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨z, hzsq, by rw [conj_toMonoidHom_apply_kl, hcz]⟩
    · rw [← hmap, ← hJmap]
      exact Subgroup.map_mono hleK

theorem isSylowOf_inf_centralizer_map_conj {σ x c : G} {K : Subgroup G}
    (hc : c ∈ H z ⊓ centralizer ({σ} : Set G))
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G))) :
    IsSylowOf 2 (K.map (MulAut.conj c).toMonoidHom)
      (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({c * x * c⁻¹} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcH, hcσ⟩ := Subgroup.mem_inf.mp hc
  have hcσ' : c * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.mp hcσ
  have hmap : (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)).map
      (MulAut.conj c).toMonoidHom =
      H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({c * x * c⁻¹} : Set G) := by
    have h1 : ((H z ⊓ centralizer ({σ} : Set G)) ⊓ centralizer ({x} : Set G)).map
        (MulAut.conj c).toMonoidHom =
        ((H z ⊓ centralizer ({σ} : Set G)).map (MulAut.conj c).toMonoidHom) ⊓
          (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom :=
      Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective
    have h2 : (H z ⊓ centralizer ({σ} : Set G)).map (MulAut.conj c).toMonoidHom =
        (H z).map (MulAut.conj c).toMonoidHom ⊓
          (centralizer ({σ} : Set G)).map (MulAut.conj c).toMonoidHom :=
      Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective
    rw [h1, h2, map_conj_H_kl hcH, map_conj_centralizer_singleton_self_kl hcσ',
      map_conj_centralizer_kl]
  rw [← hmap]
  exact CFSG.GroupTheory.isSylowOf_map_conj hK c

theorem forall_isSylowOf_lemma54KLBranches (h : Tim79a.ParrottHyp z) {σ x : G}
    {W K₀ : Subgroup G}
    (hK₀ : IsSylowOf 2 K₀ (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)))
    (hB : lemma54KLBranches z σ x W K₀) :
    ∀ K : Subgroup G,
      IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) →
        lemma54KLBranches z σ x W K := by
  intro K hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkY, hconj⟩ := IsSylowOf.exists_mem_conj hK₀ hK
  have hky : k * x * k⁻¹ = x := by
    have hkx : k * x = x * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hkY).2
    calc k * x * k⁻¹ = (x * k) * k⁻¹ := by rw [hkx]
      _ = x := by group
  have hkc : k ∈ H z ⊓ centralizer ({σ} : Set G) := (Subgroup.mem_inf.mp hkY).1
  have hKeq : K₀.map (MulAut.conj k).toMonoidHom = K := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      have hmem : k⁻¹ * (k * y₀ * k⁻¹) * k ∈ K₀ := by
        have h : k⁻¹ * (k * y₀ * k⁻¹) * k = y₀ := by group
        rw [h]; exact hy₀
      exact (hconj _).mpr hmem
    · intro hy
      refine ⟨k⁻¹ * y * k, (hconj y).mp hy, ?_⟩
      rw [conj_toMonoidHom_apply_kl]; group
  have hB' := lemma54KLBranches_conj h hkc hB
  rwa [hky, hKeq] at hB'

theorem forall_isSylowOf_lemma54KLBranches_of_conj (h : Tim79a.ParrottHyp z) {σ x c : G}
    {W : Subgroup G} (hc : c ∈ H z ⊓ centralizer ({σ} : Set G))
    (hB : ∀ K : Subgroup G, IsSylowOf 2 K
      (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({c * x * c⁻¹} : Set G)) →
        lemma54KLBranches z σ (c * x * c⁻¹) W K) :
    ∀ K : Subgroup G,
      IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) →
        lemma54KLBranches z σ x W K := by
  intro K hK
  have hc' : c⁻¹ ∈ H z ⊓ centralizer ({σ} : Set G) := Subgroup.inv_mem _ hc
  have hK' := isSylowOf_inf_centralizer_map_conj hc hK
  have hB' := hB (K.map (MulAut.conj c).toMonoidHom) hK'
  have hmain := lemma54KLBranches_conj h hc' hB'
  have hx' : c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x := by group
  have hK'' : (K.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = K := by
    have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id G := by
      ext y
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, conj_toMonoidHom_apply_kl,
        conj_toMonoidHom_apply_kl]
      group
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  rwa [hx', hK''] at hmain

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem mem_closure_t_uv_iff_kl (x : A45) :
    x ∈ Subgroup.closure ({tA, uA * vA} : Set A45) ↔
      x = 1 ∨ x = tA ∨ x = uA * vA ∨ x = tA * (uA * vA) := by
  constructor
  · intro hx
    let S : Subgroup A45 :=
      { carrier := {y | y = 1 ∨ y = tA ∨ y = uA * vA ∨ y = tA * (uA * vA)}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro y z hy hz
          simp only [Set.mem_setOf_eq] at hy hz ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            rcases hz with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one] <;>
            decide +kernel
        inv_mem' := by
          intro y hy
          simp only [Set.mem_setOf_eq] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] <;>
            decide +kernel }
    have hle : Subgroup.closure ({tA, uA * vA} : Set A45) ≤ S := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem card_lt_of_isSylowOf_centralizer_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : G}
    (hx : x ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : orderOf x = 2) (hxz : x ≠ z) {K : Subgroup G}
    (hK : IsSylowOf 2 K
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({x} : Set G))) :
    Nat.card K < 2 ^ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let Y : Subgroup G := H z ⊓ centralizer ({σ} : Set G)
  have hKY : K ≤ Y := hK.le.trans inf_le_left
  have hKpg : IsPGroup 2 K := hK.isPGroup
  have hT₂ : IsSylowOf 2 (lemma54T₂ D σ) Y :=
    isSylowOf_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
  have hcardT : Nat.card (lemma54T₂ D σ) = 2 ^ 8 :=
    card_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
  obtain ⟨S, hKS⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥Y)
    (P := K.subgroupOf Y) hKpg.comap_subtype
  have hS : IsSylowOf 2 ((S : Subgroup ↥Y).map Y.subtype) Y := ⟨S, rfl⟩
  have hKS' : K ≤ (S : Subgroup ↥Y).map Y.subtype := by
    intro k hk
    exact Subgroup.mem_map.mpr ⟨⟨k, hKY hk⟩, hKS (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
  have hScard : Nat.card ((S : Subgroup ↥Y).map Y.subtype) = 2 ^ 8 := by
    rw [hS.card_eq, ← hT₂.card_eq, hcardT]
  have hKle : Nat.card K ≤ 2 ^ 8 := by
    rw [← hScard]
    exact Subgroup.card_le_of_le hKS'
  by_contra hcon
  rw [not_lt] at hcon
  have hcardK : Nat.card K = 2 ^ 8 := le_antisymm hKle hcon
  have hcard_le : Nat.card ((S : Subgroup ↥Y).map Y.subtype) ≤ Nat.card K := by
    have hcard_eq : Nat.card ((S : Subgroup ↥Y).map Y.subtype) = Nat.card K := by
      rw [hScard, hcardK]
    exact hcard_eq.le
  have hKeqS : K = (S : Subgroup ↥Y).map Y.subtype :=
    Subgroup.eq_of_le_of_card_ge hKS' hcard_le
  have hKsyl : IsSylowOf 2 K Y := hKeqS.symm ▸ hS
  have hxY : x ∈ Y := hx
  have hxcentK : x ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK.le hk).2
  have hxpg : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx2]
    norm_num
  let E : Subgroup G := K ⊔ (Subgroup.zpowers x : Subgroup G)
  have hxself : x ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hEpg : IsPGroup 2 E :=
    IsPGroup.to_sup_of_normal_left' hKpg hxpg
      ((Subgroup.zpowers_le.mpr hxcentK).trans
        (Subgroup.centralizer_le_normalizer (K : Set G)))
  have hE_le : E ≤ Y ⊓ centralizer ({x} : Set G) :=
    sup_le hK.le (le_inf (Subgroup.zpowers_le.mpr hxY) (Subgroup.zpowers_le.mpr hxself))
  have hEeq : E = K := hK.eq_of_le le_sup_left hE_le hEpg
  have hxK : x ∈ K := hEeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxZ : x ∈ Subgroup.zpowers z := by
    have hxcenter : x ∈ centerIn K := Subgroup.mem_inf.mpr ⟨hxK, hxcentK⟩
    rwa [centerIn_isSylowOf_centralizer_sigma1Nine_mul_inv_eq_zpowers (z := z) D h hZ P hP
      hσ₂ hq₂ hc₂ hKsyl] at hxcenter
  have hz2 : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rw [h.1] at h2
    simpa [pow_two] using h2
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  have hper : z ^ n = z ^ (n % 2) := by
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · exact hx1 (by rw [← hn, hper, h0]; simp)
  · exact hxz (by rw [← hn, hper, h1]; simp)

theorem exists_conj_qH_eq_of_mem_centralizer_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) :
    ∃ c : ↥(H z),
      (c : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ∧
        (qH (z := z) D (c * x * c⁻¹) = 1 ∨ qH (z := z) D (c * x * c⁻¹) = tA ∨
          qH (z := z) D (c * x * c⁻¹) = uA * vA ∨
          qH (z := z) D (c * x * c⁻¹) = tA * (uA * vA)) := by
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hxσH : x * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * x := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hxσ
  have ha : qH (z := z) D x ∈
      Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹} : Set A45) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc qH (z := z) D x *
        ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹)
        = qH (z := z) D x * qH (z := z) D (sigma1Nine D * σ₂⁻¹) := by rw [hqσ]
      _ = qH (z := z) D (x * (sigma1Nine D * σ₂⁻¹)) := (map_mul _ _ _).symm
      _ = qH (z := z) D ((sigma1Nine D * σ₂⁻¹) * x) := by rw [hxσH]
      _ = ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) *
          qH (z := z) D x := by rw [map_mul, hqσ]
  have ha2 : qH (z := z) D x * qH (z := z) D x = 1 := by
    rw [← map_mul, hx2, map_one]
  have h2 : ∃ k : ℕ, orderOf (qH (z := z) D x) = 2 ^ k := by
    have hdvd : orderOf (qH (z := z) D x) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  obtain ⟨b, hbC, hba⟩ :=
    exists_conj_mem_closure_t_uv_of_mem_centralizer (a := qH (z := z) D x) ha h2
  have hσh3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hbcomm : b * qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) * b := by
    rw [hqσ]
    exact Subgroup.mem_centralizer_singleton_iff.mp hbC
  obtain ⟨c, hqc, hcσh⟩ := exists_lift_centralizer (z := z) (D := D)
    (r := sigma1Nine (z := z) D * σ₂⁻¹) hσh3 hbcomm
  have hcσ : (c : G) ∈ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcσh)
  refine ⟨c, hcσ, ?_⟩
  have hqcx : qH (z := z) D (c * x * c⁻¹) = b * qH (z := z) D x * b⁻¹ := by
    rw [map_mul, map_mul, map_inv, hqc]
  have hba' : b * qH (z := z) D x * b⁻¹ ∈
      Subgroup.closure ({tA, uA * vA} : Set A45) := hba
  rcases (mem_closure_t_uv_iff_kl (b * qH (z := z) D x * b⁻¹)).mp hba' with h1 | h1 | h1 | h1
  · exact Or.inl (by rw [hqcx, h1])
  · exact Or.inr (Or.inl (by rw [hqcx, h1]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hqcx, h1])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hqcx, h1])))

end CFSG.RankThree.GF2n.Parrott
