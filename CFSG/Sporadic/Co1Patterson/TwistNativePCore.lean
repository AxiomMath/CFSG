module

public import CFSG.Sporadic.Co1Patterson.TwistNativeRM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

variable
  (k : Fin 3)

theorem tw_mul (g g' : FP k) : tw k g * tw k g' = tw k (g * g') := rfl

theorem tw_inv (g : FP k) : (tw k g)⁻¹ = tw k g⁻¹ := rfl

theorem fst_conj (g g' : FP k) : (g * g' * g⁻¹ : FP k).val.1 = g.val.1 * g'.val.1 * g.val.1⁻¹ :=
  rfl

theorem conj_mem_RM {x : TM k} (hx : x ∈ Kc k) {r : TM k} (hr : r ∈ RM k) :
    x * r * x⁻¹ ∈ RM k := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', hg', rfl⟩ := (mem_RM_iff k).1 hr
  have hgK := (tw_mem_Kc_iff k g).1 hx
  rw [tw_inv, tw_mul, tw_mul]
  refine tw_mem_RM k ?_
  rw [fst_conj]
  exact conj_mem_R₀ hgK hg'

@[expose] noncomputable def firstCoords (N : Subgroup (TM k)) :
    Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  (N.comap (QuotientGroup.mk' _)).map ((MonoidHom.fst _ _).comp (FP k).subtype)

theorem mem_firstCoords {N : Subgroup (TM k)} {x : centralizer ({aNC} : Set NativeSporadic.Co1)} :
    x ∈ firstCoords k N ↔ ∃ g : FP k, tw k g ∈ N ∧ g.val.1 = x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem fst_pow (g : FP k) (n : ℕ) : (g ^ n : FP k).val.1 = g.val.1 ^ n := by
  rw [Subgroup.coe_pow, Prod.pow_fst]

theorem le_RM {N : Subgroup (TM k)} (hNK : N ≤ Kc k)
    (hnorm : ∀ x ∈ Kc k, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hP : IsPGroup 2 N) : N ≤ RM k := by
  have hN₀K : firstCoords k N ≤ K₀ := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := (mem_firstCoords k).1 hx
    exact (tw_mem_Kc_iff k g).1 (hNK hg)
  have hN₀n : ∀ k₀ ∈ K₀, ∀ x ∈ firstCoords k N, k₀ * x * k₀⁻¹ ∈ firstCoords k N := by
    intro k₀ hk₀ x hx
    obtain ⟨g, hg, rfl⟩ := (mem_firstCoords k).1 hx
    obtain ⟨e, he⟩ := wPlusMap_surjective iotaC k (typeSystemC.φ k₀)
    let g₀ : FP k := ⟨(k₀, e), by rw [mem_fibreProd, he]⟩
    have hg₀ : tw k g₀ ∈ Kc k := (tw_mem_Kc_iff k g₀).2 hk₀
    have hc := hnorm _ hg₀ _ hg
    rw [tw_inv, tw_mul, tw_mul] at hc
    exact (mem_firstCoords k).2 ⟨_, hc, fst_conj k g₀ g⟩
  have hN₀P : IsPGroup 2 (firstCoords k N) := by
    intro x
    obtain ⟨g, hg, hgx⟩ := (mem_firstCoords k).1 x.2
    obtain ⟨n, hn⟩ := hP ⟨tw k g, hg⟩
    have h1 : tw k (g ^ 2 ^ n) = tw k 1 := by
      have := congrArg Subtype.val hn
      simpa [QuotientGroup.mk_pow] using this
    refine ⟨n + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hgx, pow_succ, pow_mul, ← fst_pow]
    rcases (tw_eq_tw_iff k).1 h1 with h2 | h2
    · rw [← h2]
      simp
    · have h3 : (1 : FP k).val.1 = (g ^ 2 ^ n * zζ typeSystemC (wPlusMap iotaC k) zPlus
          (wPlusMap_zPlus iotaC k) : FP k).val.1 := by rw [← h2]
      rw [fst_mul_zζ] at h3
      have h4 : (g ^ 2 ^ n : FP k).val.1 = typeSystemC.z := by
        calc (g ^ 2 ^ n : FP k).val.1 = (g ^ 2 ^ n : FP k).val.1 * typeSystemC.z *
              typeSystemC.z := by rw [mul_assoc, typeSystemC.z_mul_self, mul_one]
          _ = typeSystemC.z := by rw [← h3]; simp
      rw [h4, sq, typeSystemC.z_mul_self]
  have hN₀R := le_R₀ hN₀K hN₀n hN₀P
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact tw_mem_RM k (hN₀R ((mem_firstCoords k).2 ⟨g, hy, rfl⟩))

theorem pCore_cent_eq : CFSG.pCore 2 (Kc k) = (RM k).subgroupOf (Kc k) :=
  pCore_subgroupOf_eq (G := TM k) (K := Kc k) (R := RM k)
    (fun _ hx _ hr => conj_mem_RM k hx hr) (isPGroup_RM k)
    (fun _ hNK hnorm hP => le_RM k hNK hnorm hP)

theorem mem_pCore_cent_iff (x : Kc k) : x ∈ CFSG.pCore 2 (Kc k) ↔ (x : TM k) ∈ RM k := by
  rw [pCore_cent_eq k, mem_subgroupOf]

theorem card_sq_pCore_eq (σ : TM k) :
    Nat.card {x : CFSG.pCore 2 (Kc k) // ((x : Kc k) : TM k) ^ 2 = σ} =
      Nat.card {q : Idx // Ψ k q.1.1 q.1.2 ^ 2 = σ} := by
  let f : {x : CFSG.pCore 2 (Kc k) // ((x : Kc k) : TM k) ^ 2 = σ} →
      {q : Idx // Ψ k q.1.1 q.1.2 ^ 2 = σ} := fun x =>
    ⟨(idxEquiv k).symm ⟨((x.1 : Kc k) : TM k), (mem_pCore_cent_iff k x.1).1 x.1.2⟩, by
      have h := congrArg Subtype.val ((idxEquiv k).apply_symm_apply
        ⟨((x.1 : Kc k) : TM k), (mem_pCore_cent_iff k x.1).1 x.1.2⟩)
      change Ψ k _ _ = _ at h
      rw [h]
      exact x.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun x y hxy => ?_, fun q => ?_⟩)
  · have h1 := congrArg (fun q => ((idxEquiv k) q.1 : TM k)) hxy
    simp only [f, Equiv.apply_symm_apply] at h1
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  · refine ⟨⟨⟨⟨Ψ k q.1.1.1 q.1.1.2, RM_le_Kc k (Ψ_mem_RM k q.1.2.1 q.1.2.2)⟩,
      (mem_pCore_cent_iff k _).2 (Ψ_mem_RM k q.1.2.1 q.1.2.2)⟩, q.2⟩, ?_⟩
    apply Subtype.ext
    simp only [f]
    rw [Equiv.symm_apply_eq]
    rfl

end CFSG.Sporadic.Co1Patterson.TwistNative
