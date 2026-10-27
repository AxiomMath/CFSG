module

public import CFSG.Sporadic.Co1Patterson.TwistNativeModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem aList_nodup : aList.Nodup := by
  rw [aList, List.nodup_flatMap]
  refine ⟨fun c _ => by simp, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ ((List.nodup_range).filter _)
  intro a b _ _ hab
  simp only [Function.onFun, List.disjoint_cons_left, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false, List.disjoint_nil_left, and_true]
  omega

set_option maxRecDepth 100000 in
theorem aList_length : aList.length = 256 := by decide

@[expose] def flipP (p : ℕ × ℕ) : ℕ × ℕ := (p.1, 1 - p.2)

theorem flipP_mem {p : ℕ × ℕ} (hp : p ∈ aList) : flipP p ∈ aList := by
  obtain ⟨h1, h2, h3⟩ := mem_aList.1 hp
  exact mem_aList.2 ⟨h1, h2, by rcases h3 with h | h <;> simp [flipP, h]⟩


theorem aElt_flip {p : ℕ × ℕ} (hp : p ∈ aList) : aElt p * typeSystemC.z = aElt (flipP p) := by
  obtain ⟨-, -, h3⟩ := mem_aList.1 hp
  have e1 : ∀ c : ℕ, aElt (c, 1) = yprodH c * typeSystemC.z := fun c => rfl
  have e0 : ∀ c : ℕ, aElt (c, 0) = yprodH c := fun c => rfl
  obtain ⟨c, d⟩ := p
  simp only at h3
  rcases h3 with rfl | rfl
  · exact (e1 c).symm.trans (by rw [flipP]; rfl)
  · rw [e1, flipP, mul_assoc, typeSystemC.z_mul_self, mul_one]
    exact (e0 c).symm

variable
  (k : Fin 3)

noncomputable abbrev Kc : Subgroup (TM k) := centralizer ({wT k} : Set (TM k))

theorem mem_Kc {y : TM k} : y ∈ Kc k ↔ y * wT k = wT k * y :=
  Subgroup.mem_centralizer_singleton_iff

theorem tw_mem_Kc_iff (g : FP k) : tw k g ∈ Kc k ↔ g.val.1 ∈ K₀ := by
  rw [mem_Kc, wT, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, tw_eq_tw_iff, mem_K₀]
  constructor
  · rintro (h | h)
    · have h1 : (wFib k * g : FP k).val.1 = (g * wFib k : FP k).val.1 := by rw [h]
      simp only [Subgroup.coe_mul, Prod.fst_mul, fst_wFib] at h1
      exact h1.symm
    · exfalso
      have h1 : (wFib k * g : FP k).val.2 = (g * wFib k * zζ typeSystemC (wPlusMap iotaC k)
          zPlus (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
      simp only [Subgroup.coe_mul, Prod.snd_mul, snd_wFib, snd_zζ, one_mul, mul_one] at h1
      exact zPlus_ne_one (mul_left_cancel (h1.symm.trans (mul_one _).symm))
  · intro h
    left
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simp only [Subgroup.coe_mul, Prod.fst_mul, fst_wFib]
      exact h.symm
    · simp only [Subgroup.coe_mul, Prod.snd_mul, snd_wFib, one_mul, mul_one]

@[expose] noncomputable def RFib : Subgroup (FP k) :=
  R₀.comap ((MonoidHom.fst _ _).comp (FP k).subtype)

@[expose] noncomputable def RM : Subgroup (TM k) := (RFib k).map (QuotientGroup.mk' _)

theorem mem_RM_iff {y : TM k} : y ∈ RM k ↔ ∃ g : FP k, g.val.1 ∈ R₀ ∧ tw k g = y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem tw_mem_RM {g : FP k} (hg : g.val.1 ∈ R₀) : tw k g ∈ RM k :=
  (mem_RM_iff k).2 ⟨g, hg, rfl⟩

theorem RM_le_Kc : RM k ≤ Kc k := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := (mem_RM_iff k).1 hy
  exact (tw_mem_Kc_iff k g).2 (R₀_le_K₀ hg)

@[expose] noncomputable def ψFib (c : ℕ) (p : ℕ × ℕ) : FP k :=
  ⟨(hcH c * aElt p, eHat k c), by rw [mem_fibreProd, map_mul, phi_aElt, mul_one, πk_eHat]⟩

theorem Ψ_eq (c : ℕ) (p : ℕ × ℕ) : Ψ k c p = tw k (ψFib k c p) := rfl

theorem fst_ψFib (c : ℕ) (p : ℕ × ℕ) : (ψFib k c p).val.1 = hcH c * aElt p := rfl

theorem snd_ψFib (c : ℕ) (p : ℕ × ℕ) : (ψFib k c p).val.2 = eHat k c := rfl

theorem fst_mul_zζ (g : FP k) : (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
    (wPlusMap_zPlus iotaC k) : FP k).val.1 = g.val.1 * typeSystemC.z := rfl

theorem snd_mul_zζ (g : FP k) : (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
    (wPlusMap_zPlus iotaC k) : FP k).val.2 = g.val.2 * zPlus := rfl

theorem Ψ_mem_RM {c : ℕ} (hc : c < 64) {p : ℕ × ℕ} (hp : p ∈ aList) : Ψ k c p ∈ RM k :=
  tw_mem_RM k (hcH_mul_aElt_mem hc hp)

theorem exists_Ψ_eq {y : TM k} (hy : y ∈ RM k) : ∃ c < 64, ∃ p ∈ aList, Ψ k c p = y := by
  obtain ⟨g, hg, rfl⟩ := (mem_RM_iff k).1 hy
  obtain ⟨c, hc, p, hp, hgp⟩ := mem_R₀_iff.1 hg
  have hπ : wPlusMap iotaC k ((eHat k c)⁻¹ * g.val.2) = 1 := by
    rw [map_mul, map_inv, πk_eHat, ← mem_fibreProd.1 g.2, hgp, map_mul, phi_aElt, mul_one,
      inv_mul_cancel]
  rcases (wPlusMap_eq_one_iff iotaC k).1 hπ with h1 | h1
  · refine ⟨c, hc, p, hp, ?_⟩
    have hg : ψFib k c p = g := Subtype.ext (Prod.ext hgp.symm (inv_mul_eq_one.1 h1))
    rw [Ψ_eq, hg]
  · refine ⟨c, hc, flipP p, flipP_mem hp, ?_⟩
    have e1 : g.val.1 = (ψFib k c (flipP p) * zζ typeSystemC (wPlusMap iotaC k) zPlus
        (wPlusMap_zPlus iotaC k) : FP k).val.1 := by
      rw [fst_mul_zζ, fst_ψFib, ← aElt_flip hp, hgp, mul_assoc, mul_assoc,
        typeSystemC.z_mul_self, mul_one]
    have e2 : g.val.2 = (ψFib k c (flipP p) * zζ typeSystemC (wPlusMap iotaC k) zPlus
        (wPlusMap_zPlus iotaC k) : FP k).val.2 := by
      rw [snd_mul_zζ, snd_ψFib, ← h1, mul_inv_cancel_left]
    rw [Ψ_eq, tw_eq_tw_iff]
    exact Or.inr (Subtype.ext (Prod.ext e1 e2))

theorem Ψ_inj {c c' : ℕ} (hc : c < 64) (hc' : c' < 64) {p p' : ℕ × ℕ} (hp : p ∈ aList)
    (hp' : p' ∈ aList) (h : Ψ k c p = Ψ k c' p') : c = c' ∧ p = p' := by
  rw [Ψ_eq, Ψ_eq, tw_eq_tw_iff] at h
  rcases h with h | h
  · have h1 : (ψFib k c' p').val.1 = (ψFib k c p).val.1 := by rw [h]
    obtain ⟨e1, e2⟩ := hcH_mul_aElt_inj hc' hc hp' hp h1
    exact ⟨e1.symm, e2.symm⟩
  · exfalso
    have h1 : (ψFib k c' p').val.1 = (ψFib k c p * zζ typeSystemC (wPlusMap iotaC k)
        zPlus (wPlusMap_zPlus iotaC k) : FP k).val.1 := by rw [h]
    have h2 : (ψFib k c' p').val.2 = (ψFib k c p * zζ typeSystemC (wPlusMap iotaC k)
        zPlus (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
    rw [fst_mul_zζ, fst_ψFib, fst_ψFib, mul_assoc, aElt_flip hp] at h1
    rw [snd_mul_zζ, snd_ψFib, snd_ψFib] at h2
    obtain ⟨e1, -⟩ := hcH_mul_aElt_inj hc' hc hp' (flipP_mem hp) h1
    subst e1
    exact zPlus_ne_one (mul_left_cancel (h2.symm.trans (mul_one _).symm))

abbrev Idx : Type := {q : ℕ × (ℕ × ℕ) // q.1 < 64 ∧ q.2 ∈ aList}

@[expose] noncomputable def idxEquiv : Idx ≃ RM k :=
  Equiv.ofBijective (fun q => ⟨Ψ k q.1.1 q.1.2, Ψ_mem_RM k q.2.1 q.2.2⟩)
    ⟨fun q q' h => by
      have := Ψ_inj k q.2.1 q'.2.1 q.2.2 q'.2.2 (congrArg Subtype.val h)
      exact Subtype.ext (Prod.ext this.1 this.2),
     fun y => by
      obtain ⟨c, hc, p, hp, hy⟩ := exists_Ψ_eq k y.2
      exact ⟨⟨(c, p), hc, hp⟩, Subtype.ext hy⟩⟩

theorem card_Idx : Nat.card Idx = 2 ^ 14 := by
  have e : Idx ≃ ((Finset.range 64) ×ˢ aList.toFinset : Finset (ℕ × (ℕ × ℕ))) :=
    Equiv.subtypeEquivRight fun q => by simp [Finset.mem_product]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product,
    Finset.card_range, List.toFinset_card_of_nodup aList_nodup, aList_length]
  norm_num

theorem card_RM : Nat.card (RM k) = 2 ^ 14 := by
  rw [← Nat.card_congr (idxEquiv k), card_Idx]

theorem isPGroup_RM : IsPGroup 2 (RM k) := IsPGroup.of_card (card_RM k)

end CFSG.Sporadic.Co1Patterson.TwistNative
