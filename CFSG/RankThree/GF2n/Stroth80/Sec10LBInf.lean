module

public import CFSG.GroupTheory.SubgroupCardInf
public import CFSG.RankThree.GF2n.Stroth80.Sec10CQt
public import CFSG.RankThree.GF2n.Smith81.TiLemmaF

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_inf_le_mul_card_inf_inf {L₁ L₂ N : Subgroup G} {c : ℕ}
    (hN : Nat.card N ≤ c * Nat.card ↥(L₂ ⊓ N)) :
    Nat.card ↥(L₁ ⊓ N) ≤ c * Nat.card ↥(L₁ ⊓ L₂ ⊓ N) := by
  have h := card_mul_card_le_card_inf_mul_card_of_le (H := L₁ ⊓ N) (K := L₂ ⊓ N) (C := N)
    inf_le_right inf_le_right
  have hinf : (L₁ ⊓ N) ⊓ (L₂ ⊓ N) = L₁ ⊓ L₂ ⊓ N := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxL₁, hxN⟩, ⟨hxL₂, -⟩⟩
      exact ⟨⟨hxL₁, hxL₂⟩, hxN⟩
    · rintro ⟨⟨hxL₁, hxL₂⟩, hxN⟩
      exact ⟨⟨hxL₁, hxN⟩, ⟨hxL₂, hxN⟩⟩
  rw [hinf] at h
  have h2 : Nat.card ↥(L₁ ⊓ N) * Nat.card ↥(L₂ ⊓ N) ≤
      Nat.card ↥(L₁ ⊓ L₂ ⊓ N) * (c * Nat.card ↥(L₂ ⊓ N)) :=
    h.trans (Nat.mul_le_mul_left _ hN)
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := ↥(L₂ ⊓ N)))
  calc Nat.card ↥(L₁ ⊓ N) * Nat.card ↥(L₂ ⊓ N)
      ≤ Nat.card ↥(L₁ ⊓ L₂ ⊓ N) * (c * Nat.card ↥(L₂ ⊓ N)) := h2
    _ = (c * Nat.card ↥(L₁ ⊓ L₂ ⊓ N)) * Nat.card ↥(L₂ ⊓ N) := by ring

private theorem Ctx.card_pow_le_card_inf_centralizer (hc : Ctx M Q Z B) {A : Subgroup G}
    (hcA : Ctx M Q Z A) {n : ℕ} {t : G} (htB : t ∈ QB B) (htA : t ∈ QB A)
    (hB : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB B))
    (hA : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB A))
    (hC : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1)) :
    Nat.card Z ^ n * Nat.card Z ^ n ≤
      Nat.card ↥(Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) *
        Nat.card Z ^ (n + 1) := by
  have hq0 : 0 < Nat.card Z := by have h := hc.hyp.q4; omega
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  let XA : Subgroup G := Q ⊓ QB A ⊓ Subgroup.centralizer ({t} : Set G)
  let XB : Subgroup G := Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)
  have hXA : Nat.card Z ^ n ≤ Nat.card ↥XA := by
    have h1 : Nat.card Z ^ (n + 1) ≤ Nat.card Z * Nat.card ↥XA :=
      hA.trans (hcA.card_inf_QB_le_mul_card_centralizer htA)
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 hq0
  have hXB : Nat.card Z ^ n ≤ Nat.card ↥XB := by
    have h1 : Nat.card Z ^ (n + 1) ≤ Nat.card Z * Nat.card ↥XB :=
      hB.trans (hc.card_inf_QB_le_mul_card_centralizer htB)
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 hq0
  have hXA_le : XA ≤ C := by
    refine le_inf ?_ inf_le_right
    exact inf_le_left.trans inf_le_left
  have hXB_le : XB ≤ C := by
    refine le_inf ?_ inf_le_right
    exact inf_le_left.trans inf_le_left
  have hprod := card_mul_card_le_card_inf_mul_card_of_le (H := XA) (K := XB) (C := C) hXA_le hXB_le
  have hmain : Nat.card Z ^ n * Nat.card Z ^ n ≤
      Nat.card ↥(XA ⊓ XB) * Nat.card Z ^ (n + 1) :=
    calc Nat.card Z ^ n * Nat.card Z ^ n
        ≤ Nat.card ↥XA * Nat.card ↥XB := Nat.mul_le_mul hXA hXB
      _ ≤ Nat.card ↥(XA ⊓ XB) * Nat.card ↥C := hprod
      _ ≤ Nat.card ↥(XA ⊓ XB) * Nat.card Z ^ (n + 1) :=
          Nat.mul_le_mul_left _ (by simpa [C] using hC)
  have hinf : XA ⊓ XB = Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext x
    simp only [XA, XB, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨⟨hxQ, hxA⟩, hxC⟩, ⟨-, hxB⟩, -⟩
      exact ⟨⟨⟨hxQ, hxA⟩, hxB⟩, hxC⟩
    · rintro ⟨⟨⟨hxQ, hxA⟩, hxB⟩, hxC⟩
      exact ⟨⟨⟨hxQ, hxA⟩, hxC⟩, ⟨⟨hxQ, hxB⟩, hxC⟩⟩
  rwa [hinf] at hmain

theorem Ctx.card_inf_QB_inf_QB_centralizer (hc : Ctx M Q Z B) {A : Subgroup G}
    (hcA : Ctx M Q Z A) {n : ℕ} {t : G} (htB : t ∈ QB B) (htA : t ∈ QB A)
    (hB : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB B))
    (hA : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB A))
    (hC : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1)) :
    Nat.card Z ^ (n + 1) ≤
      Nat.card Z ^ 2 * Nat.card ↥(Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hq0 : 0 < Nat.card Z := by have h := hc.hyp.q4; omega
  have hmain := hc.card_pow_le_card_inf_centralizer hcA htB htA hB hA hC
  have hstep := Nat.mul_le_mul_right (Nat.card Z ^ 2) hmain
  have e1 : Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1) =
      Nat.card Z ^ (n + n + 2) := by
    rw [← pow_add]
    congr 1
    ring
  have e2 : Nat.card Z ^ n * Nat.card Z ^ n * Nat.card Z ^ 2 =
      Nat.card Z ^ (n + n + 2) := by
    rw [← pow_add, ← pow_add]
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq0 (n + 1))
  calc Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1)
      = Nat.card Z ^ n * Nat.card Z ^ n * Nat.card Z ^ 2 := by rw [e1, e2]
    _ ≤ Nat.card ↥(Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) *
          Nat.card Z ^ (n + 1) * Nat.card Z ^ 2 := hstep
    _ = (Nat.card Z ^ 2 *
          Nat.card ↥(Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G))) *
          Nat.card Z ^ (n + 1) := by ring

private theorem Ctx.LB_inf_LB_le_sup (hc : Ctx M Q Z B) {A X : Subgroup G}
    (hcA : Ctx M Q Z A) (hXQ : X ≤ Q) (hXA : X ≤ QB A) (hXB : X ≤ QB B)
    (hAB : (A ⊔ Z) ⊓ (B ⊔ Z) = Z) :
    LB M Q A ⊓ LB M Q B ≤
      ((QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G)) ⊔ Q := by
  intro l hl
  obtain ⟨hlA, hlB⟩ := Subgroup.mem_inf.mp hl
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hlB
  have hsC : s ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxQ : x ∈ Q := hXQ hx
    have hZl : ⁅x, s * y⁆ ∈ Z := by
      have hAcomm : ⁅x, s * y⁆ ∈ A ⊔ Z := by
        have h := hcA.comm_LB_inf_QB_mem_sup hlA ⟨hxQ, hXA hx⟩
        rw [sup_comm] at h
        simpa only [commutatorElement_inv] using (A ⊔ Z).inv_mem h
      have hBcomm : ⁅x, s * y⁆ ∈ B ⊔ Z := by
        have h := hc.comm_LB_inf_QB_mem_sup hlB ⟨hxQ, hXB hx⟩
        rw [sup_comm] at h
        simpa only [commutatorElement_inv] using (B ⊔ Z).inv_mem h
      have hmem : ⁅x, s * y⁆ ∈ (A ⊔ Z) ⊓ (B ⊔ Z) := Subgroup.mem_inf.mpr ⟨hAcomm, hBcomm⟩
      rwa [hAB] at hmem
    have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
    have h2 : s * ⁅x, y⁆ * s⁻¹ ∈ Z := hsZ _ (comm_mem_Z hc.hyp hxQ hy)
    have hdecomp : ⁅x, s * y⁆ = ⁅x, s⁆ * (s * ⁅x, y⁆ * s⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    have hxsZ : ⁅x, s⁆ ∈ Z := by
      have h3 := Z.mul_mem (hdecomp ▸ hZl) (Z.inv_mem h2)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h3
    have hxsB : ⁅x, s⁆ ∈ B := hc.comm_QB_le_B (hXB hx) hs.1
    have h1 : ⁅x, s⁆ = 1 := by
      have hmem : ⁅x, s⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hxsZ, hxsB⟩
      rwa [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hsK : s ∈ (QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs, hsC⟩
  exact ((QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ⊔ Q).mul_mem
    (Subgroup.mem_sup_left hsK) (Subgroup.mem_sup_right hy)

private theorem Ctx.inf_QB_le_inf_sup (hc : Ctx M Q Z B) {X : Subgroup G} (hXQ : X ≤ Q)
    (hXB : X ≤ QB B) :
    Q ⊓ QB B ≤ ((QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G)) ⊓ Q := by
  refine le_inf (le_inf (le_inf inf_le_right ((inf_le_left).trans (cqt_Q_le_M hc.hyp))) ?_)
    inf_le_left
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hZ : ⁅x, w⁆ ∈ Z := comm_mem_Z hc.hyp hx.1 (hXQ hw)
  have hB : ⁅x, w⁆ ∈ B := hc.comm_QB_le_B hx.2 (hXB hw)
  have h1 : ⁅x, w⁆ = 1 := by
    have hmem : ⁅x, w⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hZ, hB⟩
    rwa [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem Ctx.card_inf_QB_inf_centralizer_mul_card_le (hc : Ctx M Q Z B)
    {X : Subgroup G} (hBX : B ≤ X) (hXQB : X ≤ QB B) {n : ℕ} (hw : Width Q Z n) :
    Nat.card ↥((QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G)) * Nat.card X ≤
      Nat.card Z ^ (2 * n + 2) := by
  let K₀ : Subgroup G := (QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G)
  have hKleWt : K₀ ≤ Wt (QB B) X :=
    le_inf (fun x hx => (Subgroup.mem_inf.mp hx).1.1) (fun x hx => (Subgroup.mem_inf.mp hx).2)
  have hcardKle : Nat.card ↥K₀ ≤ Nat.card ↥(Wt (QB B) X) :=
    Nat.card_le_card_of_injective
      (fun y : ↥K₀ => (⟨y.1, hKleWt y.2⟩ : ↥(Wt (QB B) X)))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥(Wt (QB B) X) => (z : G)) h))
  obtain ⟨g, hg⟩ := hc.conj
  have hH : StrothHyp (conjSubgroup g M) (QB B) B := by
    have h := StrothHyp.conj hc.hyp g
    rwa [← (Ctx.QB_eq hc hg).2, ← hg] at h
  have hStroth : Nat.card ↥(Wt (QB B) X) * Nat.card X ≤ Nat.card (QB B) * Nat.card B :=
    StrothHyp.card_Wt_mul_card_le hH hXQB hBX
  have hQBcard : Nat.card (QB B) = Nat.card Q := by
    rw [(Ctx.QB_eq hc hg).2, card_conjSubgroup]
  have hBcard : Nat.card B = Nat.card Z := by rw [hg, card_conjSubgroup]
  have hw' : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hw
  calc Nat.card ↥K₀ * Nat.card X
      ≤ Nat.card ↥(Wt (QB B) X) * Nat.card X := Nat.mul_le_mul_right _ hcardKle
    _ ≤ Nat.card (QB B) * Nat.card B := hStroth
    _ = Nat.card Q * Nat.card Z := by rw [hQBcard, hBcard]
    _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := by rw [hw']
    _ = Nat.card Z ^ (2 * n + 2) := by rw [← pow_succ]

theorem Ctx.card_LB_inf_LB_le (hc : Ctx M Q Z B) {A : Subgroup G} (hcA : Ctx M Q Z A)
    {n : ℕ} (hw : Width Q Z n) {X : Subgroup G} (hBX : B ≤ X) (hXQ : X ≤ Q) (hXA : X ≤ QB A)
    (hXB : X ≤ QB B) (hX : Nat.card Z ^ (n + 1) ≤ Nat.card Z ^ 2 * Nat.card X)
    (hAB : (A ⊔ Z) ⊓ (B ⊔ Z) = Z) (hQB : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Q ⊓ QB B)) :
    Nat.card ↥(LB M Q A ⊓ LB M Q B) ≤ Nat.card Z ^ 2 * Nat.card Q := by
  have hq0 : 0 < Nat.card Z := by have h := hc.hyp.q4; omega
  let K₀ : Subgroup G := (QB B ⊓ M) ⊓ Subgroup.centralizer (X : Set G)
  have hLBsup : LB M Q A ⊓ LB M Q B ≤ K₀ ⊔ Q :=
    hc.LB_inf_LB_le_sup hcA hXQ hXA hXB hAB
  have hQBK : Q ⊓ QB B ≤ K₀ ⊓ Q := hc.inf_QB_le_inf_sup hXQ hXB
  have hKnorm : K₀ ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    hc.hyp.Q_normal.2 (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hprod : Nat.card ↥(K₀ ⊔ Q) * Nat.card ↥(K₀ ⊓ Q) =
      Nat.card Q * Nat.card ↥K₀ := by
    have h := card_sup_mul_card_inf_of_normalizer (A := Q) (C := K₀) hKnorm
    rwa [sup_comm Q K₀, inf_comm Q K₀] at h
  have hLle : Nat.card ↥(LB M Q A ⊓ LB M Q B) ≤ Nat.card ↥(K₀ ⊔ Q) :=
    Nat.card_le_card_of_injective
      (fun y : ↥(LB M Q A ⊓ LB M Q B) => (⟨y.1, hLBsup y.2⟩ : ↥(K₀ ⊔ Q)))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥(K₀ ⊔ Q) => (z : G)) h))
  have hi : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(K₀ ⊓ Q) :=
    hQB.trans (Nat.card_le_card_of_injective
      (fun y : ↥(Q ⊓ QB B) => (⟨y.1, hQBK y.2⟩ : ↥(K₀ ⊓ Q)))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥(K₀ ⊓ Q) => (z : G)) h)))
  have hkX : Nat.card ↥K₀ * Nat.card X ≤ Nat.card Z ^ (2 * n + 2) :=
    hc.card_inf_QB_inf_centralizer_mul_card_le hBX hXB hw
  have hstep : Nat.card ↥(LB M Q A ⊓ LB M Q B) *
        (Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1))
      ≤ Nat.card ↥(K₀ ⊔ Q) *
        (Nat.card ↥(K₀ ⊓ Q) * (Nat.card Z ^ 2 * Nat.card X)) :=
    Nat.mul_le_mul hLle (Nat.mul_le_mul hi hX)
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq0 (2 * n + 2))
  calc Nat.card ↥(LB M Q A ⊓ LB M Q B) * Nat.card Z ^ (2 * n + 2)
      = Nat.card ↥(LB M Q A ⊓ LB M Q B) *
          (Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1)) := by
        rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, pow_add]
    _ ≤ Nat.card ↥(K₀ ⊔ Q) *
          (Nat.card ↥(K₀ ⊓ Q) * (Nat.card Z ^ 2 * Nat.card X)) := hstep
    _ = (Nat.card Q * Nat.card ↥K₀) * (Nat.card Z ^ 2 * Nat.card X) := by
        rw [← mul_assoc, hprod]
    _ = Nat.card Z ^ 2 * Nat.card Q * (Nat.card ↥K₀ * Nat.card X) := by ring
    _ ≤ Nat.card Z ^ 2 * Nat.card Q * Nat.card Z ^ (2 * n + 2) :=
        Nat.mul_le_mul_left _ hkX
    _ = (Nat.card Z ^ 2 * Nat.card Q) * Nat.card Z ^ (2 * n + 2) := by ring

end CFSG.RankThree.GF2n.Stroth80
