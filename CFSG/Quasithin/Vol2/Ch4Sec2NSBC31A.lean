module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

section Index

variable {X : Type} [Group X]

theorem isPGroup_iff_pow {p : ℕ} {Y : Subgroup X} :
    IsPGroup p ↥Y ↔ ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k = 1 := by
  constructor
  · intro h y hy
    obtain ⟨k, hk⟩ := h ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro h ⟨y, hy⟩
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem ratio_pCore [Finite X] (Nh : Subgroup X) [Nh.Normal] (h2 : IsPGroup 2 ↥Nh) :
    Nh ≤ CFSG.pCore 2 X ∧ ∃ e : ℕ, Nat.card (X ⧸ Nh) = Nat.card (X ⧸ CFSG.pCore 2 X) * 2 ^ e ∧
      (Nat.card (X ⧸ Nh) = Nat.card (X ⧸ CFSG.pCore 2 X) → CFSG.pCore 2 X = Nh) := by
  have hle : Nh ≤ CFSG.pCore 2 X := by
    unfold CFSG.pCore
    exact le_sSup ⟨inferInstance, h2⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  have hdvd : Nh.relIndex (CFSG.pCore 2 X) ∣ 2 ^ a := by
    rw [← ha]
    exact _root_.Subgroup.relIndex_dvd_card (H := Nh) (K := CFSG.pCore 2 X)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard : Nat.card (X ⧸ Nh) =
      Nat.card (X ⧸ CFSG.pCore 2 X) * Nh.relIndex (CFSG.pCore 2 X) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card, ← Subgroup.relIndex_mul_index hle,
      mul_comm]
  refine ⟨hle, e, by rw [hcard, he], fun heq => ?_⟩
  have hpos : 0 < Nat.card (X ⧸ CFSG.pCore 2 X) := Nat.card_pos
  have h1 : Nh.relIndex (CFSG.pCore 2 X) = 1 := by
    have h3 := heq
    rw [hcard] at h3
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h3, mul_one])
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle

theorem card_quot_comap {B : Type} [Group B] (φ : X →* B) (hφ : Function.Surjective φ)
    (N : Subgroup B) : Nat.card (X ⧸ N.comap φ) = Nat.card (B ⧸ N) := by
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card, Subgroup.index_comap_of_surjective (H := N) hφ]

theorem isPGroup_comap {B : Type} [Group B] (φ : X →* B) (N : Subgroup B)
    (hN : IsPGroup 2 ↥N) (hK : IsPGroup 2 ↥φ.ker) : IsPGroup 2 ↥(N.comap φ) := by
  rw [isPGroup_iff_pow] at hN hK ⊢
  intro x hx
  obtain ⟨a, ha⟩ := hN (φ x) (Subgroup.mem_comap.mp hx)
  have hker : x ^ 2 ^ a ∈ φ.ker := MonoidHom.mem_ker.mpr (by rw [map_pow]; exact ha)
  obtain ⟨b, hb⟩ := hK (x ^ 2 ^ a) hker
  exact ⟨a + b, by rw [pow_add, pow_mul]; exact hb⟩

theorem ratio_of_hom [Finite X] {B : Type} [Group B] [Finite B] (φ : X →* B)
    (hφ : Function.Surjective φ) (hK : IsPGroup 2 ↥φ.ker) (N : Subgroup B) [N.Normal]
    (hN : IsPGroup 2 ↥N) :
    ∃ e : ℕ, Nat.card (B ⧸ N) = Nat.card (X ⧸ CFSG.pCore 2 X) * 2 ^ e ∧
      (Nat.card (B ⧸ N) = Nat.card (X ⧸ CFSG.pCore 2 X) → CFSG.pCore 2 X = N.comap φ) := by
  have hNh : IsPGroup 2 ↥(N.comap φ) := isPGroup_comap φ N hN hK
  haveI : (N.comap φ).Normal := inferInstance
  obtain ⟨-, e, hcard, hcon⟩ := ratio_pCore (N.comap φ) hNh
  refine ⟨e, ?_, fun heq => hcon ((card_quot_comap φ hφ N).trans heq)⟩
  rw [← card_quot_comap φ hφ N]
  exact hcard

theorem card_le_of_pCore_eq [Finite X] {B : Type} [Group B] [Finite B] (φ : X →* B)
    (hφ : Function.Surjective φ) (N : Subgroup B) (hO : CFSG.pCore 2 X = N.comap φ)
    (W : Subgroup X) (hW : W ≤ CFSG.pCore 2 X)
    (hWφ : ∀ w ∈ W, φ w = 1 → w = 1) : Nat.card W ≤ Nat.card N := by
  have hmem : ∀ w ∈ W, φ w ∈ N := fun w hw => by
    have h := hW hw
    rw [hO] at h
    exact Subgroup.mem_comap.mp h
  refine Nat.card_le_card_of_injective (fun w : ↥W => (⟨φ w, hmem w w.2⟩ : ↥N)) ?_
  intro w1 w2 h
  have h' : φ (w1 : X) = φ (w2 : X) := congrArg Subtype.val h
  have h1 : φ ((w1 : X) * (w2 : X)⁻¹) = 1 := by rw [map_mul, map_inv, h', mul_inv_cancel]
  have h2 : (w1 : X) * (w2 : X)⁻¹ ∈ W := W.mul_mem w1.2 (W.inv_mem w2.2)
  exact Subtype.ext (mul_inv_eq_one.mp (hWφ _ h2 h1))

theorem card_le_center_of_pCore_eq [Finite X] {B : Type} [Group B] [Finite B] (φ : X →* B)
    (hφ : Function.Surjective φ) (N : Subgroup B) (hO : CFSG.pCore 2 X = N.comap φ)
    (W : Subgroup X) (hW : W ≤ CFSG.pCore 2 X)
    (hWc : ∀ w ∈ W, ∀ o ∈ CFSG.pCore 2 X, w * o = o * w)
    (hWφ : ∀ w ∈ W, φ w = 1 → w = 1) : Nat.card W ≤ Nat.card (Subgroup.center ↥N) := by
  have hmem : ∀ w ∈ W, φ w ∈ N := fun w hw => by
    have h := hW hw
    rw [hO] at h
    exact Subgroup.mem_comap.mp h
  have hcen : ∀ w (hw : w ∈ W), (⟨φ w, hmem w hw⟩ : ↥N) ∈ Subgroup.center ↥N := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := hφ g
    have hxO : x ∈ CFSG.pCore 2 X := by
      rw [hO, Subgroup.mem_comap, hx]
      exact hg
    have hc := hWc w hw x hxO
    apply Subtype.ext
    show g * φ w = φ w * g
    rw [← hx, ← map_mul, ← map_mul, hc]
  refine Nat.card_le_card_of_injective
    (fun w : ↥W => (⟨⟨φ w, hmem w w.2⟩, hcen w w.2⟩ : ↥(Subgroup.center ↥N))) ?_
  intro w1 w2 h
  have h' : φ (w1 : X) = φ (w2 : X) := congrArg (fun z : ↥(Subgroup.center ↥N) => z.1.1) h
  have h1 : φ ((w1 : X) * (w2 : X)⁻¹) = 1 := by rw [map_mul, map_inv, h', mul_inv_cancel]
  have h2 : (w1 : X) * (w2 : X)⁻¹ ∈ W := W.mul_mem w1.2 (W.inv_mem w2.2)
  exact Subtype.ext (mul_inv_eq_one.mp (hWφ _ h2 h1))

end Index

end CFSG.Quasithin.H13.Ch4.NSB
