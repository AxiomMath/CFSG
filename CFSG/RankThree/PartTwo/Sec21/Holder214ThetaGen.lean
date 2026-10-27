module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EThmA
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.KFacts
open Hering214Even

section General

variable {N : Type*} [Group N]

theorem mulAut_mul_conj_mul_inv (σ : MulAut N) (x : N) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem apply_eq_of_commute_conj (hZ : Subgroup.center N = ⊥) {σ : MulAut N} {x : N}
    (h : MulAut.conj x * σ = σ * MulAut.conj x) : σ x = x := by
  apply KS14.conj_injective_of_center_eq_bot hZ
  rw [← mulAut_mul_conj_mul_inv, ← h, mul_inv_cancel_right]

theorem noInvol_of_fixSub [Finite N] (hZ : Subgroup.center N = ⊥)
    (hAut : Nat.card (MulAut N) ≤ 2 * Nat.card N)
    (hfix : ∀ w : MulAut N, orderOf w = 2 →
      ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w))
    (F : Subgroup (MulAut N)) (hF : IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (t : MulAut N) (ht : t ∈ Subgroup.centralizer (F : Set (MulAut N))) (ht2 : t ^ 2 = 1) :
    t = 1 := by
  by_contra ht1
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hinj := KS14.conj_injective_of_center_eq_bot hZ
  set F₀ : Subgroup N := F.comap (MulAut.conj : N →* MulAut N) with hF₀
  have hFin : F ≤ (MulAut.conj : N →* MulAut N).range := by
    intro f hf
    obtain ⟨y, rfl⟩ := KS14.exists_conj_of_card_mulAut_le hZ hAut f ⟨1, by
      rw [pow_one]; exact hF.2 f hf⟩
    exact ⟨y, rfl⟩
  have hmap : F₀.map (MulAut.conj : N →* MulAut N) = F :=
    Subgroup.map_comap_eq_self hFin
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [← hF9, ← hmap, Subgroup.card_map_of_injective hinj]
  have hle : F₀ ≤ CFSG.Sporadic.Schreier.fixSub t := by
    intro x hx
    rw [CFSG.Sporadic.Schreier.mem_fixSub]
    exact apply_eq_of_commute_conj hZ (Subgroup.mem_centralizer_iff.mp ht _ hx)
  exact hfix t hto (hF₀9 ▸ Subgroup.card_dvd_of_le hle)

theorem noInvol_of_fixNine (hZ : Subgroup.center N = ⊥)
    (H : ∀ E : Subgroup N, Nat.card E = 9 → ∀ σ : MulAut N, σ ^ 2 = 1 →
      (∀ e ∈ E, σ e = e) → σ = 1)
    (F : Subgroup (MulAut N)) (hFin : F ≤ (MulAut.conj : N →* MulAut N).range)
    (hF9 : Nat.card F = 9) (t : MulAut N) (ht : t ∈ Subgroup.centralizer (F : Set (MulAut N)))
    (ht2 : t ^ 2 = 1) : t = 1 := by
  have h9 : Nat.card (F.comap (MulAut.conj : N →* MulAut N)) = 9 := by
    rw [← Subgroup.card_map_of_injective (KS14.conj_injective_of_center_eq_bot hZ),
      Subgroup.map_comap_eq_self hFin, hF9]
  exact H _ h9 t ht2 fun x hx =>
    apply_eq_of_commute_conj hZ (Subgroup.mem_centralizer_iff.mp ht _ hx)

theorem false_of_noInvol
    (h : ∀ F : Subgroup (MulAut N), F ≤ (MulAut.conj : N →* MulAut N).range →
      IsElemAbelian 3 F → Nat.card F = 9 →
        ∀ t ∈ Subgroup.centralizer (F : Set (MulAut N)), t ^ 2 = 1 → t = 1)
    {Ē Ū : Subgroup (MulAut N)} (hĒ : Ē ≤ (MulAut.conj : N →* MulAut N).range)
    (hĒ3 : IsElemAbelian 3 Ē) (hĒ9 : Nat.card Ē = 9) (hŪ : IsElemAbelian 2 Ū) (hŪ1 : Ū ≠ ⊥)
    (hcomm : ∀ u ∈ Ū, ∀ e ∈ Ē, u * e = e * u) : False := by
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hŪ1
  refine hu1 (Subtype.ext ?_)
  rw [Subgroup.coe_one]
  refine h Ē hĒ hĒ3 hĒ9 _ (Subgroup.mem_centralizer_iff.mpr fun e he => ?_) (hŪ.2 _ u.2)
  exact (hcomm _ u.2 e he).symm

theorem isElemAbelian_e9Basis (B : Asc83Table.E9Basis N) : IsElemAbelian 3 B.sub := by
  refine ⟨⟨⟨fun c d => Subtype.ext ?_⟩⟩, fun c hc => ?_⟩
  · obtain ⟨i, j, -, -, hci⟩ := B.exists_pow_mul_pow c.2
    obtain ⟨k, l, -, -, hdk⟩ := B.exists_pow_mul_pow d.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hci, hdk]
    exact ((((Commute.refl B.a).pow_pow i k).mul_right (B.hab.pow_pow i l)).mul_left
      ((B.hab.symm.pow_pow j k).mul_right ((Commute.refl B.b).pow_pow j l))).eq
  · obtain ⟨i, j, -, -, rfl⟩ := B.exists_pow_mul_pow hc
    rw [(B.hab.pow_pow i j).mul_pow, pow_right_comm, B.ha, one_pow, pow_right_comm, B.hb,
      one_pow, one_mul]

theorem exists_e9_of_e9Basis {N' : Type*} [Group N'] (B : Asc83Table.E9Basis N) (e : N ≃* N') :
    ∃ Q : Subgroup N', IsElemAbelian 3 Q ∧ Nat.card Q = 9 :=
  ⟨_, isElemAbelian_e9Basis (B.map e.toMonoidHom e.injective),
    (B.map e.toMonoidHom e.injective).card⟩

end General

theorem evenThetaFacts_of_fixNine {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (hF1 : ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range)
    (hF2 : ∃ Q : Subgroup X, IsElemAbelian 3 Q ∧ Nat.card Q = 9)
    (H : ∀ E : Subgroup X, Nat.card E = 9 → ∀ σ : MulAut X, σ ^ 2 = 1 →
      (∀ e ∈ E, σ e = e) → σ = 1) :
    EvenThetaFacts X := by
  refine ⟨hZ, hF1, hF2, fun Ē Ū hĒ hĒ3 hĒ9 hŪ hŪ1 _ hcomm => ?_⟩
  exact (false_of_noInvol (fun F hFin _ hF9 t ht ht2 => noInvol_of_fixNine hZ H F hFin hF9 t ht ht2)
    hĒ hĒ3 hĒ9 hŪ hŪ1 hcomm).elim

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
