module

public import CFSG.Quasithin.Background.A1cModuleUnits

public section

namespace CFSG.Quasithin

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

@[expose, instance_reducible] def subAction {L : Subgroup Q} (hL : IsInv A L) :
    MulDistribMulAction A ↥L where
  smul a l := ⟨a • (l : Q), hL a l l.2⟩
  one_smul l := Subtype.ext (one_smul A (l : Q))
  mul_smul a b l := Subtype.ext (mul_smul a b (l : Q))
  smul_mul a l l' := Subtype.ext (smul_mul' a (l : Q) l')
  smul_one a := Subtype.ext (smul_one a)

variable (A) in
@[expose] def aut (L : Subgroup Q) : Subgroup (MulAut ↥L) where
  carrier := {φ | ∀ (a : A) (l l' : ↥L),
    a • (l : Q) = (l' : Q) ↔ a • ((φ l : ↥L) : Q) = ((φ l' : ↥L) : Q)}
  one_mem' := fun _ _ _ => Iff.rfl
  mul_mem' := fun {φ ψ} hφ hψ a l l' => (hψ a l l').trans (hφ a (ψ l) (ψ l'))
  inv_mem' := fun {φ} hφ a l l' => by
    have h := hφ a (φ⁻¹ l) (φ⁻¹ l')
    rw [MulAut.apply_inv_self, MulAut.apply_inv_self] at h
    exact h.symm

theorem mem_aut_iff {L : Subgroup Q} {φ : MulAut ↥L} :
    φ ∈ aut A L ↔ ∀ (a : A) (l l' : ↥L),
      a • (l : Q) = (l' : Q) ↔ a • ((φ l : ↥L) : Q) = ((φ l' : ↥L) : Q) := Iff.rfl

theorem aut_eq_eqvAut {L : Subgroup Q} (hL : IsInv A L) :
    aut A L = @eqvAut A _ ↥L _ (subAction hL) := by
  let := subAction hL
  ext φ
  rw [mem_aut_iff, mem_eqvAut_iff]
  constructor
  · intro h a w
    have h1 := (h a w (a • w)).1 rfl
    exact Subtype.ext h1.symm
  · intro h a l l'
    constructor
    · intro h1
      have h2 : a • l = l' := Subtype.ext h1
      rw [← h2, h a l]
      rfl
    · intro h1
      have h2 : φ (a • l) = φ l' := by rw [h a l]; exact Subtype.ext h1
      have h3 : a • l = l' := φ.injective h2
      exact congrArg Subtype.val h3

theorem map_fixed_subAction {L : Subgroup Q} (hL : IsInv A L) :
    (@fixed A _ ↥L _ (subAction hL) ⊤).map L.subtype = fixed A L := by
  let := subAction hL
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun a => congrArg Subtype.val (hw.2 a)⟩
  · intro hq
    exact ⟨⟨q, hq.1⟩, ⟨trivial, fun a => Subtype.ext (hq.2 a)⟩, rfl⟩

theorem map_commOf_subAction {L : Subgroup Q} (hL : IsInv A L) :
    (@commOf A _ ↥L _ (subAction hL) ⊤).map L.subtype = commOf A L := by
  let := subAction hL
  unfold commOf
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨a, l, _, rfl⟩, rfl⟩
    exact ⟨a, l, l.2, rfl⟩
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨_, ⟨a, ⟨l, hl⟩, trivial, rfl⟩, rfl⟩

theorem isIrrSec_subAction {L : Subgroup Q} (hL : IsInv A L) (h : IsIrrSec A (fixed A L) L) :
    @IsIrrSec A _ ↥L _ (subAction hL) (@fixed A _ ↥L _ (subAction hL) ⊤) ⊤ := by
  let := subAction hL
  have hmapC := map_fixed_subAction hL
  have hmapT : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨?_, fun J hJ hCJ _ => ?_⟩
  · refine lt_of_le_of_ne le_top fun hc => h.1.ne ?_
    rw [← hmapC, hc, hmapT]
  · have hJinv : IsInv A (J.map L.subtype) := by
      rintro a _ ⟨w, hw, rfl⟩
      exact ⟨a • w, hJ a w hw, rfl⟩
    have hCle : fixed A L ≤ J.map L.subtype := by
      rw [← hmapC]
      exact Subgroup.map_mono hCJ
    have hle : J.map L.subtype ≤ L := Subgroup.map_subtype_le J
    rcases h.2 _ hJinv hCle hle with h1 | h1
    · left
      exact Subgroup.map_injective (Subgroup.subtype_injective L) (h1.trans hmapC.symm)
    · right
      exact Subgroup.map_injective (Subgroup.subtype_injective L) (h1.trans hmapT.symm)

theorem eqvAut_cyclic_odd_of_isIrrPlus [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {I : Subgroup Q}
    (hI : IsIrrPlus A I) (hO2 : IsTwoReduced A I) :
    letI := subAction hI.1
    (∃ f : eqvAut A ↥I →* eqvAut A (↥I ⧸ fixed A (⊤ : Subgroup ↥I)), Function.Injective f) ∧
    (Finite ↥(eqvEnd A (↥I ⧸ fixed A (⊤ : Subgroup ↥I))) ∧
      IsField ↥(eqvEnd A (↥I ⧸ fixed A (⊤ : Subgroup ↥I))) ∧
      CharP ↥(eqvEnd A (↥I ⧸ fixed A (⊤ : Subgroup ↥I))) 2) ∧
    IsCyclic ↥(eqvAut A ↥I) ∧ Odd (Nat.card ↥(eqvAut A ↥I)) := by
  obtain ⟨hinv, hcomm, hirr⟩ := hI
  let := subAction hinv
  have hP : ∀ w : ↥I, w ^ 2 = 1 := fun w => Subtype.ext (hQ w)
  have hcomm' : commOf A (⊤ : Subgroup ↥I) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective I)
    rw [map_commOf_subAction hinv, hcomm, Subgroup.map_top, Subgroup.range_subtype]
  have hirr' := isIrrSec_subAction hinv hirr
  have hO2' : IsTwoReduced A (⊤ : Subgroup ↥I) := by
    intro D hD hDk d hd w _
    have h1 : ∀ d ∈ D, ∃ k : ℕ, ∀ l ∈ I, (d ^ 2 ^ k) • l = l := fun d hd =>
      (hDk d hd).imp fun k hk l hl => congrArg Subtype.val (hk ⟨l, hl⟩ trivial)
    exact Subtype.ext (hO2 D hD h1 d hd w w.2)
  exact eqvAut_cyclic_odd (A := A) (P := ↥I) hP hcomm' hirr' hO2'

theorem isCyclic_aut_of_isIrrPlus [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {I : Subgroup Q}
    (hI : IsIrrPlus A I) (hO2 : IsTwoReduced A I) :
    IsCyclic ↥(aut A I) ∧ Odd (Nat.card ↥(aut A I)) := by
  have h := (eqvAut_cyclic_odd_of_isIrrPlus hQ hI hO2).2.2
  rw [aut_eq_eqvAut hI.1]
  exact h

end XMod

end CFSG.Quasithin
