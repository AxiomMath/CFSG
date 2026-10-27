module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem card_le_card_inf_ker_mul {E : Type*} [AddCommGroup E] [Finite E] (ε : E →+ E)
    (A T : AddSubgroup E) (h : ∀ a ∈ A, ε a ∈ T) :
    Nat.card ↥A ≤ Nat.card ↥(A ⊓ ε.ker) * Nat.card ↥T := by
  have hmap : A.map ε ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hA : ε.ker.relIndex A * Nat.card ↥(ε.ker ⊓ A) = Nat.card ↥A :=
    AddSubgroup.relIndex_mul_card ε.ker A
  have hrel : ε.ker.relIndex A = Nat.card ↥(A.map ε) := by
    rw [AddSubgroup.relIndex_ker]
  have hle : Nat.card ↥(A.map ε) ≤ Nat.card ↥T := AddSubgroup.card_le_of_le hmap
  rw [inf_comm A ε.ker]
  calc Nat.card ↥A = ε.ker.relIndex A * Nat.card ↥(ε.ker ⊓ A) := hA.symm
    _ = Nat.card ↥(A.map ε) * Nat.card ↥(ε.ker ⊓ A) := by rw [hrel]
    _ ≤ Nat.card ↥T * Nat.card ↥(ε.ker ⊓ A) := Nat.mul_le_mul hle le_rfl
    _ = Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥T := mul_comm _ _

theorem card_ker_mul_le_filtration {E : Type*} [AddCommGroup E] [Finite E] (ε : E →+ E)
    (S A : AddSubgroup E) (hSA : S ≤ A) (hεS : ∀ s ∈ S, ε s ∈ S) (hεA : ∀ a ∈ A, ε a ∈ A) :
    Nat.card ↥ε.ker * Nat.card ↥S * Nat.card ↥A ≤
      Nat.card ↥(S ⊓ ε.ker) * Nat.card ↥(A ⊓ S.comap ε) * Nat.card ↥(A.comap ε) := by
  have hsupA : ε.ker ⊔ A ≤ A.comap ε := by
    refine sup_le ?_ ?_
    · intro k hk
      rw [AddSubgroup.mem_comap, AddMonoidHom.mem_ker.mp hk]
      exact A.zero_mem
    · intro a ha
      exact AddSubgroup.mem_comap.mpr (hεA a ha)
  have ha : Nat.card ↥ε.ker * Nat.card ↥A ≤ Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥(A.comap ε) := by
    have hid := card_sup_mul_card_inf_addSubgroup ε.ker A
    have hle : Nat.card ↥(ε.ker ⊔ A) ≤ Nat.card ↥(A.comap ε) := AddSubgroup.card_le_of_le hsupA
    calc Nat.card ↥ε.ker * Nat.card ↥A
        = Nat.card ↥(ε.ker ⊔ A) * Nat.card ↥(ε.ker ⊓ A) := hid.symm
      _ ≤ Nat.card ↥(A.comap ε) * Nat.card ↥(ε.ker ⊓ A) := Nat.mul_le_mul hle le_rfl
      _ = Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥(A.comap ε) := mul_comm _ _
  have hinf : (ε.ker ⊓ A) ⊓ S = ε.ker ⊓ S := by
    rw [inf_assoc, inf_eq_right.mpr hSA]
  have hsupS : (ε.ker ⊓ A) ⊔ S ≤ A ⊓ S.comap ε := by
    refine sup_le ?_ ?_
    · intro x hx
      have hxK : x ∈ ε.ker := (AddSubgroup.mem_inf.mp hx).1
      have hxA : x ∈ A := (AddSubgroup.mem_inf.mp hx).2
      refine AddSubgroup.mem_inf.mpr ⟨hxA, ?_⟩
      rw [AddSubgroup.mem_comap, AddMonoidHom.mem_ker.mp hxK]
      exact S.zero_mem
    · intro s hs
      refine AddSubgroup.mem_inf.mpr ⟨hSA hs, ?_⟩
      exact AddSubgroup.mem_comap.mpr (hεS s hs)
  have hb : Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥S ≤
      Nat.card ↥(ε.ker ⊓ S) * Nat.card ↥(A ⊓ S.comap ε) := by
    have hid := card_sup_mul_card_inf_addSubgroup (ε.ker ⊓ A) S
    rw [hinf] at hid
    have hle : Nat.card ↥((ε.ker ⊓ A) ⊔ S) ≤ Nat.card ↥(A ⊓ S.comap ε) :=
      AddSubgroup.card_le_of_le hsupS
    calc Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥S
        = Nat.card ↥((ε.ker ⊓ A) ⊔ S) * Nat.card ↥(ε.ker ⊓ S) := hid.symm
      _ ≤ Nat.card ↥(A ⊓ S.comap ε) * Nat.card ↥(ε.ker ⊓ S) := Nat.mul_le_mul hle le_rfl
      _ = Nat.card ↥(ε.ker ⊓ S) * Nat.card ↥(A ⊓ S.comap ε) := mul_comm _ _
  rw [inf_comm S ε.ker]
  calc Nat.card ↥ε.ker * Nat.card ↥S * Nat.card ↥A
      = (Nat.card ↥ε.ker * Nat.card ↥A) * Nat.card ↥S := by ring
    _ ≤ (Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥(A.comap ε)) * Nat.card ↥S :=
        Nat.mul_le_mul ha le_rfl
    _ = Nat.card ↥(A.comap ε) * (Nat.card ↥(ε.ker ⊓ A) * Nat.card ↥S) := by ring
    _ ≤ Nat.card ↥(A.comap ε) * (Nat.card ↥(ε.ker ⊓ S) * Nat.card ↥(A ⊓ S.comap ε)) :=
        Nat.mul_le_mul le_rfl hb
    _ = Nat.card ↥(ε.ker ⊓ S) * Nat.card ↥(A ⊓ S.comap ε) * Nat.card ↥(A.comap ε) := by ring

end CFSG.RankThree.GF2n.Stroth80
