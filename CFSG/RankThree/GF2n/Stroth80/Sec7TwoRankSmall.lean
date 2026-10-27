module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Engine
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Local
public import CFSG.Quasithin.Background.Harris.Ln2.PermRank
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem card_le_of_elemAbelian_of_alt {X : Type} [Group X] {k : ℕ}
    (e : X ≃* alternatingGroup (Fin k)) {A : Subgroup X} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ (k / 2) := by
  let φ : X →* Equiv.Perm (Fin k) := (alternatingGroup (Fin k)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hc : ∀ a ∈ A.map φ, ∀ b ∈ A.map φ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (fun x : A => φ x) h
  have h2 : ∀ a ∈ A.map φ, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have h := CFSG.Quasithin.G11.Harris.Ln2.card_le_of_elemAbelian_perm hc h2
  rwa [Subgroup.card_map_of_injective hφ, Fintype.card_fin] at h

theorem isSporadic_top {X : Type} [Group X] {s : TauCeti.SporadicName} (h : IsSporadic X s) :
    IsSporadic (⊤ : Subgroup X) s := by
  obtain ⟨e⟩ := h
  exact ⟨Subgroup.topEquiv.trans e⟩

theorem twoRankSporadicAlt_holds : TwoRankSporadicAltStatement := by
  intro X _ _ hX A hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have h := hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hinv : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  rcases hX with ⟨k, hk6, hk9, ⟨e⟩⟩ | h22 | h23 | h24
  · have h := card_le_of_elemAbelian_of_alt e hA
    have hk : 2 ^ (k / 2) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact h.trans hk
  · have h := CFSG.EvenSporadicStandard.M22Std.m22_rankFour (isSporadic_top h22) A le_top
      hcomm hinv
    omega
  · have h := CFSG.EvenSporadicStandard.M23Std.m23_rankFour (isSporadic_top h23) A le_top
      hcomm hinv
    omega
  · have h := CFSG.EvenSporadicStandard.M24Std.card_le_of_elemAbelian h24 A hcomm hinv
    omega

end CFSG.RankThree.GF2n.Stroth80

end
