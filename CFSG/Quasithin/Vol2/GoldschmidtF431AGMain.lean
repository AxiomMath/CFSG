module

public import CFSG.Quasithin.Vol2.GoldschmidtF431AGBase

public section

namespace CFSG.Quasithin.H13.F431.AG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {K : Type*} [Group K]

@[expose] def BorelTitsIn (X : Subgroup K) : Prop :=
  ∀ A : Subgroup K, A ≤ X → A ≠ ⊥ → IsPGroup 2 A →
    ∃ S P : Subgroup K, IsSylowTwoOf S X ∧ P ≤ X ∧ P ≠ X ∧
      X ⊓ Subgroup.normalizer (A : Set K) ≤ P ∧
      pCoreOf 2 (X ⊓ Subgroup.normalizer (A : Set K)) ≤ pCoreOf 2 P ∧
      A ≤ pCoreOf 2 P ∧ X ⊓ Subgroup.normalizer (S : Set K) ≤ P

theorem conjSub_le_self {g : K} {H : Subgroup K} (hg : g ∈ H) : conjSub g H ≤ H := by
  rintro _ ⟨y, hy, rfl⟩
  exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)

theorem mem_normalizer_of_conjSub_eq {g : K} {H : Subgroup K} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set K) :=
  F7.mem_normalizer_of_conj_le h.le (by rw [← h, conjSub_conjSub_inv, h])

theorem conjSub_eq_of_le [Finite K] {g h : K} {H : Subgroup K} (hle : conjSub g H ≤ conjSub h H) :
    conjSub g H = conjSub h H := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hg : Nat.card (conjSub g H) = Nat.card H :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))
  have hh : Nat.card (conjSub h H) = Nat.card H :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj h))
  omega

theorem inf_normalizer_le_of_isSylowTwoOf [Finite K] {X P S T : Subgroup K} (hPX : P ≤ X)
    (hSX : IsSylowTwoOf S X) (hTX : IsSylowTwoOf T X) (hTP : T ≤ P)
    (hSP : X ⊓ Subgroup.normalizer (S : Set K) ≤ P) :
    X ⊓ Subgroup.normalizer (T : Set K) ≤ P := by
  have hSle : S ≤ P := fun s hs =>
    hSP (Subgroup.mem_inf.mpr ⟨hSX.1 hs, Subgroup.le_normalizer hs⟩)
  have hSP' : IsSylowTwoOf S P := F7.isSylowTwoOf_mono_right hSX hSle hPX
  obtain ⟨x, hxP, hxle⟩ := F7.isSylowTwoOf_exists_conj_le hSP' hTP hTX.2.1
  have hxX : x ∈ X := hPX hxP
  have hconjX : conjSub x S ≤ X := (conjSub_mono x hSX.1).trans (conjSub_le_self hxX)
  have hTeq : T = conjSub x S :=
    eq_of_le_of_isSylowTwoOf hTX hxle hconjX (F7.isPGroup_conjSub hSX.2.1)
  intro y hy
  obtain ⟨hyX, hyT⟩ := Subgroup.mem_inf.mp hy
  rw [hTeq, conjSub_normalizer, mem_conjSub] at hyT
  have hy' : x⁻¹ * y * x ∈ X ⊓ Subgroup.normalizer (S : Set K) :=
    Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem (X.inv_mem hxX) hyX) hxX, hyT⟩
  have := P.mul_mem (P.mul_mem hxP (hSP hy')) (P.inv_mem hxP)
  simpa [mul_assoc] using this

end CFSG.Quasithin.H13.F431.AG
