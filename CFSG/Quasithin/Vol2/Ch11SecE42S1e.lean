module

public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch11SecEFacts7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

variable {G : Type} [Group G]

theorem autOn_eq_of_isSimpleGroup {H K W : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hs : IsSimpleGroup ↥(autOn H W))
    (hne : autOn K W ≠ ⊥) : autOn K W = autOn H W := by
  have hle : autOn K W ≤ autOn H W := InternalSec.autOn_le_autOn_of_le hKH
  have hN : ((autOn K W).subgroupOf (autOn H W)).Normal :=
    ⟨fun a ha b => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using InternalSec.autOn_normal_of hHK _ b.2 _ ha⟩
  rcases hs.eq_bot_or_eq_top_of_normal ((autOn K W).subgroupOf (autOn H W)) with h0 | h0
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hle hx⟩ : ↥(autOn H W)) ∈ (autOn K W).subgroupOf (autOn H W) := hx
    rw [h0, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h0)

theorem nonempty_autOn_equiv_of_sup {H K W : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {Z : Type} [Group Z] [IsSimpleGroup Z]
    (e : ↥(autOn H W) ≃* Z) (hne : autOn K W ≠ ⊥) : Nonempty (↥(autOn K W) ≃* Z) :=
  ⟨(MulEquiv.subgroupCongr (autOn_eq_of_isSimpleGroup hKH hHK e.isSimpleGroup hne)).trans e⟩

namespace List701Excl

variable {Y : Type} [Group Y]

theorem psl2 {m : ℕ} (h : LieModel Y .PSL 2 2 m) : List701Excl Y := Or.inl ⟨m, h⟩

theorem sl3 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 3) K) : List701Excl Y :=
  Or.inr (Or.inl ⟨K, inferInstance, inferInstance, m, hK, Or.inl ⟨e⟩⟩)

theorem sp4 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (e : Y ≃* ↥(StatedSp 2 K)) : List701Excl Y :=
  Or.inr (Or.inl ⟨K, inferInstance, inferInstance, m, hK, Or.inr (Or.inl ⟨e⟩)⟩)

theorem g2 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (e : Y ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : List701Excl Y :=
  Or.inr (Or.inl ⟨K, inferInstance, inferInstance, m, hK, Or.inr (Or.inr (Or.inl ⟨e⟩))⟩)

theorem sl2 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (π : ↥(StatedSL 2 K) →* Y) (hπ : Function.Surjective π) : List701Excl Y :=
  Or.inr (Or.inl ⟨K, inferInstance, inferInstance, m, hK, Or.inr (Or.inr (Or.inr ⟨π, hπ⟩))⟩)

theorem a5 (e : Y ≃* alternatingGroup (Fin 5)) : List701Excl Y := Or.inr (Or.inr (Or.inl ⟨e⟩))

theorem a6 (e : Y ≃* alternatingGroup (Fin 6)) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))

theorem a7 (e : Y ≃* alternatingGroup (Fin 7)) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))

theorem threeA6 (hp : Group.IsPerfect Y) (hc : Nat.card (Subgroup.center Y) = 3)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hc, ⟨e⟩⟩)))))

theorem sl4 (e : Y ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))

theorem sl5 (e : Y ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))

theorem m24 (e : Y ≃* ↥NativeSporadic.M24) : List701Excl Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))))

theorem sl3two (e : Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : List701Excl Y :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  sl3 (m := 1) (by simp) e

end List701Excl

end CFSG.Quasithin.Vol2.Ch11.SecE
