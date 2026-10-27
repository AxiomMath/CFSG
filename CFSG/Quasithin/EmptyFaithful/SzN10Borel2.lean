module

public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.EmptyFaithful.SzN8Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.EscapingLocal

section Generic

theorem szN10_isPGroup_comap {Γ A : Type*} [Group Γ] [Group A] {p : ℕ} (Ψ : Γ →* A)
    (hk : IsPGroup p Ψ.ker) {S : Subgroup A} (hS : IsPGroup p S) : IsPGroup p (S.comap Ψ) := by
  intro x
  obtain ⟨k, hk1⟩ := hS ⟨Ψ x, x.2⟩
  have h1 : Ψ ((x : Γ) ^ p ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk1
  obtain ⟨j, hj⟩ := hk ⟨(x : Γ) ^ p ^ k, MonoidHom.mem_ker.mpr h1⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have := congrArg Subtype.val hj
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem szN10_isPGroup_sup {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) :
    IsPGroup 2 ↥(A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have hc := szN8_card_sup_mul_card_inf hAB
  rw [ha, hb, ← pow_add] at hc
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hc)
  exact IsPGroup.of_card hk

theorem szN10_mem_normalizer_subgroupOf {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X)
    (x : ↥X) : x ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (x : Y) ∈ Subgroup.normalizer (S : Set Y) := by
  have h := A312.mem_normalizer_map_subtype_iff X (S.subgroupOf X) x
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX] at h

end Generic

section BorelEq

variable {G : Type} [Group G] [Finite G]

theorem szN10_borel_eq {L V M₁ S₀ : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hker : ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) → l ∈ pCoreOf 2 L)
    (hM₁L : M₁ ≤ L) (hS₀ : IsSylowTwoOf S₀ L) (hS₀M : S₀ ≤ M₁)
    (hBor : ∃ S' : Subgroup (MulAut ↥V), IsSylowTwoOf S' (autOn L V) ∧
      autOn M₁ V = autOn L V ⊓ Subgroup.normalizer (S' : Set (MulAut ↥V))) :
    M₁ = L ⊓ Subgroup.normalizer (S₀ : Set G) := by
  classical
  obtain ⟨S', hS', hB⟩ := hBor
  have hΨs := S153D.autOnHom_surjective hLN
  let Ψ : ↥L →* ↥(autOn L V) := S153D.autOnHom hLN
  let S'' : Subgroup ↥(autOn L V) := S'.subgroupOf (autOn L V)
  let P : Subgroup ↥L := S''.comap Ψ
  have hΨc : ∀ l : ↥L, ((Ψ l : ↥(autOn L V)) : MulAut ↥V) = conjAct V ⟨l, hLN l.2⟩ := fun l => rfl
  have hkerΨ : IsPGroup 2 Ψ.ker := by
    intro x
    have hx : ((x : ↥L) : G) ∈ pCoreOf 2 L :=
      hker _ (x : ↥L).2 ((S153D.autOnHom_eq_one_iff hLN _).mp (MonoidHom.mem_ker.mp x.2))
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥(pCoreOf 2 L) => (y : G)) hk
    simpa using this
  have hS''2 : IsPGroup 2 ↥S'' := hS'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS'.1).symm
  have hP2 : IsPGroup 2 P := szN10_isPGroup_comap Ψ hkerΨ hS''2
  have hPSyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, hP2, ?_⟩
    have h1 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
    rw [h1, Subgroup.index_comap_of_surjective _ hΨs]
    exact hS'.2.2
  let Pg : Subgroup G := P.map L.subtype
  have hPgSyl : IsSylowTwoOf Pg L := isSylowTwoOf_map_subtype hPSyl
  have hnormP : ∀ x : ↥L, x ∈ Subgroup.normalizer (P : Set ↥L) ↔
      ((Ψ x : ↥(autOn L V)) : MulAut ↥V) ∈ Subgroup.normalizer (S' : Set (MulAut ↥V)) := by
    intro x
    have h1 := Subgroup.comap_normalizer_eq_of_surjective S'' hΨs
    have h2 : x ∈ (Subgroup.normalizer (S'' : Set ↥(autOn L V))).comap Ψ ↔
        x ∈ Subgroup.normalizer (P : Set ↥L) := by
      rw [h1]
    rw [← h2, Subgroup.mem_comap]
    exact szN10_mem_normalizer_subgroupOf hS'.1 (Ψ x)
  have hM₁eq : M₁ = L ⊓ Subgroup.normalizer (Pg : Set G) := by
    ext x
    constructor
    · intro hx
      have hxL : x ∈ L := hM₁L hx
      refine ⟨hxL, ?_⟩
      have h1 : conjAct V ⟨x, hLN hxL⟩ ∈ autOn M₁ V :=
        mem_autOn_iff_exists.mpr ⟨x, hLN hxL, hx, rfl⟩
      rw [hB] at h1
      have h3 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (P : Set ↥L) := (hnormP _).mpr h1.2
      exact (A312.mem_normalizer_map_subtype_iff L P ⟨x, hxL⟩).mp h3
    · rintro ⟨hxL, hxN⟩
      have h1 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (P : Set ↥L) :=
        (A312.mem_normalizer_map_subtype_iff L P ⟨x, hxL⟩).mpr hxN
      have h2 := (hnormP _).mp h1
      have h3 : conjAct V ⟨x, hLN hxL⟩ ∈ autOn M₁ V := by
        rw [hB]
        exact ⟨mem_autOn_iff_exists.mpr ⟨x, hLN hxL, hxL, rfl⟩, h2⟩
      obtain ⟨x', hx'N, hx'M, hx'⟩ := mem_autOn_iff_exists.mp h3
      have hx'L : x' ∈ L := hM₁L hx'M
      have hkx : x'⁻¹ * x ∈ pCoreOf 2 L := by
        refine hker _ (L.mul_mem (L.inv_mem hx'L) hxL) ?_
        have h4 : conjAct V (⟨x', hx'N⟩⁻¹ * ⟨x, hLN hxL⟩) = 1 := by
          rw [map_mul, map_inv, hx', inv_mul_cancel]
        exact A4.conjAct_eq_one_iff.mp h4
      have hxx : x = x' * (x'⁻¹ * x) := by group
      rw [hxx]
      exact M₁.mul_mem hx'M (hS₀M (pCoreOf_le_of_isSylowTwoOf hS₀ hkx))
  have hS₀N : S₀ ≤ Subgroup.normalizer (Pg : Set G) := fun s hs => (hM₁eq ▸ hS₀M hs).2
  have hsup : IsPGroup 2 ↥(S₀ ⊔ Pg) := szN10_isPGroup_sup hS₀N hS₀.2.1 hPgSyl.2.1
  have hsupL : S₀ ⊔ Pg ≤ L := sup_le hS₀.1 hPgSyl.1
  have h1 : S₀ ⊔ Pg ≤ S₀ := (A4.isSylowTwoOf_iff_maximal.mp hS₀).2.2 _ hsupL hsup le_sup_left
  have h2 : S₀ ⊔ Pg ≤ Pg := (A4.isSylowTwoOf_iff_maximal.mp hPgSyl).2.2 _ hsupL hsup le_sup_right
  have hSP : S₀ = Pg := le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)
  rw [hM₁eq, hSP]

end BorelEq

end CFSG.Quasithin
