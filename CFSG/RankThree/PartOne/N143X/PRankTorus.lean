module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.RootsOfUnity.Basic

public section

namespace CFSG.RankThree.PartOne.N143X

theorem exists_conj_map_le_of_not_dvd_index' {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} (hH : ¬ p ∣ H.index) {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p H) := inferInstance
  set S := (S₀ : Subgroup H).map H.subtype
  have hS : IsPGroup p S := S₀.isPGroup'.map H.subtype
  have hSi : ¬ p ∣ S.index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hH
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hS.toSylow hSi)
  refine ⟨g, ?_⟩
  calc P.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hPQ
    _ = S := by
        have h := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
        simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
        rw [← h, Subgroup.pointwise_smul_def]
        rfl
    _ ≤ H := Subgroup.map_subtype_le _

theorem card_le_sq_of_injective {E : Type} [Group E] {L : Type} [Field L] {p : ℕ} (hp : 0 < p)
    (ψ : E →* (Fin 2 → Lˣ)) (hψ : Function.Injective ψ) (hE : ∀ x : E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  let φ : E → (Fin 2 → rootsOfUnity p L) := fun x i =>
    ⟨ψ x i, (mem_rootsOfUnity p _).2 (by
      have h := congrFun (congrArg ψ (hE x)) i
      rwa [map_pow, map_one] at h)⟩
  have hφ : Function.Injective φ := fun x y h => hψ (funext fun i =>
    congrArg (fun z : rootsOfUnity p L => (z : Lˣ)) (congrFun h i))
  have hR : Nat.card (rootsOfUnity p L) ≤ p := card_rootsOfUnity L p
  calc Nat.card E ≤ Nat.card (Fin 2 → rootsOfUnity p L) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity p L) ^ 2 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hR 2

theorem false_of_pow_three_of_torus {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Type} [Field L] {T : Subgroup X} (hidx : ¬ p ∣ T.index) (ψ : T →* (Fin 2 → Lˣ))
    (hψ : Function.Injective ψ) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_map_le_of_not_dvd_index' hidx hP
  let φ : E →* T := MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp E.subtype) T
    (fun x => hg ⟨x, x.2, rfl⟩)
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  have h1 := card_le_sq_of_injective (L := L) hp.pos (ψ.comp φ) (hψ.comp hφ)
    (fun x => Subtype.ext (hE x x.2))
  rw [hcard] at h1
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem false_of_pow_three_of_cyclic {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {T : Subgroup X} [IsCyclic T] (hidx : ¬ p ∣ T.index) {E : Subgroup X}
    (hE : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_map_le_of_not_dvd_index' hidx hP
  let φ : E →* T := MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp E.subtype) T
    (fun x => hg ⟨x, x.2, rfl⟩)
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hcyc : IsCyclic E := isCyclic_of_injective φ hφ
  obtain ⟨x, hx⟩ := hcyc.exists_ofOrder_eq_natCard
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hE x x.2))
  rw [hx, hcard] at h1
  have := Nat.le_of_dvd hp.pos h1
  have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h3
  omega

end CFSG.RankThree.PartOne.N143X
