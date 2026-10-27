module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartOne

theorem sylow_eq_top_of_isPGroup {F : Type*} [Group F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : IsPGroup p F) (Q : Sylow p F) : (Q : Subgroup F) = ⊤ := by
  have h1 : ¬ p ∣ (Q : Subgroup F).index := Q.not_dvd_index
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hF
  have h2 : (Q : Subgroup F).index ∣ p ^ n := (Subgroup.index_dvd_card _).trans hn
  have h3 : (Q : Subgroup F).index = 1 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).1 h2
    cases m with
    | zero => simpa using hm
    | succ m => exact absurd (hm ▸ dvd_pow_self p (Nat.succ_ne_zero m)) h1
  exact Subgroup.index_eq_one.1 h3

theorem map_sylow_comap {M T : Type*} [Group M] [Group T] [Finite M] (π : M →* T)
    (hπ : Function.Surjective π) {p : ℕ} [Fact p.Prime] {F : Subgroup T} (hF : IsPGroup p F)
    (P : Sylow p (F.comap π)) :
    ((P : Subgroup (F.comap π)).map (F.comap π).subtype).map π = F := by
  classical
  let f : F.comap π →* F := (π.comp (F.comap π).subtype).codRestrict F fun x => x.2
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  have : Finite F := Finite.of_surjective f hf
  have h1 : (P : Subgroup (F.comap π)).map f = ⊤ :=
    sylow_eq_top_of_isPGroup hF (P.mapSurjective hf)
  rw [Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact x.2
  · intro hy
    have : (⟨y, hy⟩ : F) ∈ (P : Subgroup (F.comap π)).map f := by
      rw [h1]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, hx, congrArg Subtype.val hxy⟩

theorem exists_pSubgroup_lift {M T : Type*} [Group M] [Group T] [Finite M] (π : M →* T)
    (hπ : Function.Surjective π) {p : ℕ} [Fact p.Prime] (hpk : ¬ p ∣ Nat.card π.ker)
    {F : Subgroup T} (hF : IsPGroup p F) :
    ∃ F' : Subgroup M, IsPGroup p F' ∧ F'.map π = F ∧ Function.Injective (π.comp F'.subtype) := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p (F.comap π)) := inferInstance
  refine ⟨P.map (F.comap π).subtype, P.2.map _, map_sylow_comap π hπ hF P, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨x, hx⟩ hker
  have hxk : x ∈ π.ker := hker
  obtain ⟨m, hm⟩ := (P.2.map (F.comap π).subtype) ⟨x, hx⟩
  have hxm : x ^ p ^ m = 1 := congrArg Subtype.val hm
  have h1 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hxm
  have h2 : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hxk
  have h3 : Nat.Coprime (p ^ m) (Nat.card π.ker) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpk)
  have h4 : orderOf x = 1 := (Nat.Coprime.coprime_dvd_left h1 h3).eq_one_of_dvd h2
  exact Subtype.ext (orderOf_eq_one_iff.1 h4)

theorem exists_twoSubgroup_lift {M T : Type*} [Group M] [Group T] [Finite M] (π : M →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) {U : Subgroup T}
    (hU : IsPGroup 2 U) :
    ∃ U' : Subgroup M, IsPGroup 2 U' ∧ U'.map π = U ∧
      ∀ e : M, (∀ u ∈ U, π e * u * (π e)⁻¹ ∈ U) → (∀ u ∈ U, (π e)⁻¹ * u * π e ∈ U) →
        ∀ x ∈ U', e * x * e⁻¹ ∈ U' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G : Subgroup M := U.comap π with hG
  let f : G →* U := (π.comp G.subtype).codRestrict U fun x => x.2
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  have : Finite U := Finite.of_surjective f hf
  have hnil : Group.IsNilpotent G := by
    have : Group.IsNilpotent U := hU.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    have hxk : (x : M) ∈ π.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hxk) y)
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hPc : (P : Subgroup G).Characteristic := Sylow.characteristic_of_normal P inferInstance
  refine ⟨P.map G.subtype, P.2.map _, map_sylow_comap π hπ hU P, ?_⟩
  intro e he he' x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hmem : ∀ z : M, π z ∈ U → π (e * z * e⁻¹) ∈ U := fun z hz => by
    rw [map_mul, map_mul, map_inv]
    exact he _ hz
  have hmem' : ∀ z : M, π z ∈ U → π (e⁻¹ * z * e) ∈ U := fun z hz => by
    rw [map_mul, map_mul, map_inv]
    exact he' _ hz
  let φ : G ≃* G :=
    { toFun := fun x => ⟨e * x * e⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨e⁻¹ * x * e, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x z => Subtype.ext (by simp [mul_assoc]) }
  have hφ : (P : Subgroup G).comap φ.toMonoidHom = P := hPc.fixed φ
  have hyφ : φ y ∈ (P : Subgroup G) := by
    have : y ∈ (P : Subgroup G).comap φ.toMonoidHom := by rw [hφ]; exact hy
    exact this
  exact ⟨φ y, hyφ, rfl⟩

end CFSG.RankThree.PartOne
