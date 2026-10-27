module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecBK4R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open scoped IsMulCommutative Pointwise

namespace BK4

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (h : (A : Set G) * B = B * A) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have hba : b * a' ∈ (B : Set G) * A := ⟨b, hb, a', ha', rfl⟩
        rw [← h] at hba
        obtain ⟨a'', ha'', b'', hb'', he⟩ := hba
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        change a * a'' * (b'' * b') = a * b * (a' * b')
        rw [show a * b * (a' * b') = a * (b * a') * b' by group, ← he]
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (B : Set G) * A := ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← h] at hba
        change (a * b)⁻¹ ∈ (A : Set G) * B
        rwa [mul_inv_rev] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  obtain ⟨a, ha, b, hb, he⟩ := hle hg
  exact ⟨a, ha, b, hb, he⟩

theorem isSolvable_sup [Finite G] {D T : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : IsPGroup p D) (hT : IsPGroup 2 T) (hDT : (D : Set G) * T = T * D) :
    Group.IsSolvable ↥(D ⊔ T) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hD
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT
  have hcop : Nat.Coprime (Nat.card D) (Nat.card T) := by
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hdvd : Nat.card D * Nat.card T ∣ Nat.card ↥(D ⊔ T) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hle : Nat.card ↥(D ⊔ T) ≤ Nat.card D * Nat.card T := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective (fun x : ↥D × ↥T => (⟨x.1 * x.2,
      Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(D ⊔ T))) fun g => ?_
    obtain ⟨d, hd, t, ht, he⟩ := exists_mul_of_mem_sup hDT g.2
    exact ⟨(⟨d, hd⟩, ⟨t, ht⟩), Subtype.ext he⟩
  have hcard : Nat.card ↥(D ⊔ T) = p ^ a * 2 ^ b := by
    rw [← ha, ← hb]
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have := Fintype.ofFinite ↥(D ⊔ T)
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp
    Nat.prime_two hp2 (by rw [← Nat.card_eq_fintype_card, hcard])

theorem isSolvable_autOn {Y : Subgroup G} (V : Subgroup G) (hY : Group.IsSolvable Y) :
    Group.IsSolvable ↥(autOn Y V) :=
  isSolvable_map _ (isSolvable_subgroupOf hY _)

variable {L V : Subgroup G}

theorem isFlagW_map_conjV {T : Subgroup G} {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxT : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) {q i : ℕ} {U : Subgroup ↥V}
    (hU : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) q i U) :
    SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) q i
      (U.map (SecA.conjV V x hxV).toMonoidHom) := by
  set Z := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZ
  set φ := SecA.conjV V x hxV with hφ
  have hxV' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hxV
  have hinv : φ⁻¹ = SecA.conjV V x⁻¹ hxV' := (SecA.conjV_inv V hxV).symm
  have hφZ : ∀ z ∈ Z, φ z ∈ Z := fun z hz => G2Q8.conjV_mem_centralizer hxL hxV hz
  have hφZ' : ∀ z ∈ Z, φ⁻¹ z ∈ Z := fun z hz => by
    rw [hinv]
    exact G2Q8.conjV_mem_centralizer (Subgroup.inv_mem _ hxL) hxV' hz
  have hmem : ∀ v, v ∈ U.map φ.toMonoidHom ↔ φ⁻¹ v ∈ U := fun v => Subgroup.mem_map_equiv
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  refine ⟨fun z hz => (hmem z).mpr (hZU (hφZ' z hz)), ?_, ?_, ?_⟩
  · intro ψ hψZ hψH u hu
    rw [hmem] at hu ⊢
    let ψ' : ↥V →* ↥V := ((φ⁻¹ : MulAut ↥V).toMonoidHom.comp ψ).comp φ.toMonoidHom
    have hψ' : ∀ w, ψ' w = φ⁻¹ (ψ (φ w)) := fun w => rfl
    have hψ'Z : ∀ z ∈ Z, ψ' z ∈ Z := fun z hz => hφZ' _ (hψZ _ (hφZ z hz))
    have hψ'H : ∀ h ∈ autOn L V, ∀ w : ↥V, ψ' (h w) * (h (ψ' w))⁻¹ ∈ Z := by
      intro h hh w
      have hh'L : φ * h * φ⁻¹ ∈ autOn L V := G2Q8.conjV_mul_conjV_inv_mem hxL hxV hh
      have e1 : φ (h w) = (φ * h * φ⁻¹) (φ w) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      have e2 : h (φ⁻¹ (ψ (φ w))) = φ⁻¹ ((φ * h * φ⁻¹) (ψ (φ w))) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [hψ', hψ', e1, e2, ← map_inv, ← map_mul]
      exact hφZ' _ (hψH _ hh'L (φ w))
    have := hst ψ' hψ'Z hψ'H _ hu
    rwa [hψ', MulAut.apply_inv_self] at this
  · have hZmap : Z.map φ.toMonoidHom = Z := by
      ext z
      rw [show z ∈ Z.map φ.toMonoidHom ↔ φ⁻¹ z ∈ Z from Subgroup.mem_map_equiv]
      refine ⟨fun h => ?_, hφZ' z⟩
      have := hφZ _ h
      rwa [MulAut.apply_inv_self] at this
    rw [← hZmap, Subgroup.relIndex_map_map_of_injective (f := φ.toMonoidHom) Z U φ.injective]
    exact hidx
  · intro p hp
    refine SecA.mem_stabW.mpr fun v => ?_
    rw [hmem, hmem]
    have hp' : φ⁻¹ * p * φ ∈ autOn (T ⊓ L) V := by
      have := G2Q8.conjV_mul_conjV_inv_mem (Subgroup.inv_mem _ hxT) hxV' hp
      rwa [← hinv, inv_inv] at this
    rw [SecA.mem_stabW.mp (hPU hp') (φ⁻¹ v), MulAut.mul_apply, MulAut.mul_apply,
      MulAut.apply_inv_self]

theorem mapsTo_of_isFlagW [IsMulCommutative ↥V] {Dm : FFModel} {K M : Type} [Field K]
    [AddCommGroup M] [Module K M] {LM : KGNat.LinModel Dm K M} {π : Dm.Gam →* ↥(autOn L V)}
    {f : ↥V → M}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {T : Subgroup G} {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxT : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) {T' : M →+ M}
    (hT' : ∀ w, f (SecA.conjV V x hxV w) = T' (f w)) {S : Submodule K M} {q i : ℕ}
    (hS : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) q i (hf.pre S.toAddSubgroup))
    (huniq : ∀ U, SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) q i U → U = hf.pre S.toAddSubgroup) :
    ∀ y ∈ S, T' y ∈ S := by
  intro y hy
  obtain ⟨w, rfl⟩ := hf.surj y
  have hw : w ∈ hf.pre S.toAddSubgroup := hy
  have h2 : SecA.conjV V x hxV w ∈
      (hf.pre S.toAddSubgroup).map (SecA.conjV V x hxV).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hw
  rw [huniq _ (isFlagW_map_conjV hxV hxL hxT hS)] at h2
  rw [← hT']
  exact h2

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
