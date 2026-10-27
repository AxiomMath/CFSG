module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

theorem mem_normalizer_of_conj_le {H : Type} [Group H] [Finite H] (P : Subgroup H) {g : H}
    (hg : ∀ x ∈ P, g * x * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set H) := by
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have heq : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have : y = x := by
    have h1 := congrArg (fun z => g⁻¹ * z * g) hyx
    simpa [mul_assoc] using h1
  exact this ▸ hy

theorem exists_mem_normalizer_map_eq {H S : Type} [Group H] [Finite H] [Group S]
    (π : H →* S) (hπ : Function.Surjective π) {p : ℕ} [Fact p.Prime] (P : Sylow p H) {s : S}
    (hs : s ∈ Subgroup.normalizer (((P : Subgroup H).map π : Subgroup S) : Set S)) :
    ∃ n ∈ Subgroup.normalizer (P : Set H), π n = s := by
  set Pb : Subgroup S := (P : Subgroup H).map π with hPb
  set K : Subgroup H := (Subgroup.normalizer (Pb : Set S)).comap π with hK
  set M : Subgroup H := Pb.comap π with hM
  have hMK : M ≤ K := fun m hm => Subgroup.le_normalizer hm
  have hPM : (P : Subgroup H) ≤ M := fun x hx => ⟨x, hx, rfl⟩
  have hnormMK : (M.subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hMK).2 fun k hk => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have h1 := Subgroup.mem_normalizer_iff.1
      (show π k ∈ Subgroup.normalizer (Pb : Set S) from hk) (π m)
    change π m ∈ Pb ↔ π (k * m * k⁻¹) ∈ Pb
    rwa [map_mul, map_mul, map_inv]
  have hPK : (P : Subgroup H) ≤ K.subtype.range := by
    rw [Subgroup.range_subtype]
    exact hPM.trans hMK
  let PK : Sylow p K := P.comapOfInjective K.subtype K.subtype_injective hPK
  have hPKM : (PK : Subgroup K) ≤ M.subgroupOf K := by
    change (P : Subgroup H).comap K.subtype ≤ M.comap K.subtype
    exact Subgroup.comap_mono hPM
  have hfrat := Sylow.normalizer_sup_eq_top' (N := M.subgroupOf K) PK hPKM
  obtain ⟨k, rfl⟩ := hπ s
  have hkK : k ∈ K := hs
  have hmem : (⟨k, hkK⟩ : K) ∈ ((Subgroup.normalizer (PK : Set K) ⊔ M.subgroupOf K : Subgroup K) :
      Set K) := by
    rw [hfrat]
    trivial
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hbM : (b : H) ∈ M := hb
  obtain ⟨x, hxP, hx⟩ := hbM
  have ha' : (a : H) ∈ Subgroup.normalizer (P : Set H) := by
    refine mem_normalizer_of_conj_le (P : Subgroup H) fun y hy => ?_
    have hyK : y ∈ K := (hPM.trans hMK) hy
    have hyPK : (⟨y, hyK⟩ : K) ∈ (PK : Subgroup K) := hy
    have := (Subgroup.mem_normalizer_iff.1 ha ⟨y, hyK⟩).1 hyPK
    exact this
  refine ⟨(a : H) * x, Subgroup.mul_mem _ ha' (Subgroup.le_normalizer hxP), ?_⟩
  have hk : (a : H) * (b : H) = k := congrArg Subtype.val hab
  rw [map_mul, hx, ← map_mul, hk]

end CFSG.Quasithin.H13.U3.GC137.SQ
