module

public import CFSG.Quasithin.EmptyFaithful.S153Q5a
public import CFSG.Quasithin.EmptyFaithful.Insp11Defs
public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S153Q

namespace Q5

section Transport

variable {G : Type} [Group G] {I V₀ : Subgroup G}

theorem mem_map_kappa (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) {U : Subgroup G}
    {s : MulAut ↥V₀} :
    s ∈ (U.subgroupOf I).map (kappa I V₀ hIN) ↔ ∃ x : ↥I, (x : G) ∈ U ∧ kappa I V₀ hIN x = s := by
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem odd_mem_map_kappa (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) (Q : Subgroup ↥I)
    [Q.Normal] (hQ : (kappa I V₀ hIN).ker = Q) {X : Subgroup G}
    (hX : oTwoUpper (⊤ : Subgroup (↥I ⧸ Q)) ≤ barQ I Q X) :
    ∀ s ∈ (kappa I V₀ hIN).range, Odd (orderOf s) →
      s ∈ (X.subgroupOf I).map (kappa I V₀ hIN) := by
  obtain ⟨e, he⟩ := exists_quotEquiv hIN Q hQ
  intro s hs hodd
  have hd : e.symm ⟨s, hs⟩ ∈ barQ I Q X := by
    refine hX (mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_)
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hodd
  obtain ⟨y, hyX, hy⟩ := mem_barQ.mp hd
  rw [mem_map_kappa]
  refine ⟨y, hyX, ?_⟩
  rw [← he y, hy]
  simp

theorem map_kappa_ne_bot (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) (Q : Subgroup ↥I)
    [Q.Normal] (hQ : (kappa I V₀ hIN).ker = Q) {P : Subgroup G} (hPI : P ≤ I)
    (hPQ : ¬ P ≤ Q.map I.subtype) : (P.subgroupOf I).map (kappa I V₀ hIN) ≠ ⊥ := by
  obtain ⟨p, hp, hpQ⟩ := IsConcreteLE.not_le_iff_exists.mp hPQ
  intro hbot
  have hmem : kappa I V₀ hIN ⟨p, hPI hp⟩ ∈ (P.subgroupOf I).map (kappa I V₀ hIN) :=
    (mem_map_kappa hIN).mpr ⟨⟨p, hPI hp⟩, hp, rfl⟩
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hQ] at hmem
  exact hpQ ⟨⟨p, hPI hp⟩, hmem, rfl⟩

theorem map_kappa_fixes (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) {P V : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer (V : Set G)) :
    ∀ p ∈ (P.subgroupOf I).map (kappa I V₀ hIN), ∀ v ∈ V.subgroupOf V₀, p v = v := by
  intro p hp v hv
  obtain ⟨y, hyP, rfl⟩ := (mem_map_kappa hIN).mp hp
  apply Subtype.ext
  rw [kappa_apply_coe]
  have hcomm := Subgroup.mem_centralizer_iff.mp (hPC hyP) v hv
  rw [← hcomm, mul_inv_cancel_right]

theorem map_kappa_normalizes [Finite G] (hIN : I ≤ Subgroup.normalizer (V₀ : Set G))
    {X V V₁ V₂ : Subgroup G} (hVV₀ : V ≤ V₀)
    (hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G) →
      (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁) ∨ (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₂)) :
    ∀ s ∈ (X.subgroupOf I).map (kappa I V₀ hIN), (∀ v ∈ V.subgroupOf V₀, s v ∈ V.subgroupOf V₀) →
      (∀ v ∈ V₁.subgroupOf V₀, s v ∈ V₁.subgroupOf V₀) ∨
        (∀ v ∈ V₁.subgroupOf V₀, s v ∈ V₂.subgroupOf V₀) := by
  intro s hs hsV
  obtain ⟨y, hyX, rfl⟩ := (mem_map_kappa hIN).mp hs
  have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have := hsV ⟨n, hVV₀ hn⟩ hn
    rwa [Subgroup.mem_subgroupOf, kappa_apply_coe] at this
  rcases hnorm y hyX hyN with h | h
  · left
    intro v hv
    rw [Subgroup.mem_subgroupOf, kappa_apply_coe]
    exact h v hv
  · right
    intro v hv
    rw [Subgroup.mem_subgroupOf, kappa_apply_coe]
    exact h v hv

theorem mem_stab_iff {W : Type} [CommGroup W] (V₁ : Subgroup W) (x : MulAut W) :
    x ∈ stab V₁ ↔ ∀ v ∈ V₁, x v ∈ V₁ ∧ x⁻¹ v ∈ V₁ :=
  Iff.rfl

theorem exists_surj_stab (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) (hel : IsElemAbelian 2 V₀)
    {X V₁ : Subgroup G} (hXI : X ≤ I) (hV₁ : V₁ ≤ V₀) :
    ∃ ρ : ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)) →*
        ↥((X.subgroupOf I).map (kappa I V₀ hIN) ⊓
          @stab ↥V₀ (commGroupOfElemAbelian hel) (V₁.subgroupOf V₀)),
      Function.Surjective ρ := by
  let ι : ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)) →* ↥I :=
    Subgroup.inclusion (inf_le_left.trans hXI)
  have hmem : ∀ y : ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)),
      (kappa I V₀ hIN).comp ι y ∈ ((X.subgroupOf I).map (kappa I V₀ hIN) ⊓
        @stab ↥V₀ (commGroupOfElemAbelian hel) (V₁.subgroupOf V₀)) := by
    intro y
    refine Subgroup.mem_inf.mpr ⟨(mem_map_kappa hIN).mpr ⟨ι y, (Subgroup.mem_inf.mp y.2).1, rfl⟩,
      (@mem_stab_iff ↥V₀ (commGroupOfElemAbelian hel) _ _).mpr fun v hv => ⟨?_, ?_⟩⟩
    · rw [Subgroup.mem_subgroupOf, MonoidHom.comp_apply, kappa_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp y.2).2 v).mp hv
    · rw [Subgroup.mem_subgroupOf, MonoidHom.comp_apply, kappa_inv_apply_coe]
      have hy : ((y : G))⁻¹ * v * (y : G) ∈ V₁ := by
        simpa using (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ (Subgroup.mem_inf.mp y.2).2) v).mp hv
      exact hy
  refine ⟨((kappa I V₀ hIN).comp ι).codRestrict _ hmem, ?_⟩
  rintro ⟨s, hs⟩
  obtain ⟨hsX, hss⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨x, hxX, rfl⟩ := (mem_map_kappa hIN).mp hsX
  have hxN : (x : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := ((@mem_stab_iff ↥V₀ (commGroupOfElemAbelian hel) _ _).mp hss ⟨h, hV₁ hh⟩ hh).1
      rwa [Subgroup.mem_subgroupOf, kappa_apply_coe] at this
    · intro hh
      have := ((@mem_stab_iff ↥V₀ (commGroupOfElemAbelian hel) _ _).mp hss
        ⟨(x : G) * h * (x : G)⁻¹, hV₁ hh⟩ hh).2
      rw [Subgroup.mem_subgroupOf, kappa_inv_apply_coe] at this
      simpa [mul_assoc] using this
  exact ⟨⟨(x : G), Subgroup.mem_inf.mpr ⟨hxX, hxN⟩⟩, Subtype.ext rfl⟩

theorem not_isSolvable_of_abs [Finite G] (habs : HatGeomAbs)
    {X P V V₁ V₂ : Subgroup G} {Q : Subgroup ↥I} [Q.Normal]
    (hIN : I ≤ Subgroup.normalizer (V₀ : Set G)) (hel : IsElemAbelian 2 V₀)
    (hcard : Nat.card ↥V₀ = 2 ^ 6) (hQ : Q = (I ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf I)
    (hHS : F6.IsHatSym 6 (↥I ⧸ Q)) (hXI : X ≤ I)
    (hX : oTwoUpper (⊤ : Subgroup (↥I ⧸ Q)) ≤ barQ I Q X)
    (hVV₀ : V ≤ V₀) (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hinf : V₁ ⊓ V₂ = ⊥) (hsup : V₁ ⊔ V₂ = V)
    (h4₁ : Nat.card ↥V₁ = 4) (h4₂ : Nat.card ↥V₂ = 4)
    (hPI : P ≤ I) (hP2 : IsPGroup 2 ↥P) (hPQ : ¬ P ≤ Q.map I.subtype)
    (hPC : P ≤ Subgroup.centralizer (V : Set G))
    (hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G) →
      (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁) ∨ (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₂)) :
    ¬ Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)) := by
  have hQk : (kappa I V₀ hIN).ker = Q := (ker_kappa hIN).trans hQ.symm
  obtain ⟨e, -⟩ := exists_quotEquiv hIN Q hQk
  have hsq : ∀ w : ↥V₀, w * w = 1 := by
    intro w
    apply Subtype.ext
    have := hel.2 w w.2
    rw [sq] at this
    simpa using this
  have hV₁V₀ : V₁ ≤ V₀ := hV₁V.trans hVV₀
  have hV₂V₀ : V₂ ≤ V₀ := hV₂V.trans hVV₀
  intro hsolv
  obtain ⟨ρ, hρ⟩ := exists_surj_stab hIN hel hXI hV₁V₀
  have hsolv' := Group.isSolvable_of_surjective hρ
  refine @habs ↥V₀ (commGroupOfElemAbelian hel) inferInstance hsq hcard
    (kappa I V₀ hIN).range ((X.subgroupOf I).map (kappa I V₀ hIN))
    ((P.subgroupOf I).map (kappa I V₀ hIN)) (isHatSym_of_mulEquiv e hHS)
    (Subgroup.map_le_range _ _) (odd_mem_map_kappa hIN Q hQk hX) (Subgroup.map_le_range _ _)
    ((hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPI).symm).map _)
    (map_kappa_ne_bot hIN Q hQk hPI hPQ)
    (V.subgroupOf V₀) (V₁.subgroupOf V₀) (V₂.subgroupOf V₀) ?_ ?_ ?_ ?_
    (map_kappa_fixes hIN hPC) (map_kappa_normalizes hIN hVV₀ hnorm) hsolv'
  · rw [← Subgroup.subgroupOf_sup hV₁V₀ hV₂V₀, hsup]
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have h1 : (x : G) ∈ V₁ ⊓ V₂ := Subgroup.mem_inf.mpr (Subgroup.mem_inf.mp hx)
    rw [hinf, Subgroup.mem_bot] at h1
    exact h1
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁V₀).toEquiv).trans h4₁
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂V₀).toEquiv).trans h4₂

end Transport

end Q5

theorem a5HatGeom153_of_abs (h : HatGeomAbs) : A5HatGeom153 := by
  intro G _ _ I V₀ X P V V₁ V₂ Q _ _ hIN hel hcard hQ hHS hXI hX hVV₀ hV₁V hV₂V hinf hsup h4₁ h4₂
    hPI hP2 hPQ hPC hnorm
  exact Q5.not_isSolvable_of_abs h hIN hel hcard hQ hHS hXI hX hVV₀ hV₁V hV₂V hinf hsup h4₁ h4₂
    hPI hP2 hPQ hPC hnorm

end S153Q

end CFSG.Quasithin
