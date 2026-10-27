module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.CharacterTheory.PSL2Table.Partition
public import CFSG.CharacterTheory.PSL2Table.Classes

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.PSL2Table
open scoped MatrixGroups

section Core

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  rwa [MulAut.conj_apply] at this

private theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, orderOf_conj_eq]

private theorem isCyclic_map_conj (T : Subgroup G) [IsCyclic T] (d : G) :
    IsCyclic (T.map (MulAut.conj d).toMonoidHom) :=
  isCyclic_of_surjective _ ((MulAut.conj d).toMonoidHom.subgroupMap_surjective T)

private theorem mem_zpowers_of_orderOf_eq [Finite G] {T : Subgroup G} [IsCyclic T] {x y : G}
    (hx : x ∈ T) (hy : y ∈ T) (hxy : orderOf x = orderOf y) : y ∈ Subgroup.zpowers x := by
  have h : Subgroup.zpowers (⟨x, hx⟩ : T) = Subgroup.zpowers (⟨y, hy⟩ : T) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxy]
  have hmem : (⟨y, hy⟩ : T) ∈ Subgroup.zpowers (⟨x, hx⟩ : T) := by
    rw [h]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem map_conj_normalizer_le [Finite G] {T : Subgroup G} [IsCyclic T] {x : G}
    (hx : orderOf x = 3) {d : G} (hxd : x ∈ T.map (MulAut.conj d).toMonoidHom) :
    (Subgroup.normalizer (T : Set G)).map (MulAut.conj d).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  haveI := isCyclic_map_conj T d
  intro n hn
  rw [← CFSG.Glauberman.Dickson.MaxStructure.normalizer_map_conj] at hn
  apply Subgroup.mem_normalizer_fintype
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hh)
  rw [← conj_zpow]
  refine Subgroup.zpow_mem _ ?_ k
  exact mem_zpowers_of_orderOf_eq hxd ((Subgroup.mem_normalizer_iff.mp hn x).mp hxd)
    (by rw [orderOf_conj_eq])

private theorem normalizer_zpowers_eq [Finite G] {T : Subgroup G} [IsCyclic T]
    (hTI : ∀ (c : G) (R : Subgroup G), R ≤ T.map (MulAut.conj c).toMonoidHom → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) ≤
        (Subgroup.normalizer (T : Set G)).map (MulAut.conj c).toMonoidHom)
    {x : G} (hx : orderOf x = 3) {d : G} (hxd : x ∈ T.map (MulAut.conj d).toMonoidHom) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) =
      (Subgroup.normalizer (T : Set G)).map (MulAut.conj d).toMonoidHom := by
  refine le_antisymm (hTI d _ (Subgroup.zpowers_le.mpr hxd) ?_) (map_conj_normalizer_le hx hxd)
  rw [Ne, Subgroup.zpowers_eq_bot]
  rintro rfl
  simp at hx

private theorem isCoatom_normalizer_zpowers_of_cyclic_TI [Finite G] {T : Subgroup G} [IsCyclic T]
    (hTI : ∀ (c : G) (R : Subgroup G), R ≤ T.map (MulAut.conj c).toMonoidHom → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) ≤
        (Subgroup.normalizer (T : Set G)).map (MulAut.conj c).toMonoidHom)
    (hmax : IsCoatom (Subgroup.normalizer (T : Set G))) {x : G} (hx : orderOf x = 3) {d : G}
    (hxd : x ∈ T.map (MulAut.conj d).toMonoidHom) :
    IsCoatom (Subgroup.normalizer (Subgroup.zpowers x : Set G)) := by
  rw [normalizer_zpowers_eq hTI hx hxd]
  exact (CFSG.Glauberman.Dickson.MaxStructure.isCoatom_map_conj_iff _ d).mpr hmax

private theorem mem_zpowers_of_cyclic_TI [Finite G] {T : Subgroup G} [IsCyclic T]
    (hTI : ∀ (c : G) (R : Subgroup G), R ≤ T.map (MulAut.conj c).toMonoidHom → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) ≤
        (Subgroup.normalizer (T : Set G)).map (MulAut.conj c).toMonoidHom)
    {w : G} (hw2 : w * w = 1) (hwinv : ∀ t ∈ T, w * t * w⁻¹ = t⁻¹)
    (hN : ∀ g ∈ Subgroup.normalizer (T : Set G), g ∈ T ∨ w⁻¹ * g ∈ T)
    {x : G} (hx : orderOf x = 3) {d : G} (hxd : x ∈ T.map (MulAut.conj d).toMonoidHom)
    {y : G} (hy : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) (hy3 : orderOf y = 3) :
    y ∈ Subgroup.zpowers x := by
  haveI := isCyclic_map_conj T d
  rw [normalizer_zpowers_eq hTI hx hxd,
    CFSG.Glauberman.Dickson.MaxStructure.mem_map_conj_iff] at hy
  have hyT : d⁻¹ * y * d ∈ T := by
    rcases hN _ hy with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht, e⟩ : ∃ t ∈ T, d⁻¹ * y * d = w * t :=
        ⟨w⁻¹ * (d⁻¹ * y * d), h, by group⟩
      have hsq : (d⁻¹ * y * d) ^ 2 = 1 := by
        rw [sq, e]
        calc w * t * (w * t) = (w * t * w⁻¹) * (w * w) * t := by group
          _ = 1 := by rw [hwinv t ht, hw2]; group
      have hord : orderOf (d⁻¹ * y * d) = 3 := by
        have := orderOf_conj_eq d⁻¹ y
        rwa [inv_inv, hy3] at this
      have hdvd := orderOf_dvd_of_pow_eq_one hsq
      rw [hord] at hdvd
      omega
  refine mem_zpowers_of_orderOf_eq hxd ?_ (by rw [hx, hy3])
  rw [CFSG.Glauberman.Dickson.MaxStructure.mem_map_conj_iff]
  exact hyT

private theorem exists_mem_map_conj {T : Subgroup G} {x x₀ : G} (hx₀ : x₀ ∈ T)
    (hc : IsConj x x₀) : ∃ d : G, x ∈ T.map (MulAut.conj d).toMonoidHom := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine ⟨c⁻¹, ?_⟩
  rw [CFSG.Glauberman.Dickson.MaxStructure.mem_map_conj_iff, inv_inv, hc]
  exact hx₀

end Core

section PSL

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem field_facts {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) :
    ringChar F ≠ 2 ∧ Fintype.card F = p ^ f ∧ ¬ 3 ∣ Fintype.card F := by
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  refine ⟨CFSG.Glauberman.Dickson.MaxUp.ringChar_ne_two hF hp2, hq, ?_⟩
  rw [hq]
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

private theorem exists_isConj_torus (hF2 : ringChar F ≠ 2) (hq5 : 5 ≤ Fintype.card F)
    (h3 : ¬ 3 ∣ Fintype.card F) {x : PSL(2, F)} (hx : orderOf x = 3) :
    (∃ x₀ ∈ splitTorus F, x₀ ≠ 1 ∧ IsConj x x₀) ∨
      ∃ ν : F, ¬ IsSquare ν ∧ ∃ x₀ ∈ nonsplitTorus ν, x₀ ≠ 1 ∧ IsConj x x₀ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  have hunip : ∀ t : F, ¬ IsConj x (mk (unip t)) := by
    intro t h
    have hord : orderOf (mk (unip t)) = 3 := (orderOf_eq_of_isConj h).trans hx
    have hdvd := Subgroup.orderOf_dvd_natCard (unipotent F) (mk_unip_mem_unipotent t)
    rw [hord, card_unipotent h2] at hdvd
    exact h3 hdvd
  rcases conj_cases hF2 hq5 hν x with h | h | h | ⟨x₀, hx₀, hx₀1, hc⟩ | ⟨x₀, hx₀, hx₀1, hc⟩
  · rw [h, orderOf_one] at hx
    norm_num at hx
  · exact (hunip 1 h).elim
  · exact (hunip ν h).elim
  · exact Or.inl ⟨x₀, hx₀, hx₀1, hc⟩
  · exact Or.inr ⟨ν, hν, x₀, hx₀, hx₀1, hc⟩

theorem isCoatom_normalizer_zpowers_of_orderOf_eq_three
    {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : 9 < p ^ f) {x : PSL(2, F)} (hx : orderOf x = 3) :
    IsCoatom (Subgroup.normalizer (Subgroup.zpowers x : Set PSL(2, F))) := by
  obtain ⟨hF2, hqc, h3⟩ := field_facts hF hp2 hp3
  have hq5 : 5 ≤ Fintype.card F := by omega
  rcases exists_isConj_torus hF2 hq5 h3 hx with ⟨x₀, hx₀, hx₀1, hc⟩ |
    ⟨ν, hν, x₀, hx₀, hx₀1, hc⟩
  · obtain ⟨d, hd⟩ := exists_mem_map_conj hx₀ hc
    haveI := splitTorus_isCyclic (F := F)
    have hdvd : 3 ∣ Nat.card (splitTorus F) := by
      have := Subgroup.orderOf_dvd_natCard (splitTorus F) hx₀
      rwa [orderOf_eq_of_isConj hc, hx] at this
    have hT := card_splitTorus (Ring.two_ne_zero hF2) (F := F)
    have h13 : 13 ≤ p ^ f := by
      obtain ⟨m, hm⟩ := hdvd
      omega
    exact isCoatom_normalizer_zpowers_of_cyclic_TI
      (fun c R hR hR1 => CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_splitTorus
        hF2 hq5 c hR hR1)
      (CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_splitTorus hF hp2 h13) hx hd
  · obtain ⟨d, hd⟩ := exists_mem_map_conj hx₀ hc
    haveI := CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic (F := F) hν
    exact isCoatom_normalizer_zpowers_of_cyclic_TI
      (fun c R hR hR1 =>
        CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_nonsplitTorus hF2 hq5 hν c
          hR hR1)
      (CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_nonsplitTorus hF hp2 (by omega)
        (by omega) (by omega) hν) hx hd

theorem mem_zpowers_of_mem_normalizer_of_orderOf_eq_three
    {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : 5 ≤ p ^ f) {x : PSL(2, F)} (hx : orderOf x = 3) {y : PSL(2, F)}
    (hy : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set PSL(2, F))) (hy3 : orderOf y = 3) :
    y ∈ Subgroup.zpowers x := by
  obtain ⟨hF2, hqc, h3⟩ := field_facts hF hp2 hp3
  have hq5 : 5 ≤ Fintype.card F := by omega
  rcases exists_isConj_torus hF2 hq5 h3 hx with ⟨x₀, hx₀, hx₀1, hc⟩ |
    ⟨ν, hν, x₀, hx₀, hx₀1, hc⟩
  · obtain ⟨d, hd⟩ := exists_mem_map_conj hx₀ hc
    haveI := splitTorus_isCyclic (F := F)
    exact mem_zpowers_of_cyclic_TI
      (fun c R hR hR1 => CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_splitTorus
        hF2 hq5 c hR hR1)
      splitWeyl_mul_self (fun t ht => splitWeyl_conj ht)
      (fun g hg => (mem_normalizer_iff_of_TI splitWeyl_mul_self (fun y hy => splitWeyl_conj hy)
        hx₀ (splitTorus_conj_mem_iff hx₀ hx₀1) g).mp hg) hx hd hy hy3
  · obtain ⟨d, hd⟩ := exists_mem_map_conj hx₀ hc
    haveI := CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic (F := F) hν
    obtain ⟨w, -, hw2, hinv, hTI⟩ := exists_nonsplitWeyl hF2 hν
    exact mem_zpowers_of_cyclic_TI
      (fun c R hR hR1 =>
        CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_nonsplitTorus hF2 hq5 hν c
          hR hR1)
      hw2 hinv
      (fun g hg => (mem_normalizer_iff_of_TI hw2 hinv hx₀ (hTI x₀ hx₀ hx₀1) g).mp hg)
      hx hd hy hy3

end PSL

end CFSG.RankThree.PartTwo.Sec20
