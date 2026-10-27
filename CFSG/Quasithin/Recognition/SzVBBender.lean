module

public import CFSG.Quasithin.Recognition.SzVBOdd
public import CFSG.Quasithin.Recognition.SzVBBenderPerm

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin CFSG.Holt.H78

variable {G : Type} [Group G]

@[expose] def imgK (K P V : Subgroup G) : Subgroup (Equiv.Perm (ConjSet P V)) :=
  (K.subgroupOf P).map (MulAction.toPermHom ↥P (ConjSet P V))

structure BenderBridge (K S V : Subgroup G) : Prop where
  isBender : ∃ n i e : ℕ, IsBenderAction ↥(imgK K (K ⊔ S) V) (ConjSet (K ⊔ S) V) n i e
  nine_le : 9 ≤ Nat.card (ConjSet (K ⊔ S) V)
  ker_inv_le : ∀ x : ↥(K ⊔ S), x * x = 1 → x ∈ kerAct (K ⊔ S) V →
    (x : G) ∈ pCoreOf 2 (K ⊔ S)

theorem mem_normalizer_subgroupOf {K P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (x : ↥P) :
    x ∈ Subgroup.normalizer ((K.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp (hPN x.2) (h : G)

theorem toPermHom_mem_normalizer_imgK {K P V : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (x : ↥P) :
    MulAction.toPermHom ↥P (ConjSet P V) x ∈
      Subgroup.normalizer (imgK K P V : Set (Equiv.Perm (ConjSet P V))) :=
  Subgroup.le_normalizer_map (MulAction.toPermHom ↥P (ConjSet P V))
    (Subgroup.mem_map_of_mem _ (mem_normalizer_subgroupOf hPN x))

theorem exists_surjective_imgK {K P : Subgroup G} (V : Subgroup G) (hKP : K ≤ P) :
    ∃ g : ↥K →* ↥(imgK K P V), Function.Surjective g ∧ ∀ (k : ↥K) (U : ConjSet P V),
      ((g k : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)) U = Subgroup.inclusion hKP k • U := by
  refine ⟨((MulAction.toPermHom ↥P (ConjSet P V)).comp (Subgroup.inclusion hKP)).codRestrict
    (imgK K P V) (fun k => ?_), ?_, fun k U => rfl⟩
  · exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKP k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, Subtype.ext rfl⟩

theorem relIndex_kerAct_eq (P V : Subgroup G) (E : Subgroup ↥P) :
    (kerAct P V).relIndex E = Nat.card (E.map (MulAction.toPermHom ↥P (ConjSet P V))) := by
  unfold kerAct
  rw [Subgroup.relIndex_ker]

theorem benderLocalFacts_of_bridge [Finite G] {K S V : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S (K ⊔ S))
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hB : BenderBridge K S V) :
    BenderLocalFacts (K ⊔ S) S V := by
  obtain ⟨n, i, e, hA⟩ := hB.isBender
  have hL : IsNaturalSE (imgK K (K ⊔ S) V) := isNaturalSE_iff.mpr ⟨n, i, e, hA⟩
  have hKP : K ≤ K ⊔ S := le_sup_left
  have hPN : K ⊔ S ≤ Subgroup.normalizer (K : Set G) := sup_le K.le_normalizer hSK
  have hnorm := fun x : ↥(K ⊔ S) => toPermHom_mem_normalizer_imgK (V := V) hPN x
  refine ⟨hA.odd_card, by have := hB.nine_le; omega, le_sup_right, hS.2.1, hSV,
    hB.ker_inv_le, ?_, ?_, ?_⟩
  · intro U U' hU hU'
    obtain ⟨g, hgs, hg⟩ := exists_surjective_imgK V hKP
    have h1 : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
      F7.isSylowTwoOf_inf_normal hS hKP hSK
    have hp : IsPGroup 2 ((S ⊓ K).subgroupOf K) :=
      h1.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h1.1).symm
    obtain ⟨Q, hQeq⟩ : ∃ Q : Sylow 2 ↥(imgK K (K ⊔ S) V),
        (Q : Subgroup ↥(imgK K (K ⊔ S) V)) = ((S ⊓ K).subgroupOf K).map g :=
      ⟨(hp.map g).toSylow fun h =>
        h1.2.2 (h.trans (((S ⊓ K).subgroupOf K).index_map_dvd hgs)), rfl⟩
    have hQ : (Q : Subgroup ↥(imgK K (K ⊔ S) V)) ≤
        MulAction.stabilizer ↥(imgK K (K ⊔ S) V) (ConjSet.base (K ⊔ S) V) := by
      intro q hq
      rw [hQeq] at hq
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hq
      rw [MulAction.mem_stabilizer_iff]
      show ((g t : ↥(imgK K (K ⊔ S) V)) : Equiv.Perm (ConjSet (K ⊔ S) V))
        (ConjSet.base (K ⊔ S) V) = ConjSet.base (K ⊔ S) V
      rw [hg]
      exact Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer'
        (hSV (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1))
    obtain ⟨p, hpQ, hpU⟩ := hA.exists_mem_smul_eq hQ hU hU'
    rw [hQeq] at hpQ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hpQ
    exact ⟨Subgroup.inclusion hKP t,
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1, (hg t U).symm.trans hpU⟩
  · intro E hE
    rw [relIndex_kerAct_eq]
    refine card_le_four_of_orbits_le_two hL ?_ ?_
    · intro f hf
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hf
      exact hnorm x
    · intro f hf f' hf' U
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hf'
      exact hE x hx x' hx' U
  · intro y hyy hy
    have hσσ : MulAction.toPermHom ↥(K ⊔ S) (ConjSet (K ⊔ S) V) y *
        MulAction.toPermHom ↥(K ⊔ S) (ConjSet (K ⊔ S) V) y = 1 := by
      rw [← map_mul, hyy, map_one]
    have hσ1 : MulAction.toPermHom ↥(K ⊔ S) (ConjSet (K ⊔ S) V) y ≠ 1 := fun h =>
      hy (MonoidHom.mem_ker.mpr h)
    obtain ⟨R, hR4, hR⟩ := exists_four_two_cycles hL hB.nine_le (hnorm y) hσσ hσ1
    exact ⟨R, hR4, hR⟩

end CFSG.Quasithin.SzVB
