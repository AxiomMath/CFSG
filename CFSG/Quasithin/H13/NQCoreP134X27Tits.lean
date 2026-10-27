module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.F134TitsE9
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase

public section

namespace CFSG.Quasithin.H13.NQCore.X27Tits

open CFSG.Blueprint CFSG.Quasithin.P134 CFSG.Quasithin.F134 CFSG.QuasithinUnique
open scoped Pointwise

theorem exists_model_conj_of_sylow {A : Type} [Group A] [Finite A] {L T : Subgroup A}
    (hS : IsSylowTwoOf (T ⊓ L) L) {X : Type*} [Group X] {G T₀ : Subgroup X} {φ₀ : ↥L →* X}
    (hφ₀ : Function.Injective φ₀) (hφ₀G : ∀ x, φ₀ x ∈ G) (hφ₀s : ∀ y ∈ G, ∃ x, φ₀ x = y)
    (hT₀G : T₀ ≤ G) (hT₀ : IsPGroup 2 T₀) :
    ∃ φ : ↥L →* X, Function.Injective φ ∧ (∀ x, φ x ∈ G) ∧ (∀ y ∈ G, ∃ x, φ x = y) ∧
      T₀ ≤ ((T ⊓ L).subgroupOf L).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨TL, hTLdef⟩ : ∃ R : Subgroup ↥L, R = T₀.comap φ₀ := ⟨_, rfl⟩
  have hTLmap : TL.map φ₀ = T₀ := by
    rw [hTLdef]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ₀s y (hT₀G hy)
    exact ⟨x, hy, rfl⟩
  have hTLp : IsPGroup 2 TL :=
    hT₀.of_equiv ((TL.equivMapOfInjective _ hφ₀).trans (MulEquiv.subgroupCongr hTLmap)).symm
  have hUp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨Q, hQ⟩ := hTLp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) (hUp.toSylow hS.2.2) Q
  have hQU : ∀ x ∈ (Q : Subgroup ↥L), (MulAut.conj g)⁻¹ x ∈ (T ⊓ L).subgroupOf L := by
    intro x hx
    have hx' : x ∈ ((g • hUp.toSylow hS.2.2 : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hback : ∀ x : ↥L, (φ₀.comp (MulAut.conj g).toMonoidHom) ((MulAut.conj g)⁻¹ x) = φ₀ x := by
    intro x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply]
  refine ⟨φ₀.comp (MulAut.conj g).toMonoidHom, hφ₀.comp (MulAut.conj g).injective,
    fun x => hφ₀G _, fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hφ₀s y hy
    exact ⟨_, hback x⟩
  · intro y hy
    rw [← hTLmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, hQU x (hQ hx), hback x⟩

theorem prime_not_dvd_27_mul_two_pow {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ¬ p ∣ 27 * 2 ^ k := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h27 | h2'
  · have h27' : p ∣ 3 ^ 3 := by norm_num; exact h27
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h27'))
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2'))

theorem noX27Simple_tits
    : NoX27Simple fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 := by
  intro A _ _ L P T hcfg h27 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := tits_embedding hL
  have hS := OddConfig.isSylowTwoOf_inf hcfg
  obtain ⟨φ, hφ, hφG, -, hTφ⟩ :=
    exists_model_conj_of_sylow hS hφ₀ hφ₀mem hφ₀surj titsSyl_le titsSyl_isPGroup
  have hHL : P ⊔ (T ⊓ L) ≤ L := OddConfig.sup_inf_le hcfg
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (GL (Fin 26) (ZMod 2)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : titsSyl ≤ K := by
    rw [hKdef]
    exact hTφ.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right))
  have hKM : K ≤ titsGroup := by
    rw [hKdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφG _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := OddConfig.card_sup_inf_x27 hcfg h27
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hle := tits_card_le hTK hKM fun p hp => by
    rw [hKc, hHc, hk]
    have hprime : p.Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
    exact prime_not_dvd_27_mul_two_pow hprime (by rcases hp with h | h <;> omega)
      (by rcases hp with h | h <;> omega)
  have hTU : Nat.card titsSyl ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv,
      Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ hφ).toEquiv]
    have : Finite (((T ⊓ L).subgroupOf L).map φ) := Subgroup.instFiniteSubtypeMem _
    exact Subgroup.card_le_of_le hTφ
  have hpos : 0 < Nat.card titsSyl := Nat.card_pos
  rw [hKc, hHc] at hle
  omega

theorem facts134X27_tits :
    NoX27ConfigQ fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 :=
  noX27ConfigQ_of_noCover (fun _ _ _ _ e h => CFSG.SectionRank.reeTitsModel_of_mulEquiv e.symm h)
    noX27Simple_tits fun X _ _ hX h3 h => by
      have : Group.IsPerfect X := hX.1
      obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
      exact CFSG.QuasithinUnique.Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
        CFSG.SectionRank.Tits_perfect_odd_cover_trivial (K := K) hK π hπ hC hodd

end CFSG.Quasithin.H13.NQCore.X27Tits
