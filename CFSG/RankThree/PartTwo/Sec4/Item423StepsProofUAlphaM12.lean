module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProofUAlpha
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Step462UAlphaM12

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem finite_subgroup [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

theorem conj_injective (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun σ : MulAut G => σ x) hab
    simp only [MulAut.conj_apply] at h
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [← h]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem map_normalizer_zpowers (f : MulAut G) (a : G) :
    (Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)).map f.toMonoidHom =
      Subgroup.normalizer ((Subgroup.zpowers (f a) : Subgroup G) : Set G) := by
  rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
  rfl

noncomputable def normalizerZpowersEquiv (f : MulAut G) (a : G) :
    Subgroup.normalizer ((Subgroup.zpowers (f a) : Subgroup G) : Set G) ≃*
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
  (MulEquiv.subgroupCongr (map_normalizer_zpowers f a).symm).trans
    (Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).symm

end General

theorem card_le_four_of_normal
    {N : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))} [N.Normal]
    (hN : IsPGroup 2 N) : Nat.card N ≤ 4 := by
  have hK : Nat.card (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) = 72 := by
    rw [Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hN
  have hdvd : 2 ^ k ∣ 72 := hk ▸ hK ▸ Subgroup.card_subgroup_dvd_card N
  have hk3 : k ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 72 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h16
  have hk8 : k ≠ 3 := by
    rintro rfl
    have hq : Nat.card ((Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ⧸ N) = 9 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hK, hk] at h
      omega
    have hmem : ∀ s : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4), s ^ 2 = 1 → s ∈ N := by
      intro s hs
      set x : (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ⧸ N :=
        (QuotientGroup.mk s : (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ⧸ N) with hx
      have h2 : x ^ 2 = 1 := by rw [hx, ← QuotientGroup.mk_pow, hs, QuotientGroup.mk_one]
      have h9 : x ^ 9 = 1 := hq ▸ pow_card_eq_one'
      have h1 : orderOf x ∣ Nat.gcd 2 9 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h9)
      rw [show Nat.gcd 2 9 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact (QuotientGroup.eq_one_iff s).mp h1
    set s₁ : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) := (Equiv.swap 0 1, 1)
    set s₂ : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) := (Equiv.swap 0 2, 1)
    have hs : s₁ * s₂ ∈ N := N.mul_mem (hmem s₁ (by decide)) (hmem s₂ (by decide))
    obtain ⟨m, hm⟩ := hN ⟨s₁ * s₂, hs⟩
    have hm' : (s₁ * s₂) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have ho : orderOf (s₁ * s₂) = 3 := orderOf_eq_prime (by decide) (by decide)
    have h3 : 3 ∣ 2 ^ m := ho ▸ orderOf_dvd_of_pow_eq_one hm'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hk2 : k ≤ 2 := by omega
  rw [hk]
  interval_cases k <;> norm_num

section Core

variable {S : Type} [Group S] [Finite S]

theorem eq_inSubgroup_pCore {y : S} {V : Subgroup S}
    (hN : Nonempty (Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)))
    (hV2 : IsPGroup 2 V) (hV4 : Nat.card V = 4) (hVC : V ≤ Subgroup.centralizer ({y} : Set S))
    (hCV : ∀ s ∈ Subgroup.centralizer ({y} : Set S), s ∈ Subgroup.normalizer (V : Set S)) :
    V = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set S)) := by
  obtain ⟨e⟩ := hN
  set C := Subgroup.centralizer ({y} : Set S) with hC
  set O := inSubgroup (CFSG.pCore 2) C with hO
  set Nz := Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) with hNz
  have hVO : V ≤ O := by
    have hn : (V.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).mpr fun s hs => hCV s hs
    have hp : IsPGroup 2 (V.subgroupOf C) :=
      hV2.comap_of_injective C.subtype C.subtype_injective
    have hle : V.subgroupOf C ≤ CFSG.pCore 2 C := le_sSup ⟨hn, hp⟩
    have h := Subgroup.map_mono (f := C.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hVC] at h
  have hO2 : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hCN : C ≤ Nz := fun s hs =>
    Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hs
  have hNO : Nz ≤ Subgroup.normalizer (O : Set S) := fun g hg =>
    Step462UAlphaProof.mem_normalizer_inSubgroup_pCore
      (Step462UAlphaProof.mem_normalizer_centralizer_singleton hg)
  have hO'n : (O.subgroupOf Nz).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hOC.trans hCN)).mpr hNO
  have hO''n : ((O.subgroupOf Nz).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hO'n e.toMonoidHom e.surjective
  have hO''2 : IsPGroup 2 ((O.subgroupOf Nz).map e.toMonoidHom) :=
    (hO2.comap_of_injective Nz.subtype Nz.subtype_injective).map _
  have hcard : Nat.card ((O.subgroupOf Nz).map e.toMonoidHom) = Nat.card O := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOC.trans hCN)).toEquiv
  have hle4 := card_le_four_of_normal hO''2
  have hVle := Subgroup.card_le_of_le hVO
  exact Subgroup.eq_of_le_of_card_ge hVO (by omega)

end Core

theorem k462UAlphaAt_of_item4_14
    (h414 : Item4_14) (S : Type) [Group S]
    (hS : Nonempty (S ≃* Blueprint.NativeSporadic.M12)) : K462UAlphaAt S := by
  intro D y V hDe hD9 hyD hy1 hV2 hV4 hVC hCV hDV R hR2 hRC hRN
  obtain ⟨φ⟩ := hS
  have : Finite S := Finite.of_equiv _ φ.symm.toEquiv
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  have : Finite (Subgroup (MulAut S)) := finite_subgroup
  obtain ⟨-, hZ, -, -⟩ := KFacts.ks18M12 S ⟨φ⟩
  have hinj := conj_injective hZ
  obtain ⟨P, hDP⟩ := (Sec5.isPGroup_of_isElemAbelian hDe).exists_le_sylow
  obtain ⟨-, -, E, F, A, t, -, htZ, hΔ, hE, hF, hA, hNa⟩ := h414.1 S ⟨φ⟩ P
  have hmemΔ : ∀ B : Subgroup S, B ∈ ({E, F, A, conjugate A t} : Set (Subgroup S)) ↔
      B ≤ P ∧ Nat.card B = 9 := fun B => by rw [← hΔ]; rfl
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV4
    norm_num at hV4
  have hVinv : ∀ B : Subgroup S, B ≤ Subgroup.normalizer (V : Set S) →
      V ∈ invariantPiSubgroups ⊤ B (piOf 2) := fun B hB =>
    ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two V).mpr hV2, hB⟩
  have hnotGL : ∀ B : Subgroup S, B ≤ P → Nat.card B = 9 →
      B ≤ Subgroup.normalizer (V : Set S) → ¬ Nonempty (autIn ⊤ B ≃* GL (Fin 2) (ZMod 3)) := by
    intro B hBP hB9 hBV hgl
    have h1 := (h414.2 S ⟨φ⟩ P B hBP hB9).1 hgl
    have h2 := hVinv B hBV
    rw [h1, Set.mem_singleton_iff] at h2
    exact hVne h2
  have hEΔ := (hmemΔ E).mp (by simp)
  have hyZ : y ∉ (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) := by
    intro hy
    refine hnotGL E hEΔ.1 hEΔ.2 (fun g hg => hCV g ?_) hE
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hy.2 g (hEΔ.1 hg)
  have hDΔ := (hmemΔ D).mpr ⟨hDP, hD9⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hDΔ
  have key : Nonempty (autIn ⊤ D ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) ≃*
        Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) := by
    rcases hDΔ with h | h | h | h
    · exact absurd (h ▸ hE) (hnotGL D hDP hD9 hDV)
    · exact absurd (h ▸ hF) (hnotGL D hDP hD9 hDV)
    · subst h
      exact ⟨hA, hNa y hyD hyZ⟩
    · subst h
      obtain ⟨eA⟩ := hA
      refine ⟨⟨(Sporadic.autInTopCongr (MulAut.conj t⁻¹) A).symm.trans eA⟩, ?_⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hyD
      have haZ : a ∉ (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) := by
        intro haZ
        apply hyZ
        have h1 := htZ a⁻¹ (inv_mem haZ)
        have h2 : (MulAut.conj t⁻¹).toMonoidHom a = a⁻¹ := by
          rw [inv_inv] at h1
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          calc t⁻¹ * a * t = t⁻¹ * (t * a⁻¹ * t⁻¹) * t := by rw [h1]
            _ = a⁻¹ := by group
        rw [h2]
        exact inv_mem haZ
      obtain ⟨eN⟩ := hNa a ha haZ
      exact ⟨(normalizerZpowersEquiv (MulAut.conj t⁻¹) a).trans eN⟩
  obtain ⟨hS3, hNy⟩ := key
  have hVO := eq_inSubgroup_pCore hNy hV2 hV4 hVC hCV
  have hsig := ((h414.2 S ⟨φ⟩ P D hDP hD9).2 hS3).2 y hyD hyZ
  have hM0p : IsPGroup 2 (R ⊔ V.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) :=
    IsPGroup.to_sup_of_normal_right' hR2 (hV2.map _)
      (hRC.trans (Subgroup.centralizer_le_normalizer _))
  have hDy : D ≤ Subgroup.centralizer ({y} : Set S) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hDe.1.is_comm.comm ⟨d, hd⟩ ⟨y, hyD⟩)
  have hM0inv : R ⊔ V.map (MulAut.conj : S →* MulAut S) ∈
      invariantPiSubgroups ⊤ (D.map (MulAut.conj : S →* MulAut S)) (piOf 2) := by
    refine ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hM0p, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    refine mem_normalizer_sup (hRN d ?_) ?_
    · exact Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (hDy hd)
    · exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hDV hd))
  obtain ⟨M, hM0M, hMmax⟩ := (Set.toFinite _).exists_le_maximal hM0inv
  have hMmem : M ∈ maxInvariantPiSubgroups ⊤ (D.map (MulAut.conj : S →* MulAut S)) (piOf 2) :=
    hMmax
  rw [← hsig] at hMmem
  obtain ⟨x, -, hxM⟩ := hMmem
  simp only at hxM
  rw [← hVO] at hxM
  have hVM : V.map (MulAut.conj : S →* MulAut S) ≤ M := le_sup_right.trans hM0M
  rw [← hxM, Subgroup.map_le_map_iff_of_injective hinj] at hVM
  have hcardc : Nat.card (conjugate V x) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hVeq : V = conjugate V x := Subgroup.eq_of_le_of_card_ge hVM hcardc.le
  rw [← hVeq] at hxM
  rw [hxM]
  exact le_sup_left.trans hM0M

theorem k462M12_of_item4_14
    (h414 : Item4_14) : K462M12 :=
  fun S _ hS => k462UAlphaAt_of_item4_14 h414 S hS

end Step462UAlphaM12

open Step462UAlphaM12

theorem step462UAlpha_of_j2_l27
    (hJ : K462J2) (hL27 : K462L27) : Step462UAlpha :=
  step462UAlpha_of hJ (k462M12_of_item4_14 Sporadic.rank3II_4_14) hL27

end CFSG.RankThree.PartTwo.Sec4
