module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProofUAlphaM12
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofL27
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def K462J2Inner : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* Blueprint.NativeSporadic.J2) →
    ∀ y : S, y ^ 3 = 1 → y ≠ 1 →
    Nonempty (Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) →
    ∀ W : Subgroup S, IsPGroup 2 W →
      W ≤ Subgroup.centralizer
        ((inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set S)) : Subgroup S) : Set S) →
      (∀ n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S),
        n ∈ Subgroup.normalizer (W : Set S)) →
      W ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set S))

namespace Res462J2

theorem not_mem_inf_centralizer (h415 : Item4_15) {S : Type} [Group S] [Finite S]
    (hS : Nonempty (S ≃* Blueprint.NativeSporadic.J2)) (P : Sylow 3 S) {y : S} (hy1 : y ≠ 1)
    {V : Subgroup S} (hV4 : Nat.card V = 4)
    (hVC : V ≤ Subgroup.centralizer ({y} : Set S))
    (hCV : ∀ s ∈ Subgroup.centralizer ({y} : Set S), s ∈ Subgroup.normalizer (V : Set S)) :
    y ∉ (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) := by
  intro hyZ
  obtain ⟨hZ3, -, hext⟩ := Sec14.j2_sylow_facts h415 hS P
  have hyZ' : Subgroup.zpowers y =
      (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) := by
    have hle : Subgroup.zpowers y ≤
        (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) :=
      Subgroup.zpowers_le.mpr hyZ
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hdvd : Nat.card (Subgroup.zpowers y) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      apply hy1
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact h1
    · rw [h3, hZ3]
  have hCZ : Subgroup.centralizer
      (((P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S) : Subgroup S) :
        Set S) = Subgroup.centralizer ({y} : Set S) := by
    rw [← hyZ', Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hCZ] at hext
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  have hVn : (V.subgroupOf (Subgroup.centralizer ({y} : Set S))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).mpr fun s hs => hCV s hs
  have hV'4 : Nat.card (V.subgroupOf (Subgroup.centralizer ({y} : Set S))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hV4]
  set f : Subgroup.centralizer ({y} : Set S) →* alternatingGroup (Fin 6) :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' K) with hf
  have hfs : Function.Surjective f :=
    eQ.surjective.comp (QuotientGroup.mk'_surjective K)
  have hmap : ((V.subgroupOf (Subgroup.centralizer ({y} : Set S))).map f).Normal :=
    hVn.map f hfs
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((V.subgroupOf (Subgroup.centralizer ({y} : Set S))).map f) with h | h
  ·
    have hle : V.subgroupOf (Subgroup.centralizer ({y} : Set S)) ≤ K := by
      intro v hv
      have h1 : f v ∈ (V.subgroupOf (Subgroup.centralizer ({y} : Set S))).map f :=
        Subgroup.mem_map_of_mem f hv
      rw [h, Subgroup.mem_bot, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hK3 : Nat.card K = 3 := by
      rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hV'4, hK3] at hdvd
    norm_num at hdvd
  ·
    have hcard : Nat.card ((V.subgroupOf (Subgroup.centralizer ({y} : Set S))).map f) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) (hV'4 ▸ Subgroup.card_map_dvd _ _)
    rw [h, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    norm_num [Nat.factorial] at hcard

theorem eq_pCore_normalizer {S : Type} [Group S] [Finite S] {y : S} {V : Subgroup S}
    (hN : Nonempty (Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)))
    (hVO : V = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set S)))
    (hV2 : IsPGroup 2 V) (hV4 : Nat.card V = 4) :
    V = inSubgroup (CFSG.pCore 2)
      (Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S)) := by
  obtain ⟨e⟩ := hN
  set Nz := Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) with hNz
  have hVC : V ≤ Subgroup.centralizer ({y} : Set S) := hVO ▸ Subgroup.map_subtype_le _
  have hVN : V ≤ Nz := fun v hv =>
    Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (hVC hv)
  have hNV : ∀ g ∈ Nz, g ∈ Subgroup.normalizer (V : Set S) := fun g hg => by
    rw [hVO]
    exact Step462UAlphaProof.mem_normalizer_inSubgroup_pCore
      (Step462UAlphaProof.mem_normalizer_centralizer_singleton hg)
  have hle : V ≤ inSubgroup (CFSG.pCore 2) Nz :=
    Sporadic.J2.le_inSubgroup_pCore hVN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mpr hNV) hV2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  set O := CFSG.pCore 2 Nz with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hOe : (O.map e.toMonoidHom).Normal := hOn.map e.toMonoidHom e.surjective
  have hcard : Nat.card (O.map e.toMonoidHom) ≤ 4 :=
    Step462UAlphaM12.card_le_four_of_normal (hO2.map _)
  rw [Subgroup.card_map_of_injective e.injective] at hcard
  have hc : Nat.card (inSubgroup (CFSG.pCore 2) Nz) = Nat.card O :=
    Subgroup.card_map_of_injective Nz.subtype_injective
  rw [hc, hV4]
  exact hcard

theorem k462UAlphaAt_of_inner (h415 : Item4_15)
    (hIn : K462J2Inner) (S : Type) [Group S]
    (hS : Nonempty (S ≃* Blueprint.NativeSporadic.J2)) : K462UAlphaAt S := by
  intro D y V hDe hD9 hyD hy1 hV2 hV4 hVC hCV hDV R hR2 hRC hRN
  obtain ⟨φ⟩ := hS
  have : Finite S := Finite.of_equiv _ φ.symm.toEquiv
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  have hZS : Subgroup.center S = ⊥ := by
    have hZ : Subgroup.center Blueprint.NativeSporadic.J2 = ⊥ :=
      Item462Proof.center_eq_bot_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
        (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
    have h := Subgroup.map_center_eq φ
    rw [hZ] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
  have hinj := Step462UAlphaM12.conj_injective hZS
  have hy3 : y ^ 3 = 1 := hDe.2 y hyD
  obtain ⟨P, hDP⟩ := (Sec5.isPGroup_of_isElemAbelian hDe).exists_le_sylow
  have hyZ := not_mem_inf_centralizer h415 ⟨φ⟩ P hy1 hV4 hVC hCV
  obtain ⟨-, -, -, h4, -⟩ := h415 S ⟨φ⟩ P _ rfl _ rfl
  obtain ⟨-, hNy, -, hmax⟩ := h4 D ⟨hDP, hD9⟩ y hyD hyZ
  have hVO := Step462UAlphaM12.eq_inSubgroup_pCore hNy hV2 hV4 hVC hCV
  have hVN := eq_pCore_normalizer hNy hVO hV2 hV4
  have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers y)
  have hNV : ∀ n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S),
      n ∈ Subgroup.normalizer (V : Set S) := fun n hn => by
    rw [hVO]
    exact Step462UAlphaProof.mem_normalizer_inSubgroup_pCore
      (Step462UAlphaProof.mem_normalizer_centralizer_singleton hn)
  set W : Subgroup S := R.comap (MulAut.conj : S →* MulAut S) with hW
  have hW2 : IsPGroup 2 W := hR2.comap_of_injective _ hinj
  have hWC : W ≤ Subgroup.centralizer
      ((inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set S)) : Subgroup S) :
        Set S) := by
    intro w hw
    rw [← hVO, Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := Subgroup.mem_centralizer_iff.mp (hRC hw) (MulAut.conj v)
      (Subgroup.mem_map_of_mem _ hv)
    apply hinj
    rw [map_mul, map_mul]
    exact h1
  have hWN : ∀ n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S),
      n ∈ Subgroup.normalizer (W : Set S) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.mp (hRN n hn) (MulAut.conj w)
    rw [hW, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h1
  have hWV : W ≤ V := by
    rw [hVO]
    exact hIn S ⟨φ⟩ y hy3 hy1 hNy W hW2 hWC hWN
  have hRy : ∀ α ∈ R, α y = y := by
    intro α hα
    have hc : MulAut.conj (α y * y⁻¹) ∈ R := by
      have h1 : MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hRN y hyN) α⁻¹).mp (R.inv_mem hα)
      have h2 := R.mul_mem hα h1
      have e : α * (MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹) = MulAut.conj (α y * y⁻¹) := by
        rw [map_mul, map_inv, ← Sporadic.J2.mulAut_mul_conj]
        group
      rwa [e] at h2
    have hw : α y * y⁻¹ ∈ V := hWV hc
    have hwy : (α y * y⁻¹) * y = y * (α y * y⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hVC hw)
    have hw3 : (α y * y⁻¹) ^ 3 = 1 := by
      have h1 : (α y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
      have h2 : α y = (α y * y⁻¹) * y := by group
      rw [h2, (Commute.mul_pow hwy 3), hy3, mul_one] at h1
      exact h1
    obtain ⟨k, hk⟩ := Sporadic.J2.two_of_mem hV2 hw
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h1 : α y * y⁻¹ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one hk))
    calc α y = (α y * y⁻¹) * y := by group
      _ = y := by rw [h1, one_mul]
  have hRN' : R ≤ Subgroup.normalizer
      ((Subgroup.zpowers (MulAut.conj y) : Subgroup (MulAut S)) : Set (MulAut S)) := by
    intro α hα
    refine Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Sporadic.J2.mulAut_mul_conj α y
    rw [hRy α hα] at h1
    calc α * MulAut.conj y = α * MulAut.conj y * α⁻¹ * α := by group
      _ = MulAut.conj y * α := by rw [h1]
  set IV := V.map (MulAut.conj : S →* MulAut S) with hIV
  have hY2 : IsPGroup 2 (R ⊔ IV : Subgroup (MulAut S)) :=
    IsPGroup.to_sup_of_normal_right' hR2 (hV2.map _)
      (hRC.trans (Subgroup.centralizer_le_normalizer _))
  have hIVN : IV ≤ Subgroup.normalizer
      ((Subgroup.zpowers (MulAut.conj y) : Subgroup (MulAut S)) : Set (MulAut S)) := by
    rintro _ ⟨v, hv, rfl⟩
    refine Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    show MulAut.conj v * MulAut.conj y = MulAut.conj y * MulAut.conj v
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hVC hv)]
  have hYmem : R ⊔ IV ∈ invariantPiSubgroups
      (Subgroup.normalizer
        ((Subgroup.zpowers (MulAut.conj y) : Subgroup (MulAut S)) : Set (MulAut S)))
      ((Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S)).map
        (MulAut.conj : S →* MulAut S)) (piOf 2) := by
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    refine ⟨sup_le hRN' hIVN, hY2, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact Step462UAlphaM12.mem_normalizer_sup (hRN n hn)
      (Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hNV n hn)))
  rw [← hVN] at hmax
  have heq := (mem_maxInvariantPiSubgroups_iff.mp hmax).2 _ hYmem le_sup_right
  exact le_sup_left.trans heq.le

end Res462J2

open Res462J2

theorem k462J2_of_inner
    (hIn : K462J2Inner) :
    K462J2 :=
  fun S _ hS => k462UAlphaAt_of_inner Sporadic.rank3II_4_15 hIn S hS

theorem step462UAlpha_of_j2Inner
    (hIn : K462J2Inner) :
    Step462UAlpha :=
  step462UAlpha_of_j2_l27 (k462J2_of_inner hIn) k462L27

end CFSG.RankThree.PartTwo.Sec4
