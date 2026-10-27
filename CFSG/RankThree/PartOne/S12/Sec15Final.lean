module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools

public section

namespace CFSG.RankThree.PartOne

open scoped commutatorElement

namespace Sec15Final

open CFSG CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell

section General

variable {G : Type*} [Group G]

theorem inf_centralizer_ne_bot_of_normalized [Finite G] {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem le_of_isSylowOf_of_isPGroup [Finite G] {T N R : Subgroup G} (hT : IsSylowOf 2 T N)
    (hR : IsPGroup 2 R) (hTR : T ≤ R) (hRN : R ≤ N) : R ≤ T := by
  obtain ⟨k, hk⟩ := hR.index (T.subgroupOf R)
  have hk' : T.relIndex R = 2 ^ k := hk
  have h1 := Subgroup.relIndex_mul_relIndex T R N hTR hRN
  by_contra hRT
  have hne : T.relIndex R ≠ 1 := fun h => hRT (Subgroup.relIndex_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by rw [hk', pow_zero])
  exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left (hk' ▸ dvd_pow_self 2 hk0) _)

theorem exists_isMaximalTwoLocal_ge [Finite G] {L : Subgroup G} (hL : IsPLocal 2 L) :
    ∃ M : Subgroup G, L ≤ M ∧ IsMaximalTwoLocal M := by
  obtain ⟨M, ⟨hM, hLM⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | IsPLocal 2 K ∧ L ≤ K} (fun K => Nat.card K) (Set.toFinite _)
    ⟨L, hL, le_rfl⟩
  refine ⟨M, hLM, hM, fun H hMH hH => ?_⟩
  exact hMH.ne (Subgroup.eq_of_le_of_card_ge hMH.le (hmax H ⟨hH, hLM.trans hMH.le⟩))

theorem normalizer_le_of_forall_maximal [Finite G] {N Z X : Subgroup G} (hZ1 : Z ≠ ⊥)
    (hZ2 : IsPGroup 2 Z) (hX : X ≤ Subgroup.normalizer (Z : Set G))
    (hMX : ∀ M ∈ maximalTwoLocalsContaining (X : Set G), M ≤ N) :
    Subgroup.normalizer (Z : Set G) ≤ N := by
  obtain ⟨M, hle, hmax⟩ := exists_isMaximalTwoLocal_ge (L := Subgroup.normalizer (Z : Set G))
    ⟨Z, hZ1, hZ2, rfl⟩
  exact hle.trans (hMX M ⟨hmax, fun x hx => hle (hX hx)⟩)

theorem characteristic_iSup_map_mulAut {M : Type*} [Group M] (X : Subgroup M) :
    (⨆ α : MulAut M, X.map α.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_map]
  exact le_iSup (fun β : MulAut M => X.map β.toMonoidHom) (φ * α)

theorem conj_mem_map_subtype_of_characteristic {S : Subgroup G} {K : Subgroup S}
    (hK : K.Characteristic) {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) {w : G}
    (hw : w ∈ K.map S.subtype) : g * w * g⁻¹ ∈ K.map S.subtype := by
  obtain ⟨k, hk, rfl⟩ := hw
  let φ : MulAut S := Subgroup.normalizerMonoidHom S ⟨g, hg⟩
  have hφ : φ k ∈ K := (Subgroup.characteristic_iff_le_comap.mp hK) φ hk
  exact ⟨φ k, hφ, rfl⟩

theorem normalizer_le_normalizer_map_subtype_of_characteristic {S : Subgroup G}
    {K : Subgroup S} (hK : K.Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (K.map S.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_map_subtype_of_characteristic hK hg hh, fun hh => ?_⟩
  have := conj_mem_map_subtype_of_characteristic hK (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem normalizer_le_normalizer_of_characteristic {S T₁ : Subgroup G} (hT₁ : T₁ ≤ S)
    (hchar : (T₁.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (T₁ : Set G) := by
  have := normalizer_le_normalizer_map_subtype_of_characteristic (S := S) hchar
  rwa [Subgroup.map_subgroupOf_eq_of_le hT₁] at this

private theorem map_mulAut_centerTorsion_le {M : Type*} [Group M] (φ : MulAut M) :
    (BlueprintB2.centerTorsion 2 (⊤ : Subgroup M)).map φ.toMonoidHom ≤
      BlueprintB2.centerTorsion 2 (⊤ : Subgroup M) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨-, hc, hp⟩ := BlueprintB2.mem_centerTorsion_iff.mp hx
  rw [BlueprintB2.mem_centerTorsion_iff]
  refine ⟨trivial, fun k _ => ?_, ?_⟩
  · have h2 := congrArg φ (hc (φ.symm k) trivial)
    simpa using h2
  · show φ x ^ 2 = 1
    rw [← map_pow, hp, map_one]

private theorem iSup_map_mulAut_le_centerTorsion {M : Type*} [Group M] {X : Subgroup M}
    (hX : X ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup M)) :
    (⨆ α : MulAut M, X.map α.toMonoidHom) ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup M) :=
  iSup_le fun α => (Subgroup.map_mono hX).trans (map_mulAut_centerTorsion_le α)

theorem exists_mem_center_orderOf_two {K : Type*} [Group K] [Finite K] [Nontrivial K]
    (hK : IsPGroup 2 K) : ∃ z ∈ Subgroup.center K, orderOf z = 2 := by
  have hc : Nontrivial (Subgroup.center K) := hK.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center K) := hK.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center K) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨(x : K), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

end General

section PushingUpS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pushingUpS_iff {P : Subgroup G} {x : G} :
    x ∈ pushingUpS P ↔ x ∈ P ∧
      ∀ z ∈ inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P, z * x = x * z := by
  simp [pushingUpS, Subgroup.mem_centralizer_iff]

omit [Finite G] in
theorem pushingUpS_le (P : Subgroup G) : pushingUpS P ≤ P :=
  inf_le_left

theorem elemThompson_le_pushingUpS (P : Subgroup G) :
    elemThompson P 2 ≤ (pushingUpS P).subgroupOf P := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, mem_pushingUpS_iff]
  refine ⟨x.2, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hc := (BlueprintB2.mem_elemThompsonCenterTorsion_iff_centralizer.mp he).1
  exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc x hx)).symm

private theorem elemCenterIn_pushingUpS (P : Subgroup G) :
    elemCenterIn 2 (pushingUpS P) = elemCenterIn 2 P := by
  have hle : pushingUpS P ≤ P := pushingUpS_le P
  have h1 := BlueprintB2.elemThompsonCenterTorsion_map_subtype (p := 2) (R := ↥P)
    (Y := (pushingUpS P).subgroupOf P) (elemThompson_le_pushingUpS P)
  have h2 := elemCenterIn_map_subtype (S := G) 2 (A := P) ((pushingUpS P).subgroupOf P)
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at h2
  rw [← h2]
  exact congrArg (Subgroup.map P.subtype) h1

theorem centralizer_elemThompsonCenterTorsion_pushingUpS (P : Subgroup G) :
    Subgroup.centralizer
      (elemThompsonCenterTorsion ↥(pushingUpS P) 2 : Set ↥(pushingUpS P)) = ⊤ := by
  refine eq_top_iff.mpr fun s _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzG : (z : G) ∈ inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P := by
    have : (z : G) ∈ elemCenterIn 2 (pushingUpS P) := ⟨z, hz, rfl⟩
    rwa [elemCenterIn_pushingUpS] at this
  exact Subtype.ext ((mem_pushingUpS_iff.mp s.2).2 _ hzG)

private theorem conj_mem_elemCenterIn {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) {z : G} (hz : z ∈ elemCenterIn 2 P) :
    g * z * g⁻¹ ∈ elemCenterIn 2 P := by
  obtain ⟨e, he, rfl⟩ := hz
  let φ : MulAut P := Subgroup.normalizerMonoidHom P ⟨g, hg⟩
  have hφ : φ e ∈ elemThompsonCenterTorsion P 2 :=
    Subgroup.characteristic_iff_le_comap.mp
      (BlueprintB2.elemThompsonCenterTorsion_characteristic P 2) φ he
  exact ⟨φ e, hφ, rfl⟩

theorem conj_mem_pushingUpS {P : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    {h : G} (hh : h ∈ pushingUpS P) : g * h * g⁻¹ ∈ pushingUpS P := by
  obtain ⟨hhP, hhc⟩ := mem_pushingUpS_iff.mp hh
  refine mem_pushingUpS_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg h).mp hhP, fun z hz => ?_⟩
  have hz' : g⁻¹ * z * g⁻¹⁻¹ ∈ elemCenterIn 2 P := conj_mem_elemCenterIn (inv_mem hg) hz
  have hcomm := hhc _ hz'
  calc z * (g * h * g⁻¹) = g * ((g⁻¹ * z * g⁻¹⁻¹) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * z * g⁻¹⁻¹)) * g⁻¹ := by rw [hcomm]
    _ = g * h * g⁻¹ * z := by group

theorem normalizer_le_normalizer_pushingUpS (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (pushingUpS P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_pushingUpS hg, fun hh => ?_⟩
  have := conj_mem_pushingUpS (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

omit [Finite G] in
theorem mem_omegaOneCenterIn_iff {P : Subgroup G} {z : G} :
    z ∈ omegaOneCenterIn P ↔ z ∈ P ∧ (∀ k ∈ P, k * z = z * k) ∧ z ^ 2 = 1 := by
  have h : omegaOneCenterIn P = BlueprintB2.centerTorsion 2 P :=
    (BlueprintB2.centerTorsion_eq_closure 2 P).symm
  rw [h]
  exact BlueprintB2.mem_centerTorsion_iff

omit [Finite G] in
theorem omegaOneCenterIn_le (P : Subgroup G) : omegaOneCenterIn P ≤ P :=
  fun _ h => (mem_omegaOneCenterIn_iff.mp h).1

theorem omegaOneCenterIn_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    omegaOneCenterIn P ≠ ⊥ := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨x, hxc, hx2⟩ := exists_mem_center_orderOf_two hP
  have hxsq : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hgmem : (x : G) ∈ omegaOneCenterIn P :=
    mem_omegaOneCenterIn_iff.mpr ⟨x.2, fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩), by
        simpa using congrArg Subtype.val hxsq⟩
  intro h
  rw [h, Subgroup.mem_bot] at hgmem
  have hx1 : x = 1 := Subtype.ext hgmem
  rw [hx1, orderOf_one] at hx2
  omega

omit [Finite G] in
theorem omegaOneCenterIn_le_pushingUpS (P : Subgroup G) : omegaOneCenterIn P ≤ pushingUpS P := by
  intro z hz
  obtain ⟨hzP, hzc, -⟩ := mem_omegaOneCenterIn_iff.mp hz
  refine mem_pushingUpS_iff.mpr ⟨hzP, fun w hw => ?_⟩
  have hwP : w ∈ P := by
    obtain ⟨e, -, rfl⟩ := hw
    exact e.2
  exact hzc w hwP

theorem pushingUpS_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    pushingUpS P ≠ ⊥ := fun h =>
  omegaOneCenterIn_ne_bot hP hP1
    (le_bot_iff.mp ((omegaOneCenterIn_le_pushingUpS P).trans h.le))

omit [Finite G] in
theorem subgroupOf_omegaOneCenterIn_le (P : Subgroup G) :
    (omegaOneCenterIn P).subgroupOf (pushingUpS P) ≤
      omegaOne 2 (Subgroup.center ↥(pushingUpS P)) := by
  intro s hs
  obtain ⟨-, hc, hsq⟩ := mem_omegaOneCenterIn_iff.mp (Subgroup.mem_subgroupOf.mp hs)
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k (pushingUpS_le P k.2))
  · exact Subtype.ext hsq

end PushingUpS

end Sec15Final

open Sec15Final
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem exists_sylow_eq_of_isSylowOf {G : Type} [Group G] [Finite G] {N T X : Subgroup G}
    (hT : IsSylowOf 2 T N) (hT1 : T ≠ ⊥) (hX : X ≤ Subgroup.normalizer (pushingUpS T : Set G))
    (hMX : ∀ M ∈ CFSG.maximalTwoLocalsContaining (X : Set G), M ≤ N) :
    ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨T', hTT'⟩ := hT2.exists_le_sylow
  refine ⟨T', le_antisymm ?_ hTT'⟩
  by_contra hle
  have hnil : Group.IsNilpotent ↥(T' : Subgroup G) := T'.isPGroup'.isNilpotent
  have hproper : T.subgroupOf (T' : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hle ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥(T' : Subgroup G)) ∈ T.subgroupOf (T' : Subgroup G) := by
      rw [h]
      trivial
    exact this
  obtain ⟨x, hx_norm, hx_not⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥(T' : Subgroup G)) _ hproper)
  have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf (T' : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq hTT']
      exact hx_norm
    exact this
  have hP₁T' : T ⊔ Subgroup.zpowers (x : G) ≤ T' := sup_le hTT' (Subgroup.zpowers_le.mpr x.2)
  have hP₁2 : IsPGroup 2 (T ⊔ Subgroup.zpowers (x : G) : Subgroup G) :=
    T'.isPGroup'.to_le hP₁T'
  have hP₁N : T ⊔ Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (T : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
  have hSN := normalizer_le_of_forall_maximal (Z := pushingUpS T) (pushingUpS_ne_bot hT2 hT1)
    (hT2.to_le (pushingUpS_le T)) hX hMX
  have hxT := le_of_isSylowOf_of_isPGroup hT hP₁2 le_sup_left
    ((hP₁N.trans (normalizer_le_normalizer_pushingUpS T)).trans hSN)
  exact hx_not (hxT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

@[expose] def PushingUpCorollary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ (T : Sylow 2 G) (N : Subgroup G), N ≠ ⊤ →
      (∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T : Subgroup G) →
        (T₁.subgroupOf (pushingUpS (T : Subgroup G))).Characteristic →
          Subgroup.normalizer (T₁ : Set G) ≤ N) →
      (∀ T₂ : Subgroup G, T₂ ≠ ⊥ → T₂ ≤ omegaOneCenterIn (T : Subgroup G) →
          Subgroup.centralizer (T₂ : Set G) ≤ N) →
      (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
      (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
        Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
      ∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

theorem pushing_up_contradiction (hPU : PushingUpCorollary) (hlist : KFCGTList)
    (hsect : ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.IsCharTwoType G →
      (∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
      CFSG.Assembly.evenRank G ≤ 2)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (he : CFSG.Assembly.evenRank G = 3) {N T X Y : Subgroup G} (hN : N ≠ ⊤)
    (hT : IsSylowOf 2 T N) (hT1 : T ≠ ⊥)
    (hX : X ≤ Subgroup.normalizer (pushingUpS T : Set G))
    (hY : Y ≤ Subgroup.centralizer (omegaOneCenterIn T : Set G))
    (hMX : ∀ M ∈ CFSG.maximalTwoLocalsContaining (X : Set G), M ≤ N)
    (hMY : ∀ M ∈ CFSG.maximalTwoLocalsContaining (Y : Set G), M ≤ N) : False := by
  obtain ⟨T', rfl⟩ := exists_sylow_eq_of_isSylowOf hT hT1 hX hMX
  have hP2 : IsPGroup 2 (T' : Subgroup G) := T'.isPGroup'
  have hT₁ : ∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T' : Subgroup G) →
      (T₁.subgroupOf (pushingUpS (T' : Subgroup G))).Characteristic →
        Subgroup.normalizer (T₁ : Set G) ≤ N := by
    intro T₁ hT₁1 hT₁S hT₁char
    have hT₁2 : IsPGroup 2 T₁ := (hP2.to_le (pushingUpS_le _)).to_le hT₁S
    have hXT₁ : X ≤ Subgroup.normalizer (T₁ : Set G) :=
      hX.trans (normalizer_le_normalizer_of_characteristic hT₁S hT₁char)
    exact normalizer_le_of_forall_maximal hT₁1 hT₁2 hXT₁ hMX
  have hT₂ : ∀ T₂ : Subgroup G, T₂ ≠ ⊥ → T₂ ≤ omegaOneCenterIn (T' : Subgroup G) →
      Subgroup.centralizer (T₂ : Set G) ≤ N := by
    intro T₂ hT₂1 hT₂le
    have hT₂2 : IsPGroup 2 T₂ := hP2.to_le (hT₂le.trans (omegaOneCenterIn_le _))
    have hYT₂ : Y ≤ Subgroup.normalizer (T₂ : Set G) :=
      hY.trans ((Subgroup.centralizer_le (fun x hx => hT₂le hx)).trans
        (Subgroup.centralizer_le_normalizer _))
    exact (Subgroup.centralizer_le_normalizer _).trans
      (normalizer_le_of_forall_maximal hT₂1 hT₂2 hYT₂ hMY)
  rcases hPU G hK hchar T' N hN hT₁ hT₂ with h | h | h
  · exact absurd (hlist G hchar (Or.inl h)) (by omega)
  · exact absurd (hlist G hchar (Or.inr h)) (by omega)
  · exact absurd (hsect G hchar h) (by omega)

@[expose] def PushingUpCorollaryΩ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ (T : Sylow 2 G) (N : Subgroup G), N ≠ ⊤ →
      (∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T : Subgroup G) →
        (T₁.subgroupOf (pushingUpS (T : Subgroup G))).Characteristic →
          Subgroup.normalizer (T₁ : Set G) ≤ N) →
      Subgroup.centralizer (omegaOneCenterIn (T : Subgroup G) : Set G) ≤ N →
      (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
      (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
        Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
      ∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

theorem pushingUpCorollary_of_omega (h : PushingUpCorollaryΩ) : PushingUpCorollary := by
  intro G _ _ _ hK hchar T N hN hT₁ hT₂
  by_cases hT : (T : Subgroup G) = ⊥
  · have hT' : Nat.card (T : Subgroup G) = 1 := by
      rw [hT]
      exact Subgroup.card_bot
    refine Or.inr (Or.inr fun P hP => ⟨∅, by simp, ?_⟩)
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    have h1 : Nat.card (Q : Subgroup G) = Nat.card (T : Subgroup G) := by
      rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity T]
    have hQbot : (Q : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp (h1.trans hT')
    have hPbot : P = ⊥ := le_bot_iff.mp (hQ.trans hQbot.le)
    simp [hPbot]
  · exact h G hK hchar T N hN hT₁
      (hT₂ _ (omegaOneCenterIn_ne_bot T.isPGroup' hT) le_rfl)

theorem pushing_up_contradiction_omega (hPU : PushingUpCorollaryΩ) (hlist : KFCGTList)
    (hsect : ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.IsCharTwoType G →
      (∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
      CFSG.Assembly.evenRank G ≤ 2)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (he : CFSG.Assembly.evenRank G = 3) {N T X : Subgroup G} (hN : N ≠ ⊤)
    (hT : IsSylowOf 2 T N) (hT1 : T ≠ ⊥)
    (hX : X ≤ Subgroup.normalizer (pushingUpS T : Set G))
    (hΩ : Subgroup.centralizer (omegaOneCenterIn T : Set G) ≤ N)
    (hMX : ∀ M ∈ CFSG.maximalTwoLocalsContaining (X : Set G), M ≤ N) : False := by
  obtain ⟨T', rfl⟩ := exists_sylow_eq_of_isSylowOf hT hT1 hX hMX
  have hP2 : IsPGroup 2 (T' : Subgroup G) := T'.isPGroup'
  have hT₁ : ∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T' : Subgroup G) →
      (T₁.subgroupOf (pushingUpS (T' : Subgroup G))).Characteristic →
        Subgroup.normalizer (T₁ : Set G) ≤ N := by
    intro T₁ hT₁1 hT₁S hT₁char
    have hT₁2 : IsPGroup 2 T₁ := (hP2.to_le (pushingUpS_le _)).to_le hT₁S
    have hXT₁ : X ≤ Subgroup.normalizer (T₁ : Set G) :=
      hX.trans (normalizer_le_normalizer_of_characteristic hT₁S hT₁char)
    exact normalizer_le_of_forall_maximal hT₁1 hT₁2 hXT₁ hMX
  rcases hPU G hK hchar T' N hN hT₁ hΩ with h | h | h
  · exact absurd (hlist G hchar (Or.inl h)) (by omega)
  · exact absurd (hlist G hchar (Or.inr h)) (by omega)
  · exact absurd (hsect G hchar h) (by omega)

end CFSG.RankThree.PartOne
