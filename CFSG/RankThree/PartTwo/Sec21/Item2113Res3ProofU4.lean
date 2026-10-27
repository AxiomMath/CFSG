module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofU4
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def Item2115U4FusedA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    ∀ x ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G), x ^ 3 = 1 →
      ∃ h ∈ L, h * x * h⁻¹ ∈ A

@[expose] def Item2115U4Thompson : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    ∃ P : Subgroup G, A ≤ P ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)) ∧
      ∀ B : Subgroup G, B ≤ P → CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 3 ^ 4 → B = A

@[expose] def Item2115U4Signalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    (∃ P : Sylow 3 G, (P : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)) →
    (∀ g : G, g * c * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers c) →
    ∀ e ∈ E, e ≠ 1 → ∀ S : Subgroup G, IsPGroup 2 S →
      S ≤ Subgroup.closure {y | ∃ g ∈ Subgroup.centralizer ({e} : Set G), y = g * c * g⁻¹} →
      c ∈ Subgroup.normalizer (S : Set G) → S = ⊥

namespace Item2113Res3Proof

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylow_of_normalizer_le {P H : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H)
    (hN : normalizer (P : Set G) ≤ H) : ∃ S : Sylow 3 G, (S : Subgroup G) = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hP
  have hPH : P ≤ H := by
    rw [← hQ]
    exact map_subtype_le _
  have hP3 : IsPGroup 3 P := by
    rw [← hQ]
    exact Q.isPGroup'.map H.subtype
  have hmaxH : ∀ R : Subgroup G, IsPGroup 3 R → P ≤ R → R ≤ H → R = P := by
    intro R hR hPR hRH
    have hR' : IsPGroup 3 (R.subgroupOf H) :=
      hR.comap_of_injective H.subtype H.subtype_injective
    have hle : (Q : Subgroup H) ≤ R.subgroupOf H := by
      intro q hq
      rw [mem_subgroupOf]
      exact hPR (hQ ▸ mem_map_of_mem H.subtype hq)
    have heq := Q.is_maximal' hR' hle
    apply le_antisymm _ hPR
    intro r hr
    have hr' : (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H := mem_subgroupOf.mpr hr
    rw [heq] at hr'
    rw [← hQ]
    exact mem_map.mpr ⟨_, hr', rfl⟩
  refine ⟨⟨P, hP3, fun {R} hR hPR => ?_⟩, rfl⟩
  by_contra hne
  have hlt : P < R := lt_of_le_of_ne hPR (Ne.symm hne)
  have : Finite R := inferInstance
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hcond := Group.normalizerCondition_of_isNilpotent (G := R)
  have hPR' : P.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm _ hPR
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ P.subgroupOf R := htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt (hcond _ hPR')
  have hyN' : (y : G) ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have h1 := (mem_normalizer_iff.mp hyN ⟨p, hPR hp⟩).mp (mem_subgroupOf.mpr hp)
      exact mem_subgroupOf.mp h1
    · intro hp
      have hmem : (y * ⟨p, ?_⟩ * y⁻¹ : R) ∈ P.subgroupOf R := mem_subgroupOf.mpr hp
      · exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hyN _).mpr hmem)
      · have : p = (y : G)⁻¹ * (y * p * (y : G)⁻¹) * y := by group
        rw [this]
        exact R.mul_mem (R.mul_mem (R.inv_mem y.2) (hPR hp)) y.2
  have hyH : (y : G) ∈ H := hN hyN'
  have hS3 : IsPGroup 3 (P ⊔ zpowers (y : G) : Subgroup G) := by
    refine hR.to_le (sup_le hPR ?_)
    rw [zpowers_le]
    exact y.2
  have hSH : P ⊔ zpowers (y : G) ≤ H := sup_le hPH (zpowers_le.mpr hyH)
  have hSeq := hmaxH _ hS3 le_sup_left hSH
  apply hyP
  rw [mem_subgroupOf]
  rw [← hSeq]
  exact mem_sup_right (mem_zpowers _)

theorem exists_mem_normalizer_conj_eq {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (P : Sylow 3 G) (hAP : A ≤ P)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A)
    {c c' x : G} (hc : c ∈ A) (hc' : c' ∈ A) (hx : x * c * x⁻¹ = c') :
    ∃ w ∈ normalizer (A : Set G), w * c * w⁻¹ = c' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer ({c'} : Set G) with hC
  have hA3 : IsPGroup 3 A := P.isPGroup'.to_le hAP
  set Ax := A.map (MulAut.conj x).toMonoidHom with hAx
  have hAC : A ≤ C := fun a ha => mem_centralizer_singleton_iff.mpr (hAc a ha c' hc')
  have hAxC : Ax ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hx]
    have h := hAc a ha c hc
    calc x * a * x⁻¹ * (x * c * x⁻¹) = x * (a * c) * x⁻¹ := by group
      _ = x * (c * a) * x⁻¹ := by rw [h]
      _ = x * c * x⁻¹ * (x * a * x⁻¹) := by group
  have hA3' : IsPGroup 3 (A.subgroupOf C) := hA3.comap_of_injective C.subtype C.subtype_injective
  have hAx3 : IsPGroup 3 Ax := hA3.map _
  have hAx3' : IsPGroup 3 (Ax.subgroupOf C) :=
    hAx3.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨Q₁, hQ₁⟩ := hA3'.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hAx3'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  set Q₁G : Subgroup G := (Q₁ : Subgroup C).map C.subtype with hQ₁G
  have hAQ : A ≤ Q₁G := by
    intro a ha
    exact mem_map.mpr ⟨⟨a, hAC ha⟩, hQ₁ (mem_subgroupOf.mpr ha), rfl⟩
  have hAyQ : Ax.map (MulAut.conj (y : G)).toMonoidHom ≤ Q₁G := by
    rintro _ ⟨b, hb, rfl⟩
    have hbQ₂ : (⟨b, hAxC hb⟩ : C) ∈ (Q₂ : Subgroup C) := hQ₂ (mem_subgroupOf.mpr hb)
    have hmem : y * ⟨b, hAxC hb⟩ * y⁻¹ ∈ ((y • Q₂ : Sylow 3 C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact mem_map.mpr ⟨_, hbQ₂, rfl⟩
    rw [hy] at hmem
    exact mem_map.mpr ⟨_, hmem, rfl⟩
  have hQ3 : IsPGroup 3 Q₁G := Q₁.isPGroup'.map C.subtype
  obtain ⟨R, hR⟩ := hQ3.exists_le_sylow
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq G P R
  have hRz : (R : Subgroup G) = (P : Subgroup G).map (MulAut.conj z).toMonoidHom := by
    rw [← hz, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have key : ∀ B : Subgroup G, B ≤ R → B.map (MulAut.conj z⁻¹).toMonoidHom ≤ P := by
    intro B hB
    rintro _ ⟨b, hb, rfl⟩
    have hbR := hB hb
    rw [hRz] at hbR
    obtain ⟨p, hp, rfl⟩ := hbR
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : z⁻¹ * (z * p * z⁻¹) * z⁻¹⁻¹ = p := by group
    rw [this]
    exact hp
  have hzA := hwc z⁻¹ (key A (hAQ.trans hR))
  have hz1 : ∀ a ∈ A, z * a * z⁻¹ ∈ A := by
    intro a ha
    rw [← hzA] at ha
    obtain ⟨a', ha', e⟩ := ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]
    have : z * (z⁻¹ * a' * z⁻¹⁻¹) * z⁻¹ = a' := by group
    rw [this]
    exact ha'
  have hgP : A.map (MulAut.conj (z⁻¹ * (y : G) * x)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (y : G) * (x * a * x⁻¹) * (y : G)⁻¹ ∈ (R : Subgroup G) :=
      hR (hAyQ ⟨x * a * x⁻¹, ⟨a, ha, rfl⟩, rfl⟩)
    rw [hRz] at h1
    obtain ⟨p, hp, hpe⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpe ⊢
    have e : z⁻¹ * (y : G) * x * a * (z⁻¹ * (y : G) * x)⁻¹ = p := by
      calc z⁻¹ * (y : G) * x * a * (z⁻¹ * (y : G) * x)⁻¹ =
          z⁻¹ * ((y : G) * (x * a * x⁻¹) * (y : G)⁻¹) * z := by group
        _ = z⁻¹ * (z * p * z⁻¹) * z := by rw [hpe]
        _ = p := by group
    rw [e]
    exact hp
  have hz2 : ∀ a ∈ A, z⁻¹ * ((y : G) * (x * a * x⁻¹) * (y : G)⁻¹) * z ∈ A := by
    intro a ha
    have h1 : (MulAut.conj (z⁻¹ * (y : G) * x)).toMonoidHom a ∈
        A.map (MulAut.conj (z⁻¹ * (y : G) * x)).toMonoidHom := mem_map_of_mem _ ha
    rw [hwc _ hgP] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have e : z⁻¹ * (y : G) * x * a * (z⁻¹ * (y : G) * x)⁻¹ =
        z⁻¹ * ((y : G) * (x * a * x⁻¹) * (y : G)⁻¹) * z := by group
    rwa [e] at h1
  refine ⟨(y : G) * x, mem_normalizer_fintype fun a ha => ?_, ?_⟩
  · have := hz1 _ (hz2 a ha)
    have e : (y : G) * x * a * ((y : G) * x)⁻¹ =
        z * (z⁻¹ * ((y : G) * (x * a * x⁻¹) * (y : G)⁻¹) * z) * z⁻¹ := by group
    rw [e]
    exact this
  · have hyc : (y : G) * c' = c' * y := (mem_centralizer_singleton_iff.mp y.2)
    calc (y : G) * x * c * ((y : G) * x)⁻¹ = (y : G) * (x * c * x⁻¹) * (y : G)⁻¹ := by group
      _ = c' := by rw [hx, hyc, mul_inv_cancel_right]

theorem item2115U4Fusion_of (hF1 : Item2115U4FusedA) (hF2 : Item2115U4Thompson) :
    Item2115U4Fusion := by
  intro G _ _ A E U c L hpair hU4 h81 hS4 hW
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hAP, hPsyl, hJ⟩ := hF2 G A E U c L hpair hU4 h81 hS4 hW
  have hAe := hpair.mem_S.1.1
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hLc : L ≤ centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  have hcard : ∀ g : G, Nat.card (A.map (MulAut.conj g).toMonoidHom) = 3 ^ 4 := fun g => by
    rw [card_map_of_injective (MulAut.conj g).injective, h81]
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have helem : ∀ g : G, CFSG.Assembly.IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) := by
    intro g
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      simp only [MulMemClass.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h := hAc a ha b hb
      calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [h]
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hAe.2 a ha, mul_one, mul_inv_cancel]
  have hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A := fun g hg => hJ _ hg (helem g) (hcard g)
  have hNP : normalizer (P : Set G) ≤
      normalizer ((zpowers c : Subgroup G) : Set G) := by
    intro g hg
    apply hW
    apply mem_normalizer_fintype
    intro a ha
    have hle : A.map (MulAut.conj g).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp hg b).mp (hAP hb)
    rw [← hwc g hle]
    exact mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨S, hS⟩ := isSylow_of_normalizer_le hPsyl hNP
  have hPH : P ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
    obtain ⟨Q, hQ⟩ := hPsyl
    rw [← hQ]
    exact map_subtype_le _
  refine ⟨⟨S, hS ▸ hPH⟩, fun g hg => ?_⟩
  obtain ⟨h, hhL, hhA⟩ := hF1 G A E U c L hpair hU4 h81 hS4 hW (g * c * g⁻¹) hg (by
    rw [conj_pow, hAe.2 c hcA, mul_one, mul_inv_cancel])
  have hAS : A ≤ (S : Subgroup G) := hS ▸ hAP
  have hwcS : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A := fun g hg => hwc g (hS ▸ hg)
  obtain ⟨w, hwA, hwc'⟩ := exists_mem_normalizer_conj_eq hAc S hAS hwcS hcA hhA
    (x := h * g) (by group)
  have hc' : h * (g * c * g⁻¹) * h⁻¹ ∈ zpowers c := by
    rw [← hwc']
    exact (mem_normalizer_iff.mp (hW hwA) c).mp (mem_zpowers c)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hc'
  have hhc : ∀ m : ℤ, h⁻¹ * c ^ m * h = c ^ m := by
    intro m
    have hcomm : Commute h (c ^ m) :=
      (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hLc hhL)) m).symm.symm
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have e : g * c * g⁻¹ = h⁻¹ * (h * (g * c * g⁻¹) * h⁻¹) * h := by group
  rw [e, ← hk, hhc k]
  exact zpow_mem (mem_zpowers c) k

theorem item2115U4Local_of (hS : Item2115U4Signalizer) : Item2115U4Local := by
  intro G _ _ A E U c L hpair hU4 h81 hS4 hW hP hfus e he he1 T hT2 hET
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEe := hpair.mem_E.1.1
  have hcE : c ∈ E := hpairs.1.1
  have hce : c * e = e * c := congrArg Subtype.val (hEe.1.is_comm.comm ⟨c, hcE⟩ ⟨e, he⟩)
  set Te := T ⊓ centralizer ({e} : Set G) with hTe
  have hcTe : c ∈ normalizer (Te : Set G) := by
    apply mem_normalizer_fintype
    rintro t ⟨htT, hte⟩
    have hte' : t * e = e * t := mem_centralizer_singleton_iff.mp hte
    refine ⟨(mem_normalizer_iff.mp (hET hcE) t).mp htT, mem_centralizer_singleton_iff.mpr ?_⟩
    calc c * t * c⁻¹ * e = c * t * (c⁻¹ * e) := by group
      _ = c * t * (e * c⁻¹) := by
          rw [show c⁻¹ * e = e * c⁻¹ from by
            calc c⁻¹ * e = c⁻¹ * (e * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * e) * c⁻¹ := by rw [hce]
              _ = e * c⁻¹ := by group]
      _ = c * (t * e) * c⁻¹ := by group
      _ = c * (e * t) * c⁻¹ := by rw [hte']
      _ = (c * e) * t * c⁻¹ := by group
      _ = (e * c) * t * c⁻¹ := by rw [hce]
      _ = e * (c * t * c⁻¹) := by group
  have hzc : zpowers c ≤ normalizer (Te : Set G) := zpowers_le.mpr hcTe
  set S := ⁅Te, zpowers c⁆ with hSdef
  set Xe : Subgroup G :=
    closure {y | ∃ g ∈ centralizer ({e} : Set G), y = g * c * g⁻¹} with hXe
  have hcXe : c ∈ Xe := by
    apply Subgroup.subset_closure
    show ∃ g ∈ centralizer ({e} : Set G), c = g * c * g⁻¹
    exact ⟨1, one_mem _, by group⟩
  have hSTe : S ≤ Te := by
    rw [hSdef, commutator_le]
    intro t ht w hw
    have hw' : w * t⁻¹ * w⁻¹ ∈ Te := (mem_normalizer_iff.mp (hzc hw) t⁻¹).mp (inv_mem ht)
    rw [commutatorElement_def]
    have e1 : t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
    rw [e1]
    exact mul_mem ht hw'
  have hS2 : IsPGroup 2 S := hT2.to_le (hSTe.trans inf_le_left)
  have hSXe : S ≤ Xe := by
    rw [hSdef, commutator_le]
    intro t ht w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hgen : t * c * t⁻¹ ∈ Xe := by
      apply Subgroup.subset_closure
      show ∃ g ∈ centralizer ({e} : Set G), t * c * t⁻¹ = g * c * g⁻¹
      exact ⟨t, ht.2, rfl⟩
    have h1 : t * c ^ k * t⁻¹ ∈ Xe := by
      rw [← conj_zpow]
      exact zpow_mem hgen k
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem (zpow_mem hcXe k))
  have hcS : c ∈ normalizer (S : Set G) := by
    have h1 : Te.map (MulAut.conj c).toMonoidHom ≤ Te := by
      rintro _ ⟨t, ht, rfl⟩
      exact (mem_normalizer_iff.mp hcTe t).mp ht
    have h2 : (zpowers c).map (MulAut.conj c).toMonoidHom ≤ zpowers c := by
      rw [MonoidHom.map_zpowers, zpowers_le]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_cancel_right]
      exact mem_zpowers c
    apply mem_normalizer_fintype
    intro s hs
    have h3 : (MulAut.conj c).toMonoidHom s ∈ S.map (MulAut.conj c).toMonoidHom :=
      mem_map_of_mem _ hs
    rw [hSdef, map_commutator] at h3
    exact commutator_mono h1 h2 h3
  have hSbot := hS G A E U c L hpair hU4 h81 hS4 hW hP hfus e he he1 S hS2 hSXe hcS
  have hcomm : Te ≤ centralizer (zpowers c : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hSbot
  intro t ht
  rw [mem_centralizer_singleton_iff]
  exact ((mem_centralizer_iff.mp (hcomm ht) c (mem_zpowers c))).symm

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
