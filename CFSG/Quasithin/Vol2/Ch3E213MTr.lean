module

public import CFSG.Quasithin.Vol2.Ch3nE2
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6

theorem mem_conjugate {K : Type*} [Group K] {A : Subgroup K} {g x : K} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  show x ∈ conjSub g⁻¹ A ↔ _
  rw [mem_conjSub, inv_inv]

theorem map_conjugate_eq {K K' : Type*} [Group K] [Group K'] (f : K →* K') (A : Subgroup K)
    (g : K) : (CFSG.conjugate A g).map f = CFSG.conjugate (A.map f) (f g) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g⁻¹ * a * g, ⟨a, ha, by simp⟩, by simp⟩

variable {G : Type*} [Group G] {H : Subgroup G}

theorem map_subtype_conjugate (A : Subgroup H) (x : H) :
    (CFSG.conjugate A x).map H.subtype = conjSub (x : G)⁻¹ (A.map H.subtype) := by
  rw [map_conjugate_eq]
  rfl

theorem map_subtype_inSubgroup_pCore (p : ℕ) (A : Subgroup H) :
    (inSubgroup (CFSG.pCore p) A).map H.subtype = pCoreOf p (A.map H.subtype) := by
  set e : A ≃* A.map H.subtype := A.equivMapOfInjective H.subtype H.subtype_injective
  have he : H.subtype.comp A.subtype = (A.map H.subtype).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [inSubgroup, pCoreOf, Subgroup.map_map, he, ← Subgroup.map_map,
    CFSG.LieType.BorelTits.map_pCore_mulEquiv]

theorem isSylowTwoOf_map_subtype [Finite G] {S A : Subgroup H}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 S A) :
    IsSylowTwoOf (S.map H.subtype) (A.map H.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h
  obtain ⟨hle, hS, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hS.map _, ?_⟩
  show ¬ 2 ∣ (S.map H.subtype).relIndex (A.map H.subtype)
  rwa [Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective]

theorem exists_sylow_subgroupOf [Finite G] {T : Subgroup G} (h : IsSylowTwoOf T H) :
    ∃ T' : Sylow 2 H, (T' : Subgroup H) = T.subgroupOf H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (T.subgroupOf H) := h.2.1.comap_subtype
  exact ⟨hP.toSylow h.2.2, IsPGroup.toSylow_coe _ _⟩

theorem charTwo_map_subtype_of_isCharacteristicP {A : Subgroup H}
    (hA : CFSG.IsCharacteristicP 2 A) : CharTwo (A.map H.subtype) := by
  apply CFSG.QuasithinUnique.charTwo_map_subtype
  have h : Subgroup.centralizer (CFSG.pCore 2 A : Set A) ≤ CFSG.pCore 2 A := hA
  assumption

theorem isCharacteristicP_of_charTwo (h : CharTwo H) : CFSG.IsCharacteristicP 2 H :=
  CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.mp h

theorem map_subtype_iInf_conjugate (A I : Subgroup H) :
    (⨅ i ∈ I, CFSG.conjugate A i).map H.subtype = kerIn (A.map H.subtype) (I.map H.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ b ⟨i, hi, rfl⟩
    have hyi : y ∈ CFSG.conjugate A i := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy i) hi
    exact ⟨i * y * i⁻¹, mem_conjugate.1 hyi, by simp⟩
  · intro hx
    have hx1 := hx 1 (I.map H.subtype).one_mem
    rw [one_mul, inv_one, mul_one] at hx1
    obtain ⟨y, -, rfl⟩ := hx1
    refine ⟨y, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.2 fun hi => ?_, rfl⟩
    obtain ⟨a, ha, hae⟩ := hx (i : G) ⟨i, hi, rfl⟩
    have hae' : a = i * y * i⁻¹ := H.subtype_injective (by simpa using hae)
    exact mem_conjugate.2 (hae' ▸ ha)

theorem iInf_conjugate_eq_kerIn {K : Type*} [Group K] (A I : Subgroup K) :
    (⨅ i ∈ I, CFSG.conjugate A i) = kerIn A I := by
  ext x
  simp only [Subgroup.mem_iInf, mem_kerIn, mem_conjugate]

theorem map_subtype_kerIn (A I : Subgroup H) :
    (kerIn A I).map H.subtype = kerIn (A.map H.subtype) (I.map H.subtype) := by
  rw [← iInf_conjugate_eq_kerIn, map_subtype_iInf_conjugate]

theorem isElementaryAbelian_subgroupOf {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsElementaryAbelian 2 (V.subgroupOf H) where
  is_comm := ⟨fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val (hV.1.is_comm.comm ⟨((a : H) : G), a.2⟩ ⟨((b : H) : G), b.2⟩)
    simpa using this⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
    Subtype.ext (Subtype.ext (hV.2 _ a.2))

theorem relIndex_pCoreOf_map_subtype [Finite G] (I : Subgroup H) :
    (pCoreOf 2 (I.map H.subtype)).relIndex (I.map H.subtype) =
      Nat.card (I ⧸ CFSG.pCore 2 I) := by
  set e : I ≃* I.map H.subtype := I.equivMapOfInjective H.subtype H.subtype_injective
  have h1 : (pCoreOf 2 (I.map H.subtype)).relIndex (I.map H.subtype) =
      (CFSG.pCore 2 (I.map H.subtype)).index := by
    rw [Subgroup.relIndex, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf]
  have h2 : (CFSG.pCore 2 I).map e.toMonoidHom = CFSG.pCore 2 (I.map H.subtype) := by
    rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv]
  rw [h1, ← h2, Subgroup.index_map_of_bijective e.bijective]
  rfl

section Pair

variable {G : Type} [Group G] {H : Subgroup G}

theorem pair_of_qrc [Finite G] {T M V : Subgroup G} (hTH : T ≤ H) (hMH : M ≤ H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hVel : IsElemAbelian 2 V) {g : H}
    {I : Subgroup H} (hI : I = V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) (hgI : g ∈ I)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf H ⊓ I) I)
    (hNV : Subgroup.normalizer (V.subgroupOf H : Set H) ⊓ I ≤ M.subgroupOf H)
    (hVM : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2) (M.subgroupOf H ⊓ I))
    (hJ : (⨅ i ∈ I, CFSG.conjugate (M.subgroupOf H ⊓ I) i) = inSubgroup (CFSG.pCore 2) I) :
    I.map H.subtype = Ch3n.pairI V (g : G)⁻¹ ∧
      E2.Pair (Ch3n.pairI V (g : G)⁻¹) (T ⊓ Ch3n.pairI V (g : G)⁻¹)
        (M ⊓ Ch3n.pairI V (g : G)⁻¹) V (g : G)⁻¹ ∧
      kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹) =
        pCoreOf 2 (Ch3n.pairI V (g : G)⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := hVT.trans hTH
  set X := Ch3n.pairI V (g : G)⁻¹ with hX
  have hIX : I.map H.subtype = X := by
    rw [hI, Subgroup.map_sup, map_subtype_conjugate, Subgroup.map_subgroupOf_eq_of_le hVH]
    rfl
  have hMI : (M.subgroupOf H ⊓ I).map H.subtype = M ⊓ X := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hMH, hIX]
  have hTI : (T.subgroupOf H ⊓ I).map H.subtype = T ⊓ X := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTH, hIX]
  have hker : kerIn (M ⊓ X) X = pCoreOf 2 X := by
    rw [← hMI, ← hIX, ← map_subtype_iInf_conjugate, hJ, map_subtype_inSubgroup_pCore]
  have hK2 : IsPGroup 2 (kerIn (M ⊓ X) X) := hker ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hKK : pCoreOf 2 (kerIn (M ⊓ X) X) = kerIn (M ⊓ X) X :=
    le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hK2)
  have hs := isSylowTwoOf_map_subtype hsyl
  rw [hTI, hIX] at hs
  refine ⟨hIX, ⟨hs, le_inf hVT le_sup_left,
    inf_le_left.trans hTV, hVel, ?_, inf_le_right, ?_, ?_, ?_, rfl⟩, hker⟩
  · rintro x ⟨hxX, hxN⟩
    rw [← hIX] at hxX
    obtain ⟨y, hyI, rfl⟩ := hxX
    have hyN : y ∈ Subgroup.normalizer (V.subgroupOf H : Set H) := by
      have h1 : (y : G) ∈ H ⊓ Subgroup.normalizer (V : Set G) := ⟨y.2, hxN⟩
      rw [← CFSG.QuasithinUnique.map_subtype_normalizer hVH] at h1
      obtain ⟨y', hy', hyy'⟩ := h1
      rwa [← H.subtype_injective hyy']
    exact ⟨hNV ⟨hyN, hyI⟩, by rw [← hIX]; exact ⟨y, hyI, rfl⟩⟩
  · rw [← hMI, ← map_subtype_inSubgroup_pCore, ← Subgroup.map_subgroupOf_eq_of_le hVH]
    exact Subgroup.map_mono hVM
  · rw [hKK]
    refine ⟨le_rfl, hK2, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  · rw [← hIX]
    exact Subgroup.inv_mem _ ⟨g, hgI, rfl⟩

theorem pair_of_qrc_kerIn [Finite G] {T M V : Subgroup G} (hTH : T ≤ H) (hMH : M ≤ H)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hVel : IsElemAbelian 2 V) {g : H}
    {I : Subgroup H} (hI : I = V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) (hgI : g ∈ I)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf H ⊓ I) I)
    (hNV : Subgroup.normalizer (V.subgroupOf H : Set H) ⊓ I ≤ M.subgroupOf H)
    (hVM : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2) (M.subgroupOf H ⊓ I))
    (hJ : kerIn (M.subgroupOf H ⊓ I) I = inSubgroup (CFSG.pCore 2) I) :
    I.map H.subtype = Ch3n.pairI V (g : G)⁻¹ ∧
      E2.Pair (Ch3n.pairI V (g : G)⁻¹) (T ⊓ Ch3n.pairI V (g : G)⁻¹)
        (M ⊓ Ch3n.pairI V (g : G)⁻¹) V (g : G)⁻¹ ∧
      kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹) =
        pCoreOf 2 (Ch3n.pairI V (g : G)⁻¹) :=
  pair_of_qrc hTH hMH hVT hTV hVel hI hgI hsyl hNV hVM (by rw [iInf_conjugate_eq_kerIn, hJ])

theorem charTwo_ne_of_qrc {V : Subgroup G} (hVH : V ≤ H) {I : Subgroup H}
    (hchar : CFSG.IsCharacteristicP 2 I) (hVI : V.subgroupOf H < I) :
    CharTwo (I.map H.subtype) ∧ I.map H.subtype ≠ V := by
  refine ⟨charTwo_map_subtype_of_isCharacteristicP hchar, fun h => hVI.ne ?_⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [h, Subgroup.map_subgroupOf_eq_of_le hVH]

theorem map_subtype_pCore : (CFSG.pCore 2 H).map H.subtype = pCoreOf 2 H := by
  rw [pCoreOf]

theorem relIndex_subgroupOf_inf_pCore {V : Subgroup G} (hVH : V ≤ H) :
    (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) =
      (V ⊓ pCoreOf 2 H).relIndex V := by
  rw [← Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective,
    Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hVH,
    map_subtype_pCore]

theorem qrcHyp_of_hyp28 [Finite G] {T M V : Subgroup G} (hyp : E2.Hyp28 H T M V)
    (hchar : CharTwo H) :
    ∃ T' : Sylow 2 H, (T' : Subgroup H) = T.subgroupOf H ∧ CFSG.IsCharacteristicP 2 H ∧
      ¬ (T' : Subgroup H).Normal ∧ (T' : Subgroup H) ≤ M.subgroupOf H ∧ M.subgroupOf H < ⊤ ∧
      (∀ Y : Subgroup H, (T' : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H) ∧
      IsElementaryAbelian 2 (V.subgroupOf H) ∧ V.subgroupOf H ≤ T' ∧
      (T' : Subgroup H) ≤ Subgroup.normalizer (V.subgroupOf H : Set H) ∧
      V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2) (M.subgroupOf H) ∧
      kerIn (M.subgroupOf H) ⊤ = (kerIn M H).subgroupOf H := by
  have hmp := hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hyp.le_H
  obtain ⟨T', hT'⟩ := exists_sylow_subgroupOf hmp.isSylow
  refine ⟨T', hT', isCharacteristicP_of_charTwo hchar, fun hn => hmp.not_normal ?_,
    hT' ▸ Subgroup.comap_mono hmp.le, ?_, fun Y hTY hY => ?_,
    isElementaryAbelian_subgroupOf hyp.elem, hT' ▸ Subgroup.comap_mono hyp.le_T, ?_,
    fun v hv => ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ (h : H) (z : G), z ∈ T → (h : G) * z * (h : G)⁻¹ ∈ T := fun h z hz => by
      have h1 : (⟨z, hTH hz⟩ : H) ∈ (T' : Subgroup H) := by rw [hT']; exact hz
      have h2 := hn.conj_mem _ h1 h
      rw [hT'] at h2
      exact h2
    refine ⟨key ⟨x, hx⟩ y, fun hy => ?_⟩
    have := key ⟨x, hx⟩⁻¹ _ hy
    simpa [mul_assoc] using this
  · refine lt_of_le_of_ne le_top fun htop => hmp.maximal.1.not_ge fun x hx => ?_
    have : (⟨x, hx⟩ : H) ∈ M.subgroupOf H := htop ▸ Subgroup.mem_top _
    exact this
  · have h1 : Y.map H.subtype ≤ M := by
      refine hmp.le_of_lt ?_ ?_
      · intro t ht
        exact ⟨⟨t, hTH ht⟩, hTY (by rw [hT']; exact ht), rfl⟩
      · refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun heq => hY.ne ?_
        apply Subgroup.map_injective H.subtype_injective
        rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    intro y hy
    exact h1 ⟨y, hy, rfl⟩
  · rw [hT']
    intro t ht
    have h1 : (t : G) ∈ H ⊓ Subgroup.normalizer (V : Set G) := ⟨t.2, hyp.normal_T ht⟩
    rw [← CFSG.QuasithinUnique.map_subtype_normalizer hVH] at h1
    obtain ⟨t', ht', htt'⟩ := h1
    rwa [← H.subtype_injective htt']
  · have h1 : (v : G) ∈ pCoreOf 2 M := hyp.le_pCoreOf hv
    rw [← Subgroup.map_subgroupOf_eq_of_le hMH, ← map_subtype_inSubgroup_pCore] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    rwa [← H.subtype_injective hwv]
  · apply Subgroup.map_injective H.subtype_injective
    rw [map_subtype_kerIn, Subgroup.map_subgroupOf_eq_of_le hMH, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le (kerIn_le.trans hMH)]

end Pair

end CFSG.Quasithin.Ch3E213M
