module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionG2General
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.AGLEmbedding.KFactProofs.G2Q

private structure k1566l6b_sd3Internal {H : Type*} [Group H]
    (Q T V : Subgroup H) (y : H) (e1 e2 : ℕ) : Prop where
  T_le : T ≤ Q
  normal : (T.subgroupOf Q).Normal
  comm : IsMulCommutative ↥T
  V_le : V ≤ T
  elemAbelian : IsElemAbelian 3 V
  omegaOne : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V
  eq_sup : Q = T ⊔ Subgroup.zpowers y
  transvection : ∀ v ∈ V, (y * v * y⁻¹ * v⁻¹) ∈ V ∧
    y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹
  nontrivial : ∃ v ∈ V, y * v * y⁻¹ ≠ v
  moves : ∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v
  cardV : Nat.card V = 9
  orderY : orderOf y = 3
  iso : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)

private theorem k1566l6b_tzPart_mono
    {L : Type} [Field L] {m n : ℕ} (h : n ∣ m) :
    tzPart n ≤ tzPart (L := L) m := by
  rintro x ⟨s, t, hs, ht, rfl⟩
  exact ⟨s, t, by obtain ⟨c, hc⟩ := h; rw [hc, pow_mul, hs, one_pow],
    by obtain ⟨c, hc⟩ := h; rw [hc, pow_mul, ht, one_pow], rfl⟩

private theorem k1566l6b_tzPart_mulEquiv
    {L : Type} [Field L] (k : ℕ) (hk : k ≠ 0)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ k) :
    Nonempty (Multiplicative (ZMod k) × Multiplicative (ZMod k) ≃* ↥(tzPart (L := L) k)) := by
  classical
  let e : Multiplicative (ZMod k) × Multiplicative (ZMod k) ≃* ↥(tzPart (L := L) k) := by
    haveI : NeZero k := ⟨hk⟩
    let tzHom : Lˣ × Lˣ →* ModGL .G2 L :=
      { toFun := fun p => tz p.1 p.2
        map_one' := tz_one_one
        map_mul' := fun p q => (tz_mul p.1 p.2 q.1 q.2).symm }
    have hinj : Function.Injective tzHom := by
      intro p q h
      obtain ⟨h1, h2⟩ := tz_injective h
      exact Prod.ext h1 h2
    have hmap : ((rootsOfUnity k L).prod (rootsOfUnity k L)).map tzHom = tzPart (L := L) k := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
        exact ⟨p.1, p.2, hp1, hp2, rfl⟩
      · rintro ⟨s, t, hs, ht, rfl⟩
        exact ⟨(s, t), Subgroup.mem_prod.mpr ⟨hs, ht⟩, rfl⟩
    let eProd : ↥(((rootsOfUnity k L).prod (rootsOfUnity k L))) ≃* ↥(tzPart (L := L) k) :=
      (Subgroup.equivMapOfInjective _ tzHom hinj).trans (MulEquiv.subgroupCongr hmap)
    let eTz : rootsOfUnity k L × rootsOfUnity k L ≃* ↥(tzPart (L := L) k) :=
      (Subgroup.prodEquiv (rootsOfUnity k L) (rootsOfUnity k L)).symm.trans eProd
    let e1 : Multiplicative (ZMod k) ≃* Subgroup.zpowers ζ :=
      AddEquiv.toMultiplicativeLeft hζ.zmodEquivZPowers
    have e2 : Subgroup.zpowers ζ ≃* rootsOfUnity k L := MulEquiv.subgroupCongr hζ.zpowers_eq
    exact (e1.prodCongr e1).trans ((e2.prodCongr e2).trans eTz)
  exact ⟨e⟩

private theorem k1566l6b_sd3Internal_extSub
    {L : Type} [Field L] (b : ℕ) (hb : 1 ≤ b)
    {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ (3 ^ b)) :
    k1566l6b_sd3Internal
      (extSub (ext3_tzPart (L := L) (m := 3 ^ b) hω1))
      (tzPart (L := L) (3 ^ b)) (tzPart (L := L) 3) (yq : ModGL .G2 L) b b := by
  classical
  let H : Subgroup (ModGL .G2 L) := extSub (ext3_tzPart (L := L) (m := 3 ^ b) hω1)
  let T : Subgroup (ModGL .G2 L) := tzPart (L := L) (3 ^ b)
  let V : Subgroup (ModGL .G2 L) := tzPart (L := L) 3
  change k1566l6b_sd3Internal H T V (yq : ModGL .G2 L) b b
  have hTle : T ≤ H := le_extSub _
  have hTcomm : IsMulCommutative ↥(T) := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    obtain ⟨s, t, hs, ht, ha⟩ := a.2
    obtain ⟨s', t', hs', ht', hb'⟩ := b.2
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    rw [ha, hb', tz_mul, tz_mul, mul_comm s s', mul_comm t t']
  have hyq_inv1 : (yq : ModGL .G2 L)⁻¹ = (yq : ModGL .G2 L) ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', show 1 + 2 = 3 by norm_num, yq_pow_three]
  have hyq_inv2 : ((yq : ModGL .G2 L) ^ 2)⁻¹ = (yq : ModGL .G2 L) := by
    rw [← hyq_inv1, inv_inv]
  have hyq_norm : (yq : ModGL .G2 L) ∈ Subgroup.normalizer (T) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    constructor
    · intro hh
      have h1 := (ext3_tzPart (L := L) (m := 3 ^ b) hω1).conj_pow 2 h hh
      rw [hyq_inv2] at h1
      rwa [hyq_inv1]
    · intro hx
      have h1 := yq_conj_mem_tzPart (L := L) (m := 3 ^ b)
        ((yq : ModGL .G2 L)⁻¹ * h * yq) hx
      rwa [show (yq : ModGL .G2 L) * (yq⁻¹ * h * yq) * yq⁻¹ = h by group] at h1
  have hEqSup : H = T ⊔ Subgroup.zpowers (yq : ModGL .G2 L) := by
    apply le_antisymm
    · rw [show H = Subgroup.closure (T ∪ ({yq} : Set (ModGL .G2 L))) from
        extSub_eq_closure (ext3_tzPart (L := L) (m := 3 ^ b) hω1)]
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | hx)
      · exact Subgroup.mem_sup_left hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (yq : ModGL .G2 L))
    · exact sup_le (le_extSub _) (Subgroup.zpowers_le.mpr (y_mem_extSub _))
  have hnorm : ((T).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTle]
    rw [hEqSup]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hyq_norm)
  have hVle : V ≤ T :=
    k1566l6b_tzPart_mono (L := L) (dvd_pow_self 3 (by omega : b ≠ 0))
  have helemAb : IsElemAbelian 3 (V) := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm (fun a b => ?_)
      obtain ⟨s, t, hs, ht, ha⟩ := a.2
      obtain ⟨s', t', hs', ht', hb'⟩ := b.2
      apply Subtype.ext
      change a.val * b.val = b.val * a.val
      rw [ha, hb', tz_mul, tz_mul, mul_comm s s', mul_comm t t']
    · intro x hx
      obtain ⟨s, t, hs, ht, hx'⟩ := hx
      rw [hx', tz_pow, hs, ht, tz_one_one]
  have homegaOne : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V := by
    intro x hx hx3
    obtain ⟨s, t, hs, ht, hx'⟩ := hx
    rw [hx', tz_pow] at hx3
    obtain ⟨hs3, ht3⟩ := tz_injective (hx3.trans tz_one_one.symm)
    exact ⟨s, t, hs3, ht3, hx'⟩
  have htransvection : ∀ v ∈ V,
      ((yq : ModGL .G2 L) * v * yq⁻¹ * v⁻¹) ∈ V ∧
        (yq : ModGL .G2 L) * ((yq) * v * yq⁻¹ * v⁻¹) * yq⁻¹ =
          (yq) * v * yq⁻¹ * v⁻¹ := by
    intro v hv
    obtain ⟨s, u, hs, hu, rfl⟩ := hv
    have hu2 : ((u : Lˣ) ^ 2)⁻¹ = u := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 by norm_num, hu]
    have hs2 : ((s : Lˣ) ^ 2)⁻¹ = s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 by norm_num, hs]
    have hmem : (yq : ModGL .G2 L) * tz s u * yq⁻¹ * (tz s u)⁻¹ = tz 1 s := by
      rw [yq_tz, tz_inv, tz_mul]
      congr 1
      · rw [hu, inv_one, mul_one, mul_inv_cancel]
      · rw [hu2]; group
    constructor
    · rw [hmem]
      exact tz_mem_tzPart (m := 3) (by simp) hs
    · rw [hmem, yq_tz, hs, inv_one, mul_one, hs2, one_mul]
  have hnontrivial : ∃ v ∈ V, (yq : ModGL .G2 L) * v * yq⁻¹ ≠ v := by
    refine ⟨tz ω 1, tz_mem_tzPart (m := 3) hω3 (by simp), ?_⟩
    intro h
    rw [yq_tz] at h
    simp only [one_pow, inv_one, mul_one] at h
    exact hω1 (tz_injective h).2
  have hω3b : (ω : Lˣ) ^ (3 ^ b) = 1 := by
    obtain ⟨c, hc⟩ := dvd_pow_self 3 (by omega : b ≠ 0)
    rw [hc, pow_mul, hω3, one_pow]
  have hmoves : ∀ g ∈ H, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v := by
    intro g hgH hgT
    obtain ⟨t, ht, k, hk, rfl⟩ :=
      (mem_extSub_iff_lt (ext3_tzPart (L := L) (m := 3 ^ b) hω1)).1 hgH
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hgT (by simpa using ht)
    obtain ⟨s, u, hs, hu, rfl⟩ := ht
    have hwT : (yq : ModGL .G2 L) ^ k * tz ω 1 * ((yq) ^ k)⁻¹ ∈ T :=
      (ext3_tzPart (L := L) (m := 3 ^ b) hω1).conj_pow k _
        (tz_mem_tzPart (m := 3 ^ b) hω3b (by simp))
    have hcommt : (tz s u : ModGL .G2 L) * ((yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹) =
        ((yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹) * tz s u := by
      have h := hTcomm.is_comm.comm ⟨tz s u, tz_mem_tzPart (m := 3 ^ b) hs hu⟩
        ⟨(yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹, hwT⟩
      exact congrArg Subtype.val h
    refine ⟨tz ω 1, tz_mem_tzPart (m := 3) hω3 (by simp), ?_⟩
    intro hconj
    have h1 : (tz s u : ModGL .G2 L) * ((yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹) * (tz s u)⁻¹ =
        (yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹ := by
      rw [hcommt]; group
    have h2 : (tz s u : ModGL .G2 L) * ((yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹) * (tz s u)⁻¹ =
        tz ω 1 := by
      have hh := hconj
      rw [show (tz s u * (yq : ModGL .G2 L) ^ k) * tz ω 1 * (tz s u * (yq) ^ k)⁻¹ =
          (tz s u) * ((yq) ^ k * tz ω 1 * ((yq) ^ k)⁻¹) * (tz s u)⁻¹ by group] at hh
      exact hh
    exact yq_pow_conj_tz_one_ne hω1 hk0 hk (h1.symm.trans h2)
  have hω_prim_u : IsPrimitiveRoot ω 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω3 hω1)
  have hω_prim : IsPrimitiveRoot (ω : L) 3 := IsPrimitiveRoot.coe_units_iff.mpr hω_prim_u
  have hcardV : Nat.card (V) = 9 := by
    simpa using card_tzPart (L := L) 3 (by norm_num) hω_prim
  have hyq_ne_one : (yq : ModGL .G2 L) ≠ 1 := by
    intro h
    exact yq_not_mem_tzPart (L := L) (m := 3 ^ b) hω1 (h ▸ (T).one_mem)
  have horderY : orderOf (yq : ModGL .G2 L) = 3 :=
    orderOf_eq_prime yq_pow_three hyq_ne_one
  have hiso : Nonempty
      ((Multiplicative (ZMod (3 ^ b)) × Multiplicative (ZMod (3 ^ b))) ≃* ↥(T)) :=
    k1566l6b_tzPart_mulEquiv (L := L) (3 ^ b) (pow_ne_zero b (by norm_num)) hζ
  exact ⟨hTle, hnorm, hTcomm, hVle, helemAb, homegaOne, hEqSup, htransvection, hnontrivial,
    hmoves, hcardV, horderY, hiso⟩

private theorem k1566l6a2_sd3_of_internal
    {G H : Type*} [Group G] [Finite G] [Group H]
    (Φ : G →* H) (hΦ : Function.Injective Φ)
    {Q : Subgroup G} (hQsyl : ∃ P : Sylow 3 G, (P : Subgroup G) = Q)
    {Q' : Subgroup H} (hQmap : Q.map Φ = Q')
    {T' V' : Subgroup H} {y' : H} {e1 e2 : ℕ}
    (hInt : k1566l6b_sd3Internal Q' T' V' y' e1 e2) :
    ∃ (T V : Subgroup G) (y : G),
      T = T'.comap Φ ∧ Φ y = y' ∧ SD3 G Q T V y e1 e2 := by
  classical
  let T : Subgroup G := T'.comap Φ
  let V : Subgroup G := V'.comap Φ
  have hy'Q' : y' ∈ Q' := by
    rw [hInt.eq_sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y')
  have hy'map : y' ∈ Q.map Φ := by rw [hQmap]; exact hy'Q'
  obtain ⟨y, hyQ, hyy'⟩ := Subgroup.mem_map.mp hy'map
  obtain ⟨P, hP⟩ := hQsyl
  have hQp : IsPGroup 3 Q := by rw [← hP]; exact P.isPGroup'
  have hind : ¬ 3 ∣ Q.index := by rw [← hP]; exact P.not_dvd_index
  have hTQ : T ≤ Q := by
    intro x hx
    have hx' : Φ x ∈ Q' := hInt.T_le hx
    rw [← hQmap] at hx'
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx'
    rwa [hΦ hqx] at hq
  have hT'range : T' ≤ Φ.range := by
    intro x hx
    have hxQ' : x ∈ Q' := hInt.T_le hx
    rw [← hQmap] at hxQ'
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.mp hxQ'
    exact ⟨q, hq⟩
  have hV'range : V' ≤ Φ.range := by
    intro x hx
    have hxQ' : x ∈ Q' := hInt.T_le (hInt.V_le hx)
    rw [← hQmap] at hxQ'
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.mp hxQ'
    exact ⟨q, hq⟩
  have hmapT : T.map Φ = T' := by
    show (T'.comap Φ).map Φ = T'
    exact Subgroup.map_comap_eq_self hT'range
  have hmapV : V.map Φ = V' := by
    show (V'.comap Φ).map Φ = V'
    exact Subgroup.map_comap_eq_self hV'range
  have hnormal : (T.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTQ]
    intro x hxQ
    rw [Subgroup.mem_normalizer_iff]
    have hx' : Φ x ∈ Subgroup.normalizer T' := by
      have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hInt.T_le).mp hInt.normal
      exact hle (by rw [← hQmap]; exact Subgroup.mem_map_of_mem Φ hxQ)
    rw [Subgroup.mem_normalizer_iff] at hx'
    intro z
    have hz : z ∈ T ↔ Φ z ∈ T' := Subgroup.mem_comap
    have hz' : x * z * x⁻¹ ∈ T ↔ Φ (x * z * x⁻¹) ∈ T' := Subgroup.mem_comap
    rw [hz, hz', map_mul, map_mul, map_inv]
    exact hx' (Φ z)
  have hcomm : IsMulCommutative ↥T := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    apply Subtype.ext
    apply hΦ
    change Φ ((a : G) * (b : G)) = Φ ((b : G) * (a : G))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hInt.comm.is_comm.comm ⟨Φ a, a.2⟩ ⟨Φ b, b.2⟩)
  have hVle : V ≤ T := Subgroup.comap_mono hInt.V_le
  have helemAb : IsElemAbelian 3 V := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm (fun a b => ?_)
      apply Subtype.ext
      apply hΦ
      change Φ ((a : G) * (b : G)) = Φ ((b : G) * (a : G))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hInt.elemAbelian.1.is_comm.comm ⟨Φ a, a.2⟩ ⟨Φ b, b.2⟩)
    · intro x hx
      apply hΦ
      rw [map_pow, map_one]
      exact hInt.elemAbelian.2 (Φ x) hx
  have homegaOne : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V := by
    intro t ht ht3
    exact hInt.omegaOne (Φ t) ht (by rw [← map_pow, ht3, map_one])
  have heqSup : Q = T ⊔ Subgroup.zpowers y := by
    apply Subgroup.map_injective hΦ
    rw [hQmap, Subgroup.map_sup, hmapT, MonoidHom.map_zpowers, hyy', ← hInt.eq_sup]
  have htransvection : ∀ v ∈ V,
      ((y * v * y⁻¹ * v⁻¹) ∈ V ∧ y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹) := by
    intro v hv
    have hv' : Φ v ∈ V' := hv
    obtain ⟨h1, h2⟩ := hInt.transvection (Φ v) hv'
    have hPhiComm : Φ (y * v * y⁻¹ * v⁻¹) = y' * Φ v * y'⁻¹ * (Φ v)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyy']
    constructor
    · show Φ (y * v * y⁻¹ * v⁻¹) ∈ V'
      rw [hPhiComm]; exact h1
    · apply hΦ
      show Φ (y * (y * v * y⁻¹ * v⁻¹) * y⁻¹) = Φ (y * v * y⁻¹ * v⁻¹)
      rw [map_mul, map_mul, map_inv, hyy', hPhiComm]
      exact h2
  have hnontrivial : ∃ v ∈ V, y * v * y⁻¹ ≠ v := by
    obtain ⟨v', hv'V, hv'ne⟩ := hInt.nontrivial
    have hv'Q' : v' ∈ Q' := hInt.T_le (hInt.V_le hv'V)
    obtain ⟨v, -, hvv'⟩ := Subgroup.mem_map.mp (by rw [hQmap]; exact hv'Q')
    refine ⟨v, ?_, ?_⟩
    · show Φ v ∈ V'; rw [hvv']; exact hv'V
    · intro hconj
      apply hv'ne
      have hh : Φ (y * v * y⁻¹) = Φ v := by rw [hconj]
      rw [map_mul, map_mul, map_inv, hyy', hvv'] at hh
      exact hh
  have hmoves : ∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v := by
    intro g hgQ hgT
    have hgQ' : Φ g ∈ Q' := by rw [← hQmap]; exact Subgroup.mem_map_of_mem Φ hgQ
    have hgT' : Φ g ∉ T' := fun h => hgT h
    obtain ⟨v', hv'V, hv'ne⟩ := hInt.moves (Φ g) hgQ' hgT'
    have hv'Q' : v' ∈ Q' := hInt.T_le (hInt.V_le hv'V)
    obtain ⟨v, -, hvv'⟩ := Subgroup.mem_map.mp (by rw [hQmap]; exact hv'Q')
    refine ⟨v, ?_, ?_⟩
    · show Φ v ∈ V'; rw [hvv']; exact hv'V
    · intro hconj
      apply hv'ne
      have hh : Φ (g * v * g⁻¹) = Φ v := by rw [hconj]
      rw [map_mul, map_mul, map_inv, hvv'] at hh
      exact hh
  have hcardV : Nat.card V = 9 := by
    rw [← Subgroup.card_map_of_injective (K := V) (f := Φ) hΦ, hmapV, hInt.cardV]
  have horderY : orderOf y = 3 := by
    rw [← orderOf_injective Φ hΦ y, hyy', hInt.orderY]
  have hiso : Nonempty
      ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T) := by
    let e : ↥T ≃* ↥T' :=
      (Subgroup.equivMapOfInjective T Φ hΦ).trans (MulEquiv.subgroupCongr hmapT)
    obtain ⟨e'⟩ := hInt.iso
    exact ⟨e'.trans e.symm⟩
  exact ⟨T, V, y, rfl, hyy', hQp, hind, hTQ, hnormal, hcomm, hVle, helemAb, homegaOne, heqSup,
    htransvection, hnontrivial, hmoves, hcardV, horderY, hiso⟩

private lemma k1566l6a2_tz_zpow
    {L : Type} [Field L] (s t : Lˣ) (k : ℤ) :
    (tz s t : ModGL .G2 L) ^ k = tz (s ^ k) (t ^ k) := by
  let tzHom : Lˣ × Lˣ →* ModGL .G2 L :=
    { toFun := fun p => tz p.1 p.2
      map_one' := tz_one_one
      map_mul' := fun p q => (tz_mul p.1 p.2 q.1 q.2).symm }
  calc (tz s t : ModGL .G2 L) ^ k = (tzHom (s, t)) ^ k := rfl
    _ = tzHom ((s, t) ^ k) := (map_zpow tzHom (s, t) k).symm
    _ = tzHom (s ^ k, t ^ k) := by rfl
    _ = tz (s ^ k) (t ^ k) := rfl

private theorem k1566l6a2_actor_compat
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : L →+* L) (σ : K →+* K) (hcomp : ∀ c : K, F (algebraMap K L c) = algebraMap K L (σ c))
    (A : ModGL .G2 K) :
    baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ) A) =
      Units.map (entrywiseHom F) (baseChangeGL (algebraMap K L) A) := by
  have hcomp' : F.comp (algebraMap K L) = (algebraMap K L).comp σ := by
    ext c; exact hcomp c
  rw [units_map_entrywiseHom_eq_baseChangeGL σ A,
    units_map_entrywiseHom_eq_baseChangeGL F (baseChangeGL (algebraMap K L) A),
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hcomp']

private theorem k1566l6a_three_le_pow {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (h3f : 3 ∣ f)
    (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have _ := hp3
  have hf3 : 3 ≤ f := by
    obtain ⟨k, hk⟩ := h3f
    omega
  have hp2 : 2 ≤ p := hp.two_le
  calc 3 ≤ 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    _ ≤ p ^ f := Nat.pow_le_pow_left hp2 f

private theorem k1566l6a_v3_natAbs_eq {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (h3f : 3 ∣ f) (hf : 1 ≤ f)
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hmod : (p : ZMod 3) ^ (f / 3) = (eps : ZMod 3)) :
    padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) =
      padicValNat 3 ((p ^ f) ^ 2 - 1) := by
  have hq3 : 3 ≤ p ^ f := k1566l6a_three_le_pow hp hp3 h3f hf
  obtain ⟨k, hk⟩ := h3f
  have hfk : f / 3 = k := by omega
  have hcube : p ^ f = (p ^ (f / 3)) ^ 3 := by
    rw [hfk, hk, show 3 * k = k * 3 by ring, pow_mul]
  have hcast : ((p ^ (f / 3) : ℕ) : ZMod 3) = (eps : ZMod 3) := by
    rw [Nat.cast_pow]; exact hmod
  have hqmod : (p ^ f) % 3 = (eps : ZMod 3).val := by
    have hpf : ((p ^ f : ℕ) : ZMod 3) = (eps : ZMod 3) := by
      rw [hcube, Nat.cast_pow, hcast]
      rcases heps with rfl | rfl <;> decide
    rw [← ZMod.val_natCast 3 (p ^ f), hpf]
  rcases heps with rfl | rfl
  ·
    have hq1 : (p ^ f) % 3 = 1 := by
      have h1 : ((1 : ℤ) : ZMod 3).val = 1 := by decide
      rw [hqmod, h1]
    have hv := padicValNat_three_sq_sub_one_of_mod_one (q := p ^ f) hq3 hq1
    have hnat : Int.natAbs ((p : ℤ) ^ f - 1) = p ^ f - 1 := by
      have hcast' : ((p ^ f - 1 : ℕ) : ℤ) = (p : ℤ) ^ f - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p ^ f), Nat.cast_pow, Nat.cast_one]
      rw [← hcast', Int.natAbs_natCast]
    rw [hnat, hv]
  ·
    have hq2 : (p ^ f) % 3 = 2 := by
      have h2 : ((-1 : ℤ) : ZMod 3).val = 2 := by decide
      rw [hqmod, h2]
    have hv := padicValNat_three_sq_sub_one_of_mod_two (q := p ^ f) hq3 hq2
    have hnat : Int.natAbs ((p : ℤ) ^ f - -1) = p ^ f + 1 := by
      have hcast' : ((p ^ f + 1 : ℕ) : ℤ) = (p : ℤ) ^ f + 1 := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [show (p : ℤ) ^ f - -1 = (p : ℤ) ^ f + 1 by ring, ← hcast', Int.natAbs_natCast]
    rw [hnat, hv]

private theorem k1566l6a_q_mod {p f : ℕ} (h3f : 3 ∣ f) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hmod : (p : ZMod 3) ^ (f / 3) = (eps : ZMod 3)) :
    (p ^ f) % 3 = (eps : ZMod 3).val := by
  have hcast : ((p ^ (f / 3) : ℕ) : ZMod 3) = (eps : ZMod 3) := by
    rw [Nat.cast_pow]; exact hmod
  have hcube : p ^ f = (p ^ (f / 3)) ^ 3 := by
    nth_rewrite 1 [← Nat.div_mul_cancel h3f]
    rw [pow_mul]
  have hpf : ((p ^ f : ℕ) : ZMod 3) = (eps : ZMod 3) := by
    rw [hcube, Nat.cast_pow, hcast]
    rcases heps with rfl | rfl <;> decide
  rw [← ZMod.val_natCast 3 (p ^ f), hpf]

private lemma k1566l6a_zpow_nat_pow {G : Type*} [Group G] (s : G) (k : ℤ) (n : ℕ) :
    (s ^ k) ^ n = (s ^ n) ^ k := by
  conv_rhs => rw [← zpow_natCast (n := n), ← zpow_mul s (↑n) k]
  rw [← zpow_natCast (n := n), ← zpow_mul s k (↑n)]
  congr 1
  ring

private theorem k1566l6a_main
    (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (h3f : 3 ∣ f)
    (hcard : Nat.card K = p ^ f)
    (eps : ℤ) (heps : eps = 1 ∨ eps = -1)
    (hmod : (p : ZMod 3) ^ (f / 3) = (eps : ZMod 3))
    (σ₀ : K ≃+* K) (hσ₀ : ∀ c : K, σ₀ c = c ^ (p ^ (f / 3)))
    (φ : MulAut (adjointGroup .G2 K))
    (hφ : ∀ h : adjointGroup .G2 K, (φ h : ModGL .G2 K) =
      Units.map (entrywiseHom σ₀.toRingHom) (h : ModGL .G2 K)) :
    ∃ (Q T V : Subgroup (adjointGroup .G2 K)) (y : adjointGroup .G2 K),
      SD3 (adjointGroup .G2 K) Q T V y
          (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)))
          (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∧
      ScalarAction T φ y (eps * (p : ℤ) ^ (f / 3)) := by
  classical
  let q := Nat.card K
  let q0 := p ^ (f / 3)
  let a := padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))
  let b := padicValNat 3 (q ^ 2 - 1)
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hcard
    have h2 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  have hq : q = p ^ f := hcard
  have ha_eq_b : a = b := by
    dsimp only [a, b]
    rw [hq]
    exact k1566l6a_v3_natAbs_eq hp hp3 h3f hf1 heps hmod
  have hq3 : 3 ≤ q := by
    rw [hq]; exact k1566l6a_three_le_pow hp hp3 h3f hf1
  have h3q : ¬ 3 ∣ q := by
    intro h
    have hdiv : 3 ∣ p ^ f := by rw [← hq]; exact h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow hdiv)).symm
  have hb1 : 1 ≤ b := one_le_padicValNat_three_sq_sub_one h3q (by omega)
  have hb0 : 3 ^ b ≠ 0 := pow_ne_zero b (by norm_num)
  have hbpos : 0 < b := by omega
  have h3b1 : 1 < 3 ^ b := one_lt_pow' (by norm_num) (by omega)
  have h3bdvd : 3 ∣ 3 ^ b := by
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b = 3 * c := by
      refine ⟨3 ^ (b - 1), ?_⟩
      have hb : b = (b - 1) + 1 := by omega
      calc 3 ^ b = 3 ^ ((b - 1) + 1) := congrArg (fun n => 3 ^ n) hb
        _ = 3 ^ (b - 1) * 3 := pow_succ _ _
        _ = 3 * 3 ^ (b - 1) := by ring
    exact ⟨c, hc⟩
  have hqmod : q % 3 = (eps : ZMod 3).val := by
    rw [hq]; exact k1566l6a_q_mod h3f heps hmod
  have hFin : Fintype K := Fintype.ofFinite K
  have hFact : Fact p.Prime := ⟨hp⟩
  have hCharK : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  let L := AlgebraicClosure K
  have hCharL : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hAlgCl : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have hdiv : p ∣ 3 := (CharP.cast_eq_zero_iff L p 3).1 h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdiv)
  have hNe3 : NeZero ((3 : ℕ) : L) := ⟨h3L⟩
  have hNe3b : NeZero ((3 ^ b : ℕ) : L) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero b h3L⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3 ^ b)
  let ζu : Lˣ := (hζ.isUnit hb0).unit
  have hζu : IsPrimitiveRoot (ζu : L) (3 ^ b) := by simpa [ζu] using hζ
  have hζu_units : IsPrimitiveRoot ζu (3 ^ b) := by
    have := hζ.isUnit_unit hb0
    simpa [ζu] using this
  have hζu_ne1 : ζu ≠ 1 := fun h => hζu.ne_one h3b1 (congrArg Units.val h)
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  let ωu : Lˣ := (hω.isUnit (by norm_num)).unit
  have hωu : IsPrimitiveRoot (ωu : L) 3 := by simpa [ωu] using hω
  have hωu3 : ωu ^ 3 = 1 := Units.ext (by simpa [ωu] using hω.pow_eq_one)
  have hωu1 : ωu ≠ 1 := fun h => hωu.ne_one (by norm_num) (congrArg Units.val h)
  let F0 : L →+* L := iterateFrobenius L p (f / 3)
  have hF0 : ∀ c : L, F0 c = c ^ q0 := by intro c; rw [iterateFrobenius_def]
  have he : 1 ≤ f / 3 := by omega
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity p L (f / 3) he).1 .G2
  let n : adjointGroup .G2 L := if eps = 1 then 1 else ⟨nw0, nw0_mem_adjointGroup⟩
  obtain ⟨g, hg_eq⟩ := hLang n
  have hSg : S g = g * n := by rw [hg_eq]; group
  have hF0g : Units.map (entrywiseHom F0) (g : ModGL .G2 L) =
      (g : ModGL .G2 L) * (n : ModGL .G2 L) := by rw [← hS g, hSg]; rfl
  let k : ℤ := eps * (q0 : ℤ)
  have hn_tz : ∀ s t : Lˣ, (n : ModGL .G2 L) * tz (s ^ q0) (t ^ q0) * (n : ModGL .G2 L)⁻¹
      = tz (s ^ k) (t ^ k) := by
    intro s t
    rcases heps with rfl | rfl
    · have hn : n = 1 := by simp [n]
      have hk : k = (q0 : ℤ) := by simp [k]
      rw [hn, hk]
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
      congr 1
    · have hn : (n : ModGL .G2 L) = nw0 := by simp [n]
      have hk : k = -(q0 : ℤ) := by simp [k]
      rw [hn, hk, nw0_tz]
      congr 1 <;> rw [zpow_neg, zpow_natCast]
  have hn_yq : (n : ModGL .G2 L) * yq * (n : ModGL .G2 L)⁻¹ = yq := by
    rcases heps with rfl | rfl
    · have hn : n = 1 := by simp [n]
      rw [hn]; simp
    · have hn : (n : ModGL .G2 L) = nw0 := by simp [n]
      rw [hn, nw0_comm_yq]; group
  let dg : Lˣ → Lˣ → ModGL .G2 L := fun s t => (g : ModGL .G2 L) * tz s t * (g : ModGL .G2 L)⁻¹
  let yg : ModGL .G2 L := (g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹
  have hF0_dg : ∀ s t : Lˣ, Units.map (entrywiseHom F0) (dg s t) = dg (s ^ k) (t ^ k) := by
    intro s t
    have hs : Units.map (F0 : L →* L) s = s ^ q0 := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]; simp [hF0])
    have ht : Units.map (F0 : L →* L) t = t ^ q0 := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]; simp [hF0])
    calc Units.map (entrywiseHom F0) (dg s t)
        = Units.map (entrywiseHom F0) (g : ModGL .G2 L) * Units.map (entrywiseHom F0) (tz s t)
            * (Units.map (entrywiseHom F0) (g : ModGL .G2 L))⁻¹ := by
          simp only [dg, map_mul, map_inv]
      _ = ((g : ModGL .G2 L) * (n : ModGL .G2 L)) * tz (s ^ q0) (t ^ q0)
            * ((g : ModGL .G2 L) * (n : ModGL .G2 L))⁻¹ := by rw [hF0g, frob_tz, hs, ht]
      _ = (g : ModGL .G2 L) * ((n : ModGL .G2 L) * tz (s ^ q0) (t ^ q0) * (n : ModGL .G2 L)⁻¹)
            * (g : ModGL .G2 L)⁻¹ := by group
      _ = dg (s ^ k) (t ^ k) := by rw [hn_tz]
  have hF0_yg : Units.map (entrywiseHom F0) yg = yg := by
    calc Units.map (entrywiseHom F0) yg
        = Units.map (entrywiseHom F0) (g : ModGL .G2 L) * Units.map (entrywiseHom F0) yq
            * (Units.map (entrywiseHom F0) (g : ModGL .G2 L))⁻¹ := by
          simp only [yg, map_mul, map_inv]
      _ = ((g : ModGL .G2 L) * (n : ModGL .G2 L)) * yq
            * ((g : ModGL .G2 L) * (n : ModGL .G2 L))⁻¹ := by rw [hF0g, frob_yq]
      _ = (g : ModGL .G2 L) * ((n : ModGL .G2 L) * yq * (n : ModGL .G2 L)⁻¹)
            * (g : ModGL .G2 L)⁻¹ := by group
      _ = yg := by rw [hn_yq]
  have hq0cube : q0 ^ 3 = Nat.card K := by
    rw [hcard, ← Nat.div_mul_cancel h3f, pow_mul]
  let F3 : L →+* L := F0.comp (F0.comp F0)
  have hF3 : ∀ c : L, F3 c = c ^ Nat.card K := by
    intro c
    have h1 : F0 c = c ^ q0 := hF0 c
    have h2 : F0 (F0 c) = (F0 c) ^ q0 := hF0 _
    have h3 : F0 (F0 (F0 c)) = (F0 (F0 c)) ^ q0 := hF0 _
    show F0 (F0 (F0 c)) = c ^ Nat.card K
    rw [h3, h2, h1, ← pow_mul, ← pow_mul,
      show q0 * (q0 * q0) = q0 ^ 3 by ring, hq0cube]
  have hF3_hom : entrywiseHom (τ := .G2) F3 =
      (entrywiseHom (τ := .G2) F0).comp
        ((entrywiseHom (τ := .G2) F0).comp (entrywiseHom (τ := .G2) F0)) := by
    apply MonoidHom.ext
    intro A
    show entrywise F3 A = entrywise F0 (entrywise F0 (entrywise F0 A))
    dsimp only [F3]
    rw [← entrywise_entrywise F0 (F0.comp F0) A, ← entrywise_entrywise F0 F0 A]
  have hF3_apply : ∀ x : ModGL .G2 L, Units.map (entrywiseHom F3) x =
      Units.map (entrywiseHom F0)
        (Units.map (entrywiseHom F0) (Units.map (entrywiseHom F0) x)) := by
    intro x
    rw [hF3_hom]
    rw [Units.map_comp ((entrywiseHom (τ := .G2) F0).comp (entrywiseHom (τ := .G2) F0))
      (entrywiseHom (τ := .G2) F0)]
    rw [Units.map_comp (entrywiseHom (τ := .G2) F0) (entrywiseHom (τ := .G2) F0)]
    rfl
  have hk3 : k ^ 3 = eps * (q : ℤ) := by
    have hq0z : (q0 : ℤ) ^ 3 = (q : ℤ) := by
      rw [← Nat.cast_pow, hq0cube]
    rcases heps with rfl | rfl
    · rw [show k = (q0 : ℤ) by simp [k], hq0z]; ring
    · rw [show k = -(q0 : ℤ) by simp [k]]
      rw [show (-(q0 : ℤ)) ^ 3 = -((q0 : ℤ) ^ 3) by ring, hq0z]; ring
  have hs_eps : ∀ s : Lˣ, s ^ (3 ^ b) = 1 → s ^ (eps * (q : ℤ)) = s := by
    intro s hs
    rcases heps with rfl | rfl
    · have hq1 : q % 3 = 1 := by
        have h1 : ((1 : ℤ) : ZMod 3).val = 1 := by decide
        rw [hqmod, h1]
      have hdvd : 3 ^ b ∣ q - 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_one (q := q) (by omega) hq1
      obtain ⟨c, hc⟩ := hdvd
      have hsq : s ^ q = s := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hs, one_pow, one_mul, pow_one]
      rw [one_mul, zpow_natCast, hsq]
    · have hq2 : q % 3 = 2 := by
        have h2 : ((-1 : ℤ) : ZMod 3).val = 2 := by decide
        rw [hqmod, h2]
      have hdvd : 3 ^ b ∣ q + 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_two (q := q) (by omega) hq2
      obtain ⟨c, hc⟩ := hdvd
      have hsq : s ^ q = s⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have hsq1 : s ^ (q + 1) = 1 := by rw [hc, pow_mul, hs, one_pow]
        rwa [pow_succ] at hsq1
      rw [show (-1 : ℤ) * (q : ℤ) = -(q : ℤ) by ring, zpow_neg, zpow_natCast, hsq, inv_inv]
  have hF3_dg : ∀ s t : Lˣ, s ^ (3 ^ b) = 1 → t ^ (3 ^ b) = 1 →
      Units.map (entrywiseHom F3) (dg s t) = dg s t := by
    intro s t hs ht
    have hsk : (s ^ k) ^ (3 ^ b) = 1 := by
      rw [k1566l6a_zpow_nat_pow s k (3 ^ b), hs, one_zpow]
    have htk : (t ^ k) ^ (3 ^ b) = 1 := by
      rw [k1566l6a_zpow_nat_pow t k (3 ^ b), ht, one_zpow]
    have hs' : ((s ^ k) ^ k) ^ k = s := by
      rw [← zpow_mul s k k, ← zpow_mul s (k * k) k,
        show k * k * k = k ^ 3 by ring, hk3, hs_eps s hs]
    have ht' : ((t ^ k) ^ k) ^ k = t := by
      rw [← zpow_mul t k k, ← zpow_mul t (k * k) k,
        show k * k * k = k ^ 3 by ring, hk3, hs_eps t ht]
    calc Units.map (entrywiseHom F3) (dg s t)
        = Units.map (entrywiseHom F0)
            (Units.map (entrywiseHom F0) (Units.map (entrywiseHom F0) (dg s t))) := hF3_apply _
      _ = Units.map (entrywiseHom F0) (Units.map (entrywiseHom F0) (dg (s ^ k) (t ^ k))) := by
            rw [hF0_dg]
      _ = Units.map (entrywiseHom F0) (dg ((s ^ k) ^ k) ((t ^ k) ^ k)) := by rw [hF0_dg]
      _ = dg (((s ^ k) ^ k) ^ k) (((t ^ k) ^ k) ^ k) := by rw [hF0_dg]
      _ = dg s t := by rw [hs', ht']
  have hpow3 : ∀ s : Lˣ, s ^ 3 = 1 → s ^ (3 ^ b) = 1 := by
    intro s hs
    obtain ⟨c, hc⟩ := h3bdvd
    rw [hc, pow_mul, hs, one_pow]
  have htzPart_mono : tzPart (L := L) 3 ≤ tzPart (L := L) (3 ^ b) := by
    rintro _ ⟨s, t, hs, ht, rfl⟩
    exact ⟨s, t, hpow3 s hs, hpow3 t ht, rfl⟩
  let TL : Subgroup (ModGL .G2 L) :=
    (tzPart (L := L) (3 ^ b)).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom
  let TL3 : Subgroup (ModGL .G2 L) :=
    (tzPart (L := L) 3).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom
  let yL : ModGL .G2 L := (g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹
  have hTL_adj : TL ≤ adjointGroup .G2 L := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨s, t, -, -, rfl⟩ := hx
    exact mul_mem (mul_mem g.2 (tz_mem_adjointGroup s t)) (inv_mem g.2)
  have hTL_fixed : TL ≤ (Units.map (entrywiseHom F3)).eqLocus (MonoidHom.id _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    exact hF3_dg s t hs ht
  have hTL3_adj : TL3 ≤ adjointGroup .G2 L := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨s, t, -, -, rfl⟩ := hx
    exact mul_mem (mul_mem g.2 (tz_mem_adjointGroup s t)) (inv_mem g.2)
  have hTL3_fixed : TL3 ≤ (Units.map (entrywiseHom F3)).eqLocus (MonoidHom.id _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    exact hF3_dg s t (hpow3 s hs) (hpow3 t ht)
  have hfixed :=
    (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices (τ := .G2) (Or.inl rfl)
      K L F3 hF3).1
  have hTL_image : TL ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hfixed]; exact fun x hx => ⟨hTL_adj hx, hTL_fixed hx⟩
  have hTL3_image : TL3 ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hfixed]; exact fun x hx => ⟨hTL3_adj hx, hTL3_fixed hx⟩
  have hF3_yg : Units.map (entrywiseHom F3) yg = yg := by
    rw [hF3_apply, hF0_yg, hF0_yg, hF0_yg]
  have hyg_adj : yg ∈ adjointGroup .G2 L :=
    mul_mem (mul_mem g.2 yq_mem_adjointGroup) (inv_mem g.2)
  have hyg_image : yg ∈ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hfixed]; exact ⟨hyg_adj, hF3_yg⟩
  let hExt : Ext3 (tzPart (L := L) (3 ^ b)) (yq : ModGL .G2 L) :=
    ext3_tzPart (L := L) (m := 3 ^ b) hζu_ne1
  let SL : Subgroup (ModGL .G2 L) := (extSub hExt).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom
  have hTL_le_SL : TL ≤ SL := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem _ (le_extSub hExt hx)
  have hyL_SL : yL ∈ SL := Subgroup.mem_map_of_mem _ (y_mem_extSub hExt)
  have hSL_adj : SL ≤ adjointGroup .G2 L := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨t, ht, k, -, rfl⟩ := (mem_extSub_iff_lt hExt).1 hx
    obtain ⟨s, u, -, -, rfl⟩ := ht
    exact mul_mem (mul_mem g.2 (mul_mem (tz_mem_adjointGroup s u)
      (pow_mem yq_mem_adjointGroup k))) (inv_mem g.2)
  have hSL_fixed : SL ≤ (Units.map (entrywiseHom F3)).eqLocus (MonoidHom.id _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨t, ht, k, -, rfl⟩ := (mem_extSub_iff_lt hExt).1 hx
    obtain ⟨s, u, hs, hu, rfl⟩ := ht
    have hconj : (g : ModGL .G2 L) * (tz s u * yq ^ k) * (g : ModGL .G2 L)⁻¹
        = dg s u * yg ^ k := by dsimp only [dg, yg]; rw [conj_pow]; group
    rw [hconj]
    change Units.map (entrywiseHom F3) (dg s u * yg ^ k) = dg s u * yg ^ k
    rw [map_mul, map_pow, hF3_dg s u hs hu, hF3_yg]
  have hSL_image : SL ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hfixed]; exact fun x hx => ⟨hSL_adj hx, hSL_fixed hx⟩
  let ι : adjointGroup .G2 K →* ModGL .G2 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype
  have hιinj : Function.Injective ι :=
    (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : ι.range = (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [show ι = (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  let T : Subgroup (adjointGroup .G2 K) := TL.comap ι
  let V : Subgroup (adjointGroup .G2 K) := TL3.comap ι
  let Q : Subgroup (adjointGroup .G2 K) := SL.comap ι
  have hmapT : T.map ι = TL := Subgroup.map_comap_eq_self (by rw [hrange]; exact hTL_image)
  have hmapV : V.map ι = TL3 := Subgroup.map_comap_eq_self (by rw [hrange]; exact hTL3_image)
  have hmapQ : Q.map ι = SL := Subgroup.map_comap_eq_self (by rw [hrange]; exact hSL_image)
  have hyL_range : yL ∈ ι.range := by rw [hrange]; exact hSL_image hyL_SL
  obtain ⟨y, hyval⟩ := MonoidHom.mem_range.mp hyL_range
  have hyQ : y ∈ Q := by
    rw [Subgroup.mem_comap, hyval]
    exact hyL_SL
  have hT_le_Q : T ≤ Q := Subgroup.comap_mono hTL_le_SL
  have hTL3_le_TL : TL3 ≤ TL := Subgroup.map_mono htzPart_mono
  have hV_le_T : V ≤ T := Subgroup.comap_mono hTL3_le_TL
  have hSL_eq : SL = TL ⊔ Subgroup.zpowers yL := by
    rw [show SL = (extSub hExt).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom from rfl,
      extSub_eq_closure hExt, MonoidHom.map_closure, Set.image_union, Set.image_singleton,
      Subgroup.closure_union]
    congr 1
    · show Subgroup.closure (TL : Set (ModGL .G2 L)) = TL
      rw [Subgroup.closure_eq]
    · rw [Subgroup.zpowers_eq_closure]
      congr 1
  have hQ_eq : Q = T ⊔ Subgroup.zpowers y := by
    apply Subgroup.map_injective hιinj
    rw [Subgroup.map_sup, hmapQ, hmapT, hSL_eq, MonoidHom.map_zpowers, hyval]
  have hcardT : Nat.card T = (3 ^ b) ^ 2 := by
    rw [← Subgroup.card_map_of_injective (K := T) (f := ι) hιinj, hmapT,
      Subgroup.card_map_of_injective (K := tzPart (L := L) (3 ^ b))
        (f := (MulAut.conj (g : ModGL .G2 L)).toMonoidHom)
        (MulAut.conj (g : ModGL .G2 L)).injective,
      card_tzPart (L := L) (3 ^ b) hb0 hζu]
  have hcardT3 : Nat.card (tzPart (L := L) (3 ^ b)) = 3 ^ (2 * b) := by
    rw [card_tzPart (L := L) (3 ^ b) hb0 hζu]
    rw [show (3 ^ b) ^ 2 = 3 ^ (2 * b) by rw [← pow_mul, mul_comm]]
  have hcardV : Nat.card V = 9 := by
    rw [← Subgroup.card_map_of_injective (K := V) (f := ι) hιinj, hmapV,
      Subgroup.card_map_of_injective (K := tzPart (L := L) 3)
        (f := (MulAut.conj (g : ModGL .G2 L)).toMonoidHom)
        (MulAut.conj (g : ModGL .G2 L)).injective,
      card_tzPart (L := L) 3 (by norm_num) hωu]
    norm_num
  have hcardQ : Nat.card Q = 3 ^ (2 * b + 1) := by
    rw [← Subgroup.card_map_of_injective (K := Q) (f := ι) hιinj, hmapQ,
      show SL = (extSub hExt).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (K := extSub hExt)
        (f := (MulAut.conj (g : ModGL .G2 L)).toMonoidHom)
        (MulAut.conj (g : ModGL .G2 L)).injective,
      card_extSub hExt, hcardT3, mul_comm, pow_succ]
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 2 * b + 1) hcardQ
  have hQindex : ¬ 3 ∣ Q.index := by
    intro hdvd
    have hmul : Q.index * Nat.card Q = Nat.card (adjointGroup .G2 K) := Subgroup.index_mul_card Q
    rw [hcardQ, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2] at hmul
    have hidx0 : Q.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have hpos : 0 < CFSG.Open.ordG2 q := by
        rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
        exact Nat.card_pos
      have hq0 : CFSG.Open.ordG2 q = 0 := by
        change CFSG.Open.ordG2 (Nat.card K) = 0
        rw [← hmul]
      omega
    have hv3 : padicValNat 3 (CFSG.Open.ordG2 q) = 2 * b + 1 := by
      simpa [b, q] using
        CFSG.RankThree.PartTwo.Sec12.OrdG2D4.v3_ordG2_of_not_dvd (a := q) hq3 h3q
    have hmul' : Q.index * 3 ^ (2 * b + 1) = CFSG.Open.ordG2 q := by simpa [q] using hmul
    have hv : padicValNat 3 (Q.index * 3 ^ (2 * b + 1)) = 2 * b + 1 := by rw [hmul', hv3]
    rw [padicValNat.mul hidx0 (pow_ne_zero (2 * b + 1) (by norm_num)),
      padicValNat.prime_pow] at hv
    have hle : 1 ≤ padicValNat 3 Q.index := one_le_padicValNat_of_dvd hidx0 hdvd
    omega
  have hyq_ne_one : (yq : ModGL .G2 L) ≠ 1 := by
    intro h
    exact hExt.not_mem (h ▸ (tzPart (L := L) (3 ^ b)).one_mem)
  have horder_yq : orderOf (yq : ModGL .G2 L) = 3 :=
    orderOf_eq_prime yq_pow_three hyq_ne_one
  have hyL_eq : yL = (MulAut.conj (g : ModGL .G2 L)) yq := by
    dsimp only [yL]; rw [MulAut.conj_apply]
  have horder_yL : orderOf yL = 3 := by
    rw [hyL_eq, (MulAut.conj (g : ModGL .G2 L)).orderOf_eq yq, horder_yq]
  have horder_y : orderOf y = 3 := by
    rw [← orderOf_injective ι hιinj y, hyval, horder_yL]
  have hζu_units : IsPrimitiveRoot ζu (3 ^ b) := IsPrimitiveRoot.coe_units_iff.mp hζu
  have hInt : k1566l6b_sd3Internal
      (extSub (ext3_tzPart (L := L) (m := 3 ^ b) hωu1))
      (tzPart (L := L) (3 ^ b)) (tzPart (L := L) 3) (yq : ModGL .G2 L) b b :=
    k1566l6b_sd3Internal_extSub (L := L) b hb1 hωu3 hωu1 hζu_units
  let Φ : adjointGroup .G2 K →* ModGL .G2 L :=
    (MulAut.conj ((g : ModGL .G2 L)⁻¹)).toMonoidHom.comp ι
  have hΦinj : Function.Injective Φ :=
    (MulAut.conj ((g : ModGL .G2 L)⁻¹)).injective.comp hιinj
  have hcomp_conj : ((MulAut.conj ((g : ModGL .G2 L)⁻¹)).toMonoidHom.comp
      (MulAut.conj (g : ModGL .G2 L)).toMonoidHom) = MonoidHom.id (ModGL .G2 L) := by
    refine MonoidHom.ext (fun x => ?_)
    change (MulAut.conj ((g : ModGL .G2 L)⁻¹)) ((MulAut.conj (g : ModGL .G2 L)) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hExt_eq : extSub hExt = extSub (ext3_tzPart (L := L) (m := 3 ^ b) hωu1) :=
    congrArg extSub (Subsingleton.elim hExt _)
  have hΦmap : Q.map Φ = extSub (ext3_tzPart (L := L) (m := 3 ^ b) hωu1) := by
    have h0 : Q.map Φ = extSub hExt := by
      rw [show Φ = (MulAut.conj ((g : ModGL .G2 L)⁻¹)).toMonoidHom.comp ι from rfl,
        ← Subgroup.map_map, hmapQ,
        show SL = (extSub hExt).map (MulAut.conj (g : ModGL .G2 L)).toMonoidHom from rfl,
        Subgroup.map_map, hcomp_conj, Subgroup.map_id]
    rwa [hExt_eq] at h0
  have hQsyl : ∃ P : Sylow 3 (adjointGroup .G2 K),
      (P : Subgroup (adjointGroup .G2 K)) = Q :=
    ⟨hQp.toSylow hQindex, rfl⟩
  obtain ⟨T0, V0, y0, hT0_eq, hy0_eq, hSD3b⟩ :=
    k1566l6a2_sd3_of_internal Φ hΦinj hQsyl hΦmap hInt
  have hσ₀pow : ∀ c : K, F0 (algebraMap K L c) = algebraMap K L (σ₀.toRingHom c) := by
    intro c
    rw [hF0]
    change (algebraMap K L c) ^ q0 = algebraMap K L (σ₀ c)
    rw [hσ₀, map_pow]
  have hιφ : ∀ h : adjointGroup .G2 K,
      ι (φ h) = Units.map (entrywiseHom F0) (ι h) := by
    intro h
    have hA := k1566l6a2_actor_compat (K := K) (L := L) F0 σ₀.toRingHom hσ₀pow
      ((h : adjointGroup .G2 K) : ModGL .G2 K)
    change baseChangeGL (algebraMap K L) (((φ h : adjointGroup .G2 K) : ModGL .G2 K)) =
      Units.map (entrywiseHom F0)
        (baseChangeGL (algebraMap K L) ((h : adjointGroup .G2 K) : ModGL .G2 K))
    rw [hφ h]
    exact hA
  have hScalar : ScalarAction T0 φ y0 (eps * (p : ℤ) ^ (f / 3)) := by
    rw [show eps * (p : ℤ) ^ (f / 3) = k by simp [k, q0]]
    constructor
    · apply hιinj
      rw [hιφ y0]
      have hιy0 : ι y0 = (g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹ := by
        have hΦy0 : Φ y0 = (MulAut.conj ((g : ModGL .G2 L)⁻¹)) (ι y0) := rfl
        calc ι y0 = (MulAut.conj (g : ModGL .G2 L))
              ((MulAut.conj ((g : ModGL .G2 L)⁻¹)) (ι y0)) := by
              rw [MulAut.conj_apply, MulAut.conj_apply]; group
          _ = (MulAut.conj (g : ModGL .G2 L)) (Φ y0) := by rw [hΦy0]
          _ = (MulAut.conj (g : ModGL .G2 L)) yq := by rw [hy0_eq]
          _ = (g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹ := by rw [MulAut.conj_apply]
      rw [hιy0]
      calc Units.map (entrywiseHom F0) ((g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹)
          = Units.map (entrywiseHom F0) (g : ModGL .G2 L) *
              Units.map (entrywiseHom F0) (yq : ModGL .G2 L) *
              (Units.map (entrywiseHom F0) (g : ModGL .G2 L))⁻¹ := by
            simp only [map_mul, map_inv]
        _ = ((g : ModGL .G2 L) * (n : ModGL .G2 L)) * yq *
              ((g : ModGL .G2 L) * (n : ModGL .G2 L))⁻¹ := by rw [hF0g, frob_yq]
        _ = (g : ModGL .G2 L) * ((n : ModGL .G2 L) * yq * (n : ModGL .G2 L)⁻¹) *
              (g : ModGL .G2 L)⁻¹ := by group
        _ = (g : ModGL .G2 L) * yq * (g : ModGL .G2 L)⁻¹ := by rw [hn_yq]
    · intro t ht
      rw [hT0_eq] at ht
      rw [Subgroup.mem_comap] at ht
      obtain ⟨s, u, hs, hu, hstu⟩ := ht
      have hFs : Units.map (F0 : L →* L) s = s ^ q0 := Units.ext (by
        rw [Units.coe_map, Units.val_pow_eq_pow_val]; simp [hF0])
      have hFu : Units.map (F0 : L →* L) u = u ^ q0 := Units.ext (by
        rw [Units.coe_map, Units.val_pow_eq_pow_val]; simp [hF0])
      have hιt : ι t = (g : ModGL .G2 L) * tz s u * (g : ModGL .G2 L)⁻¹ := by
        have hΦt : Φ t = (MulAut.conj ((g : ModGL .G2 L)⁻¹)) (ι t) := rfl
        calc ι t = (MulAut.conj (g : ModGL .G2 L))
              ((MulAut.conj ((g : ModGL .G2 L)⁻¹)) (ι t)) := by
              rw [MulAut.conj_apply, MulAut.conj_apply]; group
          _ = (MulAut.conj (g : ModGL .G2 L)) (Φ t) := by rw [hΦt]
          _ = (MulAut.conj (g : ModGL .G2 L)) (tz s u) := by rw [hstu]
          _ = (g : ModGL .G2 L) * tz s u * (g : ModGL .G2 L)⁻¹ := by rw [MulAut.conj_apply]
      apply hιinj
      rw [hιφ t, hιt, map_zpow, hιt]
      calc Units.map (entrywiseHom F0)
            ((g : ModGL .G2 L) * tz s u * (g : ModGL .G2 L)⁻¹)
          = Units.map (entrywiseHom F0) (g : ModGL .G2 L) *
              Units.map (entrywiseHom F0) (tz s u) *
              (Units.map (entrywiseHom F0) (g : ModGL .G2 L))⁻¹ := by
            simp only [map_mul, map_inv]
        _ = ((g : ModGL .G2 L) * (n : ModGL .G2 L)) * tz (s ^ q0) (u ^ q0) *
              ((g : ModGL .G2 L) * (n : ModGL .G2 L))⁻¹ := by
            rw [hF0g, frob_tz, hFs, hFu]
        _ = (g : ModGL .G2 L) * ((n : ModGL .G2 L) * tz (s ^ q0) (u ^ q0) *
              (n : ModGL .G2 L)⁻¹) * (g : ModGL .G2 L)⁻¹ := by group
        _ = (g : ModGL .G2 L) * tz (s ^ k) (u ^ k) * (g : ModGL .G2 L)⁻¹ := by rw [hn_tz]
        _ = ((g : ModGL .G2 L) * tz s u * (g : ModGL .G2 L)⁻¹) ^ k := by
            conv_rhs => rw [
              show (g : ModGL .G2 L) * tz s u * (g : ModGL .G2 L)⁻¹ =
                (MulAut.conj (g : ModGL .G2 L)) (tz s u) from by rw [MulAut.conj_apply],
              ← map_zpow (MulAut.conj (g : ModGL .G2 L)) (tz s u) k,
              MulAut.conj_apply, k1566l6a2_tz_zpow]
  refine ⟨Q, T0, V0, y0, ?_, hScalar⟩
  have ha' : padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) = b := ha_eq_b
  rw [ha']
  exact hSD3b

theorem gOutTarget_holds : GOutTarget := by
  intro K _ _ p f hp hp3 h3f hcard eps heps hmod σ₀ hσ₀ φ hφ
  exact k1566l6a_main K p f hp hp3 h3f hcard eps heps hmod σ₀ hσ₀ φ hφ

private theorem k1566l6b_sd3_of_internal
    {G H : Type*} [Group G] [Finite G] [Group H]
    (Φ : G →* H) (hΦ : Function.Injective Φ)
    {Q : Subgroup G} (hQsyl : ∃ P : Sylow 3 G, (P : Subgroup G) = Q)
    {Q' : Subgroup H} (hQmap : Q.map Φ = Q')
    {T' V' : Subgroup H} {y' : H} {e1 e2 : ℕ}
    (hInt : k1566l6b_sd3Internal Q' T' V' y' e1 e2) :
    ∃ (T V : Subgroup G) (y : G), SD3 G Q T V y e1 e2 := by
  classical
  let T : Subgroup G := T'.comap Φ
  let V : Subgroup G := V'.comap Φ
  have hy'Q' : y' ∈ Q' := by
    rw [hInt.eq_sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y')
  have hy'map : y' ∈ Q.map Φ := by rw [hQmap]; exact hy'Q'
  obtain ⟨y, hyQ, hyy'⟩ := Subgroup.mem_map.mp hy'map
  obtain ⟨P, hP⟩ := hQsyl
  have hQp : IsPGroup 3 Q := by rw [← hP]; exact P.isPGroup'
  have hind : ¬ 3 ∣ Q.index := by rw [← hP]; exact P.not_dvd_index
  have hTQ : T ≤ Q := by
    intro x hx
    have hx' : Φ x ∈ Q' := hInt.T_le hx
    rw [← hQmap] at hx'
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx'
    rwa [hΦ hqx] at hq
  have hT'range : T' ≤ Φ.range := by
    intro x hx
    have hxQ' : x ∈ Q' := hInt.T_le hx
    rw [← hQmap] at hxQ'
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.mp hxQ'
    exact ⟨q, hq⟩
  have hV'range : V' ≤ Φ.range := by
    intro x hx
    have hxQ' : x ∈ Q' := hInt.T_le (hInt.V_le hx)
    rw [← hQmap] at hxQ'
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.mp hxQ'
    exact ⟨q, hq⟩
  have hmapT : T.map Φ = T' := by
    show (T'.comap Φ).map Φ = T'
    exact Subgroup.map_comap_eq_self hT'range
  have hmapV : V.map Φ = V' := by
    show (V'.comap Φ).map Φ = V'
    exact Subgroup.map_comap_eq_self hV'range
  have hnormal : (T.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTQ]
    intro x hxQ
    rw [Subgroup.mem_normalizer_iff]
    have hx' : Φ x ∈ Subgroup.normalizer T' := by
      have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hInt.T_le).mp hInt.normal
      exact hle (by rw [← hQmap]; exact Subgroup.mem_map_of_mem Φ hxQ)
    rw [Subgroup.mem_normalizer_iff] at hx'
    intro z
    have hz : z ∈ T ↔ Φ z ∈ T' := Subgroup.mem_comap
    have hz' : x * z * x⁻¹ ∈ T ↔ Φ (x * z * x⁻¹) ∈ T' := Subgroup.mem_comap
    rw [hz, hz', map_mul, map_mul, map_inv]
    exact hx' (Φ z)
  have hcomm : IsMulCommutative ↥T := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    apply Subtype.ext
    apply hΦ
    change Φ ((a : G) * (b : G)) = Φ ((b : G) * (a : G))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hInt.comm.is_comm.comm ⟨Φ a, a.2⟩ ⟨Φ b, b.2⟩)
  have hVle : V ≤ T := Subgroup.comap_mono hInt.V_le
  have helemAb : IsElemAbelian 3 V := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm (fun a b => ?_)
      apply Subtype.ext
      apply hΦ
      change Φ ((a : G) * (b : G)) = Φ ((b : G) * (a : G))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hInt.elemAbelian.1.is_comm.comm ⟨Φ a, a.2⟩ ⟨Φ b, b.2⟩)
    · intro x hx
      apply hΦ
      rw [map_pow, map_one]
      exact hInt.elemAbelian.2 (Φ x) hx
  have homegaOne : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V := by
    intro t ht ht3
    exact hInt.omegaOne (Φ t) ht (by rw [← map_pow, ht3, map_one])
  have heqSup : Q = T ⊔ Subgroup.zpowers y := by
    apply Subgroup.map_injective hΦ
    rw [hQmap, Subgroup.map_sup, hmapT, MonoidHom.map_zpowers, hyy', ← hInt.eq_sup]
  have htransvection : ∀ v ∈ V,
      ((y * v * y⁻¹ * v⁻¹) ∈ V ∧ y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹) := by
    intro v hv
    have hv' : Φ v ∈ V' := hv
    obtain ⟨h1, h2⟩ := hInt.transvection (Φ v) hv'
    have hPhiComm : Φ (y * v * y⁻¹ * v⁻¹) = y' * Φ v * y'⁻¹ * (Φ v)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyy']
    constructor
    · show Φ (y * v * y⁻¹ * v⁻¹) ∈ V'
      rw [hPhiComm]; exact h1
    · apply hΦ
      show Φ (y * (y * v * y⁻¹ * v⁻¹) * y⁻¹) = Φ (y * v * y⁻¹ * v⁻¹)
      rw [map_mul, map_mul, map_inv, hyy', hPhiComm]
      exact h2
  have hnontrivial : ∃ v ∈ V, y * v * y⁻¹ ≠ v := by
    obtain ⟨v', hv'V, hv'ne⟩ := hInt.nontrivial
    have hv'Q' : v' ∈ Q' := hInt.T_le (hInt.V_le hv'V)
    obtain ⟨v, -, hvv'⟩ := Subgroup.mem_map.mp (by rw [hQmap]; exact hv'Q')
    refine ⟨v, ?_, ?_⟩
    · show Φ v ∈ V'; rw [hvv']; exact hv'V
    · intro hconj
      apply hv'ne
      have hh : Φ (y * v * y⁻¹) = Φ v := by rw [hconj]
      rw [map_mul, map_mul, map_inv, hyy', hvv'] at hh
      exact hh
  have hmoves : ∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v := by
    intro g hgQ hgT
    have hgQ' : Φ g ∈ Q' := by rw [← hQmap]; exact Subgroup.mem_map_of_mem Φ hgQ
    have hgT' : Φ g ∉ T' := fun h => hgT h
    obtain ⟨v', hv'V, hv'ne⟩ := hInt.moves (Φ g) hgQ' hgT'
    have hv'Q' : v' ∈ Q' := hInt.T_le (hInt.V_le hv'V)
    obtain ⟨v, -, hvv'⟩ := Subgroup.mem_map.mp (by rw [hQmap]; exact hv'Q')
    refine ⟨v, ?_, ?_⟩
    · show Φ v ∈ V'; rw [hvv']; exact hv'V
    · intro hconj
      apply hv'ne
      have hh : Φ (g * v * g⁻¹) = Φ v := by rw [hconj]
      rw [map_mul, map_mul, map_inv, hvv'] at hh
      exact hh
  have hcardV : Nat.card V = 9 := by
    rw [← Subgroup.card_map_of_injective (K := V) (f := Φ) hΦ, hmapV, hInt.cardV]
  have horderY : orderOf y = 3 := by
    rw [← orderOf_injective Φ hΦ y, hyy', hInt.orderY]
  have hiso : Nonempty
      ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T) := by
    let e : ↥T ≃* ↥T' :=
      (Subgroup.equivMapOfInjective T Φ hΦ).trans (MulEquiv.subgroupCongr hmapT)
    obtain ⟨e'⟩ := hInt.iso
    exact ⟨e'.trans e.symm⟩
  refine ⟨T, V, y, ?_⟩
  exact ⟨hQp, hind, hTQ, hnormal, hcomm, hVle, helemAb, homegaOne, heqSup, htransvection,
    hnontrivial, hmoves, hcardV, horderY, hiso⟩

private theorem k1566l6b_data
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∃ (Q0 : Subgroup (adjointGroup .G2 K)) (z0 : ↥Q0),
      (∃ P : Sylow 3 (adjointGroup .G2 K), (P : Subgroup (adjointGroup .G2 K)) = Q0) ∧
      Subgroup.center ↥Q0 = Subgroup.zpowers z0 ∧
      orderOf (z0 : adjointGroup .G2 K) = 3 ∧
      ∃ (φ : adjointGroup .G2 K →* ModGL .G2 (AlgebraicClosure K))
        (g : ModGL .G2 (AlgebraicClosure K))
        (ω : (AlgebraicClosure K)ˣ) (hω1 : ω ≠ 1) (ζu : (AlgebraicClosure K)ˣ),
        Function.Injective φ ∧ (3 : AlgebraicClosure K) ≠ 0 ∧ ω ^ 3 = 1 ∧
          IsPrimitiveRoot (ζu : AlgebraicClosure K)
            (3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) ∧
          Q0.map φ = (extSub (ext3_tzPart (L := AlgebraicClosure K)
            (m := 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) hω1)).map
              (MulAut.conj g).toMonoidHom ∧
          φ z0 = g * tz 1 ω⁻¹ * g⁻¹ :=
  open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups Subgroup in by
  classical
  let q := Nat.card K
  let b := padicValNat 3 (q ^ 2 - 1)
  have hq2 : 2 ≤ q := by omega
  have hb1 : 1 ≤ b := one_le_padicValNat_three_sq_sub_one (q := q) h3 hq2
  have hb0 : 3 ^ b ≠ 0 := pow_ne_zero b (by norm_num)
  have hbpos : 0 < b := by omega
  have h3b1 : 1 < 3 ^ b := one_lt_pow' (by norm_num) (by omega)
  have h3bdvd : 3 ∣ 3 ^ b := by
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b = 3 * c := by
      refine ⟨3 ^ (b - 1), ?_⟩
      have hb : b = (b - 1) + 1 := by omega
      calc 3 ^ b = 3 ^ ((b - 1) + 1) := congrArg (fun n => 3 ^ n) hb
        _ = 3 ^ (b - 1) * 3 := pow_succ _ _
        _ = 3 * 3 ^ (b - 1) := by ring
    exact ⟨c, hc⟩
  let L := AlgebraicClosure K
  have h3K : (3 : K) ≠ 0 := by
    intro h
    apply h3
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h))
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hqe, hp3]
    exact dvd_pow_self 3 e.ne_zero
  have h3L : (3 : L) ≠ 0 := by
    intro h
    apply h3K
    have h' : (algebraMap K L) (3 : K) = 0 := by
      rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, map_natCast]
      exact h
    exact (algebraMap K L).injective (h'.trans (map_zero _).symm)
  have : NeZero ((3 : ℕ) : L) := ⟨h3L⟩
  have : NeZero ((3 ^ b : ℕ) : L) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero b h3L⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3 ^ b)
  let ζu : Lˣ := (hζ.isUnit hb0).unit
  have hζu : IsPrimitiveRoot (ζu : L) (3 ^ b) := by simpa [ζu] using hζ
  have hζu_ne1 : ζu ≠ 1 := fun h => hζu.ne_one h3b1 (congrArg Units.val h)
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  let ωu : Lˣ := (hω.isUnit (by norm_num)).unit
  have hωu : IsPrimitiveRoot (ωu : L) 3 := by simpa [ωu] using hω
  have hωu3 : ωu ^ 3 = 1 := Units.ext (by simpa [ωu] using hω.pow_eq_one)
  have hωu1 : ωu ≠ 1 := fun h => hωu.ne_one (by norm_num) (congrArg Units.val h)
  obtain ⟨F, hF, hTW⟩ := exists_rational_conj_fixed K
  let n : ModGL .G2 L := if q % 3 = 1 then 1 else nw0
  have hn_mem : n ∈ adjointGroup .G2 L := by
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact one_mem _
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact nw0_mem_adjointGroup
  have hn_y : n * Units.map (entrywiseHom F) (yq : ModGL .G2 L) * n⁻¹ = yq := by
    rw [frob_yq]
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; simp
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]
      calc nw0 * yq * nw0⁻¹ = yq * nw0 * nw0⁻¹ := by rw [nw0_comm_yq]
        _ = yq := by group
  have hn_twist : ∀ s u : Lˣ, s ^ (3 ^ b) = 1 → u ^ (3 ^ b) = 1 →
      n * Units.map (entrywiseHom F) (tz s u : ModGL .G2 L) * n⁻¹ = tz s u := by
    intro s u hs hu
    have hFs : Units.map (F : L →* L) s = s ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    have hFu : Units.map (F : L →* L) u = u ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    rw [frob_tz, hFs, hFu]
    by_cases hmod : q % 3 = 1
    · have hdvd : 3 ^ b ∣ q - 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_one (q := q) hq3 hmod
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hs, one_pow, one_mul, pow_one]
      have hufix : u ^ q = u := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hu, one_pow, one_mul, pow_one]
      have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix]
      simp
    · have hmod2 : q % 3 = 2 := by
        have := Nat.mod_lt q (by norm_num : 0 < 3)
        omega
      have hdvd : 3 ^ b ∣ q + 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_two (q := q) hq3 hmod2
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have hsq1 : s ^ (q + 1) = 1 := by rw [hc, pow_mul, hs, one_pow]
        rwa [pow_succ] at hsq1
      have hufix : u ^ q = u⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have huq1 : u ^ (q + 1) = 1 := by rw [hc, pow_mul, hu, one_pow]
        rwa [pow_succ] at huq1
      have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix, nw0_tz]
      simp
  obtain ⟨g, hg, hFg, hrat⟩ := hTW n hn_mem
  let T : Subgroup (ModGL .G2 L) := tzPart (3 ^ b)
  let hExt : Ext3 T (yq : ModGL .G2 L) := ext3_tzPart (L := L) (m := 3 ^ b) hζu_ne1
  let H : Subgroup (ModGL .G2 L) := extSub hExt
  let S : Subgroup (ModGL .G2 L) := H.map (MulAut.conj g).toMonoidHom
  have hcardT : Nat.card T = 3 ^ (2 * b) := by
    calc Nat.card T = Nat.card (tzPart (3 ^ b) : Subgroup (ModGL .G2 L)) := rfl
      _ = (3 ^ b) ^ 2 := card_tzPart (L := L) (3 ^ b) hb0 hζu
      _ = 3 ^ (2 * b) := by rw [← pow_mul]; congr 1; omega
  have hcardH : Nat.card H = 3 ^ (2 * b + 1) := by
    calc Nat.card H = 3 * Nat.card T := card_extSub hExt
      _ = 3 * 3 ^ (2 * b) := by rw [hcardT]
      _ = 3 ^ (2 * b + 1) := by rw [mul_comm, pow_succ]
  have hHle : S ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    have hH : H = Subgroup.closure (T ∪ ({yq} : Set (ModGL .G2 L))) := extSub_eq_closure hExt
    rw [show S = H.map (MulAut.conj g).toMonoidHom from rfl, hH, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_union] at hy
    rcases hy with hy | hy
    · obtain ⟨s, u, hs, hu, rfl⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat (tz s u) (tz_mem_adjointGroup s u) (hn_twist s u hs hu)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat yq yq_mem_adjointGroup hn_y
  let φ : adjointGroup .G2 K →* ModGL .G2 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : φ.range = (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [show φ = (baseChangeGL (algebraMap K L)).comp
      (adjointGroup .G2 K).subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hSle : S ≤ φ.range := by rw [hrange]; exact hHle
  let Q0 : Subgroup (adjointGroup .G2 K) := S.comap φ
  have hmapQ : Q0.map φ = S := Subgroup.map_comap_eq_self hSle
  have hcardS : Nat.card S = 3 ^ (2 * b + 1) := by
    calc Nat.card S = Nat.card (H.map (MulAut.conj g).toMonoidHom) := rfl
      _ = Nat.card H := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 3 ^ (2 * b + 1) := hcardH
  have hcardQ : Nat.card Q0 = 3 ^ (2 * b + 1) := by
    rw [← Subgroup.card_map_of_injective (K := Q0) hφinj, hmapQ, hcardS]
  have hind : ¬ 3 ∣ Q0.index := by
    intro hdvd
    have hmul : Q0.index * Nat.card Q0 = Nat.card (adjointGroup .G2 K) :=
      Subgroup.index_mul_card Q0
    rw [hcardQ, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2] at hmul
    have hidx0 : Q0.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have hpos : 0 < CFSG.Open.ordG2 (Nat.card K) := by
        rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
        exact Nat.card_pos
      omega
    have hv3 : padicValNat 3 (CFSG.Open.ordG2 q) = 2 * b + 1 := by
      simpa [b, q] using CFSG.RankThree.PartTwo.Sec12.OrdG2D4.v3_ordG2_of_not_dvd (a := q) hq3 h3
    have hmul' : Q0.index * 3 ^ (2 * b + 1) = CFSG.Open.ordG2 q := by
      simpa [q] using hmul
    have hv : padicValNat 3 (Q0.index * 3 ^ (2 * b + 1)) = 2 * b + 1 := by rw [hmul', hv3]
    rw [padicValNat.mul hidx0 (pow_ne_zero (2 * b + 1) (by norm_num)),
      padicValNat.prime_pow] at hv
    have hle : 1 ≤ padicValNat 3 Q0.index := one_le_padicValNat_of_dvd hidx0 hdvd
    omega
  have hQ0syl : ∃ P : Sylow 3 (adjointGroup .G2 K),
      (P : Subgroup (adjointGroup .G2 K)) = Q0 :=
    ⟨(IsPGroup.of_card (n := 2 * b + 1) hcardQ).toSylow hind, rfl⟩
  let z0val : ModGL .G2 L := tz 1 ωu⁻¹
  have hωu_inv_pow : (ωu⁻¹ : Lˣ) ^ (3 ^ b) = 1 := by
    have h3inv : (ωu⁻¹) ^ 3 = 1 := by rw [inv_pow, hωu3, inv_one]
    obtain ⟨c, hc⟩ := h3bdvd
    rw [hc, pow_mul, h3inv, one_pow]
  have hzHmem : z0val ∈ H :=
    le_extSub hExt (tz_mem_tzPart (m := 3 ^ b) (by simp) hωu_inv_pow)
  let zH : ↥H := ⟨z0val, hzHmem⟩
  have hzHval : (zH : ModGL .G2 L) = z0val := rfl
  have hzH_order_val : orderOf z0val = 3 := by
    have h := orderOf_tz_one (L := L) (ω := ωu⁻¹)
      (by rw [inv_pow, hωu3, inv_one]) (by simpa using hωu1)
    simpa [z0val] using h
  have hzH_order : orderOf zH = 3 := by
    rw [← Subgroup.orderOf_coe zH, hzHval, hzH_order_val]
  have hcenterH : Subgroup.center ↥H = Subgroup.zpowers zH := by
    apply le_antisymm
    · intro x hx
      have hxv :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu x).mp hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxv
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hzHc : zH ∈ Subgroup.center ↥H :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu zH).mpr
          (Subgroup.mem_zpowers z0val)
      rw [← hk]
      exact Subgroup.zpow_mem (K := Subgroup.center ↥H) hzHc k
  let eH : ↥H ≃* ↥S := (MulAut.conj g).subgroupMap H
  have hcardCenterH : Nat.card (Subgroup.center ↥H) = 3 := by
    rw [hcenterH, Nat.card_zpowers, hzH_order]
  have hzSval : ((eH zH : ↥S) : ModGL .G2 L) = g * z0val * g⁻¹ := by
    rw [show ((eH zH : ↥S) : ModGL .G2 L) =
      (MulAut.conj g) ((zH : ↥H) : ModGL .G2 L) from
        MulEquiv.coe_subgroupMap_apply (MulAut.conj g) H zH]
    rw [MulAut.conj_apply, hzHval]
  have hzS_center : eH zH ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hzHc : zH ∈ Subgroup.center ↥H := by
      rw [hcenterH]
      exact Subgroup.mem_zpowers _
    have h := Subgroup.mem_center_iff.mp hzHc (eH.symm s)
    calc s * eH zH = eH (eH.symm s) * eH zH := by rw [eH.apply_symm_apply]
      _ = eH (eH.symm s * zH) := by rw [map_mul]
      _ = eH (zH * eH.symm s) := by rw [h]
      _ = eH zH * eH (eH.symm s) := by rw [map_mul]
      _ = eH zH * s := by rw [eH.apply_symm_apply]
  have hcardCenterS : Nat.card (Subgroup.center ↥S) = 3 := by
    have h : Nat.card ((Subgroup.center ↥H).map (eH : ↥H →* ↥S)) =
        Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (K := Subgroup.center ↥H) (f := (eH : ↥H →* ↥S))
        eH.injective
    rw [Subgroup.map_center_eq eH] at h
    rw [h, hcardCenterH]
  have hzSval_mem : ((eH zH : ↥S) : ModGL .G2 L) ∈ S := (eH zH).2
  have hzSval_mem' : ((eH zH : ↥S) : ModGL .G2 L) ∈ Q0.map φ := by
    rw [hmapQ]; exact hzSval_mem
  obtain ⟨z0, hz0Q, hφz0⟩ := Subgroup.mem_map.mp hzSval_mem'
  have hz0_order : orderOf z0 = 3 := by
    have hφinjQ : Function.Injective (φ.comp Q0.subtype) := hφinj.comp Subtype.val_injective
    show orderOf ((⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) = 3
    rw [Subgroup.orderOf_coe (⟨z0, hz0Q⟩ : ↥Q0),
      ← orderOf_injective (φ.comp Q0.subtype) hφinjQ ⟨z0, hz0Q⟩]
    change orderOf (φ z0) = 3
    rw [hφz0, Subgroup.orderOf_coe, eH.orderOf_eq zH, hzH_order]
  have hcenterQ : Subgroup.center ↥Q0 = Subgroup.zpowers ⟨z0, hz0Q⟩ := by
    have hz0c : (⟨z0, hz0Q⟩ : ↥Q0) ∈ Subgroup.center ↥Q0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply hφinj
      rw [show ((y * ⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) =
            (y : ↥(adjointGroup .G2 K)) * z0 from map_mul Q0.subtype y ⟨z0, hz0Q⟩,
          show ((⟨z0, hz0Q⟩ * y : ↥Q0) : ↥(adjointGroup .G2 K)) =
            z0 * (y : ↥(adjointGroup .G2 K)) from map_mul Q0.subtype ⟨z0, hz0Q⟩ y,
          map_mul, map_mul, hφz0]
      have hyS : φ (y : ↥(adjointGroup .G2 K)) ∈ S := Subgroup.mem_comap.mp y.2
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzS_center ⟨φ y, hyS⟩)
    let eQ : ↥Q0 ≃* ↥S :=
      (Subgroup.equivMapOfInjective Q0 φ hφinj).trans (MulEquiv.subgroupCongr hmapQ)
    have heQz : eQ ⟨z0, hz0Q⟩ = eH zH := by
      apply Subtype.ext
      change φ z0 = ((eH zH : ↥S) : ModGL .G2 L)
      exact hφz0
    have hcardCenterQ : Nat.card (Subgroup.center ↥Q0) = 3 := by
      have h : Nat.card ((Subgroup.center ↥Q0).map (eQ : ↥Q0 →* ↥S)) =
          Nat.card (Subgroup.center ↥Q0) :=
        Subgroup.card_map_of_injective (K := Subgroup.center ↥Q0)
          (f := (eQ : ↥Q0 →* ↥S)) eQ.injective
      rw [Subgroup.map_center_eq eQ] at h
      rw [← h, hcardCenterS]
    have hzord : orderOf (⟨z0, hz0Q⟩ : ↥Q0) = 3 := by
      rw [← eQ.orderOf_eq ⟨z0, hz0Q⟩, heQz, eH.orderOf_eq zH, hzH_order]
    have hle : Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0) ≤ Subgroup.center ↥Q0 :=
      Subgroup.zpowers_le.mpr hz0c
    have heq : Nat.card (Subgroup.center ↥Q0) =
        Nat.card (Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0)) := by
      rw [hcardCenterQ, Nat.card_zpowers, hzord]
    exact (Subgroup.eq_of_le_of_card_ge hle heq.le).symm
  refine ⟨Q0, ⟨z0, hz0Q⟩, hQ0syl, hcenterQ, hz0_order, φ, g, ωu, hωu1, ζu,
    hφinj, h3L, hωu3, hζu, ?_, ?_⟩
  · have hext : ext3_tzPart (L := L)
        (m := 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) hωu1 = hExt := Subsingleton.elim _ _
    rw [hext]
    exact hmapQ
  · simpa [z0val] using hφz0.trans hzSval

theorem g2SDTarget_holds : G2SDTarget := by
  intro K hKfield hKfinite p f hp hp3 hf1 hcard h3q eps heps hmod3
  have _ := hf1
  classical
  have hq3 : 3 ≤ Nat.card K := by rw [hcard]; exact h3q
  have h3dvd : ¬ 3 ∣ Nat.card K := by
    rw [hcard]
    intro h
    have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    exact hp3 h3p.symm
  obtain ⟨Q0, z0, hQ0syl, hcenterQ0, hz0order, φ, g, ω, hω1, ζu,
    hφinj, h3L, hω3, hζu, hmap, hφz0⟩ := k1566l6b_data (K := K) h3dvd hq3
  have hb : 1 ≤ padicValNat 3 (Nat.card K ^ 2 - 1) :=
    one_le_padicValNat_three_sq_sub_one (q := Nat.card K) h3dvd (by omega)
  have hζu' : IsPrimitiveRoot ζu (3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) :=
    IsPrimitiveRoot.coe_units_iff.mp hζu
  have hInt : k1566l6b_sd3Internal
      (extSub (ext3_tzPart (L := AlgebraicClosure K)
        (m := 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) hω1))
      (tzPart (L := AlgebraicClosure K) (3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)))
      (tzPart (L := AlgebraicClosure K) 3) (yq : ModGL .G2 (AlgebraicClosure K))
      (padicValNat 3 (Nat.card K ^ 2 - 1)) (padicValNat 3 (Nat.card K ^ 2 - 1)) :=
    k1566l6b_sd3Internal_extSub (L := AlgebraicClosure K)
      (b := padicValNat 3 (Nat.card K ^ 2 - 1)) hb hω3 hω1 hζu'
  let Φ : adjointGroup .G2 K →* ModGL .G2 (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp φ
  have hΦinj : Function.Injective Φ := (MulAut.conj g⁻¹).injective.comp hφinj
  have hcomp : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id (ModGL .G2 (AlgebraicClosure K)) := by
    refine MonoidHom.ext (fun x => ?_)
    change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hΦmap : Q0.map Φ = extSub (ext3_tzPart (L := AlgebraicClosure K)
      (m := 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1)) hω1) := by
    rw [show Φ = (MulAut.conj g⁻¹).toMonoidHom.comp φ from rfl,
      ← Subgroup.map_map, hmap, Subgroup.map_map, hcomp, Subgroup.map_id]
  obtain ⟨T0, V0, y0, hSD3⟩ :=
    k1566l6b_sd3_of_internal Φ hΦinj hQ0syl hΦmap hInt
  have haeq : padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) =
      padicValNat 3 (Nat.card K ^ 2 - 1) := by
    rcases heps with rfl | rfl
    · have hqmod : Nat.card K % 3 = 1 := by
        have h : (Nat.card K : ZMod 3) = (1 : ZMod 3) := by
          rw [hcard, Nat.cast_pow, hmod3]
          norm_num
        have := (ZMod.natCast_eq_natCast_iff' (Nat.card K) 1 3).mp h
        simpa using this
      have hnat : Int.natAbs ((p : ℤ) ^ f - 1) = Nat.card K - 1 := by
        have hpz : ((p : ℤ) ^ f) = (Nat.card K : ℤ) := by rw [← Nat.cast_pow, hcard]
        rw [hpz]
        have hz : (Nat.card K : ℤ) - 1 = ((Nat.card K - 1 : ℕ) : ℤ) := by omega
        rw [hz, Int.natAbs_natCast]
      rw [hnat]
      exact (padicValNat_three_sq_sub_one_of_mod_one hq3 hqmod).symm
    · have hqmod : Nat.card K % 3 = 2 := by
        have h : (Nat.card K : ZMod 3) = (2 : ZMod 3) := by
          rw [hcard, Nat.cast_pow, hmod3]
          decide
        have := (ZMod.natCast_eq_natCast_iff' (Nat.card K) 2 3).mp h
        simpa using this
      have hnat : Int.natAbs ((p : ℤ) ^ f - (-1)) = Nat.card K + 1 := by
        have hpz : ((p : ℤ) ^ f) = (Nat.card K : ℤ) := by rw [← Nat.cast_pow, hcard]
        rw [hpz]
        have hz : (Nat.card K : ℤ) - (-1) = ((Nat.card K + 1 : ℕ) : ℤ) := by omega
        rw [hz, Int.natAbs_natCast]
      rw [hnat]
      exact (padicValNat_three_sq_sub_one_of_mod_two hq3 hqmod).symm
  have hcenter : Nat.card ((Subgroup.center ↥Q0).map Q0.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (K := Subgroup.center ↥Q0) (f := Q0.subtype)
      Subtype.val_injective, hcenterQ0, Nat.card_zpowers, ← Subgroup.orderOf_coe z0, hz0order]
  refine ⟨Q0, T0, V0, y0, ?_, hcenter⟩
  simpa [← haeq] using hSD3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
