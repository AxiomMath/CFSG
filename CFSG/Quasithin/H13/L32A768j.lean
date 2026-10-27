module

public import CFSG.Quasithin.H13.L32A768i
public import CFSG.Quasithin.H13.L32A767s
public import CFSG.Quasithin.H13.L32A768d
public import CFSG.Quasithin.H13.L32A768f
public import CFSG.Quasithin.H13.L32AKG1468

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem pCore_le_center_of_quasisimple {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.pCore 2 X ≤ Subgroup.center X := by
  have hq' : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup X) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := X)
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect X := hq.1
    have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hq'
    exact Group.IsPerfect.not_isSolvable X inferInstance

omit [Finite G] in
theorem map_centralizer_singleton_subtype {I : Subgroup G} (z : ↥I) :
    (Subgroup.centralizer ({z} : Set ↥I)).map I.subtype =
      I ⊓ Subgroup.centralizer ({(z : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (SetLike.mem_coe.mp hx)
    exact Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg Subtype.val hx')⟩
  · intro hg
    obtain ⟨hgI, hgz⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgz
    exact ⟨⟨g, hgI⟩, SetLike.mem_coe.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext hgz)), rfl⟩

omit [Finite G] in
theorem map_centralizer_subtype {I : Subgroup G} (S : Subgroup ↥I) :
    (Subgroup.centralizer (S : Set ↥I)).map I.subtype =
      I ⊓ Subgroup.centralizer ((S.map I.subtype : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx s hs)
  · intro hg
    obtain ⟨hgI, hgC⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgI⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hgC s ⟨s, hs, rfl⟩

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem false_of_ident (h13314 : A6.Stmt13_3_14) (hIdent : KG1468Ident) {z : G}
    (hzV1 : z ∈ fsuV1 T V) (hz1 : z ≠ 1) {I : Subgroup G} (hKI : kz T V ≤ I)
    (hne : I ≠ kz T V) (hq : CFSG.IsQuasisimple ↥I)
    (hcase : Ch1.IsL34OrG24 (↥I ⧸ CFSG.pCore 2 ↥I) ∨
      ((∃ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s ∧ s ≠ .Ru ∧
          Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* NativeSporadic.Carrier s)) ∧
        Ch1.InducesTwoCentralInner z I)) : False := by
  have h := C.hyp
  obtain ⟨hVe, -, -, hV1, -⟩ := C.hMod G T L V h.hyp h.fsu
  have hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z := by
    obtain ⟨z', hz'V1, hz'1, hgen'⟩ := exists_gen_of_card_two hV1
    rcases hgen' z hzV1 with e | e
    · exact absurd e hz1
    · exact fun c hc => e ▸ hgen' c hc
  have hHz := hz_eq_centralizer_singleton hzV1 hgen
  have hIp : ⁅I, I⁆ = I := Subgroup.isPerfect_iff.mp hq.1
  have hIH := not_le_hz_of_ne hKI hne hIp
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hzI : z ∈ I := hKI (v_le_kz h C.hMod C.h1222 C.h1332 C.h1334 hzV)
  have hzC : z ∉ Subgroup.centralizer (I : Set G) := by
    intro hzc
    apply hIH
    rw [hHz]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzc x hx
  have hUK : fsuU T V ≤ kz T V := C.fsuU_le_pCoreOf_kz.trans (pCoreOf_le 2 _)
  set φ : ↥I →* ↥I ⧸ CFSG.pCore 2 ↥I := QuotientGroup.mk' (CFSG.pCore 2 ↥I) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker = CFSG.pCore 2 ↥I := QuotientGroup.ker_mk' _
  have hkerZ : φ.ker ≤ Subgroup.center ↥I := by
    rw [hker]
    exact pCore_le_center_of_quasisimple hq
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hsub2 : IsPGroup 2 I.subtype.ker := by
    rw [Subgroup.ker_subtype]
    exact IsPGroup.of_bot
  set zY : ↥I := ⟨z, hzI⟩ with hzY
  set x₀ := φ zY with hx₀
  have hz2 : z ^ 2 = 1 := hVe.2 z hzV
  have hx2 : orderOf x₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hzC ?_
    · rw [hx₀, ← map_pow, show zY ^ 2 = 1 from Subtype.ext hz2, map_one]
    · have hmem : zY ∈ φ.ker := h1
      have hc := hkerZ hmem
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩) :)
  set KY := (kz T V).subgroupOf I with hKY
  have hKYmap : KY.map I.subtype = kz T V := Subgroup.map_subgroupOf_eq_of_le hKI
  have hB : oTwoUpper (Subgroup.centralizer ({zY} : Set ↥I)) = KY := by
    apply Subgroup.map_injective I.subtype_injective
    rw [oTwoUpper_map_of_injective _ I.subtype_injective, map_centralizer_singleton_subtype,
      hKYmap, show ((zY : ↥I) : G) = z from rfl, ← hHz]
    exact oTwoUpper_inf_hz_eq hKI
  have hK0 : oTwoUpper (Subgroup.centralizer ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I))) =
      KY.map φ := by
    rw [hx₀, oTwoUpper_centralizer_map φ hφs hkerZ hker2 zY, hB]
  have hiso : Nonempty (↥(oTwoUpper (Subgroup.centralizer ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I)))) ⧸
      CFSG.pCore 2 ↥(oTwoUpper (Subgroup.centralizer ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I))))
        ≃* alternatingGroup (Fin 5)) := by
    rw [hK0]
    obtain ⟨e1⟩ := nonempty_quot_map_equiv φ hker2 KY
    have e2 := nonempty_quot_map_equiv I.subtype hsub2 KY
    rw [hKYmap] at e2
    obtain ⟨e2⟩ := e2
    obtain ⟨e3⟩ := C.nonempty_quot_alt5
    exact ⟨e1.trans (e2.symm.trans e3)⟩
  set UY := (fsuU T V).subgroupOf I with hUY
  have hUYmap : UY.map I.subtype = fsuU T V := Subgroup.map_subgroupOf_eq_of_le (hUK.trans hKI)
  have hpK : (pCoreOf 2 KY).map I.subtype = pCoreOf 2 (kz T V) := by
    rw [← pCoreOf_map_eq I.subtype hsub2 KY, hKYmap]
  have hUO : UY ≤ pCoreOf 2 KY := by
    rw [← Subgroup.map_le_map_iff_of_injective I.subtype_injective, hUYmap, hpK]
    exact C.fsuU_le_pCoreOf_kz
  have hcommY : ∀ a ∈ UY, ∀ w ∈ pCoreOf 2 KY, a * w * a⁻¹ * w⁻¹ ∈ φ.ker →
      a * w * a⁻¹ * w⁻¹ = 1 := by
    intro a ha w hw hk
    have hwK : (w : G) ∈ pCoreOf 2 (kz T V) := hpK ▸ ⟨w, hw, rfl⟩
    have h1 := C.comm_Q (pCoreOf_kz_le hwK) (Subgroup.mem_subgroupOf.mp ha)
    have h2 : (a : G) * w * (a : G)⁻¹ * (w : G)⁻¹ ∈ fsuV1 T V := by
      have := inv_mem h1
      rwa [show ((w : G) * a * (w : G)⁻¹ * (a : G)⁻¹)⁻¹ = (a : G) * w * (a : G)⁻¹ * (w : G)⁻¹ by
        group] at this
    have hc := hkerZ hk
    apply Subtype.ext
    rcases hgen _ h2 with e | e
    · simpa using e
    · exfalso
      apply hzC
      rw [← e]
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩)
        simpa using this
  have hA1 : UY.map φ ≤ pCoreOf 2 (oTwoUpper (Subgroup.centralizer
      ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I)))) := by
    rw [hK0, pCoreOf_map_eq φ hker2 KY]
    exact Subgroup.map_mono hUO
  have hA2 : ∀ a ∈ UY.map φ, ∀ b ∈ UY.map φ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (fsuU_comm h (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
  have hA3 : oTwoUpper (Subgroup.centralizer ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I))) ≤
      Subgroup.normalizer ((UY.map φ : Subgroup _) : Set (↥I ⧸ CFSG.pCore 2 ↥I)) := by
    rw [hK0]
    rintro _ ⟨k, hk, rfl⟩
    have hkN := C.H_le_normalizer_U (oTwoUpper_le _ (Subgroup.mem_subgroupOf.mp hk))
    have hkN' : k ∈ Subgroup.normalizer (UY : Set ↥I) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hUY, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp hkN y
    exact Subgroup.le_normalizer_map φ ⟨k, hkN', rfl⟩
  have hA4 : 16 ≤ (UY.map φ ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper (Subgroup.centralizer
      ({x₀} : Set (↥I ⧸ CFSG.pCore 2 ↥I)))) : Set (↥I ⧸ CFSG.pCore 2 ↥I))).relIndex (UY.map φ) := by
    rw [hK0, relIndex_centralizer_map φ hkerZ hker2 hcommY,
      ← Subgroup.relIndex_map_map_of_injective _ _ I.subtype_injective,
      Subgroup.map_inf_eq _ _ _ I.subtype_injective, map_centralizer_subtype, hpK, hUYmap,
      ← inf_assoc, inf_eq_left.mpr (hUK.trans hKI)]
    have hle : fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (kz T V) : Set G) ≤ u0 T V :=
      fun w hw => C.mem_u0_of_centralizer_kz h13314 (Subgroup.mem_inf.mp hw).1
        fun x hx => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 x hx
    have hdvd := Subgroup.relIndex_dvd_of_le_left (fsuU T V) hle
    rw [relIndex_u0 h C.hMod C.h63] at hdvd
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero fun h0 => ?_) hdvd
    have e := Subgroup.relIndex_mul_card
      (fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (kz T V) : Set G)) (fsuU T V)
    rw [h0, zero_mul] at e
    exact (Nat.card_pos (α := ↥(fsuU T V))).ne' e.symm
  rcases hcase with hL34 | ⟨hs, l, hlI, hlz, -, P, hP, hPl⟩
  · exact hIdent _ x₀ (Or.inl ⟨hL34, hx2⟩) ⟨hiso, UY.map φ, hA1, hA2, hA3, hA4⟩
  · refine hIdent _ x₀ (Or.inr ⟨hs, Subgroup.mem_top x₀, hx2, ?_⟩)
      ⟨hiso, UY.map φ, hA1, hA2, hA3, hA4⟩
    have hc : z * l⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have e := hlz x hx
      calc x * (z * l⁻¹) = z * (z⁻¹ * x * z) * l⁻¹ := by group
        _ = z * (l⁻¹ * x * l) * l⁻¹ := by rw [e]
        _ = z * l⁻¹ * x := by group
    have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
    have hpz : ∀ p ∈ P, p * z * p⁻¹ * z⁻¹ ∈ pCoreOf 2 I := by
      intro p hp
      have hpI : p ∈ I := hP.1 hp
      have hcl : p * l * p⁻¹ * l⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
        rw [← commutatorElement_def]
        exact hPl p hp
      have hcp := Subgroup.mem_centralizer_iff.mp hc p hpI
      have hpzl : p * z * p⁻¹ * z⁻¹ = p * l * p⁻¹ * l⁻¹ := by
        have e1 : z = (z * l⁻¹) * l := by group
        calc p * z * p⁻¹ * z⁻¹ = p * ((z * l⁻¹) * l) * p⁻¹ * ((z * l⁻¹) * l)⁻¹ := by
              rw [← e1]
          _ = (p * (z * l⁻¹)) * l * p⁻¹ * l⁻¹ * (z * l⁻¹)⁻¹ := by group
          _ = ((z * l⁻¹) * p) * l * p⁻¹ * l⁻¹ * (z * l⁻¹)⁻¹ := by rw [hcp]
          _ = (z * l⁻¹) * (p * l * p⁻¹ * l⁻¹) * (z * l⁻¹)⁻¹ := by group
          _ = p * l * p⁻¹ * l⁻¹ := by
              rw [Subgroup.mem_centralizer_iff.mp hcl (z * l⁻¹) (mul_mem hzI (inv_mem hlI))]
              group
      have hcz : p * z * p⁻¹ * z⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
        rw [hpzl]
        exact hcl
      have hcI : p * z * p⁻¹ * z⁻¹ ∈ I :=
        mul_mem (mul_mem (mul_mem hpI hzI) (inv_mem hpI)) (inv_mem hzI)
      have hsq : (p * z * p⁻¹ * z⁻¹) ^ 2 = 1 := by
        have hcomm : z * (p * z * p⁻¹ * z⁻¹) = (p * z * p⁻¹ * z⁻¹) * z :=
          Subgroup.mem_centralizer_iff.mp hcz z hzI
        rw [hz'] at hcomm ⊢
        rw [pow_two]
        calc p * z * p⁻¹ * z * (p * z * p⁻¹ * z) = p * z * p⁻¹ * (z * (p * z * p⁻¹ * z)) := by
              group
          _ = p * z * p⁻¹ * ((p * z * p⁻¹ * z) * z) := by rw [hcomm]
          _ = p * (z * z) * p⁻¹ * (z * z) := by group
          _ = 1 := by rw [hzz]; group
      have hzpI : I ≤ Subgroup.normalizer (Subgroup.zpowers (p * z * p⁻¹ * z⁻¹) : Set G) := by
        intro x hx
        refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hxc : Commute x (p * z * p⁻¹ * z⁻¹) := Subgroup.mem_centralizer_iff.mp hcz x hx
        rw [(hxc.zpow_right k).eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers _ k
      have hzp2 : IsPGroup 2 (Subgroup.zpowers (p * z * p⁻¹ * z⁻¹)) := fun y =>
        ⟨1, Subtype.ext (by simpa using (isElemAbelian_zpowers_of_pow hsq).2 y y.2)⟩
      exact le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hcI) hzpI hzp2
        (Subgroup.mem_zpowers _)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set PY := P.subgroupOf I with hPY
    have hS2 : IsPGroup 2 (PY.map φ) :=
      (hP.2.1.comap_of_injective I.subtype I.subtype_injective).map φ
    have hSi : ¬ 2 ∣ (PY.map φ).index := fun h2 =>
      hP.2.2 (h2.trans (Subgroup.index_map_dvd _ hφs))
    have hSx : ∀ s ∈ PY.map φ, s * x₀ = x₀ * s := by
      rintro _ ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      have hmem : p * zY * p⁻¹ * zY⁻¹ ∈ φ.ker := by
        rw [hker, ← pCoreOf_subgroupOf_self, Subgroup.mem_subgroupOf]
        exact hpz p hpP
      have e : φ p * φ zY * (φ p)⁻¹ * (φ zY)⁻¹ = 1 := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        exact MonoidHom.mem_ker.mp hmem
      calc φ p * x₀ = φ p * φ zY * (φ p)⁻¹ * (φ zY)⁻¹ * (φ zY * φ p) := by rw [hx₀]; group
        _ = x₀ * φ p := by rw [e, one_mul]
    have hxN : Subgroup.zpowers x₀ ≤ Subgroup.normalizer ((PY.map φ : Subgroup _) : Set _) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_conj_mem fun s hs => by
        rw [← hSx s hs, mul_inv_cancel_right]
        exact hs)
    have hx2' : IsPGroup 2 (Subgroup.zpowers x₀) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hx2, pow_one])
    have hQ := IsPGroup.to_sup_of_normal_right' hx2' hS2 hxN
    have hmax := (hS2.toSylow hSi).is_maximal' hQ le_sup_right
    refine ⟨PY.map φ, ⟨le_top, hS2, ?_⟩, ?_, hSx⟩
    · show ¬ 2 ∣ (PY.map φ).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hSi
    · have hx : x₀ ∈ Subgroup.zpowers x₀ ⊔ PY.map φ :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
      rw [hmax] at hx
      exact hx

end Ctx764

end CFSG.Quasithin.H13.L32A
