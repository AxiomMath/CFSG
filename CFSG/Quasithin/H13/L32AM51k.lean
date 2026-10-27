module

public import CFSG.Quasithin.H13.L32AM51j
public import CFSG.Quasithin.H13.L32ACSk9
public import CFSG.Quasithin.H13.L32AM51h
public import CFSG.Quasithin.H13.L32AM51i

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm
open scoped IsMulCommutative commutatorElement

theorem lemma14_7_51_mod_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (h38 : Lemma14_7_38)
    (h48 : Lemma14_7_48) (hA21 : AsA21SQTKSection) (hLevi : Lemma14751Levi) :
    Lemma14_7_51_Mod := by
  classical
  intro G _ _ T L V H S K hK hHKT hl1 hP π hsurj hker V₂ hV2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hypF98_of h1222 h1332 h1334 hA37 hA38 hA39 S
  obtain ⟨W, hW⟩ := exists_topW S hF
  obtain ⟨K', hcK', -, hUK⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hK
    have e : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    rw [e, hcK'] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have C : Top51 T L V H W K π := ⟨hW, hK, hKn, hUK, hP, hker, hsurj⟩
  have : IsMulCommutative ↥(conjClosure V H) := C.comm
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', k₀, h', N⟩ := L32A.exists_not1471 hF s (h38 G T L V H S γ γ' g s)
  have hQ := (hF.F916_2_aux N.setup N.pos N.le).1
  obtain ⟨πK, hπs, hkerK, hD, hPar⟩ :=
    exists_coords51 h1222 h1332 h1334 S hK hKn hl1 hP hsurj hker C.range_piK
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, c, hz, hz1, ha, haV, hc, hcV⟩ := S14.exists_basis
  obtain ⟨x, hx, -, hxa, -⟩ := S14.exists_x hz hz1 ha haV hc hcV
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hinf : V ⊓ W = fsuV1 T V := Setting147.inf_V_eq S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW
  have hV₂U : ∀ v ∈ V₂, v ∈ conjClosure V H := fun v hv => le_conjClosure V H (hV2.2.1 hv)
  have hmkeq : ∀ u₁ u₂ : ↥(conjClosure V H),
      InternalSec.secMk (W.subgroupOf (conjClosure V H)) u₁ =
        InternalSec.secMk (W.subgroupOf (conjClosure V H)) u₂ ↔ (u₁ : G) * (u₂ : G)⁻¹ ∈ W := by
    intro u₁ u₂
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
    rfl
  set â : Hat V H W := InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨a, hV₂U a ha⟩ with hâ
  have hsec : ∀ v (hv : v ∈ V₂),
      InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨v, hV₂U v hv⟩ = 1 ∨
        InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨v, hV₂U v hv⟩ = â := by
    intro v hv
    rcases S14.mem_V2 ha haV hv with h | h
    · exact Or.inl ((A6.A6Mod.secMk_eq_one_iff _).mpr (C.hV₁W h))
    · right
      rw [hâ, hmkeq]
      show v * a⁻¹ ∈ W
      have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S14.mul_self_V (hV2.2.1 ha))
      rw [ha1, S14.comm_V (hV2.2.1 hv) (hV2.2.1 ha)]
      exact C.hV₁W h
  have hcommW : ∀ h : ↥H, C.act h â = â → ∀ v ∈ V₂, ⁅v, (h : G)⁆ ∈ W := by
    intro h hh v hv
    have hfix : C.act h (InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨v, hV₂U v hv⟩) =
        InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨v, hV₂U v hv⟩ := by
      rcases hsec v hv with h1 | h1 <;> rw [h1]
      · exact map_one _
      · exact hh
    rw [C.act_mk, hmkeq] at hfix
    rw [show ⁅v, (h : G)⁆ = ((h : G) * v * (h : G)⁻¹ * v⁻¹)⁻¹ by
      rw [commutatorElement_def]
      group]
    exact W.inv_mem hfix
  have hcommLe : ∀ Y : Subgroup G, ∀ hYH : Y ≤ H,
      (∀ y (hy : y ∈ Y), C.act ⟨y, hYH hy⟩ â = â) → ⁅V₂, Y⁆ ≤ W := by
    intro Y hYH hY
    rw [Subgroup.commutator_le]
    intro v hv y hy
    exact hcommW ⟨y, hYH hy⟩ (hY y hy) v hv
  have hTfix : ∀ k : ↥K, (k : G) ∈ T → C.act (Subgroup.inclusion C.hKH k) â = â := by
    intro k hkT
    have hka : (k : G) * a * (k : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 hkT) a).mp ha
    rw [hâ, C.act_mk]
    rcases hsec _ hka with h1 | h1
    · exfalso
      have h2 : (k : G) * a * (k : G)⁻¹ ∈ V ⊓ W :=
        ⟨hV2.2.1 hka, (A6.A6Mod.secMk_eq_one_iff _).mp h1⟩
      rw [hinf] at h2
      exact haV ((Subgroup.mem_normalizer_iff.mp (S14.T_V1 hkT) a).mpr h2)
    · exact h1
  rcases C.fix_cases hπs hkerK hA21 hQ hD hTfix with hP13 | hM2
  swap
  ·
    exfalso
    have hxK : x ∈ K := hl1 hxl
    have hxP : πK ⟨x, hxK⟩ ∈ Lin.par 4 2 := by
      rw [← hPar]
      exact Subgroup.mem_sup_right ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hxl, rfl⟩
    have h1 := hM2 ⟨x, hxK⟩ hxP
    rw [hâ, C.act_mk, hmkeq] at h1
    have h2 : c * a⁻¹ ∈ V ⊓ W := ⟨V.mul_mem hc (V.inv_mem (hV2.2.1 ha)), by
      rw [← hxa]
      exact h1⟩
    rw [hinf] at h2
    apply hcV
    have := V₂.mul_mem (hV2.1 h2) ha
    rwa [inv_mul_cancel_right] at this
  set T₀ : Subgroup G := T ⊓ preimG π (alternatingGroup (Fin 8)) with hT₀
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hT₀H : T₀ ≤ H := inf_le_left.trans hTH
  have hT₀2 : IsPGroup 2 T₀ := hTsylH.2.1.to_le inf_le_left
  have hOT : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le S.hyp hTH
  have hT₀dec : ∀ t (ht : t ∈ T₀), ∃ k : ↥K, (k : G) ∈ T ∧
      π (Subgroup.inclusion C.hKH k) = π ⟨t, hT₀H ht⟩ ∧ (k : G)⁻¹ * t ∈ pCoreOf 2 H := by
    intro t ht
    obtain ⟨htT, htA⟩ := ht
    obtain ⟨htH, hA⟩ := mem_preimG.mp htA
    obtain ⟨k, hkK, hk⟩ := C.exists_pi_eq hA
    have ho : k⁻¹ * t ∈ pCoreOf 2 H := by
      have h1 : π (⟨k⁻¹ * t, H.mul_mem (H.inv_mem (C.hKH hkK)) htH⟩ : ↥H) = 1 := by
        have e : (⟨k⁻¹ * t, H.mul_mem (H.inv_mem (C.hKH hkK)) htH⟩ : ↥H) =
            (⟨k, C.hKH hkK⟩ : ↥H)⁻¹ * ⟨t, htH⟩ := rfl
        rw [e, map_mul, map_inv, hk, inv_mul_cancel]
      exact (C.pi_eq_one_iff _).mp h1
    have hkT : k ∈ T := by
      have e : k = t * (k⁻¹ * t)⁻¹ := by group
      rw [e]
      exact T.mul_mem htT (T.inv_mem (hOT ho))
    exact ⟨⟨k, hkK⟩, hkT, hk, ho⟩
  have hT₀KO : T₀ ≤ K ⊔ pCoreOf 2 H := by
    intro t ht
    obtain ⟨k, -, -, ho⟩ := hT₀dec t ht
    have e : t = (k : G) * ((k : G)⁻¹ * t) := by group
    rw [e]
    exact Subgroup.mul_mem_sup k.2 ho
  have hT₀idx : T₀.relIndex T = 2 := by
    set φ : ↥T →* ℤˣ := Equiv.Perm.sign.comp (π.comp (Subgroup.inclusion hTH)) with hφ
    have hkerφ : T₀.subgroupOf T = φ.ker := by
      ext t
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      constructor
      · rintro ⟨-, htA⟩
        obtain ⟨htH, hA⟩ := mem_preimG.mp htA
        exact mem_alternatingGroup.mp hA
      · intro h1
        exact ⟨t.2, mem_preimG.mpr ⟨hTH t.2, mem_alternatingGroup.mpr h1⟩⟩
    have hsurjφ : Function.Surjective φ := by
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one _⟩
      · obtain ⟨t₀, ht₀T, hodd⟩ := exists_odd_T S hsurj
        refine ⟨⟨t₀, ht₀T⟩, ?_⟩
        rcases Int.units_eq_one_or (sign (π ⟨t₀, hTH ht₀T⟩)) with h1 | h1
        · exact absurd (mem_alternatingGroup.mpr h1) hodd
        · exact h1
    rw [Subgroup.relIndex, hkerφ, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurjφ,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  have hθinj := C.theta_injective hπs hkerK
  have hθA : ∀ g, C.theta hπs hkerK g ∈ alternatingGroup (Fin 8) := fun g =>
    (((C.psi hπs hkerK).symm.trans C.iota) g).2
  have hP0 : (T₀.subgroupOf H).map π = (unitriangular 4 (ZMod 2)).map (C.theta hπs hkerK) := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨k, hkT, hk, -⟩ := hT₀dec t (Subgroup.mem_subgroupOf.mp ht)
      refine ⟨πK k, ?_, ?_⟩
      · rw [← hD]
        exact ⟨k, Subgroup.mem_subgroupOf.mpr hkT, rfl⟩
      · rw [C.theta_piK hπs hkerK]
        exact hk
    · rintro ⟨u, hu, rfl⟩
      rw [← hD] at hu
      obtain ⟨k, hkT, rfl⟩ := hu
      refine ⟨Subgroup.inclusion C.hKH k, Subgroup.mem_subgroupOf.mpr
        ⟨Subgroup.mem_subgroupOf.mp hkT, mem_preimG.mpr ⟨C.hKH k.2, C.pi_mem_alt k.2⟩⟩, ?_⟩
      exact (C.theta_piK hπs hkerK k).symm
  have hkerT₀ : π.ker ≤ T₀.subgroupOf H := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    refine Subgroup.mem_subgroupOf.mpr ⟨hOT ((C.pi_eq_one_iff y).mp hy),
      mem_preimG.mpr ⟨y.2, ?_⟩⟩
    show π y ∈ alternatingGroup (Fin 8)
    rw [hy]
    exact one_mem _
  have hLev : ∀ j : ℕ, (j = 1 ∨ j = 3) → ∃ Y : Subgroup G, Y ≤ K ∧
      Y ≤ Subgroup.centralizer (V₂ : Set G) ∧
      ∀ g ∈ Lin.par 4 j, g ^ 3 = 1 → ∃ u : ↥K, (u : G) ∈ Y ∧ πK u = g := by
    intro j hj
    have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> norm_num
    have hj4 : j < 4 := by rcases hj with rfl | rfl <;> norm_num
    set R := (Lin.par 4 j).map (C.theta hπs hkerK) with hR
    have hUR : (T₀.subgroupOf H).map π ≤ R := by
      rw [hP0]
      exact Subgroup.map_mono (BinaryParabolic.unitriangular_le_flagStabilizer _)
    have hRr : R ≤ π.range := by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact le_top
    have h3 : ((T₀.subgroupOf H).map π).relIndex R = 3 := by
      rw [hP0, hR, Subgroup.relIndex_map_map_of_injective _ _ hθinj]
      exact Lin.relIndex_par hj1 hj4
    have hn : ¬ R ≤ Subgroup.normalizer
        (((T₀.subgroupOf H).map π : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
      rw [hP0]
      exact not_le_normalizer_map hθinj (Lin.not_par_le_normalizer hj1 hj4)
    obtain ⟨hTX, hsyl, hsup, hquot⟩ := s3_preimG hT₀H hT₀2 hkerT₀ hUR hRr h3 hn
    set X := preimG π R with hX
    set Y := oTwoUpper X with hY
    have hXH : X ≤ H := preimG_le π R
    have hYX : Y ≤ X := oTwoUpper_le X
    have hYH : Y ≤ H := hYX.trans hXH
    have hXA : ∀ y (hy : y ∈ X), π ⟨y, hXH hy⟩ ∈ alternatingGroup (Fin 8) := by
      intro y hy
      obtain ⟨hyH, g', hg'P, hg'⟩ := mem_preimG.mp hy
      rw [← hg']
      exact hθA g'
    have hYK : Y ≤ K := C.oTwoUpper_le_K hXH hXA
    have hYfix : ∀ y (hy : y ∈ Y), C.act ⟨y, hYH hy⟩ â = â := by
      intro y hy
      obtain ⟨hyH, g', hg'P, hg'⟩ := mem_preimG.mp (hYX hy)
      obtain ⟨k, rfl⟩ := hπs g'
      have he : C.act ⟨y, hYH hy⟩ = C.act (Subgroup.inclusion C.hKH k) :=
        C.act_eq_of_pi_eq (by rw [← C.theta_piK hπs hkerK k]; exact hg'.symm)
      rw [he]
      exact hP13 k (Lin.par_le_stab2 hj hg'P)
    have hcommY : ⁅V₂, Y⁆ ≤ W := hcommLe Y hYH hYfix
    have hYo : oTwoUpper Y = Y := oTwoUpper_idem' X
    have hT₀N : T₀ ≤ Subgroup.normalizer (Y : Set G) := hTX.trans (le_normalizer_oTwoUpper X)
    have hsyl' : IsSylowTwoOf T₀ (Y ⊔ T₀) := by
      rw [hY, hsup]
      exact hsyl
    have hquot' : quasithinO2QuotientIso (Y ⊔ T₀) (Equiv.Perm (Fin 3)) := by
      rw [hY, hsup]
      exact hquot
    have hne8 := hLevi G T L V H S K hK hHKT hl1 hP π hsurj hker W C.hV₁W C.hWU C.hHW Y V₂ T₀
      hV2 hYK hYo inf_le_left hT₀idx hT₀KO hT₀N hsyl' hquot' hcommY
    have hYc := comm_eq_bot_of_T0 S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW hV2 hYH hYo
      inf_le_left hT₀N hsyl' hquot' hne8 hcommY
    have hYC : Y ≤ Subgroup.centralizer (V₂ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm Y V₂).trans hYc)
    refine ⟨Y, hYK, hYC, fun g hg hg3 => ?_⟩
    obtain ⟨k, rfl⟩ := hπs g
    have hkX : (k : G) ∈ X := mem_preimG.mpr ⟨C.hKH k.2, ⟨πK k, hg, C.theta_piK hπs hkerK k⟩⟩
    obtain ⟨m, hm⟩ := exists_pow_mem_oTwoUpper X hkX
    obtain ⟨q, hq⟩ := L32NSet14.exists_four_pow m
    refine ⟨k ^ 4 ^ m, ?_, ?_⟩
    · have e : ((k ^ 4 ^ m : ↥K) : G) = ((k : G) ^ 2 ^ m) ^ 2 ^ m := by
        rw [Subgroup.coe_pow, ← pow_mul, ← mul_pow]
        norm_num
      rw [e]
      exact Y.pow_mem hm _
    · rw [map_pow, ← hq, pow_add, pow_one, pow_mul, hg3, one_pow, mul_one]
  obtain ⟨Y₁, -, hY₁C, hY₁l⟩ := hLev 1 (Or.inl rfl)
  obtain ⟨Y₃, -, hY₃C, hY₃l⟩ := hLev 3 (Or.inr rfl)
  obtain ⟨u₁, hu₁, hπu₁⟩ := hY₁l Lin.c1 Lin.c1_mem Lin.c1_cube
  obtain ⟨u₃, hu₃, hπu₃⟩ := hY₃l Lin.c3 Lin.c3_mem Lin.c3_cube
  set A := Subgroup.centralizer (V₂ : Set G) ⊓ K with hA
  have hu₁A : (u₁ : G) ∈ A := ⟨hY₁C hu₁, u₁.2⟩
  have hu₃A : (u₃ : G) ∈ A := ⟨hY₃C hu₃, u₃.2⟩
  let φ : ↥A →* Lin.SLn 4 := πK.comp (Subgroup.inclusion inf_le_right)
  have hφ1 : φ ⟨u₁, hu₁A⟩ = Lin.c1 := hπu₁
  have hφ3 : φ ⟨u₃, hu₃A⟩ = Lin.c3 := hπu₃
  have hker2 : IsPGroup 2 φ.ker := by
    rintro ⟨y, hy⟩
    have hy1 : πK (Subgroup.inclusion inf_le_right y) = 1 := hy
    have hyO : (y : G) ∈ pCoreOf 2 K := (hkerK _).mp hy1
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hyO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hE : Lin.e9.range ≤ φ.range := by
    rintro _ ⟨a', rfl⟩
    refine ⟨⟨u₁, hu₁A⟩ ^ (Multiplicative.toAdd a').1.val *
      ⟨u₃, hu₃A⟩ ^ (Multiplicative.toAdd a').2.val, ?_⟩
    rw [map_mul, map_pow, map_pow, hφ1, hφ3]
    rfl
  obtain ⟨P, hP', hP9⟩ := exists_e9_of_hom φ hker2 hE Lin.card_e9 Lin.e9_comm Lin.e9_cube
  exact two_le_pRank_of_injective (Subgroup.inclusion (inf_le_left : A ≤ _))
    (Subgroup.inclusion_injective _) hP' hP9

end CFSG.Quasithin.H13.L32A.C
