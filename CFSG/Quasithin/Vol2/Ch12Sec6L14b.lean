module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13b
public import CFSG.Quasithin.Vol2.Ch12Sec6L615

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

section Images

variable {G : Type} [Group G] {U : Subgroup G}

theorem autOn_sup_eq {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G))
    (hB : B ≤ Subgroup.normalizer (U : Set G)) : autOn (A ⊔ B) U = autOn A U ⊔ autOn B U := by
  unfold autOn
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem autOn_le_normalizer {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    autOn A U ≤ Subgroup.normalizer (autOn B U : Set (MulAut ↥U)) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => InternalSec.autOn_normal_of hAB a ha b hb, fun hb => ?_⟩
  have := InternalSec.autOn_normal_of hAB a⁻¹ ((autOn A U).inv_mem ha) _ hb
  rwa [show a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b by group] at this

theorem autOn_perfect {H : Subgroup G} (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hH : ⁅H, H⁆ = H) : ⁅autOn H U, autOn H U⁆ = autOn H U := by
  have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have h2 : Group.IsPerfect ↥(autOn H U) :=
    Group.IsPerfect.ofSurjective (f := InternalSec.autOnHom hHU)
      (InternalSec.autOnHom_surjective hHU)
  exact Subgroup.isPerfect_iff.mp h2

noncomputable def autOnEquiv {H : Subgroup G} (hHU : H ≤ Subgroup.normalizer (U : Set G))
    {N : Subgroup ↥H} [N.Normal]
    (hN : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (U : Set G) ↔ h ∈ N) :
    ↥H ⧸ N ≃* ↥(autOn H U) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    ext h
    rw [InternalSec.mem_ker_autOnHom hHU, hN])).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hHU))

end Images

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem isTwoReducedIn_Usec (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    IsTwoReducedIn (Kv ⊔ S) (Usec Kv S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  refine ⟨(Usec_le Kv S).trans (pCoreOf_le 2 _),
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S),
    isElemAbelian_Usec Kv S, fun D hDX hXD hD2 => ?_⟩
  have hD2' : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := hD2 d hd
    have hk' : d ^ 2 ^ k ∈ pCoreOf 2 (Kv ⊔ S) := by
      rw [hO]
      exact ⟨(Kv ⊔ S).pow_mem (hDX hd) _, hk⟩
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 _ ⟨_, hk'⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    show d ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  have hDO := le_pCoreOf_of_le_normalizer 2 hDX hXD hD2'
  rw [hO] at hDO
  exact hDO.trans inf_le_right

theorem Kv_le_normalizer_Usec {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (_hC : Ctx1262 F v Kv S) : Kv ≤ Subgroup.normalizer (Usec Kv S : Set G) :=
  ((le_sup_left : Kv ≤ Kv ⊔ S).trans (le_normalizer_pCoreOf 2 _)).trans
    (normalizer_le_normalizer_Usec Kv S)

theorem mem_centralizer_Usec_iff (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (k : ↥Kv) :
    (k : G) ∈ Subgroup.centralizer (Usec Kv S : Set G) ↔ k ∈ CFSG.pCore 2 ↥Kv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hsub : IsSubnormal Kv (Kv ⊔ S) :=
    A4.subnormal_of_normal le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hSK))
  rw [← mem_pCoreOf_iff]
  constructor
  · intro hk
    have hkO : (k : G) ∈ pCoreOf 2 (Kv ⊔ S) := by
      rw [hO]
      exact ⟨(le_sup_left : Kv ≤ Kv ⊔ S) k.2, hk⟩
    have hle : Kv ⊓ pCoreOf 2 (Kv ⊔ S) ≤ pCoreOf 2 Kv :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
          (le_normalizer_pCoreOf 2 (Kv ⊔ S) ((le_sup_left : Kv ≤ Kv ⊔ S) hx)))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle ⟨k.2, hkO⟩
  · intro hk
    have hkO := A4.pCoreOf_le_of_subnormal 2 hsub hk
    rw [hO] at hkO
    exact hkO.2

noncomputable def autOn_Kv_equiv (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    ↥Kv ⧸ CFSG.pCore 2 ↥Kv ≃* ↥(autOn Kv (Usec Kv S)) :=
  autOnEquiv (Kv_le_normalizer_Usec hC) (mem_centralizer_Usec_iff hD7 hC)

theorem isSQTKCat_autOn_Kv (h1222 : Stmt12_2_2) (hD7 : Lemma12_6_13) {F : Frame126 T L V}
    {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    CFSG.SectionRank.IsSQTKCat ↥(autOn Kv (Usec Kv S)) := by
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hq := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hqtke.1 hH2
  have h1 := (QuasithinUnique.Vol2Native.SQTKHypCat.isSQTKCat hq).subgroup
    (modO2Image (Gv v) Kv)
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hC.cComp
  let eX : ↥Kv ⧸ CFSG.pCore 2 ↥Kv ≃* ↥(modO2Image (Gv v) Kv) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have h2 : CFSG.SectionRank.IsSQTKCat (↥Kv ⧸ CFSG.pCore 2 ↥Kv) :=
    CFSG.SectionRank.IsSQTKCat.of_mulEquiv h1 eX
  exact CFSG.SectionRank.IsSQTKCat.of_mulEquiv h2 (autOn_Kv_equiv hD7 hC).symm

end S126T2

end CFSG.Quasithin.H13
