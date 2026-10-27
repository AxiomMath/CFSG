module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspL3
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspG2Aut
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspNat
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspDefs

public section
namespace CFSG.Quasithin.H13.Ch4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.NQCat L3M
  CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin (perfectCore map_perfectCore le_perfectCore_of_perfect)

theorem insp436G2_holds :
    Insp436G2 := by
  intro G _ _ K P V R₀ n hn hKq hG2 hP hPSL hnat hV hR₀2 hR₀N hR₀P hNP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup ↥K := P.comap K.subtype with hP₀
  have hPK : P ≤ K := hP.1.1
  have hP₀K : P₀.map K.subtype = P := by
    rw [hP₀, Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])]
  have hP₀max : IsMaxParabolic2 (⊤ : Subgroup ↥K) P₀ :=
    L436.isMaxParabolic2_comap K.subtype K.subtype_injective K.range_subtype.symm hP
  obtain ⟨S₁, hS₁, hNS₁, hPcov⟩ :=
    CFSG.Quasithin.Lie2Parabolic.exists_sylow_of_isMaxParabolic2 hP₀max
  obtain ⟨hn', L, _, _, _, hL, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hG2
  have : Finite (ModGL Tag.G2 L) := finite_modGL
  have hL4 := CFSG.Quasithin.H13.RootData.G2.four_le_card hL hn'
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := L) 2).1)
  have hres := CFSG.QuasithinUnique.Setup.X6.G2_residualOvergroupsAt (K := L)
  set q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hT := isSylowTwoOf_map_top hS₁ (f := e.toMonoidHom.comp q) (e.surjective.comp hqs)
  have hidx : ∀ {X : Subgroup ↥(adjointGroup Tag.G2 L)}, CFSG.QuasithinUnique.IsSylowTwoOf X ⊤ →
      ¬ 2 ∣ X.index := fun h => by
    have := h.2.2
    rwa [← Subgroup.relIndex_top_right]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(adjointGroup Tag.G2 L)
    (hT.2.1.toSylow (hidx hT)) (hU₀.2.1.toSylow (hidx hU₀))
  set θ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.G2 L) := e.trans (MulAut.conj c)
    with hθ
  set Φ : ↥K →* ↥(adjointGroup Tag.G2 L) := θ.toMonoidHom.comp q with hΦ
  have hΦs : Function.Surjective Φ := θ.surjective.comp hqs
  have hΦker : ∀ x, Φ x = 1 → x ∈ Subgroup.center ↥K := by
    intro x hx
    have h1 : q x = 1 := θ.injective (by rw [map_one]; exact hx)
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker : Φ.ker ≤ P₀ := fun x hx =>
    ((Subgroup.center_le_normalizer _).trans hNS₁) (hΦker x hx)
  have hSU : S₁.map Φ = (posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L) := by
    have h1 : ((c • hT.2.1.toSylow (hidx hT) : Sylow 2 ↥(adjointGroup Tag.G2 L)) :
        Subgroup ↥(adjointGroup Tag.G2 L)) =
        (posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L) := by
      rw [hc]
      exact IsPGroup.toSylow_coe _ _
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e (q y), Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hcov : P₀.map Φ ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective Φ hΦs]
    exact covBy_map_of_ker_le hΦs hker hPcov
  have hUM : (posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L) ≤ P₀.map Φ :=
    hSU ▸ Subgroup.map_mono (Subgroup.le_normalizer.trans hNS₁)
  obtain ⟨j, hj⟩ := (hres.2.2.1 _ hUM).mp hcov
  have hPcore : (perfectCore P₀).map K.subtype = perfectCore P := by rw [map_perfectCore, hP₀K]
  have hmemP₀ : ∀ a : ↥K, (a : G) ∈ perfectCore P → a ∈ perfectCore P₀ := by
    intro a ha
    rw [← hPcore] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rwa [Subtype.ext hba] at hb
  have hP₀le : ∀ a ∈ perfectCore P₀, (a : G) ∈ perfectCore P := fun a ha =>
    hPcore ▸ Subgroup.mem_map_of_mem _ ha
  have hcoreJ : ((perfectCore P₀).map Φ).map (adjointGroup Tag.G2 L).subtype =
      perfectCore (parabolicSubgroup Tag.G2 L {CFSG.QuasithinUnique.Setup.X6.g2Index j}) := by
    rw [map_perfectCore Φ P₀, hj, CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_map_subgroupOf
      (parabolicSubgroup_le_adjointGroup _ _ _)]
  rcases fin_two_cases (CFSG.QuasithinUnique.Setup.X6.g2Index j) with hj0 | hj1
  ·
    have hcore0 : ((perfectCore P₀).map Φ).map (adjointGroup Tag.G2 L).subtype =
        perfectCore (parabolicSubgroup Tag.G2 L {i0}) := by
      rw [← hj0]
      exact hcoreJ
    intro r hr
    set ψ : MulAut ↥K := conjOn K (hR₀N hr) with hψ
    have hfix : ∀ x ∈ perfectCore P₀, ψ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hψ, coe_conjOn, ← Subgroup.mem_centralizer_iff.mp (hR₀P hr) _ (hP₀le x hx),
        mul_inv_cancel_right]
    set φ' : MulAut ↥(adjointGroup Tag.G2 L) := θ.symm.trans ((autCenter ψ).trans θ) with hφ'
    have hφ'Φ : ∀ y : ↥K, φ' (Φ y) = Φ (ψ y) := by
      intro y
      simp only [hφ', hΦ, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
      rw [hq, QuotientGroup.mk'_apply, autCenter_mk]
      rfl
    have hfix' : ∀ x : ↥(adjointGroup Tag.G2 L),
        (x : ModGL Tag.G2 L) ∈ perfectCore (parabolicSubgroup Tag.G2 L {i0}) → φ' x = x := by
      intro x hx
      rw [← hcore0] at hx
      obtain ⟨x', hx', hx'x⟩ := hx
      have hxx : x' = x := Subtype.ext hx'x
      subst hxx
      obtain ⟨y, hy, rfl⟩ := hx'
      rw [hφ'Φ, hfix y hy]
    have hφ'1 := G2A.aut_eq_one_of_fixes hL hn' φ' hfix'
    have hψ1 : autCenter ψ = 1 := by
      ext y
      have h := congrArg (fun β : MulAut ↥(adjointGroup Tag.G2 L) => β (θ y)) hφ'1
      simp only [hφ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
      rw [MulAut.one_apply]
      exact θ.injective h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := congrArg Subtype.val (eq_of_autCenter_eq_one hKq.1 ψ hψ1 ⟨k, hk⟩)
    rw [hψ, coe_conjOn] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  ·
    exfalso
    have hcore1 : ((perfectCore P₀).map Φ).map (adjointGroup Tag.G2 L).subtype =
        perfectCore (parabolicSubgroup Tag.G2 L {i1}) := by
      rw [← hj1]
      exact hcoreJ
    obtain ⟨F, _, _, hF, hnat'⟩ := hnat
    set Ψ : ↥K →* ModGL Tag.G2 L := (adjointGroup Tag.G2 L).subtype.comp Φ with hΨ
    have hP1 : (perfectCore P₀).map Ψ = perfectCore (parabolicSubgroup Tag.G2 L {i1}) := by
      rw [hΨ, ← Subgroup.map_map]
      exact hcore1
    set O : Subgroup ↥K := (CFSG.Open.pCoreOf 2 (perfectCore P)).comap K.subtype with hO
    set Vk : Subgroup ↥K := V.comap K.subtype with hVk
    have hOle : CFSG.Open.pCoreOf 2 (perfectCore P) ≤ perfectCore P :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hOP : O ≤ perfectCore P₀ := fun a ha => hmemP₀ a (hOle ha)
    have hON : perfectCore P₀ ≤ Subgroup.normalizer (O : Set ↥K) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hO, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hP₀le a ha)) x
    have hO2 : IsPGroup 2 ↥O :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (perfectCore P)).comap_of_injective K.subtype
        K.subtype_injective
    have hRN : perfectCore (parabolicSubgroup Tag.G2 L {i1}) ≤
        Subgroup.normalizer ((O.map Ψ : Subgroup (ModGL Tag.G2 L)) : Set (ModGL Tag.G2 L)) := by
      rw [← hP1]
      exact (Subgroup.map_mono hON).trans (Subgroup.le_normalizer_map Ψ)
    have hRQ : O.map Ψ ≤ parabolicRadical Tag.G2 L {i1} := by
      rw [← G2Rad.pCoreOf_perfectCore_parabolic hL hn' i1]
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hRN (hO2.map Ψ)
      rw [← hP1]
      exact Subgroup.map_mono hOP
    have hZ1 := G2Rad.centerOf_le_of_le_normalizer hL4 hRQ hRN
    have hW : Vk.map Ψ ≤ CFSG.Quasithin.centerOf (O.map Ψ) := by
      rintro _ ⟨v, hv, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ (hV hv).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨o, ho, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 := Subgroup.mem_centralizer_iff.mp (hV hv).2 _ ho
      exact Subtype.ext (by simpa using h1)
    have hcent := G2Rad.perfectCore_le_centralizer (K := L)
    have hVK : V ≤ K := fun v hv => hPK ((CFSG.Quasithin.perfectCore_le P) (hOle (hV hv).1))
    have hAK : perfectCore P ≤ K := (CFSG.Quasithin.perfectCore_le P).trans hPK
    refine G2A.false_of_natural_comm_inf hnat' (Z := (Subgroup.center ↥K).map K.subtype) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      show (z : G) ∈ K ⊓ Subgroup.centralizer (K : Set G)
      refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · intro a ha v hv
      set a' : ↥K := ⟨a, hAK ha⟩
      set v' : ↥K := ⟨v, hVK hv⟩
      have ha' : Ψ a' ∈ perfectCore (parabolicSubgroup Tag.G2 L {i1}) := by
        rw [← hP1]
        exact Subgroup.mem_map_of_mem _ (hmemP₀ a' ha)
      have hv' : Ψ v' ∈ (N1 : Subgroup (ModGL Tag.G2 L)) :=
        hZ1 (hW (Subgroup.mem_map_of_mem _ (show v' ∈ Vk from hv)))
      have hcomm : Ψ v' * Ψ a' = Ψ a' * Ψ v' :=
        Subgroup.mem_centralizer_iff.mp (hcent ha') _ hv'
      have h1 : Ψ (a' * v' * a'⁻¹ * v'⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcomm]
        group
      have h2 : Φ (a' * v' * a'⁻¹ * v'⁻¹) = 1 := Subtype.ext h1
      exact ⟨_, hΦker _ h2, rfl⟩

end CFSG.Quasithin.H13.Ch4
