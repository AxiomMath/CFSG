module

public import CFSG.Quasithin.Vol2.Ch3Sec3G2Blk
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace G2Rho

open CFSG.Quasithin.H13.Orbit
open CFSG.Quasithin.H.Mathieu (RealizesBy realizes_iff)

section Induced

variable {N A M : Type*} [Group N] [Group A] [Group M]

theorem map_ker_eq (β : A →* M) (a : MulAut A) (ha : ∀ x, β x = 1 ↔ β (a x) = 1) :
    β.ker.map (a : A →* A) = β.ker := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (ha x).mp hx
  · intro hy
    refine ⟨a.symm y, (ha _).mpr ?_, by simp⟩
    rw [MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def inducedAut (β : A →* M) (hβ : Function.Surjective β) (a : MulAut A)
    (ha : ∀ x, β x = 1 ↔ β (a x) = 1) : MulAut M :=
  ((QuotientGroup.quotientKerEquivOfSurjective β hβ).symm.trans
    (QuotientGroup.congr β.ker β.ker a (map_ker_eq β a ha))).trans
    (QuotientGroup.quotientKerEquivOfSurjective β hβ)

theorem inducedAut_apply (β : A →* M) (hβ : Function.Surjective β) (a : MulAut A)
    (ha : ∀ x, β x = 1 ↔ β (a x) = 1) (x : A) : inducedAut β hβ a ha (β x) = β (a x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective β hβ).symm (β x) =
      (x : A ⧸ β.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective β hβ)
    ((QuotientGroup.congr β.ker β.ker a (map_ker_eq β a ha))
      ((QuotientGroup.quotientKerEquivOfSurjective β hβ).symm (β x))) = β (a x)
  rw [h1, QuotientGroup.congr_mk]
  rfl

@[expose] noncomputable def inducedHom (φ : N →* MulAut A) (β : A →* M)
    (hβ : Function.Surjective β) (hφ : ∀ n x, β x = 1 ↔ β (φ n x) = 1) : N →* MulAut M where
  toFun n := inducedAut β hβ (φ n) (hφ n)
  map_one' := by
    ext m
    obtain ⟨x, rfl⟩ := hβ m
    rw [inducedAut_apply, map_one]
    rfl
  map_mul' n₁ n₂ := by
    ext m
    obtain ⟨x, rfl⟩ := hβ m
    rw [inducedAut_apply, MulAut.mul_apply, inducedAut_apply, inducedAut_apply, map_mul,
      MulAut.mul_apply]

theorem inducedHom_apply (φ : N →* MulAut A) (β : A →* M) (hβ : Function.Surjective β)
    (hφ : ∀ n x, β x = 1 ↔ β (φ n x) = 1) (n : N) (x : A) :
    inducedHom φ β hβ hφ n (β x) = β (φ n x) :=
  inducedAut_apply β hβ (φ n) (hφ n) x

end Induced

section Coord

variable {G : Type} [Group G]

theorem exists_coord {L T : Subgroup G} [IsMulCommutative ↥(vPlus L T)]
    (hMp : mPlus L T = L) (hUV : blockU L ≤ vPlus L T)
    (hV4 : vPlus L T = ⁅vPlus L T, L⁆ ⊔
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G))
    (hVL : ⁅vPlus L T, L⁆ ≤ blockU L)
    (hreal : G2NaturalDerived (V := ↥(vPlus L T)) (autOn L (vPlus L T)) (tildeComm L T L)
      (cvPlus L T) 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = 2)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L (vPlus L T)))
      (βU : ↥(blockU L) →* (FFModel.zornQ (quasithinG2 K)).Mod),
      Function.Surjective π ∧ Function.Surjective βU ∧
      (∀ u, βU u = 1 ↔ (u : G) ∈ blockZ L) ∧
      ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (u u' : ↥(blockU L)),
        (u' : G) = ((π γ : MulAut ↥(vPlus L T)) ⟨u, hUV u.2⟩ : G) →
          βU u' = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ (βU u) := by
  obtain ⟨K, _, _, hK, hR⟩ := hreal
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := charP_two_of_natCard_two hK2
  obtain ⟨π, β, hβ⟩ := (realizes_iff _ _ _ _).1 hR
  set V := vPlus L T with hVdef
  have hVLV : ⁅V, L⁆ ≤ V := hVL.trans hUV
  have hZV : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤ V := by
    rw [hV4]
    exact le_sup_right
  have hZN : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hzV : z ∈ V := hZV hz
    have hcomm : ∀ y ∈ V, z * y * z⁻¹ = y := by
      intro y hy
      have h1 : (⟨z, hzV⟩ : ↥V) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨z, hzV⟩ := mul_comm _ _
      have h2 : z * y = y * z := congrArg Subtype.val h1
      rw [h2]
      group
    constructor
    · intro hx
      rw [hcomm x (hVLV hx)]
      exact hx
    · intro hx
      have hxV' : x ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem hzV) (hVLV hx)) hzV
        simpa [mul_assoc] using this
      rw [← hcomm x hxV']
      exact hx
  have htop : ∀ v : ↥V, v ∈ tildeComm L T L := by
    intro v
    have h1 : (⊤ : Subgroup ↥V) ≤ tildeComm L T L := by
      have e : (⊤ : Subgroup ↥V) = (⁅V, L⁆ ⊔ quasithinOmegaOneCenter T ⊓
          Subgroup.centralizer (L : Set G)).subgroupOf V := by
        rw [← hV4, Subgroup.subgroupOf_self]
      rw [e, Subgroup.subgroupOf_sup hVLV hZV]
      refine sup_le_sup le_rfl ?_
      intro x hx
      show (x : G) ∈ Subgroup.centralizer (mPlus L T : Set G)
      rw [hMp]
      exact (Subgroup.mem_subgroupOf.mp hx).2
    exact h1 (Subgroup.mem_top v)
  let ι : ↥(blockU L) →* ↥(tildeComm L T L) :=
    (Subgroup.inclusion hUV).codRestrict (tildeComm L T L) (fun u => htop _)
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK2, π, β.comp ι, hβ.1, ?_, ?_, ?_⟩
  ·
    intro m
    obtain ⟨x, rfl⟩ := hβ.2.2.2.2.2.2.2.1 m
    have hx : ((x : ↥V) : G) ∈ ⁅V, L⁆ ⊔
        quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
      rw [← hV4]
      exact (x : ↥V).2
    obtain ⟨a, ha, b, hb, hab⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZN).mp hx
    have haU : a ∈ blockU L := hVL ha
    refine ⟨⟨a, haU⟩, ?_⟩
    have hb1 : β ((ι ⟨a, haU⟩)⁻¹ * x) = 1 := by
      rw [hβ.2.2.2.2.2.2.2.2.1]
      have e : ((((ι ⟨a, haU⟩)⁻¹ * x : ↥(tildeComm L T L)) : ↥V) : G) = b := by
        show a⁻¹ * ((x : ↥V) : G) = b
        have h2 : ((x : ↥V) : G) = a * b := hab
        rw [h2]
        group
      show ((((ι ⟨a, haU⟩)⁻¹ * x : ↥(tildeComm L T L)) : ↥V) : G) ∈
        Subgroup.centralizer (mPlus L T : Set G)
      rw [e, hMp]
      exact hb.2
    rw [map_mul, map_inv, inv_mul_eq_one] at hb1
    exact hb1
  · intro u
    show β (ι u) = 1 ↔ _
    rw [hβ.2.2.2.2.2.2.2.2.1]
    constructor
    · intro h1
      refine ⟨u.2, ?_⟩
      have h2 : (u : G) ∈ Subgroup.centralizer (mPlus L T : Set G) := h1
      rwa [hMp] at h2
    · intro h1
      show (u : G) ∈ Subgroup.centralizer (mPlus L T : Set G)
      rw [hMp]
      exact h1.2
  · intro γ u u' hu'
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β (ι u))
    have hm' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ (m : Multiplicative _) ∈
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
      zornAct_mem_O0 _ (Subgroup.commutator_le_self _) γ m.2
    have hu : ((π γ : ↥(autOn L V)) : MulAut ↥V) ((ι u : ↥(tildeComm L T L)) : ↥V) ∈
        tildeComm L T L := htop _
    have h1 := hβ.2.2.2.2.2.2.2.2.2 γ (ι u) m hu hm' hm.symm
    have e : ι u' = ⟨((π γ : ↥(autOn L V)) : MulAut ↥V) ((ι u : ↥(tildeComm L T L)) : ↥V), hu⟩ :=
      Subtype.ext (Subtype.ext hu')
    show β (ι u') = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ (β (ι u))
    rw [e, h1, ← hm]
    rfl

end Coord

section Psi

variable {G : Type} [Group G]

@[expose] noncomputable def conjU (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥(blockU L) :=
  (blockU L).normalizerMonoidHom.comp
    (Subgroup.inclusion fun _ hg => C1.mem_normalizer_blockU hg)

theorem conjU_apply (L : Subgroup G) (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    ((conjU L g u : ↥(blockU L)) : G) = g * u * g⁻¹ := rfl

theorem exists_psi
    {L T : Subgroup G} [IsMulCommutative ↥(vPlus L T)]
    (hUV : blockU L ≤ vPlus L T) (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L (vPlus L T)))
    (βU : ↥(blockU L) →* (FFModel.zornQ (quasithinG2 K)).Mod) (hπ : Function.Surjective π)
    (hβs : Function.Surjective βU) (hβk : ∀ u, βU u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (u u' : ↥(blockU L)),
      (u' : G) = ((π γ : MulAut ↥(vPlus L T)) ⟨u, hUV u.2⟩ : G) →
        βU u' = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ (βU u)) :
    ∃ ψ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (FFModel.zornQ (quasithinG2 K)).Mod,
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ → βU u' = ψ g (βU u)) ∧
      (∀ g, ψ g ∈ (g2QAct K).range) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆,
        ψ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ ∧
        ((π γ : ↥(autOn L (vPlus L T))) : MulAut ↥(vPlus L T)) = conjAct (vPlus L T) ⟨ℓ, hLV hℓ⟩) ∧
      (∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∃ ℓ, ∃ hℓ : ℓ ∈ L,
        ψ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) := by
  have hφ : ∀ (n : ↥(Subgroup.normalizer (L : Set G))) (x : ↥(blockU L)),
      βU x = 1 ↔ βU (conjU L n x) = 1 := by
    intro n x
    rw [hβk, hβk, conjU_apply]
    have hnZ : ∀ (g : G), g ∈ Subgroup.normalizer (L : Set G) → ∀ z, z ∈ blockZ L →
        g * z * g⁻¹ ∈ blockZ L := by
      intro g hg z hz
      refine ⟨(Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hg) z).mp hz.1, ?_⟩
      show g * z * g⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : g⁻¹ * l * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hl'
      calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * l := by group
    constructor
    · exact hnZ n n.2 x
    · intro h1
      have h2 := hnZ (n : G)⁻¹ (Subgroup.inv_mem _ n.2) _ h1
      simpa [mul_assoc] using h2
  set ψ := inducedHom (conjU L) βU hβs hφ with hψdef
  have hψe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → βU u' = ψ g (βU u) := by
    intro g u u' hu'
    rw [hψdef, inducedHom_apply]
    congr 1
    exact Subtype.ext hu'
  have hψL : ∀ ℓ (hℓ : ℓ ∈ L), ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆,
      ψ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ ∧
      ((π γ : ↥(autOn L (vPlus L T))) : MulAut ↥(vPlus L T)) = conjAct (vPlus L T) ⟨ℓ, hLV hℓ⟩ := by
    intro ℓ hℓ
    have hmem : conjAct (vPlus L T) ⟨ℓ, hLV hℓ⟩ ∈ autOn L (vPlus L T) :=
      ⟨⟨ℓ, hLV hℓ⟩, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ ⟨_, hmem⟩
    have hγ' : ((π γ : ↥(autOn L (vPlus L T))) : MulAut ↥(vPlus L T)) =
        conjAct (vPlus L T) ⟨ℓ, hLV hℓ⟩ :=
      congrArg Subtype.val hγ
    refine ⟨γ, ?_, hγ'⟩
    ext m
    obtain ⟨u, rfl⟩ := hβs m
    have hu' : ℓ * (u : G) * ℓ⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hℓ))
        u).mp u.2
    rw [← hψe ⟨ℓ, Subgroup.le_normalizer hℓ⟩ u ⟨_, hu'⟩ rfl]
    refine hβe γ u ⟨_, hu'⟩ ?_
    rw [hγ']
    rfl
  have hψL' : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∃ ℓ, ∃ hℓ : ℓ ∈ L,
      ψ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ := by
    intro γ
    obtain ⟨⟨ℓ, hℓV⟩, hℓ', hc⟩ := Subgroup.mem_map.mp (π γ).2
    have hℓ : ℓ ∈ L := Subgroup.mem_subgroupOf.mp hℓ'
    refine ⟨ℓ, hℓ, ?_⟩
    ext m
    obtain ⟨u, rfl⟩ := hβs m
    have hu' : ℓ * (u : G) * ℓ⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hℓ))
        u).mp u.2
    rw [← hψe ⟨ℓ, Subgroup.le_normalizer hℓ⟩ u ⟨_, hu'⟩ rfl]
    refine hβe γ u ⟨_, hu'⟩ ?_
    rw [← hc]
    rfl
  have hmemL : ∀ h, h ∈ (g2Derived K).map (g2QAct K) ↔
      ∃ ℓ, ∃ hℓ : ℓ ∈ L, ψ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = h := by
    intro h
    rw [mem_map_g2Derived_iff]
    constructor
    · rintro ⟨γ, rfl⟩
      obtain ⟨ℓ, hℓ, e⟩ := hψL' γ
      exact ⟨ℓ, hℓ, e⟩
    · rintro ⟨ℓ, hℓ, rfl⟩
      obtain ⟨γ, e, -⟩ := hψL ℓ hℓ
      exact ⟨γ, e.symm⟩
  refine ⟨ψ, hψe, fun g => ?_, hψL, hψL'⟩
  refine (g2DerivedNormalizerZorn K hK).1 (ψ g) fun h => ?_
  rw [hmemL, hmemL]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    have hℓ' : (g : G) * ℓ * (g : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp g.2 ℓ).mp hℓ
    refine ⟨_, hℓ', ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  · rintro ⟨ℓ, hℓ, e⟩
    have hℓ' : (g : G)⁻¹ * ℓ * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2) ℓ).mp hℓ
      simpa using this
    refine ⟨_, hℓ', ?_⟩
    have e2 : (⟨(g : G)⁻¹ * ℓ * g, Subgroup.le_normalizer hℓ'⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = g⁻¹ * ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * g :=
      Subtype.ext rfl
    rw [e2, map_mul, map_mul, e, map_inv]
    group

end Psi

section Rho

variable {G : Type} [Group G]

theorem conjF2Hom_injective {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Function.Injective (conjF2Hom hK) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : conjF2 hK g.1 = 1 := congrArg Subtype.val hg
  apply Subtype.ext
  refine LinearEquiv.ext fun y => ?_
  have h2 := DFunLike.congr_fun h1 ((zornEquivK hK).symm y)
  rw [conjF2_apply, AddEquiv.apply_symm_apply] at h2
  have h3 := congrArg (zornEquivK hK) h2
  rw [AddEquiv.apply_symm_apply] at h3
  simpa using h3

theorem exists_rho₃ [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
      (β : ↥(blockU L) →* ModQ),
      Function.Surjective β ∧ (∀ u, β u = 1 ↔ (u : G) ∈ blockZ L) ∧
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u)) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2)) ∧
      (∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = 1 →
        ℓ ∈ Subgroup.centralizer (vPlus L T : Set G)) := by
  obtain ⟨hc, hreal⟩ := G2Blk.exists_g2Natural h38 h39 h51 h hTL hG2
  have hMp := Hyp331.mPlus_eq_of_le (L := L) (T := T) hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hG2.1 hTL
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (Hyp331.commutator_qL_le_blockU hG2.1 hTL)
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  obtain ⟨K, _, _, _, hK, π, βU, hπ, hβs, hβk, hβe⟩ := exists_coord hMp hUV hV4 hVL hreal
  obtain ⟨ψ, hψe, hψr, hψL, hψL'⟩ := exists_psi hUV hLV hK π βU hπ hβs hβk hβe
  set e := modQEquivK hK with he
  set ψ₂ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ModQ :=
    (MulAut.congr e.symm).toMonoidHom.comp ψ with hψ₂
  have hψ₂r : ∀ g, ψ₂ g ∈ (g2QAct (ZMod 2)).range := by
    intro g
    obtain ⟨γ, hγ⟩ := hψr g
    refine ⟨conjF2Hom hK γ, ?_⟩
    show g2QAct (ZMod 2) ⟨conjF2 hK γ.1, conjF2_mem hK γ.2⟩ = MulAut.congr e.symm (ψ g)
    rw [← hγ, he, congr_modQEquivK_symm]
  set ρ₃ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)) :=
    (MonoidHom.ofInjective g2QAct_injective).symm.toMonoidHom.comp
      (ψ₂.codRestrict _ hψ₂r) with hρ₃
  have hρ₃e : ∀ g, g2QAct (ZMod 2) (ρ₃ g) = ψ₂ g := by
    intro g
    have h1 := MonoidHom.ofInjective_apply g2QAct_injective (x := ρ₃ g)
    rw [hρ₃] at h1 ⊢
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hψ₂ψ : ∀ γ : ↥(quasithinG2 K), ∀ g, ψ g = g2QAct K γ → ρ₃ g = conjF2Hom hK γ := by
    intro γ g hg
    apply g2QAct_injective
    rw [hρ₃e]
    show MulAut.congr e.symm (ψ g) = g2QAct (ZMod 2) ⟨conjF2 hK γ.1, conjF2_mem hK γ.2⟩
    rw [hg, he, congr_modQEquivK_symm]
  refine ⟨ρ₃, e.symm.toMonoidHom.comp βU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs (e m)
    exact ⟨u, by simp [hu]⟩
  · intro u
    rw [← hβk u]
    simp
  · intro g u u' hu'
    rw [hρ₃e]
    show e.symm (βU u') = MulAut.congr e.symm (ψ g) (e.symm (βU u))
    rw [hψe g u u' hu', MulAut.congr_apply]
    simp
  · intro ℓ hℓ
    obtain ⟨γ, hγ, -⟩ := hψL ℓ hℓ
    rw [hψ₂ψ _ _ hγ, ← map_g2Derived_conjF2Hom hK]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr γ.2, rfl⟩
  · intro x hx
    rw [← map_g2Derived_conjF2Hom hK] at hx
    obtain ⟨γ', hγ', rfl⟩ := hx
    obtain ⟨ℓ, hℓ, hℓe⟩ := hψL' ⟨γ'.1, Subgroup.mem_subgroupOf.mp hγ'⟩
    exact ⟨ℓ, hℓ, hψ₂ψ _ _ hℓe⟩
  · intro ℓ hℓ h1
    obtain ⟨γ, hγ, hπγ⟩ := hψL ℓ hℓ
    have h2 := hψ₂ψ _ _ hγ
    rw [h1] at h2
    have h3 : (⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ : ↥(quasithinG2 K)) = 1 :=
      conjF2Hom_injective hK (h2.symm.trans (map_one _).symm)
    have h4 : γ = 1 := Subtype.ext (congrArg
      (fun x : ↥(quasithinG2 K) => (x : quasithinZorn K ≃ₗ[K] quasithinZorn K)) h3)
    rw [h4, map_one] at hπγ
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h5 := congrArg (fun a : MulAut ↥(vPlus L T) => ((a ⟨v, hv⟩ : ↥(vPlus L T)) : G)) hπγ
    simp only [OneMemClass.coe_one, MulAut.one_apply] at h5
    have h6 : ℓ * v * ℓ⁻¹ = v := h5.symm
    calc v * ℓ = ℓ * v * ℓ⁻¹ * ℓ := by rw [h6]
      _ = ℓ * v := by group

theorem mem_qL_of_rho [Finite G] {Γ : Type} [Group Γ] {L T : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T)
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = 1 → ∃ b : ℕ, ℓ ^ 2 ^ b = 1)
    {g : G} (hg : g ∈ L ⊔ T) (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (h1 : ρ ⟨g, hgN⟩ = 1) : g ∈ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  let ρ' : ↥(L ⊔ T) →* Γ := ρ.comp (Subgroup.inclusion hLTN)
  have hK2 : IsPGroup 2 ↥(ρ'.ker.map (L ⊔ T).subtype) := by
    rintro ⟨_, ⟨k', hk', rfl⟩⟩
    obtain ⟨ℓ, hℓ, t, ht, hkt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp k'.2
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hstep : ∀ n : ℕ, ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨ℓ', hℓ', e⟩ := ih
        refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) ℓ).mp hℓ
        · rw [pow_succ, e]
          group
    obtain ⟨ℓ', hℓ', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkL : (k' : G) ^ 2 ^ a ∈ L := by
      rw [hkt, e]
      exact hℓ'
    have h3 : ρ ⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ = 1 := by
      have e2 : (⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ :
          ↥(Subgroup.normalizer (L : Set G))) = (Subgroup.inclusion hLTN k') ^ 2 ^ a :=
        Subtype.ext (by simp)
      have hk1 : ρ (Subgroup.inclusion hLTN k') = 1 := hk'
      rw [e2, map_pow, hk1, one_pow]
    obtain ⟨b, hb⟩ := hρL _ hkL h3
    refine ⟨a + b, Subtype.ext ?_⟩
    show (k' : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact hb
  have hgK : g ∈ ρ'.ker.map (L ⊔ T).subtype := ⟨⟨g, hg⟩, h1, rfl⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _)
    (by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective]
      infer_instance) hK2 hgK

theorem exists_rho [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
      (β : ↥(blockU L) →* ModQ),
      Function.Surjective β ∧ (∀ u, β u = 1 ↔ (u : G) ∈ blockZ L) ∧
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u)) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2)) ∧
      (∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x) ∧
      (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sSubG) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
        g ∈ qL L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ₃, β₂, hβs, hβk, hβe, hρL, hρL', hρC⟩ := exists_rho₃ h38 h39 h51 h hTL hG2
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  obtain ⟨x, hx⟩ : ∃ x : ↥(quasithinG2 (ZMod 2)),
      ∀ t (ht : t ∈ T), x * ρ₃ ⟨t, hTL ht⟩ * x⁻¹ ∈ sSubG := by
    let f : ↥T →* ↥(quasithinG2 (ZMod 2)) := ρ₃.comp (Subgroup.inclusion hTL)
    have hf : IsPGroup 2 ↥f.range := hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨Q, hQ⟩ := hf.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) Q sylowSub
    refine ⟨g, fun t ht => ?_⟩
    have h1 : f ⟨t, ht⟩ ∈ (Q : Subgroup ↥(quasithinG2 (ZMod 2))) := hQ ⟨⟨t, ht⟩, rfl⟩
    have h2 : g * f ⟨t, ht⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 _) : Subgroup ↥(quasithinG2 (ZMod 2))) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hg, coe_sylowSub] at h2
    exact h2
  refine ⟨(MulAut.conj x).toMonoidHom.comp ρ₃,
    (g2QAct (ZMod 2) x).toMonoidHom.comp β₂, ?_, ?_, ?_, ?_, ?_, hx, ?_⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs ((g2QAct (ZMod 2) x).symm m)
    refine ⟨u, ?_⟩
    simp [hu]
  · intro u
    rw [← hβk u]
    simp
  · intro g u u' hu'
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, map_mul, map_inv, MulAut.mul_apply]
    rw [hβe g u u' hu', MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · intro ℓ hℓ
    have hn : (g2Derived (ZMod 2)).Normal := by
      rw [g2Derived_eq_commutator]
      infer_instance
    exact hn.conj_mem _ (hρL ℓ hℓ) x
  · intro y hy
    have hn : (g2Derived (ZMod 2)).Normal := by
      rw [g2Derived_eq_commutator]
      infer_instance
    have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ g2Derived (ZMod 2) := hn.conj_mem _ hy x⁻¹
    obtain ⟨ℓ, hℓ, e⟩ := hρL' _ hy'
    refine ⟨ℓ, hℓ, ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    rw [e]
    group
  · intro g hg hgN h1
    refine mem_qL_of_rho ρ₃ hTL hT2 (fun ℓ hℓ h2 => ?_) hg hgN ?_
    · have h3 := G2Blk.mem_pCore_of_mem_centralizer h38 h39 h hTL hG2 hℓ (hρC ℓ hℓ h2)
      obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h3⟩
      exact ⟨b, congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hb⟩
    · have h2 : (MulAut.conj x) (ρ₃ ⟨g, hgN⟩) = 1 := h1
      rw [MulAut.conj_apply] at h2
      have h3 := congrArg (fun y => x⁻¹ * y * x) h2
      simpa [mul_assoc] using h3

end Rho

end G2Rho

end CFSG.Quasithin.H13
