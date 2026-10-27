module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinBase

public section

namespace CFSG.Quasithin.F6.PushS3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Transport

variable {G : Type*} [Group G] {S P V : Subgroup G}

theorem charTwo_top_of_charTwo (hP : CharTwo P) : CharTwo (⊤ : Subgroup ↥P) := by
  intro x hx
  rw [CFSG.Quasithin.B6.pCoreOf_top] at hx ⊢
  have hxc : (x : G) ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hx.2 q hq
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := hP ⟨x.2, hxc⟩
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

theorem noCharNormal_top_of (hSP : S ≤ P) (hno : NoCharNormal S P) :
    NoCharNormal (S.subgroupOf P) (⊤ : Subgroup ↥P) := by
  intro C' hC'R hC'ne hC'char hn
  set C : Subgroup G := C'.map P.subtype with hC
  have hCR : C ≤ S := by
    have := Subgroup.map_mono (f := P.subtype) hC'R
    rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this
  have hCP : C ≤ P := hCR.trans hSP
  have hCne : C ≠ ⊥ := by
    intro hb
    exact hC'ne ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hb)
  have hCsub : C.subgroupOf P = C' := Subgroup.comap_map_eq_self_of_injective P.subtype_injective C'
  have hchar : (C.subgroupOf S).Characteristic := by
    let e : ↥(S.subgroupOf P) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSP
    have h1 := characteristic_map_mulEquiv e hC'char
    have h2 : (C'.subgroupOf (S.subgroupOf P)).map e.toMonoidHom = C.subgroupOf S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : ↥P) ∈ C' := hy
        exact ⟨y, hy', rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨⟨x, hSP x.2⟩, ?_⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr x.2
        · show (⟨(x : G), hSP x.2⟩ : ↥P) ∈ C'
          have : (⟨(x : G), hSP x.2⟩ : ↥P) = y := Subtype.ext hyx.symm
          rw [this]
          exact hy
        · rfl
    rw [← h2]
    exact h1
  have hnor : C'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hn)
  refine hno C hCR hCne hchar ?_
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hCP, hCsub]
  exact hnor

theorem isTwoReducedIn_top_of (hV : IsTwoReducedIn P V) :
    IsTwoReducedIn (⊤ : Subgroup ↥P) (V.subgroupOf P) := by
  have hVP : V ≤ P := hV.1
  have hVn : (V.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hV.2.1
  refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), ?_, ?_⟩
  · have hel := hV.2.2.1
    have := hel.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
    · have := hel.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  · intro D' _ hDn hDpow
    have hDnormal : D'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDn)
    have hD₀P : D'.map P.subtype ≤ P := BlueprintB2.map_subtype_le_self D'
    have hD₀N : P ≤ Subgroup.normalizer ((D'.map P.subtype : Subgroup G) : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hD₀P,
        BlueprintB2.subgroupOf_map_subtype_self]
      exact hDnormal
    have hres := hV.2.2.2 (D'.map P.subtype) hD₀P hD₀N (by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hDpow d hd
      refine ⟨k, ?_⟩
      have := (BlueprintB2.mem_centralizer_subgroupOf_iff hVP (d ^ 2 ^ k)).mp hk
      simpa using this)
    intro d hd
    exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVP d).mpr (hres ⟨d, hd, rfl⟩)

end Transport

section Setting

variable {G : Type*} [Group G] {k : Type*} [Field k]

theorem slPerm_apply_mulVec' (A : Matrix.SpecialLinearGroup (Fin 2) k) (w : Fin 2 → k) :
    slPerm k A w = (A : Matrix (Fin 2) (Fin 2) k).mulVec w := by
  rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  rfl

theorem natQuotSetting_of_module {S P M W : Subgroup G} (hSyl : IsSylowTwoOf S P)
    (hnn : ¬ (S.subgroupOf P).Normal) (hSM : S ≤ M) (hMP : ¬ P ≤ M)
    (hmax : ∀ Y : Subgroup G, S ≤ Y → Y < P → Y ≤ M)
    (hred : IsTwoReducedIn P W) (ϱ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) k)
    (hϱ : Function.Surjective ϱ) (ψ : ↥W →* Multiplicative (Fin 2 → k))
    (hψ : Function.Surjective ψ)
    (hψϱ : ∀ (p : ↥P) (v v' : ↥W), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ϱ p : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf W) :
    ∃ (ϱ' : ↥P →* Gamma k) (φ : ↥(W.subgroupOf P) →* Multiplicative (Fin 2 → k)),
      IsNatQuotSetting (S.subgroupOf P) (M.subgroupOf P) (W.subgroupOf P) ϱ' φ := by
  classical
  have hSP : S ≤ P := hSyl.1
  have hVP : W ≤ P := hred.1
  let ρ' : ↥P →* Gamma k :=
    ((slGamma k).subtype.comp (slGammaEquiv k).toMonoidHom).comp ϱ
  have hρ'apply : ∀ p : ↥P, ((ρ' p : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k (ϱ p) :=
    fun p => rfl
  let e : ↥(W.subgroupOf P) ≃* ↥W := Subgroup.subgroupOfEquivOfLe hVP
  let φ : ↥(W.subgroupOf P) →* Multiplicative (Fin 2 → k) := ψ.comp e.toMonoidHom
  refine ⟨ρ', φ, ?_⟩
  refine
    { sylow := Layer.isSylowTwoOf_subgroupOf_top' hSyl
      nonnormal := fun hn => hnn hn
      le_M := fun x hx => Subgroup.mem_subgroupOf.mpr (hSM (Subgroup.mem_subgroupOf.mp hx))
      M_lt := ?_
      M_max := ?_
      reduced := isTwoReducedIn_top_of hred
      sl_le := ?_
      two_quot := ?_
      φ_surj := hψ.comp e.surjective
      φ_equiv := ?_
      φ_ker := ?_ }
  · refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hPK : P ≤ M := fun x hx =>
      Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥P) ∈ M.subgroupOf P by rw [htop]; trivial)
    exact hMP hPK
  · intro Y hRY hY
    have hRY' : S ≤ Y.map P.subtype := by
      have := Subgroup.map_mono (f := P.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this
    have hYP : Y.map P.subtype < P := by
      refine lt_of_le_of_ne (map_subtype_le_self Y) fun heq => ?_
      apply (lt_top_iff_ne_top.mp hY)
      refine top_unique fun x _ => ?_
      have hx : (x : G) ∈ Y.map P.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hmax _ hRY' hYP ⟨y, hy, rfl⟩)
  · intro A
    obtain ⟨p, hp⟩ := hϱ A
    exact ⟨p, by rw [hρ'apply, hp]⟩
  · intro p
    exact ⟨0, by rw [pow_zero, pow_one]; exact (slGammaEquiv k (ϱ p)).2⟩
  · intro p v v' hv'
    have h1 := hψϱ p (e v) (e v') (by exact congrArg Subtype.val hv')
    rw [hρ'apply, slPerm_apply_mulVec']
    exact h1
  · ext v
    have hL : (oddOrderSubgroup (⊤ : Subgroup ↥P)) = (oddOrderSubgroup P).subgroupOf P := by
      rw [← oddOrderSubgroup_top_map P]
      exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
    rw [hL, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : e v ∈ ψ.ker := hv
      rw [hψker, Subgroup.mem_subgroupOf] at h1
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mpr h1
    · intro hv
      show e v ∈ ψ.ker
      rw [hψker, Subgroup.mem_subgroupOf]
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mp hv

end Setting

end CFSG.Quasithin.F6.PushS3
