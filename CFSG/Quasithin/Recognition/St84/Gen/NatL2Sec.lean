module

import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannSec
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18Basic

public section

namespace CFSG.Quasithin.St84

open scoped MatrixGroups

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push CFSG.Quasithin.F53Mod

variable {G : Type} [Group G] [Finite G]

private theorem exists_z_not_mem_zZero {X P Z : Subgroup G} (h : PushHyp X P Z)
    (hnt : Nontrivial (oTwoQuot ↥X)) : ∃ z ∈ Z, z ∉ zZero X Z := by
  by_contra hcon
  push Not at hcon
  have hZc : Z ≤ Subgroup.centralizer (pResidualOf 2 X : Set G) := fun z hz =>
    (Subgroup.mem_inf.mp (hcon z hz)).2
  have hOle : pResidualOf 2 X ≤ pCoreOf 2 X := by
    rw [← h.cent_eq]
    refine le_inf (pResidualOf_le_self X) ?_
    intro l hl
    exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZc hz) l hl).symm
  have hXS : X ≤ P := by
    rw [← pResidualOf_sup_eq_of_sylow h.sylow]
    exact sup_le (hOle.trans h.core_le) le_rfl
  have hPS : P = X := le_antisymm h.le_self hXS
  have hpX : IsPGroup 2 X := hPS ▸ h.sylow.2.1
  have hp2 : IsPGroup 2 (⊤ : Subgroup ↥X) := hpX.of_equiv Subgroup.topEquiv.symm
  have htopcore : CFSG.pCore 2 ↥X = ⊤ := by
    refine top_le_iff.mp ?_
    exact CFSG.LieType.BorelTits.le_pCore (r := 2) (G := ↥X) (N := ⊤)
      (inferInstance : (⊤ : Subgroup ↥X).Normal) hp2
  have hsub : Subsingleton (oTwoQuot ↥X) := by
    show Subsingleton (↥X ⧸ CFSG.pCore 2 ↥X)
    rw [htopcore]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨a, b, hab⟩ := hnt
  exact hab (Subsingleton.elim a b)

theorem exists_natCoord_of_pushHyp
    (hmod : ∀ {n : ℕ}, 2 ≤ n → ∀ {F : Type} [Field F] [Fintype F], Fintype.card F = 2 ^ n →
      ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
        (ρ : Representation (ZMod 2) SL(2, F) W), (∀ w : W, (∀ g, ρ g w = w) → w = 0) →
        ∀ (A : Subgroup SL(2, F)) [CFSG.IsElementaryAbelian 2 A], A ≠ ⊥ →
        Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} →
        ρ.IsIrreducible ∧ Nat.card A = 2 ^ n ∧
          ∃ φ : W ≃+ (Fin 2 → F), ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w))
    {X P Z : Subgroup G} (h : PushHyp X P Z) {n : ℕ} (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥X)) (hJ : ¬ thompsonJ P ≤ pCoreOf 2 X) :
    ∃ (α : ↥X →* SL(2, GaloisField 2 n))
      (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → GaloisField 2 n)),
      Function.Surjective α ∧
      α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X) ∧
      Function.Surjective β ∧
      (∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
        Multiplicative.toAdd (β v') =
          (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd (β v))) ∧
      β.ker = (Subgroup.centralizer
        ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
          (Z.subgroupOf X) := by
  classical
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  obtain ⟨e⟩ := hq
  have hntQ : Nontrivial (oTwoQuot ↥X) := by
    have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4).toNontrivial
    exact e.toEquiv.nontrivial
  let e2 : OTwoQuot X ≃* SL(2, GaloisField 2 n) :=
    e.trans (CFSG.Quasithin.pslTwoGf2EquivSl n)
  obtain ⟨α, hαs, hαk⟩ := exists_hom_of_quot (X := X) e2
  have hαker : α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    ext x
    rw [MonoidHom.mem_ker, hαk x, mem_centralizer_subgroupOf_iff hZX x]
    constructor
    · intro hx
      rw [← h.cent_eq] at hx
      exact (Subgroup.mem_inf.mp hx).2
    · intro hx
      rw [← h.cent_eq, Subgroup.mem_inf]
      exact ⟨x.2, hx⟩
  let hs : IsSec X (zZero X Z) Z := isSec_zZero h
  have hsq : ∀ w : hs.W, w ^ 2 = 1 := fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_pow, hs.proj_eq_one_iff]
    simpa using hs.sq x x.2
  have hfinW : Finite hs.W := by
    have := hs.normal_subgroupOf
    exact (inferInstance : Finite (↥Z ⧸ (zZero X Z).subgroupOf Z))
  haveI : Finite hs.W := hfinW
  haveI : Finite (Additive hs.W) := hfinW
  have hWnt : Nontrivial hs.W := by
    obtain ⟨z, hz, hz0⟩ := exists_z_not_mem_zZero h hntQ
    exact ⟨1, hs.proj ⟨z, hz⟩, fun h1 => hz0 ((hs.proj_eq_one_iff ⟨z, hz⟩).mp h1.symm)⟩
  haveI : Nontrivial (Additive hs.W) := by
    obtain ⟨a, b, hab⟩ := hWnt
    exact ⟨Additive.ofMul a, Additive.ofMul b, fun h => hab (Additive.ofMul.injective h)⟩
  letI : Module (ZMod 2) (Additive hs.W) := CFSG.Quasithin.H13.zmod2ModuleOfExp hsq
  have hkerσ : α.ker ≤ hs.conjHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine hs.conjHom_eq_one fun z hz => ?_
    have hxQ : (x : G) ∈ pCoreOf 2 X := (hαk x).mp hx
    have hcomm : (x : G) * z = z * (x : G) := (h.core_le_centralizer hxQ z hz).symm
    have h1 : (x : G) * z * (x : G)⁻¹ * z⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact (zZero X Z).one_mem
  let σ : SL(2, GaloisField 2 n) →* MulAut hs.W :=
    MonoidHom.liftOfRightInverse α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨hs.conjHom, hkerσ⟩
  have hσ : ∀ x : ↥X, σ (α x) = hs.conjHom x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨hs.conjHom, hkerσ⟩ x
  let ρ : Representation (ZMod 2) SL(2, GaloisField 2 n) (Additive hs.W) :=
    { toFun := fun g => CFSG.Quasithin.H13.linAutHom (σ g)
      map_one' := by
        show CFSG.Quasithin.H13.linAutHom (σ 1) = 1
        rw [map_one σ, map_one CFSG.Quasithin.H13.linAutHom]
      map_mul' := by
        intro g h'
        show CFSG.Quasithin.H13.linAutHom (σ (g * h')) =
          CFSG.Quasithin.H13.linAutHom (σ g) * CFSG.Quasithin.H13.linAutHom (σ h')
        rw [map_mul σ, map_mul CFSG.Quasithin.H13.linAutHom] }
  have hρ_apply : ∀ (g : SL(2, GaloisField 2 n)) (v : hs.W),
      ρ g (Additive.ofMul v) = Additive.ofMul (σ g v) :=
    fun g v => CFSG.Quasithin.H13.autLin_apply (σ g) v
  have hρ_toMul : ∀ (g : SL(2, GaloisField 2 n)) (v : hs.W),
      Additive.toMul (ρ g (Additive.ofMul v)) = σ g v := by
    intro g v
    change Additive.toMul
      (CFSG.Quasithin.H13.autLin (σ g) (Additive.ofMul v)) = σ g v
    rw [CFSG.Quasithin.H13.autLin_apply (σ g) v]
    rfl
  have hfix : ∀ w : Additive hs.W, (∀ g, ρ g w = w) → w = 0 := by
    intro w hw
    have hwv : ∀ x : ↥X, hs.conjHom x (Additive.toMul w) = Additive.toMul w := by
      intro x
      have h2 := congrArg Additive.toMul (hw (α x))
      rw [show w = Additive.ofMul (Additive.toMul w) from rfl] at h2
      rw [hρ_toMul (α x) (Additive.toMul w), hσ x] at h2
      exact h2
    obtain ⟨z, hzv⟩ := hs.proj_surjective (Additive.toMul w)
    have hzmem : (z : G) ∈ zZero X Z := by
      rw [zZero_eq]
      refine mem_inf_centralizer_oTwoRes_of_forall h.elemAbelian z.2 ?_
      intro x hx
      have hconj : hs.conjHom ⟨x, hx⟩ (hs.proj z) = hs.proj z := by
        rw [hzv]
        exact hwv ⟨x, hx⟩
      have h1 : hs.proj z = hs.proj (hs.conjN ⟨x, hx⟩ z) := by
        rw [← IsSec.conjHom_mk]
        exact hconj.symm
      simpa [zZero_eq, IsSec.conjN] using
        (hs.proj_eq_proj_iff z (hs.conjN ⟨x, hx⟩ z)).mp h1
    have hz1 : hs.proj z = 1 := (hs.proj_eq_one_iff z).mpr hzmem
    have hmain : Additive.ofMul (Additive.toMul w) = 0 := by
      rw [← hzv, hz1]
      rfl
    exact hmain
  obtain ⟨A, hA, hAQ⟩ := exists_offender (S := P) (Q := pCoreOf 2 X) hJ
  have hAX : A ≤ X := hA.1.trans h.le_self
  let B : Subgroup SL(2, GaloisField 2 n) := (A.subgroupOf X).map α
  have hB : B = (A.subgroupOf X).map α := rfl
  have hBcard : Nat.card B = (A ⊓ pCoreOf 2 X).relIndex A := by
    rw [hB, ← Subgroup.relIndex_ker (A.subgroupOf X) α]
    have hker : α.ker = (pCoreOf 2 X).comap X.subtype := by
      ext x
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, hαk x]
      rfl
    rw [hker, Subgroup.relIndex_comap (H := pCoreOf 2 X) X.subtype (A.subgroupOf X),
      Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.inf_relIndex_left]
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hAQ
    intro y hy
    have hmem : α ⟨y, hAX hy⟩ ∈ B := by
      rw [hB]
      exact ⟨⟨y, hAX hy⟩, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hαk ⟨y, hAX hy⟩).mp hmem
  have hAe : CFSG.Open.IsElemAbelian 2 A := hA.2.1
  haveI hBelem : CFSG.IsElementaryAbelian 2 B :=
    CFSG.IsElementaryAbelian.subgroup_map
      (CFSG.Open.IsElemAbelian.subgroupOf hAe X).isElementaryAbelian α
  let Fix : Subgroup hs.W :=
    { carrier := {w | ∀ b ∈ B, ρ b (Additive.ofMul w) = Additive.ofMul w}
      one_mem' := by
        intro b _
        change ρ b 0 = 0
        exact map_zero _
      mul_mem' := by
        intro a b ha hb c hc
        change ρ c (Additive.ofMul a + Additive.ofMul b) =
          Additive.ofMul a + Additive.ofMul b
        rw [map_add, ha c hc, hb c hc]
      inv_mem' := by
        intro a ha c hc
        change ρ c (-Additive.ofMul a) = -Additive.ofMul a
        rw [map_neg, ha c hc] }
  have hfixcard : Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} = Nat.card ↥Fix :=
    Nat.card_congr
      { toFun := fun w => ⟨Additive.toMul w.1, w.2⟩
        invFun := fun w => ⟨Additive.ofMul w.1, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hFixindex : Fix.index ≤ Nat.card B := by
    rw [hBcard]
    let Pm : Subgroup ↥Z := (Z ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Z
    have hPle : Pm.map hs.proj ≤ Fix := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := hw
      show ∀ b ∈ B, ρ b (Additive.ofMul (hs.proj x)) = Additive.ofMul (hs.proj x)
      intro b hb
      obtain ⟨y, hyA, rfl⟩ := hb
      have hconj : hs.conjN y x = x := by
        apply Subtype.ext
        show (y : G) * (x : G) * (y : G)⁻¹ = (x : G)
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y
          (Subgroup.mem_subgroupOf.mp hyA)
      calc ρ (α y) (Additive.ofMul (hs.proj x))
          = Additive.ofMul (σ (α y) (hs.proj x)) := hρ_apply (α y) (hs.proj x)
        _ = Additive.ofMul (hs.conjHom y (hs.proj x)) := by rw [hσ y]
        _ = Additive.ofMul (hs.proj (hs.conjN y x)) := by rw [IsSec.conjHom_mk]
        _ = Additive.ofMul (hs.proj x) := by rw [hconj]
    have h1 := Subgroup.index_dvd_of_le hPle
    have h2 : (Pm.map hs.proj).index ∣ Pm.index :=
      Subgroup.index_map_dvd (H := Pm) hs.proj_surjective
    have hpos : 0 < Pm.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    calc Fix.index ≤ Pm.index := Nat.le_of_dvd hpos (h1.trans h2)
      _ = (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := rfl
      _ ≤ (A ⊓ pCoreOf 2 X).relIndex A := offender_count h hA
  have hoff : Nat.card (Additive hs.W) ≤
      Nat.card B * Nat.card {w : Additive hs.W // ∀ a ∈ B, ρ a w = w} := by
    rw [hfixcard]
    calc Nat.card (Additive hs.W) = Fix.index * Nat.card ↥Fix := Fix.index_mul_card.symm
      _ ≤ Nat.card B * Nat.card ↥Fix := Nat.mul_le_mul_right _ hFixindex
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  obtain ⟨-, -, φ, hφ⟩ :=
    hmod (n := n) hn (F := GaloisField 2 n) (by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)])
      (W := Additive hs.W) ρ hfix B hBne hoff
  let eφ : hs.W ≃* Multiplicative (Fin 2 → GaloisField 2 n) :=
    { toFun := fun w => Multiplicative.ofAdd (φ (Additive.ofMul w))
      invFun := fun x => Additive.toMul (φ.symm (Multiplicative.toAdd x))
      left_inv := by
        intro w
        simp
      right_inv := by
        intro x
        simp
      map_mul' := by
        intro a b
        show Multiplicative.ofAdd (φ (Additive.ofMul (a * b))) =
          Multiplicative.ofAdd (φ (Additive.ofMul a)) *
            Multiplicative.ofAdd (φ (Additive.ofMul b))
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
          map_add]
        rfl }
  let β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    eφ.toMonoidHom.comp (hs.proj.comp (Subgroup.subgroupOfEquivOfLe hZX).toMonoidHom)
  have hβv : ∀ v : ↥(Z.subgroupOf X),
      β v = eφ (hs.proj (Subgroup.subgroupOfEquivOfLe hZX v)) := fun _ => rfl
  have hβs : Function.Surjective β := by
    intro y
    obtain ⟨w, rfl⟩ := eφ.surjective y
    obtain ⟨z, rfl⟩ := hs.proj_surjective w
    obtain ⟨v, rfl⟩ := (Subgroup.subgroupOfEquivOfLe hZX).surjective z
    exact ⟨v, rfl⟩
  have hβe : ∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
      Multiplicative.toAdd (β v') =
        (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (β v)) := by
    intro x v v' hv'
    set z : ↥Z := Subgroup.subgroupOfEquivOfLe hZX v with hz
    set z' : ↥Z := Subgroup.subgroupOfEquivOfLe hZX v' with hz'
    have hzconj : z' = hs.conjN x z := by
      apply Subtype.ext
      have h3 := congrArg (fun y : ↥X => (y : G)) hv'
      show (z' : G) = (x : G) * (z : G) * (x : G)⁻¹
      rw [show (z' : G) = ((v' : ↥X) : G) from rfl,
        show (z : G) = ((v : ↥X) : G) from rfl, h3]
      rfl
    calc Multiplicative.toAdd (β v')
        = φ (Additive.ofMul (hs.proj z')) := rfl
      _ = φ (Additive.ofMul (hs.proj (hs.conjN x z))) := by rw [hzconj]
      _ = φ (ρ (α x) (Additive.ofMul (hs.proj z))) := by
          rw [hρ_apply (α x) (hs.proj z), hσ x, IsSec.conjHom_mk]
      _ = (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (φ (Additive.ofMul (hs.proj z))) := hφ (α x) _
      _ = (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd (β v)) := rfl
  have hβk : β.ker = (Subgroup.centralizer
      ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
        (Z.subgroupOf X) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_oddOrder_iff]
    rw [hβv v, MulEquiv.map_eq_one_iff, hs.proj_eq_one_iff]
    constructor
    · intro hv
      exact hv.2
    · intro hv
      exact ⟨Subgroup.mem_subgroupOf.mp v.2, hv⟩
  exact ⟨α, β, hαs, hαker, hβs, hβe, hβk⟩

end CFSG.Quasithin.St84
