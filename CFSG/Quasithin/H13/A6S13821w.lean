module

public import CFSG.Quasithin.H13.A6S1372L76Of2
public import CFSG.Quasithin.Background.SmithD37Real
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Quasithin.H13.A6S13821u
public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Matrix

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem binaryNaturalSL_of_isoMod_v {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {θ : ↥H →* H6.Γ}
    (D : L32A.SecMod H (conjClosure S.V3 H) (fsuV1 T V) θ)
    [hN : ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).Normal] {K : Subgroup G}
    (hKH : K ≤ H) (hθK : (K.subgroupOf H).map θ = ⊤)
    {ρ : H6.Γ →* AddMonoid.End (Additive (↥(conjClosure S.V3 H) ⧸
      (fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hρ : ∀ (l : ↥H) (s : ↥(conjClosure S.V3 H)),
      ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
        Additive.ofMul (QuotientGroup.mk (D.conjX l s)))
    (h : H6.IsoMod ρ H6.ρV) :
    BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1 := by
  classical
  set spE := specialLinearGroupEquivStatedSL 3 (ZMod 2) with hspE
  obtain ⟨f, hf, hfe⟩ := h
  set fe : H6.V3 ≃+ Additive (↥(conjClosure S.V3 H) ⧸
    (fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := AddEquiv.ofBijective f hf with hfedef
  have hfe' : ∀ (g : H6.Γ) (m : Additive (↥(conjClosure S.V3 H) ⧸
      (fsuV1 T V).subgroupOf (conjClosure S.V3 H))), fe.symm (ρ g m) = g • fe.symm m := by
    intro g m
    apply fe.injective
    rw [AddEquiv.apply_symm_apply]
    show ρ g m = f (H6.ρV g (fe.symm m))
    rw [hfe]
    congr 1
    exact (fe.apply_symm_apply m).symm
  have he : ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).map
      (Subgroup.topEquiv.symm : ↥(conjClosure S.V3 H) ≃*
        ↥(⊤ : Subgroup ↥(conjClosure S.V3 H))).toMonoidHom =
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hy
    · intro hx
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  let ι : (↥(conjClosure S.V3 H) ⧸ (fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ≃*
      Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv.symm he
  have hι : ∀ s : ↥(conjClosure S.V3 H),
      ι.symm (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) s) =
        QuotientGroup.mk s := fun s => by
    rw [MulEquiv.symm_apply_eq]
    rfl
  let β : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ≃* Multiplicative H6.V3 :=
    ι.symm.trans (AddEquiv.toMultiplicativeRight fe.symm)
  have hβ : ∀ s : ↥(conjClosure S.V3 H),
      β (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) s) =
        Multiplicative.ofAdd (fe.symm (Additive.ofMul (QuotientGroup.mk s))) := fun s => by
    show AddEquiv.toMultiplicativeRight fe.symm
      (ι.symm (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) s)) = _
    rw [hι]
    rfl
  have hσ : ∀ (k : ↥H) (w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      β (L13825.sigmaH hH k w) = A6L76Of.natHom (spE (θ k)) (β w) := by
    intro k w
    obtain ⟨s, rfl⟩ :=
      InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) w
    have e1 : L13825.sigmaH hH k
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) s) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) (D.conjX k s) := by
      rw [A6Mod.secAct_secMk]
      congr 1
    rw [e1, hβ, hβ, ← hρ, hfe']
    apply Multiplicative.toAdd.injective
    rw [A6L76Of.natHom_apply, specialLinearGroupEquivStatedSL_coe]
    rfl
  let π₀ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) →*
      MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    { toFun := fun γ => (β.trans (A6L76Of.natHom γ)).trans β.symm
      map_one' := by
        ext w
        simp
      map_mul' := fun a b => by
        ext w
        simp [MulAut.mul_apply] }
  have hπ₀ : ∀ γ w, β (π₀ γ w) = A6L76Of.natHom γ (β w) := fun γ w =>
    β.apply_symm_apply _
  have hYK : autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) =
      (K.subgroupOf H).map (L13825.sigmaH hH) := L13825.autSec_eq_map hH hKH
  have hmem : ∀ k : ↥H, π₀ (spE (θ k)) = L13825.sigmaH hH k := fun k => by
    ext w
    apply β.injective
    rw [hπ₀, hσ]
  have hπmem : ∀ γ, π₀ γ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    intro γ
    rw [hYK]
    have hγ : spE.symm γ ∈ (K.subgroupOf H).map θ := by
      rw [hθK]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkθ⟩ := hγ
    refine ⟨k, hk, ?_⟩
    rw [← hmem k, hkθ, MulEquiv.apply_symm_apply]
  let π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) →*
      ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := π₀.codRestrict _ hπmem
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [hYK] at hy'
    obtain ⟨k, -, rfl⟩ := hy'
    exact ⟨spE (θ k), Subtype.ext (hmem k)⟩
  have hreal : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))).Realizes
      (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ :=
    SmithD37.realizes_of_mulEquiv _ rfl rfl (fun γ => G64.natAct_one_right γ) _ β π hπs
      (fun γ u => hπ₀ γ u)
  have hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have h1 : ∀ γ, A6L76Of.natHom γ (β w) = β w := fun γ => by
      rw [← hπ₀]
      congr 1
      exact hw _ (hπmem γ)
    exact β.injective ((A6L76Of.natHom_fixed h1).trans (map_one β).symm)
  have hcomm : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨g, u, hgu⟩ := A6S19.exists_sub_eq_v3 (Multiplicative.toAdd (β w))
    set w' := β.symm (Multiplicative.ofAdd u) with hw'
    have e : π₀ (spE g) w' * w'⁻¹ = w := by
      apply β.injective
      rw [map_mul, map_inv, hπ₀, hw', MulEquiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, A6L76Of.natHom_apply, specialLinearGroupEquivStatedSL_coe,
        toAdd_ofAdd, ← hgu, sub_eq_add_neg]
      rfl
    rw [← e]
    exact Subgroup.subset_closure ⟨π₀ (spE g), hπmem _, w', rfl⟩
  rw [hcomm, hfix, bot_inf_eq]
  exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], hreal⟩

variable (S)

theorem false_of_isoMod_v (h1376 : Lem1376Full) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {θ : ↥H →* H6.Γ}
    (D : L32A.SecMod H (conjClosure S.V3 H) (fsuV1 T V) θ)
    [hN : ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).Normal] {K : Subgroup G}
    (hK : K ∈ cComp H) (hθK : (K.subgroupOf H).map θ = ⊤)
    {ρ : H6.Γ →* AddMonoid.End (Additive (↥(conjClosure S.V3 H) ⧸
      (fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hρ : ∀ (l : ↥H) (s : ↥(conjClosure S.V3 H)),
      ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
        Additive.ofMul (QuotientGroup.mk (D.conjX l s)))
    (h : H6.IsoMod ρ H6.ρV) : False := by
  have hab := L13825.isElemAbelian_UH hS hH
  have hBN := binaryNaturalSL_of_isoMod_v hH D (le_of_mem_cComp hK) hθK hρ h
  obtain ⟨h34, -⟩ := (h1376 G T L V S hS.hNS hS.hNU H hH hab K hK).1 3 le_rfl hBN
  omega

end Setting4

end CFSG.Quasithin.H13.A6
