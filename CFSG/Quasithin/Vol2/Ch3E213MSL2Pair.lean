module

public import CFSG.Quasithin.H13.QRCBenderSection

public section

namespace CFSG.Quasithin.Ch3E213M.SL2Pair

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.Quasithin.H13.QRC CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL projUpperTriangular)
open scoped MatrixGroups

@[expose] def Pair {H : Type} [Group H] (T : Sylow 2 H) (M V : Subgroup H) : Prop :=
  ∃ (m : ℕ) (g : H), 2 ≤ m ∧ g ∈ V ⊔ conjugate V g ∧ V < V ⊔ conjugate V g ∧
    IsSylowOf 2 ((T : Subgroup H) ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) ∧
    (V ⊔ conjugate V g) ⊓ normalizer (V : Set H) ≤ M ⊓ (V ⊔ conjugate V g) ∧
    inSubgroup (pCore 2) (M ⊓ (V ⊔ conjugate V g)) = (T : Subgroup H) ⊓ (V ⊔ conjugate V g) ∧
    kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) =
      inSubgroup (pCore 2) (V ⊔ conjugate V g) ∧
    IsCharacteristicP 2 ↥(V ⊔ conjugate V g) ∧
    ∃ (L : Subgroup (H ⧸ kerIn M ⊤)) (ψ : ↥(V ⊔ conjugate V g) →* L),
      Function.Surjective ψ ∧
      ψ.ker = (kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g)).subgroupOf
        (V ⊔ conjugate V g) ∧
      ∃ (k' : Type) (_ : Field k'), Nat.card k' = 2 ^ m ∧ ∃ e : L ≃* projectiveSL 2 k',
        ((M ⊓ (V ⊔ conjugate V g)).subgroupOf (V ⊔ conjugate V g)).map (e.toMonoidHom.comp ψ) =
          projUpperTriangular 2 k'

theorem eq_bot_of_normal_of_benderData {G : Type*} [Group G] [Finite G] {U P : Subgroup G}
    {n : ℕ} (hD : BenderData G U n) [hPn : P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hP1
  have hPU : P ≤ U := by
    have h := (hD.isPGroup.toSylow hD.not_dvd_index).is_maximal'
      (hP.to_sup_of_normal_left hD.isPGroup) le_sup_right
    exact le_sup_left.trans h.le
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hD.stronglyEmbedded.1)
  refine hx (mem_of_le_inf_conjugate hD.stronglyEmbedded hP hP1 fun p hp =>
    ⟨le_normalizer (hPU hp), mem_conjugate_iff.2 ?_⟩)
  exact le_normalizer (hPU (hPn.conj_mem p hp x))

variable {H : Type} [Group H] [Finite H]

theorem qrc_pair_of_sl2
    (hns : ¬ Group.IsSolvable H) (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V) {k₀ : Type} [Field k₀] [Finite k₀] {n : ℕ}
    (hk₀ : Nat.card k₀ = 2 ^ n) (φ : SL(2, k₀) →* H ⧸ kerIn M ⊤) (hφinj : Function.Injective φ)
    (hφK : ∀ g, φ g ∈ (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))
    (hφS : ∀ g, φ g ∈ (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ↔
      g ∈ sl2UpperUnipotentSubgroup k₀)
    (hφB : ∀ g ∈ sl2Borel k₀, φ g ∈ M.map (QuotientGroup.mk' (kerIn M ⊤)))
    (hEφ : V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ (sl2UpperUnipotentSubgroup k₀).map φ) :
    Pair T M V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hDK₀, -, -, -, -, -, hEcard, hEO⟩ :=
    bender_section_setup hns T hTn hTM hMH hmax hVT hVM
  set D := kerIn M ⊤ with hDdef
  set π := QuotientGroup.mk' D with hπdef
  set S := (T : Subgroup H).map π with hSdef
  set B := M.map π with hBdef
  set E := V.map π with hEdef
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ
  have hEel : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
  have hES : E ≤ S := map_mono hVT
  have : CharP k₀ 2 := CFSG.ShultStronglyClosedTI.LinearModel.charP_two_of_card hk₀
  have hD₀ := benderData_sl2 hk₀
  have hco : IsCoatom (sl2Borel k₀) := sl2_normalizer_upperUnipotent (k := k₀) ▸ hD₀.isCoatom
  have hR2 : IsPGroup 2 (inSubgroup (pCore 2) B) := (pCore_isPGroup (p := 2) (G := B)).map _
  have hRn : B ≤ normalizer (inSubgroup (pCore 2) B : Set (H ⧸ D)) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic B (pCore 2 B))
  have hφB' : ∀ g, φ g ∈ B ↔ g ∈ sl2Borel k₀ := by
    refine fun g => ⟨fun hg => ?_, hφB g⟩
    by_contra hgB
    have htop : B.comap φ = ⊤ :=
      (hco.le_iff.mp fun x hx => hφB x hx).resolve_right fun h => hgB (h ▸ hg)
    have hPn : ((inSubgroup (pCore 2) B).comap φ).Normal := ⟨fun p hp h => by
      change φ (h * p * h⁻¹) ∈ inSubgroup (pCore 2) B
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (hRn (htop ▸ mem_top h : h ∈ B.comap φ)) _).1 hp⟩
    obtain ⟨e, he, he1⟩ := E.bot_or_exists_ne_one.resolve_left fun h => by
      rw [h, card_bot] at hE4
      omega
    obtain ⟨u, -, rfl⟩ := hEφ he
    have hu : u ∈ (inSubgroup (pCore 2) B).comap φ := hEO he
    rw [eq_bot_of_normal_of_benderData hD₀ (hR2.comap_of_injective φ hφinj), mem_bot] at hu
    exact he1 (by rw [hu, map_one])
  set R := φ.range with hRdef
  set θR : SL(2, k₀) ≃* R := MonoidHom.ofInjective hφinj with hθRdef
  have hθRapp : ∀ g, ((θR g : R) : H ⧸ D) = φ g := fun g => MonoidHom.ofInjective_apply hφinj
  have hRK : R ≤ (oddResidualPreimage H).map π := by
    rintro _ ⟨g, rfl⟩
    exact hφK g
  set U_R := (sl2UpperUnipotentSubgroup k₀).map θR.toMonoidHom with hURdef
  have hθRmem : ∀ (X : Subgroup SL(2, k₀)) (x : R), x ∈ X.map θR.toMonoidHom ↔ θR.symm x ∈ X :=
    fun X x => mem_map_equiv
  have hxφ : ∀ x : R, (x : H ⧸ D) = φ (θR.symm x) := fun x => by
    rw [← hθRapp, θR.apply_symm_apply]
  have hU_R : U_R = (S ⊓ R).subgroupOf R := by
    ext x
    rw [hθRmem, mem_subgroupOf, ← hφS, ← hxφ]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hD : BenderData R U_R n := hD₀.map θR
  have hBR : B ⊓ R = (normalizer (U_R : Set R)).map R.subtype := by
    rw [hURdef, ← map_equiv_normalizer_eq, sl2_normalizer_upperUnipotent]
    ext x
    constructor
    · rintro ⟨hxB, g, rfl⟩
      refine ⟨θR g, (hθRmem _ _).2 ?_, hθRapp g⟩
      rw [θR.symm_apply_apply]
      exact (hφB' g).1 hxB
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, y.2⟩
      change (y : H ⧸ D) ∈ B
      rw [hxφ]
      exact (hφB' _).2 ((hθRmem _ _).1 hy)
  have hER : E ≤ R := hEφ.trans (map_le_range _ _)
  have hESR : E ≤ S ⊓ R := le_inf hES hER
  obtain ⟨x, hxN, -, hxL, hLeq, hLR, hSF, hcore, hO2, hO2P, hBL, -⟩ :=
    bender_pair_in_quotient hU_R hD hBR hESR hE4
  have hab : ∀ u ∈ U_R, ∀ v ∈ U_R, u * v = v * u := by
    intro u hu v hv
    rw [hθRmem, mem_sl2UpperUnipotentSubgroup_iff] at hu hv
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    apply θR.symm.injective
    rw [map_mul, map_mul, ha, hb, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
  have : IsElementaryAbelian 2 (E.subgroupOf R) := IsElementaryAbelian.subgroupOf hER
  have hE'U : E.subgroupOf R ≤ U_R := by
    rw [hU_R]
    exact fun y hy => hESR hy
  have hE'4 : 4 ≤ Nat.card (E.subgroupOf R) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv]
  have hmodel := bender_pair_linear hD hab hE'U hE'4 hxN
  generalize hL'def : E.subgroupOf R ⊔ conjugate (E.subgroupOf R) x = L' at *
  obtain ⟨f, hf, -, -, e₁, he₁B, -⟩ := hmodel
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨g, -, hgI, -, hVI, -, -, -, -, -, -, -, -, hTIsyl, hNV, hO2MI, hJO, -, -, -, hcharI, ψ,
    hψs, hψker, -, hψM, -⟩ :=
    bender_lift hchar T hTn hTM hMH hmax hVT hTV hVM hVQ hDK₀ (L := L'.map R.subtype)
      (x := (x : H ⧸ D)) hxL hLeq (hLR.trans hRK) (Or.inl ⟨f, GaloisField 2 f, inferInstance, hf,
        hcardF, ⟨(L'.equivMapOfInjective R.subtype R.subtype_injective).symm.trans e₁⟩⟩)
      hSF hcore hO2 hO2P
  refine ⟨f, g, hf, hgI, hVI, hTIsyl, hNV, hO2MI, hJO, hcharI, L'.map R.subtype, ψ, hψs, hψker,
    GaloisField 2 f, inferInstance, hcardF,
    ((L'.equivMapOfInjective R.subtype R.subtype_injective).symm.trans e₁).trans
      (p2PSLEquiv _).symm, ?_⟩
  rw [← map_map, hψM, hBL, map_mulEquiv_trans, map_mulEquiv_trans,
    map_subgroupOf_equivMapOfInjective, he₁B]
  exact map_symm_eq_of_map_eq _ map_p2Equiv_projUpperTriangular

end CFSG.Quasithin.Ch3E213M.SL2Pair
