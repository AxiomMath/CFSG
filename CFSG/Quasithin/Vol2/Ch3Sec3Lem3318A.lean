module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix
open scoped IsMulCommutative

section VecAct

variable {n : ℕ} {K : Type} [Field K]

@[expose] def vecAct (k : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    (Fin k → Multiplicative (Fin n → K)) →* (Fin k → Multiplicative (Fin n → K)) where
  toFun c i := Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd (c i))
  map_one' := by
    funext i
    simp
  map_mul' c d := by
    funext i
    simp [Matrix.mulVec_add]

theorem vecAct_apply (k : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (c : Fin k → Multiplicative (Fin n → K)) (i : Fin k) :
    vecAct k A c i = Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd (c i)) := rfl

theorem vecAct_mul (k : ℕ) (A B : Matrix (Fin n) (Fin n) K)
    (c : Fin k → Multiplicative (Fin n → K)) :
    vecAct k (A * B) c = vecAct k A (vecAct k B c) := by
  funext i
  simp [vecAct_apply, Matrix.mulVec_mulVec]

theorem vecAct_one (k : ℕ) (c : Fin k → Multiplicative (Fin n → K)) :
    vecAct k (1 : Matrix (Fin n) (Fin n) K) c = c := by
  funext i
  simp [vecAct_apply]

theorem vecAct_mulSingle {k : ℕ} (A : Matrix (Fin n) (Fin n) K) (i : Fin k)
    (x : Multiplicative (Fin n → K)) :
    vecAct k A (Pi.mulSingle i x) =
      Pi.mulSingle i (Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd x)) := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp [vecAct_apply]
  · rw [vecAct_apply, Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hji]
    simp

end VecAct

variable {G : Type} [Group G]

@[expose] noncomputable def secEquiv {n : ℕ} {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    (↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃*
      Multiplicative (Fin n → K) :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup
    (Multiplicative (Fin n → K))))).trans (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

theorem secEquiv_mk {n : ℕ} {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (m : ↥(FFModel.nat Γ).sec) :
    secEquiv Γ (QuotientGroup.mk m) = ((m : (FFModel.nat Γ).Amb) : Multiplicative (Fin n → K)) :=
  rfl

theorem exists_coords {V L : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n k : ℕ} (hk : 1 ≤ k) {W : Subgroup ↥V}
    (hDS : DirectSumOfCopies (autOn L V) W ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k)
    (hcard : Nat.card ↥(autOn L V) = Nat.card (SpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ (α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2))
      (Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥V),
      Function.Surjective α ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G)) ∧
      Function.Injective Φ ∧ Φ.range = W ∧
      ∀ (l : ↥L) (c : Fin k → Multiplicative (Fin n → ZMod 2)),
        (l : G) * (Φ c : G) * (l : G)⁻¹ =
          (Φ (vecAct k ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) c) : G) := by
  classical
  set A := Multiplicative (Fin n → ZMod 2) with hA
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hDS
  have : Finite (FFModel.nat (StatedSL n (ZMod 2))).Gam :=
    (inferInstance : Finite ↥(StatedSL n (ZMod 2)))
  have hπs : Function.Surjective π := (hreal ⟨0, hk⟩).1
  have hπb : Function.Bijective π := by
    refine (Nat.bijective_iff_surjective_and_card π).mpr ⟨hπs, ?_⟩
    rw [hcard]
    exact (Nat.card_congr (specialLinearGroupEquivStatedSL n (ZMod 2)).toEquiv).symm
  let πe : ↥(StatedSL n (ZMod 2)) ≃* ↥(autOn L V) := MulEquiv.ofBijective π hπb
  set ρ := InternalSec.autOnHom hLV with hρ
  set es := specialLinearGroupEquivStatedSL n (ZMod 2) with hes
  let α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    es.symm.toMonoidHom.comp (πe.symm.toMonoidHom.comp ρ)
  have hαπ : ∀ l : ↥L, π (es (α l)) = ρ l := fun l => by
    have h1 : es (α l) = πe.symm (ρ l) := es.apply_symm_apply _
    rw [h1]
    exact πe.apply_symm_apply (ρ l)
  have hαs : Function.Surjective α :=
    es.symm.surjective.comp (πe.symm.surjective.comp (InternalSec.autOnHom_surjective hLV))
  have hαk : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := fun l => by
    rw [← InternalSec.mem_ker_autOnHom hLV l, MonoidHom.mem_ker]
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact Iff.rfl
  have hcoord : ∀ i : Fin k, ∃ ϕ : A →* ↥V, Function.Injective ϕ ∧ ϕ.range = I i ∧
      ∀ (l : ↥L) (x : A), (ρ l : MulAut ↥V) (ϕ x) =
        ϕ (Multiplicative.ofAdd (((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd x)) := by
    intro i
    obtain ⟨-, -, -, hUi, -, -, -, β, hβs, hβ1, hβe⟩ := hreal i
    let ε : ↥(I i) →* A := (secEquiv (StatedSL n (ZMod 2))).toMonoidHom.comp β
    have hεi : Function.Injective ε := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      have h1 : β u = 1 := by
        have : (secEquiv (StatedSL n (ZMod 2))) (β u) = 1 := hu
        rwa [MulEquiv.map_eq_one_iff] at this
      have h2 := (hβ1 u).mp h1
      rw [Subgroup.mem_bot] at h2 ⊢
      exact Subtype.ext h2
    have hεs : Function.Surjective ε := (secEquiv (StatedSL n (ZMod 2))).surjective.comp hβs
    set εe := MulEquiv.ofBijective ε ⟨hεi, hεs⟩ with hεe
    refine ⟨(I i).subtype.comp εe.symm.toMonoidHom, ?_, ?_, fun l x => ?_⟩
    · exact (I i).subtype_injective.comp εe.symm.injective
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr εe.symm.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · set u := εe.symm x with hu
      have hux : ε u = x := εe.apply_symm_apply x
      have hβu : β u = QuotientGroup.mk
          (⟨x, Subgroup.mem_top x⟩ : ↥(FFModel.nat (StatedSL n (ZMod 2))).sec) := by
        apply (secEquiv (StatedSL n (ZMod 2))).injective
        rw [secEquiv_mk]
        exact hux
      set γ := es (α l) with hγ
      have hmem : ((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) ∈ I i := hUi (π γ) u u.2
      have h1 := hβe γ u ⟨x, Subgroup.mem_top x⟩ hmem (Subgroup.mem_top _) hβu
      have h2 : ε ⟨_, hmem⟩ = natAct (StatedSL n (ZMod 2)) γ x := by
        show secEquiv (StatedSL n (ZMod 2)) (β ⟨_, hmem⟩) = _
        rw [h1, secEquiv_mk]
        rfl
      have h3 : natAct (StatedSL n (ZMod 2)) γ x = Multiplicative.ofAdd
          (((α l : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            Multiplicative.toAdd x) := by
        rw [natAct, hγ, specialLinearGroupEquivStatedSL_coe]
      have h4 : εe ⟨_, hmem⟩ = Multiplicative.ofAdd
          (((α l : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            Multiplicative.toAdd x) := by
        rw [← h3, ← h2]
        rfl
      show (ρ l : MulAut ↥V) (u : ↥V) = ((εe.symm _ : ↥(I i)) : ↥V)
      rw [← h4, MulEquiv.symm_apply_apply]
      show (ρ l : MulAut ↥V) (u : ↥V) = ((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V)
      rw [hγ, hαπ]
  choose ϕ hϕi hϕr hϕe using hcoord
  have hcomm : Pairwise fun i j => ∀ (x : A) (y : A), Commute (ϕ i x) (ϕ j y) :=
    fun _ _ _ x y => mul_comm (ϕ _ x) (ϕ _ y)
  set Φ := MonoidHom.noncommPiCoprod ϕ hcomm with hΦ
  have hindep : iSupIndep fun i => (ϕ i).range := by
    rw [iSupIndep_def]
    intro i
    simp only [hϕr]
    rw [disjoint_iff]
    have := hind i
    rwa [bot_sup_eq] at this
  refine ⟨α, Φ, hαs, hαk,
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (hcomm := hcomm) hindep hϕi, ?_,
    fun l c => ?_⟩
  · rw [hΦ, MonoidHom.noncommPiCoprod_range]
    simp only [hϕr]
    rw [← hsup, bot_sup_eq]
  ·
    have hext : (ρ l : MulAut ↥V).toMonoidHom.comp Φ =
        Φ.comp (vecAct k ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))) := by
      refine MonoidHom.functions_ext ↥V _ _ fun i x => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, vecAct_mulSingle, hΦ,
        MonoidHom.noncommPiCoprod_mulSingle]
      exact hϕe i l x
    have h1 := congrArg (fun f => ((f c : ↥V) : G)) hext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    rw [← h1, hρ]
    exact (Setup.rho_apply_coe hLV l (Φ c)).symm

theorem coords_conj {V L : Subgroup G} {n k : ℕ} {K : Type} [Field K]
    {α : ↥L →* SpecialLinearGroup (Fin n) K} {Φ : (Fin k → Multiplicative (Fin n → K)) →* ↥V}
    (hΦ : ∀ (l : ↥L) (c : Fin k → Multiplicative (Fin n → K)),
      (l : G) * (Φ c : G) * (l : G)⁻¹ =
        (Φ (vecAct k ((α l : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c) : G))
    (g : SpecialLinearGroup (Fin n) K) (l : ↥L) (c : Fin k → Multiplicative (Fin n → K)) :
    (l : G) * ((Φ.comp (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K))) c : G) * (l : G)⁻¹ =
      ((Φ.comp (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        (vecAct k ((((MulAut.conj g).toMonoidHom.comp α) l : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) c) : G) := by
  show (l : G) * (Φ (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) c) : G) * (l : G)⁻¹ =
    (Φ (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (vecAct k ((g * α l * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c)) :
        G)
  rw [hΦ, ← vecAct_mul, ← vecAct_mul]
  have key : (g⁻¹ * (g * α l * g⁻¹) : SpecialLinearGroup (Fin n) K) = α l * g⁻¹ := by group
  have hkey := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) key
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hkey
  simp only [Matrix.SpecialLinearGroup.coe_mul, hkey]

theorem exists_conj_unitriangular {L T : Subgroup G} [Finite G] (hS₀ : IsSylowTwoOf (T ⊓ L) L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {α : ↥L →* SpecialLinearGroup (Fin n) K} (hαs : Function.Surjective α) :
    ∃ g : SpecialLinearGroup (Fin n) K,
      ((T ⊓ L).subgroupOf L).map ((MulAut.conj g).toMonoidHom.comp α) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n K := by
  have hP₀ : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm, fun h2 => ?_⟩
    apply hS₀.2.2
    rwa [show (((T ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((T ⊓ L).subgroupOf L).index from
      Subgroup.relIndex_top_right _] at h2
  have hU₁ : IsSylowTwoOf (((T ⊓ L).subgroupOf L).map α) ⊤ := by
    have h1 := L3312.isSylowTwoOf_map_range α hP₀
    rwa [MonoidHom.range_eq_top.mpr hαs] at h1
  have hU₀ : IsSylowTwoOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n K) ⊤ :=
    SzN2.isSylowTwoOf_unitriangular hn
  obtain ⟨g, -, hg⟩ := (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀)
  refine ⟨g, ?_⟩
  rw [← Subgroup.map_map]
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  exact (hg x).symm

end CFSG.Quasithin.H13.L3318
