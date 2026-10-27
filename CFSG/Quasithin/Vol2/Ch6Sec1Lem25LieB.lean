module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Lie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

include hI in
theorem KT_case {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀K : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom) :
    K.map (MulAut.conj t₀).toMonoidHom = K ∨ (K.map (MulAut.conj t₀).toMonoidHom ≠ K ∧
      ∀ k' ∈ K.map (MulAut.conj t₀).toMonoidHom, ∀ k ∈ K, k' * k * k'⁻¹ * k⁻¹ ∈ pCoreOf 2 K) := by
  obtain ⟨-, -, -, -, hcase⟩ := d.KT_facts hI ht₀ ht₀K
  rcases hcase with h0 | ⟨-, htriv⟩
  · exact Or.inl h0
  · by_cases h0 : K.map (MulAut.conj t₀).toMonoidHom = K
    · exact Or.inl h0
    · exact Or.inr ⟨h0, htriv⟩

include hI in
theorem le_M_of_solvable (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    (kf4 : LieOvergroupFact) (hLie : IsLieChar2Big (KBar K)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom)
    {H₂ : Subgroup G} (hTH : T ≤ H₂) (hH₂ : H₂ ≤ (K ⊔ K.map (MulAut.conj t₀).toMonoidHom) ⊔ T)
    (hsolv : Group.IsSolvable ↥H₂) : H₂ ≤ M := by
  obtain ⟨-, hK'N, -, hTKT, -⟩ := d.KT_facts hI ht₀ ht₀K
  have hcase' := d.KT_case hI ht₀ ht₀K
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  set KT := K ⊔ K' with hKT
  have hKTN : KT ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  set Y := H₂ ⊓ KT with hY
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hKTN
  set Yn : Subgroup ↥(Subgroup.normalizer (K : Set G)) := Y.subgroupOf _ with hYn
  set Img : Subgroup (MulAut (KBar K)) := Yn.map (phiK K) with hImg
  have hYsolv : Group.IsSolvable ↥Yn := by
    have h1 : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYN).injective
  have hImgs : Group.IsSolvable ↥Img :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (phiK K) Yn)
  set X : Subgroup (KBar K) := Img.comap (MulAut.conj : KBar K →* MulAut (KBar K)) with hX
  have hXs : Group.IsSolvable ↥X := by
    let ψ : ↥X →* ↥Img :=
      { toFun := fun s => ⟨MulAut.conj (s : KBar K), s.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
    refine Group.isSolvable_of_isSolvable_injective (f := ψ) fun a b hab => ?_
    exact Subtype.ext (d.eq_of_conj_eq (congrArg Subtype.val hab))
  obtain ⟨hs, -⟩ := isSimpleGroup_KBar d.quasi
  have hk41 := kf4 (KBar K) hs hLie (SBar T L V K) (d.isSylowTwoOf_SBar hI.h432)
  have hSX : SBar T L V K ≤ X := by
    rintro _ ⟨⟨sk, hskK⟩, hsk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsk
    have hskN : sk ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hskK
    have hskY : sk ∈ Y := ⟨hTH hsk.1.1, Subgroup.mem_sup_left hskK⟩
    show MulAut.conj (piK K ⟨sk, hskK⟩) ∈ Img
    rw [← phiK_of_mem K ⟨sk, hskK⟩]
    exact ⟨⟨sk, hskN⟩, Subgroup.mem_subgroupOf.mpr hskY, rfl⟩
  have hXN := hk41 X hSX hXs
  have hact : ∀ y ∈ Y, ∀ hyN : y ∈ Subgroup.normalizer (K : Set G),
      ∃ s ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)),
        phiK K ⟨y, hyN⟩ = MulAut.conj s := by
    intro y hy hyN
    obtain ⟨k, hk, k', -, hφ, -⟩ := d.decomp_KT hK'N hcase' hy.2 hyN
    refine ⟨piK K ⟨k, hk⟩, hXN ?_, hφ⟩
    show MulAut.conj (piK K ⟨k, hk⟩) ∈ Img
    rw [← hφ]
    exact ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hYM : Y ≤ M := by
    intro y hy
    have ht₀H : t₀⁻¹ ∈ H₂ := H₂.inv_mem (hTH ht₀)
    have hyt : t₀⁻¹ * y * t₀ ∈ Y := by
      refine ⟨H₂.mul_mem (H₂.mul_mem ht₀H hy.1) (hTH ht₀), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hTKT (T.inv_mem ht₀)) y).mp hy.2
      simpa using this
    exact d.mem_M_of_mem_KT hI kf1 h23 ht₀ ht₀K hy.2 (hact y hy) (hact _ hyt)
  intro h hh
  obtain ⟨y, hy, t, ht, rfl⟩ := exists_mul_of_mem_sup_ch625 hTKT (hH₂ hh)
  have hyY : y ∈ Y := by
    refine ⟨?_, hy⟩
    have e : y = (y * t) * t⁻¹ := by group
    rw [e]
    exact H₂.mul_mem hh (H₂.inv_mem (hTH ht))
  exact M.mul_mem (hYM hyY) (d.hyp.T_le ht)

end Dat625

end CFSG.Quasithin.H13
