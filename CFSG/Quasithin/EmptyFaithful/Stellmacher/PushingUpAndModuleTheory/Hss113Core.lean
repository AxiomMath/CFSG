module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Sec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Off
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_subgroupOf_eq_relIndex {A N : Subgroup G} {n : ℕ} (ψ : ↥A →* Perm (Fin n))
    (hker : ∀ x : ↥A, ψ x = 1 ↔ (x : G) ∈ N) {K : Subgroup G} (hK : K ≤ A) :
    Nat.card ((K.subgroupOf A).map ψ) = N.relIndex K := by
  have h1 : ψ.ker = N.comap A.subtype := by
    ext x; exact (MonoidHom.mem_ker.trans (hker x))
  rw [← Subgroup.relIndex_ker, h1, Subgroup.relIndex_comap, Subgroup.map_subgroupOf_eq_of_le hK]

theorem hss113_core {X Z Y Q' : Subgroup G} (θ : ↥X →* Perm (Fin 5))
    (hθ : Function.Surjective θ) (hker : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 X)
    (hZ : IsElemAbelian 2 Z) (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hC : X ⊓ Subgroup.centralizer (Z : Set G) = pCoreOf 2 X)
    (hYX : Y ≤ X) (hY : IsElemAbelian 2 Y) (hYQ : ∀ y ∈ Y, ∀ q ∈ Q', y * q = q * y)
    (hYn : ¬ Y ≤ pCoreOf 2 X)
    (hle : (Z ⊓ Q').relIndex Z ≤ (Y ⊓ pCoreOf 2 X).relIndex Y) :
    (Y ⊓ pCoreOf 2 X).relIndex Y ≤ (Z ⊓ Q').relIndex Z ∧
      (IsNatSec X (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) Z ∨
        IsOrthSec X (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) Z) := by
  have hZcomm := isMulCommutative_subgroup_iff.mp hZ.1
  have hs0 : IsSec X ⊥ Z :=
    { le := bot_le
      normN := hXN
      normL := fun x _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl; simp
        · intro h1
          have : h = x⁻¹ * (x * h * x⁻¹) * x := by group
          rw [this, h1]; simp
      comm := fun x hx y hy => by
        rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact (hZcomm x hx y hy)
      sq := fun x hx => by rw [Subgroup.mem_bot]; exact hZ.2 x hx }
  have hk0 : θ.ker = (cSecIn X ⊥ Z).subgroupOf X := by
    ext f
    rw [MonoidHom.mem_ker, hker f, Subgroup.mem_subgroupOf, ← hC,
      mem_cSecIn_iff hs0.normL, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨f.2, fun x hx => ?_⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact (h x hx).symm
    · rintro ⟨-, h⟩
      refine ⟨f.2, fun x hx => ?_⟩
      have := h x hx
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  set K : Subgroup G := Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) with hKdef
  have hs : IsSec X K Z := isSec_inf_centralizer_oTwoRes hZ hXN
  have hk : θ.ker ≤ (cSecIn X K Z).subgroupOf X := by
    intro f hf
    have hf' : f ∈ (cSecIn X ⊥ Z).subgroupOf X := hk0 ▸ hf
    rw [Subgroup.mem_subgroupOf] at hf' ⊢
    obtain ⟨hfX, hfc⟩ := (mem_cSecIn_iff hs0.normL).mp hf'
    refine (mem_cSecIn_iff hs.normL).mpr ⟨hfX, fun x hx => ?_⟩
    have := hfc x hx
    rw [Subgroup.mem_bot] at this
    rw [this]; exact K.one_mem
  have hnt : ∃ w : (secModule hs θ hθ hk).W, w ≠ 1 := by
    obtain ⟨z, hz, hzK⟩ := IsConcreteLE.not_le_iff_exists.mp (not_le_inf_centralizer_oTwoRes (X := X)
      (Z := Z) θ hθ hk0)
    refine ⟨hs.proj ⟨z, hz⟩, fun h => hzK ?_⟩
    have := (hs.proj_eq_one_iff ⟨z, hz⟩).mp h
    exact this.2
  have hfix : fixW (secModule hs θ hθ hk) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨z, rfl⟩ := hs.proj_surjective w
    refine (hs.proj_eq_one_iff z).mpr ?_
    refine mem_inf_centralizer_oTwoRes_of_forall hZ z.2 fun x hx => ?_
    have h1 := hw (θ ⟨x, hx⟩) (Subgroup.mem_top _)
    rw [secModule_act_proj hs θ hθ hk ⟨x, hx⟩ z] at h1
    exact (hs.proj_eq_proj_iff _ _).mp h1.symm
  set B : Subgroup (Perm (Fin 5)) := (Y.subgroupOf X).map θ with hB
  have hBcard : Nat.card B = (Y ⊓ pCoreOf 2 X).relIndex Y := by
    rw [hB, card_map_subgroupOf_eq_relIndex θ hker hYX, Subgroup.inf_relIndex_left]
  have hBne : B ≠ ⊥ := by
    intro h
    apply hYn
    intro y hy
    have : θ ⟨y, hYX hy⟩ ∈ B := ⟨⟨y, hYX hy⟩, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (hker _).mp this
  have hBexp : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hY.2 y hy)
    rw [this, map_one]
  have hfixle : (fixW (secModule hs θ hθ hk) B).index ≤ (Z ⊓ Q').relIndex Z := by
    let P : Subgroup ↥Z := (Z ⊓ Q').subgroupOf Z
    have hPle : P.map hs.proj ≤ fixW (secModule hs θ hθ hk) B := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [secModule_act_proj hs θ hθ hk a x]
      congr 1
      apply Subtype.ext
      show (a : G) * x * (a : G)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact hYQ a ha x (Subgroup.mem_inf.mp hx).2
    have h1 : (fixW (secModule hs θ hθ hk) B).index ∣ (P.map hs.proj).index := Subgroup.index_dvd_of_le hPle
    have h2 : (P.map hs.proj).index ∣ P.index := Subgroup.index_map_dvd (H := P) hs.proj_surjective
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (h1.trans h2)
  have hoff : (fixW (secModule hs θ hθ hk) B).index ≤ Nat.card B := by rw [hBcard]; omega
  obtain ⟨hidx, hcases⟩ := offender_dichotomy (secModule hs θ hθ hk) hnt hfix hBne hBexp hoff
  refine ⟨by rw [← hBcard, ← hidx]; exact hfixle, ?_⟩
  rcases hcases with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
  · have hf := (secModule_faithful_iff hs θ hθ hk).mp (Model.Faithful.of_iso e orth_faithful)
    exact Or.inr (isModelSec_of_iso hs θ hθ (le_antisymm hk hf) e.symm)
  · have hf := (secModule_faithful_iff hs θ hθ hk).mp (Model.Faithful.of_iso e nat_faithful)
    exact Or.inl (isModelSec_of_iso hs θ hθ (le_antisymm hk hf) e.symm)

end CFSG.Quasithin.F53Mod
