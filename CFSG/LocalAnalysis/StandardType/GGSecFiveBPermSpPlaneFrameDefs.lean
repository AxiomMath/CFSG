module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {G : Type} [Group G] {p n r : ℕ} {F : Type} [Field F]

@[expose] def GGSecFiveBPermSpPlaneFrame (Bs K : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n)
    (κ : StatedSp (r + 1) F →* G)
    (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F) : Prop :=
  Function.Injective κ ∧ κ.range = K ∧ Function.Injective ζ ∧
    ∀ (b : ↥Bs) (s : StatedSp (r + 1) F),
      (b : G) * κ s * (b : G)⁻¹ =
        κ (SpJoin.spPlaneTorus (r + 1) ζ (fun m => eta b (π m.succ)) * s *
          (SpJoin.spPlaneTorus (r + 1) ζ (fun m => eta b (π m.succ)))⁻¹)

@[expose] def ggBsCoordZeroOn (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (S : Set (Fin n)) : Subgroup G :=
  Bs ⊓ ⨅ j ∈ S, ggBsCoordZero Bs eta j

@[expose] def ggBlockComm (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (S : Set (Fin n)) : Subgroup G :=
  ⁅Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G), Bs⁆

theorem mem_ggBsCoordZeroOn {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {S : Set (Fin n)} {g : G} :
    g ∈ ggBsCoordZeroOn Bs eta S ↔ ∃ h : g ∈ Bs, ∀ j ∈ S, eta ⟨g, h⟩ j = 1 := by
  simp only [ggBsCoordZeroOn, Subgroup.mem_inf, Subgroup.mem_iInf, mem_ggBsCoordZero]
  constructor
  · rintro ⟨h, hS⟩
    exact ⟨h, fun j hj => by obtain ⟨_, e⟩ := hS j hj; exact e⟩
  · rintro ⟨h, hS⟩
    exact ⟨h, fun j hj => ⟨h, hS j hj⟩⟩

theorem ggBsCoordZeroOn_le (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (S : Set (Fin n)) : ggBsCoordZeroOn Bs eta S ≤ Bs :=
  inf_le_left

theorem ggBlockComm_le_centralizer (Bs : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (S : Set (Fin n)) :
    ggBlockComm Bs eta S ≤ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) := by
  have hBs_comm : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    eta.injective (by rw [map_mul, map_mul, mul_comm])
  have hBs_le : Bs ≤ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hBs_comm ⟨h, ggBsCoordZeroOn_le Bs eta S hh⟩ ⟨b, hb⟩)
  let C := Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G)
  have hCC : ⁅C, C⁆ ≤ C := by simpa using Subgroup.commutator_le_sup C C
  exact (Subgroup.commutator_mono le_rfl hBs_le).trans hCC

open Multiplicative

theorem ggBsCoordZeroOn_pair_compl_eq_sup_zpowers
    {G : Type} [Group G] {p n : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs) {a b : Fin n} (hab : a ≠ b)
    (hxa : eta ⟨x, hxBs⟩ a ≠ 1) (hyb : eta ⟨y, hyBs⟩ b ≠ 1)
    (hxoff : ∀ i, i ≠ a → eta ⟨x, hxBs⟩ i = 1)
    (hyoff : ∀ i, i ≠ b → eta ⟨y, hyBs⟩ i = 1) :
    ggBsCoordZeroOn Bs eta ({a, b} : Set (Fin n))ᶜ =
      Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  have hxH : x ∈ ggBsCoordZeroOn Bs eta ({a, b} : Set (Fin n))ᶜ := by
    rw [mem_ggBsCoordZeroOn]
    refine ⟨hxBs, fun i hi => hxoff i ?_⟩
    intro h
    subst i
    exact hi (by simp)
  have hyH : y ∈ ggBsCoordZeroOn Bs eta ({a, b} : Set (Fin n))ᶜ := by
    rw [mem_ggBsCoordZeroOn]
    refine ⟨hyBs, fun i hi => hyoff i ?_⟩
    intro h
    subst i
    exact hi (by simp)
  refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hxH) (Subgroup.zpowers_le.mpr hyH))
  intro g hg
  obtain ⟨hgBs, hgoff⟩ := mem_ggBsCoordZeroOn.mp hg
  let gB : ↥Bs := ⟨g, hgBs⟩
  let xB : ↥Bs := ⟨x, hxBs⟩
  let yB : ↥Bs := ⟨y, hyBs⟩
  have hxa0 : toAdd (eta xB a) ≠ 0 := by
    intro h
    exact hxa (toAdd.injective (by simpa using h))
  have hyb0 : toAdd (eta yB b) ≠ 0 := by
    intro h
    exact hyb (toAdd.injective (by simpa using h))
  let k : ℕ := (toAdd (eta gB a) / toAdd (eta xB a)).val
  let l : ℕ := (toAdd (eta gB b) / toAdd (eta yB b)).val
  have hk : (eta xB a) ^ k = eta gB a := by
    apply toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul]
    dsimp only [k]
    rw [ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hxa0
  have hl : (eta yB b) ^ l = eta gB b := by
    apply toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul]
    dsimp only [l]
    rw [ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hyb0
  have hg : gB = xB ^ k * yB ^ l := by
    apply eta.injective
    funext i
    simp only [map_mul, map_pow, Pi.mul_apply, Pi.pow_apply]
    by_cases hia : i = a
    · subst i
      rw [hyoff a hab, one_pow, mul_one, hk]
    · by_cases hib : i = b
      · subst i
        rw [hxoff b hab.symm, one_pow, one_mul, hl]
      · rw [hgoff i (by simp [hia, hib]), hxoff i hia, hyoff i hib]
        simp
  have hgeq : g = x ^ k * y ^ l := congrArg Subtype.val hg
  rw [hgeq]
  exact (Subgroup.zpowers x ⊔ Subgroup.zpowers y).mul_mem
    ((show Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y from le_sup_left)
      ((Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) k))
    ((show Subgroup.zpowers y ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y from le_sup_right)
      ((Subgroup.zpowers y).pow_mem (Subgroup.mem_zpowers y) l))

end CFSG.StandardType

end
