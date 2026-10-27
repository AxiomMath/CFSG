module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_pCoreOf_iff_mem_pCore_centKS2 {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

private theorem mem_sup_of_right_le_normalizer_centKS2 {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at h
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp h
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem exists_hom_modO2 {H K : Subgroup G} (hKH : K ≤ H)
    (hKN : H ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    ∃ θ : ↥(StatedSL 3 F) →* (↥H ⧸ CFSG.pCore 2 ↥H), Function.Injective θ ∧
      ∀ (k : G) (hk : k ∈ K), θ (α ⟨k, hk⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hKH hk⟩ := by
  classical
  have hcore : K ⊓ pCoreOf 2 H = pCoreOf 2 K := by
    refine le_antisymm ?_ ?_
    · have hK' : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
        fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hk,
            (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hk⟩
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hK'
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
          (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
  let ψ : ↥K →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKH)
  have hψ : ∀ k : ↥K, ψ k = 1 ↔ α k = 1 := by
    intro k
    have h1 : ψ k = 1 ↔ (k : G) ∈ pCoreOf 2 H :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hKH k)).trans
        (mem_pCoreOf_iff_mem_pCore_centKS2 (Subgroup.inclusion hKH k)).symm
    have h2 : α k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
      rw [← MonoidHom.mem_ker, hker]
      exact (mem_pCoreOf_iff_mem_pCore_centKS2 k).symm
    have h3 : (k : G) ∈ pCoreOf 2 H ↔ (k : G) ∈ pCoreOf 2 K := by
      rw [← hcore]
      exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
    exact h1.trans (h3.trans h2.symm)
  have hle : α.ker ≤ ψ.ker := fun k hk =>
    MonoidHom.mem_ker.mpr ((hψ k).mpr (MonoidHom.mem_ker.mp hk))
  have hθ : ∀ k : ↥K, (MonoidHom.liftOfSurjective α hα ⟨ψ, hle⟩) (α k) = ψ k :=
    fun k => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  refine ⟨MonoidHom.liftOfSurjective α hα ⟨ψ, hle⟩, ?_, fun k hk => hθ ⟨k, hk⟩⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨k, rfl⟩ := hα x
  rw [hθ k] at hx
  exact (hψ k).mp hx

theorem exists_decomp_cComp (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK) {H K : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hKc : K ∈ cComp H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hYp : ⁅Y, Y⁆ = Y) :
    ∃ K' : Subgroup G, K' ≤ H ∧ (∀ k ∈ K, ∀ k' ∈ K', ⁅k, k'⁆ ∈ pCoreOf 2 H) ∧
      ∀ y ∈ Y, ∃ k ∈ K, ∃ k' ∈ K', y = k * k' := by
  classical
  set S : Set (Subgroup G) := cComp H \ {K} with hS
  have hSmem : ∀ L, L ∈ S ↔ L ∈ cComp H ∧ L ≠ K := fun L => by
    simp [hS]
  have hSH : ∀ L ∈ S, L ≤ H := fun L hL => le_of_mem_cComp ((hSmem L).mp hL).1
  have hSN : ∀ L ∈ S, L ≤ Subgroup.normalizer (K : Set G) := fun L hL =>
    le_normalizer_of_mem_cComp hKc ((hSmem L).mp hL).1
  have hSC : ∀ L ∈ S, ⁅K, L⁆ ≤ pCoreOf 2 H := by
    intro L hL
    obtain ⟨h1, h2⟩ := lemma_1_2_1_two hK hs hnab h37 hH hKc ((hSmem L).mp hL).1
      (Ne.symm ((hSmem L).mp hL).2)
    exact h1.trans h2
  let M : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ pCoreOf 2 H}
      one_mem' := by
        refine ⟨H.one_mem, fun k _ => ?_⟩
        rw [commutatorElement_one_right]
        exact (pCoreOf 2 H).one_mem
      mul_mem' := fun {x y} hx hy => by
        refine ⟨H.mul_mem hx.1 hy.1, fun k hk => ?_⟩
        have e : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (pCoreOf 2 H).mul_mem (hx.2 k hk)
          ((Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx.1) _).mp (hy.2 k hk))
      inv_mem' := fun {x} hx => by
        refine ⟨H.inv_mem hx.1, fun k hk => ?_⟩
        have e : ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff''.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx.1) _).mp
          ((pCoreOf 2 H).inv_mem (hx.2 k hk)) }
  have hMmem : ∀ x, x ∈ M ↔ x ∈ H ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ pCoreOf 2 H := fun x => Iff.rfl
  have hsM : sSup S ≤ M := sSup_le fun L hL x hx =>
    (hMmem x).mpr ⟨hSH L hL hx, fun k hk => hSC L hL (Subgroup.commutator_mem_commutator hk hx)⟩
  refine ⟨sSup S, sSup_le hSH, fun k hk k' hk' => ((hMmem k').mp (hsM hk')).2 k hk, ?_⟩
  intro y hy
  have hcc : cCompSpan H = K ⊔ sSup S := by
    have hsplit : cComp H = insert K S := by
      ext L
      constructor
      · intro hL
        by_cases hLK : L = K
        · exact Set.mem_insert_iff.mpr (Or.inl hLK)
        · exact Set.mem_insert_iff.mpr (Or.inr ((hSmem L).mpr ⟨hL, hLK⟩))
      · intro hL
        rcases Set.mem_insert_iff.mp hL with hL | hL
        · rw [hL]
          exact hKc
        · exact ((hSmem L).mp hL).1
    show sSup (cComp H) = K ⊔ sSup S
    rw [hsplit, sSup_insert]
  have hYc : Y ≤ cCompSpan H := by
    rw [lemma_1_2_1_one hK hs hnab h39 hH]
    exact le_perfectCore_of_perfect hYH hYp
  have hyK : y ∈ K ⊔ sSup S := by
    rw [← hcc]
    exact hYc hy
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_right_le_normalizer_centKS2 (sSup_le hSN) hyK
  exact ⟨a, ha, b, hb, hab⟩

end CFSG.Quasithin.H13.Ch4.CentK
