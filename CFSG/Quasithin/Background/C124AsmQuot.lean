module

public import CFSG.Quasithin.Background.C124Star
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C124InterfaceDefs

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_mem_oTwoZIn {L : Subgroup G} {n : ↥L} (hn : (n : G) ∈ oTwoZIn L)
    (w : ↥L) : ((n * w * n⁻¹ * w⁻¹ : ↥L) : G) ∈ pCoreOf 2 L := by
  unfold oTwoZIn preimageModTwoCore at hn
  obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.1 hn
  have hyn' : y = n := Subtype.ext hyn
  subst hyn'
  have hc := Subgroup.mem_center_iff.1 (Subgroup.mem_comap.1 hy)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L) w)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (y * w * y⁻¹ * w⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  rw [pCoreOf_eq_map_pCore]
  exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem not_commute_of_isQuasisimple {H : Type*} [Group H] (hq : CFSG.IsQuasisimple H) :
    ¬ ∀ a b : H, a * b = b * a := by
  intro hab
  obtain ⟨a, b, hne⟩ := hq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab])

namespace Entry

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : Entry X T V L R m hV)

include E

theorem hLX : L ≤ X := le_of_mem_cComp E.comp

theorem hLN : L ≤ Subgroup.normalizer (V : Set G) := E.hLX.trans E.red.2.1

theorem pCoreOf_L_le_C : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
  (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans E.hLX)
    (E.normal.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
    (pCoreOf_le_centralizer E.red)

theorem exists_surj_alt (hm : 5 ≤ m) :
    ∃ ψ : ↥(autI hV L) →* ↥(alternatingGroup (Fin m)), Function.Surjective ψ := by
  obtain ⟨φ, hφs, hφk⟩ := E.alt
  set σ := starHom hV L E.hLN with hσ
  have hσs : Function.Surjective σ := starHom_surjective hV E.hLN
  have hσk : ∀ x : ↥L, x ∈ σ.ker ↔ (x : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    intro x
    rw [ker_starHom hV E.hLN, Subgroup.mem_subgroupOf]
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  have hK : σ.ker ≤ φ.ker := by
    have hnorm : (σ.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
    rcases hsimple.eq_bot_or_eq_top_of_normal (σ.ker.map φ) with h | h
    · intro k hk
      have : φ k ∈ σ.ker.map φ := ⟨k, hk, rfl⟩
      rw [h] at this
      exact this
    · exfalso
      refine not_commute_of_isQuasisimple E.quasi ?_
      have hrep : ∀ a : ↥(autI hV L), ∃ n : ↥L, (n : G) ∈ oTwoZIn L ∧ σ n = a := by
        intro a
        obtain ⟨l, rfl⟩ := hσs a
        have : φ l ∈ σ.ker.map φ := by rw [h]; trivial
        obtain ⟨k, hk, hkl⟩ := this
        refine ⟨k⁻¹ * l, ?_, ?_⟩
        · have h1 : k⁻¹ * l ∈ φ.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
          rw [hφk, Subgroup.mem_subgroupOf] at h1
          exact h1
        · rw [map_mul, map_inv, (MonoidHom.mem_ker.1 hk), inv_one, one_mul]
      intro a b
      obtain ⟨n, hn, rfl⟩ := hrep a
      obtain ⟨w, rfl⟩ := hσs b
      have hc := commutator_mem_pCoreOf_of_mem_oTwoZIn hn w
      have hcC : ((n * w * n⁻¹ * w⁻¹ : ↥L) : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨(n * w * n⁻¹ * w⁻¹ : ↥L).2,
          E.pCoreOf_L_le_C hc⟩
      have h1 : σ (n * w * n⁻¹ * w⁻¹) = 1 := (hσk _).2 hcC
      have h2 : σ n * σ w * (σ n)⁻¹ * (σ w)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using h1
      calc σ n * σ w = (σ n * σ w * (σ n)⁻¹ * (σ w)⁻¹) * (σ w * σ n) := by group
        _ = σ w * σ n := by rw [h2, one_mul]
  let e : ↥L ⧸ σ.ker ≃* ↥(autI hV L) := QuotientGroup.quotientKerEquivOfSurjective σ hσs
  refine ⟨(QuotientGroup.lift σ.ker φ hK).comp e.symm.toMonoidHom, fun a => ?_⟩
  obtain ⟨l, rfl⟩ := hφs a
  refine ⟨σ l, ?_⟩
  have : e.symm (σ l) = QuotientGroup.mk l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp [this]

end Entry

end CFSG.Quasithin.C124
