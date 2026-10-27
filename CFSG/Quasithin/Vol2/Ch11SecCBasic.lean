module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

noncomputable def autOnHom (K W : Subgroup G) (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    ↥K →* ↥(autOn K W) :=
  ((conjAct W).comp (Subgroup.inclusion hK)).codRestrict (autOn K W)
    (fun k => ⟨Subgroup.inclusion hK k, k.2, rfl⟩)

theorem autOnHom_apply_coe (K W : Subgroup G) (hK : K ≤ Subgroup.normalizer (W : Set G))
    (k : ↥K) (w : ↥W) : (((autOnHom K W hK k : ↥(autOn K W)) : MulAut ↥W) w : G) =
      (k : G) * w * (k : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl _) w

theorem autOnHom_surjective (K W : Subgroup G) (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    Function.Surjective (autOnHom K W hK) := by
  rintro ⟨_, ⟨n, hn, rfl⟩⟩
  refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
  rfl

theorem ker_autOnHom (K W : Subgroup G) (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    (autOnHom K W hK).ker = (Subgroup.centralizer (W : Set G)).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have := congrArg (fun φ : ↥(autOn K W) => (((φ : MulAut ↥W) ⟨w, hw⟩ : ↥W) : G)) h
    simp only [autOnHom_apply_coe] at this
    rw [OneMemClass.coe_one, MulAut.one_apply] at this
    have h2 : (k : G) * w * (k : G)⁻¹ = w := this
    calc w * (k : G) = ((k : G) * w * (k : G)⁻¹) * k := by rw [h2]
      _ = k * w := by group
  · intro h
    apply Subtype.ext
    ext w
    rw [autOnHom_apply_coe, OneMemClass.coe_one, MulAut.one_apply, ← h w w.2,
      mul_inv_cancel_right]

noncomputable def autOnEquiv (K W : Subgroup G) (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    ↥(autOn K W) ≃* ↥K ⧸ (autOnHom K W hK).ker :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (autOnHom_surjective K W hK)).symm

theorem isSimpleGroup_SL2 {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := Fintype.ofFinite F
  have hchar : CharP F 2 := by
    obtain ⟨p, hp⟩ := CharP.exists F
    have hpp : p.Prime := CharP.char_is_prime F p
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨k, hk, hk'⟩ := FiniteField.card F p
    have h1 : (p : ℕ) ^ (k : ℕ) = 2 ^ n := by rw [← hk', ← Nat.card_eq_fintype_card, hF]
    have h2 : p ∣ 2 ^ n := ⟨p ^ ((k : ℕ) - 1), by
      rw [← h1, ← pow_succ']; congr 1; have := k.pos; omega⟩
    have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2)
    exact h3 ▸ hp
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup

theorem eq_of_nParam_eq {H : Subgroup G} {k n : ℕ} (hk : E1.nParam H = k)
    (hn : E1.nParam H = n) : k = n := by
  have : (k : ℕ∞) = n := hk.symm.trans hn
  exact_mod_cast this

end CFSG.Quasithin.Vol2.Ch11.SecC
