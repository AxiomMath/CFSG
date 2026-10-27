module

public import CFSG.Quasithin.EmptyFaithful.S146zEInner
public import CFSG.Quasithin.EmptyFaithful.S146zEPure

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section CaseII

variable {G : Type} [Group G] [Finite G] {T M K Kp U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem false_of_rank_two_one3 (S : Setting146 G T M) (h4 : Stage1463Four) (hc23 : Conc14623 T M)
    (cK : PCtx T M K U₁ U₂ s u) (hKp : Kp ∈ cComp (mcOf T))
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hUgK : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G))
    (hin : ∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), conjSub b U₁ = U₁)
    (hUp : ∀ e ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), ∀ y ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz,
      e * y * e⁻¹ * y⁻¹ ∈ Zz)
    (h2 : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1)
    (hlt : 2 < mIdx (uOfL22 T M)
      (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G)))) : False := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp2 : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hUgH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  set Ug := F8.Uγ (VZ T M) (mcOf T) (g : G) with hUg
  set D := F8.DH (VZ T M) Zz (mcOf T) (g : G) with hD
  have hrelD : D.relIndex (uOfL22 T M) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp2, h2]; norm_num
  have hrelC : 8 ≤ (centralizerMod Zz (uOfL22 T M) Ug).relIndex (uOfL22 T M) := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp2]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hlt
  have hNU : ∀ d ∈ Ug, d ∈ Subgroup.normalizer (uOfL22 T M : Set G) := fun d hd =>
    le_normalizer_conjClosure _ _ (hUgH hd)
  have hNZ : ∀ d ∈ Ug, d ∈ Subgroup.normalizer (Zz : Set G) := fun d hd => by
    rw [S.normalizer_Z]; exact hUgH hd
  have key : ∃ d b, d ∈ D ∧ (d ∈ U₁ ∨ d ∈ U₂) ∧ b ∈ Ug ∧ d * b * d⁻¹ * b⁻¹ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hAC : D ⊓ U₁ ≤ centralizerMod Zz (uOfL22 T M) Ug := fun d hd =>
      ⟨cK.hU₁U hd.2, S.conjClosure_le_normalizer_Z hG (cK.hU₁U hd.2), fun b hb => by
        rw [hno d b hd.1 (Or.inl hd.2) hb]; exact Subgroup.one_mem _⟩
    have hBC : D ⊓ U₂ ≤ centralizerMod Zz (uOfL22 T M) Ug := fun d hd =>
      ⟨cK.hU₂U hd.2, S.conjClosure_le_normalizer_Z hG (cK.hU₂U hd.2), fun b hb => by
        rw [hno d b hd.1 (Or.inr hd.2) hb]; exact Subgroup.one_mem _⟩
    have hCC : cPart T M Kp ≤ centralizerMod Zz (uOfL22 T M) Ug := fun y hy =>
      ⟨cPart_le hKpH hy, S.conjClosure_le_normalizer_Z hG (cPart_le hKpH hy), fun b hb => by
        have h1 := trivial_on_cPart S hKpH (hUgH hb) (hUp b hb) y hy
        have e : y * b * y⁻¹ * b⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by group
        rw [e]; exact Subgroup.inv_mem _ h1⟩
    have hNC : (D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cPart T M Kp ≤ centralizerMod Zz (uOfL22 T M) Ug :=
      sup_le (sup_le hAC hBC) hCC
    obtain ⟨b₁, hb₁U, hb₁⟩ := exists_rep_of_relIndex_two cK.hU₁U hrelD
    obtain ⟨b₂, hb₂U, hb₂⟩ := exists_rep_of_relIndex_two cK.hU₂U hrelD
    have hb₁' : b₁ ∈ uOfL22 T M := cK.hU₁U hb₁U
    have hb₂' : b₂ ∈ uOfL22 T M := cK.hU₂U hb₂U
    have hN4 : ((D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cPart T M Kp).relIndex (uOfL22 T M) ≤ 4 := by
      refine (relIndex_le_card_of_cover ({1, b₁, b₂, b₁ * b₂} : Finset G) ?_ ?_).trans
        Finset.card_le_four
      · intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact hb₁'
        · exact hb₂'
        · exact (uOfL22 T M).mul_mem hb₁' hb₂'
      · intro v hv
        obtain ⟨y, hy, r₂, hr₂, d, hd, rfl⟩ := exists_decomp_three S hc23 cK.toCCtx hKp hcomps hv
        have hyU := cK.hU₁U hy
        have hr₂U := cK.hU₂U hr₂
        have hdU := cPart_le hKpH hd
        have hre : ∀ a b : G, a ∈ uOfL22 T M → b ∈ uOfL22 T M →
            y * (r₂ * d) * (a * b) = (y * a) * (r₂ * b) * d := by
          intro a b ha hb
          calc y * (r₂ * d) * (a * b) = y * r₂ * (d * a) * b := by group
            _ = y * r₂ * (a * d) * b := by rw [hcommU d hdU a ha]
            _ = y * (r₂ * a) * d * b := by group
            _ = y * (a * r₂) * d * b := by rw [hcommU r₂ hr₂U a ha]
            _ = y * a * r₂ * (d * b) := by group
            _ = y * a * r₂ * (b * d) := by rw [hcommU d hdU b hb]
            _ = (y * a) * (r₂ * b) * d := by group
        have hdN : d ∈ (D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cPart T M Kp := Subgroup.mem_sup_right hd
        rcases hb₁ y hy with h₁ | h₁ <;> rcases hb₂ r₂ hr₂ with h₂ | h₂
        · refine ⟨b₁ * b₂, by simp, ?_⟩
          rw [hre b₁ b₂ hb₁' hb₂']
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨b₁, by simp, ?_⟩
          have := hre b₁ 1 hb₁' (Subgroup.one_mem _)
          simp only [mul_one] at this
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨b₂, by simp, ?_⟩
          have := hre 1 b₂ (Subgroup.one_mem _) hb₂'
          simp only [one_mul, mul_one] at this
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂))) hdN
        · refine ⟨1, by simp, ?_⟩
          rw [mul_one]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁))
            (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right h₂)) hdN)
    have hdvd := Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hNC
    have hNpos : 0 < ((D ⊓ U₁) ⊔ (D ⊓ U₂) ⊔ cPart T M Kp).relIndex (uOfL22 T M) :=
      Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
    have := Nat.le_of_dvd hNpos hdvd
    omega
  obtain ⟨d, b, hdD, hdU, hbUg, hne⟩ := key
  have hcomm : d * b * d⁻¹ * b⁻¹ ∈ conjSub (g : G) Zz := hdD.2.2 b hbUg
  have hdU' : d * b * d⁻¹ * b⁻¹ ∈ U₁ ∨ d * b * d⁻¹ * b⁻¹ ∈ U₂ := by
    rcases hdU with hd1 | hd2
    · left
      have haN₁ : b ∈ Subgroup.normalizer (U₁ : Set G) := mem_normalizer_of_conjSub_eq (hin b hbUg)
      have h1 : b * d⁻¹ * b⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp haN₁ d⁻¹).mp (U₁.inv_mem hd1)
      have e : d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) := by group
      rw [e]; exact U₁.mul_mem hd1 h1
    · right
      have haN₂ : b ∈ Subgroup.normalizer (U₂ : Set G) :=
        mem_normalizer_of_conjSub_eq
          (cK.conjSub_U₂ S (hUgK hbUg) (hNU b hbUg) (hNZ b hbUg) (hin b hbUg))
      have h1 : b * d⁻¹ * b⁻¹ ∈ U₂ := (Subgroup.mem_normalizer_iff.mp haN₂ d⁻¹).mp (U₂.inv_mem hd2)
      have e : d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) := by group
      rw [e]; exact U₂.mul_mem hd2 h1
  obtain ⟨z, hz, hz1, hzx⟩ : ∃ z ∈ Zz, z ≠ 1 ∧ (g : G) * z * (g : G)⁻¹ = d * b * d⁻¹ * b⁻¹ := by
    refine ⟨(g : G)⁻¹ * (d * b * d⁻¹ * b⁻¹) * g, mem_conjSub.mp hcomm, ?_, by group⟩
    intro h1
    apply hne
    have e : d * b * d⁻¹ * b⁻¹ = (g : G) * ((g : G)⁻¹ * (d * b * d⁻¹ * b⁻¹) * g) * (g : G)⁻¹ := by
      group
    rw [e, h1]; group
  have hxZ : d * b * d⁻¹ * b⁻¹ ∉ Zz := hzx ▸ S.conj_not_mem_Z hG hsetup hz hz1
  exact cK.pure_not_conj S h4 hdU' hxZ g z hz hz1 hzx

end CaseII

end CFSG.Quasithin.ThreeD
