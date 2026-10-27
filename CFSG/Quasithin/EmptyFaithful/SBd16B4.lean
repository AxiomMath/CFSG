module

public import CFSG.Quasithin.EmptyFaithful.SBd16Gen
public import CFSG.Quasithin.EmptyFaithful.SBd14Ctx

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_d_V₁ (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∃ d : G, d ∈ Yp ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧ d ∈ Subgroup.normalizer (V₁ : Set G) ∧
      ∃ v ∈ V₁, d * v * d⁻¹ ≠ v := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨t', ht'T, -, hc1, hc2, -⟩ := exists_swap hyp D0
  obtain ⟨d, hdD, hd3, hdN0⟩ := r.exists_outer h113 ht'T hc2
  have hdYp : d ∈ Yp := r.D_le_Yp ht'T hdD
  have hd1 : d ≠ 1 := fun h => hdN0 (h ▸ Subgroup.mem_sup_left (Subgroup.one_mem _))
  refine ⟨d, hdYp, hd3, hd1, (r.Yp_le_V h113).1 hdYp, ?_⟩
  by_contra hcon
  push Not at hcon
  have hdV₂ : ∀ v ∈ V₂, d * v = v * d := r.D_cV₂ hc1 d hdD
  have hdV₁ : ∀ v ∈ V₁, d * v = v * d := fun v hv => by
    calc d * v = (d * v * d⁻¹) * d := by group
      _ = v * d := by rw [hcon v hv]
  have hsup : V₁ ⊔ V₂ ≤ Subgroup.centralizer ({d} : Set G) :=
    sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hdV₁ v hv).symm)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hdV₂ v hv).symm)
  rw [D0.sup] at hsup
  have hdC : d ∈ Subgroup.centralizer (VZ T M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hv)
  have hdP : d ∈ pCoreOf 2 Yp := by
    rw [(r.case1 h113).1]
    exact ⟨hdYp, hdC⟩
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 Yp) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Yp
  obtain ⟨k, hk⟩ := hP2 ⟨d, hdP⟩
  have hdk : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd3 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
  have hdvd2 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hdk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h1 : orderOf d ∣ 1 := by
    have := Nat.dvd_gcd hdvd2 hdvd3
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  exact hd1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

theorem RestHyp.V₁_transitive (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∀ x ∈ V₁, x ≠ 1 → ∀ y ∈ V₁, y ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (V₁ : Set G), m⁻¹ * x * m = y := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨d, -, hd3, -, hdN, v₀, hv₀, hv₀ne⟩ := r.exists_d_V₁ h113
  have hsq : ∀ a ∈ V₁, a * a = 1 := fun a ha => r.V_sq a (D0.le₁ ha)
  have hV4 : Nat.card ↥V₁ = 4 := D0.card₁
  have hcommV : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := by
    intro a ha b hb
    have := hyp.elemAbelian.1
    exact setLike_mul_comm (D0.le₁ ha) (D0.le₁ hb)
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hd3)
  have hfix : ∀ b ∈ V₁, b ≠ 1 → d * b * d⁻¹ = b → False := by
    intro b hb hb1 hdb
    exact hv₀ne (SBd7.odd_fixes_of_card_four hV4 hsq hdN hdodd hb hb1 hdb v₀ hv₀)
  have hd3' : d * d * d = 1 := by simpa [pow_succ] using hd3
  intro x hx hx1 y hy hy1
  have hconj : ∀ z ∈ V₁, d⁻¹ * z * d ∈ V₁ := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) z).mp hz
    simpa using this
  have hconj1 : ∀ z : G, z ≠ 1 → d⁻¹ * z * d ≠ 1 := fun z hz h => hz (by
    calc z = d * (d⁻¹ * z * d) * d⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hdfix : ∀ z ∈ V₁, z ≠ 1 → d⁻¹ * z * d = z → False := by
    intro z hz hz1 h
    refine hfix z hz hz1 ?_
    have h2 : d * z = z * d := by
      calc d * z = d * (d⁻¹ * z * d) := by rw [h]
        _ = z * d := by group
    rw [h2]
    group
  have hx₁V := hconj x hx
  have hx₁1 := hconj1 x hx1
  have hx₂V := hconj _ hx₁V
  have hx₁x : d⁻¹ * x * d ≠ x := fun h => hdfix x hx hx1 h
  have hP : x * (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) = 1 := by
    set P := x * (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) with hPdef
    have hPV : P ∈ V₁ := Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hx₁V) hx₂V
    have h3 : d⁻¹ * (d⁻¹ * (d⁻¹ * x * d) * d) * d = x := by
      calc d⁻¹ * (d⁻¹ * (d⁻¹ * x * d) * d) * d = (d * d * d)⁻¹ * x * (d * d * d) := by group
        _ = x := by rw [hd3']; group
    have hconjP : d⁻¹ * P * d = P := by
      calc d⁻¹ * P * d = (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) *
            (d⁻¹ * (d⁻¹ * (d⁻¹ * x * d) * d) * d) := by rw [hPdef]; group
        _ = (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) * x := by rw [h3]
        _ = x * (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) := by
          have c1 := hcommV _ hx₁V _ hx₂V
          have c2 := hcommV _ hx₂V x hx
          have c3 := hcommV _ hx₁V x hx
          calc (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) * x
              = (d⁻¹ * x * d) * ((d⁻¹ * (d⁻¹ * x * d) * d) * x) := by group
            _ = (d⁻¹ * x * d) * (x * (d⁻¹ * (d⁻¹ * x * d) * d)) := by rw [c2]
            _ = ((d⁻¹ * x * d) * x) * (d⁻¹ * (d⁻¹ * x * d) * d) := by group
            _ = (x * (d⁻¹ * x * d)) * (d⁻¹ * (d⁻¹ * x * d) * d) := by rw [c3]
    by_contra hP1
    refine hdfix P hPV hP1 hconjP
  have hkl := SBd16.mem_klein_four hV4 hsq hx hx₁V hx1 hx₁1 hx₁x.symm
  have hx₂eq : d⁻¹ * (d⁻¹ * x * d) * d = x * (d⁻¹ * x * d) := by
    have h1 : x * (d⁻¹ * x * d) * (d⁻¹ * (d⁻¹ * x * d) * d) = 1 := hP
    have e1 : (x * (d⁻¹ * x * d)) * (x * (d⁻¹ * x * d)) = 1 := by
      have c := hcommV _ hx _ hx₁V
      calc (x * (d⁻¹ * x * d)) * (x * (d⁻¹ * x * d))
          = (x * x) * ((d⁻¹ * x * d) * (d⁻¹ * x * d)) := by
            calc (x * (d⁻¹ * x * d)) * (x * (d⁻¹ * x * d))
                = x * ((d⁻¹ * x * d) * x) * (d⁻¹ * x * d) := by group
              _ = x * (x * (d⁻¹ * x * d)) * (d⁻¹ * x * d) := by rw [← c]
              _ = (x * x) * ((d⁻¹ * x * d) * (d⁻¹ * x * d)) := by group
        _ = 1 := by rw [hsq x hx, hsq _ hx₁V]; group
    have h2 : d⁻¹ * (d⁻¹ * x * d) * d = (x * (d⁻¹ * x * d))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right e1
  rcases hkl y hy with h | h | h | h
  · exact absurd h hy1
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · exact ⟨d, hdN, by rw [h]⟩
  · exact ⟨d * d, Subgroup.mul_mem _ hdN hdN, by rw [h, ← hx₂eq]; group⟩

theorem RestHyp.V₁_TI (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hI : I = Subgroup.normalizer (V₁ : Set G))
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I) :
    ∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G) := by
  intro g x hx hx1 hgx
  refine SBd16.normalizes_of_conj_mem (X := V₁) (fun v hv hv1 => ?_)
    (fun x hx hx1 y hy hy1 _ => r.V₁_transitive h113 x hx hx1 y hy hy1) hx hx1 hgx
  rw [← hI]
  exact hK1 v hv hv1

end CFSG.Quasithin.SBd14
