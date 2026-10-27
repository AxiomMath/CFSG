module

public import CFSG.RankThree.GF2n.Stroth80.Sec41Alg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem normal_bar_Lgen [hN : (Q.subgroupOf M).Normal] (L : Subgroup G) :
    (bar M Q (Lgen M L)).Normal := by
  haveI : ((Lgen M L).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Lgen_normalizes M L)
  exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)

theorem Ctx.false_of_comm [hN : (Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (X : Subgroup (Mbar M Q)) (hXq : CFSG.IsQuasisimple X)
    (hcomm : ∀ x ∈ X, ∀ t : ↥M, (t : G) ∈ LB M Q B →
      x * (QuotientGroup.mk t : Mbar M Q) = (QuotientGroup.mk t : Mbar M Q) * x) : False := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφadd, hφsemi⟩ := exists_actionHom_M hc.hyp h
  obtain ⟨φ₀, hφ₀π, hφ₀ker, -⟩ := exists_actionHom_H0 hc.hyp h
  have hQnorm : ∀ {t : G}, t ∈ M → ∀ y ∈ Q, t * y * t⁻¹ ∈ Q := fun {t} ht y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ht) y).mp hy
  have hLH : LB M Q B ≤ H0 M Z := fun t ht => ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr
    fun z hz => by
      have := hc.LB_centralizes_Z ht z hz
      calc z * t = (t * z * t⁻¹) * t := by rw [this]
        _ = t * z := by group⟩
  let Φ : Mbar M Q →* Equiv.Perm M₀.E :=
    QuotientGroup.lift (Q.subgroupOf M) φ (fun q hq => MonoidHom.mem_ker.mpr ((hφker q).mpr hq))
  have hΦ : ∀ t : ↥M, Φ (QuotientGroup.mk t) = φ t := fun t => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ] at hx
    exact (QuotientGroup.eq_one_iff t).mpr ((hφker t).mp hx)
  have hcompat : ∀ (t : ↥M) (u : ↥(H0 M Z)), (t : G) = (u : G) → ∀ e, φ t e = φ₀ u e := by
    intro t u htu e
    refine congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (t : G)) (S₁ := φ t) (S₂ := φ₀ u)
      (hφπ t) (fun x hx => ?_)) e
    rw [htu]
    exact hφ₀π u x hx
  haveI : Group.IsPerfect ↥X := hXq.1
  haveI : Nontrivial ↥X :=
    haveI := hXq.2.1.toNontrivial
    (QuotientGroup.mk'_surjective (Subgroup.center ↥X)).nontrivial
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 m)
  let ρ : ↥X →* Equiv.Perm M₀.E := Φ.comp X.subtype
  let Λ : Subgroup (M₀.E ≃ₗ[GaloisField 2 m] M₀.E) := (φ₀.comp (Subgroup.inclusion hLH)).range
  have hΛ : IsPGroup 2 Λ := by
    intro g
    obtain ⟨T, t, rfl⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    show ((φ₀.comp (Subgroup.inclusion hLH)) t) ^ (2 ^ 1) = 1
    rw [← map_pow]
    exact (hφ₀ker (Subgroup.inclusion hLH (t ^ (2 ^ 1)))).mpr (by
      simpa using hc.sq_mem_Q_of_mem_LB t.2)
  have hle : B ⊔ Z ≤ M₀.lift (M₀.img B) := sup_le
    (fun b' hb' => ⟨hc.le hb', M₀.pi_mem_img hb' (hc.le hb')⟩)
    (fun z hz => ⟨hc.Z_le_Q hz, by
      rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
  have hLB_B : ∀ (t : ↥(LB M Q B)) (u : G), u ∈ B →
      φ₀ (Subgroup.inclusion hLH t) (M₀.π u) = M₀.π u := by
    intro t u hu
    rw [← hφ₀π _ u (hc.le hu)]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) (hc.le hu)
      (hQnorm (hc.LB_le_M t.2) u (hc.le hu))).mp (hc.comm_B_mem_Z t.2 hu)
  have hfix : ∀ v : M₀.E, (∀ T ∈ Λ, T v = v) ↔ ∃ c : GaloisField 2 m, v = c • b := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
      have hx : x ∈ CQt Q Z (LB M Q B) := by
        refine ⟨hxQ, fun t ht => ?_⟩
        have hT : φ₀ (Subgroup.inclusion hLH ⟨t, ht⟩) ∈ Λ := ⟨⟨t, ht⟩, rfl⟩
        have := hv _ hT
        rw [← hφ₀π _ x hxQ] at this
        exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
          (hQnorm (hc.LB_le_M ht) x hxQ)).mpr this
      rw [h35] at hx
      exact (hB _).mp (hle hx).2
    · rintro ⟨c, rfl⟩ T hT
      obtain ⟨t, rfl⟩ := hT
      obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
      have hTb : (φ₀.comp (Subgroup.inclusion hLH)) t b = b := by
        rw [← hu]; exact hLB_B t u huB
      rw [map_smul, hTb]
  have hcomm' : ∀ (γ : ↥X) (T : M₀.E ≃ₗ[GaloisField 2 m] M₀.E), T ∈ Λ → ∀ e,
      ρ γ (T e) = T (ρ γ e) := by
    intro γ T hT e
    obtain ⟨t, rfl⟩ := hT
    let t' : ↥M := ⟨t, hc.LB_le_M t.2⟩
    have hcm := hcomm γ γ.2 t' t.2
    have h1 : Φ (γ : Mbar M Q) * Φ (QuotientGroup.mk t') =
        Φ (QuotientGroup.mk t') * Φ (γ : Mbar M Q) := by
      rw [← map_mul, ← map_mul, hcm]
    have h2 : ∀ e, Φ (QuotientGroup.mk t') e = (φ₀.comp (Subgroup.inclusion hLH)) t e :=
      fun e => hcompat t' (Subgroup.inclusion hLH t) rfl e
    calc ρ γ ((φ₀.comp (Subgroup.inclusion hLH)) t e)
        = ρ γ (Φ (QuotientGroup.mk t') e) := by rw [h2]
      _ = (Φ (γ : Mbar M Q) * Φ (QuotientGroup.mk t')) e := rfl
      _ = (Φ (QuotientGroup.mk t') * Φ (γ : Mbar M Q)) e := by rw [h1]
      _ = Φ (QuotientGroup.mk t') (ρ γ e) := rfl
      _ = (φ₀.comp (Subgroup.inclusion hLH)) t (ρ γ e) := h2 _
  refine false_of_perfect_action ρ (hΦinj.comp X.subtype_injective) ?_ ?_ Λ hΛ b hb0 hfix hcomm'
  · intro γ e f
    obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (γ : Mbar M Q)
    show Φ (γ : Mbar M Q) (e + f) = Φ (γ : Mbar M Q) e + Φ (γ : Mbar M Q) f
    rw [← ht, hΦ]
    exact hφadd t e f
  · intro γ
    obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (γ : Mbar M Q)
    obtain ⟨σ, hσ⟩ := hφsemi t
    refine ⟨σ, fun c e => ?_⟩
    show Φ (γ : Mbar M Q) (c • e) = σ c • Φ (γ : Mbar M Q) e
    rw [← ht, hΦ]
    exact hσ c e

end CFSG.RankThree.GF2n.Stroth80
