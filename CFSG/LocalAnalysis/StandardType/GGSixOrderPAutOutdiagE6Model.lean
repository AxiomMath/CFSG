module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagModel
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagExcPpd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

namespace IsTwoPowPpd

variable {f e r : ℕ}

theorem ne_two (h : IsTwoPowPpd f e r) (hef : 0 < e * f) : r ≠ 2 := by
  rintro rfl
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 := h.2
  rw [h2, orderOf_zero] at h3
  omega

theorem ne_three (h : IsTwoPowPpd f e r) (hef : 3 ≤ e * f) : r ≠ 3 := by
  rintro rfl
  have h1 : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  have h3 := h.2
  omega

theorem not_dvd (h : IsTwoPowPpd f e r) (he : 1 ≤ e) (hf : 1 ≤ f) : ¬ r ∣ f := by
  obtain ⟨hr, hord⟩ := h
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, orderOf_zero] at hord
    have : 0 < e * f := Nat.mul_pos he hf
    omega
  haveI : Fact r.Prime := ⟨hr⟩
  have hne : (2 : ZMod r) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have hdvd := ZMod.orderOf_dvd_card_sub_one hne
  rw [hord] at hdvd
  have hle : e * f ≤ r - 1 := Nat.le_of_dvd (by
    have := hr.two_le
    omega) hdvd
  intro hrf
  have := Nat.le_of_dvd (by omega) hrf
  have : f ≤ e * f := Nat.le_mul_of_pos_left f he
  omega

end IsTwoPowPpd

theorem ringAut_eq_one_of_pow_eq_one {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime) (hrf : ¬ r ∣ f)
    (σ : GaloisField 2 f ≃+* GaloisField 2 f) (hσ : σ ^ r = 1) : σ = 1 := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcard := (card_ringAut_and_isCyclic Nat.prime_two (GaloisField 2 f) hK).1
  have h1 : orderOf σ ∣ f := by
    have h := orderOf_dvd_natCard σ
    rwa [hcard] at h
  have h2 : orderOf σ ∣ r := orderOf_dvd_of_pow_eq_one hσ
  have h3 : orderOf σ = 1 := by
    rcases (Nat.dvd_prime hr).mp h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 hrf
  exact orderOf_eq_one_iff.mp h3

section Diag


theorem conj_mul_rootDiagAutHom_apply {K : Type} [Field K] (g : adjointGroup .E6 K)
    (a : Fin Tag.E6.rank → Kˣ) (h : adjointGroup .E6 K) :
    (((MulAut.conj g * rootDiagAutHom .E6 K a) h : adjointGroup .E6 K) : ModGL .E6 K) =
      (g : ModGL .E6 K) * (rootDiagUnit .E6 a * (h : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹) *
        (g : ModGL .E6 K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply]
  rfl

end Diag

section E6

namespace OutdiagE6

theorem units_map_entrywiseHom_one {K : Type} [Field K] (g : ModGL .E6 K) :
    Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) g = g :=
  Units.ext (entrywise_id _)

theorem mem_inner_of_pow_eq_one {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hrf : ¬ r ∣ f) {α : MulAut (adjointGroup .E6 (GaloisField 2 f))} (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : adjointGroup .E6 (GaloisField 2 f) →*
      MulAut (adjointGroup .E6 (GaloisField 2 f))).range := by
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) (GaloisField 2 f)
  obtain ⟨g, a, σ, ε, hgασε⟩ :=
    exists_conj_mul_exactNormalAut (K := GaloisField 2 f) (Or.inl rfl) α
  have hexpr : ∀ h : adjointGroup .E6 (GaloisField 2 f), (α h : ModGL .E6 (GaloisField 2 f)) =
      (g : ModGL .E6 (GaloisField 2 f)) * rootDiagUnit .E6 a *
        exactQ .E6 (GaloisField 2 f) (ε : ℕ) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E6 (GaloisField 2 f)) *
          (exactQ .E6 (GaloisField 2 f) (ε : ℕ))⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
            (g : ModGL .E6 (GaloisField 2 f))⁻¹ := by
    intro h
    rw [hgασε, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hθ := hΘ α g a σ ε hexpr
  have hθp : (Θ α) ^ r = 1 := by rw [← map_pow, hα, map_one]
  have hσp : σ ^ r = 1 := by
    have h := congrArg (MonoidHom.fst (RingAut (GaloisField 2 f))
      (Multiplicative (ZMod (exactE .E6)))) hθp
    rw [map_pow, map_one, hθ] at h
    simpa using h
  have hσ1 : σ = 1 := ringAut_eq_one_of_pow_eq_one hf hr hrf σ hσp
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have he' : ((ε : ℕ) : ZMod (exactE .E6)) = 0 := by
    have h2 : Multiplicative.ofAdd (((ε : ℕ) : ZMod (exactE .E6))) ^ r = 1 := by
      have h := congrArg (MonoidHom.snd (RingAut (GaloisField 2 f))
        (Multiplicative (ZMod (exactE .E6)))) hθp
      rw [map_pow, map_one, hθ] at h
      simpa using h
    have h3 : r • (((ε : ℕ) : ZMod (exactE .E6))) = 0 := by
      rw [← ofAdd_nsmul] at h2
      exact ofAdd_eq_one.mp h2
    have h4 : ((r : ℕ) : ZMod (exactE .E6)) * ((ε : ℕ) : ZMod (exactE .E6)) = 0 := by
      simpa [nsmul_eq_mul] using h3
    have hpcast : ((r : ℕ) : ZMod (exactE .E6)) = 1 := hrodd.natCast_zmod_two
    rw [hpcast, one_mul] at h4
    exact h4
  have hε0 : (ε : ℕ) = 0 := by
    have he : ((ε : ℕ) : ZMod 2) = 0 := he'
    have hdvd : 2 ∣ (ε : ℕ) := (ZMod.natCast_eq_zero_iff (ε : ℕ) 2).mp he
    have hlt : (ε : ℕ) < 2 := by simpa [exactE] using ε.isLt
    omega
  have hq : exactQ .E6 (GaloisField 2 f) (ε : ℕ) = 1 := by
    rw [hε0]
    exact exactQ_zero .E6 (GaloisField 2 f)
  have hαeq : α = MulAut.conj g * rootDiagAutHom .E6 (GaloisField 2 f) a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hexpr h, hq, hσ1, units_map_entrywiseHom_one, conj_mul_rootDiagAutHom_apply]
    simp only [inv_one, mul_one, mul_assoc]
  have hmem : α ∈ ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup .E6 (GaloisField 2 f)) ⊔ (rootDiagAutHom .E6 (GaloisField 2 f)).range := by
    rw [hαeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  exact ExcNonsplit.mem_inner_of_pow_eq_one (D := (rootDiagAutHom .E6 (GaloisField 2 f)).range)
    (by
      rintro _ ⟨b, rfl⟩
      exact ExcNonsplit.rootDiagAutHom_pow_three_mem_inner_E6 b) hr hr3 hmem hα

theorem mem_range_of_pow_eq_one {G : Type*} [Group G] {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrf : ¬ r ∣ f)
    {χ : adjointGroup .E6 (GaloisField 2 f) →* G} (hχ : Function.Injective χ)
    (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) {m : G}
    (hm : m ∈ Subgroup.normalizer (χ.range : Set G)) (hmr : m ^ r = 1) : m ∈ χ.range := by
  obtain ⟨α, hα⟩ := OutdiagModel.exists_induces hχ hm
  have hαr : α ^ r = 1 := by
    have h1 := hα.pow r
    rw [hmr] at h1
    exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
  obtain ⟨c, rfl⟩ := mem_inner_of_pow_eq_one hf hr hr2 hr3 hrf hαr
  rw [OutdiagModel.Induces.inj hC hα (OutdiagModel.Induces.conj (χ := χ) c)]
  exact ⟨c, rfl⟩

theorem exists_model {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E6 n f).K →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .E6 n f).D .E6 n f ψ) :
    ∃ χ : adjointGroup .E6 (GaloisField 2 f) →* G, Function.Injective χ ∧ χ.range = G₀ ∧
      ∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .E6 n f).D ψ c →
        ∃ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), OutdiagModel.Induces χ c α := by
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hS.presents
  have hC := hS.centralizer_eq_bot
  subst hrange
  have hkerEq : ψ.ker = Subgroup.center (ggU .E6 n f).K := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hC, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχ, hval⟩ :=
    ExcNonsplit.exists_factor_e6Isogeny (k := GaloisField 2 f) (ψ := ψ) hkerEq
  have hrange : χ.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨y, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) c
      exact ⟨y, (hval y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e6Isogeny (GaloisField 2 f) y, hval y⟩
  refine ⟨χ, hχ, hrange, ?_⟩
  intro c hcN hci
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hcN hci
  refine ⟨α, hαD, fun x => ?_⟩
  obtain ⟨u, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) x
  obtain ⟨u', hu'⟩ := LayerSixE.exists_conj_eq hcN u
  calc c * χ (e6Isogeny (GaloisField 2 f) u) * c⁻¹ = c * ψ u * c⁻¹ :=
        congrArg (fun t => c * t * c⁻¹) (hval u)
    _ = ψ u' := hu'.symm
    _ = χ (e6Isogeny (GaloisField 2 f) u') := (hval u').symm
    _ = χ (α (e6Isogeny (GaloisField 2 f) u)) := congrArg χ (hα u u' hu')

end OutdiagE6

end E6

end CFSG.StandardType
