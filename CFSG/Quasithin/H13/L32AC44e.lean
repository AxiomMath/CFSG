module

public import CFSG.Quasithin.H13.L32AC44d
public import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Pointwise

theorem SL3N.not_two_dvd_index_upperUni {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 2) : ¬ 2 ∣ (upperUni F).index := by
  have h1 := (upperUni F).card_mul_index
  rw [card_upperUni, LinearFlag.card_SL_eq (n := 3) (by norm_num), Nat.card_eq_fintype_card,
    hF] at h1
  norm_num [Finset.prod_Icc_succ_top] at h1
  omega

theorem l34BorelFix {N : Type} [CommGroup N] [Finite N] {X : Subgroup (MulAut N)}
    {U : Subgroup N} (hX : BinaryNaturalSL X U ⊥ 3 2) {S : Subgroup (MulAut N)}
    (hS : IsSylowTwoOf S X) (α : MulAut ↥X)
    (hαS : ∀ s (hs : s ∈ X), s ∈ S → ((α ⟨s, hs⟩ : ↥X) : MulAut N) ∈ S)
    {y : MulAut N} (hyX : y ∈ X) (hyN : y ∈ Subgroup.normalizer (S : Set (MulAut N)))
    (hyS : y ∉ S) (hαy : ((α ⟨y, hyX⟩ : ↥X) : MulAut N) * y ∈ S)
    {d : MulAut N} (hdX : d ∈ X) (hdN : d ∈ Subgroup.normalizer (S : Set (MulAut N)))
    (hdS : d ∉ S) (hαd : ((α ⟨d, hdX⟩ : ↥X) : MulAut N) * d⁻¹ ∈ S)
    {v : N} (hvU : v ∈ U) (hv : ∀ s ∈ S, s v = v) (hdv : d v = v) : v = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, π, hπ⟩ := hX
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 2 := by rw [Fintype.card_eq_nat_card, hF]
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by norm_num : 1 ≤ 2) hF
  obtain ⟨f, -, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  let θ : ↥U → (Fin 3 → F) := fun u => @Multiplicative.toAdd (Fin 3 → F)
    (((f u : ↥(FFModel.nat (StatedSL 3 F)).sec) : (FFModel.nat (StatedSL 3 F)).Amb))
  have hθ1 : θ 1 = 0 := by
    show @Multiplicative.toAdd (Fin 3 → F) (((f 1 : ↥(FFModel.nat (StatedSL 3 F)).sec) :
      (FFModel.nat (StatedSL 3 F)).Amb)) = 0
    rw [map_one]
    rfl
  have hθinj : ∀ a b : ↥U, θ a = θ b → a = b := by
    intro a b hab
    have h1 : f a = f b := Subtype.ext (Multiplicative.toAdd.injective hab)
    have h2 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hfk _).mp h2
    rw [Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp (Subtype.ext h3)
  have hUinv : ∀ h : ↥X, ∀ u ∈ U, (h : MulAut N) u ∈ U := hπ.2.2.2.1
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let Φ : SL(3, F) ≃* ↥X :=
    (specialLinearGroupEquivStatedSL 3 F).trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩)
  have hθΦ : ∀ (g : SL(3, F)) (u : ↥U),
      θ ⟨((Φ g : ↥X) : MulAut N) u, hUinv _ u u.2⟩ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ θ u :=
    fun g u => congrArg Multiplicative.toAdd (hfe _ u (hUinv _ u u.2))
  set S' : Subgroup SL(3, F) := (S.subgroupOf X).comap Φ.toMonoidHom with hS'
  have hS'mem : ∀ γ, γ ∈ S' ↔ ((Φ γ : ↥X) : MulAut N) ∈ S := fun γ => Iff.rfl
  have hS'2 : IsPGroup 2 ↥S' := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf X) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact h1.comap_of_injective Φ.toMonoidHom Φ.injective
  have hS'i : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_comap_of_surjective _ Φ.surjective]
    exact hS.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, F)
    ((isPGroup_upperUni hF).toSylow (SL3N.not_two_dvd_index_upperUni hF'))
    (hS'2.toSylow hS'i)
  have hgS : ∀ γ : SL(3, F), γ ∈ S' ↔ g⁻¹ * γ * g ∈ upperUni F := by
    intro γ
    have h1 : S' = MulAut.conj g • upperUni F := by
      have := congrArg (fun P : Sylow 2 SL(3, F) => (P : Subgroup SL(3, F))) hg
      simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
      exact this.symm
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  let α' : SL(3, F) ≃* SL(3, F) :=
    (MulAut.conj g).trans (Φ.trans (α.trans (Φ.symm.trans (MulAut.conj g⁻¹))))
  have hα' : ∀ x, α' x = g⁻¹ * Φ.symm (α (Φ (g * x * g⁻¹))) * g := by
    intro x
    simp [α', MulAut.conj_apply]
  have hS'S : ∀ x : ↥X, Φ.symm x ∈ S' ↔ (x : MulAut N) ∈ S := by
    intro x
    rw [hS'mem, MulEquiv.apply_symm_apply]
  have hconjU : ∀ x : ↥X, (x : MulAut N) ∈ S → g⁻¹ * Φ.symm x * g ∈ upperUni F := by
    intro x hx
    exact (hgS _).mp ((hS'S x).mpr hx)
  have hα'U : ∀ u ∈ upperUni F, α' u ∈ upperUni F := by
    intro u hu
    rw [hα']
    apply hconjU
    have h1 : g * u * g⁻¹ ∈ S' := by
      rw [hgS]
      have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
      rw [e]
      exact hu
    exact hαS _ _ ((hS'mem _).mp h1)
  have hnorm : ∀ {z : MulAut N} (hzX : z ∈ X),
      z ∈ Subgroup.normalizer (S : Set (MulAut N)) →
        g⁻¹ * Φ.symm ⟨z, hzX⟩ * g ∈ SL3N.borel F := by
    intro z hzX hzN
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hgu : g * u * g⁻¹ ∈ S' := by
      rw [hgS]
      have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
      rw [e]
      exact hu
    have h1 : Φ.symm ⟨z, hzX⟩ * (g * u * g⁻¹) * (Φ.symm ⟨z, hzX⟩)⁻¹ ∈ S' := by
      rw [hS'mem, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have := (Subgroup.mem_normalizer_iff.mp hzN _).mp ((hS'mem _).mp hgu)
      exact this
    have e : g⁻¹ * Φ.symm ⟨z, hzX⟩ * g * u * (g⁻¹ * Φ.symm ⟨z, hzX⟩ * g)⁻¹ =
        g⁻¹ * (Φ.symm ⟨z, hzX⟩ * (g * u * g⁻¹) * (Φ.symm ⟨z, hzX⟩)⁻¹) * g := by group
    rw [e]
    exact (hgS _).mp h1
  have hnotU : ∀ {z : MulAut N} (hzX : z ∈ X), z ∉ S → g⁻¹ * Φ.symm ⟨z, hzX⟩ * g ∉ upperUni F := by
    intro z hzX hzS h
    exact hzS ((hS'S ⟨z, hzX⟩).mp ((hgS _).mpr h))
  have hα'z : ∀ {z : MulAut N} (hzX : z ∈ X), α' (g⁻¹ * Φ.symm ⟨z, hzX⟩ * g) =
      g⁻¹ * Φ.symm (α ⟨z, hzX⟩) * g := by
    intro z hzX
    rw [hα']
    have e : g * (g⁻¹ * Φ.symm ⟨z, hzX⟩ * g) * g⁻¹ = Φ.symm ⟨z, hzX⟩ := by group
    rw [e, MulEquiv.apply_symm_apply]
  have hy'1 : α' (g⁻¹ * Φ.symm ⟨y, hyX⟩ * g) * (g⁻¹ * Φ.symm ⟨y, hyX⟩ * g) ∈ upperUni F := by
    rw [hα'z]
    have e : g⁻¹ * Φ.symm (α ⟨y, hyX⟩) * g * (g⁻¹ * Φ.symm ⟨y, hyX⟩ * g) =
        g⁻¹ * Φ.symm (α ⟨y, hyX⟩ * ⟨y, hyX⟩) * g := by
      rw [map_mul]
      group
    rw [e]
    exact hconjU _ hαy
  have hd'1 : α' (g⁻¹ * Φ.symm ⟨d, hdX⟩ * g) * (g⁻¹ * Φ.symm ⟨d, hdX⟩ * g)⁻¹ ∈ upperUni F := by
    rw [hα'z]
    have e : g⁻¹ * Φ.symm (α ⟨d, hdX⟩) * g * (g⁻¹ * Φ.symm ⟨d, hdX⟩ * g)⁻¹ =
        g⁻¹ * Φ.symm (α ⟨d, hdX⟩ * ⟨d, hdX⟩⁻¹) * g := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact hconjU _ hαd
  have hd00 := SL3N.borel_fix hF' α' hα'U (hnorm hyX hyN) (hnotU hyX hyS) hy'1
    (hnorm hdX hdN) (hnotU hdX hdS) hd'1
  set w := θ ⟨v, hvU⟩ with hw
  have hfixS : ∀ s ∈ S', (s : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro s hs
    rw [hw, ← hθΦ]
    congr 1
    exact Subtype.ext (hv _ ((hS'mem s).mp hs))
  have hfixU : ∀ u ∈ upperUni F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
    intro u hu
    have hgu : g * u * g⁻¹ ∈ S' := by
      rw [hgS]
      have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
      rw [e]
      exact hu
    have h1 := hfixS _ hgu
    rw [mulVec_mulVec, SL3N.coe_mul_coe, show u * g⁻¹ = g⁻¹ * (g * u * g⁻¹) by group,
      ← SL3N.coe_mul_coe g⁻¹ (g * u * g⁻¹), ← mulVec_mulVec, h1]
  obtain ⟨h1, h2⟩ := SL3N.fix_upperUni hfixU
  have hΦd : ((Φ.symm ⟨d, hdX⟩ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    rw [hw, ← hθΦ]
    congr 1
    apply Subtype.ext
    show (((Φ (Φ.symm ⟨d, hdX⟩)) : ↥X) : MulAut N) v = v
    rw [MulEquiv.apply_symm_apply]
    exact hdv
  have hdw : ((g⁻¹ * Φ.symm ⟨d, hdX⟩ * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
    rw [mulVec_mulVec, SL3N.coe_mul_coe,
      show g⁻¹ * Φ.symm ⟨d, hdX⟩ * g * g⁻¹ = g⁻¹ * Φ.symm ⟨d, hdX⟩ by group,
      ← SL3N.coe_mul_coe g⁻¹ (Φ.symm ⟨d, hdX⟩), ← mulVec_mulVec, hΦd]
  set c := (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 0 with hcdef
  have hwe : ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = c • Pi.single 0 1 := by
    funext k
    fin_cases k
    · show c = (c • (Pi.single 0 1 : Fin 3 → F)) 0
      simp
    · show (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 1 =
        (c • (Pi.single 0 1 : Fin 3 → F)) 1
      rw [h1]
      simp
    · show (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 2 =
        (c • (Pi.single 0 1 : Fin 3 → F)) 2
      rw [h2]
      simp
  rw [hwe, mulVec_smul, SL3N.borel_mulVec_e0 (hnorm hdX hdN), smul_smul] at hdw
  have hc : c = 0 := by
    by_contra hc
    apply hd00
    have h3 := congrFun hdw 0
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    exact mul_right_injective₀ hc (h3.trans (mul_one c).symm)
  have hw0 : w = 0 := by
    have h4 : ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = 0 := by
      rw [hwe, hc, zero_smul]
    calc w = ((g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))
          *ᵥ w := by rw [SL3N.coe_mul_coe_inv, one_mulVec]
      _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by rw [mulVec_mulVec]
      _ = 0 := by rw [h4, mulVec_zero]
  have := hθinj ⟨v, hvU⟩ 1 (by rw [← hw, hw0, hθ1])
  exact congrArg Subtype.val this

end CFSG.Quasithin.H13.L32A.C
