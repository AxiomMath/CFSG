module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.StandardType.Triality

namespace OrthRestEnd

section Pow

variable {G : Type*} [Group G] [Finite G]

theorem card_le_mul_inf_of_pow {N : Subgroup G} [N.Normal] {c : G} {p : ℕ} (hp : 0 < p)
    (hcp : c ^ p = 1) {E : Subgroup G} (hE : ∀ g ∈ E, ∃ n ∈ N, ∃ k : ℕ, g = n * c ^ k) :
    Nat.card E ≤ p * Nat.card (E ⊓ N : Subgroup G) := by
  set f : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype with hf
  have hker : f.ker = N.subgroupOf E := by
    ext x
    simp [hf, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range ≤ Subgroup.zpowers (c : G ⧸ N) := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨n, hn, k, hk⟩ := hE e e.2
    refine ⟨k, ?_⟩
    change (c : G ⧸ N) ^ (k : ℤ) = ((e : G) : G ⧸ N)
    rw [hk, zpow_natCast, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul,
      QuotientGroup.mk_pow]
  have hz : Nat.card (Subgroup.zpowers (c : G ⧸ N)) ≤ p := by
    rw [Nat.card_zpowers]
    refine Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one ?_)
    rw [← QuotientGroup.mk_pow, hcp, QuotientGroup.mk_one]
  have h2 : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h3 : Nat.card f.ker = Nat.card (E ⊓ N : Subgroup G) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  rw [h2, h3]
  exact Nat.mul_le_mul_right _ ((Subgroup.card_le_of_le hrange).trans hz)

end Pow

theorem mul_mem_of_sq_mem {M : Type*} [Group M] {N : Subgroup M} [N.Normal] {ι c : M}
    (hι : ι ∈ N) (hc : c * c ∈ N) (h3 : (ι * c) ^ 3 = 1) : ι * c ∈ N := by
  have h2 : (ι * c) ^ 2 ∈ N := by
    have e : (ι * c) ^ 2 = ι * (c * ι * c⁻¹) * (c * c) := by rw [sq]; group
    rw [e]
    exact mul_mem (mul_mem hι (Subgroup.Normal.conj_mem inferInstance ι hι c)) hc
  have e : ι * c = ((ι * c) ^ 2)⁻¹ * (ι * c) ^ 3 := by group
  rw [e, h3, mul_one]
  exact inv_mem h2

section Two

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem ringEquiv_eq_one (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 :=
  RingEquiv.ext fun x => by
    rcases OrthRest.eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
    · rw [map_zero]
      rfl
    · rw [map_one]
      rfl

theorem mul_self_of_mem_plusCompl (hK : Nat.card K = 2) {c : MulAut (Om8 K)}
    (hc : c ∈ AutOm.plusCompl (K := K) one_le_four) : c * c = 1 := by
  obtain ⟨σ, rfl | rfl⟩ := hc
  · rw [ringEquiv_eq_one hK σ, map_one, mul_one]
  · rw [ringEquiv_eq_one hK σ, map_one, mul_one]
    exact AutOm.plusRefl_mul_self one_le_four

theorem conjAct_ne_of_not_mem_inner (hK : Nat.card K = 2) {α : MulAut (Om8 K)}
    (hα3 : α ^ 3 = 1) (hα : α ∉ inner (Om8 K)) (g : similarityPairs (coordinateQuadPlus 4 K)) :
    conjAct _ g ≠ α := by
  intro hg
  obtain ⟨ι, hι, c, hc, hgc⟩ := exists_inner_mul_plusCompl_of_pair g
  rw [hgc] at hg
  subst hg
  exact hα (mul_mem_of_sq_mem hι (by rw [mul_self_of_mem_plusCompl hK hc]; exact one_mem _) hα3)

theorem exists_inner_mul_pow (hK : Nat.card K = 2) {θ : MulAut (Om8 K)}
    (hρθ : AutOm.plusRefl (K := K) one_le_four * θ * AutOm.plusRefl one_le_four = θ⁻¹)
    (hgen : ∀ α : MulAut (Om8 K), ∃ ι ∈ inner (Om8 K), ∃ k : ℕ,
      ∃ c ∈ AutOm.plusCompl (K := K) one_le_four, α = ι * (θ ^ k * c))
    {β : MulAut (Om8 K)} (hβ : β ^ 3 = 1) : ∃ ι ∈ inner (Om8 K), ∃ k : ℕ, β = ι * θ ^ k := by
  obtain ⟨ι, hι, k, c, hc, rfl⟩ := hgen β
  obtain ⟨σ, rfl | rfl⟩ := hc
  · refine ⟨ι, hι, k, ?_⟩
    rw [ringEquiv_eq_one hK σ, map_one, mul_one]
  · rw [ringEquiv_eq_one hK σ, map_one, mul_one] at hβ ⊢
    set ρ := AutOm.plusRefl (K := K) one_le_four with hρ
    have hρρ : ρ * ρ = 1 := AutOm.plusRefl_mul_self one_le_four
    have hρi : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
    have hconj : ρ * θ ^ k * ρ = (θ ^ k)⁻¹ := by
      have h := conj_pow (a := ρ) (b := θ) (i := k)
      rw [hρi, hρθ, inv_pow] at h
      exact h.symm
    have hsq : θ ^ k * ρ * (θ ^ k * ρ) = 1 := by
      rw [show θ ^ k * ρ * (θ ^ k * ρ) = θ ^ k * (ρ * θ ^ k * ρ) by group, hconj, mul_inv_cancel]
    refine ⟨ι * (θ ^ k * ρ), mul_mem_of_sq_mem hι (by rw [hsq]; exact one_mem _) hβ, 0, ?_⟩
    rw [pow_zero, mul_one]

end Two

theorem center_eq_bot_of_mulEquiv {H R : Type*} [Group H] [Group R] (e : H ≃* R)
    (hZ : Subgroup.center H = ⊥) : Subgroup.center R = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨h, rfl⟩ := e.surjective z
  have hh : h ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hz (e g)
  rw [hZ, Subgroup.mem_bot] at hh
  rw [hh, map_one]
  exact one_mem _

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_of_elemAbelian_mulAut (hK : Nat.card K = 2)
    (Eh : Subgroup (MulAut (OrthRest.RPlus K 4))) (hEh : IsElemAbelian 3 Eh) :
    Nat.card Eh ≤ 3 ^ 4 := by
  have hZ : Subgroup.center (OrthRest.RPlus K 4) = ⊥ := by
    obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) (n := 4) (by norm_num)
    exact center_eq_bot_of_mulEquiv (MulEquiv.ofBijective _ hbij) hZ
  have hinj := OrthRest.conj_injective hZ
  set I := ComponentClassification.OuterAutomorphisms.inner (OrthRest.RPlus K 4) with hI
  have : I.Normal := inner_normal _
  by_cases hin : Eh ≤ I
  · have hcE : Nat.card (Eh.comap (MulAut.conj : OrthRest.RPlus K 4 →* _)) = Nat.card Eh := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self hin]
      rw [Subgroup.card_map_of_injective hinj]
    rw [← hcE]
    exact OrthRest.card_le_plus (by norm_num) Nat.prime_three (by norm_num) _
      (D4Rank.isElemAbelian_comap hinj hEh)
  obtain ⟨α, hαE, hαI⟩ := IsConcreteLE.not_le_iff_exists.mp hin
  have hα3 : α ^ 3 = 1 := hEh.2 α hαE
  have : Finite (GL (Fin 4 ⊕ Fin 4) K) := Finite.of_injective
    (fun u : GL (Fin 4 ⊕ Fin 4) K => (u : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K))
    Units.val_injective
  have : Finite (MulAut (OrthRest.RPlus K 4)) :=
    Finite.of_injective (fun β : MulAut (OrthRest.RPlus K 4) => (β : OrthRest.RPlus K 4 → _))
      fun a b h => MulEquiv.ext (congrFun h)
  let e : OrthRest.RPlus K 4 ≃* Om8 K := RecipeFieldOmega.plusEquiv (K := K) (by norm_num)
  obtain ⟨θ, hθ3, hρθ, -, hgen, -, -⟩ := plusFourTrialityInput_holds K
  have h1 : Nat.card Eh ≤ 3 * Nat.card (Eh ⊓ I : Subgroup _) := by
    refine card_le_mul_inf_of_pow (c := (MulAut.congr e).symm θ) (by norm_num)
      (by rw [← map_pow, hθ3, map_one]) fun β hβ => ?_
    have hβ3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hEh.2 β hβ, map_one]
    obtain ⟨ι, ⟨y, rfl⟩, k, hk⟩ := exists_inner_mul_pow hK hρθ hgen hβ3
    refine ⟨MulAut.conj (e.symm y), ⟨_, rfl⟩, k, ?_⟩
    apply (MulAut.congr e).injective
    rw [map_mul, map_pow, MulEquiv.apply_symm_apply, hk, congr_conj, MulEquiv.apply_symm_apply]
  have h2 : Nat.card (Eh ⊓ I : Subgroup _) ≤ 9 := by
    set A := (Eh ⊓ I).comap (MulAut.conj : OrthRest.RPlus K 4 →* _) with hA
    have hcA : Nat.card A = Nat.card (Eh ⊓ I : Subgroup _) := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self (inf_le_right : Eh ⊓ I ≤ I)]
      rw [Subgroup.card_map_of_injective hinj]
    have hEI : IsElemAbelian 3 (Eh ⊓ I) :=
      ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hEh a.2.1 b.2.1)⟩⟩,
        fun x hx => hEh.2 x hx.1⟩
    have hfixR : ∀ a ∈ A, α a = a := by
      intro a ha
      have hcomm := TableB.IsElemAbelian.comm hEh hαE ha.1
      apply hinj
      have e1 : MulAut.conj (α a) = α * MulAut.conj a * α⁻¹ := by
        refine MulEquiv.ext fun x => ?_
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
          map_mul, map_inv, MulAut.apply_inv_self]
      rw [e1, hcomm, mul_inv_cancel_right]
    have hα'3 : (MulAut.congr e α) ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hα'I : MulAut.congr e α ∉ inner (Om8 K) := by
      rintro ⟨y, hy⟩
      apply hαI
      refine ⟨e.symm y, ?_⟩
      apply (MulAut.congr e).injective
      rw [congr_conj, MulEquiv.apply_symm_apply, hy]
    have hfix : ∀ x ∈ A.map e.toMonoidHom, MulAut.congr e α x = x := by
      rintro _ ⟨a, ha, rfl⟩
      change MulAut.congr e α (e a) = e a
      rw [CFSG.RankThree.PartOne.AUTSL.congr_apply_apply', hfixR a ha]
    have h9 := D4Rank.card_le_nine_of_classInput D4Rank.ggD4TrialityClassInput_holds _ hα'3
      (conjAct_ne_of_not_mem_inner hK hα'3 hα'I) _
      (D4Rank.isElemAbelian_map _ (D4Rank.isElemAbelian_comap hinj hEI)) hfix
    rw [Subgroup.card_map_of_injective e.injective] at h9
    rw [← hcA]
    exact h9
  calc Nat.card Eh ≤ 3 * 9 := h1.trans (Nat.mul_le_mul_left 3 h2)
    _ ≤ 3 ^ 4 := by norm_num

end Main

end OrthRestEnd

theorem ggOrthRestBstarD4Input_holds : GGOrthRestBstarD4Input := by
  intro K _ _ hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl (hK.trans (pow_one 2).symm)
  intro Eb Eh _ _ hr _ _ _ hEh hcardh
  exfalso
  have h1 := OrthRestEnd.card_le_of_elemAbelian_mulAut hK Eh hEh
  have h2 : 3 ^ 2 * 3 ^ 3 ≤ Nat.card Eh := (Nat.mul_le_mul_left _ hr).trans hcardh
  norm_num at h1 h2
  omega

end CFSG.StandardType
