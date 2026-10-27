module

public import CFSG.RankThree.PartOne.K133.SimpleSL2
public import CFSG.RankThree.PartOne.K133.ProjUnip3

public section

namespace CFSG.RankThree.PartOne.K133

open scoped commutatorElement

theorem commutator_sup_le_of_normalizes {G : Type*} [Group G] (H D : Subgroup G)
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHD : H ≤ Subgroup.normalizer (D : Set G)) :
    ⁅H ⊔ D, H ⊔ D⁆ ≤ D := by
  have hMN : H ⊔ D ≤ Subgroup.normalizer (D : Set G) := sup_le hHD Subgroup.le_normalizer
  have hnorm : ∀ m ∈ H ⊔ D, ∀ d ∈ D, m * d * m⁻¹ ∈ D := fun m hm d hd =>
    (Subgroup.mem_normalizer_iff.1 (hMN hm) d).1 hd
  have hnorm' : ∀ m ∈ H ⊔ D, ∀ d ∈ D, m⁻¹ * d * m ∈ D := fun m hm d hd => by
    simpa using hnorm m⁻¹ (Subgroup.inv_mem _ hm) d hd
  have step1 : ∀ a ∈ H, ∀ b ∈ H ⊔ D, ⁅a, b⁆ ∈ D := by
    intro a ha b hb
    have hb' := hb
    rw [Subgroup.sup_eq_closure] at hb'
    induction hb' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [commutatorElement_def, hHc a ha x hx]
        simp
      · exact D.mul_mem (hnorm a ((le_sup_left : H ≤ H ⊔ D) ha) x hx) (D.inv_mem hx)
    | one => simp [commutatorElement_def]
    | mul x y hx hy ihx ihy =>
      have hxM : x ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
      have hyM : y ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
      have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem (ihx hxM) (hnorm x hxM _ (ihy hyM))
    | inv x hx ihx =>
      have hxM : x ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
      have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hnorm' x hxM _ (D.inv_mem (ihx hxM))
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' := ha
  rw [Subgroup.sup_eq_closure] at ha'
  induction ha' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact step1 x hx b hb
    · have : ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact D.mul_mem hx (hnorm b hb _ (D.inv_mem hx))
  | one => simp [commutatorElement_def]
  | mul x y hx hy ihx ihy =>
    have hxM : x ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
    have hyM : y ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
    have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact D.mul_mem (hnorm x hxM _ (ihy hyM)) (ihx hxM)
  | inv x hx ihx =>
    have hxM : x ∈ H ⊔ D := by rwa [Subgroup.sup_eq_closure]
    have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hnorm' x hxM _ (D.inv_mem (ihx hxM))

theorem exists_projection_hom {G : Type*} [Group G] (P Q M : Subgroup G) (hMP : M ≤ P)
    (hQn : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hfac : ∀ g ∈ P, ∃! qm : G × G, qm.1 ∈ Q ∧ qm.2 ∈ M ∧ g = qm.1 * qm.2) :
    ∃ π : P →* M, ∀ g : P, ∃ q ∈ Q, (g : G) = q * ((π g : M) : G) := by
  choose f hf using fun g : P => hfac g g.2
  have hf' : ∀ g : P, (f g).1 ∈ Q ∧ (f g).2 ∈ M ∧ (g : G) = (f g).1 * (f g).2 := fun g => (hf g).1
  have huniq : ∀ (g : P) (y : G × G), y.1 ∈ Q → y.2 ∈ M → (g : G) = y.1 * y.2 → y = f g :=
    fun g y h1 h2 h3 => (hf g).2 y ⟨h1, h2, h3⟩
  have hmul : ∀ g g' : P, (f (g * g')).2 = (f g).2 * (f g').2 := by
    intro g g'
    obtain ⟨hq, hm, hgg⟩ := hf' g
    obtain ⟨hq', hm', hgg'⟩ := hf' g'
    have h := huniq (g * g') ((f g).1 * ((f g).2 * (f g').1 * (f g).2⁻¹), (f g).2 * (f g').2)
      (Q.mul_mem hq (hQn _ (hMP hm) _ hq')) (M.mul_mem hm hm') (by
        rw [Subgroup.coe_mul, hgg, hgg']
        simp only [mul_assoc]
        group)
    exact (congrArg Prod.snd h).symm
  have hone : (f 1).2 = 1 := by
    have h := huniq 1 (1, 1) Q.one_mem M.one_mem (by simp)
    exact (congrArg Prod.snd h).symm
  refine ⟨{ toFun := fun g => ⟨(f g).2, (hf' g).2.1⟩
            map_one' := Subtype.ext hone
            map_mul' := fun g g' => Subtype.ext (hmul g g') }, fun g => ?_⟩
  exact ⟨(f g).1, (hf' g).1, (hf' g).2.2⟩

theorem false_of_simple_in_semidirect {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P Q M D : Subgroup G) (hMP : M ≤ P)
    (hQn : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hfac : ∀ g ∈ P, ∃! qm : G × G, qm.1 ∈ Q ∧ qm.2 ∈ M ∧ g = qm.1 * qm.2) (hQp : IsPGroup p Q)
    (hcomm : ⁅M, M⁆ ≤ D) {Kb : Type} [Group Kb] [Finite Kb] [IsSimpleGroup Kb]
    (hKn : ∃ a b : Kb, a * b ≠ b * a) (ι : Kb →* G) (hι : Function.Injective ι) (hιP : ∀ k, ι k ∈ P)
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (δ : D →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hδ : Function.Injective δ) : False := by
  classical
  obtain ⟨π, hπ⟩ := exists_projection_hom P Q M hMP hQn hfac
  let κ : Kb →* P := ι.codRestrict P hιP
  let ψ : Kb →* G := M.subtype.comp (π.comp κ)
  have hker : ∀ k, ψ k = 1 → ι k ∈ Q := by
    intro k hk
    obtain ⟨q, hq, hqe⟩ := hπ (κ k)
    have h1 : ((π (κ k) : M) : G) = 1 := hk
    rw [h1, mul_one] at hqe
    have : (ι k : G) = q := hqe
    rw [this]
    exact hq
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    by_contra hk1
    have hkerN : ψ.ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exfalso
        apply hk1
        have : k ∈ ψ.ker := hk
        rw [h] at this
        exact this
      · exact h
    have hall : ∀ k, ι k ∈ Q := fun k => hker k (by
      have : k ∈ ψ.ker := by rw [hkerN]; exact Subgroup.mem_top k
      exact this)
    have hKp : IsPGroup p Kb := by
      intro k
      obtain ⟨n, hn⟩ := hQp ⟨ι k, hall k⟩
      refine ⟨n, hι ?_⟩
      have := congrArg Subtype.val hn
      simpa using this
    have hnil : Group.IsNilpotent Kb := hKp.isNilpotent
    have hsol : Group.IsSolvable Kb := inferInstance
    obtain ⟨u, v, huv⟩ := hKn
    exact huv ((IsSimpleGroup.comm_iff_isSolvable).2 hsol u v)
  have hKperf : Group.IsPerfect Kb := isPerfect_of_simple_nonabelian hKn
  have hψD : ∀ k, ψ k ∈ D := by
    intro k
    have hk : k ∈ (⁅(⊤ : Subgroup Kb), ⊤⁆ : Subgroup Kb) := by
      have h : (⁅(⊤ : Subgroup Kb), ⊤⁆ : Subgroup Kb) = ⊤ := hKperf.commutator_eq_top
      rw [h]
      exact Subgroup.mem_top k
    have h1 : ψ k ∈ (⁅(⊤ : Subgroup Kb), ⊤⁆ : Subgroup Kb).map ψ := Subgroup.mem_map_of_mem ψ hk
    rw [Subgroup.map_commutator] at h1
    refine hcomm (Subgroup.commutator_mono ?_ ?_ h1)
    · rintro _ ⟨x, -, rfl⟩
      exact (π (κ x)).2
    · rintro _ ⟨x, -, rfl⟩
      exact (π (κ x)).2
  let ψ' : Kb →* D := ψ.codRestrict D hψD
  have hψ' : Function.Injective ψ' := fun a b h => hinj (by have := congrArg Subtype.val h; exact this)
  exact false_of_simple_nonabelian_hom_sl2 h2 hKn (δ.comp ψ') (hδ.comp hψ')

end CFSG.RankThree.PartOne.K133
