module

public import CFSG.RankThree.SubgroupLists.MitchellNondegenerate
public import CFSG.RankThree.SubgroupLists.MitchellPairOrder

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem commute_mul_of_cliffB_eq_zero (h2 : (2 : K) ≠ 0) {d e v : Matrix V₄ V₄ K}
    (hd : d ∈ (cliffSpace : Submodule K _)) (he : e ∈ (cliffSpace : Submodule K _))
    (hv : v ∈ (cliffSpace : Submodule K _)) (hdv : cliffB d v = 0) (hev : cliffB e v = 0) :
    Commute (d * e) v := by
  have hd' := (mul_eq_neg_mul_iff h2 hd hv).mpr hdv
  have he' := (mul_eq_neg_mul_iff h2 he hv).mpr hev
  show d * e * v = v * (d * e)
  rw [Matrix.mul_assoc, he', Matrix.mul_neg, ← Matrix.mul_assoc, hd', Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

theorem exists_commute_of_isNCInv_four (h2 : (2 : K) ≠ 0) {d₁ e₁ d₂ e₂ : GL V₄ K}
    (hd₁ : IsNCInv d₁) (he₁ : IsNCInv e₁) (hd₂ : IsNCInv d₂) (he₂ : IsNCInv e₂) :
    ∃ v ∈ (cliffSpace : Submodule K _), v ≠ 0 ∧
      ((d₁ * e₁ : GL V₄ K) : Matrix V₄ V₄ K) * v = v * ((d₁ * e₁ : GL V₄ K) : Matrix V₄ V₄ K) ∧
      ((d₂ * e₂ : GL V₄ K) : Matrix V₄ V₄ K) * v = v * ((d₂ * e₂ : GL V₄ K) : Matrix V₄ V₄ K) := by
  have hM : ∀ {w : GL V₄ K}, IsNCInv w → (w : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) :=
    fun hw => (mem_cliffSpace_of_involution h2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).1
  obtain ⟨v, hvM, hv0, h₁, h₂, h₃, h₄⟩ :=
    exists_ne_zero_orth_four h2 (hM hd₁) (hM he₁) (hM hd₂) (hM he₂)
  refine ⟨v, hvM, hv0, ?_, ?_⟩
  · rw [Units.val_mul]
    exact (commute_mul_of_cliffB_eq_zero h2 (hM hd₁) (hM he₁) hvM
      ((cliffB_comm _ _).trans h₁) ((cliffB_comm _ _).trans h₂)).eq
  · rw [Units.val_mul]
    exact (commute_mul_of_cliffB_eq_zero h2 (hM hd₂) (hM he₂) hvM
      ((cliffB_comm _ _).trans h₃) ((cliffB_comm _ _).trans h₄)).eq

theorem mul_comm_of_conj_commute {Ω : Type*} [Group Ω] [IsSimpleGroup Ω] {ω : Ω} (hω : ω ≠ 1)
    (hc : ∀ a b : Ω, a * ω * a⁻¹ * (b * ω * b⁻¹) = b * ω * b⁻¹ * (a * ω * a⁻¹)) (x y : Ω) :
    x * y = y * x := by
  have hcomm : (Group.conjugatesOfSet ({ω} : Set Ω)).Pairwise Commute := by
    intro u hu w hw _
    obtain ⟨a, ha, hau⟩ := Group.mem_conjugatesOfSet_iff.mp hu
    obtain ⟨b, hb, hbw⟩ := Group.mem_conjugatesOfSet_iff.mp hw
    rw [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    obtain ⟨c, rfl⟩ := isConj_iff.mp hau
    obtain ⟨d, rfl⟩ := isConj_iff.mp hbw
    exact hc c d
  have htop : Subgroup.normalClosure ({ω} : Set Ω) = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left fun h =>
      hω (Subgroup.normalClosure_eq_bot_iff.mp h (Set.mem_singleton ω))
  have hC : IsMulCommutative (Subgroup.normalClosure ({ω} : Set Ω)) :=
    Subgroup.isMulCommutative_closure hcomm
  rw [htop] at hC
  exact congrArg Subtype.val (hC.is_comm.comm ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)

private theorem neg_one_ne_one_gl (h2 : (2 : K) ≠ 0) : (-1 : GL V₄ K) ≠ 1 := fun h =>
  one_ne_neg_one_of_two h2 (by
    simpa using congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0)) h.symm)

theorem false_of_conj_sq_comm (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {x : G} (hx4 : (x : GL V₄ K) ^ 4 = -1)
    (hc : ∀ a b : G, ((a * x * a⁻¹ : G) : GL V₄ K) ^ 2 * ((b * x * b⁻¹ : G) : GL V₄ K) ^ 2 =
        ((b * x * b⁻¹ : G) : GL V₄ K) ^ 2 * ((a * x * a⁻¹ : G) : GL V₄ K) ^ 2 ∨
      ((a * x * a⁻¹ : G) : GL V₄ K) ^ 2 * ((b * x * b⁻¹ : G) : GL V₄ K) ^ 2 =
        -(((b * x * b⁻¹ : G) : GL V₄ K) ^ 2 * ((a * x * a⁻¹ : G) : GL V₄ K) ^ 2)) : False := by
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hω : (QuotientGroup.mk (x ^ 2) : G ⧸ Subgroup.center G) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hZ hneg, Subgroup.coe_pow]
    have hx4' : ((x : GL V₄ K) ^ 2) ^ 2 = -1 := by rw [← pow_mul]; exact hx4
    rintro (h | h)
    · rw [h, one_pow] at hx4'
      exact neg_one_ne_one_gl h2 hx4'.symm
    · rw [h, neg_one_sq] at hx4'
      exact neg_one_ne_one_gl h2 hx4'.symm
  have e : ∀ c : G, (QuotientGroup.mk c : G ⧸ Subgroup.center G) * QuotientGroup.mk (x ^ 2) *
      (QuotientGroup.mk c)⁻¹ = QuotientGroup.mk ((c * x * c⁻¹) ^ 2) := by
    intro c
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, conj_pow]
  obtain ⟨a, b, hab⟩ := hq.2.2
  refine hab (mul_comm_of_conj_commute hω (fun a b => ?_) a b)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [e, e, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff hZ hneg]
  have h := hc a b
  simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h ⊢
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem false_of_forall_sq_mul_sq (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G)
    (hSQ : ∀ {d₁ e₁ d₂ e₂ : GL V₄ K}, d₁ ∈ G → e₁ ∈ G → d₂ ∈ G → e₂ ∈ G → IsNCInv d₁ →
      IsNCInv e₁ → IsNCInv d₂ → IsNCInv e₂ →
      cliffB (d₁ : Matrix V₄ V₄ K) (e₁ : Matrix V₄ V₄ K) ^ 2 = 2⁻¹ →
      cliffB (d₂ : Matrix V₄ V₄ K) (e₂ : Matrix V₄ V₄ K) ^ 2 = 2⁻¹ →
      (d₁ * e₁) ^ 2 * (d₂ * e₂) ^ 2 = (d₂ * e₂) ^ 2 * (d₁ * e₁) ^ 2 ∨
        (d₁ * e₁) ^ 2 * (d₂ * e₂) ^ 2 = -((d₂ * e₂) ^ 2 * (d₁ * e₁) ^ 2))
    {t : G} (ht : IsNCInv (t : GL V₄ K)) (g : G)
    (hβ : cliffB ((t : GL V₄ K) : Matrix V₄ V₄ K)
      (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ^ 2 = 2⁻¹) : False := by
  set s : G := g * t * g⁻¹
  have hs : IsNCInv (s : GL V₄ K) := conj_isNCInv hGS ht g
  have hM : ∀ {w : GL V₄ K}, IsNCInv w → (w : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) :=
    fun hw => (mem_cliffSpace_of_involution h2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).1
  have hconj : ∀ a : G, ((a * (t * s) * a⁻¹ : G) : GL V₄ K) =
      ((a * t * a⁻¹ : G) : GL V₄ K) * ((a * s * a⁻¹ : G) : GL V₄ K) := by
    intro a
    rw [← Subgroup.coe_mul]
    congr 1
    group
  have hB : ∀ a : G, cliffB (((a * t * a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)
      (((a * s * a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) ^ 2 = 2⁻¹ := by
    intro a
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [cliffB_conj h2 (a : GL V₄ K) (hM ht) (hM hs)]
    exact hβ
  refine false_of_conj_sq_comm h2 hq hZ hneg (x := t * s) ?_ fun a b => ?_
  · rw [Subgroup.coe_mul]
    exact pow_four_eq_neg_one_of_sq_eq_half h2 ht hs hβ
  · rw [hconj a, hconj b]
    exact hSQ (a * t * a⁻¹).2 (a * s * a⁻¹).2 (b * t * b⁻¹).2 (b * s * b⁻¹).2
      (conj_isNCInv hGS ht a) (conj_isNCInv hGS hs a) (conj_isNCInv hGS ht b)
      (conj_isNCInv hGS hs b) (hB a) (hB b)

end CFSG.RankThree.SubgroupLists
