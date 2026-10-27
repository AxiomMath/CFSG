module

public import CFSG.RankThree.GF2n.Stroth80.Sec8TypeCount

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

section Acts

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] def Sec8ActsAs (M₀ : Tim79.QuadModel Q Z K γ) (m : G) (T : M₀.E ≃ₗ[K] M₀.E) : Prop :=
  ∀ y ∈ Q, M₀.π (m * y * m⁻¹) = T (M₀.π y)

variable {M₀ : Tim79.QuadModel Q Z K γ}

theorem Sec8ActsAs.mul {M : Subgroup G} (hQ : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q) {m m' : G}
    (hm' : m' ∈ M) {T T' : M₀.E ≃ₗ[K] M₀.E} (h : Sec8ActsAs M₀ m T) (h' : Sec8ActsAs M₀ m' T') :
    Sec8ActsAs M₀ (m * m') (T * T') := by
  intro y hy
  have e : m * m' * y * (m * m')⁻¹ = m * (m' * y * m'⁻¹) * m⁻¹ := by group
  rw [e, h _ (hQ m' hm' y hy), h' y hy]
  rfl

theorem Sec8ActsAs.inv {M : Subgroup G} (hQ : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q) {m : G}
    (hm : m ∈ M) {T : M₀.E ≃ₗ[K] M₀.E} (h : Sec8ActsAs M₀ m T) : Sec8ActsAs M₀ m⁻¹ T⁻¹ := by
  intro y hy
  have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ Q := hQ m⁻¹ (M.inv_mem hm) y hy
  have key := h _ hy'
  rw [show m * (m⁻¹ * y * m⁻¹⁻¹) * m⁻¹ = y by group] at key
  show M₀.π (m⁻¹ * y * m⁻¹⁻¹) = T.symm (M₀.π y)
  rw [key]
  simp

theorem Sec8ActsAs.of_mem_Q {q : G} (hq : q ∈ Q) : Sec8ActsAs M₀ q 1 := by
  intro y hy
  rw [Tim79.QuadModel.pi_conj_self (M₀ := M₀) hq hy]
  rfl

theorem Sec8ActsAs.unique {m : G} {T T' : M₀.E ≃ₗ[K] M₀.E} (h : Sec8ActsAs M₀ m T)
    (h' : Sec8ActsAs M₀ m T') : T = T' := by
  refine LinearEquiv.ext fun e => ?_
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
  rw [← h y hy, ← h' y hy]

end Acts

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

section Pieces

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] {γ : G → K}

theorem sec8_img_inf_eq_zero (M₀ : Tim79.QuadModel Q Z K γ) {S S' : Subgroup G} (hZS' : Z ≤ S')
    (h : S ⊓ S' ≤ Z) {e : M₀.E} (he : e ∈ M₀.img S) (he' : e ∈ M₀.img S') : e = 0 := by
  obtain ⟨a, haS, haQ, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp he
  obtain ⟨b, hbS', hbQ, hb⟩ := (Tim79.QuadModel.mem_img M₀).mp he'
  have hz : b⁻¹ * a ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hbQ haQ).mp hb
  have haS' : a ∈ S' := by
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact S'.mul_mem hbS' (hZS' hz)
  exact (M₀.π_ker a haQ).mpr (h ⟨haS, haS'⟩)

theorem sec8_img_sup_le (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B) {e : M₀.E}
    (he : e ∈ M₀.img (Z ⊔ B)) : e ∈ M₀.img B := by
  obtain ⟨y, hy, hyQ, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp he
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hu))
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN
    (by rwa [sup_comm] at hy)
  have hbQ : b ∈ Q := hc.le hb
  have hzQ : z ∈ Q := hc.hyp.Z_normal.1 hz
  rw [M₀.π_mul b hbQ z hzQ, (M₀.π_ker z hzQ).mpr hz, add_zero]
  exact Tim79.QuadModel.pi_mem_img M₀ hb hbQ

theorem sec8_card_img_B_le [Finite K] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) : Nat.card ↥(M₀.img B) ≤ Nat.card K := by
  obtain ⟨g, hg⟩ := hc.conj
  have hne : conjSubgroup g Z ≠ Z := hg ▸ hc.ne
  have hle : conjSubgroup g Z ≤ Q := hg ▸ hc.le
  obtain ⟨e, -, hline⟩ := hD.line g hne hle
  rw [← hg] at hline
  refine Nat.card_le_card_of_surjective
    (fun s : K => (⟨s • e, (hline _).mpr ⟨s, rfl⟩⟩ : ↥(M₀.img B))) ?_
  rintro ⟨v, hv⟩
  obtain ⟨s, rfl⟩ := (hline v).mp hv
  exact ⟨s, rfl⟩

theorem sec8_bridge_S_iso (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) :
    ∀ s ∈ M₀.img (Q ⊓ QB B), ∀ s' ∈ M₀.img (Q ⊓ QB B), M₀.B s s' = 0 := by
  have hsub : Q ⊓ QB B ≤ Q := inf_le_left
  refine (Tim79.QuadModel.commute_iff M₀ hD.reg hsub hsub).mp (fun a ha b hb => ?_)
  have h1 : ⁅a, b⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V (Subgroup.mem_inf.mp ha).1
    (Subgroup.mem_inf.mp hb).1
  have h2 : ⁅a, b⁆ ∈ B := hc.comm_QB_le_B (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp hb).2
  have h3 : ⁅a, b⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem sec8_bridge_S_card [Finite K] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Nat.card Q = Nat.card Z ^ (2 * n + 1))
    (hcard : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1)) :
    Nat.card ↥(M₀.img (Q ⊓ QB B)) * Nat.card ↥(M₀.img (Q ⊓ QB B)) = Nat.card M₀.E := by
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have hZS : Z ≤ Q ⊓ QB B := le_inf hc.hyp.Z_normal.1 hc.Z_le_QB.1
  have h1 := M₀.card_eq (inf_le_left : Q ⊓ QB B ≤ Q) hZS
  have hS : Nat.card ↥(M₀.img (Q ⊓ QB B)) = Nat.card Z ^ n := by
    rw [hcard, pow_succ'] at h1
    exact (Nat.eq_of_mul_eq_mul_left hzpos h1).symm
  haveI : Finite M₀.E := by
    haveI : Module.Finite K M₀.E := M₀.fin
    exact Module.finite_of_finite K
  have himgQ : M₀.img Q = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
    exact (Tim79.QuadModel.mem_img M₀).mpr ⟨x, hxQ, hxQ, hx⟩
  have hQE : Nat.card Q = Nat.card Z * Nat.card M₀.E := by
    rw [M₀.card_eq le_rfl hD.reg.V_le, himgQ, AddSubgroup.card_top]
  have hE : Nat.card M₀.E = Nat.card Z ^ (2 * n) := by
    rw [hw, pow_succ'] at hQE
    exact (Nat.eq_of_mul_eq_mul_left hzpos hQE).symm
  rw [hS, hE, ← pow_add]
  congr 1
  omega

theorem sec8_range_iff_img [Finite K] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {x : G} (hxM : x ∈ M) (hx2 : x ^ 2 ∈ Q)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : Sec8ActsAs M₀ x T) (e : M₀.E) :
    e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ↔ e ∈ M₀.img (Ut Q Z x) := by
  rw [sec8_img_Ut_iff hc hD hxM hx2 hT e, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, by rw [← hf]; simp⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, by rw [hf]; simp⟩

theorem sec8_bridge_dim [Finite K] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {x : G} (hxM : x ∈ M) (hx2 : x ^ 2 ∈ Q)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : Sec8ActsAs M₀ x T) (hUQ : Ut Q Z x ≤ Q)
    (hcard : Nat.card ↥(Ut Q Z x) = Nat.card Z ^ 5) :
    Nat.card ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = Nat.card K ^ 4 := by
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have h1 : Nat.card ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) =
      Nat.card ↥(M₀.img (Ut Q Z x)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => sec8_range_iff_img M₀ hc hD hxM hx2 hT e)
  have h2 := M₀.card_eq hUQ (le_sup_right : Z ≤ Ut Q Z x)
  rw [hcard, pow_succ' (Nat.card Z) 4] at h2
  rw [h1, hD.card]
  exact (Nat.eq_of_mul_eq_mul_left hzpos h2).symm

theorem sec8_bridge_disj [Finite K] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {x x' : G} (hxM : x ∈ M) (hx2 : x ^ 2 ∈ Q)
    (hx'M : x' ∈ M) (hx'2 : x' ^ 2 ∈ Q) {T T' : M₀.E ≃ₗ[K] M₀.E} (hT : Sec8ActsAs M₀ x T)
    (hT' : Sec8ActsAs M₀ x' T') (hinter : Ut Q Z x ⊓ Ut Q Z x' ≤ Z) (e : M₀.E)
    (he : e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))
    (he' : e ∈ LinearMap.range ((T' : M₀.E →ₗ[K] M₀.E) - 1)) : e = 0 :=
  sec8_img_inf_eq_zero M₀ (le_sup_right : Z ≤ Ut Q Z x') hinter
    ((sec8_range_iff_img M₀ hc hD hxM hx2 hT e).mp he)
    ((sec8_range_iff_img M₀ hc hD hx'M hx'2 hT' e).mp he')

theorem sec8_involution_range [CharP K 2] {E : Type} [AddCommGroup E] [Module K E]
    {T : E ≃ₗ[K] E} (hTT : T * T = 1) (f : E) : T (T f - f) = T f - f := by
  have hTf : T (T f) = f := by
    have := congrArg (fun S : E ≃ₗ[K] E => S f) hTT
    simpa using this
  have h2 : ∀ v : E, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  rw [map_sub, hTf]
  have e1 : f - T f - (T f - f) = (f + f) - (T f + T f) := by abel
  rw [h2 f, h2 (T f), sub_zero] at e1
  exact sub_eq_zero.mp e1

theorem sec8_bridge_aa [Finite K] [CharP K 2] (M₀ : Tim79.QuadModel Q Z K γ) (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {x x' e₀ : G} (hxM : x ∈ M) (hx2 : x ^ 2 ∈ Q)
    (hx'M : x' ∈ M) (he₀M : e₀ ∈ M) (hxe : x' = e₀ * x) {T T' : M₀.E ≃ₗ[K] M₀.E}
    (hT : Sec8ActsAs M₀ x T) (hT' : Sec8ActsAs M₀ x' T') (hTT : T * T = 1) {V₁ W₁ : Subgroup G}
    (hZV₁ : Z ≤ V₁) (hW : ∀ w ∈ Ut Q Z x, w ∈ W₁) (he₀ : ∀ w ∈ W₁, ⁅e₀, w⁆ ∈ V₁)
    (hinter : V₁ ⊓ Ut Q Z x' ≤ Z) (e : M₀.E)
    (he : e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :
    ((T' : M₀.E →ₗ[K] M₀.E) - 1) e = 0 := by
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp he
  have hTe : T (T f - f) = T f - f := sec8_involution_range hTT f
  have heimg := (sec8_range_iff_img M₀ hc hD hxM hx2 hT _).mp ⟨f, rfl⟩
  obtain ⟨w, hwU, hwQ, hwe⟩ := (Tim79.QuadModel.mem_img M₀).mp heimg
  have hwe' : M₀.π w = T f - f := by simpa using hwe
  have hxwQ : x * w * x⁻¹ ∈ Q := hQn x hxM w hwQ
  have hcQ : ⁅x, w⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hxwQ (Q.inv_mem hwQ)
  have hxwZ : ⁅x, w⁆ ∈ Z := by
    refine (M₀.π_ker _ hcQ).mp ?_
    rw [sec8_pi_comm M₀ hwQ hxwQ (hT w hwQ), hwe', hTe, sub_self]
  have hmemV₁ : ⁅x', w⁆ ∈ V₁ := by
    have e1 : ⁅x', w⁆ = e₀ * ⁅x, w⁆ * e₀⁻¹ * ⁅e₀, w⁆ := by
      rw [hxe]
      simp only [commutatorElement_def]
      group
    rw [e1]
    have hz : e₀ * ⁅x, w⁆ * e₀⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 he₀M) _).mp hxwZ
    exact V₁.mul_mem (hZV₁ hz) (he₀ w (hW w hwU))
  have hmemUt : ⁅x', w⁆ ∈ Ut Q Z x' := sec8_comm_mem_Ut hwQ
  have hx'wQ : x' * w * x'⁻¹ ∈ Q := hQn x' hx'M w hwQ
  have hc'Q : ⁅x', w⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hx'wQ (Q.inv_mem hwQ)
  have hzero : M₀.π ⁅x', w⁆ = 0 :=
    sec8_img_inf_eq_zero M₀ (le_sup_right : Z ≤ Ut Q Z x') hinter
      (Tim79.QuadModel.pi_mem_img M₀ hmemV₁ hc'Q) (Tim79.QuadModel.pi_mem_img M₀ hmemUt hc'Q)
  rw [sec8_pi_comm M₀ hwQ hx'wQ (hT' w hwQ)] at hzero
  have hfin : T' (T f - f) - (T f - f) = 0 := by rw [← hwe']; exact hzero
  simpa using hfin

end Pieces

end

end CFSG.RankThree.GF2n.Stroth80
