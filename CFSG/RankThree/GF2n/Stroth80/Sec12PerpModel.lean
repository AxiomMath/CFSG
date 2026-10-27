module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Perp
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.eq_of_le_sup_Z (hc : Ctx M Q Z B) {N : Subgroup G} (hNQ : N ≤ Q)
    (hNn : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) (hQN : Q ≤ N ⊔ Z) : N = Q := by
  have H := hc.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hdec : ((N ⊔ Z : Subgroup G) : Set G) = (N : Set G) * (Z : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right N Z
      (fun u hu => H.Z_normal.2 (H.Q_normal.1 (hNQ hu)))
  have hBZ : ¬ B ≤ Z := by
    intro hle
    obtain ⟨g, hg⟩ := hc.conj
    exact hc.ne (Subgroup.eq_of_le_of_card_ge hle (by rw [hg, card_conjSubgroup]))
  obtain ⟨a, haB, haZ⟩ := SetLike.not_le_iff_exists.mp hBZ
  have haQ : a ∈ Q := hc.le haB
  obtain ⟨c, hcQ, hca⟩ : ∃ c ∈ Q, c * a ≠ a * c := by
    by_contra hcon
    push Not at hcon
    apply haZ
    rw [H.hZ, cen_eq]
    exact Subgroup.mem_inf.mpr ⟨haQ, Subgroup.mem_centralizer_iff.mpr fun c hc => (hcon c hc)⟩
  have hmemNZ : ∀ x ∈ Q, ∃ x' ∈ N, ∃ z ∈ Z, x' * z = x := fun x hx => by
    have : x ∈ (N : Set G) * (Z : Set G) := by rw [← hdec]; exact hQN hx
    obtain ⟨x', hx', z, hz, rfl⟩ := Set.mem_mul.mp this
    exact ⟨x', hx', z, hz, rfl⟩
  obtain ⟨a', ha', z₁, hz₁, rfl⟩ := hmemNZ a haQ
  obtain ⟨c', hc', z₂, hz₂, rfl⟩ := hmemNZ c hcQ
  have ha'Q := hNQ ha'
  have hc'Q := hNQ hc'
  have hcomm : ⁅a' * z₁, c' * z₂⁆ = ⁅a', c'⁆ := by
    have e1 := Smith81.Z_central H hz₁ hc'Q
    have e3 := Smith81.Z_central H hz₁ (hZQ hz₂)
    simp only [commutatorElement_def, mul_inv_rev]
    calc a' * z₁ * (c' * z₂) * (z₁⁻¹ * a'⁻¹) * (z₂⁻¹ * c'⁻¹)
        = a' * (z₁ * c') * z₂ * z₁⁻¹ * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by group
      _ = a' * c' * a'⁻¹ * c'⁻¹ := by
        rw [e1]
        have e4 : z₂ * a'⁻¹ = a'⁻¹ * z₂ := by
          have := Smith81.Z_central H hz₂ (Q.inv_mem ha'Q); exact this
        calc a' * (c' * z₁) * z₂ * z₁⁻¹ * a'⁻¹ * z₂⁻¹ * c'⁻¹
            = a' * c' * (z₁ * z₂ * z₁⁻¹) * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by group
          _ = a' * c' * z₂ * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by
            rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [e3]; group]
          _ = a' * c' * a'⁻¹ * c'⁻¹ := by rw [mul_assoc (a' * c') z₂, e4]; group
  have hk1 : ⁅a', c'⁆ ≠ 1 := by
    rw [← hcomm]
    intro h
    exact hca (by rw [commutatorElement_eq_one_iff_mul_comm] at h; exact h.symm)
  have hkZ : ⁅a', c'⁆ ∈ Z := Smith81.comm_mem_Z H ha'Q hc'Q
  have hkN : ⁅a', c'⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem ha' hc') (N.inv_mem ha')) (N.inv_mem hc')
  have hZN : Z ≤ N := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact N.one_mem
    obtain ⟨m, hm, hmz⟩ := Smith81.Z_isConj H hkZ hk1 hz hz1
    rw [← hmz]; exact hNn m hm _ hkN
  exact le_antisymm hNQ (hQN.trans (sup_le le_rfl hZN))

section Model

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.smul_mem_img_Lgen (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) (κ : K)
    {e : M₀.E} (he : e ∈ M₀.img (Lgen M B)) : κ • e ∈ M₀.img (Lgen M B) := by
  let T : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∀ κ : K, ∃ x' ∈ Lgen M B, M₀.π x' = κ • M₀.π x}
      mul_mem' := by
        rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
        refine ⟨Q.mul_mem haQ hbQ, fun κ => ?_⟩
        obtain ⟨a', ha', haπ⟩ := ha κ
        obtain ⟨b', hb', hbπ⟩ := hb κ
        refine ⟨a' * b', (Lgen M B).mul_mem ha' hb', ?_⟩
        rw [M₀.π_mul _ (hc.Lgen_le_Q ha') _ (hc.Lgen_le_Q hb'), haπ, hbπ,
          M₀.π_mul _ haQ _ hbQ, smul_add]
      one_mem' := by
        refine ⟨Q.one_mem, fun κ => ⟨1, (Lgen M B).one_mem, ?_⟩⟩
        rw [Tim79.QuadModel.pi_one M₀, smul_zero]
      inv_mem' := by
        rintro a ⟨haQ, ha⟩
        refine ⟨Q.inv_mem haQ, fun κ => ?_⟩
        obtain ⟨a', ha', haπ⟩ := ha κ
        refine ⟨a'⁻¹, (Lgen M B).inv_mem ha', ?_⟩
        rw [Tim79.QuadModel.pi_inv M₀ (hc.Lgen_le_Q ha'), Tim79.QuadModel.pi_inv M₀ haQ, haπ,
          smul_neg] }
  have hgen : Lgen M B ≤ T := by
    refine iSup₂_le fun m hm u hu => ?_
    have hC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
    obtain ⟨b', -, -, hB', -⟩ := hC.dictB h
    have huQ : u ∈ Q := hC.le hu
    refine ⟨huQ, fun κ => ?_⟩
    obtain ⟨s, hs⟩ := (hB' _).mp (M₀.pi_mem_img hu huQ)
    obtain ⟨u', hu', -, hu'π⟩ :=
      (hB' (κ • M₀.π u)).mpr ⟨κ * s, by rw [hs, smul_smul]⟩
    exact ⟨u', le_iSup₂_of_le (f := fun (m : G) (_ : m ∈ M) => conjSubgroup m B) m hm
      le_rfl hu', hu'π⟩
  obtain ⟨x, hxN, hxQ, rfl⟩ := he
  obtain ⟨x', hx', hx'π⟩ := (hgen hxN).2 κ
  exact ⟨x', hx', hc.Lgen_le_Q hx', hx'π⟩

@[expose] def PerpSub (M₀ : Tim79.QuadModel Q Z K γ) (N : Subgroup G) : Submodule K M₀.E where
  carrier := {e | ∀ n ∈ N, M₀.B e (M₀.π n) = 0}
  add_mem' := fun {a b} ha hb n hn => by
    rw [map_add, LinearMap.add_apply, ha n hn, hb n hn, add_zero]
  zero_mem' := fun n _ => by simp
  smul_mem' := fun c e he n hn => by
    rw [map_smul, LinearMap.smul_apply, he n hn, smul_zero]

theorem Ctx.mem_img_PerpB_iff (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) (e : M₀.E) :
    e ∈ M₀.img (PerpB M Q B) ↔ e ∈ PerpSub M₀ (Lgen M B) := by
  constructor
  · rintro ⟨x, hx, hxQ, rfl⟩ n hn
    exact (Tim79.QuadModel.comm_iff_B M₀ h.reg hxQ (hc.Lgen_le_Q hn)).mp
      (Subgroup.mem_centralizer_iff.mp hx.2 n hn).symm
  · intro he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    refine ⟨x, ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩, hxQ, rfl⟩
    refine (Tim79.QuadModel.comm_iff_B M₀ h.reg (hc.Lgen_le_Q hn) hxQ).mpr ?_
    rw [Tim79.QuadModel.B_comm, he n hn, neg_zero]

theorem Ctx.card_PerpB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    Nat.card (PerpB M Q B) =
      Nat.card Z * Nat.card K ^ Module.finrank K (PerpSub M₀ (Lgen M B)) := by
  rw [M₀.card_eq PerpB_le_Q hc.Z_le_PerpB]
  congr 1
  rw [← Module.natCard_eq_pow_finrank]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e => hc.mem_img_PerpB_iff h e)

theorem Ctx.two_le_finrank_PerpSub (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (hne : PerpB M Q B ≠ Z) : 2 ≤ Module.finrank K (PerpSub M₀ (Lgen M B)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp (Nat.le_of_lt_succ hlt)
  have hxw : ∀ x ∈ PerpB M Q B, ∃ c : K, c • (w : M₀.E) = M₀.π x := fun x hx => by
    obtain ⟨c, hcx⟩ := hw ⟨M₀.π x, (hc.mem_img_PerpB_iff h _).mp (M₀.pi_mem_img hx hx.1)⟩
    exact ⟨c, congrArg Subtype.val hcx⟩
  have hcomm : IsMulCommutative (PerpB M Q B) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨s, hs⟩ := hxw a a.2
    obtain ⟨t, ht⟩ := hxw b b.2
    refine (Tim79.QuadModel.comm_iff_B M₀ h.reg (PerpB_le_Q a.2) (PerpB_le_Q b.2)).mpr ?_
    rw [← hs, ← ht, map_smul, map_smul, LinearMap.smul_apply, M₀.alt, smul_zero, smul_zero]
  have hMU : M ≤ Subgroup.normalizer ((PerpB M Q B : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hc.PerpB_conj hm hx, fun hx => ?_⟩
    have := hc.PerpB_conj (M.inv_mem hm) hx
    simpa [mul_assoc] using this
  have hmax := hc.hyp.maxAb.eq_of_le ⟨PerpB_le_Q.trans hc.hyp.Q_normal.1, hMU, hcomm⟩
    hc.Z_le_PerpB
  exact hne hmax.symm

end Model

end CFSG.RankThree.GF2n.Stroth80
