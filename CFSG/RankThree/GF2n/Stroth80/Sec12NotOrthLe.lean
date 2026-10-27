module

public import CFSG.RankThree.GF2n.Stroth80.Sec12PerpModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.genByB_of_PerpB_le (hc : Ctx M Q Z B) (hle : PerpB M Q B ≤ Z) : GenByB M Q B := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  let Wn : Submodule (GaloisField 2 m) M₀.E :=
    { carrier := (M₀.img (Lgen M B) : Set M₀.E)
      add_mem' := fun ha hb => (M₀.img (Lgen M B)).add_mem ha hb
      zero_mem' := (M₀.img (Lgen M B)).zero_mem
      smul_mem' := fun c e he => hc.smul_mem_img_Lgen h c he }
  have horth : M₀.B.orthogonal Wn = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
    have hePerp : e ∈ PerpSub M₀ (Lgen M B) := fun n hn => by
      have h0 : M₀.B (M₀.π n) e = 0 := he (M₀.π n) (M₀.pi_mem_img hn (hc.Lgen_le_Q hn))
      rw [Tim79.QuadModel.B_comm, h0, neg_zero]
    obtain ⟨x, hx, hxQ, rfl⟩ := (hc.mem_img_PerpB_iff h e).mpr hePerp
    have := (M₀.π_ker x hxQ).mpr (hle hx)
    simpa using this
  have hfin : Module.finrank (GaloisField 2 m) Wn = Module.finrank (GaloisField 2 m) M₀.E := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd Wn
    rw [horth, finrank_bot] at h1
    have h2 := Submodule.finrank_le Wn
    omega
  have hWtop : Wn = ⊤ := Submodule.eq_top_of_finrank_eq hfin
  have hQN : Q ≤ Lgen M B ⊔ Z := by
    intro x hxQ
    have hx : M₀.π x ∈ Wn := hWtop ▸ Submodule.mem_top
    obtain ⟨n, hn, hnQ, hnx⟩ := hx
    have hz : n⁻¹ * x ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hnQ hxQ).mp hnx
    have e : x = n * (n⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hz)
  have hNn : ∀ m ∈ M, ∀ x ∈ Lgen M B, m * x * m⁻¹ ∈ Lgen M B := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M B hm) x).mp hx
  exact (hc.eq_of_le_sup_Z hc.Lgen_le_Q hNn hQN).symm

theorem Ctx.card_Spure_ge_pow {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    Nat.card Q * Nat.card Z ^ Module.finrank K (PerpSub M₀ (Lgen M B)) ≤
      Nat.card hc.Spure := by
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  obtain ⟨ω, h1, h2, h3, h4⟩ := hc.exists_swap'
  set C := conjSubgroup ω (PerpB M Q B) with hCdef
  have hCS : C ≤ hc.Spure := hc.conj_PerpB_le_Spure h1 h2 h3 h4
  have hQS : Q ≤ hc.Spure := hc.Q_le_Spure
  have hCM : C ≤ M := fun t ht => hc.LB_le_M (hCS ht).1
  have hCN : C ≤ Subgroup.normalizer (Q : Set G) := fun t ht => hc.hyp.Q_normal.2 (hCM ht)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCN
  have hinf : Nat.card ↥(Q ⊓ C) ≤ Nat.card Z := by
    have hle : Q ⊓ C ≤ B := fun x hx => hc.conj_PerpB_inf_Q_le h2 h3 ⟨hx.2, hx.1⟩
    obtain ⟨g, hg⟩ := hc.conj
    calc Nat.card ↥(Q ⊓ C) ≤ Nat.card B := Subgroup.card_le_of_le hle
      _ = Nat.card Z := by rw [hg, card_conjSubgroup]
  have hCcard : Nat.card C = Nat.card (PerpB M Q B) := card_conjSubgroup ω _
  have hsup : Nat.card ↥(Q ⊔ C) ≤ Nat.card hc.Spure := Subgroup.card_le_of_le (sup_le hQS hCS)
  have hPcard := hc.card_PerpB h
  rw [h.card] at hPcard
  have hkey : Nat.card Q * Nat.card Z ^ Module.finrank K (PerpSub M₀ (Lgen M B)) *
      Nat.card Z ≤ Nat.card ↥(Q ⊔ C) * Nat.card Z := by
    calc Nat.card Q * Nat.card Z ^ Module.finrank K (PerpSub M₀ (Lgen M B)) * Nat.card Z
        = Nat.card Q * (Nat.card Z * Nat.card Z ^ Module.finrank K (PerpSub M₀ (Lgen M B))) := by
          ring
      _ = Nat.card Q * Nat.card (PerpB M Q B) := by rw [hPcard]
      _ = Nat.card ↥(Q ⊔ C) * Nat.card ↥(Q ⊓ C) := by rw [← hCcard]; exact hprod.symm
      _ ≤ Nat.card ↥(Q ⊔ C) * Nat.card Z := Nat.mul_le_mul_left _ hinf
  exact (Nat.le_of_mul_le_mul_right hkey hqpos).trans hsup

theorem Ctx.card_Spure_ge_of_not_genByB (hc : Ctx M Q Z B) (hng : ¬ GenByB M Q B) :
    Nat.card Q * Nat.card Z ^ 2 ≤ Nat.card hc.Spure := by
  have hne : PerpB M Q B ≠ Z := fun h' => hng (hc.genByB_of_PerpB_le h'.le)
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hd := hc.two_le_finrank_PerpSub h hne
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hqpos hd)).trans (hc.card_Spure_ge_pow h)

theorem Ctx.orthLe_and_not_Spure_le_Q_of_not_genByB (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hng : ¬ GenByB M Q B) :
    OrthLe M B ∧ ¬ hc.Spure ≤ Q := by
  have h1 := hc.card_Spure_ge_of_not_genByB hng
  have hq4 := hc.hyp.q4
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hlt : Nat.card Q * Nat.card Z < Nat.card hc.Spure := by
    refine lt_of_lt_of_le ?_ h1
    have : Nat.card Z < Nat.card Z ^ 2 := by nlinarith
    exact Nat.mul_lt_mul_of_pos_left this hQpos
  refine ⟨hc.orthLe_of_card_Spure hw hn hno hlt, fun hSQ => ?_⟩
  have h2 : Nat.card hc.Spure ≤ Nat.card Q := Subgroup.card_le_of_le hSQ
  have : Nat.card Q ≤ Nat.card Q * Nat.card Z := Nat.le_mul_of_pos_right _ hqpos
  omega

end CFSG.RankThree.GF2n.Stroth80
