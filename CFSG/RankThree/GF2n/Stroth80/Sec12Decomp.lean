module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NotOrthLe

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem modelB_nondegenerate (M₀ : Tim79.QuadModel Q Z K γ) : M₀.B.Nondegenerate :=
  ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩

@[expose] def Ctx.Wn (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    Submodule K M₀.E where
  carrier := (M₀.img (Lgen M B) : Set M₀.E)
  add_mem' := fun ha hb => (M₀.img (Lgen M B)).add_mem ha hb
  zero_mem' := (M₀.img (Lgen M B)).zero_mem
  smul_mem' := fun c e he => hc.smul_mem_img_Lgen h c he

theorem Ctx.orthogonal_Wn (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    M₀.B.orthogonal (hc.Wn h) = PerpSub M₀ (Lgen M B) := by
  ext e
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro he n hn
    have h0 : M₀.B (M₀.π n) e = 0 := he (M₀.π n) (M₀.pi_mem_img hn (hc.Lgen_le_Q hn))
    rw [Tim79.QuadModel.B_comm, h0, neg_zero]
  · intro he n hn
    obtain ⟨x, hx, -, rfl⟩ := hn
    show M₀.B (M₀.π x) e = 0
    rw [Tim79.QuadModel.B_comm, he x hx, neg_zero]

theorem Ctx.Wn_inf_Wp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    hc.Wn h ⊓ PerpSub M₀ (Lgen M B) = ⊥ := by
  rw [eq_bot_iff]
  rintro e ⟨hn, hp⟩
  obtain ⟨n, hnN, hnQ, rfl⟩ := hn
  obtain ⟨c, hcP, hcQ, hcn⟩ := (hc.mem_img_PerpB_iff h _).mpr hp
  have hz : c⁻¹ * n ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hcQ hnQ).mp hcn
  have hcsup : c ∈ Lgen M B ⊔ Z := by
    have e : c = n * (c⁻¹ * n)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right (Z.inv_mem hz))
  have hcZ : c ∈ Z := hc.PerpB_inf_sup_le hcP hcsup
  have : M₀.π c = 0 := (M₀.π_ker c hcQ).mpr hcZ
  show M₀.π n = 0
  rw [← hcn]
  exact this

theorem Ctx.finrank_Wn_add (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    Module.finrank K (hc.Wn h) + Module.finrank K (PerpSub M₀ (Lgen M B)) =
      Module.finrank K M₀.E := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal (modelB_nondegenerate M₀) (hc.Wn h)
  rw [hc.orthogonal_Wn h] at h1
  have h2 := Submodule.finrank_le (hc.Wn h)
  omega

theorem Ctx.Wn_sup_Wp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    hc.Wn h ⊔ PerpSub M₀ (Lgen M B) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (hc.Wn h) (PerpSub M₀ (Lgen M B))
  rw [hc.Wn_inf_Wp h, finrank_bot] at h1
  have := hc.finrank_Wn_add h
  omega

theorem Ctx.orthogonal_Wp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    M₀.B.orthogonal (PerpSub M₀ (Lgen M B)) = hc.Wn h := by
  have hle : hc.Wn h ≤ M₀.B.orthogonal (PerpSub M₀ (Lgen M B)) := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨x, hx, -, rfl⟩ := he
    exact hy x hx
  have h1 := LinearMap.BilinForm.finrank_orthogonal (modelB_nondegenerate M₀)
    (PerpSub M₀ (Lgen M B))
  have h2 := hc.finrank_Wn_add h
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem Ctx.Wp_inf_orthogonal (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    PerpSub M₀ (Lgen M B) ⊓ M₀.B.orthogonal (PerpSub M₀ (Lgen M B)) = ⊥ := by
  rw [hc.orthogonal_Wp h, inf_comm]
  exact hc.Wn_inf_Wp h

theorem Ctx.Wn_inf_orthogonal (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    hc.Wn h ⊓ M₀.B.orthogonal (hc.Wn h) = ⊥ := by
  rw [hc.orthogonal_Wn h]
  exact hc.Wn_inf_Wp h

theorem Ctx.mem_Wn_of_mem_img (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {x : G} (hx : x ∈ Lgen M B) : M₀.π x ∈ hc.Wn h :=
  M₀.pi_mem_img hx (hc.Lgen_le_Q hx)

theorem Ctx.B_Wp_Wn (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {y e : M₀.E} (hy : y ∈ PerpSub M₀ (Lgen M B)) (he : e ∈ hc.Wn h) : M₀.B y e = 0 := by
  obtain ⟨x, hx, -, rfl⟩ := he
  exact hy x hx

theorem Ctx.B_Wn_Wp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {y e : M₀.E} (hy : y ∈ PerpSub M₀ (Lgen M B)) (he : e ∈ hc.Wn h) : M₀.B e y = 0 := by
  rw [Tim79.QuadModel.B_comm, hc.B_Wp_Wn h hy he, neg_zero]

theorem Ctx.b_mem_Wn (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) : b ∈ hc.Wn h := by
  have hb : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  exact M₀.img_mono (le_Lgen_self M B) hb

theorem Ctx.finrank_Wp_eq_two (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (hng : ¬ GenByB M Q B) (hS : Nat.card hc.Spure = Nat.card Q * Nat.card Z ^ 2) :
    Module.finrank K (PerpSub M₀ (Lgen M B)) = 2 := by
  have hne : PerpB M Q B ≠ Z := fun h' => hng (hc.genByB_of_PerpB_le h'.le)
  have hd := hc.two_le_finrank_PerpSub h hne
  have hle := hc.card_Spure_ge_pow h
  rw [hS] at hle
  have hq4 := hc.hyp.q4
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h2 : Nat.card Z ^ Module.finrank K (PerpSub M₀ (Lgen M B)) ≤ Nat.card Z ^ 2 :=
    Nat.le_of_mul_le_mul_left hle hQpos
  have h3 := (Nat.pow_le_pow_iff_right (by omega)).mp h2
  omega

end CFSG.RankThree.GF2n.Stroth80
