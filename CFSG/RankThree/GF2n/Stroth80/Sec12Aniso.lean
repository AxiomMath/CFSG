module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Singular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.Wp_anisotropic [CharP K 2] (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (hno : NoA2 Q Z (LB M Q B)) (hng : ¬ GenByB M Q B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hn3 : n = 3) (hS : Nat.card hc.Spure = Nat.card Q * Nat.card Z ^ 2) {b : M₀.E} (hb0 : b ≠ 0)
    (hbs : M₀.Qf b = 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {u : M₀.E} (hu : u ∈ PerpSub M₀ (Lgen M B)) (huq : M₀.Qf u = 0) : u = 0 := by
  classical
  have hbW := hc.b_mem_Wn h hB
  obtain ⟨Dsub, hDmem, hDperp⟩ := hc.img_inf_QB_lagrangian hw hn hno h
  have hDiso : ∀ e ∈ Dsub, ∀ e' ∈ Dsub, M₀.B e e' = 0 := by
    intro e he e' he'
    obtain ⟨x, hx, hxQ, rfl⟩ := (hDmem e).mpr he
    obtain ⟨y, hy, hyQ, rfl⟩ := (hDmem e').mpr he'
    exact (Tim79.QuadModel.comm_iff_B M₀ h.reg hxQ hyQ).mp
      (congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hDsing : ∀ e ∈ Dsub, M₀.Qf e = 0 := fun e he =>
    (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian e
      ((hDmem e).mpr he)
  have hbD : b ∈ Dsub := by
    rw [← hDmem]
    have hb : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    exact M₀.img_mono (le_inf hc.le hc.B_le_QB) hb
  have hDWp : Dsub ⊓ PerpSub M₀ (Lgen M B) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heD, heP⟩
    obtain ⟨d, hdD, hdQ, rfl⟩ := (hDmem e).mpr heD
    obtain ⟨c, hcP, hcQ, hcd⟩ := (hc.mem_img_PerpB_iff h _).mpr heP
    have hz : c⁻¹ * d ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hcQ hdQ).mp hcd
    have hdP : d ∈ PerpB M Q B := by
      have e1 : d = c * (c⁻¹ * d) := by group
      rw [e1]
      exact (PerpB M Q B).mul_mem hcP (hc.Z_le_PerpB hz)
    have hdZ : d ∈ Z := hc.PerpB_inf_QB_le ⟨hdP, (Subgroup.mem_inf.mp hdD).2⟩
    exact (M₀.π_ker d hdQ).mpr hdZ
  have hDW : Dsub ⊔ hc.Wn h = ⊤ := by
    have horth : M₀.B.orthogonal (Dsub ⊔ hc.Wn h) = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
      have heD : e ∈ Dsub := by
        refine hDperp e fun u' hu' => ?_
        have := he u' (Submodule.mem_sup_left hu')
        rw [Tim79.QuadModel.B_comm, this, neg_zero]
      have heP : e ∈ PerpSub M₀ (Lgen M B) := fun n hn' => by
        have := he (M₀.π n) (Submodule.mem_sup_right (hc.mem_Wn_of_mem_img h hn'))
        rw [Tim79.QuadModel.B_comm, this, neg_zero]
      have : e ∈ Dsub ⊓ PerpSub M₀ (Lgen M B) := ⟨heD, heP⟩
      rwa [hDWp] at this
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.BilinForm.finrank_orthogonal (modelB_nondegenerate M₀) (Dsub ⊔ hc.Wn h)
    rw [horth, finrank_bot] at h1
    have h2 := Submodule.finrank_le (Dsub ⊔ hc.Wn h)
    omega
  have huDW : u ∈ Dsub ⊔ hc.Wn h := by rw [hDW]; exact Submodule.mem_top
  obtain ⟨d, hd, w₀, hw₀, hdw⟩ := Submodule.mem_sup.mp huDW
  have huw₀ : M₀.B u w₀ = 0 := hc.B_Wp_Wn h hu hw₀
  have hdw₀ : M₀.B d w₀ = 0 := by
    rw [← hdw, map_add, LinearMap.add_apply, M₀.alt, add_zero] at huw₀
    exact huw₀
  have hw₀q : M₀.Qf w₀ = 0 := by
    have := M₀.Qf_add d w₀
    rw [hdw, huq, hDsing d hd, hdw₀] at this
    simpa using this.symm
  have hw₀b : M₀.B w₀ b = 0 := by
    have e : w₀ = u - d := by rw [← hdw]; abel
    have hub : M₀.B u b = 0 := hc.B_Wp_Wn h hu hbW
    have hdb : M₀.B d b = 0 := hDiso d hd b hbD
    rw [e, map_sub, LinearMap.sub_apply, hub, hdb, sub_zero]
  obtain ⟨κ, hκ⟩ := hc.eq_smul_of_singular_Wn h hno hng hw hn3 hS hb0 hbs hB hcent hw₀ hw₀b hw₀q
  have hw₀D : w₀ ∈ Dsub := by rw [hκ]; exact Dsub.smul_mem κ hbD
  have huD : u ∈ Dsub := by rw [← hdw]; exact Dsub.add_mem hd hw₀D
  have : u ∈ Dsub ⊓ PerpSub M₀ (Lgen M B) := ⟨huD, hu⟩
  rwa [hDWp, Submodule.mem_bot] at this

end CFSG.RankThree.GF2n.Stroth80
