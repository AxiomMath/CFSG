module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec12Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec12Plane

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.eq_smul_of_singular_Wn [CharP K 2] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (hno : NoA2 Q Z (LB M Q B)) (hng : ¬ GenByB M Q B)
    {n : ℕ} (hw : Width Q Z n) (hn3 : n = 3)
    (hS : Nat.card hc.Spure = Nat.card Q * Nat.card Z ^ 2) {b : M₀.E} (hb0 : b ≠ 0)
    (hbs : M₀.Qf b = 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {w : M₀.E} (hwW : w ∈ hc.Wn h) (hwb : M₀.B w b = 0) (hwq : M₀.Qf w = 0) :
    ∃ κ : K, w = κ • b := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsymm : ∀ x y : M₀.E, M₀.B x y = M₀.B y x := fun x y => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  have hd := hc.finrank_Wp_eq_two h hng hS
  have hbW := hc.b_mem_Wn h hB
  obtain ⟨f, hfb⟩ : ∃ f : M₀.E, M₀.B f b = 1 := by
    obtain ⟨f₀, hf₀⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
    exact ⟨(M₀.B f₀ b)⁻¹ • f₀, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]⟩
  set Wp := PerpSub M₀ (Lgen M B) with hWp
  set U := M₀.B.orthogonal (Submodule.span K {b, f} ⊔ Wp) with hU
  have hUcard : Nat.card U = Nat.card K ^ 2 := by
    have := hc.finrank_U h hw hd hb0 hbW hfb
    rw [hn3] at this
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U)]
    congr 1
  have hmemU : ∀ u : M₀.E, M₀.B b u = 0 → M₀.B f u = 0 → (∀ y ∈ Wp, M₀.B y u = 0) → u ∈ U := by
    intro u hbu hfu hyu
    rw [hU, LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz₁
    show M₀.B (s • b + t • f + z₂) u = 0
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hbu,
      hfu, hyu z₂ hz₂]
    ring
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  let Φ : ↥hc.Spure →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hc.Spure_le_H0)
  have hΦπ : ∀ (s : ↥hc.Spure) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = Φ s (M₀.π x) := fun s x hx =>
    hφπ (Subgroup.inclusion hc.Spure_le_H0 s) x hx
  have hΦker : ∀ s : ↥hc.Spure, Φ s = 1 ↔ (s : G) ∈ Q := fun s =>
    hφker (Subgroup.inclusion hc.Spure_le_H0 s)
  have hQS : Q ≤ hc.Spure := hc.Q_le_Spure
  have hkerΦ : Φ.ker = Q.subgroupOf hc.Spure := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hΦker s
  have hcard : Nat.card hc.Spure = Nat.card Q * Nat.card Φ.range := by
    have h1 : Nat.card Φ.ker = Nat.card Q := by
      rw [hkerΦ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hΛcard : Nat.card Φ.range = Nat.card K ^ 2 := by
    rw [h.card]
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hQpos (hcard.symm.trans hS)
  have hex : ∀ s : ↥hc.Spure, ∃ v : M₀.E, M₀.B v b = 0 ∧ ∀ y, Φ s y =
      y + M₀.B y b • v + M₀.B y v • b + (M₀.Qf v * M₀.B y b) • b := fun s =>
    hc.eichler_of_Spure h hb0 hB hcent s.2 (T := (Φ s : M₀.E →ₗ[K] M₀.E)) (hΦπ s)
  choose v hvb hvE using hex
  let u : ↥hc.Spure → M₀.E := fun s => v s - M₀.B (v s) f • b
  have hub : ∀ s, M₀.B (u s) b = 0 := fun s => by
    show M₀.B (v s - M₀.B (v s) f • b) b = 0
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, M₀.alt, hvb s]
    simp
  have hu_eq : ∀ s y, Φ s y = eichlerMap M₀ b (u s) y := by
    intro s y
    have e : u s + M₀.B (v s) f • b = v s := sub_add_cancel _ _
    calc Φ s y = eichlerMap M₀ b (v s) y := hvE s y
      _ = eichlerMap M₀ b (u s + M₀.B (v s) f • b) y := by rw [e]
      _ = eichlerMap M₀ b (u s) y := eichlerMap_add_smul M₀ hbs (hub s) _ y
  have huU : ∀ s, u s ∈ U := by
    intro s
    refine hmemU _ ?_ ?_ ?_
    · rw [hsymm, hub s]
    · show M₀.B f (v s - M₀.B (v s) f • b) = 0
      rw [map_sub, map_smul, hfb, hsymm f (v s)]
      simp
    · intro y hy
      have hfix : Φ s y = y := hc.act_fixes_Wp h s.2.1 (T := fun e => Φ s e) (hΦπ s) hy
      have hyb : M₀.B y b = 0 := hc.B_Wp_Wn h hy hbW
      have h1 := hu_eq s y
      rw [hfix] at h1
      unfold eichlerMap at h1
      rw [hyb] at h1
      simp only [zero_smul, add_zero, zero_mul] at h1
      have h3 : M₀.B y (u s) • b = 0 := by
        have := h1.symm
        simpa using this
      exact (smul_eq_zero.mp h3).resolve_right hb0
  have hani : ∀ s : ↥hc.Spure,
      (∀ e ∈ LinearMap.range ((Φ s : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf e = 0) → Φ s = 1 := by
    intro s hs
    by_contra hne
    have hsQ : (s : G) ∉ Q := fun hsQ => hne ((hΦker s).mpr hsQ)
    obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M s.2.1)
    refine hc.not_elemAbelian_comm_Spure hno s.2 hsQ ?_
    rw [isElemAbelian_comm_zpowers_iff M₀ h.reg (Φ s) hQn hQn' (hΦπ s)]
    exact hs
  let g : Φ.range → U := fun T =>
    ⟨u (Classical.choose (MonoidHom.mem_range.mp T.2)),
      huU (Classical.choose (MonoidHom.mem_range.mp T.2))⟩
  have hginj : Function.Injective g := by
    intro T₁ T₂ hT
    have e1 := Classical.choose_spec (MonoidHom.mem_range.mp T₁.2)
    have e2 := Classical.choose_spec (MonoidHom.mem_range.mp T₂.2)
    have hu12 : u (Classical.choose (MonoidHom.mem_range.mp T₁.2)) =
        u (Classical.choose (MonoidHom.mem_range.mp T₂.2)) := congrArg Subtype.val hT
    refine Subtype.ext ?_
    rw [← e1, ← e2]
    refine LinearEquiv.ext fun y => ?_
    rw [hu_eq, hu_eq, hu12]
  have hgbij : Function.Bijective g :=
    hginj.bijective_of_nat_card_le (by rw [hUcard, hΛcard])
  set u₀ : M₀.E := w - M₀.B w f • b with hu₀def
  have hu₀b : M₀.B u₀ b = 0 := by
    rw [hu₀def, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, M₀.alt, hwb]
    simp
  have hbu₀ : M₀.B b u₀ = 0 := by rw [hsymm, hu₀b]
  have hfu₀ : M₀.B f u₀ = 0 := by
    rw [hu₀def, map_sub, map_smul, hfb, hsymm f w]
    simp
  have hu₀U : u₀ ∈ U := by
    refine hmemU _ hbu₀ hfu₀ fun y hy => ?_
    have hyb : M₀.B y b = 0 := hc.B_Wp_Wn h hy hbW
    rw [hu₀def, map_sub, map_smul, hc.B_Wp_Wn h hy hwW, hyb]
    simp
  have hxx : ∀ x : M₀.E, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have hu₀q : M₀.Qf u₀ = 0 := by
    have e : u₀ = w + M₀.B w f • b := by
      rw [hu₀def, sub_eq_add_neg, neg_eq_of_add_eq_zero_right (hxx (M₀.B w f • b))]
    rw [e, M₀.Qf_add, M₀.Qf_smul, hbs, map_smul, hwb, hwq]
    simp
  obtain ⟨T, hT⟩ := hgbij.2 ⟨u₀, hu₀U⟩
  have hus : u (Classical.choose (MonoidHom.mem_range.mp T.2)) = u₀ := congrArg Subtype.val hT
  have hΦ1 : Φ (Classical.choose (MonoidHom.mem_range.mp T.2)) = 1 := by
    refine hani _ ?_
    rintro _ ⟨y, rfl⟩
    show M₀.Qf (Φ (Classical.choose (MonoidHom.mem_range.mp T.2)) y - y) = 0
    rw [hu_eq _ y, hus]
    exact Qf_eichlerMap_sub M₀ hbs hu₀b hu₀q y
  have hf1 : Φ (Classical.choose (MonoidHom.mem_range.mp T.2)) f = f := by rw [hΦ1]; rfl
  rw [hu_eq _ f, hus] at hf1
  unfold eichlerMap at hf1
  rw [hfb, hfu₀, hu₀q] at hf1
  have hu0 : u₀ = 0 := by simpa using hf1
  exact ⟨M₀.B w f, sub_eq_zero.mp (hu₀def ▸ hu0)⟩

end CFSG.RankThree.GF2n.Stroth80
