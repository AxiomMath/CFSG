module

public import CFSG.Quasithin.H13.AS91Sec8KautZ
public import CFSG.Quasithin.H13.AS91Sec6Defs
public import CFSG.Quasithin.H13.AS91Sec8Uniq

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem RE_conj {k : G} (hk : k ∈ c.K) {n : G} (hn : n ∈ c.R ⊔ c.E) :
    k * n * k⁻¹ ∈ c.R ⊔ c.E := by
  have h1 : (c.R ⊔ c.E).map (MulAut.conj k).toMonoidHom ≤ c.R ⊔ c.E := by
    rw [Subgroup.map_sup]
    apply sup_le_sup
    · rintro _ ⟨r, hr, rfl⟩
      exact c.R_conj hk hr
    · rintro _ ⟨e, he, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (c.K_le_G1 hk) e).mp he
  exact h1 ⟨n, hn, rfl⟩

theorem card_K : Nat.card c.K = 2 ^ 15 * 168 := by
  have h := Subgroup.relIndex_mul_card (H := c.R) (K := c.K)
  have h1 : c.R.relIndex c.K = 168 := c.index_R_K
  rw [inf_eq_left.mpr c.R_le_K, c.card_R, h1] at h
  rw [← h]
  ring

theorem E_not_le_K : ¬ c.E ≤ c.K := by
  intro hE
  have hRE_K : c.R ⊔ c.E ≤ c.K := sup_le c.R_le_K hE
  obtain ⟨φ, hφs, hφk⟩ := c.K_quot
  haveI hs := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  let N : Subgroup ↥c.K := (c.R ⊔ c.E).subgroupOf c.K
  haveI hNn : N.Normal :=
    ⟨fun n hn k => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using c.RE_conj k.2 hn⟩
  haveI : (N.map φ).Normal := hNn.map φ hφs
  have hkerN : φ.ker ≤ N := by
    rw [hφk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_sup_left hx
  rcases hs.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  · have hle : c.R ⊔ c.E ≤ c.R := by
      intro x hx
      have hxK : x ∈ c.K := hRE_K hx
      have h1 : (⟨x, hxK⟩ : ↥c.K) ∈ N := hx
      have h2 : φ ⟨x, hxK⟩ ∈ N.map φ := Subgroup.mem_map_of_mem φ h1
      rw [hbot, Subgroup.mem_bot] at h2
      have h3 : (⟨x, hxK⟩ : ↥c.K) ∈ φ.ker := h2
      rw [hφk, Subgroup.mem_subgroupOf] at h3
      exact h3
    have := Subgroup.card_le_of_le hle
    rw [c.card_RE, c.card_R] at this
    norm_num at this
  · have hN : N = ⊤ := by
      have h1 := Subgroup.comap_map_eq φ N
      rw [htop, Subgroup.comap_top, sup_eq_left.mpr hkerN] at h1
      exact h1.symm
    have hKRE : c.K ≤ c.R ⊔ c.E := by
      intro x hx
      have : (⟨x, hx⟩ : ↥c.K) ∈ N := by rw [hN]; exact Subgroup.mem_top _
      exact this
    have heq : c.R ⊔ c.E = c.K := le_antisymm hRE_K hKRE
    have h1 := c.card_RE
    rw [heq, c.card_K] at h1
    norm_num at h1

theorem exists_perm_triple {α : Type*} [DecidableEq α] {x p q a b : α} (hxp : x ≠ p)
    (hxq : x ≠ q) (hpq : p ≠ q) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ x = x ∧ σ p = a ∧ σ q = b := by
  have h1 : Equiv.swap p a x = x := Equiv.swap_apply_of_ne_of_ne hxp hxa
  have hq' : x ≠ Equiv.swap p a q := by
    intro h
    apply hxq
    have := congrArg (Equiv.swap p a) h
    rw [h1, Equiv.swap_apply_self] at this
    exact this
  have haq' : a ≠ Equiv.swap p a q := by
    intro h
    have h2 : Equiv.swap p a p = Equiv.swap p a q := by
      rw [Equiv.swap_apply_left]; exact h
    exact hpq ((Equiv.swap p a).injective h2)
  refine ⟨(Equiv.swap p a).trans (Equiv.swap (Equiv.swap p a q) b), ?_, ?_, ?_⟩
  · rw [Equiv.trans_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne hq' hxb
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne haq' hab
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem exists_CZ_perm (σ : Equiv.Perm ↥c.ptsL) :
    ∃ s ∈ c.CZ, ∀ p : ↥c.ptsL, s • (p : G ⧸ c.G1) = ((σ p : ↥c.ptsL) : G ⧸ c.G1) :=
  exists_mem_smul_eq_perm c.G1 c.G2 c.CZ c.R c.CZ_le_G2 c.card_ptsL c.ker_CZ_le_R c.index_R_CZ σ

theorem E_transitive {a b : G ⧸ c.G1} (ha : a ∈ c.ptsL) (hb : b ∈ c.ptsL) (hax : a ≠ c.x0)
    (hbx : b ≠ c.x0) : ∃ e ∈ c.E, e • a = b := by
  classical
  by_cases hab : a = b
  · exact ⟨1, one_mem _, by rw [one_smul, hab]⟩
  obtain ⟨e₀, he₀, he₀K⟩ : ∃ e₀ ∈ c.E, e₀ ∉ c.K := by
    by_contra hcon
    push Not at hcon
    exact c.E_not_le_K fun e he => hcon e he
  have he₀G2 : e₀ ∈ c.G2 := c.E_le_G2 he₀
  have he₀x : e₀ • c.x0 = c.x0 := by
    have : e₀ ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact c.E_le_G1 he₀
    exact mem_stabilizer_iff.mp this
  obtain ⟨p, hp, hpe⟩ : ∃ p ∈ c.ptsL, e₀ • p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact he₀K ((c.kernel_ptsL e₀ he₀G2).mp hcon)
  have hq : e₀ • p ∈ c.ptsL := smul_mem_objOf_base he₀G2 hp
  have hpx : p ≠ c.x0 := fun h => hpe (by rw [h, he₀x])
  have hqx : e₀ • p ≠ c.x0 := fun h => hpx (smul_left_cancel e₀ (h.trans he₀x.symm))
  let X0 : ↥c.ptsL := ⟨c.x0, c.x0_mem_ptsL⟩
  obtain ⟨σ, hσx, hσp, hσq⟩ := exists_perm_triple (α := ↥c.ptsL) (x := X0)
    (p := ⟨p, hp⟩) (q := ⟨e₀ • p, hq⟩) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (fun h => hpx (congrArg Subtype.val h).symm) (fun h => hqx (congrArg Subtype.val h).symm)
    (fun h => hpe (congrArg Subtype.val h).symm) (fun h => hax (congrArg Subtype.val h).symm)
    (fun h => hbx (congrArg Subtype.val h).symm) (fun h => hab (congrArg Subtype.val h))
  obtain ⟨s, hsCZ, hs⟩ := c.exists_CZ_perm σ
  have hsx : s • c.x0 = c.x0 := by
    have := hs X0
    rw [hσx] at this
    exact this
  have hsG1 : s ∈ c.G1 := by
    rw [← c.stab_x0]
    exact mem_stabilizer_iff.mpr hsx
  have heE : s * e₀ * s⁻¹ ∈ c.E := (Subgroup.mem_normalizer_iff.mp hsG1 e₀).mp he₀
  have h1 : s • p = a := by
    have := hs ⟨p, hp⟩
    rw [hσp] at this
    exact this
  have h2 : s • (e₀ • p) = b := by
    have := hs ⟨e₀ • p, hq⟩
    rw [hσq] at this
    exact this
  refine ⟨s * e₀ * s⁻¹, heE, ?_⟩
  calc (s * e₀ * s⁻¹) • a = (s * e₀ * s⁻¹) • (s • p) := by rw [h1]
    _ = s • (e₀ • p) := by rw [mul_smul, mul_smul, inv_smul_smul]
    _ = b := h2

theorem coset_geom_local' (h52 : Stmt5_2u) (h65 : Stmt6_5u) (hJ : HypJ4 G z) :
    CosetGeomLocal c.G1 c.G2 c.G3 := by
  have hc5 := c.card_ptsL
  obtain ⟨hg1, hg3⟩ := h52 G z hJ c
  have hsup := h65 G z hJ c
  have hker := c.ker_CZ_le_R
  refine ⟨c.exists_pt hc5, ?_, hsup, hg1, hg3, ?_⟩
  · intro a b a' b' ha hb ha' hb' hab hab'
    obtain ⟨s, hs, h1, h2⟩ := exists_mem_smul_pair c.G1 c.G2 c.CZ c.R c.CZ_le_G2 hc5 hker
      c.index_R_CZ ha hb ha' hb' hab hab'
    exact ⟨s, ⟨c.CZ_le_G2 hs, c.CZ_le_G3 hs⟩, h1, h2⟩
  · intro y hy hyx
    refine gamma5_of_transitive c.G1 c.G2 c.G3 c.E ?_ ?_ hy hyx
    · exact le_inf (le_inf c.E_le_G1 c.E_le_G2) c.E_le_G3
    · intro y₁ y₂ h1 h2 h1x h2x
      exact c.E_transitive h1 h2 h1x h2x

end Loc49

end CFSG.Quasithin.H13.AS91
