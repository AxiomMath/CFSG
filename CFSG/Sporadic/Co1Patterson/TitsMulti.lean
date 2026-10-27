module

public import CFSG.Sporadic.Co1Patterson.TitsMultiCover

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph CFSG.Monster.B.Recog

theorem tits_universal_completion_by {V : Type*} {G : SimpleGraph V} {X : Type*} [Group X]
    [MulAction X V] {T : Set V → Prop}
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    (hconn : G.Preconnected) (hG : TriangulableBy G T)
    {v w : V} (hvw : G.Adj v w) (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    (Xv Xe : Subgroup X) (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} (u : ι → V) (Xt : ι → Subgroup X)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T {v, y₁, y₂} →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    {Y : Type*} [Group Y] (φv : Xv →* Y) (φe : Xe →* Y) (φt : ∀ j, Xt j →* Y)
    (hve : ∀ a (ha : a ∈ Xv) (hb : a ∈ Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ Xv) (hb : a ∈ Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ Xe) (hb : a ∈ Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : Xv, Φ a = φv a) ∧ (∀ a : Xe, Φ a = φe a) ∧
      ∀ j (a : Xt j), Φ a = φt j a := by
  set K := homGraph φv ⊔ homGraph φe with hK
  have hinj : Set.InjOn (MonoidHom.snd Y X) K :=
    injOn_sup_of_triangulableBy hG hadj hTinv hvw hloc hswap hXv hXe hτ hρ htri
      (MonoidHom.snd Y X) (injOn_snd_homGraph φv) (injOn_snd_homGraph φe)
      (fun j => injOn_snd_homGraph (φt j)) (map_snd_homGraph φv) (map_snd_homGraph φe)
      (fun j => map_snd_homGraph (φt j)) (inf_le_map_inf_homGraph hve)
      (fun j => inf_le_map_inf_homGraph (hvt j)) (fun j => inf_le_map_inf_homGraph (het j))
  have htop : Xv ⊔ Xe = ⊤ := sup_eq_top_of_preconnected hadj hconn hloc hswap hXv hXe
  have hsurj : K.map (MonoidHom.snd Y X) = ⊤ := by
    rw [hK, Subgroup.map_sup, map_snd_homGraph, map_snd_homGraph, htop]
  have htK : ∀ j (a : Xt j), (φt j a, (a : X)) ∈ K := by
    intro j
    let L := K.comap ((φt j).prod (Xt j).subtype)
    have hLv : ∀ a : Xt j, (a : X) • v = v → a ∈ L := fun ⟨a, ha⟩ hav => by
      change (φt j ⟨a, ha⟩, a) ∈ K
      rw [← hvt j a ((hXv a).2 hav) ha]
      exact Subgroup.mem_sup_left (mk_mem_homGraph φv ⟨a, _⟩)
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨ρ, hρm, hρv, hρw, -⟩ := hρ j
    have hτL : (⟨τ, hτm⟩ : Xt j) ∈ L := by
      change (φt j ⟨τ, hτm⟩, τ) ∈ K
      rw [← het j τ ((hXe τ).2 (Or.inr ⟨hτv, hτw⟩)) hτm]
      exact Subgroup.mem_sup_right (mk_mem_homGraph φe ⟨τ, _⟩)
    have hLw : ∀ a : Xt j, (a : X) • v = w → a ∈ L := fun a hav => by
      have : (⟨τ, hτm⟩ : Xt j)⁻¹ * a ∈ L := hLv _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hav, inv_smul_eq_iff, hτv])
      simpa using L.mul_mem hτL this
    intro a
    rcases hXt j a a.2 with h | h | h
    · exact hLv a h
    · exact hLw a h
    · have : (⟨ρ, hρm⟩ : Xt j)⁻¹ * a ∈ L := hLw _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, inv_smul_eq_iff, hρw])
      exact (by simpa using L.mul_mem (hLw ⟨ρ, hρm⟩ hρv) this : a ∈ L)
  let f : K →* X := (MonoidHom.snd Y X).comp K.subtype
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 h), fun x => ?_⟩
    obtain ⟨q, hq, hqx⟩ : x ∈ K.map (MonoidHom.snd Y X) := hsurj ▸ Subgroup.mem_top x
    exact ⟨⟨q, hq⟩, hqx⟩
  let e : K ≃* X := MulEquiv.ofBijective f hf
  have he : ∀ (q : Y × X) (hq : q ∈ K), e.symm q.2 = ⟨q, hq⟩ := fun q hq =>
    e.symm_apply_eq.2 rfl
  let Φ : X →* Y := (MonoidHom.fst Y X).comp (K.subtype.comp e.symm.toMonoidHom)
  have hΦ : ∀ (q : Y × X), q ∈ K → Φ q.2 = q.1 := fun q hq => by
    change ((e.symm q.2 : K) : Y × X).1 = q.1
    rw [he q hq]
  refine ⟨Φ, ⟨fun a => hΦ (φv a, a) (Subgroup.mem_sup_left (mk_mem_homGraph φv a)),
    fun a => hΦ (φe a, a) (Subgroup.mem_sup_right (mk_mem_homGraph φe a)),
    fun j a => hΦ (φt j a, a) (htK j a)⟩, ?_⟩
  rintro Ψ ⟨hΨv, hΨe, -⟩
  have hle : Xv ⊔ Xe ≤ MonoidHom.eqLocus Ψ Φ := sup_le
    (fun a ha => (hΨv ⟨a, ha⟩).trans
      (hΦ (φv ⟨a, ha⟩, a) (Subgroup.mem_sup_left (mk_mem_homGraph φv ⟨a, ha⟩))).symm)
    (fun a ha => (hΨe ⟨a, ha⟩).trans
      (hΦ (φe ⟨a, ha⟩, a) (Subgroup.mem_sup_right (mk_mem_homGraph φe ⟨a, ha⟩))).symm)
  rw [htop] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

structure TitsDataBy {V : Type*} (Γ : SimpleGraph V) (T : Set V → Prop) (X : Type*) [Group X]
    [MulAction X V] (ι : Type*) where
  v : V
  w : V
  u : ι → V
  Xv : Subgroup X
  Xe : Subgroup X
  Xt : ι → Subgroup X
  hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)
  hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S)
  hconn : Γ.Preconnected
  hΓ : TriangulableBy Γ T
  hvw : Γ.Adj v w
  hloc : ∀ y, Γ.Adj v y → ∃ g : X, g • v = v ∧ g • w = y
  hswap : ∃ g : X, g • v = w ∧ g • w = v
  hXv : ∀ g, g ∈ Xv ↔ g • v = v
  hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v)
  hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j
  hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v
  hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v
  htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v → T {v, y₁, y₂} →
    ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂

namespace TitsDataBy

variable {V : Type*} {Γ : SimpleGraph V} {T : Set V → Prop} {X : Type*} [Group X]
  [MulAction X V] {ι : Type*}

theorem existsUnique_hom (D : TitsDataBy Γ T X ι) {Y : Type*} [Group Y] (φv : D.Xv →* Y)
    (φe : D.Xe →* Y) (φt : ∀ j, D.Xt j →* Y)
    (hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : D.Xv, Φ a = φv a) ∧ (∀ a : D.Xe, Φ a = φe a) ∧
      ∀ j (a : D.Xt j), Φ a = φt j a :=
  tits_universal_completion_by D.hadj D.hTinv D.hconn D.hΓ D.hvw D.hloc D.hswap D.Xv D.Xe
    D.hXv D.hXe D.u D.Xt D.hXt D.hτ D.hρ D.htri φv φe φt hve hvt het

theorem injective_of_isSimpleGroup (D : TitsDataBy Γ T X ι) (hX : IsSimpleGroup X)
    {Y : Type*} [Group Y] (Φ : X →* Y) (h : ∃ a : D.Xv, Φ a ≠ 1) : Function.Injective Φ := by
  rcases hX.eq_bot_or_eq_top_of_normal Φ.ker with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff Φ).1 hk
  · obtain ⟨a, ha⟩ := h
    exact absurd (MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top (a : X))) ha

end TitsDataBy

end CFSG.Sporadic.Co1Patterson
