module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.E2TenKG3

public section

namespace CFSG.Quasithin.H13

@[expose] def E3Good_e34 (X : Type) [Group X] (q : ℕ) (S : Subgroup X) : Prop :=
  (∃ Z : Subgroup X, Z ≤ S ∧ Nat.card ↥Z = q ∧ (∀ z ∈ Z, z ^ 2 = 1) ∧
      (∀ s ∈ S, s ^ 2 = 1 → s ∈ Z) ∧
      ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (S : Set X), g * z * g⁻¹ = z') ∧
  (∀ g : X, g ∉ Subgroup.normalizer (S : Set X) → S ⊓ S.map (MulAut.conj g).toMonoidHom = ⊥) ∧
  ∃ C : Subgroup X, C ≤ Subgroup.normalizer (S : Set X) ∧ IsCyclic ↥C ∧
    ∀ n ∈ Subgroup.normalizer (S : Set X), ∃ s ∈ S, ∃ c ∈ C, n = s * c

theorem isCyclic_quot_e34 {H : Type} [Group H] (N S C : Subgroup H) (hCN : C ≤ N)
    [IsCyclic ↥C] [(S.subgroupOf N).Normal] (hdec : ∀ n ∈ N, ∃ s ∈ S, ∃ c ∈ C, n = s * c) :
    IsCyclic (↥N ⧸ S.subgroupOf N) := by
  let f : ↥C →* ↥N ⧸ S.subgroupOf N :=
    (QuotientGroup.mk' (S.subgroupOf N)).comp (Subgroup.inclusion hCN)
  refine isCyclic_of_surjective f ?_
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨s, hs, c, hc, hn⟩ := hdec (n : H) n.2
  have hsN : s ∈ N := by
    have hs' : s = (n : H) * (c : H)⁻¹ := by rw [hn]; group
    rw [hs']
    exact N.mul_mem n.2 (N.inv_mem (hCN hc))
  refine ⟨⟨c, hc⟩, ?_⟩
  have h1 : (QuotientGroup.mk ⟨s, hsN⟩ : ↥N ⧸ S.subgroupOf N) = 1 :=
    (QuotientGroup.eq_one_iff (⟨s, hsN⟩ : ↥N)).2 (Subgroup.mem_subgroupOf.2 hs)
  have hsc : n = (⟨s, hsN⟩ : ↥N) * (⟨c, hCN hc⟩ : ↥N) := Subtype.ext hn
  show (QuotientGroup.mk (⟨c, hCN hc⟩ : ↥N) : ↥N ⧸ S.subgroupOf N) = QuotientGroup.mk n
  rw [hsc, QuotientGroup.mk_mul, h1, one_mul]

theorem good_map_e34 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (q : ℕ) (S : Subgroup X)
    (h : E3Good_e34 X q S) : E3Good_e34 Y q (S.map e.toMonoidHom) := by
  obtain ⟨⟨Z, hZS, hZc, hZsq, hZinv, hZtr⟩, hTI, C, hCN, hCc, hCdec⟩ := h
  have hN : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq S e).symm
  have hmemN : ∀ g : X, g ∈ Subgroup.normalizer (S : Set X) ↔
      e g ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    intro g
    rw [hN]
    constructor
    · intro hg
      exact Subgroup.mem_map_of_mem _ hg
    · intro hg
      obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.1 hg
      have : g' = g := e.injective hgg
      exact this ▸ hg'
  refine ⟨⟨Z.map e.toMonoidHom, Subgroup.map_mono hZS, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hZc
  · rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, hZsq z hz, map_one]
  · rintro _ ⟨s0, hs0, rfl⟩ hs
    have h2 : s0 ^ 2 = 1 := by
      rw [← map_pow] at hs
      exact (map_eq_one_iff e.toMonoidHom e.injective).1 hs
    exact Subgroup.mem_map_of_mem _ (hZinv s0 hs0 h2)
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ hne hne'
    have hz1 : z ≠ 1 := fun h => hne (by rw [h, map_one])
    have hz1' : z' ≠ 1 := fun h => hne' (by rw [h, map_one])
    obtain ⟨g, hg, hgz⟩ := hZtr z hz z' hz' hz1 hz1'
    refine ⟨e g, (hmemN g).1 hg, ?_⟩
    rw [← hgz]
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  · intro y hy
    obtain ⟨g, rfl⟩ := e.surjective y
    have hg : g ∉ Subgroup.normalizer (S : Set X) := fun h => hy ((hmemN g).1 h)
    have hT := hTI g hg
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw1
    obtain ⟨s', hs', hs'eq⟩ := Subgroup.mem_map.1 hw2
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs'
    have hxc : x ∈ S.map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨s, hs, ?_⟩
      apply e.injective
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hs'eq ⊢
      exact hs'eq
    have hx1 : x ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom := Subgroup.mem_inf.2 ⟨hx, hxc⟩
    rw [hT, Subgroup.mem_bot] at hx1
    rw [Subgroup.mem_bot, hx1, map_one]
  · refine ⟨C.map e.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact (hmemN c).1 (hCN hc)
    · refine isCyclic_of_surjective
        ((e.toMonoidHom.comp C.subtype).codRestrict (C.map e.toMonoidHom)
          (fun c => Subgroup.mem_map_of_mem _ c.2)) ?_
      rintro ⟨y, hy⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨c, hc⟩, rfl⟩
    · intro n hn
      rw [hN] at hn
      obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.1 hn
      obtain ⟨s, hs, c, hc, hsc⟩ := hCdec n0 hn0
      exact ⟨e s, Subgroup.mem_map_of_mem _ hs, e c, Subgroup.mem_map_of_mem _ hc,
        by rw [hsc]; simp only [map_mul, MulEquiv.coe_toMonoidHom]⟩

end CFSG.Quasithin.H13
