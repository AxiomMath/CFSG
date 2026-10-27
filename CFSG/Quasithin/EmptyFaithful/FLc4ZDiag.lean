module

public import CFSG.Quasithin.EmptyFaithful.FLc4ZOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_thompsonJi_one {T : Subgroup G} {g : G} (hg : g ∈ T) {j : G}
    (hj : j ∈ thompsonJi T 1) : g * j * g⁻¹ ∈ thompsonJi T 1 := by
  have hmap : T.map (MulAut.conj g).toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact T.mul_mem (T.mul_mem hg hy) (T.inv_mem hg)
    · intro hx
      refine ⟨g⁻¹ * x * g, T.mul_mem (T.mul_mem (T.inv_mem hg) hx) hg, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  have h1 := thompsonJi_map_mulEquiv151 (MulAut.conj g) T 1
  rw [hmap] at h1
  have : g * j * g⁻¹ ∈ (thompsonJi T 1).map (MulAut.conj g).toMonoidHom := ⟨j, hj, rfl⟩
  rw [h1] at this
  exact this

theorem conj_mem_vE1516 {T Mc M : Subgroup G} (hTM : T ≤ M) {g : G} (hg : g ∈ T) {x : G}
    (hx : x ∈ vE1516 T Mc M) : g * x * g⁻¹ ∈ vE1516 T Mc M := by
  refine ⟨?_, Subgroup.mem_centralizer_iff.2 ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_V154 T Mc M (hTM hg)) x).1 hx.1
  · intro j hj
    have hj' : g⁻¹ * j * g ∈ thompsonJi T 1 := by
      have := conj_mem_thompsonJi_one (T.inv_mem hg) hj
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hx.2 _ hj'
    calc j * (g * x * g⁻¹) = g * ((g⁻¹ * j * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * j := by group

theorem input15129ZDiagonal_holds : Input15129ZDiagonal := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h
  have hS := hc.base.ctx.setting
  have hq := hc.base.ctx.qtfe
  have hM := hc.base.ctx.mf
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.base.hL.comp
  have hsmall : Ce15Small T Mc M := Or.inr (Or.inl h)
  have hn7 : ¬ Ce15Seven T Mc M := h.not_seven
  obtain ⟨-, -, hZc⟩ := hS.ranks_six ⟨3, Or.inl rfl, h⟩
  obtain ⟨hZ1c, hZ2c⟩ := hZc hsmall
  have hdiag := (hS.diagonal hsmall hn7).2
  have hidx : (s1516 T Z₁).relIndex T = 2 := hS.index_two hsmall hn7
  have hswap := hS.swap_small hsmall hn7
  obtain ⟨-, hZ₁V₁, -, hV₁₂inf⟩ := hS.decomp_other hn7
  have hZ₂V₂ := hS.z2_le_v2 hn7
  have hVab := hS.V_isElemAbelian hq hM
  have hVT := hS.V_le_T hq hM
  have hTM : T ≤ M := hM.1.1.2
  have hVc : ∀ x ∈ V154 T Mc M, ∀ y ∈ V154 T Mc M, x * y = y * x := by
    intro x hx y hy
    have := hVab.1
    exact setLike_mul_comm hx hy
  have hV2 : ∀ x ∈ V154 T Mc M, x ^ 2 = 1 := hVab.2
  have hcomm : ∀ a ∈ Z₁, ∀ b ∈ Z₂, a * b = b * a := fun a ha b hb =>
    hVc a (hS.z1_le_V ha) b (hS.z2_le_V hb)
  have hZ12 : ∀ z ∈ quasithinOmegaOneCenter T, ∃ a ∈ Z₁, ∃ b ∈ Z₂, z = a * b := by
    intro z hz
    have : z ∈ Z₁ ⊔ Z₂ := hS.vE_sup.2 hz
    exact exists_mul_of_mem_sup_comm4 hcomm this
  have hZZ1 : ∀ w ∈ quasithinOmegaOneCenter T, w ∈ Z₁ → w = 1 := by
    intro w hwZ hwZ₁
    by_contra hw1
    have h6 := hc.base.h18.six w hwZ hw1
    have hGM : g1_1516 Z₁ ≤ Mc := fun g hg => h6.centralizer_z_le (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg w hwZ₁).symm)
    exact hc.base.hL.not_le fun l hl => ⟨hLG hl, hGM (hLG hl)⟩
  choose a ha b hb hzab using hZ12
  have hup : Nat.card (quasithinOmegaOneCenter T) ≤ 4 := by
    let f : ↥(quasithinOmegaOneCenter T) → ↥Z₂ := fun z => ⟨b z.1 z.2, hb z.1 z.2⟩
    have hinj : Function.Injective f := by
      intro z z' hzz
      have hbeq : b z.1 z.2 = b z'.1 z'.2 := congrArg Subtype.val hzz
      have hz1 := hzab z.1 z.2
      have hz2 := hzab z'.1 z'.2
      have hha1 := ha z.1 z.2
      have hha2 := ha z'.1 z'.2
      set a₁ := a z.1 z.2
      set a₂ := a z'.1 z'.2
      set b₁ := b z.1 z.2
      set b₂ := b z'.1 z'.2
      have hw : z.1 * z'.1⁻¹ = a₁ * a₂⁻¹ := by
        calc z.1 * z'.1⁻¹ = (a₁ * b₁) * (a₂ * b₂)⁻¹ := by rw [← hz1, ← hz2]
          _ = a₁ * a₂⁻¹ := by rw [← hbeq]; group
      have hwZ : z.1 * z'.1⁻¹ ∈ quasithinOmegaOneCenter T :=
        (quasithinOmegaOneCenter T).mul_mem z.2 ((quasithinOmegaOneCenter T).inv_mem z'.2)
      have hw1 := hZZ1 _ hwZ (by rw [hw]; exact Z₁.mul_mem hha1 (Z₁.inv_mem hha2))
      exact Subtype.ext (mul_inv_eq_one.1 hw1)
    calc Nat.card (quasithinOmegaOneCenter T) ≤ Nat.card ↥Z₂ :=
          Nat.card_le_card_of_injective f hinj
      _ = 4 := hZ2c
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hcon
    push Not at hcon
    have h1 : (s1516 T Z₁).relIndex T = 1 := Subgroup.relIndex_eq_one.2 hcon
    omega
  have hSc1 : ∀ s ∈ s1516 T Z₁, ∀ x ∈ Z₁, s * x = x * s := fun s hs x hx =>
    (Subgroup.mem_centralizer_iff.1 (s1516_le_g1 T Z₁ hs) x hx).symm
  have hSc2 : ∀ s ∈ s1516 T Z₁, ∀ y ∈ Z₂, s * y = y * s := by
    intro s hs y hy
    have : s ∈ T ⊓ Subgroup.centralizer (Z₂ : Set G) := by rw [← hdiag]; exact hs
    exact (Subgroup.mem_centralizer_iff.1 this.2 y hy).symm
  have hidx' : ((s1516 T Z₁).subgroupOf T).index = 2 := hidx
  have htt : t * t ∈ s1516 T Z₁ := by
    have := Subgroup.mul_self_mem_of_index_two hidx' (⟨t, htT⟩ : ↥T)
    exact this
  have htg : ∀ g ∈ T, g ∉ s1516 T Z₁ → t⁻¹ * g ∈ s1516 T Z₁ := by
    intro g hg hgS
    have := (Subgroup.mul_mem_iff_of_index_two hidx' (a := (⟨t⁻¹, T.inv_mem htT⟩ : ↥T))
      (b := (⟨g, hg⟩ : ↥T))).2 (by
        constructor
        · intro h1
          exact absurd ((s1516 T Z₁).inv_mem_iff.1 h1) htS
        · intro h2
          exact absurd h2 hgS)
    exact this
  have hZ₁Z₂ : ∀ x ∈ Z₁, t * x * t⁻¹ ∈ Z₂ := by
    intro x hx
    have htS' : t⁻¹ ∉ s1516 T Z₁ := fun h1 => htS ((s1516 T Z₁).inv_mem_iff.1 h1)
    have hsw := hswap t⁻¹ (T.inv_mem htT) htS'
    have hxV₂ : t * x * t⁻¹ ∈ V₂ := by
      have hx1 : x ∈ conjByElt t⁻¹ V₂ := by rw [hsw]; exact hZ₁V₁ hx
      have := mem_conjByElt.1 hx1
      simpa using this
    have hxE : t * x * t⁻¹ ∈ Z₁ ⊔ Z₂ := by
      rw [hS.vE_sup_small hsmall]
      exact conj_mem_vE1516 hTM htT (hS.z1_le hx)
    obtain ⟨a', ha', b', hb', hab⟩ := exists_mul_of_mem_sup_comm4 hcomm hxE
    have ha'V₂ : a' ∈ V₂ := by
      have h1 : a' = (t * x * t⁻¹) * b'⁻¹ := by rw [hab]; group
      rw [h1]
      exact V₂.mul_mem hxV₂ (V₂.inv_mem (hZ₂V₂ hb'))
    have ha'1 : a' = 1 := by
      have : a' ∈ V₁ ⊓ V₂ := ⟨hZ₁V₁ ha', ha'V₂⟩
      rw [hV₁₂inf] at this
      exact Subgroup.mem_bot.1 this
    rw [hab, ha'1, one_mul]
    exact hb'
  have hφ : ∀ x ∈ Z₁, x * (t * x * t⁻¹) ∈ quasithinOmegaOneCenter T := by
    intro x hx
    have hy : t * x * t⁻¹ ∈ Z₂ := hZ₁Z₂ x hx
    have hxV : x ∈ V154 T Mc M := hS.z1_le_V hx
    have hyV : t * x * t⁻¹ ∈ V154 T Mc M := hS.z2_le_V hy
    have hφV : x * (t * x * t⁻¹) ∈ V154 T Mc M := (V154 T Mc M).mul_mem hxV hyV
    have hxy : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x := hVc _ hxV _ hyV
    have hSφ : ∀ s ∈ s1516 T Z₁, s * (x * (t * x * t⁻¹)) = (x * (t * x * t⁻¹)) * s := by
      intro s hs
      calc s * (x * (t * x * t⁻¹)) = (s * x) * (t * x * t⁻¹) := by group
        _ = (x * s) * (t * x * t⁻¹) := by rw [hSc1 s hs x hx]
        _ = x * (s * (t * x * t⁻¹)) := by group
        _ = x * ((t * x * t⁻¹) * s) := by rw [hSc2 s hs _ hy]
        _ = (x * (t * x * t⁻¹)) * s := by group
    have htφ : t * (x * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹) := by
      have h1 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        have := hSc1 (t * t) htt x hx
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
          _ = ((t * t) * x) * (t * t)⁻¹ := rfl
          _ = (x * (t * t)) * (t * t)⁻¹ := by rw [this]
          _ = x := by group
      calc t * (x * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
        _ = (t * x * t⁻¹) * x := by rw [h1]
        _ = x * (t * x * t⁻¹) := hxy.symm
    refine Subgroup.subset_closure ⟨⟨hVT hφV, Subgroup.mem_centralizer_iff.2 ?_⟩, hV2 _ hφV⟩
    intro g hg
    by_cases hgS : g ∈ s1516 T Z₁
    · exact hSφ g hgS
    ·
      have hσ := htg g hg hgS
      have hg' : g = t * (t⁻¹ * g) := by group
      have h1 := hSφ _ hσ
      calc g * (x * (t * x * t⁻¹)) = t * ((t⁻¹ * g) * (x * (t * x * t⁻¹))) := by group
        _ = t * ((x * (t * x * t⁻¹)) * (t⁻¹ * g)) := by rw [h1]
        _ = (t * (x * (t * x * t⁻¹)) * t⁻¹) * g := by group
        _ = (x * (t * x * t⁻¹)) * g := by rw [htφ]
  have hlow : 4 ≤ Nat.card (quasithinOmegaOneCenter T) := by
    let φ : ↥Z₁ → ↥(quasithinOmegaOneCenter T) := fun x => ⟨x.1 * (t * x.1 * t⁻¹), hφ x.1 x.2⟩
    have hφinj : Function.Injective φ := by
      intro x y hxy
      have h1 : x.1 * (t * x.1 * t⁻¹) = y.1 * (t * y.1 * t⁻¹) := congrArg Subtype.val hxy
      have hx2 := hZ₁Z₂ x.1 x.2
      have hy2 := hZ₁Z₂ y.1 y.2
      have h2 : x.1 * y.1⁻¹ = (t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹ := by
        have hc := hcomm y.1⁻¹ (Z₁.inv_mem y.2) (t * x.1 * t⁻¹) hx2
        calc x.1 * y.1⁻¹ = (x.1 * (t * x.1 * t⁻¹)) * (t * x.1 * t⁻¹)⁻¹ * y.1⁻¹ := by group
          _ = (y.1 * (t * y.1 * t⁻¹)) * (t * x.1 * t⁻¹)⁻¹ * y.1⁻¹ := by rw [h1]
          _ = (t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹ := by
              have hcomm' : y.1 * ((t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹) =
                  ((t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹) * y.1 :=
                hcomm y.1 y.2 _ (Z₂.mul_mem hy2 (Z₂.inv_mem hx2))
              calc (y.1 * (t * y.1 * t⁻¹)) * (t * x.1 * t⁻¹)⁻¹ * y.1⁻¹ =
                  y.1 * ((t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹) * y.1⁻¹ := by group
                _ = (((t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹) * y.1) * y.1⁻¹ := by rw [hcomm']
                _ = (t * y.1 * t⁻¹) * (t * x.1 * t⁻¹)⁻¹ := by group
      have hmem : x.1 * y.1⁻¹ ∈ Z₁ ⊓ Z₂ :=
        ⟨Z₁.mul_mem x.2 (Z₁.inv_mem y.2), by rw [h2]; exact Z₂.mul_mem hy2 (Z₂.inv_mem hx2)⟩
      rw [hS.vE_inf] at hmem
      exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem))
    calc 4 = Nat.card ↥Z₁ := hZ1c.symm
      _ ≤ Nat.card (quasithinOmegaOneCenter T) := Nat.card_le_card_of_injective φ hφinj
  omega

end CFSG.Quasithin
