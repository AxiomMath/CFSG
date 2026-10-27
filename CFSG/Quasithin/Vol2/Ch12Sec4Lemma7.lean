module

public import CFSG.Quasithin.Vol2.Ch12Sec4Cx
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem centralizer_singleton_eq_conjugate {v z k : G} (hk : k⁻¹ * v * k = z) :
    Subgroup.centralizer ({z} : Set G) =
      CFSG.conjugate (Subgroup.centralizer ({v} : Set G)) k := by
  ext x
  rw [mem_conjugate_iff_mul_mem, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← hk]
  constructor
  · intro hx
    calc k * x * k⁻¹ * v = k * (x * (k⁻¹ * v * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * v * k) * x) * k⁻¹ := by rw [hx]
      _ = v * (k * x * k⁻¹) := by group
  · intro hx
    calc x * (k⁻¹ * v * k) = k⁻¹ * ((k * x * k⁻¹) * v) * k := by group
      _ = k⁻¹ * (v * (k * x * k⁻¹)) * k := by rw [hx]
      _ = k⁻¹ * v * k * x := by group

theorem lemma12_4_7_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h1246 : Lemma12_4_6) (hCov : G2NaturalCover) (hOrb : OrbitG2Weyl)
    (hNorm : G2WeylNormalizerOrbits) : Lemma12_4_7 := by
  intro G _ _ T L V hcx hq v hv g hgv
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx hq
  have := hf.comm
  by_cases hv1 : v = 1
  · exact ⟨1, L.one_mem, by rw [hv1]; group⟩
  have hv'1 : g⁻¹ * v * g ≠ 1 := fun h => hv1 (by
    calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTz := hf.T_le_centralizer hTL
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.1 (hTz ht)
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hcommGr := commV_autOn_eq_top hf.normalizes hf.commutator
  have hS : IsPGroup 2 (autOn T V) := isPGroup_autOn hyp.sylow.1
  have hSN : ∀ s ∈ autOn T V, ∀ h, h ∈ autOn L V ↔ s * h * s⁻¹ ∈ autOn L V := fun s hs =>
    Subgroup.mem_normalizer_iff.1 (autOn_le_normalizer_autOn_of_le hTL hs)
  rcases hq with h3' | hU
  ·
    obtain ⟨hV16, -, -, hnat⟩ := cx_l3_module h1222 hcx hf h3'
    have htrans : ∀ u ∈ V, u ∉ Subgroup.centralizer (L : Set G) → ∀ w ∈ V,
        w ∉ Subgroup.centralizer (L : Set G) → ∃ l ∈ L, l * u * l⁻¹ = w := by
      intro u hu huL w hw hwL
      have hu' : (⟨u, hu⟩ : ↥V) ∉ fixV (autOn L V) := by
        rw [fixV_autOn_eq hf.normalizes]
        exact huL
      have hw' : (⟨w, hw⟩ : ↥V) ∉ fixV (autOn L V) := by
        rw [fixV_autOn_eq hf.normalizes]
        exact hwL
      obtain ⟨x, hx, hxu⟩ := exists_mem_apply_eq_of_l3 hW hV16 hnat hcommGr hu' hw'
      obtain ⟨l, hl, hle⟩ := exists_eq_conj_of_mem_autOn hf.normalizes hx
      refine ⟨l, hl, ?_⟩
      rw [← hle ⟨u, hu⟩, hxu]
    obtain ⟨D⟩ := hnat.toL3Coord
    have hSX : autOn T V ≤ autOn L V := fun s hs =>
      Vol2.Ch10.SecD.mem_of_normalizes D hcommGr (hSN s hs)
    obtain ⟨E₀, hE₀4, -, hE₀S⟩ := exists_card_four_of_l3 hV16 hnat hSX hS
    have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
      rw [fixV_autOn_eq hf.normalizes, card_subgroupOf_eq_card_inf, hf.card_zV]
    obtain ⟨e, heE, heZ⟩ : ∃ e ∈ E₀, e ∉ fixV (autOn L V) := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (fun x hx => h x hx : E₀ ≤ fixV (autOn L V))
      omega
    have heL : (e : G) ∉ Subgroup.centralizer (L : Set G) := by
      rw [fixV_autOn_eq hf.normalizes] at heZ
      exact heZ
    have hEV : E₀.map V.subtype ≤ V := Subgroup.map_subtype_le E₀
    have hE4 : Nat.card (E₀.map V.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective V.subtype_injective, hE₀4]
    have hkey : ∀ t ∈ T, ∀ x ∈ E₀.map V.subtype, t * x * t⁻¹ ∈ E₀.map V.subtype := by
      rintro t ht _ ⟨x, hx, rfl⟩
      have hs : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn T V :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
      refine ⟨_, hE₀S _ hs x hx, ?_⟩
      exact A5Mod.conjAct_apply_coe V ⟨t, hf.T_le ht⟩ x
    have hTE : T ≤ Subgroup.normalizer ((E₀.map V.subtype : Subgroup G) : Set G) := fun t ht =>
      B6.mem_normalizer_of_forall_mem (hkey t ht)
        (fun x hx => by simpa using hkey t⁻¹ (T.inv_mem ht) x hx)
    have heE' : (e : G) ∈ E₀.map V.subtype := ⟨e, heE, rfl⟩
    obtain ⟨hR₁, hR₁T⟩ := h1246 G T L V hcx h3' _ hEV hE4 hTE _ heE' heL
    have hnotz : ∀ w ∈ V, w ∉ Subgroup.centralizer (L : Set G) → ∀ h : G, h⁻¹ * w * h ≠ z := by
      intro w hw hwL h hh
      obtain ⟨l, hl, hlw⟩ := htrans _ e.2 heL w hw hwL
      have hk : (l⁻¹ * h)⁻¹ * (e : G) * (l⁻¹ * h) = z := by
        rw [← hh, ← hlw]
        group
      have hCz := centralizer_singleton_eq_conjugate hk
      have hTsyl : QuasithinUnique.IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
        isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTz
      have h1 := hTsyl.card_eq
      have h2 := hR₁.card_eq
      have h3 : QuasithinUnique.twoPart (Subgroup.centralizer ({z} : Set G)) =
          QuasithinUnique.twoPart (Subgroup.centralizer ({(e : G)} : Set G)) := by
        unfold QuasithinUnique.twoPart
        rw [hCz, card_conjugate_eq]
      have h4 := Subgroup.relIndex_mul_card
        (T ⊓ Subgroup.centralizer ((E₀.map V.subtype : Subgroup G) : Set G)) T
      rw [inf_eq_left.2 (inf_le_left.trans (le_refl T)), hR₁T] at h4
      have hpos : 0 < Nat.card ↥(T ⊓ Subgroup.centralizer
          ((E₀.map V.subtype : Subgroup G) : Set G)) := Nat.card_pos
      omega
    by_cases hvL : v ∈ Subgroup.centralizer (L : Set G)
    ·
      have hvz : v = z := hf.eq_of_mem_zV ⟨hv, hvL⟩ hv1
      have hgL : g⁻¹ * v * g ∈ Subgroup.centralizer (L : Set G) := by
        by_contra hgL
        apply hnotz _ hgv hgL g⁻¹
        rw [hvz]
        group
      have hgz := hf.eq_of_mem_zV ⟨hgv, hgL⟩ hv'1
      refine ⟨1, L.one_mem, ?_⟩
      rw [hgz, inv_one, one_mul, mul_one, hvz]
    · have hgL : g⁻¹ * v * g ∉ Subgroup.centralizer (L : Set G) := fun hgL =>
        hnotz v hv hvL g (hf.eq_of_mem_zV ⟨hgv, hgL⟩ hv'1)
      obtain ⟨l, hl, hle⟩ := htrans v hv hvL _ hgv hgL
      exact ⟨l⁻¹, inv_mem hl, by rw [inv_inv]; exact hle⟩
  ·
    obtain ⟨-, hnat⟩ := cx_g2_module h1222 hcx hf hU
    have hzV' : (⟨z, hf.mem_zV.1⟩ : ↥V) ∈ fixV (autOn L V) := by
      rw [fixV_autOn_eq hf.normalizes]
      exact hf.mem_zV.2
    have hz1' : (⟨z, hf.mem_zV.1⟩ : ↥V) ≠ 1 := fun h => hf.ne_one (congrArg Subtype.val h)
    have hWeyl : G2WeylDerived (autOn L V) := by
      rcases hCov ↥V hW (autOn L V) (fixV (autOn L V)) le_rfl hcommGr hnat with h0 | ⟨-, -, h⟩
      · exfalso
        rw [h0] at hzV'
        exact hz1' ((Subgroup.mem_bot).1 hzV')
      · exact h
    obtain ⟨hlen, hsep⟩ := hOrb ↥V (autOn L V) _ hz1' hzV' hWeyl
    obtain ⟨u₁, hu₁V, hu₁L⟩ : ∃ u₁ ∈ V, u₁ ∉ Subgroup.centralizer (L : Set G) := by
      by_contra h
      push Not at h
      apply hf.notCent
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.1 (h w hw) l hl).symm
    have hu₁1 : (⟨u₁, hu₁V⟩ : ↥V) ≠ 1 := fun h => hu₁L (by
      rw [show u₁ = 1 from congrArg Subtype.val h]
      exact Subgroup.one_mem _)
    have hu₁z : (⟨u₁, hu₁V⟩ : ↥V) ≠ ⟨z, hf.mem_zV.1⟩ := fun h => hu₁L (by
      rw [show u₁ = z from congrArg Subtype.val h]
      exact hf.mem_zV.2)
    obtain ⟨u, hu1, huz, hufix⟩ :=
      exists_fixed_of_g2Weyl hOrb hNorm hWeyl hz1' hzV' hu₁1 hu₁z hS hSN
    have huT : (u : G) ∈ Subgroup.centralizer (T : Set G) := by
      have h1 : u ∈ fixV (autOn T V) := fun s hs => hufix s hs
      rw [fixV_autOn_eq hf.T_le] at h1
      exact h1
    have hrep : ∀ y ∈ V, y ≠ 1 → ∃ l ∈ L, ∃ x ∈ V, x ∈ Subgroup.centralizer (T : Set G) ∧
        l * y * l⁻¹ = x := by
      intro y hy hy1
      by_cases hyL : y ∈ Subgroup.centralizer (L : Set G)
      · have hyz := hf.eq_of_mem_zV ⟨hy, hyL⟩ hy1
        exact ⟨1, L.one_mem, z, hf.mem_zV.1, hzT, by rw [hyz]; group⟩
      · have hy' : (⟨y, hy⟩ : ↥V) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
        have hyz' : (⟨y, hy⟩ : ↥V) ≠ ⟨z, hf.mem_zV.1⟩ := fun h => hyL (by
          rw [show y = z from congrArg Subtype.val h]
          exact hf.mem_zV.2)
        have hc : Nat.card (Orbit.orbitIn (autOn L V) ⟨y, hy⟩) =
            Nat.card (Orbit.orbitIn (autOn L V) u) := by
          rw [List.mem_singleton.1 (hlen _ hy' hyz'), List.mem_singleton.1 (hlen _ hu1 huz)]
        obtain ⟨a, ha, hau⟩ := hsep _ u hy' hu1 hyz' huz hc
        obtain ⟨l, hl, hle⟩ := exists_eq_conj_of_mem_autOn hf.normalizes ha
        refine ⟨l, hl, _, (a ⟨y, hy⟩).2, ?_, (hle ⟨y, hy⟩).symm⟩
        rcases hau with h | h
        · rw [h]
          exact huT
        · rw [h]
          exact Subgroup.mul_mem _ huT hzT
    obtain ⟨l₁, hl₁, x, hxV, hxT, hx⟩ := hrep v hv hv1
    obtain ⟨l₂, hl₂, x', -, hx'T, hx'⟩ := hrep _ hgv hv'1
    have hk : (l₁ * g * l₂⁻¹)⁻¹ * x * (l₁ * g * l₂⁻¹) = x' := by
      rw [← hx, ← hx']
      group
    obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    obtain ⟨-, -, -, hNT, -⟩ := h331B L hyp.maximal hyp.quasisimple
    rw [hyp.conjClosure_eq] at hNT
    obtain ⟨n, hnN, hn⟩ :=
      (hyp.sylow.1.toSylow hyp.sylow.2).conj_eq_normalizer_conj_of_mem_centralizer
        x (l₁ * g * l₂⁻¹) hxT (by rw [hk]; exact hx'T)
    have hnL : n ∈ Subgroup.normalizer (L : Set G) := hNT hnN
    have hnV : n ∈ Subgroup.normalizer (V : Set G) := hf.MN ▸ hnL
    obtain ⟨a, ha, hax⟩ := hNorm ↥V (autOn L V) hWeyl (conjAct V ⟨n⁻¹, inv_mem hnV⟩)
      (fun h => conj_mem_autOn_iff (inv_mem hnL) (inv_mem hnV) h) ⟨x, hxV⟩
    obtain ⟨l₃, hl₃, hle₃⟩ := exists_eq_conj_of_mem_autOn hf.normalizes ha
    have h1 : l₃ * x * l₃⁻¹ = n⁻¹ * x * n := by
      have h2 := hle₃ ⟨x, hxV⟩
      rw [hax, A5Mod.conjAct_apply_coe, inv_inv] at h2
      exact h2.symm
    refine ⟨l₁⁻¹ * l₃⁻¹ * l₂, L.mul_mem (L.mul_mem (inv_mem hl₁) (inv_mem hl₃)) hl₂, ?_⟩
    calc (l₁⁻¹ * l₃⁻¹ * l₂)⁻¹ * v * (l₁⁻¹ * l₃⁻¹ * l₂) =
          l₂⁻¹ * (l₃ * (l₁ * v * l₁⁻¹) * l₃⁻¹) * l₂ := by group
      _ = l₂⁻¹ * (n⁻¹ * x * n) * l₂ := by rw [hx, h1]
      _ = l₂⁻¹ * ((l₁ * g * l₂⁻¹)⁻¹ * x * (l₁ * g * l₂⁻¹)) * l₂ := by rw [hn]
      _ = g⁻¹ * v * g := by rw [← hx]; group

end CFSG.Quasithin.H13
