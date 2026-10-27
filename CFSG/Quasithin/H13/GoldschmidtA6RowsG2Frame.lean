module

public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6.GR

namespace G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.H13.VolI Matrix

theorem g2_frame_data
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : G2NaturalDerived L ⊤ ⊥ 1) :
    ∃ (e : V ≃* Multiplicative (Ix3 → ZMod 2)) (ψ : ↥subG2 →* ↥L), Function.Bijective ψ ∧
      ∀ (g : ↥subG2) (w : V), Multiplicative.toAdd (e (((ψ g : ↥L) : MulAut V) w)) =
        muQ g *ᵥ Multiplicative.toAdd (e w) := by
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hKc
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  have hcp : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
    (g2Derived_le K).trans (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).symm.le
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ hle) hπ
  obtain ⟨hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hπ
  let β₀ : V →* (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec :=
    { toFun := fun v => β ⟨v, Subgroup.mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩ }
  let β' : V →* Multiplicative (Ix3 → ZMod 2) :=
    ((zornSecEquiv (F := ZMod 2) ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).toMonoidHom.comp
      (zornQSecEquiv ε).toMonoidHom).comp β₀
  have hβ'inj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h0 : (zornSecEquiv (F := ZMod 2) ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
        (zornQSecEquiv ε (β₀ v)) = 1 := hv
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h0
    have h1 : β ⟨v, Subgroup.mem_top v⟩ = 1 := h0
    exact Subgroup.mem_bot.mp ((hβk ⟨v, Subgroup.mem_top v⟩).1 h1)
  have hβ'surj : Function.Surjective β' := by
    intro y
    obtain ⟨s, hs⟩ := (zornQSecEquiv ε).surjective
      ((zornSecEquiv (F := ZMod 2) ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).symm y)
    obtain ⟨u, hu⟩ := hβs s
    refine ⟨u.1, ?_⟩
    have hu' : β₀ u.1 = s := hu
    show (zornSecEquiv (F := ZMod 2) ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
      (zornQSecEquiv ε (β₀ u.1)) = y
    rw [hu', hs, MulEquiv.apply_symm_apply]
  let θ : ↥subG2 ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
    g2TwoEquiv.symm.trans (g2DerivedFieldEquiv ε).symm
  have hequiv : ∀ (g : ↥subG2) (w : V),
      Multiplicative.toAdd (β' (((π (θ g) : ↥L) : MulAut V) w)) =
        muQ g *ᵥ Multiplicative.toAdd (β' w) := by
    intro g w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ w)
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (zornQSecEquiv ε (β₀ w))
    have hm0 : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act (θ g) m.1 ∈
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
      zornAct_mem_O0 _ hle _ m.2
    have hm'0 : zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
        (g2TwoEquiv.symm g) m'.1 ∈ zornO0 (ZMod 2) :=
      zornAct_mem_O0 _ g2Derived_two_le _ m'.2
    have h1 := hβe (θ g) ⟨w, Subgroup.mem_top w⟩ m (Subgroup.mem_top _) hm0 hm.symm
    have h2 : zornQSecEquiv ε (QuotientGroup.mk m) = QuotientGroup.mk m' := by
      rw [hm, hm']
    have h3 := zornQSecEquiv_act ε (θ g) (g2TwoEquiv.symm g) (MulEquiv.apply_symm_apply _ _)
      m m' h2 hm0 hm'0
    have h3' : zornQSecEquiv ε (QuotientGroup.mk ⟨(FFModel.zornQ ⁅quasithinG2 K,
        quasithinG2 K⁆).act (θ g) m.1, hm0⟩) = QuotientGroup.mk ⟨zornAct
          ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ (g2TwoEquiv.symm g) m'.1, hm'0⟩ := h3
    have h4 : Multiplicative.toAdd (β' w) = zP (Multiplicative.toAdd m'.1) := by
      show Multiplicative.toAdd (zornSecEquiv (F := ZMod 2)
        ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ (zornQSecEquiv ε (β₀ w))) = _
      rw [← hm']
      rfl
    have h5 : Multiplicative.toAdd (β' (((π (θ g) : ↥L) : MulAut V) w)) =
        zP (((g2TwoEquiv.symm g : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
          quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))
            (Multiplicative.toAdd m'.1)) := by
      show Multiplicative.toAdd (zornSecEquiv (F := ZMod 2)
        ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
          (zornQSecEquiv ε (β ⟨((π (θ g) : ↥L) : MulAut V) w, Subgroup.mem_top _⟩))) = _
      rw [h1, h3']
      rfl
    rw [h5, h4, zP_act _ m'.2, ← muK_g2TwoEquiv, MulEquiv.apply_symm_apply, muK_eq_mulVec]
  refine ⟨MulEquiv.ofBijective β' ⟨hβ'inj, hβ'surj⟩, π.comp θ.toMonoidHom, ?_, hequiv⟩
  exact ⟨hinj.comp θ.injective, hπs.comp θ.surjective⟩

theorem commutator_range_eq_map' {G H : Type} [Group G] [Group H] (f : G →* H) :
    ⁅f.range, f.range⁆ = (commutator G).map f := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rfl

theorem g2Derived_of_g2
    {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} (hB4 : B4Hyp G L)
    (h : G2Natural (ffJ G) ⊤ ⊥ 1) : G2NaturalDerived L ⊤ ⊥ 1 := by
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hKc
  have hcp : CharP K 2 := FFC.charTwo_of_card_two hK2
  have hinj : Function.Injective π := FFC.injective_of_zornQ_realizes hπ
  let e : ↥(quasithinG2 K) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨-, -, -, hq⟩ := FFC.b4hyp_data hB4
  have hJL : ffJ G ≠ L := fun hEq =>
    R3c2.not_isQuasisimple_quasithinG2_two hK2 (X := ↥L)
      ((MulEquiv.subgroupCongr hEq.symm).trans e.symm) hq
  obtain ⟨hL, -⟩ := FFC.ident_g2 hB4 hJL hK2 e.symm
  have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
    (g2Derived_le K).trans (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).symm.le
  obtain ⟨hπs, -, -, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := hπ
  let f : ↥(quasithinG2 K) →* MulAut V := (ffJ G).subtype.comp π
  have hrange : f.range = ffJ G := by
    show ((ffJ G).subtype.comp π).range = ffJ G
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective π hπs, Subgroup.map_top,
      Subgroup.range_subtype]
  have hLmap : L = (commutator ↥(quasithinG2 K)).map f := by
    rw [hL, ← hrange, commutator_range_eq_map']
  have hN : (commutator ↥(quasithinG2 K)).map (quasithinG2 K).subtype =
      ⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hmem : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆,
      Subgroup.inclusion hle γ ∈ commutator ↥(quasithinG2 K) := by
    intro γ
    have h1 : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
        (commutator ↥(quasithinG2 K)).map (quasithinG2 K).subtype := by
      rw [hN]
      exact γ.2
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.mp h1
    have : Subgroup.inclusion hle γ = g := Subtype.ext hgγ.symm
    rw [this]
    exact hg
  let π' : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥L :=
    (f.comp (Subgroup.inclusion hle)).codRestrict L fun γ => by
      rw [hLmap]
      exact ⟨_, hmem γ, rfl⟩
  refine ⟨K, hKf, hKfin, hKc, π', ?_, bot_le, zornR_le_zornO0, fun _ _ _ => Subgroup.mem_top _,
    fun h z hz => ?_, fun γ m hm => zornAct_mem_O0 _ hle γ hm,
    fun γ m hm => zornAct_mem_R _ hle γ hm, β, hβs, hβk, fun γ u m hu hm hβ => ?_⟩
  · intro l
    have hl : (l : MulAut V) ∈ (commutator ↥(quasithinG2 K)).map f := by
      rw [← hLmap]
      exact l.2
    obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.mp hl
    have h1 : (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
        ⁅quasithinG2 K, quasithinG2 K⁆ := by
      rw [← hN]
      exact ⟨g, hg, rfl⟩
    refine ⟨⟨g, h1⟩, Subtype.ext ?_⟩
    exact hgl
  · rw [Subgroup.mem_bot.mp hz, map_one]
    exact Subgroup.one_mem _
  · exact hβe (Subgroup.inclusion hle γ) u m hu hm hβ

end G2

end CFSG.Quasithin.H13.A6.GR
