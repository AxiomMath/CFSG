module

public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.QTFE14Cat
public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1417

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc : Subgroup G}

@[expose] def inclMod {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := fun a b => IntMod.val_mul a b

theorem exists_Z_of_normal_in_T (h : quasithinQTFE14Cat G T Mc) {W₀ V : Subgroup G}
    (hVe : IsElemAbelian 2 V) (hW₀V : W₀ ≤ V) (hVT : V ≤ T) (hne : W₀ ≠ ⊥)
    (hn : T ≤ Subgroup.normalizer (W₀ : Set G)) :
    ∃ w ∈ W₀, w ≠ 1 ∧ w ∈ quasithinOmegaOneCenter T := by
  have hW₀T : W₀ ≤ T := hW₀V.trans hVT
  have hTnil : Group.IsNilpotent T := h.sylow.1.isNilpotent
  have hWTnormal : (W₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW₀T).mpr hn
  have hWT' : W₀.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hW₀T, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hWT')
  have hwW : (w : G) ∈ W₀ := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1
  have hwZ : (w : G) ∈ quasithinOmegaOneCenter T := by
    apply Subgroup.subset_closure
    refine ⟨⟨w.2, ?_⟩, hVe.2 _ (hW₀V hwW)⟩
    show (w : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
    exact (congrArg Subtype.val this)
  exact ⟨w, hwW, fun h1 => hw1 (Subtype.ext (Subtype.ext h1)), hwZ⟩

theorem exists_Z_of_stable (h : quasithinQTFE14Cat G T Mc) {V : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hTN : T ≤ Subgroup.normalizer (V : Set G)) {U : Subgroup (IntMod V hVe)}
    (hU : U ≠ ⊥) (hst : ∀ g ∈ autI hVe T, ∀ u ∈ U, g u ∈ U) :
    ∃ u ∈ U, u ≠ 1 ∧ IntMod.val u ∈ quasithinOmegaOneCenter T := by
  set W₀ : Subgroup G := U.map (inclMod hVe) with hW₀
  have hW₀V : W₀ ≤ V := by
    rintro _ ⟨u, -, rfl⟩
    exact IntMod.val_mem u
  have hmem : ∀ t ∈ T, ∀ w ∈ W₀, t * w * t⁻¹ ∈ W₀ := by
    intro t ht w hw
    obtain ⟨u, hu, rfl⟩ := hw
    have htN : t ∈ Subgroup.normalizer (V : Set G) := hTN ht
    refine ⟨convI hVe ⟨t, htN⟩ u, hst _ (convI_mem_autI hVe ht htN) u hu, ?_⟩
    exact convI_apply_val hVe ⟨t, htN⟩ u
  have hn : T ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hmem t ht w hw, fun hw => ?_⟩
    have := hmem t⁻¹ (T.inv_mem ht) _ hw
    simpa [mul_assoc] using this
  have hne : W₀ ≠ ⊥ := by
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    intro hbot
    have : (u : IntMod V hVe).val ∈ W₀ := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 (Subtype.ext (IntMod.val_injective (by simpa using this)))
  obtain ⟨w, ⟨u, hu, rfl⟩, hw1, hwZ⟩ := exists_Z_of_normal_in_T h hVe hW₀V hVT hne hn
  refine ⟨u, hu, fun h1 => hw1 ?_, hwZ⟩
  rw [h1]
  rfl

theorem centralizer_singleton_le_mc (h : quasithinQTFE14Cat G T Mc) {w : G}
    (hw : w ∈ quasithinOmegaOneCenter T) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set G) ≤ Mc := by
  have hwT : w ∈ T := (Subgroup.closure_le _).2 (fun z hz => hz.1.1) hw
  set P : Subgroup G := Subgroup.zpowers w
  have hPp : IsPGroup 2 P := h.sylow.1.to_le (Subgroup.zpowers_le.mpr hwT)
  have hP1 : P ≠ ⊥ := by
    intro hb
    exact hw1 ((Subgroup.zpowers_eq_bot).mp hb)
  have hCN : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have : Subgroup.centralizer ({w} : Set G) = Subgroup.centralizer (P : Set G) := by
      change _ = Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [this]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨M'', hM'', hNM''⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (P : Set G)) ⟨P, hP1, hPp, rfl⟩
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M'' := by
    refine le_trans ?_ (hCN.trans hNM'')
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw)
  have hM''eq : M'' = Mc := h.mc_unique M'' hM'' hCZ
  intro x hx
  rw [← hM''eq]
  exact hNM'' (hCN hx)

theorem isSolvable_autI {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hper : perfectCore M ≤ Subgroup.centralizer (V : Set G)) :
    Group.IsSolvable ↥(autI hV M) := by
  rw [isSolvable_iff_perfectCore_eq_bot]
  have h1 : (perfectCore (M.subgroupOf (Subgroup.normalizer (V : Set G)))).map (convI hV) =
      perfectCore (autI hV M) := map_perfectCore (convI hV) _
  rw [← h1]
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  have h2 : (perfectCore (M.subgroupOf (Subgroup.normalizer (V : Set G)))).map
      (Subgroup.normalizer (V : Set G)).subtype = perfectCore M := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hMN]
  have h3 : (x : G) ∈ perfectCore M := by
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot]
  exact (convI_eq_one_iff hV x).mpr (hper h3)

theorem pRank_top_le_two (h : quasithinQTFE14Cat G T Mc) {M : Subgroup G}
    (hM : quasithinIsMaxTwoLocal M) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ 2 := by
  intro p hp hp2
  have h1 := CFSG.SectionRank.pRank_le_map hp.one_lt M.subtype M.subtype_injective
    (⊤ : Subgroup ↥M)
  have h0 : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h0] at h1
  have h2 := A1b.pRank_le_evenRank hp hp2 hM.1
  have h3 : CFSG.Open.evenRank G ≤ 2 := h.qtke.2.2
  omega

omit [Finite G] in
theorem conjAut_autI_thompsonJ {V H : Subgroup G} (hV : IsElemAbelian 2 V) :
    ∀ g ∈ autI hV H, B1.conjAut g (autI hV (thompsonJ H)) = autI hV (thompsonJ H) := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hg
  have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
  rw [conjAut_eq_map, autI_cjSub hV hyN (thompsonJ H),
    B2F.cjSub_eq_of_mem_normalizer
      (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hy))]

theorem omegaOneCenter_le_omegaOneCenterOf (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  refine (Subgroup.closure_le _).2 fun z hz => Subgroup.subset_closure ⟨⟨hz.1.1, ?_⟩, hz.2⟩
  exact Subgroup.centralizer_le (iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hz.1.2

theorem omegaOneCenterOf_inf_eq {T V : Subgroup G} (hVe : IsElemAbelian 2 V) (hVT : V ≤ T) :
    omegaOneCenterOf (thompsonJ T) ⊓ V = V ⊓ Subgroup.centralizer (thompsonJ T : Set G) := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.2, ?_⟩
    have : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
      (Subgroup.closure_le _).2 fun z hz => hz.1.2
    exact this hx.1
  · intro x hx
    refine ⟨?_, hx.1⟩
    rw [omegaOneCenterOf, ← omegaOneCenterOf, ← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨hVT hx.1, hx.2⟩, hVe.2 x hx.1⟩

end Setup

end S1417

end CFSG.Quasithin
