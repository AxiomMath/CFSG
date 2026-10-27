module

public import CFSG.Quasithin.Vol2.Ch11SecSXK2
public import CFSG.Quasithin.Vol2.Ch11SecSPGL2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSK0d
public import CFSG.Quasithin.Vol2.Ch11SecSXCard

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem card_modO2Image_of_odd {Y X : Subgroup G} (hXY : X ≤ Y) (hX : Odd (Nat.card ↥X)) :
    Nat.card ↥(modO2Image Y X) = Nat.card ↥X := by
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (X.subgroupOf Y).subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxO : ((x : ↥Y) : G) ∈ pCoreOf 2 Y := by
      rw [pCoreOf_two_eq_map]
      exact ⟨_, hx, rfl⟩
    have hbot := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hX
    have : ((x : ↥Y) : G) ∈ pCoreOf 2 Y ⊓ X := ⟨hxO, x.2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have h1 : modO2Image Y X = φ.range := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem xOne_k0Of_ne_bot (hT : FactPGL34Torus) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) : xOne X (k0Of K P₂) ≠ ⊥ := by
  set Y := K ⊔ xOne X (LOf L V₁) with hY
  have hKY : K ≤ Y := le_sup_left
  have hL₁Y : LOf L V₁ ≤ Y := h.L₁_le_K.trans hKY
  have hK₀Y : k0Of K P₂ ≤ Y := (k0Of_le K P₂).trans hKY
  have hXY : X ≤ Y := hc.a.trans (sup_le le_sup_right (inf_le_right.trans hL₁Y))
  have hSY := h.isSylowTwoOf_inf_sup hN h1102 hc
  have hOY : pCoreOf 2 Y ≤ T ⊓ K := pCoreOf_two_le_of_isSylowTwoOf hSY
  have hQs := isSolvable_pCoreOf_two Y
  have hQ₁ : pCoreOf 2 Y ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    hOY.trans (inf_le_left.trans h.T_le_normalizer_L₁)
  have hQ₀ : pCoreOf 2 Y ≤ Subgroup.normalizer (k0Of K P₂ : Set G) :=
    hOY.trans (inf_le_left.trans (h.T_le_normalizer_k0Of hP))
  have hL₁ne : LOf L V₁ ≠ ⊥ := fun hb => hP.c₁.1 (by
    rw [← hP.l₁, hb]; unfold modO2Image; simp)
  obtain ⟨F, _, _, hF, he⟩ := h.pgl
  have hKR : modO2Image Y K ≤ ⁅(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)), ⊤⁆ := by
    rw [← modO2Image_perfect hKY h.perfect]
    exact Subgroup.commutator_mono le_top le_top
  have hne' : ∀ B : Subgroup G, B ≤ K → ⁅B, B⁆ = B →
      pCoreOf 2 Y ≤ Subgroup.normalizer (B : Set G) → B ≠ K →
        modO2Image Y B ≠ ⁅(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)), ⊤⁆ := by
    intro B hBK hBp hQB hBne heq
    apply hBne
    refine le_antisymm hBK ?_
    have h1 := le_sup_of_modO2Image_le hKY (hBK.trans hKY) (heq ▸ hKR)
    calc K = perfectCore K := (perfectCore_eq_self_of_perfect h.perfect).symm
      _ ≤ perfectCore (B ⊔ pCoreOf 2 Y) := perfectCore_mono h1
      _ = B := perfectCore_sup_eq hBp hQs hQB
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hcard : Nat.card ↥(modO2Image Y X) = 9 := by
    rw [card_modO2Image_of_odd hXY h.cartan.2.1,
      card_cartan hc hXN (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)]
  have hE := hT _ ⟨F, inferInstance, inferInstance, hF, he⟩ _ _ _ (isSylowTwoOf_modO2Image hSY)
    ?_ (modO2Image_ne_bot hL₁Y h.perfect_L₁ hL₁ne)
    (modO2Image_ne_bot hK₀Y (k0Of_perfect K P₂) hP.k0Of_ne_bot)
    (modO2Image_perfect hL₁Y h.perfect_L₁) (modO2Image_perfect hK₀Y (k0Of_perfect K P₂))
    (hne' _ h.L₁_le_K h.perfect_L₁ hQ₁ h.L₁_ne_K)
    (hne' _ (k0Of_le K P₂) (k0Of_perfect K P₂) hQ₀ (k0Of_ne_K hP))
    (modO2Image_le_normalizer (inf_le_left.trans h.T_le_normalizer_L₁))
    (modO2Image_le_normalizer (inf_le_left.trans (h.T_le_normalizer_k0Of hP)))
    (modO2Image Y X) (modO2Image_le_normalizer (h.cartan_le_normalizer_inf hN h1102 hP)) hcard
  · obtain ⟨⟨e, heE, heC⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    obtain ⟨⟨x, hxY⟩, hxX, rfl⟩ := heE
    have hxC := mem_sectionCentralizer_of_mk hK₀Y hxY
      (h.cartan_le_normalizer_k0Of hN h1102 hP hxX) heC
    intro hbot
    have hx1 : x ∈ (⊥ : Subgroup G) := hbot ▸ (⟨hxX, hxC⟩ : x ∈ xOne X (k0Of K P₂))
    rw [Subgroup.mem_bot] at hx1
    subst hx1
    refine hne1 (Subtype.ext ?_)
    change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) 1 = 1
    exact map_one _
  · intro heq
    have h1 := sup_eq_of_modO2Image_eq hL₁Y hK₀Y heq
    apply k0Of_ne_L₁ hP
    rw [← perfectCore_sup_eq (k0Of_perfect K P₂) hQs hQ₀, ← h1,
      perfectCore_sup_eq h.perfect_L₁ hQs hQ₁]

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
