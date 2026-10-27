module

public import CFSG.RankThree.PartOne.KF.F132Dih
public import CFSG.RankThree.PartOne.KF.F132Core

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

section Engine

variable {G : Type} [Group G] {p : ℕ} {c : G} {L E : Subgroup G} {Γ V : Type} [Group Γ] [Group V]
  {act : Γ →* MulAut V}

theorem autMoved_actF_map {F : Subgroup G} (S : WCtx act L F) (γ : Γ) :
    autMoved F (S.actF γ) = (movedV (act γ)).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨act γ d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

theorem actF_injective_of_inj {F : Subgroup G} (S : WCtx act L F) (hinj : Function.Injective act) :
    Function.Injective S.actF := fun _ _ h => hinj ((MulAut.congr S.tor).injective h)

theorem exists_engine_reflection {n : ℕ} {act : DihedralGroup n →* MulAut V}
    (S : WCtx act L (E ⊓ L)) (R : Sec12Three.Restr c L E (E ⊓ L))
    (hinj : Function.Injective S.actF) (k : ZMod n)
    (hk : IsAutReflection p (E ⊓ L) (S.actF (DihedralGroup.sr k))) :
    ∃ (t : MulAut E) (ht : t ∈ torusImage E L), IsAutReflection p E t ∧
      weylG S R hinj ⟨t, ht⟩ = DihedralGroup.sr k := by
  obtain ⟨g, hgF, hgL, hgγ⟩ := S.exists_elt (DihedralGroup.sr k)
  have hgE : g ∈ Subgroup.normalizer (E : Set G) := R.inf_normalizer_ge ⟨hgL, hgF⟩
  have hmem : conjAut E g hgE ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.mpr ⟨g, hgL, hgE, rfl⟩
  have hw : weylG S R hinj ⟨conjAut E g hgE, hmem⟩ = DihedralGroup.sr k := by
    apply hinj
    rw [actF_weylG S R hinj hgL hgE hgF, hgγ]
    rfl
  refine ⟨conjAut E g hgE, hmem, ?_, hw⟩
  have := (isAutReflection_iff_weylG (p := p) S R hinj ⟨conjAut E g hgE, hmem⟩).2
  rw [hw] at this
  exact this hk

theorem exists_sr_of_reflection {n : ℕ} {act : DihedralGroup n →* MulAut V}
    (S : WCtx act L (E ⊓ L)) (R : Sec12Three.Restr c L E (E ⊓ L))
    (hinj : Function.Injective S.actF)
    (hrefl : ∀ γ : DihedralGroup n, γ * γ = 1 → γ ≠ 1 → Nat.card (movedV (act γ)) = p →
      ∃ i : ZMod n, γ = DihedralGroup.sr i)
    {t : MulAut E} (ht : t ∈ torusImage E L) (hr : IsAutReflection p E t) :
    ∃ i : ZMod n, weylG S R hinj ⟨t, ht⟩ = DihedralGroup.sr i := by
  set γ := weylG S R hinj ⟨t, ht⟩ with hγ
  obtain ⟨hord, hcard⟩ := (isAutReflection_iff_weylG (p := p) S R hinj ⟨t, ht⟩).1 hr
  rw [← hγ] at hord hcard
  have hγ2 : γ * γ = 1 := by
    apply hinj
    rw [map_mul, map_one, ← pow_two]
    have := pow_orderOf_eq_one (S.actF γ)
    rwa [hord] at this
  have hγ1 : γ ≠ 1 := by
    intro h1
    rw [h1, map_one, orderOf_one] at hord
    omega
  have hmov : Nat.card (movedV (act γ)) = p := by
    rw [autMoved_actF_map S γ, Subgroup.card_map_of_injective S.tor.injective] at hcard
    exact hcard
  exact hrefl γ hγ2 hγ1 hmov

theorem isAutReflection_actF_sr {n : ℕ} {act : DihedralGroup n →* MulAut V} {F : Subgroup G}
    (S : WCtx act L F) (hinj : Function.Injective S.actF) (k : ZMod n)
    (hmov : Nat.card (movedV (act (DihedralGroup.sr k))) = p) :
    IsAutReflection p F (S.actF (DihedralGroup.sr k)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective S.actF hinj, DihedralGroup.orderOf_sr]
  · rw [autMoved_actF_map S, Subgroup.card_map_of_injective S.tor.injective]
    exact hmov

theorem fix_of_weylG_fix {n : ℕ} {act : DihedralGroup n →* MulAut V}
    (S : WCtx act L (E ⊓ L)) (R : Sec12Three.Restr c L E (E ⊓ L))
    (hinj : Function.Injective S.actF) {t : MulAut E} (ht : t ∈ torusImage E L) (d : V)
    (hd : act (weylG S R hinj ⟨t, ht⟩) d = d) :
    ((t ⟨((S.tor d : ↥(E ⊓ L)) : G), R.F_le_E (S.tor d).2⟩ : E) : G) =
      ((S.tor d : ↥(E ⊓ L)) : G) := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage ht
  have hxF : x ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    R.inf_normalizer_le ⟨hxL, hxE⟩
  have hγ : (⟨t, ht⟩ : ↥(torusImage E L)) =
      ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr ⟨x, hxL, hxE, rfl⟩⟩ := Subtype.ext hx
  have hA := actF_weylG S R hinj hxL hxE hxF
  rw [← hγ] at hA
  have h1 : S.actF (weylG S R hinj ⟨t, ht⟩) (S.tor d) = S.tor d := by
    rw [S.actF_apply, hd]
  rw [hA] at h1
  have h2 := congrArg (fun e : ↥(E ⊓ L) => (e : G)) h1
  have h3 : x * ((S.tor d : ↥(E ⊓ L)) : G) * x⁻¹ = ((S.tor d : ↥(E ⊓ L)) : G) := h2
  rw [hx]
  exact h3

theorem g2v_ne_one_of_primitive {K : Type} [Field K] {z : rootsOfUnity p K} (hp1 : 1 < p)
    (hz : IsPrimitiveRoot (z : Kˣ) p) : z ≠ 1 := fun h =>
  hz.ne_one hp1 (congrArg Subtype.val h)

end Engine

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kfAt_of_core_refl
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L) {b : G} {K : Subgroup G}
    (hd : LayerCore p A L b K) {g : ℕ} (hg3 : 3 ≤ g)
    (hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 2 2 g)
    {t : MulAut E} (htr : IsAutReflection p E t) (htL : t ∈ torusImage E L)
    (hsplit : E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
      Nat.card ↥(autMovedInG E t) = p)
    (hbE : b ∈ E) (hbt : ((t ⟨b, hbE⟩ : E) : G) = b) : KFAt p E g t := by
  obtain ⟨hbA, hbL, hb1⟩ := hd.b_mem
  have hK := hd.K_eq
  subst hK
  have hZ : Subgroup.center ↥(kLayer L b) = ⊥ :=
    psl2EvenCenterTrivial_of_multipliers hGA hg3 hd.K_qs hmodel
  have hAK : Nat.card ↥(E ⊓ kLayer L b) = p := by rw [hEA]; exact hd.A_K
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  exact (kfAt_of_layer h hE3 h.L_le_centralizer hcL htr htL hsplit hbE hbL hb1 hbt hAK hmodel hZ).1

theorem exists_dihedral_conj_parity {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) :
    ∀ i₀ i : ZMod n, i₀.val % 2 = i.val % 2 →
      ∃ w : DihedralGroup n, w * DihedralGroup.sr i₀ * w⁻¹ = DihedralGroup.sr i := by
  rcases hn with rfl | rfl | rfl <;> decide +kernel

variable {n : ℕ} {V : Type} [Group V] {act : DihedralGroup n →* MulAut V}

theorem kfAt_dih_classes
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (S : WCtx act L (E ⊓ L)) (hinj : Function.Injective act)
    (hrefl : ∀ γ : DihedralGroup n, γ * γ = 1 → γ ≠ 1 → Nat.card (movedV (act γ)) = p →
      ∃ i : ZMod n, γ = DihedralGroup.sr i)
    (hmov0 : Nat.card (movedV (act (DihedralGroup.sr 0))) = p)
    (hmov1 : Nat.card (movedV (act (DihedralGroup.sr 1))) = p)
    {v₀ v₁ : V} (hv₀ : act (DihedralGroup.sr 0) v₀ = v₀) (hv₁ : act (DihedralGroup.sr 1) v₁ = v₁)
    {K₀ K₁ : Subgroup G} {g₀ g₁ : ℕ}
    (hd₀ : LayerCore p A L ((S.tor v₀ : ↥(E ⊓ L)) : G) K₀) (hg₀ : 3 ≤ g₀)
    (hm₀ : StatedClassicalModel (↥K₀ ⧸ Subgroup.center ↥K₀) .PSL 2 2 g₀)
    (hd₁ : LayerCore p A L ((S.tor v₁ : ↥(E ⊓ L)) : G) K₁) (hg₁ : 3 ≤ g₁)
    (hm₁ : StatedClassicalModel (↥K₁ ⧸ Subgroup.center ↥K₁) .PSL 2 2 g₁) :
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E g₀ t ∨ KFAt p E g₁ t := by
  classical
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hinjF := actF_injective_of_inj S hinj
  have hconj := exists_dihedral_conj_parity hn
  have hone : (1 : ZMod n).val = 1 := by rcases hn with rfl | rfl | rfl <;> rfl
  obtain ⟨t₀, ht₀L, hr₀, hw₀⟩ := exists_engine_reflection (p := p) S R hinjF 0
    (isAutReflection_actF_sr S hinjF 0 hmov0)
  obtain ⟨t₁, ht₁L, hr₁, hw₁⟩ := exists_engine_reflection (p := p) S R hinjF 1
    (isAutReflection_actF_sr S hinjF 1 hmov1)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hfix₀ := fix_of_weylG_fix S R hinjF ht₀L v₀ (by rw [hw₀]; exact hv₀)
  have hfix₁ := fix_of_weylG_fix S R hinjF ht₁L v₁ (by rw [hw₁]; exact hv₁)
  have hbE₀ : ((S.tor v₀ : ↥(E ⊓ L)) : G) ∈ E := R.F_le_E (S.tor v₀).2
  have hbE₁ : ((S.tor v₁ : ↥(E ⊓ L)) : G) ∈ E := R.F_le_E (S.tor v₁).2
  have hK₀ : KFAt p E g₀ t₀ :=
    kfAt_of_core_refl hGA h hEA hcL hd₀ hg₀ hm₀ hr₀ ht₀L (hF13.reflection t₀ hrs₀) hbE₀ hfix₀
  have hK₁ : KFAt p E g₁ t₁ :=
    kfAt_of_core_refl hGA h hEA hcL hd₁ hg₁ hm₁ hr₁ ht₁L (hF13.reflection t₁ hrs₁) hbE₁ hfix₁
  intro t ht htL
  obtain ⟨i, hi⟩ := exists_sr_of_reflection S R hinjF hrefl htL ht.1
  have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · left
    exact kfAt_of_parity_G S R hinjF (MulEquiv.refl _) hconj hw₀ hi
      (by rw [ZMod.val_zero]; omega) hK₀
  · right
    exact kfAt_of_parity_G S R hinjF (MulEquiv.refl _) hconj hw₁ hi
      (by rw [hone]; omega) hK₁

end Main

end CFSG.RankThree.PartOne.KF132
