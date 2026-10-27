module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.LocalAnalysis.StandardType.GGSporKCoprime
public import CFSG.Assembly.Subnormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem gk1_isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Assembly.IsQuasisimple A) : CFSG.Assembly.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := h
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

theorem ggSporK_noComponent_of_noPComponent {W : Type} [Group W] [Finite W] (p : ℕ)
    {X : Subgroup W} (h1 : LargeEvenPPrimeCore p ↥X = ⊥)
    (h2 : ∀ C : Subgroup W, ¬ LargeEvenPComponent p X C) :
    ∀ J : Subgroup W, ¬ IsComponentOf J X := by
  intro J hJ
  apply h2 J
  have hker : (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', h1]
  have hinj : Function.Injective (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) :=
    QuotientGroup.mk'_surjective _
  let Φ : ↥X ≃* (↥X ⧸ LargeEvenPPrimeCore p ↥X) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) ⟨hinj, hsurj⟩
  have hΦ : (Φ : ↥X →* (↥X ⧸ LargeEvenPPrimeCore p ↥X)) =
      QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X) := rfl
  refine ⟨hJ.1, hJ.2.1, ?_, ?_⟩
  ·
    have hsub : IsSubnormal (J.subgroupOf X) ⊤ :=
      IsSubnormal.of_mathlib ((IsSubnormal.iff_subgroupOf hJ.1).mp hJ.2.1)
    have hqs : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf X) :=
      gk1_isQuasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hJ.1).symm hJ.2.2
    have hcomp : IsComponentOf (J.subgroupOf X) (⊤ : Subgroup ↥X) := ⟨le_top, hsub, hqs⟩
    have key : IsComponentOf ((J.subgroupOf X).map Φ.toMonoidHom)
        ((⊤ : Subgroup ↥X).map Φ.toMonoidHom) :=
      ⟨Subgroup.map_mono hcomp.1, hcomp.2.1.map Φ.toMonoidHom,
        gk1_isQuasisimple_of_equiv ((J.subgroupOf X).equivMapOfInjective Φ.toMonoidHom Φ.injective)
          hcomp.2.2⟩
    rw [Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective] at key
    exact key
  · intro J' hlt _ heq
    apply (ne_of_lt hlt)
    have himg : (J'.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) =
        (J.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) := heq
    have := Subgroup.map_injective hinj himg
    have hJ'X : J' ≤ X := hlt.le.trans hJ.1
    have h3 := Subgroup.subgroupOf_inj.mp this
    rw [inf_eq_left.mpr hJ'X, inf_eq_left.mpr hJ.1] at h3
    exact h3


theorem ggSporK_step_one {W : Type} [Group W] [Finite W] {p : ℕ} (hCen : BMNoLiePComp p W)
    (hG1 : BMPPrimeCore p W) {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E) {e : W}
    (he : e ∈ E) (he1 : e ≠ 1) :
    Subgroup.centralizer {e} ≤ H ∧
      (∀ C : Subgroup W, ¬ LargeEvenPComponent p (Subgroup.centralizer {e}) C) ∧
      LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({e} : Set W)) = ⊥ ∧
      ∀ J : Subgroup W, ¬ IsComponentOf J (Subgroup.centralizer {e}) := by
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  have hfus : GGControlsStrongFusion H E := hyp.1.2.2.2.2
  have hIV : GGHypRestIVFlat p E := hyp.2.2.2.2.2.2
  have hord : orderOf e = p := orderOf_eq_prime (hyp.1.2.2.1.2 e he) he1
  have hC : Subgroup.centralizer {e} ≤ H := hfus.centralizer_le he he1
  have hnoP : ∀ C : Subgroup W, ¬ LargeEvenPComponent p (Subgroup.centralizer {e}) C :=
    fun C hC' => hCen e hord C hC' (hIV e he he1 C hC')
  have hP' : LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({e} : Set W)) = ⊥ := hG1 e hord hnoP
  exact ⟨hC, hnoP, hP', ggSporK_noComponent_of_noPComponent p hP' hnoP⟩

theorem ggSporK_pPrimeCore_eq_bot {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) : LargeEvenPPrimeCore p ↥H = ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  set N : Subgroup ↥H := LargeEvenPPrimeCore p ↥H with hN
  have hNn : N.Normal := inferInstance
  have hNcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card
  let R : Subgroup W := N.map H.subtype
  have hRcard : Nat.card R = Nat.card N :=
    (Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have hRcop : Nat.Coprime p (Nat.card R) := by rw [hRcard]; exact hNcop
  have hR : ¬ p ∣ Nat.card R := fun hd =>
    (Nat.Prime.one_lt (Fact.out : p.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hRcop hd)
  have hRnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    obtain ⟨n, hn, rfl⟩ := hr
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hNn.conj_mem n hn ⟨h, hh⟩, rfl⟩
  have hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := fun e he r hr => hRnorm e (hEH he) r hr
  have hCe : ∀ e ∈ E, e ≠ 1 → R ⊓ Subgroup.centralizer {e} = ⊥ := by
    intro e he he1
    obtain ⟨hCH, -, hP'C, -⟩ := ggSporK_step_one hCen hG1 hyp he he1
    set C : Subgroup W := Subgroup.centralizer {e} with hCdef
    have hTle : R ⊓ C ≤ C := inf_le_right
    set T' : Subgroup ↥C := (R ⊓ C).subgroupOf C with hT'
    have hT'n : T'.Normal := by
      refine ⟨fun x hx c => ?_⟩
      rw [hT', Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simpa using hRnorm (c : W) (hCH c.2) _ hxR
      · simpa using C.mul_mem (C.mul_mem c.2 hxC) (C.inv_mem c.2)
    have hT'card : Nat.Coprime p (Nat.card T') := by
      have hdvd : Nat.card T' ∣ Nat.card R := by
        rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right hdvd hRcop
    have hbot : T' = ⊥ := (CFSG.pPrimeCore_eq_bot_iff).mp hP'C T' hT'n hT'card
    rw [eq_bot_iff]
    intro x hx
    have hxT : (⟨x, hx.2⟩ : ↥C) ∈ T' := by
      rw [hT', Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot, Subgroup.mem_bot] at hxT
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxT
  have hRbot : R = ⊥ :=
    pPrimeCore_eq_bot_of_centralizers hyp.1.2.2.1 hyp.1.2.2.2.1 hR hER hCe
  exact (Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).mp hRbot

private theorem gk1_isComponentOf_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    {K C : Subgroup G} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map φ.toMonoidHom,
    gk1_isQuasisimple_of_equiv (K.equivMapOfInjective φ.toMonoidHom φ.injective) h.2.2⟩

private theorem gk1_isComponentOf_map_subtype {W : Type*} [Group W] {H : Subgroup W}
    {A : Subgroup ↥H} (h : IsComponentOf A ⊤) : IsComponentOf (A.map H.subtype) H := by
  refine ⟨?_, ?_, gk1_isQuasisimple_of_equiv (A.equivMapOfInjective H.subtype H.subtype_injective)
    h.2.2⟩
  · exact Subgroup.map_subtype_le A
  · have := h.2.1.map H.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this

theorem ggSporK_exists_component {W : Type} [Group W] [Finite W] {H : Subgroup W}
    (h2 : CFSG.pCore 2 ↥H = ⊥) (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ∃ J : Subgroup W, IsComponentOf J H := by
  have hne : {K : Subgroup (GGHypQuot H) | IsComponentOf K ⊤}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hL
    show sSup {K : Subgroup (GGHypQuot H) | IsComponentOf K ⊤} = ⊥
    rw [hemp, sSup_empty]
  obtain ⟨C, hC⟩ := hne
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', h2]
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
    QuotientGroup.mk'_surjective _
  let Φ : ↥H ≃* GGHypQuot H :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨hinj, hsurj⟩
  have key : IsComponentOf (C.map Φ.symm.toMonoidHom) ((⊤ : Subgroup (GGHypQuot H)).map
      Φ.symm.toMonoidHom) := gk1_isComponentOf_map_mulEquiv Φ.symm hC
  rw [Subgroup.map_top_of_surjective Φ.symm.toMonoidHom Φ.symm.surjective] at key
  exact ⟨_, gk1_isComponentOf_map_subtype key⟩

end CFSG.StandardType.SporadicShape
