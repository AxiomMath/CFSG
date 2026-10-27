module

public import CFSG.RankThree.PartTwo.Sec4.Item462Proof
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def K462UAlphaAt (S : Type) [Group S] : Prop :=
  ∀ (D : Subgroup S) (y : S) (V : Subgroup S), CFSG.Assembly.IsElemAbelian 3 D →
    Nat.card D = 9 → y ∈ D → y ≠ 1 → IsPGroup 2 V → Nat.card V = 4 →
    V ≤ Subgroup.centralizer ({y} : Set S) →
    (∀ s ∈ Subgroup.centralizer ({y} : Set S), s ∈ Subgroup.normalizer (V : Set S)) →
    D ≤ Subgroup.normalizer (V : Set S) →
    ∀ R : Subgroup (MulAut S), IsPGroup 2 R →
      R ≤ Subgroup.centralizer
        ((V.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) →
      (∀ n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S),
        MulAut.conj n ∈ Subgroup.normalizer (R : Set (MulAut S))) →
      R ≤ V.map (MulAut.conj : S →* MulAut S)

@[expose] def K462J2 : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* Blueprint.NativeSporadic.J2) → K462UAlphaAt S

@[expose] def K462M12 : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* Blueprint.NativeSporadic.M12) → K462UAlphaAt S

@[expose] def K462L27 : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* projSL 2 (GaloisField 3 3)) →
    ∀ V : Subgroup S, Nat.card V = 4 → ∀ τ : MulAut S, (∃ k : ℕ, τ ^ 2 ^ k = 1) →
      (∀ v ∈ V, τ v = v) → τ ∈ V.map (MulAut.conj : S →* MulAut S)

namespace Step462UAlphaProof

section General

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have key : ∀ g' ∈ Subgroup.normalizer (H : Set G), ∀ z' ∈ Subgroup.centralizer (H : Set G),
      g' * z' * g'⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro g' hg' z' hz'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : g'⁻¹ * h * g'⁻¹⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hg') h).mp hh
    have hc := Subgroup.mem_centralizer_iff.mp hz' _ hh'
    calc h * (g' * z' * g'⁻¹) = g' * ((g'⁻¹ * h * g'⁻¹⁻¹) * z') * g'⁻¹ := by group
      _ = g' * (z' * (g'⁻¹ * h * g'⁻¹⁻¹)) * g'⁻¹ := by rw [hc]
      _ = g' * z' * g'⁻¹ * h := by group
  refine ⟨fun hz => key g hg z hz, fun hz => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hz
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this

theorem mem_normalizer_inSubgroup_pCore {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hg' : H.map (MulAut.conj g).toMonoidHom = H := hg
  have key : (inSubgroup (CFSG.pCore 2) H).map (MulAut.conj g).toMonoidHom =
      inSubgroup (CFSG.pCore 2) (H.map (MulAut.conj g).toMonoidHom) := by
    rw [inSubgroup, inSubgroup, ← CFSG.pCore_map_iso 2
      (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective),
      Subgroup.map_map, Subgroup.map_map]
    rfl
  change (inSubgroup (CFSG.pCore 2) H).map (MulAut.conj g).toMonoidHom = _
  rw [key, hg']

theorem mem_normalizer_centralizer_singleton {y g : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  have h := mem_normalizer_centralizer hg
  have he : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [he] at h

theorem mem_normalizer_subgroupOf {H K : Subgroup G} {g : K}
    (hg : (g : G) ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((H.subgroupOf K : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hg h

theorem card_map_of_injOn {H K : Type*} [Group H] [Group K] (f : H →* K) (P : Subgroup H)
    (hinj : Set.InjOn f (P : Set H)) : Nat.card (P.map f) = Nat.card P := by
  have h1 : Nat.card (f '' (P : Set H)) = Nat.card (P : Set H) := Nat.card_image_of_injOn hinj
  have e1 : Nat.card (P.map f) = Nat.card (f '' (P : Set H)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e1, h1]
  rfl

theorem inf_eq_bot_of_kleinFour [Finite G] {U T A : Subgroup G} (hU : IsKleinFour U)
    (hUA : ⁅U, A⁆ = U) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hUT : ¬ U ≤ T) : U ⊓ T = ⊥ := by
  by_contra hne
  apply hUT
  set K : Subgroup U := T.subgroupOf U with hK
  have hU4 : Nat.card U = 4 := @IsKleinFour.card_four _ _ hU
  have hK1 : K ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxK : (⟨x, hx.1⟩ : U) ∈ K := Subgroup.mem_subgroupOf.mpr hx.2
    rw [h, Subgroup.mem_bot] at hxK
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxK
  have hKtop : K ≠ ⊤ := by
    intro h
    apply hUT
    intro x hx
    have hxK : (⟨x, hx⟩ : U) ∈ K := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxK
  have hKc : Nat.card K = 2 := by
    have hdvd : Nat.card K ∣ 4 := hU4 ▸ Subgroup.card_subgroup_dvd_card K
    have h1 : Nat.card K ≠ 1 := fun h => hK1 (Subgroup.card_eq_one.mp h)
    have h4 : Nat.card K ≠ 4 := fun h =>
      hKtop (Subgroup.card_eq_iff_eq_top K |>.mp (h.trans hU4.symm))
    have hle : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card K <;> simp_all
  have hKi : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    rw [hKc, hU4] at h
    omega
  rw [← hUA, Subgroup.commutator_le]
  intro u hu x hx
  have hw : x * u⁻¹ * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAU hx) _).mp (inv_mem hu)
  have hiff : (⟨u, hu⟩ : U) * ⟨x * u⁻¹ * x⁻¹, hw⟩ ∈ K ↔
      ((⟨u, hu⟩ : U) ∈ K ↔ (⟨x * u⁻¹ * x⁻¹, hw⟩ : U) ∈ K) :=
    Subgroup.mul_mem_iff_of_index_two hKi
  have hT : (⟨u, hu⟩ : U) ∈ K ↔ (⟨x * u⁻¹ * x⁻¹, hw⟩ : U) ∈ K := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change u ∈ T ↔ x * u⁻¹ * x⁻¹ ∈ T
    rw [← Subgroup.mem_normalizer_iff.mp (hAT hx) u⁻¹, inv_mem_iff]
  have hmem := hiff.mpr hT
  rw [Subgroup.mem_subgroupOf] at hmem
  rw [commutatorElement_def]
  have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
  rw [e]
  exact hmem

end General

section Action

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_eq {L U : Subgroup G} {x u : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (huU : u ∈ U)
    (h : thetaQuotMulAut L (compAction L ⟨x, hx⟩) = thetaQuotMulAut L (compAction L ⟨u, hu⟩)) :
    x ∈ U ⊔ thetaQuotCentralizer L := by
  have hk : u⁻¹ * x ∈ thetaQuotCentralizer L := by
    refine ⟨⟨u⁻¹ * x, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have he : (⟨u⁻¹ * x, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx⟩ :
        Subgroup.normalizer (L : Set G)) = (⟨u, hu⟩)⁻¹ * ⟨x, hx⟩ := rfl
    rw [he, map_mul, map_inv, map_mul, map_inv]
    change (thetaQuotMulAut L (compAction L ⟨u, hu⟩))⁻¹ *
      thetaQuotMulAut L (compAction L ⟨x, hx⟩) = 1
    rw [h, inv_mul_cancel]
  have e : x = u * (u⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huU) (Subgroup.mem_sup_right hk)

theorem thetaAct_mem_normalizer {L X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    thetaQuotMulAut L (compAction L ⟨g, hg⟩) ∈
      Subgroup.normalizer (((X.subgroupOf (Subgroup.normalizer (L : Set G))).map
        ((thetaQuotMulAut L).comp (compAction L)) : Subgroup _) : Set _) :=
  Subgroup.le_normalizer_map _ ⟨⟨g, hg⟩, mem_normalizer_subgroupOf hgX, rfl⟩

omit [Finite G] in
theorem not_le_theta {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) :
    ¬ L ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  intro h
  obtain ⟨-, -, ⟨x, y, hxy⟩⟩ := hL.2.2
  apply hxy
  have h1 : ∀ q : L ⧸ aschbacherSolvableCore 3 L, q = 1 := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨l', hl', hl'e⟩ := h l.2
    have : l' = l := Subtype.ext hl'e
    rw [← this]
    exact hl'
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [h1 x', h1 y']

theorem eq_one_of_mem_of_mem_thetaQuotCentralizer {L : Subgroup G}
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ thetaQuotCentralizer L) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨n, hn, hne⟩ := hxC
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hn
  have hn' : n = ⟨x, Subgroup.le_normalizer hxL⟩ := Subtype.ext hne
  rw [hn'] at hn
  change thetaQuotMulAut L (compAction L ⟨x, Subgroup.le_normalizer hxL⟩) = 1 at hn
  rw [KFacts.thetaQuotMulAut_compAction_of_mem hxL] at hn
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun σ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => σ g) hn
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩
        = (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ * g *
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩)⁻¹) *
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ := by rw [h]
      _ = QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ * g := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hx3' : (⟨x, hxL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have h1 := Item424Proof.eq_one_of_pow_three_of_not_dvd
    (KFacts.not_three_dvd_card_aschbacherSolvableCore L) hcen hx3'
  exact congrArg Subtype.val h1

theorem eq_one_of_mk_eq_one {L : Subgroup G} {x : L}
    (hx : QuotientGroup.mk' (aschbacherSolvableCore 3 L) x = 1) (hx3 : x ^ 3 = 1) : x = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact Item424Proof.eq_one_of_pow_three_of_not_dvd
    (KFacts.not_three_dvd_card_aschbacherSolvableCore L) hx hx3

end Action

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_U {A B U : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) (hUO : U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G))) :
    A ≤ Subgroup.normalizer (U : Set G) := by
  intro x hx
  rw [hUO]
  apply Item462Proof.le_normalizer_inSubgroup_pCore
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hBA hy⟩ ⟨x, hx⟩)

omit [Finite G] in
theorem mem_normalizer_X {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer
      ((inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) : Subgroup G) : Set G) :=
  mem_normalizer_inSubgroup_pCore (mem_normalizer_centralizer hg)

theorem card_map_U {A U L : Subgroup G} (hU : IsKleinFour U) (hUA : ⁅U, A⁆ = U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ L) (hLU : ⁅L, U⁆ = L) :
    Nat.card ((U.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) = 4 := by
  have hθN : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hAL.trans (Sec6.normalizer_le_normalizer_theta L)
  have hUθ : ¬ U ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    intro h
    apply not_le_theta hL
    have h1 : U ≤ thetaQuotCentralizer L := h.trans (Sec6.theta_le_thetaQuotCentralizer L)
    have h2 := (Sec6.commutator_le_theta_iff (hUL.trans Subgroup.le_normalizer)).mpr h1
    rwa [hLU] at h2
  have hUinf := inf_eq_bot_of_kleinFour hU hUA hAU hθN hUθ
  have hinj : Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
      ((U.subgroupOf L : Subgroup L) : Set L) := by
    intro u hu v hv huv
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huv
    have h2 : ((u⁻¹ * v : L) : G) ∈ U ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨U.mul_mem (U.inv_mem (Subgroup.mem_subgroupOf.mp hu)) (Subgroup.mem_subgroupOf.mp hv),
        ⟨u⁻¹ * v, huv, rfl⟩⟩
    rw [hUinf, Subgroup.mem_bot] at h2
    have h3 : u⁻¹ * v = 1 := Subtype.ext h2
    exact (inv_mul_eq_one.mp h3)
  rw [card_map_of_injOn _ _ hinj, ← @IsKleinFour.card_four _ _ hU]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv

theorem isPGroup_map_X {L X : Subgroup G} (hX : IsPGroup 2 X) :
    IsPGroup 2 ((X.subgroupOf (Subgroup.normalizer (L : Set G))).map
      ((thetaQuotMulAut L).comp (compAction L))) :=
  (hX.comap_subtype).map _

theorem map_X_le_centralizer {L U X : Subgroup G}
    (hXU : X ≤ Subgroup.centralizer (U : Set G)) :
    (X.subgroupOf (Subgroup.normalizer (L : Set G))).map ((thetaQuotMulAut L).comp (compAction L))
      ≤ Subgroup.centralizer ((((U.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map
          (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _) : Subgroup _) : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
  have hxU : (x : G) ∈ Subgroup.centralizer (U : Set G) := hXU (Subgroup.mem_subgroupOf.mp hx)
  have hcomm : (u : G) * x = x * u := Subgroup.mem_centralizer_iff.mp hxU _ huU
  have hu' : (u : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer u.2
  have e1 : MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) u) =
      ((thetaQuotMulAut L).comp (compAction L)) ⟨u, hu'⟩ := by
    rw [MonoidHom.comp_apply, KFacts.thetaQuotMulAut_compAction_of_mem u.2 hu']
  rw [e1, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

theorem le_sup_of_map_le {L U X : Subgroup G}
    (hLG : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G))
    (h : (X.subgroupOf (Subgroup.normalizer (L : Set G))).map
        ((thetaQuotMulAut L).comp (compAction L)) ≤ ((U.subgroupOf L).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map
            (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _)) :
    X ≤ U ⊔ thetaQuotCentralizer L := by
  intro x hx
  have hxR : ((thetaQuotMulAut L).comp (compAction L)) ⟨x, hLG x⟩ ∈
      (X.subgroupOf (Subgroup.normalizer (L : Set G))).map
        ((thetaQuotMulAut L).comp (compAction L)) :=
    ⟨⟨x, hLG x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := h hxR
  have hu' : (u : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer u.2
  refine mem_sup_of_eq (hLG x) hu' (Subgroup.mem_subgroupOf.mp hu) ?_
  rw [MonoidHom.comp_apply] at hue
  rw [← hue, KFacts.thetaQuotMulAut_compAction_of_mem u.2 hu']

theorem le_sup_of_inner {A B U L : Subgroup G} {a : G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    (haB : a ∈ B) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hU : IsKleinFour U) (hUA : ⁅U, A⁆ = U)
    (hUO : U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G)))
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ L)
    (hLU : ⁅L, U⁆ = L) (hLG : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hK : K462UAlphaAt (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinner : ∀ x ∈ A, ¬ InducesOuterTheta x L) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ≤
      U ⊔ thetaQuotCentralizer L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  have hALa : ∀ x ∈ A, x ∈ L ⊔ Subgroup.zpowers a := fun x hx =>
    Item462Proof.mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA hZ hx (hinner x hx)
  set X := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hXdef
  obtain ⟨b, hbB, hba, hCB⟩ := Item462Proof.exists_centralizer_eq hB9
    (fun x hx => hAe.2 x (hBA hx)) haB haZ ha3
  obtain ⟨y, hyL, w, hw, hyw⟩ := Subgroup.mem_sup_of_normal_right.mp (hALa b (hBA hbB))
  have hwB : w ∈ B := Subgroup.zpowers_le.mpr haB hw
  have hyB : y ∈ B := by
    have e : y = b * w⁻¹ := by rw [← hyw]; group
    rw [e]
    exact B.mul_mem hbB (B.inv_mem hwB)
  have hyA : y ∈ A := hBA hyB
  have hy3 : y ^ 3 = 1 := hAe.2 y hyA
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hba
    rw [← hyw, one_mul]
    exact hw
  have hwZ : w ∈ Subgroup.center G := Subgroup.zpowers_le.mpr haZ hw
  have hCy : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({y} : Set G) := by
    rw [hCB]
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hyw]
    have hwg : w * g = g * w := (Subgroup.mem_center_iff.mp hwZ g).symm
    constructor
    · intro h
      have h' : g * y * w = y * g * w := by
        calc g * y * w = g * (y * w) := by group
          _ = y * w * g := h
          _ = y * (w * g) := by group
          _ = y * (g * w) := by rw [hwg]
          _ = y * g * w := by group
      exact mul_right_cancel h'
    · intro h
      calc g * (y * w) = g * y * w := by group
        _ = y * g * w := by rw [h]
        _ = y * (g * w) := by group
        _ = y * (w * g) := by rw [hwg]
        _ = y * w * g := by group
  have hUO' : U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set G)) := by
    rw [hUO, hCy]
  have hNyX : ∀ g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (X : Set G) := fun g hg => by
    apply mem_normalizer_X
    rw [hUO']
    exact mem_normalizer_inSubgroup_pCore (mem_normalizer_centralizer_singleton hg)
  have hAU := le_normalizer_U hAe hBA hUO
  have hAX : ∀ x ∈ A, x ∈ Subgroup.normalizer (X : Set G) := fun x hx => mem_normalizer_X (hAU hx)
  have haL : a ∉ L := fun haL => ha1 (eq_one_of_mem_of_mem_thetaQuotCentralizer hZ haL
    ((hCA a haA).mpr (Subgroup.mem_zpowers a)) (hAe.2 a haA))
  have hAsup : (A ⊓ L) ⊔ Subgroup.zpowers a = A := by
    apply le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr haA))
    intro x hx
    obtain ⟨l, hl, w', hw', hlw⟩ := Subgroup.mem_sup_of_normal_right.mp (hALa x hx)
    have hlA : l ∈ A := by
      have e : l = x * w'⁻¹ := by rw [← hlw]; group
      rw [e]
      exact A.mul_mem hx (A.inv_mem (Subgroup.zpowers_le.mpr haA hw'))
    rw [← hlw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlA, hl⟩) (Subgroup.mem_sup_right hw')
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    have h := Item462Proof.card_sup_zpowers_of_not_mem haZ ha3 (B := A ⊓ L) (fun h => haL h.2)
    rw [hAsup, h27] at h
    omega
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set V := (U.subgroupOf L).map π with hV
  set D := Sec8.imageModTheta L (A ⊓ L) with hD
  set R := (X.subgroupOf (Subgroup.normalizer (L : Set G))).map
    ((thetaQuotMulAut L).comp (compAction L)) with hR
  have hALp : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_subgroupOf.mp x.2).1))⟩
  have hALe : CFSG.Assembly.IsElemAbelian 3 ((A ⊓ L).subgroupOf L) := by
    refine ⟨⟨⟨fun x z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun z hz => ?_⟩
    · show ((x : L) : G) * ((z : L) : G) = ((z : L) : G) * ((x : L) : G)
      exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨_, (Subgroup.mem_subgroupOf.mp x.2).1⟩
        ⟨_, (Subgroup.mem_subgroupOf.mp z.2).1⟩)
    · exact Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_subgroupOf.mp hz).1)
  have hDe : CFSG.Assembly.IsElemAbelian 3 D := Item462Proof.isElemAbelian_map' π hALe
  have hD9 : Nat.card D = 9 := by
    rw [hD, Sec8.imageModTheta, Item424Proof.card_map_mk_of_isPGroup hALp, ← hAL9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hyD : π ⟨y, hyL⟩ ∈ D := ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr ⟨hyA, hyL⟩, rfl⟩
  have hy1' : π ⟨y, hyL⟩ ≠ 1 := fun h =>
    hy1 (congrArg Subtype.val (eq_one_of_mk_eq_one h (Subtype.ext (by simpa using hy3))))
  have hU2 : IsPGroup 2 U :=
    IsPGroup.of_card (n := 2) (by rw [@IsKleinFour.card_four _ _ hU]; norm_num)
  have hV2 : IsPGroup 2 V := hU2.comap_subtype.map π
  have hV4 : Nat.card V = 4 := card_map_U hU hUA hAU hL hAL hUL hLU
  have hUB : U ≤ Subgroup.centralizer (B : Set G) := by
    rw [hUO]
    exact Subgroup.map_subtype_le _
  have hVC : V ≤ Subgroup.centralizer ({π ⟨y, hyL⟩} : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hUB (Subgroup.mem_subgroupOf.mp hu)) y hyB).symm
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hLG y
  have hbarC := KFacts.imageModTheta_centralizer_eq (L := L) hyN ⟨1, by simpa using hy3⟩
  have hCV : ∀ s ∈ Subgroup.centralizer ({π ⟨y, hyL⟩} : Set (L ⧸ aschbacherSolvableCore 3 L)),
      s ∈ Subgroup.normalizer (V : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro s hs
    have hs' : s ∈ Sec8.barCentralizer (Subgroup.zpowers y) L := by
      rw [KFacts.mem_barCentralizer_zpowers_iff hyN,
        KFacts.thetaQuotMulAut_compAction_of_mem hyL hyN, MulAut.conj_apply]
      rw [Subgroup.mem_centralizer_singleton_iff] at hs
      rw [← hs]
      exact mul_inv_cancel_right _ _
    rw [← hbarC] at hs'
    obtain ⟨ℓ, hℓ, rfl⟩ := hs'
    have hℓC : (ℓ : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [hCy]
      exact (Subgroup.mem_subgroupOf.mp hℓ).2
    have hℓU : (ℓ : G) ∈ Subgroup.normalizer (U : Set G) := by
      rw [hUO]
      exact Item462Proof.le_normalizer_inSubgroup_pCore _ hℓC
    exact Subgroup.le_normalizer_map π ⟨ℓ, mem_normalizer_subgroupOf hℓU, rfl⟩
  have hDV : D ≤ Subgroup.normalizer (V : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have hℓU : (ℓ : G) ∈ Subgroup.normalizer (U : Set G) :=
      hAU (Subgroup.mem_subgroupOf.mp hℓ).1
    exact Subgroup.le_normalizer_map π ⟨ℓ, mem_normalizer_subgroupOf hℓU, rfl⟩
  have hX2 : IsPGroup 2 X := CFSG.pCore_isPGroup.map _
  have hR2 : IsPGroup 2 R := isPGroup_map_X hX2
  have hXU : X ≤ Subgroup.centralizer (U : Set G) := Subgroup.map_subtype_le _
  have hRC := map_X_le_centralizer (L := L) hXU
  have hyo : orderOf (⟨y, hyL⟩ : L) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hy3 hy1
  have hRN : ∀ n ∈ Subgroup.normalizer
      ((Subgroup.zpowers (π ⟨y, hyL⟩) : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
        Set (L ⧸ aschbacherSolvableCore 3 L)),
      MulAut.conj n ∈ Subgroup.normalizer (R : Set (MulAut (L ⧸ aschbacherSolvableCore 3 L))) := by
    intro n hn
    obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective n
    have hP3 : IsPGroup 3 (Subgroup.zpowers (⟨y, hyL⟩ : L)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
    have hPmap : (Subgroup.zpowers (⟨y, hyL⟩ : L)).map π = Subgroup.zpowers (π ⟨y, hyL⟩) :=
      MonoidHom.map_zpowers _ _
    have hn' : (n₀ : L ⧸ aschbacherSolvableCore 3 L) ∈ Subgroup.normalizer
        (((Subgroup.zpowers (⟨y, hyL⟩ : L)).map π : Subgroup _) : Set _) := by
      rw [hPmap]
      exact hn
    obtain ⟨w₀, hwP, e, he, hne⟩ := Item424Proof.exists_normalizer_lift hP3 hn'
    rw [hne, map_mul]
    refine Subgroup.mul_mem _ ?_ ?_
    · obtain ⟨e₀, he₀, rfl⟩ := he
      have he₀A : (e₀ : G) ∈ A := by
        have h1 : (e₀ : G) ∈ (Subgroup.zpowers (⟨y, hyL⟩ : L)).map L.subtype :=
          ⟨e₀, he₀, rfl⟩
        rw [MonoidHom.map_zpowers] at h1
        exact Subgroup.zpowers_le.mpr hyA h1
      have h1 := thetaAct_mem_normalizer (hLG e₀) (hAX _ he₀A)
      rw [KFacts.thetaQuotMulAut_compAction_of_mem e₀.2 (hLG e₀)] at h1
      exact h1
    · have hwN : (w₀ : G) ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
        have h1 := Subgroup.le_normalizer_map L.subtype ⟨w₀, hwP, rfl⟩
        rwa [MonoidHom.map_zpowers] at h1
      have h1 := thetaAct_mem_normalizer (hLG w₀) (hNyX _ hwN)
      rw [KFacts.thetaQuotMulAut_compAction_of_mem w₀.2 (hLG w₀)] at h1
      exact h1
  exact le_sup_of_map_le hLG
    (hK D (π ⟨y, hyL⟩) V hDe hD9 hyD hy1' hV2 hV4 hVC hCV hDV R hR2 hRC hRN)

theorem le_sup_of_l27 {A U L : Subgroup G} (hU : IsKleinFour U) (hUA : ⁅U, A⁆ = U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ L) (hLU : ⁅L, U⁆ = L)
    (hLG : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G))
    (hK : ∀ V : Subgroup (L ⧸ aschbacherSolvableCore 3 L), Nat.card V = 4 →
      ∀ τ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, τ ^ 2 ^ k = 1) →
        (∀ v ∈ V, τ v = v) → τ ∈ V.map (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _)) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ≤
      U ⊔ thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G))) :=
    CFSG.pCore_isPGroup.map _
  have hXU : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ≤
      Subgroup.centralizer (U : Set G) := Subgroup.map_subtype_le _
  apply le_sup_of_map_le hLG
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  have hxX := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨k, hk⟩ := hX2 ⟨x, hxX⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine hK _ (card_map_U hU hUA hAU hL hAL hUL hLU) _ ⟨k, ?_⟩ ?_
  · rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hxk)
    rw [h1, map_one]
  · rintro _ ⟨u, hu, rfl⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change (L.normalizerMonoidHom ⟨x, hxN⟩ u : G) = u
    rw [normalizerMonoidHom_apply_coe]
    have hc : (u : G) * x = x * u :=
      Subgroup.mem_centralizer_iff.mp (hXU hxX) _ (Subgroup.mem_subgroupOf.mp hu)
    rw [← hc, mul_inv_cancel_right]

end Config

end Step462UAlphaProof

theorem step462UAlpha_of
    (hJ : K462J2) (hM : K462M12) (hL27 : K462L27) : Step462UAlpha := by
  intro G _ _ _ A hmax h27 a haA haZ ha1 B haB hBA hB9 U hU hUA hUO _ _ _ _ _ _
    L hL hAL hUL hLU hLG hCA hlist
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAU := Step462UAlphaProof.le_normalizer_U hAe hBA hUO
  rcases hlist with (he | he) | ⟨he, -⟩
  · obtain ⟨e⟩ := he
    exact Step462UAlphaProof.le_sup_of_inner hmax h27 haA haZ ha1 haB hBA hB9 hU hUA hUO hL hAL
      hUL hLU hLG hCA (hJ _ ⟨e⟩) (Item462Proof.center_eq_bot_of_j2 e)
      (fun x hx => Item462Proof.not_inducesOuterTheta_of_j2 e (hAe.2 x hx))
  · obtain ⟨e⟩ := he
    obtain ⟨hZ, hinn⟩ := Item462Proof.not_inducesOuterTheta_of_m12 (G := G) e
    exact Step462UAlphaProof.le_sup_of_inner hmax h27 haA haZ ha1 haB hBA hB9 hU hUA hUO hL hAL
      hUL hLU hLG hCA (hM _ ⟨e⟩) hZ (fun x hx => hinn x (hAe.2 x hx))
  · obtain ⟨e⟩ := he
    exact Step462UAlphaProof.le_sup_of_l27 hU hUA hAU hL hAL hUL hLU hLG (hL27 _ ⟨e⟩)

end CFSG.RankThree.PartTwo.Sec4
