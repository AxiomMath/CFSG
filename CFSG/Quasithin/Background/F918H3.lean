module

public import CFSG.Quasithin.Background.F918Q2
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.LieType.BorelTits

section Restrict

variable {W : Type} [CommGroup W]

theorem le_stabSub_of_forall_mem {X : Subgroup (MulAut W)} {Y : Subgroup W}
    (h : ∀ x ∈ X, ∀ w ∈ Y, x w ∈ Y) : X ≤ stabSub Y :=
  CFSG.Quasithin.le_stabSub_of_forall_memQ2 h

theorem mem_stabSub_commSub {X : Subgroup (MulAut W)} {Y : Subgroup W} {g : MulAut W}
    (hgY : g ∈ stabSub Y) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    g ∈ stabSub (commSub Y X) :=
  CFSG.Quasithin.StabLat.mem_stabSub_commSub hgY hgX

theorem exists_mem_of_mem_sup_of_le_centSub {X Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) (hY : Y ≤ centSub U) :
    ∀ a ∈ X ⊔ Y, ∃ l ∈ X, ∀ u ∈ U, a u = l u := by
  intro a ha
  have : a ∈ ((X ⊔ Y : Subgroup (MulAut W)) : Set (MulAut W)) := ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X Y hYX] at this
  obtain ⟨l, hl, y, hy, rfl⟩ := this
  exact ⟨l, hl, fun u hu => by simp [MulAut.mul_apply, hY hy u hu]⟩

@[expose] noncomputable def resHomOn (U : Subgroup W) {H : Subgroup (MulAut W)} (hH : H ≤ stabSub U) :
    ↥H →* MulAut ↥U :=
  (resHom U).comp (Subgroup.inclusion hH)

theorem autSub_eq_map_resHomOn {K H : Subgroup (MulAut W)} {U : Subgroup W} (hKH : K ≤ H)
    (hH : H ≤ stabSub U) : autSub K U = (K.subgroupOf H).map (resHomOn U hH) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact ⟨⟨(g : MulAut W), hKH hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact mem_autSub.mpr ⟨⟨(g : MulAut W), hH g.2⟩, Subgroup.mem_subgroupOf.mp hg, rfl⟩

theorem autSub_eq_range_resHomOn {H : Subgroup (MulAut W)} {U : Subgroup W} (hH : H ≤ stabSub U) :
    autSub H U = (resHomOn U hH).range := by
  rw [autSub_eq_map_resHomOn le_rfl hH, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem actCompat_autSub {X₁ X₂ : Subgroup (MulAut W)} {U : Subgroup W} (hX₂ : X₂ ≤ stabSub U)
    (h₁ : X₁ ≤ X₂) (h : ∀ a ∈ X₂, ∃ l ∈ X₁, ∀ u ∈ U, a u = l u) :
    ActCompat U.subtype (autSub X₁ U) X₂ := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hb
    exact ⟨(g : MulAut W), h₁ hg, fun p => rfl⟩
  · intro a ha
    obtain ⟨l, hl, hal⟩ := h a ha
    have hl' : l ∈ stabSub U := hX₂ (h₁ hl)
    refine ⟨resHom U ⟨l, hl'⟩, mem_autSub.mpr ⟨⟨l, hl'⟩, hl, rfl⟩, fun p => ?_⟩
    exact (hal p p.2).symm

end Restrict

section SylowCount

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_of_le_normalizer_aux {B A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hA).toEquiv.symm

theorem isSylowTwoOf_sup_of_inf_le {Mp T S : Subgroup G} (hST : S ≤ T)
    (hTn : T ≤ Subgroup.normalizer (Mp : Set G)) (hinf : Mp ⊓ T ≤ S)
    (hT : IsSylowTwoOf T (Mp ⊔ T)) : IsSylowTwoOf S (Mp ⊔ S) := by
  have hSn : S ≤ Subgroup.normalizer (Mp : Set G) := hST.trans hTn
  have hSA : S ≤ Mp ⊔ S := le_sup_right
  have hAB : Mp ⊔ S ≤ Mp ⊔ T := sup_le_sup_left hST Mp
  have hTB : T ≤ Mp ⊔ T := le_sup_right
  have hMS : Mp ⊓ S = Mp ⊓ T := le_antisymm (inf_le_inf_left Mp hST) (le_inf inf_le_left hinf)
  have h1 : S.relIndex (Mp ⊔ S) * (Mp ⊔ S).relIndex (Mp ⊔ T) =
      S.relIndex T * T.relIndex (Mp ⊔ T) := by
    rw [Subgroup.relIndex_mul_relIndex S (Mp ⊔ S) (Mp ⊔ T) hSA hAB,
      Subgroup.relIndex_mul_relIndex S T (Mp ⊔ T) hST hTB]
  have hne : Mp.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hc : S.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have e1 : Mp.relIndex (Mp ⊔ S) = Mp.relIndex S := by
    rw [sup_comm]; exact relIndex_sup_of_le_normalizer_aux hSn
  have e2 : Mp.relIndex (Mp ⊔ T) = Mp.relIndex T := by
    rw [sup_comm]; exact relIndex_sup_of_le_normalizer_aux hTn
  have e3 : Mp.relIndex T = Mp.relIndex S * S.relIndex T := by
    have h := Subgroup.relIndex_mul_relIndex (Mp ⊓ T) S T hinf hST
    have hA : (Mp ⊓ T).relIndex S = Mp.relIndex S := by
      rw [← hMS]; exact Subgroup.inf_relIndex_right Mp S
    have hB : (Mp ⊓ T).relIndex T = Mp.relIndex T := Subgroup.inf_relIndex_right Mp T
    rw [hA, hB] at h
    exact h.symm
  have h2 : Mp.relIndex S * (Mp ⊔ S).relIndex (Mp ⊔ T) = Mp.relIndex S * S.relIndex T := by
    have := Subgroup.relIndex_mul_relIndex Mp (Mp ⊔ S) (Mp ⊔ T) le_sup_left hAB
    rw [e1, e2, e3] at this
    exact this
  have hb : (Mp ⊔ S).relIndex (Mp ⊔ T) = S.relIndex T :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h2
  rw [hb] at h1
  have ha : S.relIndex (Mp ⊔ S) = T.relIndex (Mp ⊔ T) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) (by rw [h1, mul_comm])
  refine ⟨hSA, hT.2.1.to_le hST, ?_⟩
  show ¬ 2 ∣ S.relIndex (Mp ⊔ S)
  rw [ha]
  exact hT.2.2

end SylowCount

section SQTKStable

theorem isQuotientOfSQTK_of_le_aux {G : Type*} [Group G] {M N : Subgroup G} (hNM : N ≤ M)
    (hM : IsQuotientOfSQTKTC ↥M) : IsQuotientOfSQTKTC ↥N := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hM
  let N' : Subgroup ↥M := N.subgroupOf M
  refine ⟨↥(N'.comap φ), inferInstance, inferInstance, ?_, hK.subgroup _, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (N'.comap φ).subtype
      (N'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom.comp (φ.subgroupComap N'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hNM).surjective.comp
      (MonoidHom.subgroupComap_surjective φ N' hφ)

theorem isQuotientOfSQTK_range_aux {N : Type*} [Group N] {Γ : Type*} [Group Γ] (ρ : N →* Γ)
    (hN : IsQuotientOfSQTKTC N) : IsQuotientOfSQTKTC ↥ρ.range := by
  obtain ⟨S, _, _, h1, h2, φ, hφ⟩ := hN
  exact ⟨S, inferInstance, inferInstance, h1, h2, ρ.rangeRestrict.comp φ,
    ρ.rangeRestrict_surjective.comp hφ⟩

theorem isQuotientOfSQTK_autSub_aux {W : Type} [CommGroup W] {X M : Subgroup (MulAut W)}
    {U : Subgroup W} (hXM : X ≤ M) (hM : IsQuotientOfSQTKTC ↥M) :
    IsQuotientOfSQTKTC ↥(autSub X U) := by
  have hN : IsQuotientOfSQTKTC ↥(X ⊓ stabSub U) :=
    isQuotientOfSQTK_of_le_aux (inf_le_left.trans hXM) hM
  have h := isQuotientOfSQTK_range_aux ((resHom U).comp (Subgroup.inclusion
    (inf_le_right : X ⊓ stabSub U ≤ stabSub U))) hN
  have e : autSub X U = ((resHom U).comp (Subgroup.inclusion
      (inf_le_right : X ⊓ stabSub U ≤ stabSub U))).range := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      exact ⟨⟨(g : MulAut W), hg, g.2⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact mem_autSub.mpr ⟨⟨(g : MulAut W), g.2.2⟩, g.2.1, rfl⟩
  rw [e]
  exact h

end SQTKStable

section D36Facts

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
private theorem d36r_conj_conj (s t : MulAut W) (L : Subgroup (MulAut W)) :
    conjAutSub s (conjAutSub t L) = conjAutSub (s * t) L := by
  unfold conjAutSub
  rw [Subgroup.map_map]
  congr 1

private theorem d36r_l38 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    A38Types ↥L ∧ (∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x) ∧
      ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L := by
  obtain ⟨h1, h2, -, h4⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  refine ⟨h1, fun x hx y hy => ?_, h4⟩
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2 hx
  exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

private theorem d36r_TM (n : D36Norm M Mp T L V t) : T ≤ M := n.std.hyp.sylow.1

private theorem d36r_LM (n : D36Norm M Mp T L V t) : L ≤ M := le_of_mem_cComp n.std.hyp.comp

private theorem d36r_L_le_Mp (n : D36Norm M Mp T L V t) : L ≤ Mp := by
  rw [n.Mp_eq]; exact le_sup_left

private theorem d36r_Mp_le_M (n : D36Norm M Mp T L V t) : Mp ≤ M := by
  rw [n.std.hyp.Mp_eq]
  exact conjClosure_le fun s hs z hz =>
    M.mul_mem (M.mul_mem (d36r_TM n hs) (d36r_LM n hz)) (M.inv_mem (d36r_TM n hs))

private theorem d36r_T_le_normalizer (n : D36Norm M Mp T L V t) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [n.std.hyp.Mp_eq]; exact le_normalizer_conjClosure L T

private theorem d36r_Lt_le_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun y hy =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
    (d36r_l38 hL38 n).2.1 h hh y hy)

private theorem d36r_Mp_le_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [n.Mp_eq]
  exact sup_le Subgroup.le_normalizer (d36r_Lt_le_normalizer hL38 n)

private theorem d36r_stab_V (n : D36Norm M Mp T L V t) : Mp ≤ stabSub V := by
  have hinv := n.std.hyp.irr.2.1
  exact le_stabSub_of_forall_mem fun x hx w hw => hinv ⟨x, hx⟩ w hw

private theorem d36r_stab_orbSup (n : D36Norm M Mp T L V t) : Mp ≤ stabSub (orbSup T V) := by
  refine le_stabSub_of_forall_mem fun x hx w hw => ?_
  have key : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    show x (s v) ∈ orbSup T V
    have hx' : s⁻¹ * x * s ∈ Mp :=
      (Subgroup.mem_normalizer_iff''.mp (d36r_T_le_normalizer n hs) x).mp hx
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    rw [h1]
    exact map_le_orbSup hs ⟨_, (d36r_stab_V n hx' v).2 hv, rfl⟩
  exact key hw

private theorem d36r_nontriv (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  have h1 := n.std.hyp.irr.2.2.2.1
  have hfix : V ≤ XMod.fixed ↥Mp V := by
    intro v hv
    refine ⟨hv, fun a => ?_⟩
    have ha : (a : MulAut W) ∈ L ⊔ conjAutSub t L :=
      (congrArg (fun H : Subgroup (MulAut W) => (a : MulAut W) ∈ H) n.Mp_eq).mp a.2
    obtain ⟨l, hl, hal⟩ := exists_mem_of_mem_sup_of_le_centSub (X := L) (Y := conjAutSub t L)
      (U := V) (d36r_Lt_le_normalizer hL38 n) (fun y hy u hu => n.triv u hu y hy) (a : MulAut W) ha
    show (a : MulAut W) v = v
    rw [hal v hv]
    exact hcon l hl v hv
  exact absurd hfix (not_le_of_gt h1)

private theorem d36r_S_normalizer_Lt (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ s ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      s ∈ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) := by
  rintro s ⟨hsT, hsN⟩
  have hD := (d36r_l38 hL38 n).2.2 (s * t) (T.mul_mem hsT n.tT)
  rcases hD with h | h
  · exfalso
    apply n.tn
    have h1 : conjAutSub t L = conjAutSub s⁻¹ (conjAutSub s (conjAutSub t L)) :=
      (conjAutSub_inv_conjAutSub _ s).symm
    rw [d36r_conj_conj s t L, h] at h1
    have h2 : conjAutSub s⁻¹ L = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hsN)
    rw [h2] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  · rw [← d36r_conj_conj] at h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private theorem d36r_L_le_stabU (n : D36Norm M Mp T L V t) :
    L ≤ stabSub (commSub (orbSup T V) L) := fun _ hg =>
  mem_stabSub_commSub (d36r_stab_orbSup n (d36r_L_le_Mp n hg)) (Subgroup.le_normalizer hg)

omit [Finite W] in
private theorem d36r_S_le_stabU :
    T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commSub (orbSup T V) L) :=
  fun _ hg => mem_stabSub_commSub (le_stabSub_orbSup T V hg.1) hg.2

private theorem d36r_Lt_le_centU (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    conjAutSub t L ≤ centSub (commSub (orbSup T V) L) := by
  intro g hg u hu
  rw [d36_U_eq hL38 n] at hu
  have key : orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ≤ fixV (conjAutSub t L) := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩ g hg
    have hn := d36r_S_normalizer_Lt hL38 n s hs
    have hg' : s⁻¹ * g * s ∈ conjAutSub t L := (Subgroup.mem_normalizer_iff''.mp hn g).mp hg
    have h1 : g (s v) = s ((s⁻¹ * g * s) v) := by simp [MulAut.mul_apply]
    show g (s v) = s v
    rw [h1, n.triv v hv _ hg']
  exact key hu g hg

private theorem d36r_Mp_le_stabU (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ stabSub (commSub (orbSup T V) L) := by
  rw [n.Mp_eq]
  exact sup_le (d36r_L_le_stabU n) ((d36r_Lt_le_centU hL38 n).trans (centSub_le_stabSub _))

private theorem d36r_K1 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ commSub (orbSup T V) L, a u = l u := by
  intro a ha
  rw [n.Mp_eq] at ha
  exact exists_mem_of_mem_sup_of_le_centSub (d36r_Lt_le_normalizer hL38 n)
    (d36r_Lt_le_centU hL38 n) a ha

private theorem d36r_t_not_stab (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    t ∉ stabSub (commSub (orbSup T V) L) := by
  intro ht
  obtain ⟨l, hl, v, hv, hne⟩ := d36r_nontriv hL38 n
  apply hne
  have hVU := d36_V_le_U hL38 n
  have hg : t * l * t⁻¹ ∈ conjAutSub t L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have h1 := d36r_Lt_le_centU hL38 n hg (t v) ((ht v).2 (hVU hv))
  have h2 : t (l v) = t v := by simpa [MulAut.mul_apply] using h1
  exact t.injective h2

private theorem d36r_T_inf_stab_le (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ s ∈ T, s ∈ stabSub (commSub (orbSup T V) L) → s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  intro s hsT hs
  rcases d36_split hL38 n s hsT with h | h
  · exact h
  · exfalso
    apply d36r_t_not_stab hL38 n
    have hr : t⁻¹ * s ∈ stabSub (commSub (orbSup T V) L) :=
      d36r_S_le_stabU ⟨T.mul_mem (T.inv_mem n.tT) hsT, h⟩
    have h' := (stabSub (commSub (orbSup T V) L)).mul_mem hs
      ((stabSub (commSub (orbSup T V) L)).inv_mem hr)
    rwa [show s * (t⁻¹ * s)⁻¹ = t by group] at h'

end D36Facts

section Transport

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem orbSup_autSub_subgroupOf_eq_top {S : Subgroup (MulAut W)} {V U : Subgroup W} (hVU : V ≤ U)
    (hS : S ≤ stabSub U) (hUS : U ≤ orbSup S V) :
    orbSup (autSub S U) (V.subgroupOf U) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : W) ∈ orbSup S V := hUS x.2
  have hle : orbSup S V ≤ (orbSup (autSub S U) (V.subgroupOf U)).map U.subtype := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvU : v ∈ U := hVU hv
    refine ⟨resHom U ⟨s, hS hs⟩ ⟨v, hvU⟩, ?_, rfl⟩
    exact map_le_orbSup (mem_autSub.mpr ⟨⟨s, hS hs⟩, hs, rfl⟩) ⟨⟨v, hvU⟩, hv, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

theorem pCoreOf_autSub_eq_bot_of_isSimple {L : Subgroup (MulAut W)} {U : Subgroup W} (hL : L ≤ stabSub U)
    [IsSimpleGroup ↥L] (hns : ¬ Group.IsSolvable ↥L) (hnt : autSub L U ≠ ⊥) :
    pCoreOf 2 (autSub L U) = ⊥ := by
  have hrange : (resHomOn U hL).range = autSub L U := (autSub_eq_range_resHomOn hL).symm
  have hker : (resHomOn U hL).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resHomOn U hL).ker with h | h
    · exact h
    · exfalso
      apply hnt
      rw [← hrange, eq_bot_iff]
      rintro _ ⟨l, rfl⟩
      have : l ∈ (resHomOn U hL).ker := by rw [h]; trivial
      exact this
  have hinj : Function.Injective (resHomOn U hL) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hPnorm : autSub L U ≤ Subgroup.normalizer (pCoreOf 2 (autSub L U) : Set (MulAut ↥U)) :=
    le_normalizer_pCoreOf 2 _
  have hPL : pCoreOf 2 (autSub L U) ≤ autSub L U := pCoreOf_le 2 _
  have hmem : ∀ l : ↥L, resHomOn U hL l ∈ autSub L U := fun l => by
    rw [← hrange]; exact ⟨l, rfl⟩
  have hPtn : ((pCoreOf 2 (autSub L U)).comap (resHomOn U hL)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hPnorm (hmem g)) _).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pCoreOf 2 (autSub L U)).comap (resHomOn U hL))
    with h | h
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨l, rfl⟩ : x ∈ (resHomOn U hL).range := by rw [hrange]; exact hPL hx
    have hl : l ∈ (pCoreOf 2 (autSub L U)).comap (resHomOn U hL) := hx
    rw [h, Subgroup.mem_bot] at hl
    rw [hl, map_one]
    exact Subgroup.one_mem _
  · exfalso
    have hall : ∀ l : ↥L, resHomOn U hL l ∈ pCoreOf 2 (autSub L U) := fun l => by
      have : l ∈ (pCoreOf 2 (autSub L U)).comap (resHomOn U hL) := by rw [h]; trivial
      exact this
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (autSub L U)) := pCoreOf_isPGroup 2 _
    have hL2 : IsPGroup 2 ↥L := by
      refine IsPGroup.of_injective hP2 ((resHomOn U hL).codRestrict _ hall) ?_
      intro a b hab
      exact hinj (congrArg Subtype.val hab)
    have : Group.IsNilpotent ↥L := hL2.isNilpotent
    exact hns inferInstance

end Transport

section Transport2

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L S : Subgroup (MulAut W)} {V U : Subgroup W}

omit [Finite W] in
theorem autSub_ne_bot_of_exists {L : Subgroup (MulAut W)} {V U : Subgroup W} (hLs : L ≤ stabSub U)
    (hVU : V ≤ U) (hnt : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v) : autSub L U ≠ ⊥ := by
  intro hbot
  obtain ⟨l, hl, v, hv, hne⟩ := hnt
  apply hne
  have h0 : resHom U ⟨l, hLs hl⟩ ∈ autSub L U := mem_autSub.mpr ⟨⟨l, hLs hl⟩, hl, rfl⟩
  rw [hbot] at h0
  have h1 : resHom U ⟨l, hLs hl⟩ = 1 := h0
  exact congrArg (fun f : MulAut ↥U => ((f ⟨v, hVU hv⟩ : ↥U) : W)) h1


theorem isQuasisimple_map_subgroupOf_of_ne_bot {G Γ : Type*} [Group G] [Group Γ] {L X : Subgroup G}
    (hLX : L ≤ X) (hL : CFSG.IsQuasisimple ↥L) (φ : ↥X →* Γ)
    (hne : (L.subgroupOf X).map φ ≠ ⊥) : CFSG.IsQuasisimple ↥((L.subgroupOf X).map φ) := by
  let ψ : ↥L →* ↥((L.subgroupOf X).map φ) :=
    (φ.comp (Subgroup.inclusion hLX)).codRestrict _
      (fun l => ⟨⟨(l : G), hLX l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩
  obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨l, rfl⟩ := hsurj y
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hL hsurj ⟨l, hy⟩

theorem d3Std_restrict (hD : D3Std M Mp T L V)
    (hST : S ≤ T) (hSL : S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hMpL : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hSyl : IsSylowTwoOf S (Mp ⊔ S))
    (hLs : L ≤ stabSub U) (hSs : S ≤ stabSub U) (hMps : Mp ≤ stabSub U)
    (hK1 : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ U, a u = l u)
    (hVU : V ≤ U) (hUS : U ≤ orbSup S V) (hnt : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v)
    (hO2 : pCoreOf 2 (autSub L U) = ⊥)
    (hq : qhatOf (autSub L U ⊔ autSub S U) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autSub (Mp ⊔ S) U) (autSub L U) (autSub S U) (autSub L U) (V.subgroupOf U) := by
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hLMp : L ≤ Mp := by rw [hD.hyp.Mp_eq]; exact le_conjClosure L T
  have hMpM : Mp ≤ M := by
    rw [hD.hyp.Mp_eq]
    exact conjClosure_le fun s hs z hz =>
      M.mul_mem (M.mul_mem (hTM hs) (hLM hz)) (M.inv_mem (hTM hs))
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]; exact le_normalizer_conjClosure L T
  have hSMp : S ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hST.trans hTn
  have hX : Mp ⊔ S ≤ stabSub U := sup_le hMps hSs
  have hXM : Mp ⊔ S ≤ M := sup_le hMpM (hST.trans hTM)
  have hXL : Mp ⊔ S ≤ Subgroup.normalizer (L : Set (MulAut W)) := sup_le hMpL hSL
  have hLX : L ≤ Mp ⊔ S := hLMp.trans le_sup_left
  have hSX : S ≤ Mp ⊔ S := le_sup_right
  have hexp : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have eL : autSub L U = (L.subgroupOf (Mp ⊔ S)).map (resHomOn U hX) := autSub_eq_map_resHomOn hLX hX
  have eS : autSub S U = (S.subgroupOf (Mp ⊔ S)).map (resHomOn U hX) := autSub_eq_map_resHomOn hSX hX
  have eX : autSub (Mp ⊔ S) U = ((Mp ⊔ S).subgroupOf (Mp ⊔ S)).map (resHomOn U hX) :=
    autSub_eq_map_resHomOn le_rfl hX
  have hLne : autSub L U ≠ ⊥ := autSub_ne_bot_of_exists hLs hVU hnt
  have hMnorm : autSub (Mp ⊔ S) U ≤ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) := by
    rw [eX, eL]
    exact map_le_normalizer_map_of_le_normalizer (resHomOn U hX) hLX hXL
  have hSylF : IsSylowTwoOf (autSub S U) (autSub (Mp ⊔ S) U) := by
    rw [eS, eX]
    exact isSylowTwoOf_map_subgroupOf (resHomOn U hX) hSyl
  have hcomp : autSub L U ∈ cComp (autSub (Mp ⊔ S) U) := by
    rw [eL, eX]
    exact map_subgroupOf_mem_cComp (resHomOn U hX) (cComp_mem_of_le hD.hyp.comp hLX hXM)
      (by rw [← eL]; exact hLne)
  have hquasi : CFSG.IsQuasisimple ↥(autSub L U) := by
    rw [eL]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLX hD.hyp.quasi (resHomOn U hX)
      (by rw [← eL]; exact hLne)
  have hcc : conjClosure L S = L := le_antisymm
    (conjClosure_le fun s hs z hz => (Subgroup.mem_normalizer_iff.mp (hSL hs) z).mp hz)
    (le_conjClosure L S)
  have hMpeq : autSub L U = conjClosure (autSub L U) (autSub S U) := by
    have h := map_subgroupOf_conjClosure (resHomOn U hX) hLX hSX
    rw [hcc] at h
    rw [eL, eS]
    exact h
  have hMpAC : ActCompat U.subtype (autSub L U) Mp := actCompat_autSub hMps hLMp hK1
  have hSAC : ActCompat U.subtype (autSub S U) S :=
    actCompat_autSub hSs le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hmapV : (V.subgroupOf U).map U.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVU
  have hVirr : XMod.IsIrrPlus ↥(autSub L U) (V.subgroupOf U) :=
    (hMpAC.isIrrPlus_map_iff U.subtype_injective (V.subgroupOf U)).mp
      (by rw [hmapV]; exact hD.hyp.irr.2)
  have hWT : ∀ s ∈ T, ∀ w ∈ orbSup T V, s • w ∈ orbSup T V := fun s hs w hw =>
    mem_orbSup_of_mem_map hs hw
  have hI : V ∈ IrrPlus Mp (orbSup T V) := hD.irrT.1
  have hirrS : V ∈ IrrPlusOn Mp (orbSup T V) S := by
    refine (forall_smul_eq_iff_mem_irrPlusOn hSMp (fun s hs w hw => hWT s (hST hs) w hw) hI).mp ?_
    intro s hs
    exact ((forall_smul_eq_iff_mem_irrPlusOn hTn hWT hI).mpr hD.irrT) s ⟨hST hs.1, hs.2⟩
  have hTnAut : autSub S U ≤ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) :=
    (autSub_mono hSX U).trans hMnorm
  have hirrT : V.subgroupOf U ∈
      IrrPlusOn (autSub L U) (orbSup (autSub S U) (V.subgroupOf U)) (autSub S U) := by
    rw [orbSup_eq_biSup_smul]
    exact hMpAC.mem_irrPlusOn_of_map U.subtype_injective hSAC hTnAut hSMp
      (Wq := orbSup T V) (fun s hs w hw => hWT s (hST hs) w hw) (by rw [hmapV]; exact hirrS)
  have hSylF' : IsSylowTwoOf (autSub S U) (autSub L U ⊔ autSub S U) :=
    isSylowTwoOf_mono_right hSylF le_sup_right
      (sup_le (autSub_mono hLX U) (autSub_mono hSX U))
  have ho2 := o2inv_of_irrPlusOn hTnAut hSylF' hO2 hirrT
  have htop : orbSup (autSub S U) (V.subgroupOf U) = ⊤ :=
    orbSup_autSub_subgroupOf_eq_top hVU hSs hUS
  have hgen : (⨆ m ∈ autSub (Mp ⊔ S) U, (V.subgroupOf U).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ ((autSub_mono hSX U) hτ) le_rfl
  have hqhat : qhatOf (autSub (autSub L U ⊔ autSub S U)
      (orbSup (autSub S U) (V.subgroupOf U))) ≤ ((2 : ℚ) : WithTop ℚ) := by
    obtain ⟨A, hA2, hAk, hAr⟩ := kq_le_iff.mp hq
    have hAst : A ≤ stabSub (orbSup (autSub S U) (V.subgroupOf U)) := by
      rw [htop]; exact le_stabSub_top A
    have hAf : A ⊓ centSub (orbSup (autSub S U) (V.subgroupOf U)) = ⊥ := by
      rw [htop, eq_bot_iff]
      rintro a ⟨-, ha⟩
      rw [Subgroup.mem_bot]
      ext u
      exact congrArg Subtype.val (ha u trivial)
    have hAU : commSub (orbSup (autSub S U) (V.subgroupOf U)) A ≠ ⊥ := by
      rw [htop]
      intro hbot
      apply hA2.ne_bot
      rw [commSub_eq_bot_iff] at hbot
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      ext u
      exact congrArg Subtype.val (hbot (Subgroup.mem_top u) a ha)
    exact kq_le_iff.mpr ⟨autSub A _, IsA2.autSub hA2 hAst hAU, commSeries_autSub_eq_bot hAst hAk,
      (rAV_autSub_le_of_faithful hexp hAst hAf).trans hAr⟩
  exact ⟨⟨hexp, isQuotientOfSQTK_autSub_aux hXM hD.hyp.qsqtk, hSylF, hcomp, hquasi, hMpeq, hMnorm,
    ⟨le_top, hVirr⟩, ho2, hgen⟩, hqhat, hirrT⟩

end Transport2

section D36Restrict

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem d36r_autSub_sup (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    autSub (Mp ⊔ T) (commSub (orbSup T V) L) =
      autSub L (commSub (orbSup T V) L) ⊔
        autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub (orbSup T V) L) := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    have hg' : (g : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T (d36r_T_le_normalizer n)] at hg'
    obtain ⟨m, hm, s', hs', hms⟩ := hg'
    have hmstab : m ∈ stabSub (commSub (orbSup T V) L) := d36r_Mp_le_stabU hL38 n hm
    have hs'stab : s' ∈ stabSub (commSub (orbSup T V) L) := by
      have h1 : s' = m⁻¹ * (g : MulAut W) := by rw [← hms]; group
      rw [h1]
      exact (stabSub (commSub (orbSup T V) L)).mul_mem
        ((stabSub (commSub (orbSup T V) L)).inv_mem hmstab) g.2
    have hs'S : s' ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
      ⟨hs', d36r_T_inf_stab_le hL38 n s' hs' hs'stab⟩
    obtain ⟨l, hl, hml⟩ := d36r_K1 hL38 n m hm
    have hlstab : l ∈ stabSub (commSub (orbSup T V) L) := d36r_L_le_stabU n hl
    have e1 : resHom (commSub (orbSup T V) L) g =
        resHom (commSub (orbSup T V) L) ⟨l, hlstab⟩ *
          resHom (commSub (orbSup T V) L) ⟨s', hs'stab⟩ := by
      ext u
      show (g : MulAut W) (u : W) = l (s' (u : W))
      rw [← hms]
      show m (s' (u : W)) = l (s' (u : W))
      exact hml _ ((hs'stab _).2 u.2)
    rw [e1]
    exact Subgroup.mul_mem_sup (mem_autSub.mpr ⟨⟨l, hlstab⟩, hl, rfl⟩)
      (mem_autSub.mpr ⟨⟨s', hs'stab⟩, hs'S, rfl⟩)
  · exact sup_le (autSub_mono (d36r_L_le_Mp n |>.trans le_sup_left) _)
      (autSub_mono (inf_le_left.trans le_sup_right) _)

theorem d36_restrict (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hq : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autSub (Mp ⊔ (T ⊓ Subgroup.normalizer (L : Set (MulAut W)))) (commSub (orbSup T V) L))
      (autSub L (commSub (orbSup T V) L))
      (autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub (orbSup T V) L))
      (autSub L (commSub (orbSup T V) L)) (V.subgroupOf (commSub (orbSup T V) L)) := by
  have hSyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (Mp ⊔ T ⊓ Subgroup.normalizer (L : Set (MulAut W))) :=
    isSylowTwoOf_sup_of_inf_le inf_le_left (d36r_T_le_normalizer n)
      (fun g hg => ⟨hg.2, d36r_Mp_le_normalizer hL38 n hg.1⟩)
      (isSylowTwoOf_mono_right n.std.hyp.sylow le_sup_right
        (sup_le (d36r_Mp_le_M n) (d36r_TM n)))
  have : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types (d36r_l38 hL38 n).1
  have hO2 : pCoreOf 2 (autSub L (commSub (orbSup T V) L)) = ⊥ :=
    pCoreOf_autSub_eq_bot_of_isSimple (d36r_L_le_stabU n) (not_isSolvable_of_mem_cComp n.std.hyp.comp)
      (autSub_ne_bot_of_exists (d36r_L_le_stabU n) (d36_V_le_U hL38 n) (d36r_nontriv hL38 n))
  exact d3Std_restrict n.std inf_le_left inf_le_right (d36r_Mp_le_normalizer hL38 n) hSyl
    (d36r_L_le_stabU n) d36r_S_le_stabU (d36r_Mp_le_stabU hL38 n) (d36r_K1 hL38 n)
    (d36_V_le_U hL38 n) (d36_U_eq hL38 n).le (d36r_nontriv hL38 n) hO2
    (by rw [← d36r_autSub_sup hL38 n]; exact hq)

theorem d36_restrict_aux (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hVU : V < commSub (orbSup T V) L) :
    V.subgroupOf (commSub (orbSup T V) L) <
        orbSup (autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub (orbSup T V) L))
          (V.subgroupOf (commSub (orbSup T V) L)) ∧
      ∀ g ∈ autSub L (commSub (orbSup T V) L),
        (∀ v ∈ V.subgroupOf (commSub (orbSup T V) L), g v = v) →
          ∀ x ∈ autSub L (commSub (orbSup T V) L), g * x = x * g := by
  have htop := orbSup_autSub_subgroupOf_eq_top (d36_V_le_U hL38 n) d36r_S_le_stabU
    (d36_U_eq hL38 n).le
  refine ⟨?_, ?_⟩
  · rw [htop]
    exact lt_top_iff_ne_top.mpr fun h => hVU.not_ge (Subgroup.subgroupOf_eq_top.mp h)
  · intro g hg hfix x _
    obtain ⟨⟨l, hlstab⟩, hl, rfl⟩ := mem_autSub.mp hg
    have hlV : ∀ v ∈ V, l v = v := fun v hv =>
      congrArg Subtype.val (hfix ⟨v, (d36_V_le_U hL38 n) hv⟩ hv)
    have : IsSimpleGroup ↥L :=
      CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types (d36r_l38 hL38 n).1
    have hKn : ((centSub V).subgroupOf L).Normal := by
      refine ⟨fun k hk g => ?_⟩
      rw [Subgroup.mem_subgroupOf, mem_centSub] at hk ⊢
      intro v hv
      have hgv : (g : MulAut W)⁻¹ v ∈ V :=
        (d36r_stab_V n (d36r_L_le_Mp n ((L.inv_mem g.2) : (g : MulAut W)⁻¹ ∈ L)) v).2 hv
      have h1 := hk _ hgv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
      rw [h1]
      simp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((centSub V).subgroupOf L) with h | h
    · have hl1 : (⟨l, hl⟩ : ↥L) ∈ (centSub V).subgroupOf L := hlV
      rw [h, Subgroup.mem_bot] at hl1
      have hl1' : l = 1 := congrArg Subtype.val hl1
      subst hl1'
      have h1 : resHom (commSub (orbSup T V) L) ⟨1, hlstab⟩ = 1 := map_one _
      rw [h1, one_mul, mul_one]
    · exfalso
      obtain ⟨l₀, hl₀, v, hv, hne⟩ := d36r_nontriv hL38 n
      have : (⟨l₀, hl₀⟩ : ↥L) ∈ (centSub V).subgroupOf L := by rw [h]; trivial
      exact hne (this v hv)

end D36Restrict

end CFSG.Quasithin
