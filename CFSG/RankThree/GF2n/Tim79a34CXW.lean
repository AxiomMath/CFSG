module

public import CFSG.RankThree.GF2n.Tim79a34Natural
public import CFSG.RankThree.GF2n.Tim79a34SpFacts
public import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ComponentClassification.PresentationLocal
open CFSG.SignalizerFunctorTheorem.NonLocal
open scoped commutatorElement

theorem cxw_comm_statedSp_two_le {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (K : Subgroup (StatedSp 2 F)) [K.Normal] (hK : K ≠ ⊥) :
    commutator (StatedSp 2 F) ≤ K := by
  let φ : StatedSp 2 F ≃* Equiv.Perm (Fin 6) :=
    (spTwoTwoEquiv hF).trans
      (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩)
  haveI hA : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hmap : (commutator (StatedSp 2 F)).map φ.toMonoidHom =
      commutator (Equiv.Perm (Fin 6)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 φ.surjective]
  let K' : Subgroup (Equiv.Perm (Fin 6)) := K.map φ.toMonoidHom
  haveI : K'.Normal := Subgroup.Normal.map ‹K.Normal› φ.toMonoidHom φ.surjective
  have hK'ne : K' ≠ ⊥ :=
    fun h => hK ((Subgroup.map_eq_bot_iff_of_injective K (f := φ.toMonoidHom) φ.injective).1 h)
  have hAK : alternatingGroup (Fin 6) ≤ K' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (K'.subgroupOf (alternatingGroup (Fin 6))) with h | h
    · exfalso
      apply hK'ne
      rw [Subgroup.eq_bot_iff_forall]
      intro k hk
      have hcomm : ∀ a ∈ alternatingGroup (Fin 6), k * a = a * k := by
        intro a ha
        have hcA : ⁅k, a⁆ ∈ alternatingGroup (Fin 6) := by
          rw [commutatorElement_def]
          exact (alternatingGroup (Fin 6)).mul_mem
            (Subgroup.Normal.conj_mem inferInstance a ha k)
            ((alternatingGroup (Fin 6)).inv_mem ha)
        have hcK : ⁅k, a⁆ ∈ K' := by
          have e : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by
            rw [commutatorElement_def]
            simp only [mul_assoc]
          rw [e]
          exact K'.mul_mem hk (Subgroup.Normal.conj_mem inferInstance k⁻¹ (K'.inv_mem hk) a)
        have h1 : (⟨⁅k, a⁆, hcA⟩ : alternatingGroup (Fin 6)) ∈
            K'.subgroupOf (alternatingGroup (Fin 6)) :=
          Subgroup.mem_subgroupOf.2 hcK
        rw [h, Subgroup.mem_bot] at h1
        have h2 : ⁅k, a⁆ = 1 := congrArg Subtype.val h1
        calc k * a = (k * a * k⁻¹ * a⁻¹) * (a * k) := by group
          _ = a * k := by rw [← commutatorElement_def, h2, one_mul]
      exact CFSG.ClassicalInvolution.Sp62Rec.I1.eq_one_of_commute_alternating k hcomm
    · intro a ha
      have h1 : (⟨a, ha⟩ : alternatingGroup (Fin 6)) ∈
          K'.subgroupOf (alternatingGroup (Fin 6)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 h1
  intro x hx
  have hx' : φ x ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hx'' : φ x ∈ K' :=
    hAK (alternatingGroup.commutator_perm_le (α := Fin 6) hx')
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx''
  have hkx' : k = x := φ.injective hkx
  exact hkx' ▸ hk

theorem cxw_comm_statedSp_le {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (K : Subgroup (StatedSp n F)) [K.Normal] (hK : K ≠ ⊥) :
    commutator (StatedSp n F) ≤ K := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    exact cxw_comm_statedSp_two_le hF K hK
  · haveI := isSimpleGroup_statedSp_of_card_two h3 hF
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact absurd h hK
    · rw [h]
      exact le_top

theorem cxw_comm_le_of_mulEquiv {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2) (e : Y ≃* StatedSp n F) (K : Subgroup Y) [K.Normal]
    (hK : K ≠ ⊥) : commutator Y ≤ K := by
  have hKe : K.map e.toMonoidHom ≠ ⊥ := fun h =>
    hK ((Subgroup.map_eq_bot_iff_of_injective K (f := e.toMonoidHom) e.injective).1 h)
  haveI : (K.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹K.Normal› e.toMonoidHom e.surjective
  have hc := cxw_comm_statedSp_le hn hF (K.map e.toMonoidHom) hKe
  have hmap : (commutator Y).map e.toMonoidHom = commutator (StatedSp n F) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  intro x hx
  have hx' : e x ∈ commutator (StatedSp n F) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hc hx')
  have hkx' : k = x := e.injective hkx
  exact hkx' ▸ hk

theorem cxw_comm_statedSp_ne_bot {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : commutator (StatedSp n F) ≠ ⊥ := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    intro h
    have h1 : Nat.card (commutator (StatedSp 2 F)) = 360 := by
      rw [Nat.card_congr (commutatorSpTwoEquiv hF).toEquiv, nat_card_alternatingGroup,
        Nat.card_fin]
      rfl
    rw [h, Subgroup.card_bot] at h1
    omega
  · intro h
    rw [commutator_statedSp_eq_top h3 hF, Subgroup.eq_bot_iff_forall] at h
    haveI := isSimpleGroup_statedSp_of_card_two h3 hF
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedSp n F)
    exact hx (h x (Subgroup.mem_top x))

theorem cxw_comm_eq_bot {Y : Type} [Group Y] (h : ∀ a b : Y, a * b = b * a) :
    commutator Y = ⊥ := by
  rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a _
  rw [Subgroup.mem_centralizer_iff]
  intro b _
  exact h b a

theorem cxw_comm_ne_bot_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : commutator Z ≠ ⊥) : commutator Y ≠ ⊥ := by
  intro h1
  apply h
  have hmap : (commutator Y).map e.toMonoidHom = commutator Z := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  rw [← hmap, h1, Subgroup.map_bot]

theorem cxw_eq_of_ne_one {S : Type} [Group S] (hS : Nat.card S = 2) {a b : S}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨c, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : S)).1 hS
  exact (huniq a ha).trans (huniq b hb).symm

theorem cxw_xbar_iso {G : Type} [Group G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hcen : Subgroup.center (Xbar V H) = ⊥) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (Xbar V H ≃* StatedSp n (GaloisField 2 1)) := by
  obtain ⟨f, hf, h2f, n, hn, Φ, hΦ, -⟩ := id hH.three
  have hf1 : f = 1 := by
    have : 2 ^ f = 2 ^ 1 := by rw [h2f, hH.q_two]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hf1
  have hproj : Function.Bijective (projZ V H) := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (QuotientGroup.mk a : Xbar V H ⧸ Subgroup.center (Xbar V H)) = 1 := ha
    rw [QuotientGroup.eq_one_iff, hcen, Subgroup.mem_bot] at h1
    exact h1
  exact ⟨n, hn, ⟨(MulEquiv.ofBijective (projZ V H) hproj).trans
    (MulEquiv.ofBijective Φ hΦ).symm⟩⟩

section Centralizer

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem cxw_wOf_conj {h w : G} (hh : h ∈ H) (hw : w ∈ wOf V H) : h * w * h⁻¹ ∈ wOf V H :=
  (Subgroup.mem_normalizer_iff.1 (H_le_normalizer_wOf V H hh) w).1 hw

theorem cxw_wOf_comm (hc : MinCex M V Q P H) {w t : G} (hw : w ∈ wOf V H) (ht : t ∈ wOf V H) :
    w * t = t * w :=
  congrArg Subtype.val (hc.wOf_isElemAbelian.1.is_comm.comm ⟨w, hw⟩ ⟨t, ht⟩)

@[expose] def cxwCent (V H : Subgroup G) : Subgroup G :=
  xOf V H ⊓ Subgroup.centralizer (wOf V H : Set G)

theorem cxw_mem {x : G} : x ∈ cxwCent V H ↔ x ∈ xOf V H ∧ ∀ w ∈ wOf V H, w * x = x * w := by
  rw [cxwCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem cxw_wOf_le (hc : MinCex M V Q P H) : wOf V H ≤ cxwCent V H := fun w hw =>
  cxw_mem.2 ⟨wOf_le_xOf V H hw, fun u hu => cxw_wOf_comm hc hu hw⟩

theorem cxw_subgroupOf_normal (hVH : V ≤ H) : ((cxwCent V H).subgroupOf (xOf V H)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnX, hnC⟩ := cxw_mem.1 hn
  have hg : (g : G) ∈ H := xOf_le_H hVH g.2
  refine cxw_mem.2 ⟨?_, fun w hw => ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (xOf V H).mul_mem ((xOf V H).mul_mem g.2 hnX) ((xOf V H).inv_mem g.2)
  · have hw' : (g : G)⁻¹ * w * (g : G) ∈ wOf V H := by
      have := cxw_wOf_conj (H.inv_mem hg) hw
      rwa [inv_inv] at this
    have key := hnC _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e : w * ((g : G) * (n : G) * (g : G)⁻¹) =
        (g : G) * (((g : G)⁻¹ * w * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
    rw [e, key]
    group

@[expose] noncomputable def cxwKbar (hVH : V ≤ H) : Subgroup (Xbar V H) :=
  ((cxwCent V H).subgroupOf (xOf V H)).map (xToXbar hVH)

theorem cxwKbar_normal (hVH : V ≤ H) : (cxwKbar hVH).Normal :=
  Subgroup.Normal.map (cxw_subgroupOf_normal hVH) (xToXbar hVH) (xToXbar_surjective hVH)

theorem cxw_xToXbar_eq_one (hVH : V ≤ H) (x : ↥(xOf V H)) :
    xToXbar hVH x = 1 ↔ (x : G) ∈ wOf V H := by
  constructor
  · intro h
    have h1 : ((xToXbar hVH x : Xbar V H) : Hbar V H) = 1 := by simp [h]
    rw [coe_xToXbar] at h1
    exact (piBar_eq_one_iff _).1 h1
  · intro h
    apply Subtype.ext
    rw [coe_xToXbar]
    exact (piBar_eq_one_iff _).2 h

theorem cxwKbar_ne_bot (hVH : V ≤ H) {x : ↥(xOf V H)} (hx : (x : G) ∈ cxwCent V H)
    (hxW : (x : G) ∉ wOf V H) : cxwKbar hVH ≠ ⊥ := by
  intro h
  have hmem : xToXbar hVH x ∈ cxwKbar hVH :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
  rw [h, Subgroup.mem_bot] at hmem
  exact hxW ((cxw_xToXbar_eq_one hVH x).1 hmem)

theorem cxw_xToXbar_mem_Dy (hVH : V ≤ H) {x : ↥(xOf V H)} (hxd : (x : G) ∈ dOf V H)
    (hxW : (x : G) ∉ wOf V H) : xToXbar hVH x ∈ Dy V H := by
  show ((xToXbar hVH x : Xbar V H) : Hbar V H) ∈ dbarOf V H
  rw [coe_xToXbar]
  exact mem_dbarOf_iff.2 ⟨Subgroup.inclusion (xOf_le_H hVH) x, hxd, hxW, rfl⟩

theorem cxw_mem_dOf {U : Subgroup G} (hU : U ∈ omegaOf V H) {y : G} (hyU : y ∈ U)
    (hyW : y ∉ wOf V H) : y ∈ dOf V H := by
  rw [dOf, Set.mem_setOf_eq]
  exact ⟨fun h1 => hyW (by rw [h1]; exact (wOf V H).one_mem), U, hU, hyU⟩

theorem cxw_Dy_div (hd : Sec23Data V H) {a b : Xbar V H} (ha : a ∈ Dy V H)
    (hb : b ∈ Dy V H) : a⁻¹ * b ∈ commutator (Xbar V H) := by
  obtain ⟨d₀, hd₀⟩ := hd.isClass
  rw [hd₀, Set.mem_setOf_eq] at ha hb
  obtain ⟨c, hc⟩ := isConj_iff.1 (ha.symm.trans hb)
  rw [← hc]
  have e : a⁻¹ * (c * a * c⁻¹) = ⁅a⁻¹, c⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem cxw_of_mem_Dy (hc : MinCex M V Q P H) (hVH : V ≤ H) (hd : Sec23Data V H)
    (hK : commutator (Xbar V H) ≤ cxwKbar hVH) {y y' : ↥(xOf V H)}
    (hy : xToXbar hVH y ∈ Dy V H) (hy' : xToXbar hVH y' ∈ Dy V H) :
    (y : G)⁻¹ * (y' : G) ∈ cxwCent V H := by
  have hdiv : (xToXbar hVH y)⁻¹ * xToXbar hVH y' ∈ cxwKbar hVH :=
    hK (cxw_Dy_div hd hy hy')
  obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 hdiv
  have hk' : (k : G) ∈ cxwCent V H := Subgroup.mem_subgroupOf.1 hk
  have h1 : xToXbar hVH (k⁻¹ * (y⁻¹ * y')) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hkeq]
    group
  have h2 : (k : G)⁻¹ * ((y : G)⁻¹ * (y' : G)) ∈ wOf V H := by
    have := (cxw_xToXbar_eq_one hVH _).1 h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have e : (y : G)⁻¹ * (y' : G) = (k : G) * ((k : G)⁻¹ * ((y : G)⁻¹ * (y' : G))) := by
    group
  rw [e]
  exact (cxwCent V H).mul_mem hk' (cxw_wOf_le hc h2)

theorem cxw_conj_eq {yV y : G} (hk : ∀ w ∈ wOf V H, w * (yV⁻¹ * y) = (yV⁻¹ * y) * w) :
    ∀ w ∈ wOf V H, y * w * y⁻¹ = yV * w * yV⁻¹ := by
  intro w hw
  calc y * w * y⁻¹ = yV * ((yV⁻¹ * y) * w * (yV⁻¹ * y)⁻¹) * yV⁻¹ := by group
    _ = yV * (w * (yV⁻¹ * y) * (yV⁻¹ * y)⁻¹) * yV⁻¹ := by rw [← hk w hw]
    _ = yV * w * yV⁻¹ := by group

theorem cxw_wOf_normalizer [Finite G] (hc : MinCex M V Q P H) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) {w : G} (hw : w ∈ wOf V H) :
    w ∈ Subgroup.normalizer (U : Set G) := by
  obtain ⟨h, hh, rfl⟩ := hU
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hc.conj_inf_wOf_ne_bot hh)
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti h)
    (Subgroup.mem_inf.1 ht).1 ht1' (cxw_wOf_comm hc hw (Subgroup.mem_inf.1 ht).2)

theorem cxw_natCard_barOf {U : Subgroup G} (hU : U ∈ omegaOf V H) :
    Nat.card (barOf V H U) = qBar V H := by
  obtain ⟨h, hh, rfl⟩ := hU
  have e : conjSubgroup (piBar V H ⟨h, hh⟩) (barOf V H V) = barOf V H (conjSubgroup h V) :=
    conjSubgroup_piBar_barOf ⟨h, hh⟩ V
  change Nat.card (barOf V H (conjSubgroup h V)) = Nat.card (barOf V H V)
  rw [← e, card_conjSubgroup]

theorem cxw_piBar_eq {S : Subgroup G} (hSH : S ≤ H) (hcard : Nat.card (barOf V H S) = 2)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hu' : u ∉ wOf V H) (hv' : v ∉ wOf V H) :
    piBar V H ⟨u, hSH hu⟩ = piBar V H ⟨v, hSH hv⟩ := by
  have h1 : ∀ {x : G} (hx : x ∈ S), x ∉ wOf V H →
      (⟨piBar V H ⟨x, hSH hx⟩, mem_barOf_iff.2 ⟨⟨x, hSH hx⟩, hx, rfl⟩⟩ :
        ↥(barOf V H S)) ≠ 1 := by
    intro x hx hxW h1
    apply hxW
    exact (piBar_eq_one_iff _).1 (congrArg Subtype.val h1)
  exact congrArg Subtype.val (cxw_eq_of_ne_one hcard (h1 hu hu') (h1 hv hv'))

theorem cxw_exists_not_mem (hc : MinCex M V Q P H) {U : Subgroup G} (hU : U ∈ omegaOf V H) :
    ∃ y ∈ U, y ∉ wOf V H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h, hh, rfl⟩ := hU
  apply hc.not_V_le_wOf
  intro v hv
  have hmem : h * v * h⁻¹ ∈ conjSubgroup h V := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * (h * v * h⁻¹) * h = v := by group
    rw [e]
    exact hv
  have h2 := cxw_wOf_conj (H.inv_mem hh) (hcon _ hmem)
  have e2 : h⁻¹ * (h * v * h⁻¹) * h⁻¹⁻¹ = v := by group
  rw [e2] at h2
  exact h2

theorem cxw_exists_y (hc : MinCex M V Q P H) (hVH : V ≤ H) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) :
    ∃ y : ↥(xOf V H), (y : G) ∈ U ∧ (y : G) ∉ wOf V H ∧ xToXbar hVH y ∈ Dy V H := by
  obtain ⟨y, hyU, hyW⟩ := cxw_exists_not_mem hc hU
  exact ⟨⟨y, le_xOf hU hyU⟩, hyU, hyW, cxw_xToXbar_mem_Dy hVH (cxw_mem_dOf hU hyU hyW) hyW⟩

end Centralizer

theorem cxw_holds : CXWStatement := by
  intro G _ _ M V Q P H hH hcen x hxX hcomm
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hd : Sec23Data V H := hH.setup.data
  obtain ⟨n, hn, ⟨e⟩⟩ := cxw_xbar_iso hH hcen
  have hFcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  by_contra hxW
  have hxC : x ∈ cxwCent V H := cxw_mem.2 ⟨hxX, fun w hw => (hcomm w hw).symm⟩
  have hK : cxwKbar hVH ≠ ⊥ := cxwKbar_ne_bot hVH (x := ⟨x, hxX⟩) hxC hxW
  haveI := cxwKbar_normal hVH
  have hKle : commutator (Xbar V H) ≤ cxwKbar hVH :=
    cxw_comm_le_of_mulEquiv hn hFcard e (cxwKbar hVH) hK
  obtain ⟨yV, hyVV, hyVW⟩ : ∃ y ∈ V, y ∉ wOf V H := by
    by_contra hcon
    push Not at hcon
    exact hc.not_V_le_wOf (fun v hv => hcon v hv)
  have hyVX : yV ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hyVV
  have hdV : xToXbar hVH ⟨yV, hyVX⟩ ∈ Dy V H :=
    cxw_xToXbar_mem_Dy hVH (cxw_mem_dOf (V_mem_omegaOf V H) hyVV hyVW) hyVW
  have hcent : ∀ y : ↥(xOf V H), xToXbar hVH y ∈ Dy V H →
      ∀ w ∈ wOf V H, (y : G) * w * (y : G)⁻¹ = yV * w * yV⁻¹ := by
    intro y hy
    have hk : yV⁻¹ * (y : G) ∈ cxwCent V H := cxw_of_mem_Dy hc hVH hd hKle hdV hy
    exact cxw_conj_eq (cxw_mem.1 hk).2
  by_cases hA : ∃ w ∈ wOf V H, w * yV * w⁻¹ * yV⁻¹ ≠ 1
  ·
    obtain ⟨w, hw, hne⟩ := hA
    have hUV : ∀ U ∈ omegaOf V H, U = V := by
      intro U hU
      obtain ⟨y, hyU, hyW, hy⟩ := cxw_exists_y hc hVH hU
      have hcy := hcent y hy
      have hcV : w * yV * w⁻¹ * yV⁻¹ ∈ V := by
        have h1 : w * yV * w⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (cxw_wOf_normalizer hc (V_mem_omegaOf V H) hw) yV).1
            hyVV
        have e1 : w * yV * w⁻¹ * yV⁻¹ = (w * yV * w⁻¹) * yV⁻¹ := rfl
        rw [e1]
        exact V.mul_mem h1 (V.inv_mem hyVV)
      have hcU : w * yV * w⁻¹ * yV⁻¹ ∈ U := by
        have h2 : w * yV * w⁻¹ * yV⁻¹ = w * ((y : G) * w⁻¹ * (y : G)⁻¹) := by
          rw [hcy w⁻¹ ((wOf V H).inv_mem hw)]
          group
        rw [h2]
        have h3 : w * ((y : G) * w⁻¹ * (y : G)⁻¹) = (w * (y : G) * w⁻¹) * (y : G)⁻¹ := by group
        rw [h3]
        exact U.mul_mem
          ((Subgroup.mem_normalizer_iff.1 (cxw_wOf_normalizer hc hU hw) (y : G)).1 hyU)
          (U.inv_mem hyU)
      obtain ⟨h, hh, hUh⟩ := hU
      rw [hUh] at hcU ⊢
      apply conjSubgroup_eq_of_isTI hc.ti
      intro hbot
      have hmem : w * yV * w⁻¹ * yV⁻¹ ∈ V ⊓ conjSubgroup h V := Subgroup.mem_inf.2 ⟨hcV, hcU⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne hmem
    have hXV : xOf V H = V := by
      refine le_antisymm ?_ (le_xOf (V_mem_omegaOf V H))
      unfold xOf
      exact iSup₂_le fun U hU => (hUV U hU).le
    have hcomm_bot : commutator (Xbar V H) = ⊥ := by
      apply cxw_comm_eq_bot
      intro a b
      obtain ⟨a', rfl⟩ := xToXbar_surjective hVH a
      obtain ⟨b', rfl⟩ := xToXbar_surjective hVH b
      rw [← map_mul, ← map_mul]
      congr 1
      have ha' : (a' : G) ∈ V := hXV.le a'.2
      have hb' : (b' : G) ∈ V := hXV.le b'.2
      have hcomm' := congrArg Subtype.val
        (hc.elemAb.1.is_comm.comm ⟨(a' : G), ha'⟩ ⟨(b' : G), hb'⟩)
      exact Subtype.ext hcomm'
    exact cxw_comm_ne_bot_of_mulEquiv e (cxw_comm_statedSp_ne_bot hn hFcard) hcomm_bot
  ·
    push Not at hA
    have hyVc : ∀ w ∈ wOf V H, w * yV = yV * w := by
      intro w hw
      calc w * yV = (w * yV * w⁻¹ * yV⁻¹) * (yV * w) := by group
        _ = yV * w := by rw [hA w hw, one_mul]
    have hUc : ∀ U ∈ omegaOf V H, ∀ u ∈ U, ∀ w ∈ wOf V H, w * u = u * w := by
      intro U hU u hu w hw
      by_cases huW : u ∈ wOf V H
      · exact cxw_wOf_comm hc hw huW
      obtain ⟨y, hyU, hyW, hy⟩ := cxw_exists_y hc hVH hU
      have hyc : ∀ w ∈ wOf V H, w * (y : G) = (y : G) * w := by
        intro w hw
        have hk : yV⁻¹ * (y : G) ∈ cxwCent V H := cxw_of_mem_Dy hc hVH hd hKle hdV hy
        have hk' := (cxw_mem.1 hk).2 w hw
        calc w * (y : G) = w * yV * (yV⁻¹ * (y : G)) := by group
          _ = yV * w * (yV⁻¹ * (y : G)) := by rw [hyVc w hw]
          _ = yV * (w * (yV⁻¹ * (y : G))) := by group
          _ = yV * ((yV⁻¹ * (y : G)) * w) := by rw [hk']
          _ = (y : G) * w := by group
      have hUH : U ≤ H := (le_xOf hU).trans (xOf_le_H hVH)
      have hcard : Nat.card (barOf V H U) = 2 := by
        rw [cxw_natCard_barOf hU]
        exact hH.q_two
      have hpi : piBar V H ⟨u, hUH hu⟩ = piBar V H ⟨(y : G), hUH hyU⟩ :=
        cxw_piBar_eq hUH hcard hu hyU huW hyW
      have hw' : (y : G)⁻¹ * u ∈ wOf V H := by
        have h1 : piBar V H ((⟨(y : G), hUH hyU⟩ : ↥H)⁻¹ * ⟨u, hUH hu⟩) = 1 := by
          rw [map_mul, map_inv, hpi, inv_mul_cancel]
        exact (piBar_eq_one_iff _).1 h1
      calc w * u = w * ((y : G) * ((y : G)⁻¹ * u)) := by group
        _ = (w * (y : G)) * ((y : G)⁻¹ * u) := by rw [mul_assoc]
        _ = ((y : G) * w) * ((y : G)⁻¹ * u) := by rw [hyc w hw]
        _ = (y : G) * (w * ((y : G)⁻¹ * u)) := by rw [mul_assoc]
        _ = (y : G) * (((y : G)⁻¹ * u) * w) := by rw [cxw_wOf_comm hc hw hw']
        _ = u * w := by group
    have hXc : xOf V H ≤ Subgroup.centralizer (wOf V H : Set G) := by
      unfold xOf
      refine iSup₂_le fun U hU => ?_
      intro u hu
      exact Subgroup.mem_centralizer_iff.2 fun w hw => hUc U hU u hu w hw
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.V_inf_wOf_ne_bot
    have haV : (a : G) ∈ V := (Subgroup.mem_inf.1 a.2).1
    have haW : (a : G) ∈ wOf V H := (Subgroup.mem_inf.1 a.2).2
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hXN : ∀ x ∈ xOf V H, x ∈ Subgroup.normalizer (V : Set G) := fun x hx =>
      Tim77.mem_normalizer_of_commute_of_isTI hc.ti haV ha1
        (Subgroup.mem_centralizer_iff.1 (hXc hx) a haW).symm
    have hcentre : xToXbar hVH ⟨yV, hyVX⟩ ∈ Subgroup.center (Xbar V H) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := xToXbar_surjective hVH g
      have hgX : (g' : G) ∈ xOf V H := g'.2
      have hzV : (g' : G) * yV * (g' : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hXN _ hgX) yV).1 hyVV
      have hzW : (g' : G) * yV * (g' : G)⁻¹ ∉ wOf V H := by
        intro hz
        apply hyVW
        have h1 := cxw_wOf_conj (H.inv_mem (xOf_le_H hVH hgX)) hz
        have e1 : (g' : G)⁻¹ * ((g' : G) * yV * (g' : G)⁻¹) * (g' : G)⁻¹⁻¹ = yV := by
          group
        rwa [e1] at h1
      have hcardV : Nat.card (barOf V H V) = 2 := hH.q_two
      have hpi : piBar V H ⟨(g' : G) * yV * (g' : G)⁻¹, hVH hzV⟩ = piBar V H ⟨yV, hVH hyVV⟩ :=
        cxw_piBar_eq hVH hcardV hzV hyVV hzW hyVW
      apply Subtype.ext
      simp only [Subgroup.coe_mul, coe_xToXbar]
      have hconj : piBar V H (Subgroup.inclusion (xOf_le_H hVH) g' *
          ⟨yV, hVH hyVV⟩ * (Subgroup.inclusion (xOf_le_H hVH) g')⁻¹) =
          piBar V H ⟨yV, hVH hyVV⟩ := hpi
      rw [map_mul, map_mul, map_inv] at hconj
      calc piBar V H (Subgroup.inclusion (xOf_le_H hVH) g') *
            piBar V H ⟨yV, hVH hyVV⟩
          = (piBar V H (Subgroup.inclusion (xOf_le_H hVH) g') * piBar V H ⟨yV, hVH hyVV⟩ *
              (piBar V H (Subgroup.inclusion (xOf_le_H hVH) g'))⁻¹) *
              piBar V H (Subgroup.inclusion (xOf_le_H hVH) g') := by group
        _ = piBar V H ⟨yV, hVH hyVV⟩ * piBar V H (Subgroup.inclusion (xOf_le_H hVH) g') := by
          rw [hconj]
    exact hd.noncentral _ hdV hcentre

end CFSG.RankThree.GF2n.Tim79a
