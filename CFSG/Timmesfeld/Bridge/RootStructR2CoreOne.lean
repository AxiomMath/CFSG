module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManySplit
public import CFSG.Timmesfeld.Bridge.RootStructWTIModStep
public import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS
open scoped Matrix commutatorElement

namespace LineSetting

variable {G : Type*} [Group G] {D : Set G} (hL : LineSetting G D)
include hL

section Line

variable {a d : G}

theorem conj_mem_line_of_mem_sup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) {g : G}
    (hg : g ∈ rootGroup D x ⊔ rootGroup D y) {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) :
    g * t * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have hD := hL.hyp.root
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hyT
  have hle : rootGroup D x ⊔ rootGroup D y ≤
      Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [rootGroup, Subgroup.closure_le]
      intro x' hx'
      exact mem_normalizer_of_mul_self_eq_one (hD.mul_self_eq_one hx'.1) fun t ht =>
        hL.conj_mem_line_of_collinear ha hd had hadD hdT hx hax haxD hxT hx' ht
    · rw [rootGroup, Subgroup.closure_le]
      intro y' hy'
      refine mem_normalizer_of_mul_self_eq_one (hD.mul_self_eq_one hy'.1) fun t ht => ?_
      rw [sup_comm] at ht ⊢
      exact hL.conj_mem_line_of_collinear hd ha had.symm hdaD haT hy hdy hdyD hyT' hy' ht
  exact (Subgroup.mem_normalizer_iff.1 (hle hg) t).1 ht

theorem exists_natural_line (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d)
    {K : Type*} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2]
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφx : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      upperUnipotent K)
    (hφy : ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      lowerUnipotent K) :
    ∃ θ₀ : (Fin 2 → K) → G, IsNaturalModule φ θ₀ ∧
      ∀ t, t ∈ rootGroup D a ⊔ rootGroup D d ↔ ∃ v, θ₀ v = t := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hc := hL.closure
  have hclass := hL.hyp.isClass
  have hTI := hL.lineTI ha hd had hadD hdT
  have hH : QuotMod.Hyp (rootGroup D x ⊔ rootGroup D y) (rootGroup D a ⊔ rootGroup D d) ⊥ :=
    { le := bot_le
      comm := fun n hn n' hn' => by
        rw [Subgroup.mem_bot, (commute_of_mem_sup_rootGroup ha hd had hn hn').eq,
          mul_inv_cancel_right, mul_inv_cancel]
      conj := fun g hg t ht =>
        hL.conj_mem_line_of_mem_sup ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT hg ht
      conj₀ := fun g _ n hn => by
        rw [Subgroup.mem_bot] at hn ⊢
        rw [hn, mul_one, mul_inv_cancel] }
  have := hH.normal
  have hxd4 := hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT
  have hya4 : orderOf (a * y) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line' hD hL.lineCentralizerEq ha hd had hadD hdT hTI hy
      hdy hyT
  have hxA : ∀ x' : ↥(rootGroup D x ⊔ rootGroup D y), φ x' ∈ upperUnipotent K →
      (x' : G) ∈ rootGroup D x :=
    fun x' hx' => (NaturalModule.coe_mem_iff hφx x').2 hx'
  have hyA : ∀ y' : ↥(rootGroup D x ⊔ rootGroup D y), φ y' ∈ lowerUnipotent K →
      (y' : G) ∈ rootGroup D y :=
    fun y' hy' => (NaturalModule.coe_mem_iff hφy y').2 hy'
  have hxX : x ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
  have hyX : y ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self hy))
  obtain ⟨k₀, Nf₀, θ, hNf₀, -, hsup₀, hcard₀, -, -⟩ := QuotMod.exists_isNaturalQuotient hH φ
    (A := rootGroup D a) (B := rootGroup D d) bot_le bot_le le_sup_left le_sup_right rfl
    (fun x' hx' α hα => by
      rw [Subgroup.mem_bot, (commute_of_mem_rootGroup_of_commute' ha (hxA x' hx') hα
        hax.symm).eq, mul_inv_cancel_right, mul_inv_cancel])
    (fun x' hx' δ hδ => by
      rcases (mem_rootGroup_iff_of_rootClosure hD hc hx).1 (hxA x' hx') with h1 | h1
      · rw [h1, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · exact hL.mul_inv_mem_of_collinear ha hd had hadD hdT hx hax haxD hxT h1
          (Subgroup.mem_sup_right hδ))
    ⟨⟨x, hxX⟩, (NaturalModule.coe_mem_iff hφx _).1 (rootSet_subset_rootGroup D x
      (mem_rootSet_self hx)), fun δ hδ h1 => by
      rw [Subgroup.mem_bot] at h1 ⊢
      rcases (mem_rootGroup_iff_of_rootClosure hD hc hd).1 hδ with h2 | h2
      · exact h2
      · exfalso
        have hxδ : Commute x δ := by
          rw [mul_inv_eq_one] at h1
          calc x * δ = x * δ * x⁻¹ * x := by group
            _ = δ * x := by rw [h1]
        have hxd : Commute d x := (h2.2 x hx).1 hxδ.symm
        exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hx)
          hxd4 hxd⟩
    (fun y' hy' δ hδ => by
      rw [Subgroup.mem_bot, (commute_of_mem_rootGroup_of_commute' hd (hyA y' hy') hδ
        hdy.symm).eq, mul_inv_cancel_right, mul_inv_cancel])
    ⟨⟨y, hyX⟩, (NaturalModule.coe_mem_iff hφy _).1 (rootSet_subset_rootGroup D y
      (mem_rootSet_self hy)), fun α hα h1 => by
      rw [Subgroup.mem_bot] at h1 ⊢
      rcases (mem_rootGroup_iff_of_rootClosure hD hc ha).1 hα with h2 | h2
      · exact h2
      · exfalso
        have hyα : Commute y α := by
          rw [mul_inv_eq_one] at h1
          calc y * α = y * α * y⁻¹ * y := by group
            _ = α * y := by rw [h1]
        have hay' : Commute a y := (h2.2 y hy).1 hyα.symm
        exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hy)
          hya4 hay'⟩
  have hqK := hL.card_rootGroup_eq_card_field ha hx φ hφx
  have hcardT : Nat.card ↥(rootGroup D a ⊔ rootGroup D d) = Nat.card K ^ 2 := by
    rw [card_sup_rootGroup hL.hyp hc ha hd had hdT, card_rootGroup_eq hclass hD hc ha hd, hqK,
      sq]
  have hK2 : 2 ≤ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [Subgroup.card_bot, one_mul, hcardT] at hcard₀
  have hk₀ : k₀ = 1 := by
    have := Nat.pow_right_injective hK2 hcard₀
    omega
  subst hk₀
  obtain ⟨-, hq⟩ := hNf₀ 0
  have hNf₀T : Nf₀ 0 ≤ rootGroup D a ⊔ rootGroup D d := by
    rw [← hsup₀]
    exact le_sup_of_le_right (le_iSup Nf₀ 0)
  refine ⟨θ 0, ⟨fun v v' => ?_, fun v v' hvv => ?_, fun g v => ?_⟩, fun t => ⟨fun ht => ?_, ?_⟩⟩
  · have := hq.map_add v v'
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this.symm
  · have hadd : θ 0 v = θ 0 v' * θ 0 (v - v') := by
      have := hq.map_add v' (v - v')
      rw [Subgroup.mem_bot, inv_mul_eq_one, add_sub_cancel] at this
      exact this.symm
    rw [hvv, left_eq_mul] at hadd
    exact sub_eq_zero.1 (hq.eq_zero_of_mem _ (by rw [hadd]; exact Subgroup.one_mem _))
  · have := hq.map_mulVec g v
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this
  · rw [← hsup₀, bot_sup_eq, iSup_unique] at ht
    obtain ⟨v, hv⟩ := hq.exists_eq t ht
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hv
    exact ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    exact hNf₀T (hq.mem v)

end Line

end LineSetting

theorem thinGateCoreOneStep : ThinGateCoreOneStep := by
  intro G _ D q C K a ha d hd had hadD hdT hZ hN
  have := C.hyp.finite
  have hL := RootMany.lineSetting_of_counter C
  have hD := C.hyp.root
  have hc := C.closure
  have hclass := C.hyp.isClass
  have hq4 : 4 ≤ q := by
    rw [← K.card_rootGroup a ha]
    exact four_le_card_rootGroup hclass hD hc C.nontrivial ha
  obtain ⟨L, hL', hLT⟩ := hL.exists_ne_mem_rootLines ha ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨x, hx, hax, haxD, hxTa, rfl⟩ := hL'
  have hxT : x ∉ rootGroup D a ⊔ rootGroup D d := fun h =>
    hLT (hL.sup_rootGroup_eq_of_mem_sup ha hx hd hax hxTa had hadD hdT h)
  have hTI := hL.lineTI ha hd had hadD hdT
  obtain ⟨y, hy, hdy, hdyD, hay⟩ := exists_special_of_not_mem_line C.hyp hc C.special
    hL.lineCentralizerEq ha hd had hadD hdT hTI hx hax haxD hxTa hxT
  have hyT : y ∉ rootGroup D a ⊔ rootGroup D d := fun h =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hy) hay
      (commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) h)
  obtain ⟨e, -, φ, hφx, hφy⟩ :=
    hL.exists_mulEquiv_SL2_line ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  have hKq : Nat.card (GaloisField 2 e) = q := by
    rw [← hL.card_rootGroup_eq_card_field ha hx φ hφx, K.card_rootGroup a ha]
  have hcardT : Nat.card ↥(rootGroup D a ⊔ rootGroup D d) = q ^ 2 := by
    rw [card_sup_rootGroup C.hyp hc ha hd had hdT, K.card_rootGroup a ha, K.card_rootGroup d hd,
      sq]
  have hN₀ : lineN₀ D a d = rootGroup D a ⊔ rootGroup D d :=
    (Subgroup.eq_of_le_of_card_ge (hL.line_le_lineN₀ ha hd had) (by
      rw [show lineN₀ D a d = nCore D a ⊓ nCore D d from rfl, hN, hcardT])).symm
  obtain ⟨θ₀, hθ₀, hθ₀T⟩ :=
    hL.exists_natural_line ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT φ hφx hφy
  obtain ⟨k, Nf, θ, hNf, -, hsup, -, hA, hB⟩ :=
    hL.exists_natural_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT φ hφx hφy
  have hH := hL.quotModHyp ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  have hNfN : ∀ i, Nf i ≤ lineN D a d := fun i => by
    rw [← hsup]
    exact le_sup_of_le_right (le_iSup Nf i)
  have hext : ∀ i, Higman.IsNaturalExtension φ (Nf i) (rootGroup D a ⊔ rootGroup D d) θ₀
      (θ i) := by
    intro i
    obtain ⟨hle, hq⟩ := hNf i
    rw [hN₀] at hle hq
    refine ⟨hle, fun n hn t ht => ?_, fun g hg n hn => ?_, hθ₀, hθ₀T, hq⟩
    · rw [(hL.commute_of_mem_lineN ha hd had hadD hdT (hNfN i hn) ht).eq, mul_inv_cancel_right]
      exact ht
    · obtain ⟨v, hv⟩ := hq.exists_eq n hn
      have h1 := hq.map_mulVec ⟨g, hg⟩ v
      have h2 : g * ((θ i v)⁻¹ * n) * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
        rw [← hN₀]
        exact hH.conj₀ g hg _ (by rw [hN₀]; exact hv)
      have e : g * n * g⁻¹ = θ i ((φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ v) *
          ((θ i ((φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ v))⁻¹ *
            (g * θ i v * g⁻¹)) * (g * ((θ i v)⁻¹ * n) * g⁻¹) := by group
      rw [e]
      exact (Nf i).mul_mem ((Nf i).mul_mem (hq.mem _) (hle h1)) (hle h2)
  have hcomm : ∀ i j, ∀ n ∈ Nf i, ∀ n' ∈ Nf j, ⁅n, n'⁆ ∈ rootGroup D a ⊔ rootGroup D d := by
    intro i j n hn n' hn'
    rw [commutatorElement_def, ← hN₀]
    exact hL.commutator_mem_lineN₀ ha hd had hadD hdT (hNfN i hn) (hNfN j hn')
  obtain ⟨hab, -⟩ := Higman.elementary_of_family (by rw [hKq]; omega) hext hcomm
  have hS_le : (⨆ i, Nf i) ≤ lineN D a d := iSup_le hNfN
  have hsup' : (rootGroup D a ⊔ rootGroup D d) ⊔ ⨆ i, Nf i = lineN D a d := by
    rw [← hN₀]
    exact hsup
  have hSc : ∀ s ∈ ⨆ i, Nf i, ∀ n ∈ lineN D a d, Commute s n := by
    intro s hs n hn
    rw [← hsup'] at hn
    have hle : (rootGroup D a ⊔ rootGroup D d) ⊔ ⨆ i, Nf i ≤ Subgroup.centralizer {s} :=
      sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2
        (hL.commute_of_mem_lineN ha hd had hadD hdT (hS_le hs) ht).eq.symm)
        (fun s' hs' => Subgroup.mem_centralizer_singleton_iff.2 (hab s' hs' s hs).eq)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hn)).symm
  have hNab : ∀ n ∈ lineN D a d, ∀ n' ∈ lineN D a d, Commute n n' := by
    intro n hn n' hn'
    rw [← hsup'] at hn
    have hle : (rootGroup D a ⊔ rootGroup D d) ⊔ ⨆ i, Nf i ≤ Subgroup.centralizer {n'} :=
      sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2
        (hL.commute_of_mem_lineN ha hd had hadD hdT hn' ht).eq.symm)
        (fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hSc s hs n' hn').eq)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hn)
  have hUab : ∀ u ∈ nCore D a ⊓ Subgroup.centralizer {d},
      ∀ u' ∈ nCore D a ⊓ Subgroup.centralizer {d}, Commute u u' := fun u hu u' hu' =>
    hNab u (Subgroup.mem_sup_left hu) u' (Subgroup.mem_sup_left hu')
  have hsub : nCore D a ⊓ Subgroup.centralizer {d} ⊓ Subgroup.centralizer {x} ≤
      rootGroup D a := by
    rintro u ⟨hu, hux⟩
    have hux' : Commute u x := Subgroup.mem_centralizer_singleton_iff.1 hux
    have htr := RootMany.nCore_le_transv C ha hx hax hu.1
    have huA : ∀ x' ∈ rootGroup D x, Commute u x' := by
      intro x' hx'
      have h1 : u * x' * u⁻¹ ∈ rootGroup D x := by
        have := RankOne.conj_mem_map_conj u hx'
        rwa [← rootGroup_conj hclass, hux'.eq, mul_inv_cancel_right] at this
      have h2 := htr.2 x' (Subgroup.mem_sup_right hx')
      have hne : rootSet D a ≠ rootSet D x := fun h' => hxTa (h' ▸ mem_rootSet_self hx)
      have hmem : u * x' * u⁻¹ * x'⁻¹ ∈ rootGroup D a ⊓ rootGroup D x :=
        ⟨h2, (rootGroup D x).mul_mem h1 ((rootGroup D x).inv_mem hx')⟩
      rw [rootGroup_inf_eq_bot_of_rootClosure hD hc ha hx hne, Subgroup.mem_bot,
        mul_inv_eq_one] at hmem
      calc u * x' = u * x' * u⁻¹ * u := by group
        _ = x' * u := by rw [hmem]
    refine hZ u hu.1 fun m hm => ?_
    rw [hL.nCore_eq_rootGroup_sup ha hd had hadD hdT hx hax haxD hxT] at hm
    have hle : rootGroup D x ⊔ (nCore D a ⊓ Subgroup.centralizer {d}) ≤
        Subgroup.centralizer {u} := sup_le (fun x' hx' =>
          Subgroup.mem_centralizer_singleton_iff.2 (huA x' hx').eq.symm)
        (fun u' hu' => Subgroup.mem_centralizer_singleton_iff.2 (hUab u hu u' hu').eq.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm
  have hU := RootMany.card_le_mul_card_inf_of_le ha hx
    (H := nCore D a ⊓ Subgroup.centralizer {d})
    (inf_le_left.trans (RootMany.nCore_le_transv C ha hx hax))
  have hU' := Subgroup.card_le_of_le hsub
  have hcount := hL.card_nCore_inf_eq ha hd had hadD hdT hx hax haxD hxT
  rw [K.ncard_rootLines a ha, show lineN₀ D a d = nCore D a ⊓ nCore D d from rfl, hN,
    Nat.add_sub_cancel] at hcount
  have hUa : Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) = q ^ 2 * q ^ 2 := by
    rw [hA, ← hB, hcount]
  rw [hUa, K.card_rootGroup a ha] at hU
  rw [K.card_rootGroup a ha] at hU'
  have h1 : q ^ 2 * q ^ 2 ≤ q * q := hU.trans (Nat.mul_le_mul_left _ hU')
  have h2 : q ^ 2 * q ^ 2 = (q * q) * (q * q) := by ring
  have h3 : 16 ≤ q * q := Nat.mul_le_mul hq4 hq4
  have h4 : 16 * (q * q) ≤ (q * q) * (q * q) := Nat.mul_le_mul_right _ h3
  rw [h2] at h1
  generalize q * q = m at h1 h3 h4
  generalize m * m = M at h1 h4
  omega

end CFSG.Timmesfeld.Bridge
