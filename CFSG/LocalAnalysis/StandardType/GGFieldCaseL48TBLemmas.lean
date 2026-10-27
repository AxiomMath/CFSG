module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWNormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem ggBstarInnerDiagLInputOn_true_of_cover {S : ℕ → LargeEvenLabel → Prop}
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (h : GGBstarInnerDiagLInputOn S) : GGBstarInnerDiagLInputOn fun _ _ => True := by
  intro G _ _ p B Bs x L D J hC hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  have hL' : GGInnerDiagOnLab S p B L := ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.2.1, hP.2⟩) hraw⟩
  obtain ⟨hperf', lab', hlab', hraw'⟩ := h G p B Bs x L D J hC hL'
  exact ⟨hperf', lab', hlab', largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, trivial, hP.2⟩) hraw'⟩

theorem ggL48NonCyclicInput_of_lNoncyclic (ha₀ : GGLNoncyclicInput) : GGL48NonCyclicInput :=
  fun G _ _ p B _ x L _ _ _ _ _ _ _ _ _ hS => ha₀ G p B x L hS.1.1.1

theorem not_mem_closure_weyl {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hF : GGL48NbrFieldInput) (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hUK : U ⊓ K ≤ U₁) {S : Subgroup G} {W : Set G}
    (hSp : IsPGroup p S)
    (hSC : S ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hSK : S ≤ K)
    (hWN : W ⊆ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) :
    x ∉ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G)) := by
  intro hx
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hcan, hX1, hX2, hX3, hX4, hX5⟩, -, -, -, -, h44, h45, hID, hNU⟩ := id hS
  obtain ⟨hDd, hd1, hNbr, hyd, -⟩ := h44
  obtain ⟨hUC, hUp, hUmax, -⟩ := h45
  have hdD : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hDd]; exact Subgroup.mem_zpowers d
  have hcanK := hcan X hX1 hX2 hX3 hX4 hX5 d hdD hd1 y K hNbr hyd
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hCK : Subgroup.centralizer (B₁ : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    refine hcanK ⟨Subgroup.centralizer_le_normalizer _ hg, ?_⟩
    have hzle : Subgroup.zpowers d ≤ B₁ := by
      rw [Subgroup.zpowers_le]; exact hdD.2
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hzle hg)
  have hU₁K : U₁ ≤ Subgroup.normalizer (K : Set G) := hID.2.1.trans hID.1
  have hmem := GGL48TW.mem_commutator_sup_of_weyl hUC hUp (fun R hRC hRp hUR => hUmax R hRC hRp hUR)
    hNU hCK hU₁K hUK hSp hSC hSK hWN hx
  exact hF G p B Bs x L D J X B₂ d y K U U₁ hS hmem

omit [Finite G] in
theorem ggLAut_of_mem_conj {L : Subgroup G} {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (l : L) (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)) :
    ggLAut L θ ⟨l, hl⟩ = MulAut.conj (θ (l : L ⧸ Subgroup.center L)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [ggLAut_apply, MulAut.conj_apply]
    have h : L.normalizerMonoidHom ⟨l, hl⟩ m = l * m * l⁻¹ :=
      Subtype.ext (by rw [normalizerMonoidHom_coe]; simp)
    rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]

theorem mem_sup_of_comm_mem_centralizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {g : G} (hgH : g ∈ Subgroup.centralizer ({x} : Set G))
    (hg : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    g ∈ (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxp : x ^ p = 1 := hBsp x hxBs
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  have hNB := normalizer_le_normalizer_of_ggFieldCase hS.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H := Subgroup.centralizer ({x} : Set G) with hH
  set F := H ⊓ Subgroup.centralizer (B₁ : Set G) with hF
  set Y := H ⊓ Subgroup.centralizer (L : Set G) with hY
  have hB₁Bs : B₁ ≤ Bs := inf_le_left
  have hB₁H : B₁ ≤ H := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hBcomm b (hB₁Bs hb) x hxBs)
  have hxH : x ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hxY : x ∈ Y := ⟨hxH, mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLx hl)⟩
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, ggNormalizer_le_normalizer_centralizer L (hN hh)⟩
  have hB₁p : IsPGroup p B₁ := fun b => ⟨1, Subtype.ext (by simpa using hBsp _ (hB₁Bs b.2))⟩
  have hcycY : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S := fun S hSY hSp =>
    hcycL S (hSY.trans inf_le_right) hSp
  have hzc : ∀ g ∈ Y, g * x = x * g := fun g hg => mem_centralizer_singleton_iff.mp hg.1
  obtain ⟨w, O, a, hwY, hxw, ha, hBw, hO, hdec⟩ :=
    GGL48TW.Cent.exists_invariant_cyclic_complement hp2 (hB₁H.trans hHY) hB₁p hcycY hxY hx1 hxp hzc
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hTle : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ zpowers x :=
    GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp) (fun t ht => hBsp t ht.1)
      ⟨hxBs, hxY.2⟩ hx1
  have htriv : ∀ c ∈ B₁, c ∈ zpowers w → c = 1 := by
    intro c hcB hcw
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := (zpowers_le.mpr hwY.2) hcw
    exact GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 (hTle ⟨hB₁Bs hcB, hcL⟩) hcB
  have hB₁Y : ∀ c ∈ B₁, c ∈ Y → c = 1 := fun c hc hcY =>
    GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 (hTle ⟨hB₁Bs hc, hcY.2⟩) hc
  have hBw' := GGL48TW.Cent.commute_of_cyclic_invariant hp2 hBsp hBst.2.2.2 h43.2 hNB hx1 hxp hxw
    (fun b hb => hBcomm b (hB₁Bs hb) x hxBs) hBw htriv ha
  have hOY : O ≤ Y := fun g hg => ((hO g).mp hg).1
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := by
    intro h hh
    apply GGL48TW.Cent.mem_normalizer_of_conj_mem
    intro g hg
    obtain ⟨hgY, hgo⟩ := (hO g).mp hg
    refine (hO _).mpr ⟨(mem_normalizer_iff.mp (hHY hh) g).mp hgY, ?_⟩
    have : orderOf (h * g * h⁻¹) = orderOf g := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj h) g
    rwa [this]
  have hwx : w * x = x * w := hzc w hwY
  have hwC : w ∈ Subgroup.centralizer (Bs : Set G) := by
    have hle : Bs ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [h43.2]
      refine sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (hBw' b hb))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwx.symm))
    exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)
  set P := B₁ ⊔ zpowers w with hPdef
  have hPC : P ≤ Subgroup.centralizer (Bs : Set G) :=
    sup_le (fun b hb => mem_centralizer_iff.mpr fun h hh => hBcomm h hh b (hB₁Bs hb))
      (zpowers_le.mpr hwC)
  have hwp : IsPGroup p (zpowers w) := IsPGroup.of_card (by rw [Nat.card_zpowers, ha])
  have hwN : zpowers w ≤ Subgroup.normalizer (B₁ : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr hBw'))
  have hPp : IsPGroup p P := IsPGroup.to_sup_of_normal_left' hB₁p hwp hwN
  have hPH : P ≤ H := sup_le hB₁H (zpowers_le.mpr hwY.1)
  have hPO : P ≤ Subgroup.normalizer (O : Set G) := hPH.trans hHO
  set M := O ⊔ P with hMdef
  have hMset : (M : Set G) = (O : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O P hPO
  have hOnd : ¬ p ∣ Nat.card O := by
    intro hd
    obtain ⟨o, ho⟩ := exists_prime_orderOf_dvd_card' p hd
    have h1 := ((hO o).mp o.2).2
    rw [Subgroup.orderOf_coe, ho] at h1
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd h1 dvd_rfl)
  have hPM : P ≤ M := le_sup_right
  have hOM : O ≤ M := le_sup_left
  have hcardM : Nat.card M = Nat.card P * Nat.card O := by
    apply le_antisymm
    · have h1 : Nat.card ((O : Set G) * (P : Set G)) ≤ Nat.card O * Nat.card P :=
        Set.natCard_mul_le
      rw [← hMset] at h1
      rw [mul_comm]; exact h1
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
      have hcop : Nat.Coprime (Nat.card P) (Nat.card O) := by
        rw [hk]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hOnd)
      exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd
        (Subgroup.card_dvd_of_le hPM) (Subgroup.card_dvd_of_le hOM))
  have hPcard : Nat.card (P.subgroupOf M) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have hPidx : (P.subgroupOf M).index = Nat.card O := by
    have h := (P.subgroupOf M).card_mul_index
    rw [hPcard, hcardM] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hPp' : IsPGroup p (P.subgroupOf M) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  set SP : Sylow p M := hPp'.toSylow (by rw [hPidx]; exact hOnd) with hSP
  set Q := B₁.map (MulAut.conj g).toMonoidHom with hQ
  have hgb : ∀ b ∈ B₁, g * b * g⁻¹ * b⁻¹ ∈ Y := fun b hb =>
    ⟨H.mul_mem (H.mul_mem (H.mul_mem hgH (hB₁H hb)) (H.inv_mem hgH)) (H.inv_mem (hB₁H hb)),
      hg b hb⟩
  have hYM : Y ≤ M := by
    intro t ht
    obtain ⟨o, ho, s, hs, rfl⟩ := hdec t ht
    exact M.mul_mem (hOM ho) (hPM (mem_sup_right hs))
  have hQM : Q ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    have : (MulAut.conj g).toMonoidHom b = (g * b * g⁻¹ * b⁻¹) * b := by
      simp [MulAut.conj_apply]
    rw [this]
    exact M.mul_mem (hYM (hgb b hb)) (hPM (mem_sup_left hb))
  have hQp : IsPGroup p Q := hB₁p.map _
  have hQp' : IsPGroup p (Q.subgroupOf M) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  obtain ⟨SQ, hSQ⟩ := hQp'.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M SP SQ
  have hmO : (m : G) ∈ (O : Set G) * (P : Set G) := by rw [← hMset]; exact m.2
  obtain ⟨o, ho, π, hπ, hoπ⟩ := hmO
  have hoπ : o * π = (m : G) := hoπ
  set g' := o⁻¹ * g with hg'
  have hconjP : ∀ b ∈ B₁, g' * b * g'⁻¹ ∈ P := by
    intro b hb
    have hqM : g * b * g⁻¹ ∈ M := hQM ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have hq : (⟨g * b * g⁻¹, hqM⟩ : M) ∈ ((m • SP : Sylow p M) : Subgroup M) := by
      rw [hm]; exact hSQ ⟨b, hb, by simp [MulAut.conj_apply]⟩
    first
      | rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
      | rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at hq
    have hq' : (m : G)⁻¹ * (g * b * g⁻¹) * m ∈ P := by
      have := hq
      rw [hSP, IsPGroup.toSylow_coe] at this
      simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using this
    rw [← hoπ] at hq'
    have h2 : π * ((π)⁻¹ * (o⁻¹ * (g * b * g⁻¹) * o) * π) * π⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem hπ (by simpa [mul_assoc] using hq')) (P.inv_mem hπ)
    have : g' * b * g'⁻¹ = π * ((π)⁻¹ * (o⁻¹ * (g * b * g⁻¹) * o) * π) * π⁻¹ := by
      rw [hg']; group
    rw [this]; exact h2
  have hoH : o ∈ H := (hOY ho).1
  have hg'H : g' ∈ H := H.mul_mem (H.inv_mem hoH) hgH
  have hg'x : g' * x * g'⁻¹ = x := by
    have := mem_centralizer_singleton_iff.mp hg'H
    rw [show g' * x = x * g' from by first | exact this | exact this.symm]; group
  have hg'Bs : g' ∈ Subgroup.normalizer (Bs : Set G) := by
    apply GGL48TW.Cent.mem_normalizer_of_conj_mem
    have hle : B₁ ⊔ zpowers x ≤ Bs.comap (MulAut.conj g').toMonoidHom := by
      refine sup_le (fun b hb => ?_) (zpowers_le.mpr ?_)
      · show g' * b * g'⁻¹ ∈ Bs
        apply hBst.2.2.2 _ (hPC (hconjP b hb))
        rw [conj_pow, hBsp b (hB₁Bs hb)]; group
      · show g' * x * g'⁻¹ ∈ Bs
        rw [hg'x]; exact hxBs
    intro s hs
    rw [h43.2] at hs
    exact hle hs
  have hg'B₁ := hNB hg'Bs
  have hg'F : g' ∈ F := by
    refine ⟨hg'H, mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hc1 : g' * b * g'⁻¹ * b⁻¹ ∈ B₁ :=
      B₁.mul_mem ((mem_normalizer_iff.mp hg'B₁ b).mp hb) (B₁.inv_mem hb)
    have hboY : b * o * b⁻¹ ∈ Y := (mem_normalizer_iff.mp (hHY (hB₁H hb)) o).mp (hOY ho)
    have hc2 : g' * b * g'⁻¹ * b⁻¹ ∈ Y := by
      have : g' * b * g'⁻¹ * b⁻¹ =
          (o⁻¹ * (g * b * g⁻¹ * b⁻¹) * o) * (o⁻¹ * (b * o * b⁻¹)) := by
        rw [hg']; group
      rw [this]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem (hOY ho)) (hgb b hb)) (hOY ho))
        (Y.mul_mem (Y.inv_mem (hOY ho)) hboY)
    have h1 := hB₁Y _ hc1 hc2
    have : g' * b = b * g' := by
      have h2 : g' * b * g'⁻¹ = b := by
        calc g' * b * g'⁻¹ = (g' * b * g'⁻¹ * b⁻¹) * b := by group
          _ = b := by rw [h1, one_mul]
      calc g' * b = (g' * b * g'⁻¹) * g' := by group
        _ = b * g' := by rw [h2]
    exact this.symm
  have : g = o * g' := by rw [hg']; group
  rw [this]
  exact mul_mem (mem_sup_right (hOY ho)) (mem_sup_left hg'F)

end CFSG.StandardType
