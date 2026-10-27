module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_conj_mem_sup {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {g : G} (hgH : g ∈ Subgroup.centralizer ({x} : Set G))
    (hg : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      g * b * g⁻¹ ∈ Bs ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G))) :
    ∃ o ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G),
      o⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) := by
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
  have hYM : Y ≤ M := by
    intro t ht
    obtain ⟨o, ho, s, hs, rfl⟩ := hdec t ht
    exact M.mul_mem (hOM ho) (hPM (mem_sup_right hs))
  have hBsM : Bs ≤ M := by
    intro s hs
    rw [h43.2] at hs
    exact (sup_le ((le_sup_left : B₁ ≤ P).trans hPM)
      (zpowers_le.mpr (hPM (mem_sup_right hxw)))) hs
  have hQM : Q ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    have : (MulAut.conj g).toMonoidHom b = g * b * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [this]
    exact (sup_le hBsM hYM) (hg b hb)
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
  exact ⟨o, hOY ho, hg'Bs⟩

@[expose] noncomputable def ggLAutImage {M : Type} [Group M] (L' : Subgroup M) {R : Type} [Group R]
    (θ : L' ⧸ Subgroup.center L' ≃* R) (S : Subgroup M) : Subgroup (MulAut R) :=
  (S.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ)

omit [Finite G] in
theorem ggLAut_mem_normalizer_image {L : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {S : Subgroup G} (g : Subgroup.normalizer (L : Set G))
    (hg : (g : G) ∈ Subgroup.normalizer (S : Set G)) :
    ggLAut L θ g ∈ Subgroup.normalizer (ggLAutImage L θ S : Set (MulAut R)) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨g * s * g⁻¹, (mem_normalizer_iff.mp hg s).mp hs, ?_⟩
    simp only [map_mul, map_inv]
  · rintro ⟨s, hs, hseq⟩
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hg) (s : G)).mp hs
      rw [inv_inv] at this
      exact this
    · rw [map_mul, map_mul, map_inv, hseq]; group

@[expose] def GGIrredModTableB (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    ∀ S : Subgroup M, E ⊓ Subgroup.centralizer (L' : Set M) ≤ S → S ≤ E →
      (∀ n ∈ L' ⊓ Subgroup.normalizer (E : Set M), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = E ⊓ Subgroup.centralizer (L' : Set M) ∨ S = E

@[expose] def GGWPlusTableB (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) →
    ∀ (A M₁ E₁ : Subgroup (MulAut R)) (h : MulAut R),
      (MulAut.conj : R →* MulAut R).range ⊓
          Subgroup.normalizer (ggLAutImage L' θ E : Set (MulAut R)) ≤ A →
      A ≤ Subgroup.normalizer (ggLAutImage L' θ E : Set (MulAut R)) →
      (∀ a ∈ A, (∃ k : ℕ, a ^ p ^ k = 1) → a ∈ (MulAut.conj : R →* MulAut R).range ⊔
        Subgroup.centralizer (ggLAutImage L' θ E : Set (MulAut R))) →
      M₁ ≤ E₁ → E₁ ≤ A →
      A ⊓ Subgroup.centralizer (ggLAutImage L' θ E : Set (MulAut R)) ≤ M₁ →
      A ≤ Subgroup.normalizer (M₁ : Set (MulAut R)) →
      A ≤ Subgroup.normalizer (E₁ : Set (MulAut R)) →
      (∀ e ∈ E₁, ∃ k : ℕ, e ^ p ^ k ∈ M₁) → h ∈ A → (orderOf h).Coprime p →
      A ≤ E₁ ⊔ Subgroup.zpowers h → E₁ ≤ M₁

theorem homocyclic_of_irredModTableB (hF : GGL48NbrFieldInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hKG : GGIrredModTableB p R I) : GGL48Homocyclic p U₁ := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = zpowers x :=
    le_antisymm (GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1) (zpowers_le.mpr ⟨hxBs, hxC⟩)
  have hirr := hKG G L Bs θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3)
  have h1 := ggL48AutomizerFirst_of_nbrField hF hS h46
  refine ggL48Homocyclic_of_irreducible hp.one_lt h46.1 (A := ggL48H0 x U₁) inf_le_right
    h46.2.2.2.1 ?_
  intro M hMB hM1 hMA
  set S := M ⊔ zpowers x with hSdef
  have hMx : zpowers x ≤ Subgroup.normalizer (M : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun m hm => hBcomm m (hMB hm).1 x hxBs))
  have hSBs : S ≤ Bs := sup_le (hMB.trans inf_le_left) (zpowers_le.mpr hxBs)
  have hNS : ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G) ≤
      Subgroup.normalizer (S : Set G) := by
    apply sup_le
    · intro a ha
      apply Subgroup.inf_normalizer_le_normalizer_sup M (zpowers x)
      exact ⟨GGL48TW.Cent.mem_normalizer_of_conj_mem (hMA a ha),
        Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          have hxa : Commute x a := by
            have := mem_centralizer_singleton_iff.mp ha.1
            first | exact this | exact this.symm
          exact (Commute.zpow_left hxa k).eq)⟩
    · intro c hc
      apply GGL48TW.Cent.mem_normalizer_of_conj_mem
      intro s hs
      have := (mem_centralizer_iff.mp hc) s (hSBs hs)
      rw [← this]; simpa using hs
  have hSN : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    intro n hn s hs
    exact (mem_normalizer_iff.mp (hNS (h1 ⟨hLx hn.1, hn.2⟩)) s).mp hs
  rw [hCx] at hirr
  rcases hirr S le_sup_right hSBs hSN with h | h
  · exfalso
    apply hM1
    rw [eq_bot_iff]
    intro m hm
    have hmx : m ∈ zpowers x := h ▸ (le_sup_left : M ≤ S) hm
    exact Subgroup.mem_bot.mpr (GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hmx (hMB hm))
  · apply Subgroup.eq_of_le_of_card_ge hMB
    have h2 : Nat.card ((M : Set G) * (zpowers x : Set G)) ≤ Nat.card M * Nat.card (zpowers x) :=
      Set.natCard_mul_le
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M (zpowers x) hMx, ← hSdef, h,
      Nat.card_zpowers, hxo] at h2
    change Nat.card Bs ≤ _ at h2
    rw [card_bstar_eq hS] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos

theorem mem_centralizer_of_ggLAut_mem {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (a : Subgroup.normalizer (L : Set G))
    (ha : (a : G) ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G))
    (hac : ggLAut L θ a ∈ Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R))) :
    (a : G) ∈ Subgroup.centralizer (Bs : Set G) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have h43 := hS.2.2.1
  have hNB := normalizer_le_normalizer_of_ggFieldCase hS.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ zpowers x :=
    GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1
  have hB₁ab : ∀ b ∈ B₁, b * (a : G) = (a : G) * b := by
    intro b hb
    set bN : Subgroup.normalizer (L : Set G) := ⟨b, hBsN hb.1⟩ with hbN
    have hbE : ggLAut L θ bN ∈ ggLAutImage L θ Bs := ⟨bN, hb.1, rfl⟩
    have hcomm := (mem_centralizer_iff.mp hac) _ hbE
    have h1 : ggLAut L θ (a * bN * a⁻¹ * bN⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]; group
    have hcL := mem_centralizer_of_ggLAut_eq_one L θ hL h1
    have hcB : (a : G) * b * (a : G)⁻¹ * b⁻¹ ∈ B₁ :=
      B₁.mul_mem ((mem_normalizer_iff.mp (hNB ha.2) b).mp hb) (B₁.inv_mem hb)
    have hcx : (a : G) * b * (a : G)⁻¹ * b⁻¹ ∈ zpowers x :=
      hCx ⟨hcB.1, by simpa [hbN] using hcL⟩
    have hc1 := GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hcx hcB
    have h2 : (a : G) * b * (a : G)⁻¹ = b := mul_inv_eq_one.mp hc1
    calc b * (a : G) = ((a : G) * b * (a : G)⁻¹) * a := by rw [h2]
      _ = (a : G) * b := by group
  have hle : Bs ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro s hs
    rw [h43.2] at hs
    refine (sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (hB₁ab b hb))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))) hs
    have := mem_centralizer_singleton_iff.mp ha.1
    first | exact this | exact this.symm
  exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)

theorem automizerMeta_at_of_tableB {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hZ : ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G))
    (hKGp : GGCoverPTableB p R I) (hKGw : GGWPlusTableB p R I) :
    GGL48AutomizerMetaAt p Bs x := by
  intro Mc Ec h hME hEA hCM hAM hAE hEp hh hhp hAEh
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hBst := hS.1.1.2.1
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsH : ∀ b ∈ Bs, b ∈ Subgroup.centralizer ({x} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hBcomm b hb x hxBs)
  set A := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) with hA
  have hpos := tableBPosition_of_setup hS θ hL hBsN h3
  have hhN : h ∈ Subgroup.normalizer (L : Set G) := hN hh.1
  have hX : (MulAut.conj : R →* MulAut R).range ⊓
      Subgroup.normalizer (ggLAutImage L θ Bs : Set (MulAut R)) ≤ ggLAutImage L θ A := by
    rintro ξ ⟨⟨r, hr⟩, hξN⟩
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    have hℓH : (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) := hLx ℓ.2
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (L : Set G) := hN hℓH
    have hφℓ : ggLAut L θ ⟨ℓ, hℓN⟩ = ξ := by rw [ggLAut_of_mem_conj θ ℓ hℓN]; exact hr
    have hconj : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), (ℓ : G) * b * (ℓ : G)⁻¹ ∈
        Bs ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)) := by
      intro b hb
      set bN : Subgroup.normalizer (L : Set G) := ⟨b, hBsN hb.1⟩ with hbN
      have hbE : ggLAut L θ bN ∈ ggLAutImage L θ Bs := ⟨bN, hb.1, rfl⟩
      obtain ⟨b', hb', hb'eq⟩ := (mem_normalizer_iff.mp hξN _).mp hbE
      have h2 : ggLAut L θ (b'⁻¹ * (⟨ℓ, hℓN⟩ * bN * (⟨ℓ, hℓN⟩ : Subgroup.normalizer (L : Set G))⁻¹))
          = 1 := by
        rw [map_mul, map_inv, hb'eq, map_mul, map_mul, map_inv, hφℓ]; group
      have hcL := mem_centralizer_of_ggLAut_eq_one L θ hL h2
      have hb'G : (b' : G) ∈ Bs := hb'
      have hc : (b' : G)⁻¹ * ((ℓ : G) * b * (ℓ : G)⁻¹) ∈
          Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨?_, by simpa [hbN] using hcL⟩
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBsH _ hb'G))
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ hℓH (hBsH b hb.1)) (Subgroup.inv_mem _ hℓH))
      have : (ℓ : G) * b * (ℓ : G)⁻¹ = (b' : G) * ((b' : G)⁻¹ * ((ℓ : G) * b * (ℓ : G)⁻¹)) := by
        group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left hb'G) (mem_sup_right hc)
    obtain ⟨o, hoY, hoN⟩ := exists_mem_normalizer_of_conj_mem_sup hS hN hℓH hconj
    have hoN' : o ∈ Subgroup.normalizer (L : Set G) := hN hoY.1
    have hoℓH : o⁻¹ * (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      mul_mem (inv_mem hoY.1) hℓH
    refine ⟨⟨o⁻¹ * ℓ, hN hoℓH⟩, ⟨hoℓH, hoN⟩, ?_⟩
    have he : (⟨o⁻¹ * ℓ, hN hoℓH⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨o, hoN'⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨ℓ, hℓN⟩ := rfl
    rw [he, map_mul, map_inv,
      ggLAut_eq_one_of_mem_centralizer L θ (g := ⟨o, hoN'⟩) hoY.2, inv_one, one_mul, hφℓ]
  have hAN : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a haA.2
  have hpel : ∀ a ∈ ggLAutImage L θ A, (∃ k : ℕ, a ^ p ^ k = 1) →
      a ∈ (MulAut.conj : R →* MulAut R).range ⊔
        Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
    rintro a - ⟨k, hk⟩
    obtain ⟨ρ, hρ⟩ := hKGp G L Bs θ hBsN hpos a ⟨k, hk⟩
    have hcC : (MulAut.conj ρ)⁻¹ * a ∈
        Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      exact (hρ ⟨b, hb⟩).eq.symm
    have : a = MulAut.conj ρ * ((MulAut.conj ρ)⁻¹ * a) := by group
    rw [this]
    exact mul_mem (mem_sup_left ⟨ρ, rfl⟩) (mem_sup_right hcC)
  have hMÊ : ggLAutImage L θ Mc ≤ ggLAutImage L θ Ec := by
    rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hME hm, rfl⟩
  have hÊÂ : ggLAutImage L θ Ec ≤ ggLAutImage L θ A := by
    rintro _ ⟨e, he, rfl⟩; exact ⟨e, hEA he, rfl⟩
  have hCM' : ggLAutImage L θ A ⊓ Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) ≤
      ggLAutImage L θ Mc := by
    rintro _ ⟨⟨a, haA, rfl⟩, hac⟩
    exact ⟨a, hCM ⟨haA, mem_centralizer_of_ggLAut_mem hS θ hL hBsN a haA hac⟩, rfl⟩
  have hÂM : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Mc : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a (hAM haA)
  have hÂE : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Ec : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a (hAE haA)
  have hEp' : ∀ e ∈ ggLAutImage L θ Ec, ∃ k : ℕ, e ^ p ^ k ∈ ggLAutImage L θ Mc := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨k, hk⟩ := hEp e he
    refine ⟨k, e ^ p ^ k, ?_, map_pow _ _ _⟩
    show ((e ^ p ^ k : Subgroup.normalizer (L : Set G)) : G) ∈ Mc
    rw [SubgroupClass.coe_pow]; exact hk
  have hcop : (orderOf (ggLAut L θ ⟨h, hhN⟩)).Coprime p := by
    have h1 : orderOf (ggLAut L θ ⟨h, hhN⟩) ∣ orderOf h := by
      have := orderOf_map_dvd (ggLAut L θ) (⟨h, hhN⟩ : Subgroup.normalizer (L : Set G))
      rwa [← Subgroup.orderOf_coe] at this
    exact Nat.Coprime.coprime_dvd_left h1 hhp
  have hÂEh : ggLAutImage L θ A ≤ ggLAutImage L θ Ec ⊔ zpowers (ggLAut L θ ⟨h, hhN⟩) := by
    rintro _ ⟨a, haA, rfl⟩
    have hhE : zpowers h ≤ Subgroup.normalizer (Ec : Set G) := zpowers_le.mpr (hAE hh)
    have ha' : (a : G) ∈ (Ec : Set G) * (zpowers h : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Ec (zpowers h) hhE]; exact hAEh haA
    obtain ⟨e, he, t, ht, het⟩ := ha'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    have heN : e ∈ Subgroup.normalizer (L : Set G) := hN (hEA he).1
    have : a = (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) * (⟨h, hhN⟩ ^ j) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      exact het.symm
    rw [this, map_mul, map_zpow]
    exact mul_mem (mem_sup_left ⟨⟨e, heN⟩, he, rfl⟩) (mem_sup_right (zpow_mem (mem_zpowers _) j))
  have key := hKGw G L Bs θ hBsN hpos hZ (ggLAutImage L θ A) (ggLAutImage L θ Mc)
    (ggLAutImage L θ Ec) (ggLAut L θ ⟨h, hhN⟩) hX hAN hpel hMÊ hÊÂ hCM' hÂM hÂE hEp'
    ⟨⟨h, hhN⟩, hh, rfl⟩ hcop hÂEh
  intro e he
  have heN : e ∈ Subgroup.normalizer (L : Set G) := hN (hEA he).1
  obtain ⟨m, hm, hme⟩ := key ⟨⟨e, heN⟩, he, rfl⟩
  have hmA : (m : G) ∈ A := hEA (hME hm)
  set a : Subgroup.normalizer (L : Set G) := m⁻¹ * ⟨e, heN⟩ with ha
  have haA : (a : G) ∈ A := mul_mem (inv_mem hmA) (hEA he)
  have ha1 : ggLAut L θ a = 1 := by rw [ha, map_mul, map_inv, hme, inv_mul_cancel]
  have haC := mem_centralizer_of_ggLAut_mem hS θ hL hBsN a haA (by rw [ha1]; exact one_mem _)
  have haM : (a : G) ∈ Mc := hCM ⟨haA, haC⟩
  have : e = (m : G) * a := by
    show e = (m : G) * ((m : G)⁻¹ * e); group
  rw [this]
  exact mul_mem hm haM

end CFSG.StandardType
