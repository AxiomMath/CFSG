module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Induction
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Bar

variable {G : Type} [Group G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem quotSat_bar_of {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) {S N : Subgroup G}
    (hQN : Q ≤ N) (hNS : N ≤ S) (hSM : S ≤ M) (h : QuotSat S N P) :
    QuotSat (bar M Q S) (bar M Q N) P := by
  obtain ⟨hn, hP'⟩ := h
  let f0 : ↥S →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)
  have hf0 : ∀ s, f0 s ∈ bar M Q S := fun s =>
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion hSM s, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  let f : ↥S →* ↥(bar M Q S) := f0.codRestrict (bar M Q S) hf0
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨s, Subgroup.mem_subgroupOf.mp hs⟩, rfl⟩
  have hker : ∀ s : ↥S, f s ∈ (bar M Q N).subgroupOf (bar M Q S) ↔ (s : G) ∈ N := by
    intro s
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQN (Subgroup.inclusion hSM s)
  have hK : ((bar M Q N).subgroupOf (bar M Q S)).Normal := by
    have : (bar M Q N).subgroupOf (bar M Q S) = (N.subgroupOf S).map f := by
      ext y
      constructor
      · intro hy
        obtain ⟨s, rfl⟩ := hfs y
        exact ⟨s, (hker s).mp hy, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact (hker s).mpr hs
    rw [this]
    exact Subgroup.Normal.map hn f hfs
  let g : ↥S →* ↥(bar M Q S) ⧸ (bar M Q N).subgroupOf (bar M Q S) :=
    (QuotientGroup.mk' _).comp f
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hfs
  have hgk : g.ker = N.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' _) (f s) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hker s]
    rfl
  let e := (QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  exact ⟨hK, hP _ _ e hP'⟩

end Bar

@[expose] def IsSpModel (m q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ Nonempty (X ≃* ↥(StatedSp m K))

theorem IsSpModel.congr {m q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSpModel m q X) : IsSpModel m q Y := by
  obtain ⟨K, f, fin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, f, fin, hK, ⟨e.symm.trans e'⟩⟩

section SpNat

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem SpMNat.quotSat {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SpMNat hc t m) :
    QuotSat (Rt M (LB M Q B) t) (hc.CN t) (IsSpModel m (Nat.card Z)) := by
  obtain ⟨K, fK, finK, hK, φ, hrange, hker, -⟩ := h
  haveI hn : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    rw [← hker]
    exact φ.normal_ker
  refine ⟨hn, K, fK, finK, hK, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)

end SpNat

section Config

variable {X : Type} [Group X]

@[expose] def ConfigSatz (N : Subgroup X) : Prop :=
  StrothHyp (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) ∧
  ∀ B₂ : Subgroup X, Ctx (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂ →
    StrothConclusion (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂

theorem StrothHyp.ne_cen [Finite X] {M₂ Q Z : Subgroup X} (H : StrothHyp M₂ Q Z) : Q ≠ Z := by
  intro hQZ
  apply H.notWC
  have hZQ : Z ≤ Q := by
    rw [H.hZ]
    exact Subgroup.map_subtype_le _
  refine ⟨hZQ, fun g hg => ?_⟩
  rw [hQZ] at hg
  exact Subgroup.eq_of_le_of_card_ge hg (by rw [card_conjSubgroup])

theorem mem_normalizer_cen_of_mem_normalizer [Finite X] (N : Subgroup X) {g : X}
    (hg : g ∈ Subgroup.normalizer (N : Set X)) :
    g ∈ Subgroup.normalizer ((cen N : Subgroup X) : Set X) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' : x ∈ cen N := hx
  rw [cen_eq] at hx' ⊢
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx'
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxN,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set X)).inv_mem hg) y).mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp hxC _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by
        rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by group]
        rw [h1]
    _ = g * x * g⁻¹ * y := by group

end Config

section SubCfg

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem ConfigSatz.of_subConfigSatz {N : Subgroup G} (h : SubConfigSatz M Q Z N) :
    ∃ hN : (Q.subgroupOf (H0 M Z)).Normal, haveI := hN; ConfigSatz (bar (H0 M Z) Q N) := by
  obtain ⟨⟨hN, hS⟩, hN', hall⟩ := h
  exact ⟨hN, hS, hall⟩

theorem bar_centre_le_cen (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t)
    [(Q.subgroupOf (H0 M Z)).Normal] :
    bar (H0 M Z) Q Z0 ≤ cen (bar (H0 M Z) Q (hc.CN t)) := by
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  intro x hx
  rw [cen_eq]
  have hsub : Z0.subgroupOf (H0 M Z) ≤ (hc.CN t).subgroupOf (H0 M Z) := fun a ha => hZN ha
  have hxN : x ∈ bar (H0 M Z) Q (hc.CN t) := Subgroup.map_mono hsub hx
  refine ⟨hxN, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨c, hcc, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  have hzZ : (z : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
  have hcN : (c : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hcc
  exact (step716_mk_mul_comm (a := z) (b := c) (hZ0.comm_mem hzZ (hCNR hcN))).symm

theorem cen_bar_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    [(Q.subgroupOf (H0 M Z)).Normal]
    (hne : cen (bar (H0 M Z) Q (hc.CN t)) ≠ bar (H0 M Z) Q (hc.CN t)) :
    cen (bar (H0 M Z) Q (hc.CN t)) = bar (H0 M Z) Q Z0 := by
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  refine le_antisymm ?_ (bar_centre_le_cen hc hZ0 hZN)
  obtain ⟨A, hQA, hAH, hbarA⟩ := exists_pre (M := H0 M Z) hQH
    (cen (bar (H0 M Z) Q (hc.CN t)))
  have hCN' : cen (bar (H0 M Z) Q (hc.CN t)) ≤ bar (H0 M Z) Q (hc.CN t) := by
    intro x hx
    rw [cen_eq] at hx
    exact (Subgroup.mem_inf.mp hx).1
  have hZ0A : Z0 ≤ A := by
    intro u hu
    have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hZ0H0 hu⟩ ∈ bar (H0 M Z) Q A := by
      rw [hbarA]
      exact bar_centre_le_cen hc hZ0 hZN
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
    exact (mk_mem_bar_iff_sec4 hQA _).mp h1
  have hAN : A ≤ hc.CN t := by
    intro u hu
    have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hAH hu⟩ ∈
        bar (H0 M Z) Q (hc.CN t) :=
      hCN' (hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
    exact (mk_mem_bar_iff_sec4 hQN _).mp h1
  have hRinv : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A := by
    intro r hr
    have hrH : r ∈ H0 M Z := hc.Rt_le_H0 t hr
    have hrN : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hr hx
    have h1 := mk_mem_normalizer_bar_of_normalizer (M := H0 M Z) hQN ⟨r, hrH⟩ hrN
    have h2 := mem_normalizer_cen_of_mem_normalizer _ h1
    rw [← hbarA] at h2
    exact conjSubgroup_eq_self_iff.mpr
      (mem_normalizer_of_mk_mem_normalizer_bar (M := H0 M Z) hQA hAH ⟨r, hrH⟩ h2)
  rcases hirr.2.2.2 A hZ0A hAN hRinv with h | h
  · rw [← hbarA, h]
  · exact absurd (by rw [← hbarA, h]) hne

@[expose] def SecondCfgFalseE
    (E : ∀ (X : Type) [Group X] [Finite X], Subgroup X → Prop)
    (P : ℕ → ∀ (X : Type) [Group X], Prop) (k : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N R : Subgroup X), ConfigSatz N → E X N →
    Width N (cen N) k → N ≤ R → R ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X) →
    QuotSat R N (P (Nat.card (cen N))) →
    (∀ A : Subgroup X, cen N ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) →
      A = cen N ∨ A = N) → False

@[expose] def SecondCfgFalse
    (P : ℕ → ∀ (X : Type) [Group X], Prop) (k : ℕ) : Prop :=
  SecondCfgFalseE (fun _ _ _ _ => True) P k

theorem Ctx.false_of_secondCfg (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {E : ∀ (X : Type) [Group X] [Finite X], Subgroup X → Prop}
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t)
    (hZcard : Nat.card Z0 = Nat.card Q * Nat.card Z)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0) {k : ℕ}
    (hN : Nat.card (hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * k + 1))
    {P : ℕ → ∀ (X : Type) [Group X], Prop}
    (hP : ∀ q (X Y : Type) [Group X] [Group Y], X ≃* Y → P q X → P q Y)
    (hq : QuotSat (Rt M (LB M Q B) t) (hc.CN t) (P (Nat.card Z)))
    (hE : ∀ [(Q.subgroupOf (H0 M Z)).Normal],
      E (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) (bar (H0 M Z) Q (hc.CN t)))
    (hsub : SubConfigSatz M Q Z (hc.CN t)) (hS : SecondCfgFalseE E P k) : False := by
  obtain ⟨⟨hN', H₂⟩, hN'', hall⟩ := hsub
  haveI := hN'
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hCNH0 : hc.CN t ≤ H0 M Z := hCNR.trans hRH0
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans hRH0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hbar := bar_card_mul_card_of_le (M := H0 M Z) hQN hCNH0
  have hbarZ := bar_card_mul_card_of_le (M := H0 M Z) hQZ0 hZ0H0
  have hbarN : Nat.card (bar (H0 M Z) Q (hc.CN t)) = Nat.card Z ^ (2 * k + 1) := by
    rw [hN] at hbar
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [hbar]; ring)
  have hbarZq : Nat.card (bar (H0 M Z) Q Z0) = Nat.card Z := by
    rw [hZcard] at hbarZ
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [hbarZ]; ring)
  have hcen := cen_bar_eq hc ht hZ0 hZN hirr (fun h => H₂.ne_cen h.symm)
  have hcard : Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) = Nat.card Z := by
    rw [hcen]
    exact hbarZq
  refine hS (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) (bar (H0 M Z) Q (hc.CN t))
    (bar (H0 M Z) Q (Rt M (LB M Q B) t)) ⟨H₂, hall⟩ hE ?_ ?_ ?_ ?_ ?_
  · show Nat.card (bar (H0 M Z) Q (hc.CN t)) =
      Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ (2 * k + 1)
    rw [hbarN, hcard]
  · exact Subgroup.map_mono (fun a ha => hCNR ha)
  · intro x hx
    rw [hcen]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have haR : (a : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp ha
    have hzZ : (z : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
    exact (step716_mk_mul_comm (a := z) (b := a) (hZ0.comm_mem hzZ haR))
  · rw [hcard]
    exact quotSat_bar_of (fun X Y _ _ e h => hP _ X Y e h) hQN hCNR hRH0 hq
  · intro A hCA hAN hRinv
    obtain ⟨A', hQA', hA'H, hbarA⟩ := exists_pre (M := H0 M Z) hQH A
    have hZ0A : Z0 ≤ A' := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hZ0H0 hu⟩ ∈ bar (H0 M Z) Q A' := by
        rw [hbarA]
        apply hCA
        rw [hcen]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
      exact (mk_mem_bar_iff_sec4 hQA' _).mp h1
    have hA'N : A' ≤ hc.CN t := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hA'H hu⟩ ∈
          bar (H0 M Z) Q (hc.CN t) :=
        hAN (hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
      exact (mk_mem_bar_iff_sec4 hQN _).mp h1
    have hRinv' : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A' = A' := by
      intro r hr
      have hrH : r ∈ H0 M Z := hRH0 hr
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨r, hrH⟩ ∈
          bar (H0 M Z) Q (Rt M (LB M Q B) t) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
      have h2 := conjSubgroup_eq_self_iff.mp (hRinv _ h1)
      rw [← hbarA] at h2
      exact conjSubgroup_eq_self_iff.mpr
        (mem_normalizer_of_mk_mem_normalizer_bar (M := H0 M Z) hQA' hA'H ⟨r, hrH⟩ h2)
    rcases hirr.2.2.2 A' hZ0A hA'N hRinv' with h | h
    · left
      rw [← hbarA, h, hcen]
    · right
      rw [← hbarA, h]

end SubCfg

section Omega

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsCentrePre.unique {Z0 Z1 R : Subgroup G} (h0 : IsCentrePre Z0 R Q)
    (h1 : IsCentrePre Z1 R Q) : Z1 = Z0 :=
  Subgroup.ext fun x => (h1 x).trans (h0 x).symm

@[expose] def Stroth12Omega6MinusStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → OmegaMinusNat hc t 3 →
    SubConfigSatz M Q Z (hc.CN t) → False

end Omega

end CFSG.RankThree.GF2n.Stroth80
