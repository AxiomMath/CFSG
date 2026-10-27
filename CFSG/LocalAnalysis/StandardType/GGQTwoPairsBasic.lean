module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF1 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {Y J : Subgroup G} {b : G}
    (hJ : IsQuasisimple ↥J)
    (hpJ : p ∣ Nat.card J) (hJY : J ≤ Y) (hb : b ∈ Subgroup.normalizer (J : Set G))
    (h : ⁅J, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p Y) :
    b ∈ Subgroup.centralizer (J : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpc : LargeEvenPPrimeCoreOf p Y = CFSG.Open.lBalancePrimeCore p Y := by
    rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map]
    rfl
  have hN : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p Y)) := by
    rw [hpc]
    exact CFSG.ComponentClassification.LBalance.primeCore_coprime p Y
  exact mem_centralizer_of_commutator_le_coprime hp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mpr hJ)
    hpJ hN
    (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJY hj))) hb h

theorem ggF2 {G : Type} [Group G] [Finite G] {p : ℕ} {H X X' : Subgroup G}
    (hX : LargeEvenPComponent p H X)
    (hX' : LargeEvenPComponent p H X') (h : X ≤ X') : X = X' := by
  have hXl : CFSG.Open.lBalanceIsPComponent p H X :=
    ((largeEvenPComponent_iff_lBalance p H X).1 hX).2
  have hX'l : CFSG.Open.lBalanceIsPComponent p H X' :=
    ((largeEvenPComponent_iff_lBalance p H X').1 hX').2
  have hmin' :=
    ((CFSG.ComponentClassification.LBalance.pComponent_iff_minimal_image p H X' hX'.1).1 hX'l).2.2
  have hQle : CFSG.ComponentClassification.LBalance.quotientImage p H X ≤
      CFSG.ComponentClassification.LBalance.quotientImage p H X' :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H h)
  have hQXi : CFSG.Open.IsComponentOf
      (CFSG.ComponentClassification.LBalance.quotientImage p H X) ⊤ :=
    CFSG.ComponentClassification.LBalance.pComponent_image p H X hXl
  have hQX'i : CFSG.Open.IsComponentOf
      (CFSG.ComponentClassification.LBalance.quotientImage p H X') ⊤ :=
    CFSG.ComponentClassification.LBalance.pComponent_image p H X' hX'l
  have hsub : CFSG.Open.IsSubnormal
      ((CFSG.ComponentClassification.LBalance.quotientImage p H X).subgroupOf
        (CFSG.ComponentClassification.LBalance.quotientImage p H X')) ⊤ := by
    have hh := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hQXi.2.1
      (CFSG.ComponentClassification.LBalance.quotientImage p H X')
    rwa [Subgroup.top_subgroupOf] at hh
  have hQeq : CFSG.ComponentClassification.LBalance.quotientImage p H X =
      CFSG.ComponentClassification.LBalance.quotientImage p H X' := by
    rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hQX'i.2.2
        ((CFSG.ComponentClassification.LBalance.quotientImage p H X).subgroupOf
          (CFSG.ComponentClassification.LBalance.quotientImage p H X')) hsub with hcen | htop
    · exfalso
      have hcomm : ⁅CFSG.ComponentClassification.LBalance.quotientImage p H X,
          CFSG.ComponentClassification.LBalance.quotientImage p H X⁆ = ⊥ :=
        commutator_eq_bot_of_subgroupOf_le_center hcen hQle
      exact commutator_ne_bot_of_isQuasisimple hQXi.2.2 hcomm
    · exact le_antisymm hQle ((Subgroup.subgroupOf_eq_top).mp htop)
  exact hmin' X h hXl.1 hQeq

private theorem ggQ2x_conjAut_conj_apply {G : Type} [Group G] {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (t : MulAut ↥Bs) (b : ↥Bs) :
    (((ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) b : ↥Bs) : G) =
      g * (t ⟨g⁻¹ * b * g, ((ggConjAut Bs hg)⁻¹ b).2⟩ : G) * g⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply]
  rfl

private theorem ggQ2x_mem_ggInduced_map_conj {G : Type} [Group G] {Bs X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {t : MulAut ↥Bs} (ht : t ∈ ggInduced X Bs) :
    ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹ ∈
      ggInduced (X.map (MulAut.conj g).toMonoidHom) Bs := by
  obtain ⟨k, hkX, hkN, hk⟩ := ht
  refine ⟨g * k * g⁻¹, ⟨k, hkX, rfl⟩, ?_, fun b => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hkN) (Subgroup.inv_mem _ hg)
  · rw [ggQ2x_conjAut_conj_apply hg, hk]
    simp only
    group

theorem ggStdPair_conj {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {w g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (h : GGStdPair p Bs w X) :
    GGStdPair p Bs (g * w * g⁻¹) (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h.1
    rw [map_conj_eq_of_mem_normalizer hg] at hm
    simpa [MulAut.conj_apply] using hm
  · intro h1
    have h2 : g⁻¹ * (g * w * g⁻¹) * g = g⁻¹ * 1 * g :=
      congrArg (fun z => g⁻¹ * z * g) h1
    have h3 : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    have h4 : g⁻¹ * 1 * g = 1 := by group
    exact h.2.1 (by rwa [h3, h4] at h2)
  · rw [← CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g w]
    exact largeEvenPComponent_map_conj' h.2.2.1 g
  · intro b hb
    rw [mem_normalizer_iff_map_conj]
    have hbg : g⁻¹ * b * g ∈ Bs := by
      have hm := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb
      rw [map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hg)] at hm
      simpa [MulAut.conj_apply] using hm
    rw [map_conj_map_conj]
    rw [show b * g = g * (g⁻¹ * b * g) by group, ← map_conj_map_conj,
      map_conj_eq_of_mem_normalizer (h.2.2.2.1 hbg)]
  · intro b hb
    have hbg : g⁻¹ * b * g ∈ Bs := by
      have hm := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb
      rw [map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hg)] at hm
      simpa [MulAut.conj_apply] using hm
    have hb' := h.2.2.2.2.1 (g⁻¹ * b * g) hbg
    have heq : (⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) =
        (⁅X, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G).map
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      congr 1
      congr 1
      simp [MulAut.conj_apply]
      group
    have hcomm : (⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) ↔
        (⁅X, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p X := by
      rw [heq, largeEvenPPrimeCoreOf_map_conj]
      exact map_conj_le_map_conj_iff g
    rw [hcomm, hb']
    constructor
    · intro hmem
      have hthis := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at hthis
      have h1 : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := rfl
      have h2 : (MulAut.conj g).toMonoidHom (g⁻¹ * b * g) = b := by
        show g * (g⁻¹ * b * g) * g⁻¹ = b
        group
      rwa [h1, h2] at hthis
    · intro hmem
      have hthis := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at hthis
      have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * w * g⁻¹) = w := by
        show g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w
        group
      have h2 : (MulAut.conj g⁻¹).toMonoidHom b = g⁻¹ * b * g := by
        show g⁻¹ * b * (g⁻¹)⁻¹ = g⁻¹ * b * g
        rw [inv_inv]
      rwa [h1, h2] at hthis
  · obtain ⟨⟨φ, hφmem⟩, hφne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.2.2.2.2.2
    have hclos : ∀ ψ ∈ ggAutomizer X Bs,
        ggConjAut Bs hg * ψ * (ggConjAut Bs hg)⁻¹ ∈
          ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs := by
      intro ψ hψ
      have hmap := Subgroup.mem_map_of_mem
        (MulAut.conj (ggConjAut Bs hg)).toMonoidHom hψ
      have hle : (ggAutomizer X Bs).map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom ≤
          ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs := by
        rw [ggAutomizer_eq X Bs, ggAutomizer_eq (X.map (MulAut.conj g).toMonoidHom) Bs]
        rintro _ ⟨t, ht, rfl⟩
        exact ggQ2x_mem_ggInduced_map_conj hg ht
      simpa [MulAut.conj_apply] using hle hmap
    have hmem := hclos φ hφmem
    have hne : ggConjAut Bs hg * φ * (ggConjAut Bs hg)⁻¹ ≠ 1 := by
      intro h1
      apply hφne
      apply Subtype.ext
      have h2 := congrArg (fun ψ => (ggConjAut Bs hg)⁻¹ * ψ * ggConjAut Bs hg) h1
      have h3 : (ggConjAut Bs hg)⁻¹ * (ggConjAut Bs hg * φ * (ggConjAut Bs hg)⁻¹) *
          ggConjAut Bs hg = φ := by group
      have h4 : (ggConjAut Bs hg)⁻¹ * 1 * ggConjAut Bs hg = 1 := by group
      rwa [h3, h4] at h2
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨_, hmem⟩, fun h => hne (congrArg Subtype.val h)⟩

end CFSG.StandardType

end
