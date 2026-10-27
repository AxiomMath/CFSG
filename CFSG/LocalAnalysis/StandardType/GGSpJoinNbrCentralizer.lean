module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrInner
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCentralizer
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic CFSG.Open
  CFSG.StandardType.SpJoin

@[expose] def GGSpLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (y : G) (K : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J (m + 1) f y K →
    ∀ X : Subgroup G, (X = L ∨ ∃ y' : G, GGNbr p B x D J y' X ∧
        ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    ∀ φ₀ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ₀ → φ₀.range = X →
      ∃ φ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ ∧ φ.range = X ∧
        (φ.comp (spLeviBlock m (GaloisField 2 f))).range = J

@[expose] def GGSpLeviInputAtL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (y : G) (K : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J (m + 1) f y K →
    ∀ φ₀ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ₀ → φ₀.range = L →
      ∃ φ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ ∧ φ.range = L ∧
        (φ.comp (spLeviBlock m (GaloisField 2 f))).range = J

@[expose] def GGSpLeviInputAtNbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (y : G) (K : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J (m + 1) f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs →
    ∀ φ₀ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ₀ → φ₀.range = K' →
      ∃ φ : StatedSp (m + 1) (GaloisField 2 f) →* G, Function.Injective φ ∧ φ.range = K' ∧
        (φ.comp (spLeviBlock m (GaloisField 2 f))).range = J

section Pieces

variable {G : Type} [Group G] [Finite G]

theorem center_range_statedSp_eq_bot {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (φ : StatedSp n F →* G) (hinj : Function.Injective φ) : Subgroup.center φ.range = ⊥ := by
  have hZsp : Subgroup.center (StatedSp n F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  exact he.symm

theorem ggNbr_inf_centralizer_le_zpowers {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    D ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hx
    apply hnbr.2.2.2
    have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hx
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
    exact bot_le
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hnbr.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
  rintro c ⟨hcD, hcK⟩
  rw [hnbr.2.1] at hcD
  exact mem_zpowers_of_mem_closure_pair hp hxp hxy hyK hxK hcD hcK

end Pieces

theorem ggSpStdSubCentralizer_of_levi (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput)
    (hLevi : GGSpLeviInputAtL) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hpF : (p : GaloisField 2 f) ≠ 0 := natCast_ne_zero_of_two_eq_zero h2 hp2 hp
  obtain ⟨φ₀, hφ₀inj, hφ₀range⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  obtain ⟨φ, hφinj, hφrange, hφlevi⟩ :=
    hLevi G p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN φ₀ hφ₀inj hφ₀range
  have hinner : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by have := hN.2.1; omega) hN.1.1 hInn.1 φ hφinj hφrange
  have hZ : Subgroup.center L = ⊥ := by
    have := center_range_statedSp_eq_bot φ hφinj
    rwa [hφrange] at this
  have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) := hInn.1.le_normalizer
  have hsplit := ggBstar_split_of_inner hBs hZ hnorm hinner
  have hJL : J ≤ L := by
    rw [← hφlevi, MonoidHom.range_comp, ← hφrange]
    exact Subgroup.map_le_range _ _
  have hCLJ : Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.centralizer_le hJL
  set E : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G) with hE
  set EL : Subgroup G := E ⊓ L with hEL
  set EC : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G) with hEC
  have hECcard : Nat.card EC ≤ p := hcfg.card_bstar_centralizer_le
  have hELcard : Nat.card EL ≤ p := by
    let E' : Subgroup (StatedSp (m + 1) (GaloisField 2 f)) := EL.comap φ
    have hELle : EL ≤ φ.range := by
      rw [hφrange]
      exact inf_le_right
    have hE'map : E'.map φ = EL := Subgroup.map_comap_eq_self hELle
    have hcard : Nat.card E' = Nat.card EL := by
      rw [← hE'map]
      exact (Subgroup.card_map_of_injective (K := E') hφinj).symm
    have hELBs : EL ≤ Bs := inf_le_left.trans inf_le_left
    have hE'ab : IsElemAbelian p E' :=
      IsElemAbelian.comap (IsElemAbelian.mono hBs.2.1 hELBs) hφinj
    have hE'le : E' ≤ (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam
        (0 : Fin (m + 1)) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
        StatedSp (m + 1) (GaloisField 2 f)).range := by
      intro e he
      have heEL : φ e ∈ EL := he
      have heC : φ e ∈ Subgroup.centralizer (J : Set G) := heEL.1.2
      have hecent : e ∈ Subgroup.centralizer
          ((spLeviBlock m (GaloisField 2 f)).range : Set (StatedSp (m + 1) (GaloisField 2 f))) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨h, rfl⟩
        have hJmem : φ (spLeviBlock m (GaloisField 2 f) h) ∈ J := by
          rw [← hφlevi]
          exact ⟨h, rfl⟩
        have hcomm := Subgroup.mem_centralizer_iff.mp heC _ hJmem
        apply hφinj
        rw [map_mul, map_mul]
        exact hcomm
      obtain ⟨g, rfl⟩ := exists_lam_zero_of_mem_centralizer_levi hecent
      exact ⟨g, rfl⟩
    rw [← hcard]
    exact card_le_of_isElemAbelian_le_range_lam_zero hp hp2 hpF hE'ab hE'le
  have hEcard : Nat.card E ≤ Nat.card EL * Nat.card EC := by
    have hECE : EC ≤ E := fun c hc => ⟨hc.1, hCLJ hc.2⟩
    let f' : ↥EL × ↥EC → ↥E := fun q => ⟨(q.1 : G) * (q.2 : G), E.mul_mem q.1.2.1 (hECE q.2.2)⟩
    have hsurj : Function.Surjective f' := by
      intro b
      obtain ⟨u, hu, c, hc, hbc⟩ := hsplit b.1 b.2.1
      have huE : u ∈ E := by
        have hcE : c ∈ E := hECE hc
        have : u = b.1 * c⁻¹ := by rw [hbc]; group
        rw [this]
        exact E.mul_mem b.2 (E.inv_mem hcE)
      exact ⟨(⟨u, huE, hu.2⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩
    have := Nat.card_le_card_of_surjective f' hsurj
    rwa [Nat.card_prod] at this
  have hDE : D ≤ E := by
    have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
    intro d hd
    have hd' : d ∈ B ⊓ Subgroup.centralizer (J : Set G) := hDeq ▸ hd
    exact ⟨hBs.1 hd'.1, hd'.2⟩
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hle2 : Nat.card E ≤ Nat.card D := by
    calc Nat.card E ≤ Nat.card EL * Nat.card EC := hEcard
      _ ≤ p * p := Nat.mul_le_mul hELcard hECcard
      _ = Nat.card D := by rw [hDcard, sq]
  exact (Subgroup.eq_of_le_of_card_ge hDE hle2).ge

theorem ggSpNbrCentralizerInput_of_atL (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput)
    (hsub : GGNbrSubcomponentInput) (hLevi : GGSpLeviInputAtL) : GGSpNbrCentralizerInput := by
  intro G _ _ p B Bs x L D J m f y K y' K' hat
  have hcfg := hat.1
  have hnbr := hat.2.2.2.2.2.1
  have hN := hat.2.2.2.2.1
  have h3b := ggSpStdSubCentralizer_of_levi hMp hlift hLevi hcfg hat.2.1 hat.2.2.1 hat.2.2.2.1 hN
  have hJK' : J ≤ K' := hsub G p B x L D J hcfg.1 hcfg.2.2 y' K' hnbr
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  haveI := Fact.mk hp
  have hy : orderOf y' = p := orderOf_eq_prime (hnbr.1.1.1.2 y' hnbr.1.2.1) hnbr.1.2.2.1
  have hle : Bs ⊓ Subgroup.centralizer (K' : Set G) ≤ Subgroup.zpowers y' := by
    rintro c ⟨hcBs, hcK⟩
    have hcD : c ∈ D := h3b ⟨hcBs, Subgroup.centralizer_le hJK' hcK⟩
    exact ggNbr_inf_centralizer_le_zpowers hcfg.1 hnbr ⟨hcD, hcK⟩
  calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G))
      ≤ Nat.card (Subgroup.zpowers y') := Subgroup.card_le_of_le hle
    _ = p := by rw [Nat.card_zpowers, hy]

end CFSG.StandardType
