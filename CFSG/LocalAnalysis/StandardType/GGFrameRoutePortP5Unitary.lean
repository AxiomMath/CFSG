module

public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortOmegaTransfer
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5StdSub
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryDetect
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryLift
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryMark

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

section Setup

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x z : G} {L : Subgroup G}
variable {K : Type} [Field K] {d : ℕ}
variable {φ : ↥(LargeEvenSUGroup (Fin d) K 2) →* ↥L}
variable {ζ : Kˣ} {w : G → Fin d → ZMod 3}
variable {I : Finset (Fin d)} {t : ZMod 3} {r : ℕ}

private theorem center_eq_bot_largeEvenProj_suBlock (hK : Nat.card K = 4)
    (h5 : 5 ≤ I.card) (hId : I.card < d) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)) = ⊥ := by
  let R := LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hsimple : IsSimpleGroup R := by
    change IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU d 2 K))
    exact @CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K _ hfin 2 1 _
      (by rw [hK]; norm_num) d (by omega) (by
        rintro ⟨h1, -⟩
        omega)
  have hquasi : CFSG.IsQuasisimple ↥(suBlock hK I) :=
    isQuasisimple_suBlock (hK := hK) (by omega) hId
  have hnc : ¬ IsMulCommutative ↥(suBlock hK I) := by
    intro hc
    obtain ⟨a, b, hab⟩ := hquasi.2.2
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, isMulCommutative_iff.mp hc u v]
  have hRnc : ¬ IsMulCommutative R := by
    intro hc
    refine hnc (IsMulCommutative.of_comm fun a b => Subtype.ext ?_)
    exact isMulCommutative_iff.mp hc a.1 b.1
  exact @TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative R _ hsimple hRnc

omit [Finite G] in
private theorem exists_psi_of_unitaryCover (hφ : Function.Surjective φ)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)}
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s)
    (hζ : orderOf ζ = 3)
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(LargeEvenSUGroup (Fin d) K 2),
      (s' : GL (Fin d) K) = TauCeti.diagGL (fun i => ζ ^ (w b i).val) * s *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹ →
        ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) :
    ∃ ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)),
      (∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ψ b)) ∧
      ∀ b ∈ Bs, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
        (fun h h' => (h' : GL (Fin d) K) =
          TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
            (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) (ψ b) := by
  classical
  let R := LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)
  have hthree : ∀ b : G, ∀ i : Fin d, (ζ ^ (w b i).val) ^ (2 + 1) = 1 := by
    intro b i
    rw [show (2 + 1 : ℕ) = 3 by norm_num, ← pow_mul, mul_comm, pow_mul,
      show ζ ^ 3 = 1 from by simpa [hζ] using pow_orderOf_eq_one ζ, one_pow]
  have hex : ∀ b : G, ∃ ψ : MulAut R,
      (b ∈ Bs → LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) ∧
      (b ∈ Bs → LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
        (fun h h' => (h' : GL (Fin d) K) =
          TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
            (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) ψ) := by
    intro b
    by_cases hb : b ∈ Bs
    · obtain ⟨ψ, h1, h2⟩ := exists_mulAut_of_diagConj hφ hθ
        (e := fun i => ζ ^ (w b i).val) (fun i => hthree b i) (hw b hb)
      exact ⟨ψ, fun _ => h1, fun _ => h2⟩
    · exact ⟨1, fun h => absurd h hb, fun h => absurd h hb⟩
  choose ψ hψ using hex
  exact ⟨ψ, fun b hb => (hψ b).1 hb, fun b hb => (hψ b).2 hb⟩

omit [Finite G] in
private theorem mem_inf_centralizer_coverComponent_iff (hK : Nat.card K = 4)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h5 : 5 ≤ I.card) (hId : I.card < d)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))
    (ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    (hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ψ b)) :
    ∀ b, b ∈ Bs ⊓ Subgroup.centralizer (coverComponent θ (suBlock hK I) : Set G) ↔
      b ∈ Bs ∧ ∀ j ∈ suBlock hK I, ψ b j = j := by
  intro b
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hb, hc⟩
    obtain ⟨hperf, -⟩ := isQuasisimple_suBlock (hK := hK) (by omega) hId
    exact ⟨hb, (mem_centralizer_coverComponent_iff θ hperf (hN hb) (hψ b hb)).mp hc⟩
  · rintro ⟨hb, hfix⟩
    obtain ⟨hperf, -⟩ := isQuasisimple_suBlock (hK := hK) (by omega) hId
    exact ⟨hb, (mem_centralizer_coverComponent_iff θ hperf (hN hb) (hψ b hb)).mpr hfix⟩

omit [Finite G] in
private theorem inf_centralizer_eq_closure (hK : Nat.card K = 4) (hζ : orderOf ζ = 3)
    (hBBs : B ≤ Bs) (F : Subgroup G)
    (ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    (hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ suBlock hK I, (ψ b) j = j)
    (hψG : ∀ b ∈ Bs, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) (ψ b))
    (hBF : ∀ b ∈ B, (∀ i ∈ I, ∀ j ∈ I, w b i = w b j) ↔ b ∈ Subgroup.closure {x, z})
    (hDB : Subgroup.closure {x, z} ≤ B) :
    B ⊓ F = Subgroup.closure {x, z} := by
  classical
  ext b
  rw [Subgroup.mem_inf, hF b]
  by_cases hb : b ∈ Bs
  · rw [forall_mem_suBlock_apply_eq_iff (hK := hK) (hζ := hζ) (I := I) (w := w b)
      (ψ := ψ b) (hψG b hb)]
    simp only [hb, true_and]
    constructor
    · rintro ⟨hbB, hw⟩
      exact (hBF b hbB).1 hw
    · intro hD
      exact ⟨hDB hD, (hBF b (hDB hD)).2 hD⟩
  · constructor
    · rintro ⟨-, ⟨hb', -⟩⟩
      exact absurd hb' hb
    · intro hD
      exact absurd (hBBs (hDB hD)) hb

omit [Finite G] in
private theorem exists_unitaryBlock_data (hK : Nat.card K = 4) (hζ : orderOf ζ = 3)
    (hI : ∀ i, i ∈ I ↔ w z i = t) (h5 : 5 ≤ I.card) (hId : I.card < d)
    (hdI : d ≤ I.card + 2) (hDB : Subgroup.closure {x, z} ≤ B) (hBs : GGBstar 3 B Bs)
    (ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    (hψG : ∀ b ∈ Bs, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) (ψ b)) :
    z ∈ Bs ∧ CFSG.IsQuasisimple ↥(suBlock hK I) ∧
      suBlock hK I ≤ TauCeti.fixedSubgroup (ψ z).toMonoidHom ∧
      ((suBlock hK I).subgroupOf (TauCeti.fixedSubgroup (ψ z).toMonoidHom)).Normal ∧
      25920 < Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) ∧
      LargeEvenMarking ↥(suBlock hK I)
        (fun lab _ _ _ _ _ => lab = (⟨.twA, I.card - 1, 1⟩ : LargeEvenLabel)) := by
  have hzB : z ∈ B := hDB (Subgroup.subset_closure (by simp))
  have hzBs : z ∈ Bs := hBs.1 hzB
  have hJq : CFSG.IsQuasisimple ↥(suBlock hK I) :=
    isQuasisimple_suBlock (hK := hK) (by omega) hId
  have hfix : suBlock hK I ≤ TauCeti.fixedSubgroup (ψ z).toMonoidHom :=
    suBlock_le_fixedSubgroup (hK := hK) (hζ := hζ) (hI := hI) (φ := ψ z)
      (hφ := hψG z hzBs)
  have hlt : d < 2 * I.card := by omega
  have hnorm : ((suBlock hK I).subgroupOf (TauCeti.fixedSubgroup (ψ z).toMonoidHom)).Normal :=
    suBlock_subgroupOf_normal (hK := hK) (hζ := hζ) (hI := hI) (hd := hlt)
      (φ := ψ z) (hφ := hψG z hzBs)
  have hbig : 25920 < Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) :=
    lt_card_centerQuot_suBlock (hK := hK) h5 hId
  have hmark : LargeEvenMarking ↥(suBlock hK I)
      (fun lab _ _ _ _ _ => lab = (⟨.twA, I.card - 1, 1⟩ : LargeEvenLabel)) :=
    largeEvenMarking_suBlock (hK := hK) (m := I.card - 1) (by omega) (by omega) hId
  exact ⟨hzBs, hJq, hfix, hnorm, hbig, hmark⟩

omit [Finite G] in
private theorem coverComponent_suBlock_props (hK : Nat.card K = 4)
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s) (h5 : 5 ≤ I.card)
    (hId : I.card < d) :
    Nonempty (↥(coverComponent θ (suBlock hK I)) ≃* unitarySU 2 1 K I.card) ∧
      3 ∣ Nat.card (coverComponent θ (suBlock hK I)) := by
  have hJq : CFSG.IsQuasisimple ↥(suBlock hK I) :=
    isQuasisimple_suBlock (hK := hK) (by omega) hId
  constructor
  · exact nonempty_coverComponent_suBlock_mulEquiv hK hker hθ (by omega) hId
  · obtain ⟨e⟩ := nonempty_centerQuot_coverComponent θ hJq
    have hcard : Nat.card (↥(coverComponent θ (suBlock hK I)) ⧸
        Subgroup.center ↥(coverComponent θ (suBlock hK I))) =
        Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) :=
      Nat.card_congr e.toEquiv
    have h3q : 3 ∣ Nat.card (↥(coverComponent θ (suBlock hK I)) ⧸
        Subgroup.center ↥(coverComponent θ (suBlock hK I))) :=
      hcard.symm ▸ three_dvd_card_centerQuot_suBlock (hK := hK) (by omega) hId
    exact h3q.trans
      (Subgroup.card_quotient_dvd_card (Subgroup.center ↥(coverComponent θ (suBlock hK I))))

omit [Finite G] in
private theorem exists_layer_coverComponent_suBlock (hK : Nat.card K = 4)
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    (hζ : orderOf ζ = 3) (hI : ∀ i, i ∈ I ↔ w z i = t) (h5 : 5 ≤ I.card)
    (hId : I.card < d) (hdI : d ≤ I.card + 2) (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hDB : Subgroup.closure {x, z} ≤ B) (hDe : IsElemAbelian 3 (Subgroup.closure {x, z}))
    (hDc : Nat.card (Subgroup.closure {x, z}) = 3 ^ 2) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s)
    (ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    (hψI : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ψ b))
    (hψG : ∀ b ∈ Bs, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) (ψ b))
    (F : Subgroup G)
    (hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ suBlock hK I, (ψ b) j = j)
    (hBF1 : B ⊓ F = Subgroup.closure {x, z}) :
    ∃ J₁ : Subgroup G,
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenStdSub 3 B x L (Subgroup.closure {x, z}) J₁ ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, I.card - 1, 1⟩) ∧
      Bs ⊓ Subgroup.centralizer (J₁ : Set G) = F ∧
      Nonempty (↥J₁ ≃* unitarySU 2 1 K I.card) ∧ 3 ∣ Nat.card J₁ := by
  obtain ⟨hzBs, hJq, hfix, hnorm, hbig, hmark⟩ :=
    exists_unitaryBlock_data (hK := hK) (hζ := hζ) (hI := hI) (h5 := h5) (hId := hId)
      (hdI := hdI) (hDB := hDB) (hBs := hBs) (ψ := ψ) (hψG := hψG)
  have hsolv : IsSolvable (↥(TauCeti.fixedSubgroup (ψ z).toMonoidHom) ⧸
      (suBlock hK I).subgroupOf (TauCeti.fixedSubgroup (ψ z).toMonoidHom)) :=
    @isSolvable_fixedSubgroup_quotient_suBlock K _ d hK ζ hζ (w z) t I hI (by omega) hdI
      (ψ z) (hψG z hzBs) hnorm
  obtain ⟨J₁, hlay, hcomp, hq, hnormC, hsolvC, hmarkC, hcent, hstd⟩ :=
    @exists_goodPlane_component_of_cover G _ L _ _ θ B Bs F x z (ψ z) (suBlock hK I)
      hDB hDe hDc hx (hN hzBs) (hψI z hzBs) hJq hfix hnorm hsolv hbig
      (⟨.twA, I.card - 1, 1⟩ : LargeEvenLabel) hmark hBs.1 hN ψ hψI hF hBF1
  have hcc := @coverComponent_eq_layer G _ L _ _ θ x z (ψ z) (suBlock hK I)
    hx (hN hzBs) (hψI z hzBs) hJq hfix hnorm hsolv
  dsimp only at hcc
  have heq : J₁ = coverComponent θ (suBlock hK I) := hlay.trans hcc.1.symm
  obtain ⟨hSU, h3⟩ := coverComponent_suBlock_props (hK := hK) (hker := hker)
    (hθ := hθ) (h5 := h5) (hId := hId) (θ := θ)
  exact ⟨J₁, hlay, hstd, hmarkC, hcent, heq.symm ▸ hSU, heq.symm ▸ h3⟩

private theorem p5Out_of_layer (hK : Nat.card K = 4) (hζ : orderOf ζ = 3)
    (hThm : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hDB' : Subgroup.closure {x, z} ≠ B) {J₁ F : Subgroup G}
    (hBF1 : B ⊓ F = Subgroup.closure {x, z})
    (ψ : G → MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    (hstd : LargeEvenStdSub 3 B x L (Subgroup.closure {x, z}) J₁)
    (hcent : Bs ⊓ Subgroup.centralizer (J₁ : Set G) = F)
    (hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ suBlock hK I, (ψ b) j = j)
    (hψG : ∀ b ∈ Bs, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w b i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹) (ψ b))
    (hSU : Nonempty (↥J₁ ≃* unitarySU 2 1 K I.card))
    (h3 : 3 ∣ Nat.card J₁) (hr : Rank3Witness (unitarySU 2 1 K I.card) r)
    (hm : LargeEvenTwoLocalRank 3 G < 2 * r + 1) :
    P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      (∀ b, b ∈ Bs ⊓ Subgroup.centralizer (J₁ : Set G) ↔
        b ∈ Bs ∧ ∀ i ∈ I, ∀ j ∈ I, w b i = w b j) := by
  have hA1 := not_le_centralizer_of_inf_eq hBs.1 hcent hBF1 hDB'
  refine ⟨⟨⟨hThm, hBs, hstd⟩, rfl, hN, h3, hA1, ⟨r, hm, ?_⟩⟩, ?_⟩
  · obtain ⟨e⟩ := hSU
    exact Rank3Witness.of_mulEquiv e.symm hr
  · intro b
    rw [hcent, hF b]
    constructor
    · rintro ⟨hb, hfix⟩
      exact ⟨hb, (forall_mem_suBlock_apply_eq_iff (hK := hK) (hζ := hζ) (I := I)
        (w := w b) (ψ := ψ b) (hψG b hb)).mp hfix⟩
    · rintro ⟨hb, hw⟩
      exact ⟨hb, (forall_mem_suBlock_apply_eq_iff (hK := hK) (hζ := hζ) (I := I)
        (w := w b) (ψ := ψ b) (hψG b hb)).mpr hw⟩

end Setup

theorem exists_p5Out_of_unitaryCover {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x z : G} {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {K : Type} [Field K] (hK : Nat.card K = 4)
    {d : ℕ} {φ : ↥(LargeEvenSUGroup (Fin d) K 2) →* ↥L} (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    {ζ : Kˣ} (hζ : orderOf ζ = 3) {w : G → Fin d → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(LargeEvenSUGroup (Fin d) K 2),
      (s' : GL (Fin d) K) = TauCeti.diagGL (fun i => ζ ^ (w b i).val) * s *
          (TauCeti.diagGL (fun i => ζ ^ (w b i).val))⁻¹ →
        ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    {I : Finset (Fin d)} {t : ZMod 3} (hI : ∀ i, i ∈ I ↔ w z i = t) (h5 : 5 ≤ I.card)
    (hId : I.card < d) (hdI : d ≤ I.card + 2) (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hDB : Subgroup.closure {x, z} ≤ B) (hDB' : Subgroup.closure {x, z} ≠ B)
    (hDe : IsElemAbelian 3 (Subgroup.closure {x, z}))
    (hDc : Nat.card (Subgroup.closure {x, z}) = 3 ^ 2)
    (hBF : ∀ b ∈ B, (∀ i ∈ I, ∀ j ∈ I, w b i = w b j) ↔ b ∈ Subgroup.closure {x, z})
    {r : ℕ} (hr : Rank3Witness (unitarySU 2 1 K I.card) r)
    (hm : LargeEvenTwoLocalRank 3 G < 2 * r + 1) :
    ∃ J₁ : Subgroup G, P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, I.card - 1, 1⟩) ∧
      (∀ b, b ∈ Bs ⊓ Subgroup.centralizer (J₁ : Set G) ↔
        b ∈ Bs ∧ ∀ i ∈ I, ∀ j ∈ I, w b i = w b j) ∧
      Nonempty (↥J₁ ≃* unitarySU 2 1 K I.card) := by
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)) = ⊥ :=
    center_eq_bot_largeEvenProj_suBlock (hK := hK) (h5 := h5) (hId := hId)
  obtain ⟨θ, hθ⟩ := exists_centerQuotEquiv_of_cover (q := 2) hφ hker hZ
  obtain ⟨ψ, hψI, hψG⟩ := exists_psi_of_unitaryCover (hφ := hφ) (hθ := hθ) (hζ := hζ)
    (hw := hw)
  let F : Subgroup G := Bs ⊓ Subgroup.centralizer (coverComponent θ (suBlock hK I) : Set G)
  have hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ suBlock hK I, (ψ b) j = j :=
    mem_inf_centralizer_coverComponent_iff (hK := hK) (hN := hN) (h5 := h5) (hId := hId)
      (θ := θ) (ψ := ψ) (hψ := hψI)
  have hBF1 : B ⊓ F = Subgroup.closure {x, z} :=
    inf_centralizer_eq_closure (hK := hK) (hζ := hζ) hBs.1 F ψ hF hψG hBF hDB
  obtain ⟨J₁, hlay, hstd, hmark, hcent, hSU, h3⟩ :=
    exists_layer_coverComponent_suBlock (hK := hK) (hker := hker) (hζ := hζ)
      (hI := hI) (h5 := h5) (hId := hId) (hdI := hdI) (hx := hx) (hDB := hDB)
      (hDe := hDe) (hDc := hDc) (hBs := hBs) (hN := hN) (θ := θ) (hθ := hθ)
      (ψ := ψ) (hψI := hψI) (hψG := hψG) (F := F) (hF := hF) (hBF1 := hBF1)
  obtain ⟨hP5, hcent'⟩ :=
    p5Out_of_layer (hK := hK) (hζ := hζ) (hThm := hThm) (hBs := hBs)
      (hN := hN) (hDB' := hDB') (hBF1 := hBF1) (ψ := ψ) (hstd := hstd)
      (hcent := hcent) (hF := hF) (hψG := hψG) (hSU := hSU) (h3 := h3) (hr := hr) (hm := hm)
  exact ⟨J₁, hP5, hlay, hmark, hcent', hSU⟩

end CFSG.StandardType.FrameRoute.UnitaryModel
