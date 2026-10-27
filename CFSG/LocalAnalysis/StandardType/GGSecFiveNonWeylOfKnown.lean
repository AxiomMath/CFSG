module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGA8NbrPlumb
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggA8Nbr_two_pow_mod_seven (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (2 ^ 3) (n / 3) 7]
  norm_num

theorem ggA8Nbr_seven_dvd_two_pow_sub_one_iff (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h := ggA8Nbr_two_pow_mod_seven n
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> rw [hr] at h <;> norm_num at h <;> omega

theorem ggA8Nbr_not_seven_dvd_two_pow_add_one (n : ℕ) : ¬ 7 ∣ 2 ^ n + 1 := by
  have h := ggA8Nbr_two_pow_mod_seven n
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> rw [hr] at h <;> norm_num at h <;> omega

theorem largeEvenSplit_seven_dvd {lab : LargeEvenLabel} (h : LargeEvenSplit 7 lab) :
    3 ∣ lab.n := by
  rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact (ggA8Nbr_seven_dvd_two_pow_sub_one_iff _).1 h
  · exact absurd h (ggA8Nbr_not_seven_dvd_two_pow_add_one _)
  · exact (ggA8Nbr_seven_dvd_two_pow_sub_one_iff _).1 h
  · omega

theorem ggTablePRow_a8_left {t : LargeEvenLieTag} {r n : ℕ}
    (h : GGTablePRow 7 ⟨t, r, n⟩ ⟨.A, 8, 1⟩) :
    (t = .A ∧ r = 2 ∧ n = 3) ∨ (t = .A ∧ r = 5 ∧ n = 1) := by
  cases t <;> simp [GGTablePRow] at h ⊢
  rcases h with ⟨h1, -, ⟨-, rfl⟩ | ⟨⟨-, rfl⟩, -⟩⟩ | ⟨h1, -, -, rfl⟩ | h | h
  · simp at h1
  · simp at h1
  · simp at h1
  · exact Or.inl h
  · exact Or.inr h

theorem ggTablePRow_e6_left {t : LargeEvenLieTag} {r n : ℕ}
    (h : GGTablePRow 7 ⟨t, r, n⟩ ⟨.E6, 0, 1⟩) : t = .triD4 ∧ n = 1 := by
  cases t <;> simp [GGTablePRow] at h ⊢
  · rcases h with ⟨h1, -, -, rfl⟩ | ⟨h1, -, -, rfl⟩ <;> simp at h1
  · obtain ⟨h1, -, rfl⟩ := h
    simp at h1
  · obtain ⟨h1, -, -, rfl⟩ := h
    simp at h1
  · exact h.2.2

theorem ggTablePRow_a23_right {t : LargeEvenLieTag} {r n : ℕ}
    (h : GGTablePRow 7 ⟨.A, 2, 3⟩ ⟨t, r, n⟩) :
    (t = .A ∧ r = 3 ∧ n = 3) ∨ (t = .C ∧ r = 3 ∧ n = 3) ∨ (t = .D ∧ r = 3 ∧ n = 3) ∨
      (t = .twD ∧ r = 4 ∧ n = 3) ∨ (t = .A ∧ r = 8 ∧ n = 1) := by
  cases t <;> simp [GGTablePRow] at h ⊢ <;> omega

theorem ggHasLabel_of_mulEquiv {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGHasLabel lab R) : GGHasLabel lab R' :=
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨e.symm.trans f⟩) h

theorem ggMarking_and_labelAll_dep {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (P' lab))
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP'⟩

section Transport

variable {G : Type} [Group G]

theorem ggIsComponentOf_ggFixSub_normalizerMonoidHom {L J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer ({g} : Set G))) :
    IsComponentOf (J.subgroupOf L) (ggFixSub (L.normalizerMonoidHom ⟨g, hg⟩)) := by
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have heq : ggFixSub (L.normalizerMonoidHom ⟨g, hg⟩) =
      (L ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf L := by
    ext l
    rw [mem_ggFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
      refine ⟨l.2, ?_⟩
      calc (l : G) * g = g * l * g⁻¹ * g := by rw [h']
        _ = g * l := by group
    · rintro ⟨-, h⟩
      refine Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      calc g * (l : G) * g⁻¹ = (l : G) * g * g⁻¹ := by rw [h]
        _ = l := by group
  rw [heq]
  exact ⟨Subgroup.comap_mono hJ.1, hJ.2.1.comap L.subtype,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) hJ.2.2⟩

theorem ggInf_centralizer_pair {L : Subgroup G} {x y : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ?_, h.2⟩⟩
  have := hLx h.1
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

end Transport

section Label

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_label_J_of_tcj (hTCJ : GGTCJKnown) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ LargeEvenSplit p lab ∧
      GGHasLabel lab (L ⧸ Subgroup.center L) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hy : y ∈ B := hnb.1.2.1
  have hMark : GGInnerDiagOnLab (fun _ _ => True) p B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hT
  have hLperf : commutator ↥L = ⊤ := hMark.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hTCJ p hp hp2 lab hlab) hMark
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨-, hsplit, hNL, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hy
  have hy1 : y ^ p = 1 := hBel.2 y hy
  have hep : L.normalizerMonoidHom ⟨y, hyN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (B.inv_mem hy)
  let ψ : ↥L →* R := (θ : L ⧸ Subgroup.center L →* R).comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥L := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥L ψ hψsurj hψker hLperf _ hep hφe (J.subgroupOf L) hJcomp
  refine ⟨lab, labJ, hlab, hsplit, hhas, hlabJ, hdvd, ?_⟩
  exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
    (Subgroup.map_center_eq _)) hhasJ

end Label

open CFSG.Open

theorem ggMarking_mono_lab {X : Type*} [Group X] {P P' : LargeEvenMarkProp X}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), LargeEvenInLambda2 lab → P lab R I F θ → P' lab R I F θ)
    (h : LargeEvenMarking X P) : LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hlab hθ⟩

theorem largeEvenInLambda2_a8 : LargeEvenInLambda2 ⟨.A, 8, 1⟩ := by
  simp [LargeEvenInLambda2]

theorem largeEvenInLambda2_e6 : LargeEvenInLambda2 ⟨.E6, 0, 1⟩ := ⟨le_refl _, rfl⟩

section Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_exc_of_not_reflGen (hnc : GGNbrReflGenNonSplitFull) (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hZ : GGNbrBstarCenterInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hnr : ¬ GGReflGenerated p (ggAutomizer K Bs)) :
    p = 7 ∧ (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) := by
  have hHS := ggNbr_halfSplit_of_secFiveRest hraw hiso h hK
  by_cases hsp : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
  · exact absurd (ggNbrReflGen_of_tableB hTB hRig hZ h hK hsp) hnr
  by_cases hq : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1)
  · exact absurd (hnc G p B Bs x L D J h y K hK hsp hq) hnr
  have hDisj : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      p ∣ (2 ^ lab.n) ^ 2 - 1 ∨ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩))) :=
    ggMarking_mono_lab (fun lab _ _ _ _ _ hlab hP => largeEvenHalfSplit_dvd hlab hP) hHS
  rcases largeEvenMarking_or hDisj with hd | hex
  · exact absurd hd hq
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hp7, hl⟩ := largeEvenMarking_exists_hasLabel hex
  refine ⟨hp7, ?_⟩
  rcases hl with rfl | rfl
  · exact Or.inl hhas
  · exact Or.inr hhas

theorem eq_of_ggLabelIso_D4 {lab : LargeEvenLabel} {f : ℕ} (h : GGLabelIso lab ⟨.D, 4, f⟩) :
    lab = ⟨.D, 4, f⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem eq_of_ggLabelIso_triD4 {lab : LargeEvenLabel} {r f : ℕ}
    (h : GGLabelIso lab ⟨.triD4, r, f⟩) : lab = ⟨.triD4, r, f⟩ := by
  obtain ⟨t, rk, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggSecFiveA11Config_of_nonReflGen
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    (hCoord : GGA8NbrCoordInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hexc : p = 7 ∧ (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)))
    (hnr : ¬ GGReflGenerated p (ggAutomizer K Bs)) : GGSecFiveA11Config p B Bs x L D J := by
  obtain ⟨hp7, hexc⟩ := hexc
  subst hp7
  obtain ⟨lab, labJ, hlab, hsplit, hhasL, hlabJ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ h.1 hK
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨hTPJ, hTPL⟩ := hTP G 7 B Bs x L D J h rfl y K hK hexc
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ := hTPJ labJ hlabJ hhasJ
  have hKA8 : GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) := by
    rcases hexc with hA | hE
    · exact hA
    · exfalso
      have hkE : klab = ⟨.E6, 0, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inr rfl)
        (hRig klab ⟨.E6, 0, 1⟩ _ hkΛ largeEvenInLambda2_e6 hhasK1 hE)
      subst hkE
      obtain ⟨t, r, n⟩ := jlab
      obtain ⟨rfl, rfl⟩ := ggTablePRow_e6_left hrow
      have hJ := eq_of_ggLabelIso_triD4 (hRig labJ ⟨.triD4, r, 1⟩ _ hlabJ hjΛ hhasJ hhasJ1)
      subst hJ
      have := Nat.le_of_dvd one_pos hdvd
      omega
  have hkA : klab = ⟨.A, 8, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inl rfl)
    (hRig klab ⟨.A, 8, 1⟩ _ hkΛ largeEvenInLambda2_a8 hhasK1 hKA8)
  subst hkA
  obtain ⟨t, r, n⟩ := jlab
  have hLlab : GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
      GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L) := by
    rcases ggTablePRow_a8_left hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h23, -⟩
      · have hdvd3 : lab.n ∣ 3 := hdvd
        have h33 := Nat.le_of_dvd (by norm_num) hdvd3
        have hL3 : lab.n = 3 := by omega
        obtain ⟨jlab2, llab2, hj2Λ, hl2Λ, hrow2, hhasJ2, hhasL2⟩ :=
          hTPL ⟨.A, 2, 3⟩ lab hlabJ hlab hhasJ hhasL
        rcases ggLabelIso_typeA_cases hRig (r := 2) (f := 3) (by norm_num) hj2Λ hjΛ hhasJ2 hhasJ
          with rfl | ⟨h23, -⟩
        · obtain ⟨t2, r2, n2⟩ := llab2
          rcases ggTablePRow_a23_right hrow2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
              ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Or.inl hhasL2
          · exact Or.inr (Or.inl hhasL2)
          · exact Or.inl (ggHasLabel_D3_iff_A3.1 hhasL2)
          · exact Or.inr (Or.inr hhasL2)
          · exfalso
            rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num) hlab
                largeEvenInLambda2_a8 hhasL hhasL2 with rfl | ⟨h83, -⟩
            · have hL1 : (1 : ℕ) = 3 := hL3
              omega
            · omega
        · omega
      · omega
    · exfalso
      rcases ggLabelIso_typeA_cases hRig (r := 5) (f := 1) (by norm_num) hlabJ hjΛ hhasJ hhasJ1
        with rfl | ⟨h53, -⟩
      · have := Nat.le_of_dvd one_pos hdvd
        omega
      · omega
  have hKmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 :=
    statedClassicalModel_of_hasLabel_typeA (n := 8) (f := 1) largeEvenInLambda2_a8 hKA8
  obtain ⟨c, ι, hcall, hgen, hcL⟩ := hCoord G 7 B Bs x L D J h rfl y K hK hKmodel hLlab
  have hLmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := by
    by_cases hc : c ∈ Certificates.A8Nbr476.excCases
    · exact hcL (ggA8Nbr_excCases_fst c hc)
    · exact (ggA8Nbr_false_of_coord L K h.2.2.2.1 ι hcall hc hgen).elim
  exact ⟨rfl, hLmodel, y, K, hK, hKmodel, hnr⟩

end Dichotomy

section Input

theorem ggSecFiveN2Input_of_known (h : GGSecFiveNonWeylKnown)
    (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) : GGSecFiveN2Input := by
  obtain ⟨hnc, hR, hW, hC, hTCJ, hTP, hCoord, hA11⟩ := h
  have hZ := ggNbrBstarCenterInput_of_centerPCyclic hC
  intro G _ _ p B Bs x L D J hRest ⟨y, K, hK, hnr⟩
  exact hA11 G p B Bs x L D J hRest
    (ggSecFiveA11Config_of_nonReflGen hRig hTCJ hTP hCoord hRest hK
      (ggNbr_exc_of_not_reflGen (ggNbrReflGenNonSplitFull_of_rank hnc hR hW hRig hZ) hTB hRig hZ
        hraw hiso hRest hK hnr) hnr)

theorem ggSecFiveNonWeylInput_of_known
    (h : GGSecFiveNonWeylKnown) (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) : GGSecFiveNonWeylInput :=
  ggSecFiveNonWeylInput_iff.2 (ggSecFiveN2Input_of_known h hRig hTB hraw hiso)

end Input

end CFSG.StandardType

end
