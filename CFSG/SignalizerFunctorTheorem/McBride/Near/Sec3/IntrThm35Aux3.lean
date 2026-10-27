module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux2

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

variable {Γ : Type u} [Group Γ]

theorem normal_qimg_subgroupOf {M D D₂ : Subgroup Γ} [(D₂.subgroupOf D).Normal]
    (hD₂ : D₂ ≤ D) :
    ((AChief.qimg M D₂).subgroupOf (AChief.qimg M D)).Normal := by
  have h1 : D ≤ Subgroup.normalizer (D₂ : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD₂).mp inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (SolQuot.qimg_mono hD₂)).mpr
    (AChief.qimg_le_normalizer h1)

theorem qimg_fittingPre {M D D₂ : Subgroup Γ} [(D₂.subgroupOf D).Normal]
    [((AChief.qimg M D₂).subgroupOf (AChief.qimg M D)).Normal]
    (hD : D ≤ AChief.nrm M) (hD₂ : D₂ ≤ D) (hMD : D ⊓ M ≤ D₂) :
    AChief.qimg M (fittingPre D D₂) = fittingPre (AChief.qimg M D) (AChief.qimg M D₂) := by
  set φ := SolQuot.qres M D hD with hφ
  set K := D₂.subgroupOf D with hK
  set K' := (AChief.qimg M D₂).subgroupOf (AChief.qimg M D) with hK'
  have hKK' : K ≤ K'.comap φ := by
    intro y hy
    refine Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    exact (AChief.mem_qimg_iff M D₂ _).mpr ⟨⟨y, hD y.2⟩, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  let ψ : ↥D ⧸ K →* ↥(AChief.qimg M D) ⧸ K' := QuotientGroup.map K K' φ hKK'
  have hψ : ∀ y : ↥D, ψ (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨y, rfl⟩ := SolQuot.qres_surjective hD z'
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hψ] at hq
    have h1 : φ y ∈ K' := (QuotientGroup.eq_one_iff _).mp hq
    have h2 : ((φ y : ↥(AChief.qimg M D)) : AChief.QG M) ∈ AChief.qimg M D₂ :=
      Subgroup.mem_subgroupOf.mp h1
    obtain ⟨x, hx, hxy⟩ := (AChief.mem_qimg_iff M D₂ _).mp h2
    have hxy' : AChief.qmap M x = AChief.qmap M ⟨y, hD y.2⟩ := hxy
    have h3 : ((x : Γ))⁻¹ * (y : Γ) ∈ M :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hxy')
    have h4 : ((x : Γ))⁻¹ * (y : Γ) ∈ D ⊓ M :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hD₂ hx)) y.2, h3⟩
    have h5 : (y : Γ) ∈ D₂ := by
      have := mul_mem hx (hMD h4)
      simpa using this
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr h5)
  let e : ↥D ⧸ K ≃* ↥(AChief.qimg M D) ⧸ K' := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have he : ∀ y : ↥D, e (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
  have hF : ∀ z, z ∈ CFSG.fittingSubgroup (↥D ⧸ K) ↔
      e z ∈ CFSG.fittingSubgroup (↥(AChief.qimg M D) ⧸ K') := by
    intro z
    rw [← fittingSubgroup_map_equiv e]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', hzz⟩
      exact (e.injective hzz) ▸ hz'
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff M (fittingPre D D₂) z).mp hz
    obtain ⟨d, hd, hdy⟩ := hy
    have hyd : y = ⟨d, hD d.2⟩ := Subtype.ext hdy.symm
    refine ⟨φ d, ?_, ?_⟩
    · refine Subgroup.mem_comap.mpr ?_
      have h1 : e (QuotientGroup.mk d) ∈ CFSG.fittingSubgroup (↥(AChief.qimg M D) ⧸ K') :=
        (hF _).mp (Subgroup.mem_comap.mp hd)
      rw [he] at h1
      exact h1
    · rw [hyd]
      rfl
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨d, rfl⟩ := SolQuot.qres_surjective hD w
    refine (AChief.mem_qimg_iff M _ _).mpr ⟨⟨d, hD d.2⟩, ⟨d, ?_, rfl⟩, rfl⟩
    refine Subgroup.mem_comap.mpr ((hF _).mpr ?_)
    show e (QuotientGroup.mk d) ∈ _
    rw [he d]
    exact Subgroup.mem_comap.mp hw

theorem isNormalIn_qimg {M N H : Subgroup Γ} (h : IsNormalIn N H) :
    IsNormalIn (AChief.qimg M N) (AChief.qimg M H) :=
  ⟨SolQuot.qimg_mono h.1, AChief.qimg_le_normalizer h.2⟩

theorem isChiefFactorOf_qimg {H L N M : Subgroup Γ} (hc : IsChiefFactorOf H L N)
    (hH : H ≤ AChief.nrm M) (hML : M ⊓ L ≤ N) :
    IsChiefFactorOf (AChief.qimg M H) (AChief.qimg M L) (AChief.qimg M N) := by
  obtain ⟨hN, hL, hNL, hmin⟩ := hc
  have hNn : N ≤ AChief.nrm M := hN.1.trans hH
  have hLn : L ≤ AChief.nrm M := hL.1.trans hH
  refine ⟨isNormalIn_qimg hN, isNormalIn_qimg hL, ?_, ?_⟩
  · refine lt_of_le_of_ne (SolQuot.qimg_mono hNL.le) fun heq => ?_
    have h2 : L ≤ N ⊔ M := (SolQuot.qimg_le_qimg_iff hLn hNn).mp heq.ge
    refine absurd (fun l hl => ?_ : L ≤ N) (not_le_of_gt hNL)
    have hNM : N ≤ Subgroup.normalizer (M : Set Γ) := hNn
    have hl' : l ∈ (N : Set Γ) * M := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right N M hNM]
      exact h2 hl
    obtain ⟨n, hn, m, hm, rfl⟩ := hl'
    have hmL : m ∈ M ⊓ L := Subgroup.mem_inf.mpr ⟨hm, by
      have := mul_mem (inv_mem (hNL.le hn)) hl
      simpa using this⟩
    exact mul_mem hn (hML hmL)
  · intro K hK hNK hKL
    have hqn : SolQuot.qpre M K ≤ AChief.nrm M := SolQuot.qpre_le_nrm K
    have hHq : H ≤ Subgroup.normalizer (SolQuot.qpre M K : Set Γ) := by
      refine (SolQuot.qimg_le_normalizer_iff (R := M) (Y := AChief.nrm M) hqn
        (inf_le_right.trans (SolQuot.le_qpre K)) le_rfl hH).mp ?_
      rw [SolQuot.qimg_qpre]
      exact hK.2
    have hNK' : N ≤ L ⊓ SolQuot.qpre M K :=
      le_inf hNL.le ((SolQuot.qimg_le_iff hNn).mp hNK)
    have hnormK' : IsNormalIn (L ⊓ SolQuot.qpre M K) H :=
      ⟨inf_le_left.trans hL.1, fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hL.2 hg, hHq hg⟩⟩
    have hKeq : K = AChief.qimg M (L ⊓ SolQuot.qpre M K) := by
      refine le_antisymm (fun z hz => ?_)
        ((SolQuot.qimg_le_iff (inf_le_left.trans hLn)).mpr inf_le_right)
      obtain ⟨y, hyL, rfl⟩ := (AChief.mem_qimg_iff M L z).mp (hKL hz)
      exact (AChief.mem_qimg_iff M _ _).mpr
        ⟨y, Subgroup.mem_inf.mpr ⟨hyL, SolQuot.mem_qpre_iff.mpr ⟨y.2, hz⟩⟩, rfl⟩
    rcases hmin _ hnormK' hNK' inf_le_left with h | h
    · left
      rw [hKeq, h]
    · right
      rw [hKeq, h]

theorem qimg_le_secCenIn {A' R' H L N M : Subgroup Γ} (hH : H ≤ AChief.nrm M)
    (h : A' ⊔ R' ≤ secCenIn H L N) :
    AChief.qimg M A' ⊔ AChief.qimg M R' ≤
      secCenIn (AChief.qimg M H) (AChief.qimg M L) (AChief.qimg M N) := by
  have hle : A' ⊔ R' ≤ H := h.trans inf_le_left
  have hA' : A' ≤ AChief.nrm M := (le_sup_left.trans hle).trans hH
  have hR' : R' ≤ AChief.nrm M := (le_sup_right.trans hle).trans hH
  rw [← SolQuot.qimg_sup hA' hR']
  intro z hz
  obtain ⟨g, hg, rfl⟩ := (AChief.mem_qimg_iff M _ z).mp hz
  have hgs := h hg
  obtain ⟨hgH, hgc⟩ := Subgroup.mem_inf.mp hgs
  refine Subgroup.mem_inf.mpr ⟨(AChief.mem_qimg_iff M H _).mpr ⟨g, hgH, rfl⟩, ?_⟩
  obtain ⟨hgN, hgL, hgcomm⟩ := mem_sectionCentralizer_iff.mp hgc
  refine mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun y hy => ?_⟩
  · exact AChief.qimg_le_normalizer (Y := N) (E := Subgroup.zpowers (g : Γ))
      (Subgroup.zpowers_le.mpr hgN)
      ((AChief.mem_qimg_iff M _ _).mpr ⟨g, Subgroup.mem_zpowers _, rfl⟩)
  · exact AChief.qimg_le_normalizer (Y := L) (E := Subgroup.zpowers (g : Γ))
      (Subgroup.zpowers_le.mpr hgL)
      ((AChief.mem_qimg_iff M _ _).mpr ⟨g, Subgroup.mem_zpowers _, rfl⟩)
  · obtain ⟨l, hl, rfl⟩ := (AChief.mem_qimg_iff M L y).mp hy
    refine (AChief.mem_qimg_iff M N _).mpr ⟨⁅g, l⁆, hgcomm _ hl, ?_⟩
    rw [map_commutatorElement]

theorem qimg_inf_cenIn [Finite Γ] {p : ℕ} {A X Y M : Subgroup Γ} (h : NearAsolvAction p A X)
    (hY : Y ≤ X) (hAY : Admits A Y) (hX : X ≤ AChief.nrm M) (hA : A ≤ AChief.nrm M) :
    AChief.qimg M (Y ⊓ cenIn X (A : Set Γ)) =
      AChief.qimg M Y ⊓ cenIn (AChief.qimg M X)
        ((AChief.qimg M A : Subgroup (AChief.QG M)) : Set (AChief.QG M)) := by
  have hcop : Nat.Coprime p (Nat.card ↥Y) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hY)
  have h1 : Y ⊓ cenIn X (A : Set Γ) = Y ⊓ Subgroup.centralizer (A : Set Γ) := by
    unfold cenIn
    rw [← inf_assoc, inf_eq_left.mpr hY]
  rw [h1, AChief.qimg_inf_centralizer h.prime h.elemAbelian hAY hA (hY.trans hX) hcop]
  unfold cenIn
  rw [← inf_assoc, inf_eq_left.mpr (SolQuot.qimg_mono hY)]

theorem hyp_qimg [Finite Γ] {p : ℕ} {A X D D₂ N L R M X₁ X₂ : Subgroup Γ}
    [(D₂.subgroupOf D).Normal] [((AChief.qimg M D₂).subgroupOf (AChief.qimg M D)).Normal]
    (H : Hyp p A X D D₂ N L R) (hP : (X₁, X₂) ∈ iPairsY A X D₂) (hMX : M ≤ X)
    (hXM : X ≤ AChief.nrm M) (hAM : A ≤ AChief.nrm M) (hM1 : M ⊓ X₁ ≤ X₂) :
    Hyp p (AChief.qimg M A) (AChief.qimg M X) (AChief.qimg M D) (AChief.qimg M D₂)
      (AChief.qimg M N) (AChief.qimg M L) (AChief.qimg M R) := by
  have hDn : D ≤ AChief.nrm M := H.D_le_X.trans hXM
  have hRn : R ≤ AChief.nrm M := H.hR.trans hXM
  have hLn : L ≤ AChief.nrm M := H.hL.trans hXM
  have hNn : N ≤ AChief.nrm M := H.hN.trans hXM
  have hD₂n : D₂ ≤ AChief.nrm M := H.D₂_le_X.trans hXM
  have hDsn : fittingPre D D₂ ≤ AChief.nrm M := fittingPre_le.trans hDn
  have hHn : R ⊔ D ⊔ A ≤ AChief.nrm M := sup_le (sup_le hRn hDn) hAM
  have hMD : D ⊓ M ≤ D₂ := by
    have := Thm33a.inf_dsub_le hP hXM hM1
    rw [H.cen] at this
    rwa [inf_comm]
  have hML : M ⊓ L ≤ N := fun l hl =>
    H.inf_sup_le hMX hXM hAM hMD (Subgroup.mem_inf.mpr ⟨hl.2, Subgroup.mem_sup_right hl.1⟩)
  have hHq : AChief.qimg M R ⊔ AChief.qimg M D ⊔ AChief.qimg M A =
      AChief.qimg M (R ⊔ D ⊔ A) := by
    rw [SolQuot.qimg_sup (sup_le hRn hDn) hAM, SolQuot.qimg_sup hRn hDn]
  have hcenq : cenIn (AChief.qimg M X) ((AChief.qimg M A : Subgroup (AChief.QG M)) :
      Set (AChief.QG M)) = AChief.qimg M D :=
    (Thm33a.cenIn_qimg H.near hXM hAM).trans (by rw [H.cen])
  have hFq := qimg_fittingPre hDn H.D₂_le_D hMD
  refine
    { near := Thm211.nearAsolvAction_qimg H.near hXM hAM
      cen := hcenq
      pair := ⟨_, Thm33a.qimg_mem_iPairsY H.near hP hXM hAM hM1⟩
      hN := SolQuot.qimg_mono H.hN
      hL := SolQuot.qimg_mono H.hL
      hR := SolQuot.qimg_mono H.hR
      nN := by rw [hHq]; exact isNormalIn_qimg H.nN
      nL := by rw [hHq]; exact isNormalIn_qimg H.nL
      nR := by rw [hHq]; exact isNormalIn_qimg H.nR
      chief := by rw [hHq]; exact isChiefFactorOf_qimg H.chief hHn hML
      LR := SolQuot.qimg_mono H.LR
      cent := by rw [hHq]; exact qimg_le_secCenIn hHn H.cent
      RD := ?_
      ND := ?_
      prod := ?_ }
  · have hAR : Admits A R := (A_le_H R D A).trans H.H_le_R
    rw [← hFq, ← H.RD, ← H.cen, qimg_inf_cenIn H.near H.hR hAR hXM hAM,
      ← Thm33a.cenIn_qimg H.near hXM hAM]
  · rw [inf_comm, ← hcenq, ← qimg_inf_cenIn H.near H.hN H.admits_A_N hXM hAM]
    exact SolQuot.qimg_mono (by rw [H.cen, inf_comm]; exact H.ND)
  · rw [← hFq]
    obtain ⟨-, -, h3, -, h5⟩ := H.prod
    refine ⟨le_sup_right, SolQuot.qimg_mono H.N_le_L, ?_, ?_, ?_⟩
    · have := congrArg (AChief.qimg M) h3
      rw [SolQuot.qimg_sup (sup_le hD₂n hNn) hLn, SolQuot.qimg_sup hD₂n hNn,
        SolQuot.qimg_sup hDsn hNn] at this
      exact this
    · refine le_antisymm (fun z hz => ?_) (le_inf le_sup_right (SolQuot.qimg_mono H.N_le_L))
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
      rw [← SolQuot.qimg_sup hD₂n hNn] at hz1
      obtain ⟨a, ha, rfl⟩ := (AChief.mem_qimg_iff M _ z).mp hz1
      obtain ⟨b, hb, hab⟩ := (AChief.mem_qimg_iff M L _).mp hz2
      have hm : (a : Γ)⁻¹ * (b : Γ) ∈ M :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hab.symm)
      have hbS : (b : Γ) ∈ D₂ ⊔ N ⊔ M := by
        have := mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hm)
        simpa using this
      have hbN : (b : Γ) ∈ N :=
        H.inf_sup_le hMX hXM hAM hMD (Subgroup.mem_inf.mpr ⟨hb, hbS⟩)
      exact (AChief.mem_qimg_iff M N _).mpr ⟨b, hbN, hab⟩
    · rw [← SolQuot.qimg_sup hD₂n hNn, ← Thm33a.qimg_commutator (sup_le hD₂n hNn) hLn]
      exact SolQuot.qimg_mono h5

theorem concl_of_qimg [Finite Γ] {p : ℕ} {A X D D₂ N L R M : Subgroup Γ}
    [(D₂.subgroupOf D).Normal] [((AChief.qimg M D₂).subgroupOf (AChief.qimg M D)).Normal]
    (H : Hyp p A X D D₂ N L R) (hMD : D ⊓ M ≤ D₂) (hXM : X ≤ AChief.nrm M)
    (hAM : A ≤ AChief.nrm M)
    (hC : Concl (AChief.qimg M A) (AChief.qimg M D) (AChief.qimg M D₂) (AChief.qimg M R)) :
    Concl A D D₂ R := by
  obtain ⟨B, hBR, hBn, hBD, hRB⟩ := hC
  have hDn : D ≤ AChief.nrm M := H.D_le_X.trans hXM
  have hRn : R ≤ AChief.nrm M := H.hR.trans hXM
  have hHn : R ⊔ D ⊔ A ≤ AChief.nrm M := sup_le (sup_le hRn hDn) hAM
  have hHq : AChief.qimg M R ⊔ AChief.qimg M D ⊔ AChief.qimg M A =
      AChief.qimg M (R ⊔ D ⊔ A) := by
    rw [SolQuot.qimg_sup (sup_le hRn hDn) hAM, SolQuot.qimg_sup hRn hDn]
  have hFq := qimg_fittingPre hDn H.D₂_le_D hMD
  have hqn : SolQuot.qpre M B ≤ AChief.nrm M := SolQuot.qpre_le_nrm B
  have hHB : R ⊔ D ⊔ A ≤ Subgroup.normalizer (SolQuot.qpre M B : Set Γ) := by
    refine (SolQuot.qimg_le_normalizer_iff (R := M) (Y := AChief.nrm M) hqn
      (inf_le_right.trans (SolQuot.le_qpre B)) le_rfl hHn).mp ?_
    rw [SolQuot.qimg_qpre, ← hHq]
    exact hBn.2
  have hD₂n : D₂ ≤ AChief.nrm M := H.D₂_le_X.trans hXM
  have hD₂B : AChief.qimg M D₂ ≤ B := le_of_eq_of_le hBD.symm inf_le_left
  refine ⟨SolQuot.qpre M B ⊓ R, inf_le_right, ⟨inf_le_right.trans (R_le_H R D A), fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHB hg, H.H_le_R hg⟩⟩, ?_, ?_⟩
  · refine le_antisymm (fun x hx => ?_)
      (le_inf (le_inf ((SolQuot.qimg_le_iff hD₂n).mp hD₂B) H.D₂_le_R) H.D₂_le_D)
    obtain ⟨hxBR, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxB, hxR⟩ := Subgroup.mem_inf.mp hxBR
    obtain ⟨hxn, hxq⟩ := SolQuot.mem_qpre_iff.mp hxB
    have hxD' : AChief.qmap M ⟨x, hxn⟩ ∈ AChief.qimg M D :=
      (AChief.mem_qimg_iff M D _).mpr ⟨⟨x, hxn⟩, hxD, rfl⟩
    have hx2 : AChief.qmap M ⟨x, hxn⟩ ∈ AChief.qimg M D₂ := by
      rw [← hBD]
      exact Subgroup.mem_inf.mpr ⟨hxq, hxD'⟩
    obtain ⟨y, hy, hyx⟩ := (AChief.mem_qimg_iff M D₂ _).mp hx2
    have hm : (y : Γ)⁻¹ * x ∈ M := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hyx)
    have hmD : (y : Γ)⁻¹ * x ∈ D ⊓ M :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (H.D₂_le_D hy)) hxD, hm⟩
    have := mul_mem hy (hMD hmD)
    simpa using this
  · refine le_antisymm (fun r hr => ?_) (sup_le inf_le_right H.Ds_le_R)
    have hrn := hRn hr
    have hz : AChief.qmap M ⟨r, hrn⟩ ∈ AChief.qimg M R :=
      (AChief.mem_qimg_iff M R _).mpr ⟨⟨r, hrn⟩, hr, rfl⟩
    rw [← hFq] at hRB
    rw [hRB, sup_comm] at hz
    have hDsB : AChief.qimg M (fittingPre D D₂) ≤ Subgroup.normalizer (B : Set _) :=
      (SolQuot.qimg_mono fittingPre_le).trans ((le_sup_right.trans le_sup_left).trans hBn.2)
    have hz2 : AChief.qmap M ⟨r, hrn⟩ ∈
        (AChief.qimg M (fittingPre D D₂) : Set (AChief.QG M)) * (B : Set (AChief.QG M)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDsB]
      exact hz
    obtain ⟨f, hf, b, hb, hfb⟩ := hz2
    obtain ⟨d, hd, rfl⟩ := (AChief.mem_qimg_iff M _ f).mp hf
    have hb' : AChief.qmap M (d⁻¹ * ⟨r, hrn⟩) = b := by
      rw [map_mul, map_inv, ← hfb]
      group
    have hrB : (d : Γ)⁻¹ * r ∈ SolQuot.qpre M B ⊓ R :=
      Subgroup.mem_inf.mpr ⟨SolQuot.mem_qpre_iff.mpr ⟨(d⁻¹ * ⟨r, hrn⟩).2, hb' ▸ hb⟩,
        mul_mem (inv_mem (H.Ds_le_R hd)) hr⟩
    have hr' : r = (d : Γ) * ((d : Γ)⁻¹ * r) := by group
    rw [hr', sup_comm]
    exact Subgroup.mul_mem_sup hd hrB

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
