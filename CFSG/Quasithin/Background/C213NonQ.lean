module

public import CFSG.Quasithin.Background.C213NonQMain
public import CFSG.Quasithin.Background.C2ThirteenStep
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C213NonQ

open CFSG.Open CFSG.QuasithinUnique

theorem eq_of_le_of_a37 (h37 : A37ForSQTK) {Q : Type} [Group Q] (hQ : SQTKHyp Q)
    {M L K : Subgroup Q} (hL : L ∈ cComp M) (hK : K ∈ cComp (⊤ : Subgroup Q)) (hKM : K ≤ M)
    (hKL : ⁅K, L⁆ = K) : K = L := by
  have := hQ.finite
  have hKMc : K ∈ cComp M := cComp_mem_of_le hK hKM le_top
  set Γ := ↥M ⧸ CFSG.pCore 2 ↥M
  have hΓ : SQTKHyp Γ := SQTKHyp.of_sqtkGroup ↥M (hQ.subgroup M)
  have h37Γ := h37 Γ hΓ
  set f := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hf
  have hker : Group.IsSolvable ↥f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥M) := CFSG.pCore_isPGroup.isNilpotent
    infer_instance
  have hK₁ := subgroupOf_mem_cComp hKMc
  have hL₁ := subgroupOf_mem_cComp hL
  have hK₂ := map_mem_cComp_top f (QuotientGroup.mk'_surjective _) hker hK₁
  have hL₂ := map_mem_cComp_top f (QuotientGroup.mk'_surjective _) hker hL₁
  by_cases h : (K.subgroupOf M).map f = (L.subgroupOf M).map f
  · have h1 := map_injOn_cComp_top f hker hK₁ hL₁ h
    rw [← Subgroup.map_subgroupOf_eq_of_le hKM,
      ← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL), h1]
  · exfalso
    have h2 := h37Γ _ hK₂ _ hL₂ h
    have hKL₁ : ⁅K.subgroupOf M, L.subgroupOf M⁆ = K.subgroupOf M := by
      rw [← C48Spor.commutator_subgroupOf_of_le hKM (le_of_mem_cComp hL), hKL]
    have h3 : K.subgroupOf M ≤ f.ker := by
      rw [← hKL₁, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
      exact h2
    rw [hf, QuotientGroup.ker_mk'] at h3
    have hsol : Group.IsSolvable ↥(K.subgroupOf M) := by
      have : IsPGroup 2 ↥(K.subgroupOf M) := CFSG.pCore_isPGroup.to_le h3
      have : Group.IsNilpotent ↥(K.subgroupOf M) := this.isNilpotent
      infer_instance
    exact not_isSolvable_of_mem_cComp hK₁ hsol

section Hyp

variable {G : Type} [Group G] [Finite G] {H R M L V : Subgroup G}

abbrev o2H (H : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype

omit [Finite G] in
theorem o2H_le_oTwoFstarIn (H : Subgroup G) : o2H H ≤ oTwoFstarIn H := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ CFSG.generalizedFitting _
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem le_normalizer_o2H (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((o2H H : Subgroup G) : Set G) :=
  le_normalizer_map_of_characteristic (Q := G) Subgroup.le_normalizer _

theorem le_of_le_centralizerSection (h : HypC28 H R M L V) {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPC : P ≤ centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)))
    (hPn : M ≤ Subgroup.normalizer (P : Set G)) : P ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) ≤ M :=
    fun x hx => hx.1
  refine (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 P _ hPC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mpr (hCM.trans hPn)) hP).trans ?_
  exact CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.sylow

omit [Finite G] in
theorem le_normalizer_pCoreOf_M₀ (L M : Subgroup G) :
    M ≤ Subgroup.normalizer ((pCoreOf 2 (conjClosure L M) : Subgroup G) : Set G) :=
  (le_normalizer_conjClosure L M).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure L M))

theorem pCoreOf_M₀_le (h : HypC28 H R M L V) : pCoreOf 2 (conjClosure L M) ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M with hM₀
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hO : pCoreOf 2 M₀ ≤ M₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 M₀
  refine le_of_le_centralizerSection h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀)
    (fun x hx => ⟨hM₀M (hO hx), Subgroup.le_normalizer (hO hx),
      Subgroup.le_normalizer hx, fun m hm => ?_⟩) (le_normalizer_pCoreOf_M₀ L M)
  have h1 : m * x * m⁻¹ ∈ pCoreOf 2 M₀ :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M₀ (Subgroup.le_normalizer hm))
      x).mp hx
  exact (pCoreOf 2 M₀).mul_mem h1 ((pCoreOf 2 M₀).inv_mem hx)

theorem o2H_le (h : HypC28 H R M L V) (hF : oTwoFstarIn H ≤ M) : o2H H ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M with hM₀
  have hOM : o2H H ≤ M := (o2H_le_oTwoFstarIn H).trans hF
  have hM₀H : M₀ ≤ H := (C2Nine.conjClosure_le_M h).trans h.le_H
  have hOp : IsPGroup 2 ↥(o2H H) := CFSG.pCore_isPGroup.map H.subtype
  refine le_of_le_centralizerSection h hOp (fun x hx => ⟨hOM hx,
    le_normalizer_conjClosure L M (hOM hx), le_normalizer_pCoreOf_M₀ L M (hOM hx),
    fun m hm => ?_⟩) ((h.le_H).trans (le_normalizer_o2H H))
  have h1 : m * x * m⁻¹ * x⁻¹ ∈ M₀ := by
    have h2 : x * m⁻¹ * x⁻¹ ∈ M₀ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L M (hOM hx)) m⁻¹).mp
        (M₀.inv_mem hm)
    rw [show m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) by group]
    exact M₀.mul_mem hm h2
  have h3 : m * x * m⁻¹ * x⁻¹ ∈ o2H H := by
    have h4 : m * x * m⁻¹ ∈ o2H H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_o2H H (hM₀H hm)) x).mp hx
    exact (o2H H).mul_mem h4 ((o2H H).inv_mem hx)
  have hI : M₀ ⊓ o2H H ≤ pCoreOf 2 M₀ := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ M₀ inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_)
      (hOp.to_le inf_le_right)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgH := le_normalizer_o2H H (hM₀H hg)
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨M₀.mul_mem (M₀.mul_mem hg hy1) (M₀.inv_mem hg),
        (Subgroup.mem_normalizer_iff.mp hgH y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hgH y).mpr hy2⟩
      rw [e]
      exact M₀.mul_mem (M₀.mul_mem (M₀.inv_mem hg) hy1) hg
  exact hI ⟨h1, h3⟩

theorem inf_normalizer_le (h : HypC28 H R M L V) : H ⊓ Subgroup.normalizer (R : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using h.V_elem.2 x x.2)⟩
  have hVO₂ : V ≤ pCoreOf 2 (conjClosure L M) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V _ h.V_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.V_le).mpr
        (C48Spor.M0_le_normalizer_V h)) hV2
  have hRne : R ≠ ⊥ := fun hb => h.V_ne (le_bot_iff.mp (hb ▸ hVO₂.trans (pCoreOf_M₀_le h)))
  have hchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  refine le_trans ?_ h.cgs
  unfold cgsIn
  exact le_iSup₂_of_le R le_rfl (le_iSup₂_of_le hRne hchar le_rfl)

theorem asc213StepNonQ_of_a3 (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    ASC213StepNonQ G := by
  intro H R M L V h hF _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M with hM₀
  have hMH : M ≤ H := h.le_H
  have hLM₀ : L ≤ M₀ := le_conjClosure L M
  have hRM : R ≤ M := h.le_M
  set N₂ := CFSG.pCore 2 ↥H with hN₂
  have hQ : SQTKHyp (↥H ⧸ N₂) := SQTKHyp.of_sqtkGroup ↥H h.sqtk
  have hN₂s : Group.IsSolvable ↥N₂ := by
    have : Group.IsNilpotent ↥N₂ := CFSG.pCore_isPGroup.isNilpotent
    infer_instance
  have hbij := (cComp_quotient_bijOn N₂ hN₂s).comp (cComp_subgroupOf_bijOn H)
  have hO2R : o2H H ≤ R := o2H_le h hF
  have hO2M : o2H H ≤ M := (o2H_le_oTwoFstarIn H).trans hF
  have hO2s : Group.IsSolvable ↥(o2H H) := by
    have : Group.IsNilpotent ↥(o2H H) := (CFSG.pCore_isPGroup.map H.subtype).isNilpotent
    infer_instance
  have hFM : CFSG.generalizedFitting (↥H ⧸ N₂) ≤ C48Spor.img N₂ M := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₂ x
    have hy : (y : G) ∈ oTwoFstarIn H := ⟨y, hx, rfl⟩
    exact ⟨y, hF hy, rfl⟩
  have hLne : C48Spor.img N₂ L ≠ ⊥ := by
    intro hb
    have h1 : L.subgroupOf H ≤ N₂ := by
      have := (Subgroup.map_eq_bot_iff _).mp hb
      rwa [QuotientGroup.ker_mk'] at this
    have h2 : L ≤ o2H H := by
      intro x hx
      exact ⟨⟨x, hMH (le_of_mem_cComp h.comp hx)⟩, h1 hx, rfl⟩
    have hsol : Group.IsSolvable ↥L := by
      have : IsPGroup 2 ↥L := (CFSG.pCore_isPGroup.map H.subtype).to_le h2
      have : Group.IsNilpotent ↥L := this.isNilpotent
      infer_instance
    exact not_isSolvable_of_mem_cComp h.comp hsol
  have hLb : C48Spor.img N₂ L ∈ cComp (C48Spor.img N₂ M) := C48Spor.img_mem_cComp hMH h.comp hLne
  have hRO : ∀ m ∈ C48Spor.img N₂ M₀, ∀ r ∈ C48Spor.img N₂ R,
      m * r * m⁻¹ * r⁻¹ ∈ C48Spor.img N₂ (pCoreOf 2 M₀) := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨r, hr, rfl⟩
    have h1 := (h.sylow.1 hr).2.2.2 m hm
    exact ⟨m * r * m⁻¹ * r⁻¹, h1, by simp [map_mul, map_inv]⟩
  have hcgs : ∀ K ∈ cComp (⊤ : Subgroup (↥H ⧸ N₂)),
      C48Spor.img N₂ R ≤ Subgroup.centralizer (K : Set (↥H ⧸ N₂)) → K ≤ C48Spor.img N₂ M := by
    intro K hK hRK
    obtain ⟨K', hK', rfl⟩ := hbij.surjOn hK
    have hK'H : K' ≤ H := le_of_mem_cComp hK'
    have key : ∀ k ∈ K', ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
      intro k hk r hr
      have hkH := hK'H hk
      have hrH := hMH (hRM hr)
      have h1 : QuotientGroup.mk' N₂ ⟨k, hkH⟩ * QuotientGroup.mk' N₂ ⟨r, hrH⟩ =
          QuotientGroup.mk' N₂ ⟨r, hrH⟩ * QuotientGroup.mk' N₂ ⟨k, hkH⟩ :=
        Subgroup.mem_centralizer_iff.mp (hRK ⟨⟨r, hrH⟩, hr, rfl⟩) _ ⟨⟨k, hkH⟩, hk, rfl⟩
      have h2 : (⟨k, hkH⟩ : ↥H) * ⟨r, hrH⟩ * (⟨k, hkH⟩ : ↥H)⁻¹ * (⟨r, hrH⟩ : ↥H)⁻¹ ∈ N₂ := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        have h1' : ((⟨k, hkH⟩ : ↥H) : ↥H ⧸ N₂) * ((⟨r, hrH⟩ : ↥H) : ↥H ⧸ N₂) =
            ((⟨r, hrH⟩ : ↥H) : ↥H ⧸ N₂) * ((⟨k, hkH⟩ : ↥H) : ↥H ⧸ N₂) := h1
        rw [h1']
        group
      have h3 : k * r * k⁻¹ * r⁻¹ ∈ R := hO2R ⟨_, h2, rfl⟩
      have e : k * r * k⁻¹ = (k * r * k⁻¹ * r⁻¹) * r := by group
      rw [e]
      exact R.mul_mem h3 hr
    have hK'R : K' ≤ H ⊓ Subgroup.normalizer (R : Set G) := by
      intro k hk
      refine ⟨hK'H hk, Subgroup.mem_normalizer_iff.mpr fun r => ⟨key k hk r, fun hr' => ?_⟩⟩
      have := key k⁻¹ (K'.inv_mem hk) _ hr'
      simpa [mul_assoc] using this
    exact C48Spor.img_mono (hK'R.trans (inf_normalizer_le h))
  have hmain : C48Spor.img N₂ L ∈ cComp (⊤ : Subgroup (↥H ⧸ N₂)) :=
    mem_cComp_top (h36 _ hQ) (h37 _ hQ) (h39 _ hQ) hFM hLb (C48Spor.img_mono hLM₀)
      (C48Spor.isPGroup_img h.pgroup)
      (C48Spor.isPGroup_img (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀)) hRO
      (fun K hK hKM hKL => eq_of_le_of_a37 h37 hQ hLb hK hKM hKL) hcgs
  obtain ⟨L', hL', hL'eq⟩ := hbij.surjOn hmain
  have hL'H : L' ≤ H := le_of_mem_cComp hL'
  have hLH : L ≤ H := (le_of_mem_cComp h.comp).trans hMH
  have hsup : L' ⊔ o2H H = L ⊔ o2H H := by
    have h1 : (L'.subgroupOf H).map (QuotientGroup.mk' N₂) =
        (L.subgroupOf H).map (QuotientGroup.mk' N₂) := hL'eq
    have h2 := congrArg (fun X => (X.comap (QuotientGroup.mk' N₂)).map H.subtype) h1
    simp only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hL'H, Subgroup.map_subgroupOf_eq_of_le hLH] at h2
    exact h2
  have hL'1 := (cComp_commutator_perfectCore hL' (o2H_le_oTwoFstarIn H |>.trans
    (C2ThirteenStep.oTwoFstarIn_le H)) hO2s (hL'H.trans (le_normalizer_o2H H))).2
  have hL1 := (cComp_commutator_perfectCore h.comp hO2M hO2s
    (hLH.trans (le_normalizer_o2H H))).2
  have heq : L' = L := by rw [← hL'1, hsup, hL1]
  rw [← heq]
  exact hL'

end Hyp

end CFSG.Quasithin.C213NonQ
