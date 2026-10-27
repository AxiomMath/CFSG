module

public import CFSG.Quasithin.Background.SmithC27RJ

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section General

variable {Γ : Type} [Group Γ]

private theorem isSylowTwoOf_of_ge {Q S C : Subgroup Γ} (hQ : IsSylowTwoOf Q C) (hQS : Q ≤ S)
    (hSC : S ≤ C) (hS : IsPGroup 2 S) : IsSylowTwoOf S C :=
  ⟨hSC, hS, fun h2 => hQ.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left C hQS))⟩

private theorem isSylowTwoOf_of_isSylowTwoOf_le {S Y X T : Subgroup Γ} (hS : IsSylowTwoOf S Y)
    (hYX : Y ≤ X) (hT : IsSylowTwoOf T X) (hTY : T ≤ Y) : IsSylowTwoOf S X := by
  refine ⟨hS.1.trans hYX, hS.2.1, fun h2 => ?_⟩
  have e1 := Subgroup.relIndex_mul_relIndex S Y X hS.1 hYX
  have e2 := Subgroup.relIndex_mul_relIndex T Y X hTY hYX
  have h2' : 2 ∣ S.relIndex Y * Y.relIndex X := by
    rw [e1]
    exact h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2' with h | h
  · exact hS.2.2 h
  · apply hT.2.2
    show 2 ∣ T.relIndex X
    rw [← e2]
    exact Dvd.dvd.mul_left h _

variable [Finite Γ]

private theorem exists_sylow_le_normalizer_core {Xs Ks Rs Ms Ns S : Subgroup Γ}
    (hXK : Xs ≤ Subgroup.normalizer (Ks : Set Γ)) (hKX : Ks ≤ Xs) (hXs : Xs ≤ Ks ⊔ Rs)
    (hRN : Rs ≤ Ns) (hNM : Ns ≤ Ms) (hMN : Ms ≤ Subgroup.normalizer (Ns : Set Γ))
    (hMX : Ms ≤ Xs) (hRsyl : IsSylowTwoOf Rs Ns) (hS : IsSylowTwoOf S Ks) (hSM : S ≤ Ms)
    (hDn : Ms ⊓ Ks ≤ Subgroup.normalizer ((Rs ⊓ Ks : Subgroup Γ) : Set Γ)) :
    ∃ T : Subgroup Γ, IsSylowTwoOf T Xs ∧ T ≤ Subgroup.normalizer (Rs : Set Γ) := by
  have hRM : Rs ≤ Ms := hRN.trans hNM
  have hRX : Rs ≤ Xs := hRM.trans hMX
  have hLM : Ns ⊓ Ks ≤ Ms ⊓ Ks := inf_le_inf_right _ hNM
  have hNL : Ns ≤ Subgroup.normalizer ((Ns ⊓ Ks : Subgroup Γ) : Set Γ) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hXK (hMX (hNM hx))⟩
  have hDL : IsSylowTwoOf (Rs ⊓ Ks) (Ns ⊓ Ks) := by
    have h1 := A4.isSylowTwoOf_inf_normal hRsyl inf_le_left hNL
    have e : Rs ⊓ (Ns ⊓ Ks) = Rs ⊓ Ks := by rw [← inf_assoc, inf_eq_left.2 hRN]
    rwa [e] at h1
  have hkey : ∀ P : Subgroup Γ, P ≤ Ns ⊓ Ks → IsPGroup 2 P → P ≤ Rs ⊓ Ks := by
    intro P hPL hP2
    have h1 : IsPGroup 2 ↥((Rs ⊓ Ks) ⊔ P) :=
      IsPGroup.to_sup_of_normal_left' hDL.2.1 hP2 ((hPL.trans hLM).trans hDn)
    exact le_sup_right.trans
      ((A4.isSylowTwoOf_iff_maximal.1 hDL).2.2 _ (sup_le hDL.1 hPL) h1 le_sup_left)
  have hRMK : Rs ≤ Subgroup.normalizer ((Ms ⊓ Ks : Subgroup Γ) : Set Γ) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hRM hx), hXK (hRX hx)⟩
  have hWN : (Ms ⊓ Ks) ⊔ Rs ≤ Subgroup.normalizer ((Ms ⊓ Ks : Subgroup Γ) : Set Γ) :=
    sup_le Subgroup.le_normalizer hRMK
  obtain ⟨T₁, hT₁, hRT₁⟩ :=
    A4.exists_isSylowTwoOf_ge (le_sup_right : Rs ≤ (Ms ⊓ Ks) ⊔ Rs) hRsyl.2.1
  have hU : IsSylowTwoOf (T₁ ⊓ (Ms ⊓ Ks)) (Ms ⊓ Ks) :=
    A4.isSylowTwoOf_inf_normal hT₁ le_sup_left hWN
  have hUK : IsSylowTwoOf (T₁ ⊓ (Ms ⊓ Ks)) Ks :=
    isSylowTwoOf_of_isSylowTwoOf_le hU inf_le_right hS (le_inf hSM hS.1)
  have hUR : T₁ ⊓ (Ms ⊓ Ks) ≤ Subgroup.normalizer (Rs : Set Γ) := by
    rintro u ⟨huT, huM, huK⟩
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hcK : u * r * u⁻¹ * r⁻¹ ∈ Ks := by
      have h1 : r * u⁻¹ * r⁻¹ ∈ Ks :=
        (Subgroup.mem_normalizer_iff.1 (hXK (hRX hr)) u⁻¹).1 (Ks.inv_mem huK)
      have e : u * r * u⁻¹ * r⁻¹ = u * (r * u⁻¹ * r⁻¹) := by group
      rw [e]
      exact Ks.mul_mem huK h1
    have hcN : u * r * u⁻¹ * r⁻¹ ∈ Ns :=
      Ns.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMN huM) r).1 (hRN hr)) (Ns.inv_mem (hRN hr))
    have hcT : u * r * u⁻¹ * r⁻¹ ∈ T₁ :=
      T₁.mul_mem (T₁.mul_mem (T₁.mul_mem huT (hRT₁ hr)) (T₁.inv_mem huT)) (T₁.inv_mem (hRT₁ hr))
    have hcD : u * r * u⁻¹ * r⁻¹ ∈ Rs ⊓ Ks :=
      hkey ((Ns ⊓ Ks) ⊓ T₁) inf_le_left (hT₁.2.1.to_le inf_le_right) ⟨⟨hcN, hcK⟩, hcT⟩
    have e : u * r * u⁻¹ = (u * r * u⁻¹ * r⁻¹) * r := by group
    rw [e]
    exact Rs.mul_mem hcD.1 hr
  have hT2 : IsPGroup 2 ↥((T₁ ⊓ (Ms ⊓ Ks)) ⊔ Rs) := hT₁.2.1.to_le (sup_le inf_le_left hRT₁)
  have hTX : (T₁ ⊓ (Ms ⊓ Ks)) ⊔ Rs ≤ Xs := sup_le (hUK.1.trans hKX) hRX
  have hTK : IsSylowTwoOf (((T₁ ⊓ (Ms ⊓ Ks)) ⊔ Rs) ⊓ Ks) Ks :=
    isSylowTwoOf_of_ge hUK (le_inf le_sup_left hUK.1) inf_le_right (hT2.to_le inf_le_left)
  have h1 := isSylowTwoOf_sup_of_le_normalizer' (hTX.trans hXK) hT2 hTK
  have e : Ks ⊔ ((T₁ ⊓ (Ms ⊓ Ks)) ⊔ Rs) = Xs :=
    le_antisymm (sup_le hKX hTX) (hXs.trans (sup_le_sup_left le_sup_right _))
  rw [e] at h1
  exact ⟨_, h1, sup_le hUR Subgroup.le_normalizer⟩

end General

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem exists_sylow_le_normalizer_of_star (hs : StarHyp R K V) {T' : Subgroup (MulAut ↥V)}
    (hT' : IsSylowTwoOf T' (autOn (K ⊔ R) V))
    (hT'R : T' ≤ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) :
    ∃ T : Subgroup G, IsSylowTwoOf T (K ⊔ R) ∧ T ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := hs.le_normalizer_V
  have hYX : (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ K ⊔ R := inf_le_left
  have hQY : pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (pCoreOf_le 2 _) (hs.core.trans Subgroup.le_normalizer)
  obtain ⟨T, hT, hQT⟩ := A4.exists_isSylowTwoOf_ge hQY (pCoreOf_isPGroup 2 _)
  have hTC : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) :=
    isSylowTwoOf_of_ge hs.centralizer_isSylow (le_inf hQT hs.pCore_le_centralizer)
      (inf_le_inf_right _ (hT.1.trans hYX)) (hT.2.1.to_le inf_le_left)
  have hTCY : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.centralizer (V : Set G)) :=
    A4.isSylowTwoOf_mono hTC (inf_le_inf_right _ hT.1) (inf_le_inf_right _ hYX)
  have hTY := (isSylowTwoOf_iff_autOn (hYX.trans hXN) hT.1 hT.2.1 hTCY).1 hT
  have hRC : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hs.pCore_eq_inf]
    exact hs.centralizer_isSylow
  have hT'Y : T' ≤ autOn ((K ⊔ R) ⊓ Subgroup.normalizer (R : Set G)) V :=
    (le_inf hT'.1 hT'R).trans (autOn_inf_normalizer_le hXN le_sup_right hs.pgroup hRC)
  have hTX := isSylowTwoOf_of_isSylowTwoOf_le hTY (autOn_mono' hYX) hT' hT'Y
  exact ⟨T, (isSylowTwoOf_iff_autOn hXN (hT.1.trans hYX) hT.2.1 hTC).2 hTX,
    hT.1.trans inf_le_right⟩

theorem exists_sylow_le_normalizer_R (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hP : IsParabolic2 (autOn K V) (autOn (M ⊓ K) V))
    (hO : pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V) :
    ∃ T : Subgroup G, IsSylowTwoOf T (K ⊔ R) ∧ T ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRM : R ≤ M ⊓ (K ⊔ R) := le_inf h.R_le_M le_sup_right
  have hNM : conjClosure R (M ⊓ (K ⊔ R)) ≤ M ⊓ (K ⊔ R) :=
    conjClosure_le fun x hx r hr =>
      (M ⊓ (K ⊔ R)).mul_mem ((M ⊓ (K ⊔ R)).mul_mem hx (hRM hr)) ((M ⊓ (K ⊔ R)).inv_mem hx)
  have hNX : conjClosure R (M ⊓ (K ⊔ R)) ≤ K ⊔ R := hNM.trans inf_le_right
  have hRC : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hs.pCore_eq_inf]
    exact hs.centralizer_isSylow
  have hRsyl : IsSylowTwoOf (autOn R V) (autOn (conjClosure R (M ⊓ (K ⊔ R))) V) :=
    (isSylowTwoOf_iff_autOn (hNX.trans hs.le_normalizer_V) (le_conjClosure R _) hs.pgroup
      (A4.isSylowTwoOf_mono hRC (inf_le_inf_right _ (le_conjClosure R _))
        (inf_le_inf_right _ hNX))).1 h.isSylowTwoOf_conjClosure
  have hMK := hs.autOn_inf_M h.R_le_M
  obtain ⟨-, S, hS, hSN⟩ := hP
  have hSMK : S ≤ autOn (M ⊓ K) V := fun x hx => hSN ⟨hS.1 hx, Subgroup.le_normalizer hx⟩
  have hDn : autOn (M ⊓ K) V ≤ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V)) := by
    rw [← hO]
    exact le_normalizer_pCoreOf 2 _
  rw [hMK] at hSMK hDn
  rw [← hs.autOn_inf_R] at hDn
  obtain ⟨T', hT', hT'R⟩ := exists_sylow_le_normalizer_core hs.normalizes
    (autOn_mono' le_sup_left) hs.autOn_sup.le (autOn_mono' (le_conjClosure R _))
    (autOn_mono' hNM) (autOn_le_normalizer_autOn (le_normalizer_conjClosure R _))
    (autOn_mono' inf_le_right) hRsyl hS (hSMK.trans inf_le_left) hDn
  exact exists_sylow_le_normalizer_of_star hs hT' hT'R

theorem isMSPair_of (h : Hyp27 H R M K)
    (hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hT : ∃ T : Subgroup G, IsSylowTwoOf T (K ⊔ R) ∧ T ≤ Subgroup.normalizer (R : Set G)) :
    IsMSPair (K ⊔ R) R := by
  obtain ⟨T, hT, hTN⟩ := hT
  refine ⟨⟨h.hypC23_sup.sqtk, h.charTwo_sup, K, h.mem_cComp_sup, h.coe_sup, hr⟩,
    Or.inl ⟨(K ⊔ R) ⊓ Subgroup.normalizer (R : Set G), ?_, ?_, h.isTwoRadicalIn_sup.2.2⟩, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun heq => h.not_le ?_
    intro k hk
    have hk' : k ∈ (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) := by
      rw [heq]
      exact Subgroup.mem_sup_left hk
    exact h.inf_normalizer_le ⟨h.K_le hk, hk'.2⟩
  · exact fun h2 => hT.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left _ (le_inf hT.1 hTN)))
  · intro C hCR hC1 hCh hXC
    apply h.not_le
    intro k hk
    exact h.hyp.cgs (inf_normalizer_le_cgsIn_of_char hCR hC1 hCh
      ⟨h.K_le hk, hXC (Subgroup.mem_sup_left hk)⟩)

theorem maxParabolic_of (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hBT : IsRadicalParabolic (autOn K V)) (hMax : MaxParabolicMaximal (autOn K V))
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) :
    IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧
      pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDK : autOn (R ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  have hO := pCore_autOn_inf_normalizer_D h hs
  have hPar := hBT (autOn (R ⊓ K) V) hDK (autOn_D_ne_bot h hs hJ)
    (isPGroup_autOn (h.isPGroup.to_le inf_le_left)) hO
  have hPM : autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V)) ≤
      autOn (M ⊓ K) V := by
    rw [← autOn_inf_normalizer_D hs]
    exact autOn_mono' (le_inf (inf_normalizer_D_le_M h hs hJ) inf_le_left)
  have hnB : ¬ IsBorelIn (autOn K V)
      (autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V))) := by
    rintro ⟨S, hS, hB⟩
    apply hnS
    refine isSylowTwoOf_R_of_sylow_le hs hS ?_
    have h1 : S ≤ pCoreOf 2
        (autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V))) := by
      rw [hB]
      exact le_pCoreOf_of_le_normalizer 2 (le_inf hS.1 Subgroup.le_normalizer) inf_le_right
        hS.2.1
    rw [hO] at h1
    exact h1.trans (autOn_mono' inf_le_left)
  have hMK : autOn (M ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  have hPne : autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V)) ≠
      autOn K V := fun he => autOn_MK_ne h hs (le_antisymm hMK (he ▸ hPM))
  obtain ⟨hmax, hY⟩ := hMax _ hPar hnB hPne
  have he := hY _ hPM (autOn_MK_ne h hs) hMK
  rw [he]
  exact ⟨hmax, hO⟩

end CFSG.Quasithin.SmithC27
