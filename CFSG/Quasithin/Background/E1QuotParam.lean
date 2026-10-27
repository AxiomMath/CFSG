module

public import CFSG.Quasithin.Background.E1Sec7Two
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.E1Param

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique

variable {Q : Type*} [Group Q] [Finite Q]

theorem inEFor_of_quotient_of_minParabolic {T M Y : Subgroup Q} [Y.Normal]
    (h : MinParabolic (⊤ : Subgroup Q) T M) (hYM : Y ≤ M) {i : ℕ}
    (hI : InE i (⊤ : Subgroup (Q ⧸ Y))) : InEFor i ⊤ T := by
  intro Ω hΩ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hT : IsSylowIn 2 T ⊤ := h.isSylow
  have hMtop : M < ⊤ := h.maximal.1
  set W := weakClosure T Ω with hW
  set X : Subgroup Q := eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (W : Set Q)) with hX
  have hNX : ⊤ ⊓ Subgroup.normalizer (W : Set Q) ≤ X := le_sup_right
  have hTX : T ≤ X := fun t ht => hNX ⟨Subgroup.mem_top t, le_normalizer_weakClosure hΩ ht⟩
  by_contra hne
  have hXM : X ≤ M := h.le_of_lt hTX (lt_top_iff_ne_top.mpr hne)
  have hTM : T ≤ M := hTX.trans hXM
  have hMb : ¬ (⊤ : Subgroup (Q ⧸ Y)) ≤ M.map π := by
    intro hle
    have h1 : (⊤ : Subgroup Q) ≤ M := by
      intro x _
      obtain ⟨m, hm, hmx⟩ := hle (Subgroup.mem_top (π x))
      have h2 : m⁻¹ * x ∈ Y := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
      have e : x = m * (m⁻¹ * x) := by group
      rw [e]
      exact M.mul_mem hm (hYM h2)
    exact absurd (lt_of_le_of_lt h1 hMtop) (lt_irrefl _)
  have hTb : IsSylowIn 2 (T.map π) ⊤ := isSylowIn_two_map_top hπs hT
  have hΩb : IsInvColl ⊤ (Subgroup.map π '' Ω) := isInvColl_map_of_surjective π hπs hΩ
  have hIT := hI _ hTb _ hΩb
  have hE : eGen i ⊤ (T.map π) (Subgroup.map π '' Ω) ≤ M.map π := by
    refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_
    obtain ⟨A₀, hA₀, rfl⟩ := hB
    obtain ⟨n, hn, hnA⟩ := exists_mem_conj_le_of_map_le hT
      (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) hBT
    have hAΩ : conjSub n A₀ ∈ Ω := hΩ.conj A₀ hA₀ n (Subgroup.mem_top n)
    have hAT : conjSub n A₀ ≤ T := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      have := hnA _ hy
      rwa [e] at this
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    have hAeq : (conjSub n A₀).map π = A₀.map π := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ conjSub n A₀ := hy
        rw [mem_conjSub_iff] at hy'
        refine ⟨n⁻¹ * y * n, hy', ?_⟩
        simp [hπn]
      · rintro _ ⟨a, ha, rfl⟩
        refine ⟨n * a * n⁻¹, mem_conjSub_of_mem ha, ?_⟩
        simp [hπn]
    have hK' : IsE i ⊤ (T.map π) ((conjSub n A₀).map π) K := by
      rw [hAeq]
      exact hK
    obtain ⟨J, hJ, hJK⟩ := ten_seven hT hAT (hΩ.isElemAbelian _ hAΩ) hK'
    have hJM : J ≤ M := (le_eGen hAΩ hAT hJ).trans (le_sup_left.trans hXM)
    calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := le_twoResidual_sup_of_isSylowIn hK.2.2.1
      _ ≤ (twoResidual J).map π ⊔ T.map π := by
        rw [hJK]
        exact sup_le_sup le_rfl inf_le_left
      _ ≤ M.map π := sup_le (Subgroup.map_mono ((twoResidual_le J).trans hJM))
        (Subgroup.map_mono hTM)
  set Wb := weakClosure (T.map π) (Subgroup.map π '' Ω) with hWb
  have hNb : ∀ x : Q ⧸ Y, x ∈ Subgroup.normalizer (Wb : Set (Q ⧸ Y)) := by
    set N := (Subgroup.normalizer (Wb : Set (Q ⧸ Y))).comap π with hN
    have hTN : T ≤ N := fun t ht =>
      le_normalizer_weakClosure hΩb (Subgroup.mem_map_of_mem π ht)
    have hNM : ¬ N ≤ M := by
      intro hNM
      apply hMb
      rw [← hIT]
      refine sup_le hE ?_
      intro x hx
      obtain ⟨g, rfl⟩ := hπs x
      have hg : g ∈ N := hx.2
      exact ⟨g, hNM hg, rfl⟩
    have hNtop : N = ⊤ := h.eq_of_not_le hTN le_top hNM
    intro x
    obtain ⟨g, rfl⟩ := hπs x
    have hg : g ∈ N := hNtop ▸ Subgroup.mem_top g
    exact hg
  set P := Wb.comap π with hP
  have hPn : ∀ x : Q, x ∈ Subgroup.normalizer (P : Set Q) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.mp (hNb (π x)) (π z)
    simp only [hP, Subgroup.mem_comap, map_mul, map_inv]
    exact this
  have hPnorm : P.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun x _ => hPn x)
  have hPM : P ≤ M := by
    intro x hx
    obtain ⟨t, ht, hte⟩ : π x ∈ T.map π := weakClosure_le hx
    have h2 : t⁻¹ * x ∈ Y := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
    have e : x = t * (t⁻¹ * x) := by group
    rw [e]
    exact M.mul_mem (hTM ht) (hYM h2)
  have hWP : W ≤ P := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_weakClosure ⟨A, hA, rfl⟩ (Subgroup.map_mono hAT)
  have hSyl : IsSylowTwoOf (T ⊓ P) P := hT.inf_normal le_top inferInstance
  have hfr := B6.frattini_two le_top (fun x _ => hPn x) hSyl
  have hTPn : ⊤ ⊓ Subgroup.normalizer ((T ⊓ P : Subgroup Q) : Set Q) = ⊤ := by
    refine h.eq_of_not_le (le_inf le_top fun t ht =>
      mem_normalizer_inf (Subgroup.le_normalizer ht) (hPn t)) le_top ?_
    intro hle
    have : (⊤ : Subgroup Q) ≤ M := hfr.trans (sup_le hPM hle)
    exact absurd (lt_of_le_of_lt this hMtop) (lt_irrefl _)
  have hTPx : ∀ x : Q, x ∈ Subgroup.normalizer ((T ⊓ P : Subgroup Q) : Set Q) := fun x =>
    (hTPn.ge (Subgroup.mem_top x)).2
  have hΩP : ∀ A ∈ Ω, A ≤ T ⊓ P := by
    intro A hA
    obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 (le_top : A ≤ ⊤)
      (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA))
    obtain ⟨g, -, hgS⟩ := B6.isSylowTwoOf_exists_conj hT hS
    have hA' : conjSub g⁻¹ A ∈ Ω := hΩ.conj A hA g⁻¹ (Subgroup.mem_top _)
    have hA'T : conjSub g⁻¹ A ≤ T := by
      intro y hy
      rw [mem_conjSub_iff, inv_inv] at hy
      have h1 : g * y * g⁻¹ ∈ S := hAS hy
      rw [hgS, B6.mem_conjSub] at h1
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [e] at h1
    have h1 : conjSub g⁻¹ A ≤ T ⊓ P := le_inf hA'T ((le_weakClosure hA' hA'T).trans hWP)
    intro a ha
    have h2 : g⁻¹ * a * g ∈ T ⊓ P := by
      apply h1
      rw [mem_conjSub_iff, inv_inv]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rwa [e]
    have h3 := (Subgroup.mem_normalizer_iff.mp (hTPx g) _).mp h2
    have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rwa [e] at h3
  apply hne
  refine eq_top_iff.mpr fun x _ => hNX ⟨Subgroup.mem_top x, ?_⟩
  apply mem_normalizer_weakClosure hΩ
  intro w hw
  have hWTP : W ≤ T ⊓ P := iSup₂_le fun A hA => iSup_le fun _ => hΩP A hA
  exact ((Subgroup.mem_normalizer_iff.mp (hTPx x) w).mp (hWTP hw)).1

theorem nParam_top_le_quotient {T M Y : Subgroup Q} [Y.Normal]
    (h : MinParabolic (⊤ : Subgroup Q) T M) (hYM : Y ≤ M) :
    nParam (⊤ : Subgroup Q) ≤ nParam (⊤ : Subgroup (Q ⧸ Y)) := by
  have hodd : ¬ Odd (Nat.card (⊤ : Subgroup (Q ⧸ Y))) := by
    intro hodd
    have hTb : IsSylowIn 2 (T.map (QuotientGroup.mk' Y)) ⊤ :=
      isSylowIn_two_map_top (QuotientGroup.mk'_surjective Y) h.isSylow
    have h1 := eq_bot_of_isSylowIn_odd hTb hodd
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    have hTY : IsSylowTwoOf T Y := B6.isSylowTwoOf_mono h.isSylow h1 le_top
    have hYn : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (Y : Set Q) := fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top x
    have hfr := B6.frattini_two le_top hYn hTY
    have : (⊤ : Subgroup Q) ≤ M := hfr.trans (sup_le hYM h.inf_normalizer_le)
    exact absurd (lt_of_le_of_lt this h.maximal.1) (lt_irrefl _)
  have e : nParam (⊤ : Subgroup (Q ⧸ Y)) =
      ⨅ i ∈ {i : ℕ | 0 < i ∧ InE i (⊤ : Subgroup (Q ⧸ Y))}, (i : ℕ∞) := by
    unfold nParam
    simp only [hodd, ↓reduceIte]
  rw [e]
  refine le_iInf₂ fun i hi => ?_
  exact (nParam_le_iff hi.1).mpr
    ((inE_iff_inEFor h.isSylow).mpr (inEFor_of_quotient_of_minParabolic h hYM hi.2))

end E1

end CFSG.Quasithin
