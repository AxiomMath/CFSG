module

public import CFSG.Quasithin.H13.L32NLem14331e
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32NLem14331f
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

theorem perm3_words' : ∀ s c x : Equiv.Perm (Fin 3), s * s = 1 → s ≠ 1 → c ^ 3 = 1 → c ≠ 1 →
    x = 1 ∨ x = c ∨ x = c * c ∨ x = s ∨ x = s * c ∨ x = s * (c * c) := by
  decide +kernel

theorem perm3_conj : ∀ c h : Equiv.Perm (Fin 3), c ^ 3 = 1 → c ≠ 1 →
    h⁻¹ * c * h = c ∨ h⁻¹ * c * h = c * c := by
  decide +kernel

theorem c3_pow : c3 ^ 3 = 1 ∧ c3 ≠ 1 := by
  decide

theorem c3_pow_two_pow (j : ℕ) : (c3 ^ 2 ^ j) ^ 3 = 1 ∧ c3 ^ 2 ^ j ≠ 1 := by
  have ho : orderOf c3 = 3 := orderOf_eq_prime c3_pow.1 c3_pow.2
  refine ⟨by rw [← pow_mul, mul_comm, pow_mul, c3_pow.1, one_pow], fun h => ?_⟩
  have h3 := orderOf_dvd_of_pow_eq_one h
  rw [ho] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem pi_mem_span {v : G} (hv : v ∈ V) :
    D.π v ∈ Submodule.span (ZMod 2) {D.π (g⁻¹ * z * g), D.π (z * b)} := by
  by_cases hv1 : v ∈ fsuV1 T V
  · rw [(L128A.HatU.π_eq_zero_iff D (V_le_U hv)).mpr (C.lt.le hv1)]
    exact Submodule.zero_mem _
  · rcases C.pi_mem_plane D hv hv1 with h | h | h <;> rw [h]
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    · exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

theorem caseI_not_fix_alpha (X : CaseI T L V g D e) :
    ¬ ∀ k ∈ kA T V (l⁻¹ * e * l), ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨k, hkN⟩ (D.π (g⁻¹ * z * g)) = D.π (g⁻¹ * z * g) := by
  intro hfix
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have ha := C.conj_mem_zIl X.he
  have haN := C.caseI_a_N D X
  have haH := C.caseI_a_H D X
  have ha1 : l⁻¹ * e * l ≠ 1 := by
    intro h
    apply C.caseI_rho_ne D X
    have : (⟨l⁻¹ * e * l, haN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 :=
      Subtype.ext h
    rw [this, map_one]
  have hkey : ∀ h ∈ l32nH T V, ∀ v ∈ V,
      h * v * h⁻¹ ∈ fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G) := by
    intro h hh v hv
    have hvU : h * v * h⁻¹ ∈ fsuU T V := mem_conjClosure hh hv
    obtain ⟨u₀, hu₀⟩ := (C.comm_eq D X.h14325 X.h1222 X.h12213 X.h12810 X.h12813 ha ha1 haN
      (D.π v)).mpr (C.pi_mem_span D hv)
    have hkH : h * (l⁻¹ * e * l) * h⁻¹ ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem hh haH) ((l32nH T V).inv_mem hh)
    have hkK : h * (l⁻¹ * e * l) * h⁻¹ ∈ kA T V (l⁻¹ * e * l) :=
      mem_conjClosure hh (Subgroup.mem_zpowers _)
    set ρk := D.ρ ⟨h * (l⁻¹ * e * l) * h⁻¹, hN hkH⟩ with hρk
    set ρh := D.ρ ⟨h, hN hh⟩ with hρh
    have e1 : ρk * ρh = ρh * D.ρ ⟨l⁻¹ * e * l, haN⟩ := by
      rw [hρk, hρh, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show h * (l⁻¹ * e * l) * h⁻¹ * h = h * (l⁻¹ * e * l)
      group
    have e2 : D.π (h * v * h⁻¹) = ρk (ρh u₀) - ρh u₀ := by
      have h1 : ρk (ρh u₀) = ρh u₀ + D.π (h * v * h⁻¹) := by
        rw [← LinearEquiv.mul_apply, e1, LinearEquiv.mul_apply, hu₀, map_add, hρh,
          D.ρ_π _ v (V_le_U hv)]
      rw [h1]
      abel
    have hB : D.B (D.π (h * v * h⁻¹)) (D.π (g⁻¹ * z * g)) = 0 := by
      have h1 := L128A.HatU.B_rho D ⟨h * (l⁻¹ * e * l) * h⁻¹, hN hkH⟩ (ρh u₀)
        (D.π (g⁻¹ * z * g))
      rw [← hρk, hfix _ hkK (hN hkH)] at h1
      rw [e2, LinearMap.BilinForm.sub_left, h1, sub_self]
    have hcomm := (D.B_spec _ hvU _ (V_le_U C.a_V)).mp hB
    refine C.mem_W hvU ?_
    calc h * v * h⁻¹ * (g⁻¹ * z * g) =
        h * v * h⁻¹ * (g⁻¹ * z * g) * (h * v * h⁻¹)⁻¹ * (g⁻¹ * z * g)⁻¹ *
          ((g⁻¹ * z * g) * (h * v * h⁻¹)) := by group
      _ = (g⁻¹ * z * g) * (h * v * h⁻¹) := by rw [hcomm, one_mul]
  have hUW : fsuU T V ≤ fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G) :=
    conjClosure_le hkey
  obtain ⟨ua, -, hua, -, -⟩ := C.exists_dual_ab D X.h1222 X.h12213
  obtain ⟨u, hu, rfl⟩ := D.π_surj ua
  have hcomm : u * (g⁻¹ * z * g) * u⁻¹ * (g⁻¹ * z * g)⁻¹ = 1 := by
    rw [← Subgroup.mem_centralizer_iff.mp (hUW hu).2 _ C.a_mem]
    group
  have h0 := (D.B_spec u hu _ (V_le_U C.a_V)).mpr hcomm
  rw [h0] at hua
  exact zero_ne_one hua

theorem caseI_exists_y (X : CaseI T L V g D e) :
    ∃ y ∈ kA T V (l⁻¹ * e * l), y ^ 3 = 1 ∧ y ≠ 1 ∧
      (∀ h ∈ l32nH T V, ∃ k ∈ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V),
        h⁻¹ * y * h = k * y ∨ h⁻¹ * y * h = k * y⁻¹) ∧
      (∃ u ∈ fsuU T V, y * u * y⁻¹ * u⁻¹ ∉ Subgroup.centralizer (V₂ : Set G)) ∧
      y * (g⁻¹ * z * g) * y⁻¹ ≠ g⁻¹ * z * g := by
  obtain ⟨φ, hφ2, hφ1⟩ := C.caseI_exists_phi D X
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKH := C.caseI_K_H D X
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have hHK : l32nH T V ≤ Subgroup.normalizer (K : Set G) := le_normalizer_kA _
  set ψ : ↥(l32nH T V) →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (L14332.imgHom D)) with hψ
  have hψapp : ∀ x : ↥(l32nH T V), ψ x = (φ (L14332.imgHom D x)).1 := fun _ => rfl
  have hsame : ∀ (k : G) (hk : k ∈ K) (w : G) (hw : w ∈ K), ψ ⟨k, hKH hk⟩ = ψ ⟨w, hKH hw⟩ →
      D.ρ ⟨k, hN (hKH hk)⟩ = D.ρ ⟨w, hN (hKH hw)⟩ := by
    intro k hk w hw hkw
    have h1 : φ (L14332.imgHom D ⟨k, hKH hk⟩) = φ (L14332.imgHom D ⟨w, hKH hw⟩) :=
      Prod.ext hkw ((hφ2 k hk (hKH hk)).trans (hφ2 w hw (hKH hw)).symm)
    have h2 := congrArg Subtype.val (φ.injective h1)
    rwa [L14332.imgHom_apply, L14332.imgHom_apply] at h2
  have hKC : K ⊓ l32nCHat T V ≤ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) := by
    rw [X.hQ]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hKH)
      ((le_inf hHK (le_normalizer_cHat D)).trans Subgroup.inf_normalizer_le_normalizer_inf)
      fun x => ?_
    obtain ⟨n, hn⟩ := exists_two_pow_of_odd (S := K ⊓ l32nCHat T V)
      (fun c hc hco => C.eq_one_of_mem_cHat X.hQ (C.caseI_K_Z D X) hc.1 hc.2 hco) x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hker : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = 1 → k ∈ l32nCHat T V := by
    intro k hk h1
    have h2 : φ (L14332.imgHom D ⟨k, hKH hk⟩) = 1 := Prod.ext h1 (hφ2 k hk (hKH hk))
    have h3 := congrArg Subtype.val (φ.injective (h2.trans φ.map_one.symm))
    rw [L14332.imgHom_apply] at h3
    exact (L14332.rho_eq_one_iff_mem (D := D) (hKH hk) (hN (hKH hk))).mp h3
  obtain ⟨y₀, hy₀K, hy₀H, hy₀⟩ := hφ1 c3
  have hy₀ψ : ψ ⟨y₀, hKH hy₀K⟩ = c3 := hy₀
  have hpowψ : ∀ (k : G) (hk : k ∈ l32nH T V) (n : ℕ),
      ψ ⟨k ^ n, (l32nH T V).pow_mem hk n⟩ = ψ ⟨k, hk⟩ ^ n := by
    intro k hk n
    rw [← map_pow]
    rfl
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (y₀ ^ 3) ^ 2 ^ j = 1 := by
    obtain ⟨j, hj⟩ := exists_two_pow_of_odd (S := K ⊓ l32nCHat T V)
      (fun c hc hco => C.eq_one_of_mem_cHat X.hQ (C.caseI_K_Z D X) hc.1 hc.2 hco)
      (⟨K.pow_mem hy₀K 3, hker _ (K.pow_mem hy₀K 3) (by
        rw [hpowψ y₀ (hKH hy₀K), hy₀ψ]; exact c3_pow.1)⟩ : y₀ ^ 3 ∈ K ⊓ l32nCHat T V)
    exact ⟨j, hj⟩
  set y := y₀ ^ 2 ^ j with hy
  have hyK : y ∈ K := K.pow_mem hy₀K _
  have hyH := hKH hyK
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul]
    exact hj
  have hyψ : ψ ⟨y, hyH⟩ = c3 ^ 2 ^ j := by
    rw [show (⟨y, hyH⟩ : ↥(l32nH T V)) = ⟨y₀ ^ 2 ^ j, (l32nH T V).pow_mem (hKH hy₀K) _⟩ from rfl,
      hpowψ y₀ (hKH hy₀K), hy₀ψ]
  obtain ⟨hc3, hc1⟩ := c3_pow_two_pow j
  have hy1 : y ≠ 1 := by
    intro h
    apply hc1
    rw [← hyψ]
    have : (⟨y, hyH⟩ : ↥(l32nH T V)) = 1 := Subtype.ext h
    rw [this, map_one]
  refine ⟨y, hyK, hy3, hy1, fun h hh => ?_, ?_⟩
  ·
    have hcK : h⁻¹ * y * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hHK ((l32nH T V).inv_mem hh)) y).mp hyK
      rwa [inv_inv] at this
    have hcψ : ψ ⟨h⁻¹ * y * h, hKH hcK⟩ = (ψ ⟨h, hh⟩)⁻¹ * ψ ⟨y, hyH⟩ * ψ ⟨h, hh⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hyψ] at hcψ
    have hy2K : y * y ∈ K := K.mul_mem hyK hyK
    rcases perm3_conj _ (ψ ⟨h, hh⟩) hc3 hc1 with h1 | h1
    ·
      have hk : h⁻¹ * y * h * y⁻¹ ∈ K := K.mul_mem hcK (K.inv_mem hyK)
      refine ⟨h⁻¹ * y * h * y⁻¹, hKC ⟨hk, ?_⟩, Or.inl (by group)⟩
      refine hker _ hk ?_
      have e1 : (⟨h⁻¹ * y * h * y⁻¹, hKH hk⟩ : ↥(l32nH T V)) =
          ⟨h⁻¹ * y * h, hKH hcK⟩ * (⟨y, hyH⟩)⁻¹ := rfl
      rw [e1, map_mul, map_inv, hcψ, h1, hyψ, mul_inv_cancel]
    ·
      have hk : h⁻¹ * y * h * y ∈ K := K.mul_mem hcK hyK
      refine ⟨h⁻¹ * y * h * y, hKC ⟨hk, ?_⟩, Or.inr (by group)⟩
      refine hker _ hk ?_
      have e1 : (⟨h⁻¹ * y * h * y, hKH hk⟩ : ↥(l32nH T V)) =
          ⟨h⁻¹ * y * h, hKH hcK⟩ * ⟨y, hyH⟩ := rfl
      rw [e1, map_mul, hcψ, h1, hyψ, ← pow_three']
      exact hc3
  ·
    have hyN := hN hyH
    set ρy := D.ρ ⟨y, hyN⟩ with hρy
    set α := D.π (g⁻¹ * z * g) with hα
    have hyα_ne : ρy α ≠ α := by
      intro hyα
      have hεK : l⁻¹ * e * l ∈ K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
      have hεN := hN (hKH hεK)
      have hεα : D.ρ ⟨l⁻¹ * e * l, hεN⟩ α = α :=
        (C.rho_fix D X.h1222 X.h12213 X.h12810 X.h12813 (C.conj_mem_zIl X.he) _).1
      have hs2 : ψ ⟨_, hKH hεK⟩ * ψ ⟨_, hKH hεK⟩ = 1 := by
        rw [← map_mul]
        have : (⟨l⁻¹ * e * l, hKH hεK⟩ : ↥(l32nH T V)) * ⟨l⁻¹ * e * l, hKH hεK⟩ = 1 :=
          Subtype.ext (by
            show l⁻¹ * e * l * (l⁻¹ * e * l) = 1
            rw [show l⁻¹ * e * l * (l⁻¹ * e * l) = l⁻¹ * (e * e) * l by group, X.he2]
            group)
        rw [this, map_one]
      have hs1 : ψ ⟨_, hKH hεK⟩ ≠ 1 := by
        intro h1
        apply C.caseI_rho_ne D X
        exact (L14332.rho_eq_one_iff_mem (D := D) (hKH hεK) _).mpr (hker _ hεK h1)
      have hmul : ∀ {w₁ w₂ : G} (h₁ : w₁ ∈ Subgroup.normalizer (fsuU T V : Set G))
          (h₂ : w₂ ∈ Subgroup.normalizer (fsuU T V : Set G)), D.ρ ⟨w₁, h₁⟩ α = α →
          D.ρ ⟨w₂, h₂⟩ α = α → D.ρ ⟨w₁ * w₂, Subgroup.mul_mem _ h₁ h₂⟩ α = α := by
        intro w₁ w₂ h₁ h₂ e₁ e₂
        have : (⟨w₁ * w₂, Subgroup.mul_mem _ h₁ h₂⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
            ⟨w₁, h₁⟩ * ⟨w₂, h₂⟩ := rfl
        rw [this, map_mul, LinearEquiv.mul_apply, e₂, e₁]
      have hψmul : ∀ {w₁ w₂ : G} (h₁ : w₁ ∈ l32nH T V) (h₂ : w₂ ∈ l32nH T V),
          ψ ⟨w₁ * w₂, (l32nH T V).mul_mem h₁ h₂⟩ = ψ ⟨w₁, h₁⟩ * ψ ⟨w₂, h₂⟩ := by
        intro w₁ w₂ h₁ h₂
        rw [← map_mul]
        rfl
      apply C.caseI_not_fix_alpha D X
      intro k hk hkN
      have hc3' : ψ ⟨y, hyH⟩ ^ 3 = 1 := by rw [hyψ]; exact hc3
      have hc1' : ψ ⟨y, hyH⟩ ≠ 1 := by rw [hyψ]; exact hc1
      have hyyK : y * y ∈ K := K.mul_mem hyK hyK
      rcases perm3_words' _ _ (ψ ⟨k, hKH hk⟩) hs2 hs1 hc3' hc1' with h1 | h1 | h1 | h1 | h1 | h1
      · rw [(L14332.rho_eq_one_iff_mem (D := D) (hKH hk) hkN).mpr (hker k hk h1)]
        rfl
      · rw [show D.ρ ⟨k, hkN⟩ = D.ρ ⟨y, hyN⟩ from hsame k hk y hyK h1]
        exact hyα
      · rw [show D.ρ ⟨k, hkN⟩ = D.ρ ⟨y * y, Subgroup.mul_mem _ hyN hyN⟩ from
          hsame k hk (y * y) hyyK (by rw [h1, ← hψmul])]
        exact hmul hyN hyN hyα hyα
      · rw [show D.ρ ⟨k, hkN⟩ = D.ρ ⟨l⁻¹ * e * l, hεN⟩ from hsame k hk _ hεK h1]
        exact hεα
      · rw [show D.ρ ⟨k, hkN⟩ = D.ρ ⟨l⁻¹ * e * l * y, Subgroup.mul_mem _ hεN hyN⟩ from
          hsame k hk _ (K.mul_mem hεK hyK) (by rw [h1, ← hψmul])]
        exact hmul hεN hyN hεα hyα
      · rw [show D.ρ ⟨k, hkN⟩ = D.ρ ⟨l⁻¹ * e * l * (y * y),
            Subgroup.mul_mem _ hεN (Subgroup.mul_mem _ hyN hyN)⟩ from
          hsame k hk _ (K.mul_mem hεK hyyK) (by rw [h1, ← hψmul, ← hψmul])]
        exact hmul hεN (Subgroup.mul_mem _ hyN hyN) hεα (hmul hyN hyN hyα hyα)
    refine ⟨?_, ?_⟩
    ·
      by_contra hall
      push Not at hall
      have hBy : ∀ w : D.V, D.B (ρy w) α = D.B w α := by
        intro w
        obtain ⟨u, hu, rfl⟩ := D.π_surj w
        have hcU : y * u * y⁻¹ * u⁻¹ ∈ fsuU T V :=
          (fsuU T V).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN u).mp hu) ((fsuU T V).inv_mem hu)
        have hc := hall u hu
        have h0 : D.B (D.π (y * u * y⁻¹ * u⁻¹)) α = 0 := by
          refine (D.B_spec _ hcU _ (V_le_U C.a_V)).mpr ?_
          rw [← Subgroup.mem_centralizer_iff.mp hc _ C.a_mem]
          group
        rw [← L128A.HatU.rho_sub_π D hyN hu, LinearMap.BilinForm.sub_left, sub_eq_zero] at h0
        exact h0
      have hyα : ρy α = α := by
        have h1 : ∀ w : D.V, D.B w (ρy α - α) = 0 := by
          intro w
          have h2 := L128A.HatU.B_rho D ⟨y, hyN⟩ (ρy.symm w) α
          rw [← hρy, LinearEquiv.apply_symm_apply] at h2
          rw [LinearMap.BilinForm.sub_right, h2, ← hBy (ρy.symm w), LinearEquiv.apply_symm_apply,
            sub_self]
        have h3 := L128A.HatU.B_nondegenerate D (ρy α - α) fun w => by
          rw [L128A.HatU.B_symm D]
          exact h1 w
        exact sub_eq_zero.mp h3
      exact hyα_ne hyα
    · intro h
      apply hyα_ne
      rw [hρy, hα, D.ρ_π ⟨y, hyN⟩ _ (V_le_U C.a_V), h]

end Ctx

end L14328

end CFSG.Quasithin.H13
