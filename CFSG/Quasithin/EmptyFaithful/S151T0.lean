module

public import CFSG.Quasithin.EmptyFaithful.S151U3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped commutatorElement

variable {G : Type} [Group G]

theorem s151t_sl3_schur (v w : Vt 3) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ g : SLt 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = w) : w = v := by
  revert v w
  decide +kernel

theorem s151t_β_eq_iff {L : Subgroup G} {e : ↥L →* SLt 3} {β : ↥(blockU L) →* Multiplicative (Vt 3)}
    (hs : LnStr L e β) (x y : ↥(blockU L)) : β x = β y ↔ (x : G)⁻¹ * (y : G) ∈ blockZ L := by
  have key : β x = β y ↔ β (x⁻¹ * y) = 1 := by
    constructor
    · intro h
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    · intro h
      rw [map_mul, map_inv] at h
      exact inv_mul_eq_one.mp h
  rw [key, ← MonoidHom.mem_ker, hs.βker, Subgroup.mem_subgroupOf]
  rfl

theorem s151t_e_eq_one {L : Subgroup G} {e : ↥L →* SLt 3} {β : ↥(blockU L) →* Multiplicative (Vt 3)}
    (hs : LnStr L e β) {x : G} (hxL : x ∈ L) (hx : x ∈ pCoreOf 2 L) : e ⟨x, hxL⟩ = 1 := by
  have h1 : ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := s151u_mk_eq_one_iff.mpr hx
  have h2 := QuotientGroup.eq_one_iff _ |>.mp h1
  rw [← hs.ker] at h2
  exact h2

theorem s151t_conj_mod_Z {L L' : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hsh : IsShort2 L) (hs : LnStr L e β)
    (hN : L' ≤ Subgroup.normalizer (L : Set G)) (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L)
    {l' : G} (hl' : l' ∈ L') {u : G} (hu : u ∈ blockU L) :
    l' * u * l'⁻¹ * u⁻¹ ∈ blockZ L := by
  have hl'N : l' ∈ Subgroup.normalizer (L : Set G) := hN hl'
  have hU : ∀ x ∈ blockU L, l' * x * l'⁻¹ ∈ blockU L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (s151v_normalizer_le_normalizer_blockU L hl'N) x).mp hx
  have hZ : ∀ x ∈ blockZ L, l' * x * l'⁻¹ ∈ blockZ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (s151v_normalizer_le_normalizer_blockZ L hl'N) x).mp hx
  have hZ' : ∀ x ∈ blockZ L, l'⁻¹ * x * l' ∈ blockZ L := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp
      (s151v_normalizer_le_normalizer_blockZ L (inv_mem hl'N)) x).mp hx
    simpa using this
  have hu₁ : l' * u * l'⁻¹ ∈ blockU L := hU u hu
  let uU : ↥(blockU L) := ⟨u, hu⟩
  let uU₁ : ↥(blockU L) := ⟨l' * u * l'⁻¹, hu₁⟩
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := fun z hz l hl => s151v_blockZ_comm hz hl
  by_cases hv : Multiplicative.toAdd (β uU) = 0
  ·
    have h1 : β uU = 1 := toAdd_eq_zero.mp hv
    have hu0 : u ∈ blockZ L := by
      have := (s151t_β_eq_iff hs 1 uU).mpr
      have h2 : β 1 = β uU := by rw [h1, map_one]
      have h3 := (s151t_β_eq_iff hs 1 uU).mp h2
      simpa using h3
    exact (blockZ L).mul_mem (hZ u hu0) ((blockZ L).inv_mem hu0)
  · have hw : Multiplicative.toAdd (β uU₁) ≠ 0 := by
      intro hw0
      apply hv
      have h1 : β uU₁ = 1 := toAdd_eq_zero.mp hw0
      have h2 : β 1 = β uU₁ := by rw [h1, map_one]
      have h3 := (s151t_β_eq_iff hs 1 uU₁).mp h2
      have h4 : l' * u * l'⁻¹ ∈ blockZ L := by simpa using h3
      have h5 := hZ' _ h4
      have h6 : u ∈ blockZ L := by simpa [mul_assoc] using h5
      have h7 : β uU = 1 := by
        have := (s151t_β_eq_iff hs 1 uU).mpr (by simpa using h6)
        rw [← this, map_one]
      rw [h7]
      rfl
    have hfix : ∀ g : SLt 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd (β uU)) = Multiplicative.toAdd (β uU) →
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β uU₁)) =
          Multiplicative.toAdd (β uU₁) := by
      intro g hg
      obtain ⟨l, hl⟩ := hs.surj g
      have hlL : (l : G) ∈ L := l.2
      have hu' : (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L hlL) u).mp hu
      let uU' : ↥(blockU L) := ⟨(l : G) * u * (l : G)⁻¹, hu'⟩
      have e1 : Multiplicative.toAdd (β uU') = Multiplicative.toAdd (β uU) := by
        rw [hs.equiv l uU uU' rfl, hl]
        exact hg
      have e2 : β uU' = β uU := by
        have := congrArg Multiplicative.ofAdd e1
        simpa using this
      have e3 := (s151t_β_eq_iff hs uU uU').mp e2.symm
      have hu'₁ : l' * ((l : G) * u * (l : G)⁻¹) * l'⁻¹ ∈ blockU L := hU _ hu'
      let uU'₁ : ↥(blockU L) := ⟨l' * ((l : G) * u * (l : G)⁻¹) * l'⁻¹, hu'₁⟩
      have e4 : β uU'₁ = β uU₁ := by
        symm
        apply (s151t_β_eq_iff hs uU₁ uU'₁).mpr
        have : (uU₁ : G)⁻¹ * (uU'₁ : G) =
            l' * (u⁻¹ * ((l : G) * u * (l : G)⁻¹)) * l'⁻¹ := by
          show (l' * u * l'⁻¹)⁻¹ * (l' * ((l : G) * u * (l : G)⁻¹) * l'⁻¹) = _
          group
        rw [this]
        exact hZ _ (by simpa using e3)
      have hℓL : l' * (l : G) * l'⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hl'N (l : G)).mp hlL
      let ℓ : ↥L := ⟨l' * (l : G) * l'⁻¹, hℓL⟩
      have e5 : (uU'₁ : G) = (ℓ : G) * (uU₁ : G) * (ℓ : G)⁻¹ := by
        show l' * ((l : G) * u * (l : G)⁻¹) * l'⁻¹ =
          (l' * (l : G) * l'⁻¹) * (l' * u * l'⁻¹) * (l' * (l : G) * l'⁻¹)⁻¹
        group
      have e6 := hs.equiv ℓ uU₁ uU'₁ e5
      have hcomm : l' * (l : G) * l'⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L := by
        have h1 : ⁅(l : G), l'⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hlL hl'
        have h2 := hc h1
        have h3 := (pCoreOf 2 L).inv_mem h2
        have : ⁅(l : G), l'⁆⁻¹ = l' * (l : G) * l'⁻¹ * (l : G)⁻¹ := by
          simp only [commutatorElement_def]; group
        rwa [this] at h3
      have hcL : l' * (l : G) * l'⁻¹ * (l : G)⁻¹ ∈ L := L.mul_mem hℓL (L.inv_mem hlL)
      have e7 : e ⟨l' * (l : G) * l'⁻¹ * (l : G)⁻¹, hcL⟩ = 1 := s151t_e_eq_one hs hcL hcomm
      have e8 : e ℓ = g := by
        have : ℓ = ⟨l' * (l : G) * l'⁻¹ * (l : G)⁻¹, hcL⟩ * l := by
          apply Subtype.ext
          show l' * (l : G) * l'⁻¹ = l' * (l : G) * l'⁻¹ * (l : G)⁻¹ * (l : G)
          group
        rw [this, map_mul, e7, one_mul, hl]
      rw [e8, e4] at e6
      exact e6.symm
    have hvv := hv
    have hw' := s151t_sl3_schur _ _ hvv hw hfix
    have h1 : β uU₁ = β uU := by
      have := congrArg Multiplicative.ofAdd hw'
      simpa using this
    have h2 := (s151t_β_eq_iff hs uU uU₁).mp h1.symm
    have h3 : (uU : G)⁻¹ * (uU₁ : G) = u⁻¹ * (l' * u * l'⁻¹) := rfl
    rw [h3] at h2
    have h4 : l' * u * l'⁻¹ * u⁻¹ = u * (u⁻¹ * (l' * u * l'⁻¹)) * u⁻¹ := by group
    rw [h4]
    have hu0L : u ∈ L := s151v_blockU_le_L hsh hu
    rw [hZc _ h2 u hu0L]
    exact h2

theorem s151t_blocks_commute [Finite G] {L L' : Subgroup G} (h3 : IsLnBlock L 3)
    (hLperf : ⁅L, L⁆ = L) (hL'perf : ⁅L', L'⁆ = L')
    (hLN : L ≤ Subgroup.normalizer (L' : Set G)) (hL'N : L' ≤ Subgroup.normalizer (L : Set G))
    (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L) : ⁅L, L'⁆ = ⊥ := by
  obtain ⟨e, β, hs⟩ := exists_lnStr h3
  have hsh : IsShort2 L := h3.1
  have hc0 := hc
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G, X = ⁅L, L'⁆ := ⟨_, rfl⟩
  rw [← hXdef] at hc ⊢
  have hX' : ⁅L', L⁆ = X := by rw [hXdef]; exact Subgroup.commutator_comm L' L
  have hXL : L ≤ Subgroup.normalizer (X : Set G) := fun x hx => by
    rw [hXdef]; exact normalizer_commutator (Subgroup.le_normalizer hx) (hLN hx)
  have hXL' : L' ≤ Subgroup.normalizer (X : Set G) := fun x hx => by
    rw [hXdef]; exact normalizer_commutator (hL'N hx) (Subgroup.le_normalizer hx)
  have hN₁L : L ≤ Subgroup.normalizer ((⁅X, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hXL hx) (Subgroup.le_normalizer hx)
  have hN₁L' : L' ≤ Subgroup.normalizer ((⁅X, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hXL' hx) (hL'N hx)
  have hN₂L : L ≤ Subgroup.normalizer ((⁅X, L'⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hXL hx) (hLN hx)
  have hN₂L' : L' ≤ Subgroup.normalizer ((⁅X, L'⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hXL' hx) (Subgroup.le_normalizer hx)
  have hX1 : X ≤ ⁅X, L⁆ := by
    have h := s151v_three_subgroups_le (H₁ := L) (H₂ := L) (H₃ := L') (N := ⁅X, L⁆)
      hN₁L hN₁L hN₁L' (by rw [← hXdef]) (by rw [hX'])
    rwa [hLperf, ← hXdef] at h
  have hX2 : X ≤ ⁅X, L'⁆ := by
    have h := s151v_three_subgroups_le (H₁ := L') (H₂ := L') (H₃ := L) (N := ⁅X, L'⁆)
      hN₂L' hN₂L' hN₂L (by rw [hX']) (by rw [← hXdef])
    rwa [hL'perf, hX'] at h
  have hXQ : X ≤ blockQ L := hc
  have hXU : X ≤ blockU L := hX1.trans (Subgroup.commutator_mono hXQ le_rfl)
  have hX2Z : ⁅X, L'⁆ ≤ blockZ L := by
    rw [Subgroup.commutator_le]
    intro x hx l' hl'
    have h := s151t_conj_mod_Z hsh hs hL'N hc0 hl' (hXU hx)
    have : ⁅x, l'⁆ = (l' * x * l'⁻¹ * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact (blockZ L).inv_mem h
  have hXZ : X ≤ blockZ L := hX2.trans hX2Z
  have hZL : ⁅blockZ L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  exact eq_bot_iff.mpr (hX1.trans ((Subgroup.commutator_mono hXZ le_rfl).trans (le_of_eq hZL)))

end CFSG.Quasithin
