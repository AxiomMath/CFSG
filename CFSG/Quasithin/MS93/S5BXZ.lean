module

public import CFSG.Quasithin.MS93.S5Stmt
public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.MSPBridge
public import CFSG.ClassicalGroups.Symplectic.Perfect

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace S5B

theorem inv_mul_mem_of_relIndex_le_two {Γ : Type*} [Group Γ] {H K : Subgroup Γ}
    (hHK : H.relIndex K ≤ 2) (h0 : H.relIndex K ≠ 0) {x y : Γ} (hx : x ∈ K) (hy : y ∈ K)
    (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  classical
  by_contra hxy
  set Q := ↥K ⧸ H.subgroupOf K
  have hQ : Nat.card Q ≤ 2 := hHK
  have : Finite Q := Nat.finite_of_card_ne_zero h0
  have : Fintype Q := Fintype.ofFinite Q
  set q₁ : Q := (QuotientGroup.mk (1 : ↥K) : Q)
  set q₂ : Q := (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : Q)
  set q₃ : Q := (QuotientGroup.mk (⟨y, hy⟩ : ↥K) : Q)
  have h12 : q₁ ≠ q₂ := by
    intro he
    apply hxH
    have := QuotientGroup.eq.1 he
    simpa [Subgroup.mem_subgroupOf] using this
  have h13 : q₁ ≠ q₃ := by
    intro he
    apply hyH
    have := QuotientGroup.eq.1 he
    simpa [Subgroup.mem_subgroupOf] using this
  have h23 : q₂ ≠ q₃ := by
    intro he
    apply hxy
    have := QuotientGroup.eq.1 he
    simpa [Subgroup.mem_subgroupOf] using this
  have h3 : ({q₁, q₂, q₃} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have h4 : ({q₁, q₂, q₃} : Finset Q).card ≤ Nat.card Q := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

section Kernel

variable {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

abbrev kerG (a : ↥M →* ↥(StatedSp 2 F)) : Subgroup G := (a.ker).map M.subtype

omit [Finite G] [Fintype F] in
theorem le_normalizer_kerG : M ≤ Subgroup.normalizer (kerG a : Set G) := by
  have hle : kerG a ≤ M := Subgroup.map_subtype_le _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 ?_
  rw [kerG, PU.map_subtype_subgroupOf]
  exact a.normal_ker

theorem not_le_kerG (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) : ¬ L ≤ kerG a := by
  intro hL
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hLU : ⁅L, Uq M T L⁆ ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    have hlM : l ∈ M := h.L_le hl
    have hconj : l * u * l⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hlM) u).1 hu
    obtain ⟨m, hm, hml⟩ := hL hl
    have hm' : m = ⟨l, hlM⟩ := Subtype.ext hml
    subst hm'
    have hv := c.vec_commutator ⟨l, hlM⟩ ⟨u, hu⟩ hconj
    rw [MonoidHom.mem_ker.1 hm, MSP.mat_one, Matrix.one_mulVec, sub_self] at hv
    have := (c.vec_eq_zero_iff _).1 hv
    exact (Subgroup.mem_inf.1 this).2
  have hUC : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_comm]
    exact hLU
  apply h.Uq_ne_bot
  have h1 : ⁅⁅Uq M T L, L⁆, L⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hUC
  rwa [h.Uq_comm, h.Uq_comm] at h1

theorem mem_pCoreOf_of_ker (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {m : ↥M}
    (hm : a m = 1) (h2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1) : (m : G) ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_rel le_normalizer_kerG (not_le_kerG h hd) m.2 h2 fun l hl => ?_
  refine ⟨⁅m, ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
  show _ ∈ a.ker
  rw [MonoidHom.mem_ker, map_commutatorElement, hm, commutatorElement_one_left]

theorem le_of_map_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {N : Subgroup G}
    (hNM : N ≤ M) (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hON : pCoreOf 2 M ≤ N)
    (hmap : ∀ m : ↥M, ∃ n : ↥M, (n : G) ∈ N ∧ a n = a m) : T ≤ N := by
  intro t ht
  set t' : ↥M := ⟨t, h.le ht⟩
  obtain ⟨n, hnN, hn⟩ := hmap t'
  set κ : ↥M := n⁻¹ * t'
  have hκ : a κ = 1 := by
    simp only [κ, map_mul, map_inv, hn, inv_mul_cancel]
  have hNs : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hNn
  set φ := QuotientGroup.mk' (N.subgroupOf M)
  have hφn : φ n = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hnN
  have hφκ : φ κ = φ t' := by
    simp only [κ, map_mul, map_inv, hφn, inv_one, one_mul]
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
  have he' : t' ^ 2 ^ e = 1 := Subtype.ext (by
    have := congrArg Subtype.val he
    simpa [t'] using this)
  have hφκe : φ κ ^ 2 ^ e = 1 := by rw [hφκ, ← map_pow, he', map_one]
  obtain ⟨j, hj, f, hf⟩ := exists_pow_isTwoElt φ κ hφκe
  have hκj : ((κ ^ j : ↥M) : G) ∈ pCoreOf 2 M := by
    refine mem_pCoreOf_of_ker h hd (by rw [map_pow, hκ, one_pow]) ⟨f, ?_⟩
    have := congrArg Subtype.val hf
    simpa using this
  have hφ1 : φ (κ ^ j) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hON hκj
  have ht1 : φ t' = 1 := by rw [← hφκ, ← hj, hφ1]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht1
  exact ht1

theorem eq_of_map_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {N : Subgroup G}
    (hNM : N ≤ M) (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hLN : L ≤ N)
    (hON : pCoreOf 2 M ≤ N) (hmap : ∀ m : ↥M, ∃ n : ↥M, (n : G) ∈ N ∧ a n = a m) : N = M :=
  le_antisymm hNM (h.eq_sup.le.trans (sup_le hLN (le_of_map_eq h hd hNM hNn hON hmap)))

omit [Fintype F] in
theorem isPerfect_sp4 (hF : 4 ≤ Nat.card F) : Group.IsPerfect ↥(StatedSp 2 F) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin 2 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F 2 (Or.inl (Or.inr hF))
  let e : TauCeti.GLSymplecticFin 2 F ≃* StatedSp 2 F :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 F).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := F)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem map_L_eq_top (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k) :
    (L.subgroupOf M).map a = ⊤ := by
  have hF : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hd.2.1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := isPerfect_sp4 hF
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have : ((L.subgroupOf M).map a).Normal := hLn.map a hd.2.2.1
  refine eq_top_of_perfect_of_two _ fun g => ?_
  obtain ⟨m, rfl⟩ := hd.2.2.1 g
  have hsup : L.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨a l, Subgroup.mem_map_of_mem a hl, ?_⟩
  obtain ⟨e, he⟩ := h.isPGroup ⟨(t : G), ht⟩
  refine ⟨e, ?_⟩
  have he' : t ^ 2 ^ e = 1 := Subtype.ext (by
    have := congrArg Subtype.val he
    simpa using this)
  rw [← hlt, map_mul, inv_mul_cancel_left, ← map_pow, he', map_one]

theorem eq_sup_pCoreOf (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k) :
    M = L ⊔ pCoreOf 2 M := by
  have hNn : M ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
    le_normalizer_sup h.le_normalizer (le_normalizer_pCoreOf M)
  refine (eq_of_map_eq h hd (sup_le h.L_le (pCoreOf_le' M)) hNn le_sup_left le_sup_right
    fun m => ?_).symm
  have hm : a m ∈ (L.subgroupOf M).map a := by rw [map_L_eq_top h hd hk]; exact Subgroup.mem_top _
  obtain ⟨l, hl, hlm⟩ := hm
  exact ⟨l, Subgroup.mem_sup_left hl, hlm⟩

end Kernel

section Two

variable {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem charP_two_of_card (hF : Fintype.card F = 2 ^ k) : CharP F 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 2 ^ k := by
    rw [← hF, hn]
    exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  exact ringChar.of_eq h2

end Two

section Main

variable {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem relIndex_centralizer_ofA (hTM : T ≤ M) {K : Subgroup G} (hK : K ≤ M) (z : ↥M) :
    (Subgroup.centralizer ({(puAmalgam hTM).ofA z} : Set (puAmalgam hTM).Universal)).relIndex
        (imM hTM K) = (Subgroup.centralizer ({(z : G)} : Set G)).relIndex K := by
  have hinf : imM hTM K ⊓ Subgroup.centralizer ({(puAmalgam hTM).ofA z} :
      Set (puAmalgam hTM).Universal) = imM hTM (K ⊓ Subgroup.centralizer ({(z : G)} : Set G)) := by
    ext y
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, hc⟩
      refine ⟨m, ⟨Subgroup.mem_subgroupOf.1 hm, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hc
      rw [← map_mul, ← map_mul] at this
      exact congrArg Subtype.val ((puAmalgam hTM).ofA_injective this)
    · rintro ⟨m, ⟨hmK, hmC⟩, rfl⟩
      refine ⟨⟨m, hmK, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hmC))
  rw [← Subgroup.inf_relIndex_right, inf_comm, hinf, imM, imM,
    Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hK, inf_comm, Subgroup.inf_relIndex_right]

end Main

end S5B

end CFSG.Quasithin.MS93
