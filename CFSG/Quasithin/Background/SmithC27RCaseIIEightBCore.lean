module

public import CFSG.Quasithin.Background.SmithC27RCaseIIEightBPerm
public import CFSG.Quasithin.Background.SmithC27RCaseIIStar
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.Quasithin.Background.SmithC27Perm
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.SmithC27RCaseIIRad

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem conj_mem_alternatingGroup_iff_B8 {n : ℕ} (π σ : Perm (Fin n)) :
    π * σ * π⁻¹ ∈ alternatingGroup (Fin n) ↔ σ ∈ alternatingGroup (Fin n) := by
  simp only [mem_alternatingGroup, map_mul, map_inv, mul_inv_cancel_comm]

namespace CaseIICtx

variable {n : ℕ}

@[expose] noncomputable def conjB8 (C : CaseIICtx R K V n) (π : Perm (Fin n)) :
    CaseIICtx R K V n where
  hV := C.hV
  ι := C.ι.trans (MulAut.conj π)
  mem_K x := by
    rw [C.mem_K]
    exact (conj_mem_alternatingGroup_iff_B8 π (C.ι x)).symm
  β := (C124.YZ.dAct n π).toMonoidHom.comp C.β
  β_surj := (C124.YZ.dAct n π).surjective.comp C.β_surj
  β_ker u := by
    rw [← C.β_ker u]
    exact map_eq_one_iff _ (C124.YZ.dAct n π).injective
  β_equiv g u hu := by
    show C124.YZ.dAct n π (C.β ⟨_, hu⟩) =
      C124.YZ.dAct n (π * C.ι g * π⁻¹) (C124.YZ.dAct n π (C.β u))
    rw [C.β_equiv g u hu, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group

omit [Finite G] in
theorem bar_conjB8 (C : CaseIICtx R K V n) (π : Perm (Fin n)) (Y : Subgroup G) :
    (C.conjB8 π).bar Y = (C.bar Y).map (MulAut.conj π).toMonoidHom := by
  ext σ
  rw [mem_bar_iff, Subgroup.mem_map_equiv, mem_bar_iff]
  rfl

@[expose] noncomputable def starB8 (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G)) :
    ↥(K ⊔ R) →* ↥(autOn (K ⊔ R) V) :=
  ((conjAct V).comp (Subgroup.inclusion hXV)).codRestrict (autOn (K ⊔ R) V) fun x =>
    mem_autOn_iff'.2 ⟨⟨x, hXV x.2⟩, x.2, rfl⟩

omit [Finite G] in
theorem coe_starB8 (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G)) (x : ↥(K ⊔ R)) :
    ((starB8 hXV x : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) = conjAct V ⟨x, hXV x.2⟩ := rfl

omit [Finite G] in
theorem starB8_surjective (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (starB8 hXV) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hgX, hgφ⟩ := mem_autOn_iff'.1 hφ
  exact ⟨⟨g, hgX⟩, Subtype.ext hgφ⟩

@[expose] noncomputable def phiB8 (C : CaseIICtx R K V n)
    (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G)) : ↥(K ⊔ R) →* Perm (Fin n) :=
  C.ι.toMonoidHom.comp (starB8 hXV)

variable (C : CaseIICtx R K V n) (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G))

omit [Finite G] in
theorem phiB8_apply (x : ↥(K ⊔ R)) : C.phiB8 hXV x = C.ι (starB8 hXV x) := rfl

omit [Finite G] in
theorem phiB8_surjective : Function.Surjective (C.phiB8 hXV) :=
  C.ι.surjective.comp (starB8_surjective hXV)

omit [Finite G] in
theorem phiB8_eq_one_iff (x : ↥(K ⊔ R)) :
    C.phiB8 hXV x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [phiB8_apply, map_eq_one_iff _ C.ι.injective]
  have h := conjAct_eq_one_iff' (V := V) ⟨x, hXV x.2⟩
  constructor
  · intro h1
    exact h.1 (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext (h.2 h1)

omit [Finite G] in
theorem phiB8_mem_bar {Y : Subgroup G} {x : ↥(K ⊔ R)} (hx : (x : G) ∈ Y) :
    C.phiB8 hXV x ∈ C.bar Y := by
  rw [mem_bar_iff, phiB8_apply, MulEquiv.symm_apply_apply, coe_starB8]
  exact mem_autOn_iff'.2 ⟨⟨x, hXV x.2⟩, hx, rfl⟩

omit [Finite G] in
theorem mem_of_phiB8_mem_bar {Y : Subgroup G} (hYX : Y ≤ K ⊔ R)
    (hC : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ Y) {x : ↥(K ⊔ R)}
    (hx : C.phiB8 hXV x ∈ C.bar Y) : (x : G) ∈ Y := by
  rw [mem_bar_iff, phiB8_apply, MulEquiv.symm_apply_apply, coe_starB8] at hx
  obtain ⟨g, hgY, hgx⟩ := mem_autOn_iff'.1 hx
  have hc : ((g⁻¹ * ⟨x, hXV x.2⟩ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    rw [← conjAct_eq_one_iff', map_mul, map_inv, hgx]
    exact inv_mul_cancel _
  have hmem : (g : G)⁻¹ * x ∈ Y :=
    hC ⟨(K ⊔ R).mul_mem ((K ⊔ R).inv_mem (hYX hgY)) x.2, hc⟩
  have : (x : G) = g * ((g : G)⁻¹ * x) := by group
  rw [this]
  exact Y.mul_mem hgY hmem

@[expose] noncomputable def alphaB8 (hs : StarHyp R K V) : ↥K →* alternatingGroup (Fin n) :=
  ((C.phiB8 hs.le_normalizer_V).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ R))).codRestrict
    _ fun k => by
      have h1 : C.phiB8 hs.le_normalizer_V (Subgroup.inclusion le_sup_left k) ∈ C.bar K :=
        C.phiB8_mem_bar _ k.2
      rwa [C.bar_K] at h1

omit [Finite G] in
theorem coe_alphaB8 (hs : StarHyp R K V) (k : ↥K) :
    (C.alphaB8 hs k : Perm (Fin n)) =
      C.phiB8 hs.le_normalizer_V ⟨k, Subgroup.mem_sup_left k.2⟩ := rfl

omit [Finite G] in
theorem alphaB8_surjective (hs : StarHyp R K V) : Function.Surjective (C.alphaB8 hs) := by
  rintro ⟨σ, hσ⟩
  rw [← C.bar_K, mem_bar_iff] at hσ
  obtain ⟨g, hgK, hgσ⟩ := mem_autOn_iff'.1 hσ
  refine ⟨⟨g, hgK⟩, Subtype.ext ?_⟩
  rw [coe_alphaB8, phiB8_apply]
  have h1 : starB8 hs.le_normalizer_V ⟨g, Subgroup.mem_sup_left hgK⟩ = C.ι.symm σ :=
    Subtype.ext hgσ
  rw [h1, MulEquiv.apply_symm_apply]

end CaseIICtx

theorem odd_card_of_le_center_B8 {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥)
    {N : Subgroup Q} (hN : N ≤ Subgroup.center Q) : Odd (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (even_iff_two_dvd.1 hev)
  have hxc : (x : Q) ∈ Subgroup.center Q := hN x.2
  have hnorm : (Subgroup.zpowers (x : Q)).Normal := by
    constructor
    intro y hy g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hk : (x : Q) ^ k ∈ Subgroup.center Q := Subgroup.zpow_mem _ hxc k
    rw [(Subgroup.mem_center_iff.1 hk g), mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  have hp : IsPGroup 2 (Subgroup.zpowers (x : Q)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  have hle : Subgroup.zpowers (x : Q) ≤ CFSG.pCore 2 Q := le_sSup ⟨hnorm, hp⟩
  rw [hQ] at hle
  have h1 : (x : Q) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have h2 := Subgroup.orderOf_coe x
  rw [h1, orderOf_one, hx] at h2
  omega

namespace CaseIICtx

variable (C : CaseIICtx R K V 8)

private theorem pCore_le_ker_alphaB8 (hs : StarHyp R K V) :
    CFSG.pCore 2 ↥K ≤ (C.alphaB8 hs).ker := by
  intro k hk
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  rw [coe_alphaB8]
  exact (C.phiB8_eq_one_iff _ _).2
    (hs.pCore_K_le_centralizer ((mem_pCore_iff_mem_pCoreOf k).1 hk))

private theorem ker_lift_alphaB8 (hs : StarHyp R K V) :
    (QuotientGroup.lift (CFSG.pCore 2 ↥K) (C.alphaB8 hs) (C.pCore_le_ker_alphaB8 hs)).ker = ⊥ := by
  set η := QuotientGroup.lift (CFSG.pCore 2 ↥K) (C.alphaB8 hs) (C.pCore_le_ker_alphaB8 hs)
  have hηs : Function.Surjective η := by
    intro σ
    obtain ⟨k, rfl⟩ := C.alphaB8_surjective hs σ
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hηZ : η.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H k =>
      have hk : C.alphaB8 hs k = 1 := hz
      have hkC : (k : G) ∈ Subgroup.centralizer (V : Set G) :=
        (C.phiB8_eq_one_iff _ _).1 (congrArg Subtype.val hk)
      exact mk_mem_center_of_mem_oTwoZIn (hs.inf_centralizer_le ⟨k.2, hkC⟩)
  have hodd : Odd (Nat.card η.ker) :=
    odd_card_of_le_center_B8 (pCore_two_quotient_pCore_two ↥K) hηZ
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hs.quasi.1
  exact Subgroup.card_eq_one.1
    (CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 6) le_rfl η hηs hηZ hodd)

theorem ker_alphaB8 (hs : StarHyp R K V) : (C.alphaB8 hs).ker = CFSG.pCore 2 ↥K := by
  refine le_antisymm (fun k hk => ?_) (C.pCore_le_ker_alphaB8 hs)
  have h1 : (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      (QuotientGroup.lift (CFSG.pCore 2 ↥K) (C.alphaB8 hs) (C.pCore_le_ker_alphaB8 hs)).ker := hk
  rw [C.ker_lift_alphaB8 hs, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

include C in
theorem center_eq_bot_B8 (hs : StarHyp R K V) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  set η := QuotientGroup.lift (CFSG.pCore 2 ↥K) (C.alphaB8 hs) (C.pCore_le_ker_alphaB8 hs)
  have hinj : Function.Injective η := (MonoidHom.ker_eq_bot_iff η).1 (C.ker_lift_alphaB8 hs)
  have hsurj : Function.Surjective η := by
    intro σ
    obtain ⟨k, rfl⟩ := C.alphaB8_surjective hs σ
    exact ⟨QuotientGroup.mk k, rfl⟩
  rw [eq_bot_iff]
  intro z hz
  have h1 : η z ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact hinj (h1.trans (map_one η).symm)

include C in
theorem inf_centralizer_eq_B8 (hs : StarHyp R K V) :
    (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (K ⊔ R) := by
  apply le_antisymm
  · have h1 := hs.cent
    rw [oTwoZIn_eq_of_center_eq_bot (C.center_eq_bot_B8 hs)] at h1
    exact h1.trans (sup_le le_rfl hs.pCore_K_le_pCore)
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hs.pCore_le_centralizer

end CaseIICtx

namespace CaseIICtx

variable {n : ℕ} (C : CaseIICtx R K V n)

omit [Finite G] in
theorem bar_le_bar {Y Y' : Subgroup G} (h : autOn Y V ≤ autOn Y' V) : C.bar Y ≤ C.bar Y' :=
  fun _ hσ => (C.mem_bar_iff).2 (h ((C.mem_bar_iff).1 hσ))

omit [Finite G] in
theorem autOn_eq_of_bar_eq {Y Y' : Subgroup G} (hY : autOn Y V ≤ autOn (K ⊔ R) V)
    (hY' : autOn Y' V ≤ autOn (K ⊔ R) V) (h : C.bar Y = C.bar Y') : autOn Y V = autOn Y' V := by
  have key : ∀ {A B : Subgroup G}, autOn A V ≤ autOn (K ⊔ R) V → C.bar A = C.bar B →
      autOn A V ≤ autOn B V := by
    intro A B hA hAB φ hφ
    have h1 : C.ι ⟨φ, hA hφ⟩ ∈ C.bar A := by
      rw [mem_bar_iff, MulEquiv.symm_apply_apply]
      exact hφ
    rw [hAB, mem_bar_iff, MulEquiv.symm_apply_apply] at h1
    exact h1
  exact le_antisymm (key hY h) (key hY' h.symm)

omit [Finite G] in
theorem autOn_R_eq_B8 (C : CaseIICtx R K V 8) (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    autOn R V = Subgroup.zpowers ((C.ι.symm (swap 0 1) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) := by
  have hτ : ((C.ι.symm (swap 0 1) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∈ autOn R V := by
    rw [← mem_bar_iff, hR]
    exact Subgroup.mem_zpowers _
  refine le_antisymm (fun φ hφ => ?_) ((Subgroup.zpowers_le).2 hτ)
  have hφX : φ ∈ autOn (K ⊔ R) V := autOn_mono' le_sup_right hφ
  have h1 : C.ι ⟨φ, hφX⟩ ∈ C.bar R := by
    rw [mem_bar_iff, MulEquiv.symm_apply_apply]
    exact hφ
  rw [hR, mem_zpowers_swap_iff_B8] at h1
  rcases h1 with h1 | h1
  · have h2 : (⟨φ, hφX⟩ : ↥(autOn (K ⊔ R) V)) = 1 := C.ι.injective (h1.trans (map_one _).symm)
    rw [show φ = 1 from congrArg Subtype.val h2]
    exact Subgroup.one_mem _
  · have h2 : (⟨φ, hφX⟩ : ↥(autOn (K ⊔ R) V)) = C.ι.symm (swap 0 1) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [show φ = _ from congrArg Subtype.val h2]
    exact Subgroup.mem_zpowers _

theorem bar_MK_B8 (h : Hyp27 H R M K) (hs : StarHyp R K V) (C : CaseIICtx R K V 8)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    C.bar (M ⊓ K) = alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {swap (0 : Fin 8) 1} := by
  have hle : C.bar (M ⊓ K) ≤ alternatingGroup (Fin 8) := by
    rw [← C.bar_K]
    exact C.bar_le_bar (autOn_mono' inf_le_right)
  have hstar : alternatingGroup (Fin 8) ⊓ Subgroup.centralizer {swap (0 : Fin 8) 1} ≤
      C.bar (M ⊓ K) := by
    intro σ hσ
    obtain ⟨hσA, hσC⟩ := Subgroup.mem_inf.1 hσ
    have hσs : σ * swap 0 1 = swap 0 1 * σ := Subgroup.mem_centralizer_singleton_iff.1 hσC
    rw [mem_bar_iff]
    apply autOn_K_inf_normalizer_R_le h hs
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← mem_bar_iff, C.bar_K]
      exact hσA
    · rw [autOn_R_eq_B8 C hR]
      refine Subgroup.mem_normalizer_fintype fun φ hφ => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      have hc : C.ι.symm σ * C.ι.symm (swap 0 1) = C.ι.symm (swap 0 1) * C.ι.symm σ := by
        rw [← map_mul, ← map_mul, hσs]
      have hc' : Commute ((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V)
          ((C.ι.symm (swap 0 1) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) :=
        congrArg Subtype.val hc
      rw [(hc'.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ _
  have h5 : 5 ≤ Fintype.card (Fin 8) := by simp
  have hk := kJ_swap_eq_centralizer (α := Fin 8) (a := 0) (b := 1) (by decide)
  rcases kJ_swap_overgroups h5 ⟨0, 1, by decide, rfl⟩ (hk ▸ hstar) hle with h1 | h1
  · rw [h1, hk]
  · exfalso
    apply autOn_MK_ne h hs
    refine C.autOn_eq_of_bar_eq (autOn_mono' (inf_le_right.trans le_sup_left))
      (autOn_mono' le_sup_left) ?_
    rw [h1, C.bar_K]

omit [Finite G] in
theorem exists_t_B8 (hs : StarHyp R K V) (C : CaseIICtx R K V 8)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    ∃ t : G, ∃ htR : t ∈ R, ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
      C.phiB8 hs.le_normalizer_V ⟨t, Subgroup.mem_sup_right htR⟩ = swap 0 1 ∧
      conjAct V ⟨t, htV⟩ = ((C.ι.symm (swap 0 1) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∧
      autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧ orderOf (conjAct V ⟨t, htV⟩) = 2 := by
  have hτ : ((C.ι.symm (swap 0 1) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∈ autOn R V := by
    rw [autOn_R_eq_B8 C hR]
    exact Subgroup.mem_zpowers _
  obtain ⟨g, hgR, hgτ⟩ := mem_autOn_iff'.1 hτ
  refine ⟨g, hgR, g.2, ?_, hgτ, ?_, ?_⟩
  · rw [phiB8_apply]
    have h1 : starB8 hs.le_normalizer_V ⟨g, Subgroup.mem_sup_right hgR⟩ = C.ι.symm (swap 0 1) :=
      Subtype.ext hgτ
    rw [h1, MulEquiv.apply_symm_apply]
  · have hg : (⟨(g : G), g.2⟩ : ↥(Subgroup.normalizer (V : Set G))) = g := rfl
    rw [hg, hgτ]
    exact autOn_R_eq_B8 C hR
  · have hg : (⟨(g : G), g.2⟩ : ↥(Subgroup.normalizer (V : Set G))) = g := rfl
    rw [hg, hgτ, Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq C.ι, MulEquiv.apply_symm_apply]
    exact orderOf_swap_B8

theorem autOn_MK_eq_B8 (h : Hyp27 H R M K) (hs : StarHyp R K V) (C : CaseIICtx R K V 8)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)) := by
  set τ : ↥(autOn (K ⊔ R) V) := C.ι.symm (swap 0 1) with hτdef
  have hMK := C.bar_MK_B8 h hs hR
  rw [autOn_R_eq_B8 C hR]
  apply le_antisymm
  · intro φ hφ
    refine Subgroup.mem_inf.2 ⟨autOn_mono' inf_le_right hφ,
      Subgroup.mem_centralizer_iff.2 fun ψ hψ => ?_⟩
    have hφX : φ ∈ autOn (K ⊔ R) V := autOn_mono' (inf_le_right.trans le_sup_left) hφ
    have h1 : C.ι ⟨φ, hφX⟩ ∈ C.bar (M ⊓ K) := by
      rw [mem_bar_iff, MulEquiv.symm_apply_apply]
      exact hφ
    rw [hMK] at h1
    have h2 : C.ι ⟨φ, hφX⟩ * swap 0 1 = swap 0 1 * C.ι ⟨φ, hφX⟩ :=
      Subgroup.mem_centralizer_singleton_iff.1 h1.2
    have h3 : (⟨φ, hφX⟩ : ↥(autOn (K ⊔ R) V)) * τ = τ * ⟨φ, hφX⟩ := by
      apply C.ι.injective
      rw [map_mul, map_mul, hτdef, MulEquiv.apply_symm_apply]
      exact h2
    have h4 : Commute φ (τ : MulAut ↥V) := congrArg Subtype.val h3
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hψ
    exact ((h4.zpow_right k).eq).symm
  · intro φ hφ
    obtain ⟨hφK, hφC⟩ := Subgroup.mem_inf.1 hφ
    have hφX : φ ∈ autOn (K ⊔ R) V := autOn_mono' le_sup_left hφK
    have hcomm := Subgroup.mem_centralizer_iff.1 hφC _ (Subgroup.mem_zpowers (τ : MulAut ↥V))
    have h1 : C.ι ⟨φ, hφX⟩ ∈ C.bar (M ⊓ K) := by
      rw [hMK]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← C.mem_K]
        exact hφK
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h3 : (⟨φ, hφX⟩ : ↥(autOn (K ⊔ R) V)) * τ = τ * ⟨φ, hφX⟩ :=
          Subtype.ext hcomm.symm
        have h4 := congrArg C.ι h3
        rw [map_mul, map_mul, hτdef, MulEquiv.apply_symm_apply] at h4
        exact h4
    rw [mem_bar_iff, MulEquiv.symm_apply_apply] at h1
    exact h1

end CaseIICtx

end CFSG.Quasithin.SmithC27
