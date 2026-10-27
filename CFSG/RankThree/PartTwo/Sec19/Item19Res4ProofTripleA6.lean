module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
import CFSG.LocalAnalysis.AGLEmbedding.AltSix

public section

namespace CFSG.RankThree.PartTwo.Sec19

namespace Item19Res4Proof

open Equiv

section A6

theorem perm_six_exists_inv_of_pow_three : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 →
    ∃ τ : Perm (Fin 6), Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

theorem card_alternatingGroup_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

@[expose] def threeCycleSix : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 0 2, by
    rw [Perm.mem_alternatingGroup]
    decide⟩

theorem threeCycleSix_pow_three : threeCycleSix ^ 3 = 1 := by
  apply Subtype.ext
  change (swap (0 : Fin 6) 1 * swap 0 2) ^ 3 = 1
  decide

theorem threeCycleSix_ne_one : threeCycleSix ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  change swap (0 : Fin 6) 1 * swap 0 2 = 1 at h1
  revert h1
  decide

end A6

section Basic

variable {X : Type} [Group X]

theorem card_eq_of_isTripleA6 (h : IsTripleA6 X) : Nat.card X = 1080 := by
  obtain ⟨hZ, ⟨φ⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, hZ,
    Nat.card_congr φ.toEquiv, card_alternatingGroup_six']

theorem pow_three_eq_one_of_mem_center (h : IsTripleA6 X) {z : X}
    (hz : z ∈ Subgroup.center X) : z ^ 3 = 1 := by
  have : Finite (Subgroup.center X) := Nat.finite_of_card_ne_zero (by rw [h.1]; norm_num)
  have h1 := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
  rw [h.1] at h1
  simpa using congrArg Subtype.val h1

theorem pow_three_eq_one_of_isTripleA6 (h : IsTripleA6 X) {x : X}
    (hx : (x : X ⧸ Subgroup.center X) ^ 3 = 1) : x ^ 3 = 1 := by
  obtain ⟨φ⟩ := h.2
  set σ : alternatingGroup (Fin 6) := φ (x : X ⧸ Subgroup.center X) with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx, map_one]
  obtain ⟨τ, hτs, hτ⟩ := perm_six_exists_inv_of_pow_three (σ : Perm (Fin 6))
    (by rw [← Subgroup.coe_pow, hσ3]; rfl)
  set τ' : alternatingGroup (Fin 6) := ⟨τ, by rw [Perm.mem_alternatingGroup]; exact hτs⟩
  have hτ' : τ' * σ * τ'⁻¹ = σ⁻¹ := Subtype.ext hτ
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (φ.symm τ')
  have hinv : ((t * x * t⁻¹ : X) : X ⧸ Subgroup.center X) =
      ((x⁻¹ : X) : X ⧸ Subgroup.center X) := by
    apply φ.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, ht, MulEquiv.apply_symm_apply, QuotientGroup.mk_inv, map_inv, ← hσ, hτ']
  obtain ⟨z, hz, hzeq⟩ : ∃ z ∈ Subgroup.center X, t * x * t⁻¹ = x⁻¹ * z := by
    refine ⟨(x⁻¹)⁻¹ * (t * x * t⁻¹), ?_, by group⟩
    exact QuotientGroup.eq.mp hinv.symm
  have hz3 := pow_three_eq_one_of_mem_center h hz
  have hw : x ^ 3 ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  have hw3 : (x ^ 3) ^ 3 = 1 := pow_three_eq_one_of_mem_center h hw
  have h1 : t * x ^ 3 * t⁻¹ = x ^ 3 := by
    rw [(Subgroup.mem_center_iff.mp hw t), mul_inv_cancel_right]
  have h2 : t * x ^ 3 * t⁻¹ = (t * x * t⁻¹) ^ 3 := conj_pow.symm
  have hc : Commute x⁻¹ z := Subgroup.mem_center_iff.mp hz x⁻¹
  rw [hzeq, hc.mul_pow, hz3, mul_one, h1, inv_pow] at h2
  have h6 : (x ^ 3) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h2]
    exact mul_inv_cancel _
  calc x ^ 3 = (x ^ 3) ^ 3 * ((x ^ 3) ^ 2)⁻¹ := by group
    _ = 1 := by rw [hw3, h6, inv_one, mul_one]

theorem exists_noncentral_of_isTripleA6 (h : IsTripleA6 X) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X := by
  obtain ⟨φ⟩ := h.2
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm threeCycleSix)
  refine ⟨x, pow_three_eq_one_of_isTripleA6 h ?_, fun hxz => threeCycleSix_ne_one ?_⟩
  · rw [hx, ← map_pow, threeCycleSix_pow_three, map_one]
  · have h1 : (x : X ⧸ Subgroup.center X) = 1 := (QuotientGroup.eq_one_iff x).mpr hxz
    rw [hx] at h1
    simpa using congrArg φ h1

theorem exists_mem_center_ne_one (h : IsTripleA6 X) : ∃ z ∈ Subgroup.center X, z ≠ 1 := by
  by_contra hall
  push Not at hall
  have hbot : Subgroup.center X = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
  have h1 := h.1
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem card_ne_twentySeven_of_isTripleA6 [Finite X] [Group.IsPerfect X] (h : IsTripleA6 X)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≠ 27 := by
  intro hE27
  classical
  have hcard := card_eq_of_isTripleA6 h
  have hindex : E.index = 40 := by
    have h1 := E.card_mul_index
    rw [hE27, hcard] at h1
    omega
  have : E.FiniteIndex := ⟨by rw [hindex]; norm_num⟩
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => hE.1.is_comm.comm a b }
  obtain ⟨z, hz, hz1⟩ := exists_mem_center_ne_one h
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ E → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have htr := MonoidHom.transfer_eq_pow (MonoidHom.id E) z key
  have htriv : MonoidHom.transfer (MonoidHom.id E) z = 1 := by
    have hker := Abelianization.commutator_subset_ker (MonoidHom.transfer (MonoidHom.id E))
    rw [Group.IsPerfect.commutator_eq_top] at hker
    exact hker (Subgroup.mem_top z)
  rw [htriv] at htr
  have hz3 := pow_three_eq_one_of_mem_center h hz
  have h40 : z ^ E.index = z := by
    rw [hindex, show (40 : ℕ) = 3 * 13 + 1 by norm_num, pow_succ, pow_mul, hz3, one_pow, one_mul]
  have h2 := congrArg Subtype.val htr
  simp only [MonoidHom.id_apply, OneMemClass.coe_one] at h2
  exact hz1 (by rw [← h40, ← h2])

theorem eq_one_of_forall_mul_inv_mem_center [Group.IsPerfect X] (σ : MulAut X)
    (hσ : ∀ x : X, σ x * x⁻¹ ∈ Subgroup.center X) : σ = 1 := by
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨σ x * x⁻¹, hσ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change σ (x * y) * (x * y)⁻¹ = (σ x * x⁻¹) * (σ y * y⁻¹)
        have hc := Subgroup.mem_center_iff.mp (hσ y) x⁻¹
        calc σ (x * y) * (x * y)⁻¹ = σ x * ((σ y * y⁻¹) * x⁻¹) := by rw [map_mul]; group
          _ = σ x * (x⁻¹ * (σ y * y⁻¹)) := by rw [hc]
          _ = (σ x * x⁻¹) * (σ y * y⁻¹) := by group }
  have hker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext x
  have h1 := hker (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at h1
  have h2 : σ x * x⁻¹ = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h2

@[expose] noncomputable def centerQuotMulAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem centerQuotMulAut_mk (σ : MulAut X) (x : X) :
    centerQuotMulAut X σ (x : X ⧸ Subgroup.center X) = ((σ x : X) : X ⧸ Subgroup.center X) :=
  rfl

theorem exists_eq_conj_of_isTripleA6 [Group.IsPerfect X] (h : IsTripleA6 X) (σ : MulAut X)
    (hσ : σ ^ 3 = 1) : ∃ y : X, σ = MulAut.conj y := by
  obtain ⟨φ⟩ := h.2
  set σb := centerQuotMulAut X σ with hσb
  set f : MulAut (alternatingGroup (Fin 6)) := MulAut.congr φ σb with hf
  have hf3 : f ^ 3 = 1 := by
    rw [hf, ← map_pow, hσb, ← map_pow, hσ, map_one, map_one]
  obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.mem_range_conj_of_pow_eq_one Nat.prime_three (by norm_num) hf3
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm a)
  refine ⟨y, ?_⟩
  have hbar : ∀ q : X ⧸ Subgroup.center X, σb q = (y : X ⧸ Subgroup.center X) * q *
      (y : X ⧸ Subgroup.center X)⁻¹ := by
    intro q
    have h1 := congrArg (fun ψ : MulAut (alternatingGroup (Fin 6)) => ψ (φ q)) ha
    simp only [MulAut.conj_apply, hf, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    apply φ.injective
    rw [← h1, map_mul, map_mul, map_inv, hy, MulEquiv.apply_symm_apply]
  have hτ := eq_one_of_forall_mul_inv_mem_center ((MulAut.conj y)⁻¹ * σ) (fun x => by
    have h1 := hbar (x : X ⧸ Subgroup.center X)
    rw [hσb, centerQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at h1
    set c := (y * x * y⁻¹)⁻¹ * σ x with hc
    have hcz : c ∈ Subgroup.center X := QuotientGroup.eq.mp h1.symm
    have hσx : σ x = y * x * y⁻¹ * c := by rw [hc]; group
    have hcc := Subgroup.mem_center_iff.mp hcz
    have h3 : ((MulAut.conj y)⁻¹ * σ) x * x⁻¹ = c := by
      rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, hσx]
      calc y⁻¹ * (y * x * y⁻¹ * c) * y⁻¹⁻¹ * x⁻¹ = x * (y⁻¹ * (c * y)) * x⁻¹ := by group
        _ = x * (y⁻¹ * (y * c)) * x⁻¹ := by rw [hcc y]
        _ = x * c * x⁻¹ := by group
        _ = c * x * x⁻¹ := by rw [hcc x]
        _ = c := by group
    rw [h3]
    exact hcz)
  exact (inv_mul_eq_one.mp hτ).symm

theorem index_ne_five_of_isSimpleGroup {Y : Type*} [Group Y] [Finite Y] (hY : IsSimpleGroup Y)
    (hcard : Nat.card Y = 360) (H : Subgroup Y) : H.index ≠ 5 := by
  classical
  intro hindex
  set ρ := MulAction.toPermHom Y (Y ⧸ H) with hρ
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hY ρ.ker ρ.normal_ker with hker | hker
  · have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
    have hle := Nat.card_le_card_of_injective ρ hinj
    rw [Nat.card_perm, hcard, ← Subgroup.index, hindex] at hle
    norm_num [Nat.factorial] at hle
  · have hHtop : H = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ ρ.ker := hker ▸ Subgroup.mem_top y
      rw [MonoidHom.mem_ker] at hy
      have h1 := congrArg (fun π : Perm (Y ⧸ H) => π (QuotientGroup.mk 1)) hy
      simp only [hρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.coe_one,
        id_eq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h1
      have h2 : y⁻¹ * 1 ∈ H := QuotientGroup.eq.mp h1
      simpa using h2
    rw [hHtop, Subgroup.index_top] at hindex
    omega

theorem exists_fixed_of_isTripleA6 [Finite X] [Group.IsPerfect X] (h : IsTripleA6 X)
    (W : Subgroup (MulAut X)) (hW3 : ∀ w ∈ W, w ^ 3 = 1) (P : Subgroup X)
    (hP : IsProperParabolic P) (hWP : ∀ w ∈ W, ∀ p ∈ P, w p ∈ P) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X ∧ ∀ w ∈ W, w x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := h.2
  have hcard := card_eq_of_isTripleA6 h
  set Z := Subgroup.center X with hZ
  have hconjZ : ∀ z ∈ Z, MulAut.conj z = 1 := fun z hz => by
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hz x,
      mul_inv_cancel_right]
  set Y := W.comap (MulAut.conj : X →* MulAut X) with hY
  have hZY : Z ≤ Y := fun z hz => by
    change MulAut.conj z ∈ W
    rw [hconjZ z hz]
    exact W.one_mem
  have hWY : ∀ w ∈ W, ∃ y ∈ Y, w = MulAut.conj y := fun w hw => by
    obtain ⟨y, hy⟩ := exists_eq_conj_of_isTripleA6 h w (hW3 w hw)
    refine ⟨y, ?_, hy⟩
    change MulAut.conj y ∈ W
    rw [← hy]
    exact hw
  have hY3 : ∀ y ∈ Y, y ^ 3 = 1 := fun y hy => by
    apply pow_three_eq_one_of_isTripleA6 h
    have h1 : MulAut.conj (y ^ 3) = 1 := by
      rw [map_pow]
      exact hW3 _ hy
    have hc : y ^ 3 ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun ψ : MulAut X => ψ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
        _ = y ^ 3 * g := by group
    rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hc]
  have hY3p : IsPGroup 3 Y := fun y => ⟨1, Subtype.ext (by simpa using hY3 y y.2)⟩
  have hYN : Y ≤ Subgroup.normalizer (P : Set X) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact hWP _ hy p hp
    · intro hp
      have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
      have h1 := hWP _ hy' _ hp
      simpa [MulAut.conj_apply, mul_assoc] using h1
  obtain ⟨k, hk⟩ := hY3p.exists_card_eq
  have hk3 : k ≤ 3 := by
    have h1 : 3 ^ k ∣ 3 ^ 3 * 40 := by
      rw [← hk, show (3 : ℕ) ^ 3 * 40 = 1080 by norm_num, ← hcard]
      exact Subgroup.card_subgroup_dvd_card Y
    have h2 : 3 ^ k ∣ 3 ^ 3 :=
      (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) h1)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hk1 : 1 ≤ k := by
    have h1 : Nat.card Z ∣ Nat.card Y := Subgroup.card_dvd_of_le hZY
    rw [h.1, hk] at h1
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · norm_num at h1
    · exact hpos
  interval_cases k
  ·
    have hYZ : Y = Z := (Subgroup.eq_of_le_of_card_ge hZY (by rw [hk, h.1]; norm_num)).symm
    obtain ⟨x, hx3, hxc⟩ := exists_noncentral_of_isTripleA6 h
    refine ⟨x, hx3, hxc, fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hWY w hw
    rw [hYZ] at hy
    rw [hconjZ y hy, MulAut.one_apply]
  ·
    have hYab : IsMulCommutative Y :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hk])
    obtain ⟨y, hyY, hyZ⟩ : ∃ y ∈ Y, y ∉ Z := by
      by_contra hall
      push Not at hall
      have h1 := Subgroup.card_le_of_le (fun y hy => hall y hy : Y ≤ Z)
      rw [hk, h.1] at h1
      norm_num at h1
    refine ⟨y, hY3 y hyY, hyZ, fun w hw => ?_⟩
    obtain ⟨y', hy', rfl⟩ := hWY w hw
    have hc : y' * y = y * y' := congrArg Subtype.val (hYab.is_comm.comm ⟨y', hy'⟩ ⟨y, hyY⟩)
    rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  ·
    exfalso
    obtain ⟨hPne, T, hT⟩ := hP
    have hT8 : 8 ∣ Nat.card T :=
      T.pow_dvd_card_of_pow_dvd_card (n := 3) (by rw [hcard]; norm_num)
    have h8 : 8 ∣ Nat.card P :=
      hT8.trans (Subgroup.card_dvd_of_le (Subgroup.le_normalizer.trans hT))
    set Q := P ⊔ Y with hQ
    have h216 : 216 ∣ Nat.card Q := by
      have h1 : 8 ∣ Nat.card Q := h8.trans (Subgroup.card_dvd_of_le le_sup_left)
      have h2 : 27 ∣ Nat.card Q := by
        have := Subgroup.card_dvd_of_le (le_sup_right : Y ≤ Q)
        rwa [hk] at this
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    have hZQ : Z ≤ Q := hZY.trans le_sup_right
    have hQi : Q.index = 1 ∨ Q.index = 5 := by
      have h1 := Q.card_mul_index
      rw [hcard] at h1
      obtain ⟨m, hm⟩ := h216
      have h2 : m * Q.index = 5 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 216)
          (by rw [← mul_assoc, ← hm, h1])
      have h3 : Q.index ∣ 5 := Dvd.intro_left m h2
      rcases (Nat.dvd_prime (by norm_num)).mp h3 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4
    have hsimp : IsSimpleGroup (X ⧸ Z) := by
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
      exact φ.isSimpleGroup
    have hcardq : Nat.card (X ⧸ Z) = 360 := by
      rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_six']
    have hkerQ : (QuotientGroup.mk' Z).ker ≤ Q := by rw [QuotientGroup.ker_mk']; exact hZQ
    have hQtop : Q = ⊤ := by
      rcases hQi with h1 | h1
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        apply index_ne_five_of_isSimpleGroup hsimp hcardq (Q.map (QuotientGroup.mk' Z))
        rw [Subgroup.index_map_eq Q (QuotientGroup.mk'_surjective Z) hkerQ, h1]
    have hPn : P.Normal := by
      refine ⟨fun p hp g => ?_⟩
      have hg : g ∈ Subgroup.normalizer (P : Set X) := by
        have : g ∈ Q := hQtop ▸ Subgroup.mem_top g
        exact (sup_le Subgroup.le_normalizer hYN) this
      exact (Subgroup.mem_normalizer_iff.mp hg p).mp hp
    have hPZ : Z ≤ P := fun z hz =>
      hT (Subgroup.mem_normalizer_iff.mpr fun t => by
        rw [← Subgroup.mem_center_iff.mp hz t, mul_inv_cancel_right])
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp (P.map (QuotientGroup.mk' Z))
        (Subgroup.Normal.map hPn _ (QuotientGroup.mk'_surjective Z)) with hb | ht
    ·
      have hPle : P ≤ Z := by
        intro p hp
        have : (QuotientGroup.mk' Z p) ∈ P.map (QuotientGroup.mk' Z) := ⟨p, hp, rfl⟩
        rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      have h1 := (h8.trans (Subgroup.card_dvd_of_le hPle))
      rw [h.1] at h1
      norm_num at h1
    ·
      apply hPne
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk' Z x) ∈ P.map (QuotientGroup.mk' Z) := ht ▸ Subgroup.mem_top _
      obtain ⟨p, hp, hpx⟩ := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpx
      have := P.mul_mem hp (hPZ hpx)
      simpa using this

end Basic

end Item19Res4Proof

end CFSG.RankThree.PartTwo.Sec19
